#!/usr/bin/env python
import os
import datetime
import sys
import math
from pylisp2 import lisp_parse, LispNode
import itertools

def binaries(n): return map("".join, itertools.product('01',repeat=n))
# this next one is needed for the analysis printouts
def sbinaries(n): return  sorted(binaries(n), key=(lambda z:-sum(map(int,z))))
# convert a hex string to a binary string
def hex_to_binary(h): return "".join(map(lambda x:binaries(4)[int(x,16)], h))

def define_const(lispnode_list):
  "desugars define-const into the define-fun it always was"
  for lispnode in lispnode_list:
    for const in lispnode.find("define-const"):
      const.token="define-fun"
      const.parent.children.insert(2,LispNode("()"))

def declare_const(lispnode_list):
  "desugars declare-const into the declare-fun it always was"
  for lispnode in lispnode_list:
    for const in lispnode.find("declare-const"):
      const.token="declare-fun"
      const.parent.children.insert(2,LispNode("()"))

def define_fun_no_input(all_lines_list, lispnode_list):
  """Because apparently some solvers can't handle it, replaces no input
     define-fun with declare fun and assertion"""
  for lispnode in lispnode_list:
    for define in lispnode.find("define-fun"):
      if define.parent.children[2] == "()":
        define.token="declare-fun"
        lispnode_index = lispnode_list.index(lispnode)
        all_lines_index = all_lines_list.index(lispnode)
        lispnode_list.insert(lispnode_index+1, LispNode(children=
          [LispNode("assert"), LispNode(children=
             [LispNode("="), LispNode(define.parent.children[1]), 
              define.parent.children.pop(4)])]))
        all_lines_list.insert(all_lines_index+1,lispnode_list[lispnode_index+1])

def bv_all_zero_1_in_ith_place(n, i):
  "creates a node that evaluates to a bitvec size n with a 1 only in place i"
  if i >= n:
    return LispNode("((_ repeat "+str(n)+") #b0)")
  if i == 0:
    return LispNode("((_ zero_extend "+str(n-1)+")  #b1)")
  return LispNode(children=[LispNode("concat"), 
                            bv_all_zero_1_in_ith_place(n-i, 0), 
                            bv_all_zero_1_in_ith_place(i, i)])

def item_descriptions_from_enclosing_foralls(lispnode):
  "returns the item descriptions form all enclosing foralls"
  input_item_descriptions = []
  p = lispnode.parent
  while (p != None):
    if len(p.children) > 2:
      if p.children[0] == "forall" or p.children[0] == "exists": 
        input_item_descriptions += p.children[1].children
      if p.children[0] == "define-fun":
        input_item_descriptions += p.children[2].children
    p = p.parent
  return input_item_descriptions

def forall_single(lispnode_list):
  "replaces all foralls with multiple items with nested singleton foralls"
  for lispnode in lispnode_list:
    for forall in lispnode.find("forall"):
      parent = forall.parent
      while len(parent.children[1].children) > 1:
        parent.children[2] = LispNode(parent = parent, children = 
            [LispNode("forall"),
             LispNode(children = parent.children[1].children[1:]),
             parent.children[2]])
        parent.children[1].children = parent.children[1].children[:1]
        parent = parent.children[2]

def forall_unroll(all_lines_list, lispnode_list):
  """Unroll any forall BitVec into a big and"""
  foralls_unrolled_so_far = 0
  lispnode_index = 0
  all_lines_index = 0
  while (lispnode_index < len(lispnode_list)):
    lispnode = lispnode_list[lispnode_index]
    while all_lines_list[all_lines_index] != lispnode:
      all_lines_index += 1
    for forall in lispnode.find("forall")[::-1]: # innermost first
      enclosing_item_descriptions = \
          item_descriptions_from_enclosing_foralls(forall.parent)
      item_descriptions = forall.parent.children[1].children
      if reduce(lambda x,y: x and (len(y.children[1].children) > 2) and 
                              y.children[1].children[1] == "BitVec", 
                item_descriptions, True):
        #make a function representing this forall
        lispnode_list.insert(lispnode_index, LispNode(children=
          [LispNode("define-fun"), 
           LispNode("forall-unroll-"+str(foralls_unrolled_so_far)),
           LispNode(children = map(LispNode, 
               enclosing_item_descriptions + item_descriptions)), 
           LispNode("Bool"), 
           forall.parent.children[2]]))
        all_lines_list.insert(all_lines_index, lispnode_list[lispnode_index])
        lispnode_index += 1
        all_lines_index += 1
        forall.token = "and"
        forall.parent.children = [forall]
        call_forall_unroll = LispNode(children=
          [LispNode("forall-unroll-"+str(foralls_unrolled_so_far))]+
           map(lambda node:LispNode(node.children[0]), 
               enclosing_item_descriptions + item_descriptions))
        # I'm going to unroll this forall one bit at a time, so as
        # to guarantee program expansion linear in the size of the 
        # largest bitvector
        if len(item_descriptions) > 0:
          item_description = item_descriptions[0]
          num_bits = int(str(item_description.children[1].children[2]))
          if num_bits == 0:
            print "ERROR: 0 BIT BITVECTOR: "+str(forall.parent)
          else:
            for i in range(num_bits-1):
              lispnode_list.insert(lispnode_index, LispNode(children=
                [LispNode("define-fun"),
                 LispNode("forall-unroll-"+str(foralls_unrolled_so_far)+\
                          "-bit-"+str(i)),
                 LispNode(children = map(LispNode, 
                       enclosing_item_descriptions + item_descriptions)), 
                 LispNode("Bool"),
                 LispNode(children=[LispNode("and"),
                                    LispNode(call_forall_unroll),
                                    LispNode(call_forall_unroll)])
                ]))
              all_lines_list.insert(all_lines_index, \
                                    lispnode_list[lispnode_index])
              # now I replace one of the arguments in that function with an
              # argument at sets the ith bit to 1
              lispnode_list[lispnode_index].children[4].children[2].replace(
                  item_description.children[0], 
                  LispNode(children=[LispNode("bvor"),
                                     item_description.children[0],
                                     bv_all_zero_1_in_ith_place(num_bits,i)]))
              call_forall_unroll = LispNode(children=
                [LispNode("forall-unroll-"+str(foralls_unrolled_so_far)+\
                          "-bit-"+str(i))]+
                 map(lambda node:LispNode(node.children[0]), 
                     enclosing_item_descriptions + item_descriptions))
              lispnode_index += 1
              all_lines_index += 1
            forall.parent.children.append(LispNode(call_forall_unroll, 
                                                   parent=forall.parent))
            forall.parent.children.append(LispNode(call_forall_unroll, 
                                                   parent=forall.parent))
            forall.parent.children[1].replace(item_description.children[0], 
                bv_all_zero_1_in_ith_place(num_bits, num_bits-1))
            forall.parent.children[2].replace(item_description.children[0], 
                bv_all_zero_1_in_ith_place(num_bits, num_bits))
      foralls_unrolled_so_far+=1
    lispnode_index += 1
    all_lines_index += 1


def exists_replace(lispnode_list):
  " replaces (exists foo bar) with (not (forall foo (not bar))) "
  for lispnode in lispnode_list:
    lispnode_index = lispnode_list.index(lispnode)
    for exists in lispnode.find("exists"):
      exists.parent.children = [LispNode("not", parent=exists.parent),
          LispNode(parent = exists.parent, children = [
              LispNode("forall"),
              exists.parent.children[1],
              LispNode(children = [
                  LispNode("not"),
                  exists.parent.children[2]])])]



def functions_boolean_output_to_bv(all_lines_list, lispnode_list):
  """if any declared functions have Bool outputs, creates a new declared
     version with BitVec output, and defines the old function to read from the
     new one. In order to bias z3 towards functiosn returning "true" in cases
     where it doesn't matter, the bv version returns 0 when the original
     returns true"""
  for lispnode in lispnode_list:
    for declare_fun in lispnode.find("declare-fun"):
      if declare_fun.parent.children[3] == "Bool":
        lispnode_index = lispnode_list.index(lispnode)
        all_lines_index = all_lines_list.index(lispnode)
        lispnode_list.insert(lispnode_index, LispNode(children = 
           [LispNode("declare-fun"),
            LispNode(str(declare_fun.parent.children[1])+"-bv-version"),
            LispNode(declare_fun.parent.children[2]),
            LispNode("(_ BitVec 1)")]))
        all_lines_list.insert(all_lines_index, lispnode_list[lispnode_index])
        declare_fun.parent.children[0].token = "define-fun"
        for i in range(len(declare_fun.parent.children[2].children)):
          declare_fun.parent.children[2].children[i] = LispNode(
              parent = declare_fun.parent.children[2], 
              children = [LispNode("generated-input-name-"+str(i)), 
                          declare_fun.parent.children[2].children[i]])
        declare_fun.parent.children.append(LispNode("(= #b0 ("+
            str(declare_fun.parent.children[1])+"-bv-version "+
            " ".join(map(lambda i:"generated-input-name-"+str(i), 
                         range(len(declare_fun.parent.children[2].children))))+
            "))"))

def bv_functions_to_tables(all_lines_list, lispnode_list):
  """turns all declare-fun with bv inputs and outputs into defined functions
     that just look up stuff in a BV lookup value."""
  name_counter = 0
  for lispnode in lispnode_list:
    lispnode_index = lispnode_list.index(lispnode)
    all_lines_index = all_lines_list.index(lispnode)
    for declare_fun in lispnode.find("declare-fun"):
      # if this function's inputs and outputs are all bitvecs
      if len(declare_fun.parent.children) > 3 and\
         len(declare_fun.parent.children[3].children) > 2 and\
         declare_fun.parent.children[3].children[1] == "BitVec" and\
         str(declare_fun.parent.children[2]) != "()" and\
         reduce(lambda x,y:x and (not y.is_token) and len(y.children) > 2 and \
                             y.children[1] == "BitVec", 
                declare_fun.parent.children[2].children, True):
        name = declare_fun.parent.children[1]
        args = LispNode(declare_fun.parent.children[2]).children
        sort = declare_fun.parent.children[3]
        arg_bits = reduce(lambda x,y:x+int(str(y.children[2])), args, 0)
        sort_bits =int(str(sort.children[2]))
        num_bits = (2**arg_bits) * sort_bits
        lispnode_list.insert(lispnode_index, 
            LispNode("(declare-fun "+str(name)+"-lookup-table () (_ BitVec "+
                     str(num_bits)+"))"))
        all_lines_list.insert(all_lines_index, lispnode_list[lispnode_index])
        declare_fun.token="define-fun"
        for i in range(len(declare_fun.parent.children[2].children)):
          declare_fun.parent.children[2].children[i] = LispNode(
              parent = declare_fun.parent.children[2], 
              children = [LispNode("generated-input-name-"+str(i)), 
                          declare_fun.parent.children[2].children[i]])
        sort_bits_expressed = \
            binaries(int(math.ceil(math.log((sort_bits+1), 2))))[sort_bits]
        sort_bits_expressed = LispNode(children=
           [LispNode("concat"), 
            bv_all_zero_1_in_ith_place(num_bits - len(sort_bits_expressed), 
                                       num_bits), 
            LispNode("#b"+sort_bits_expressed)])
        concat_args = reduce(lambda z,w: LispNode(children = 
           [LispNode("concat"), z, LispNode(w.children[0])]), 
            declare_fun.parent.children[2].children[1:], 
            LispNode(declare_fun.parent.children[2].children[0].children[0]))
        concat_args = LispNode(children=
           [LispNode("concat"), 
            bv_all_zero_1_in_ith_place(num_bits - arg_bits, num_bits), 
            concat_args])
        declare_fun.parent.children.append(LispNode(
            "((_ extract "+str(sort_bits-1)+" 0) (bvlshr "+str(name)+\
            "-lookup-table (bvmul "+str(concat_args)+" "+\
            str(sort_bits_expressed)+")))", parent = declare_fun.parent))


def replace_boolean_function_input(function_token, input_index, lispnode_list):
  """ Should replace the input_index th input of the function with the given
      function token with an if-than-else expression that takes the old
      boolean value, and returns #b1 if true of #b0 if false"""
  for lispnode in lispnode_list:
    for f in lispnode.find(function_token):
      if (len(f.parent.children) > input_index) and (f.parent.children[0] == f):
        replacement = LispNode("(ite "+str(f.parent.children[input_index+1])+\
                               " #b1 #b0)")
        replacement.parent = f.parent
        f.parent.children[input_index+1] = replacement

def define_fun_boolean_input(lispnode_list):
  "replace all define-fun functions with Bool inputs with BitVec 1 inputs"
  for lispnode in lispnode_list:
    for f in lispnode.find("define-fun"):
      if len(f.parent.children) > 3:
        function_token = f.parent.children[1]
        for input_index in range(len(f.parent.children[2].children)):
          input_description = f.parent.children[2].children[input_index]
          if len(input_description.children) > 1:
            if input_description.children[1] == "Bool":
              # replace all instances of this in the function definition
              for input_use in f.parent.children[4].find(
                               input_description.children[0]):
                replacement = LispNode("(= #b1 "+str(input_use)+")")
                input_use.children = replacement.children
                input_use.token = ""
                input_use.is_token = False
              # replace all inputs elsewhere, and change type
              input_description.children[1] = LispNode("(_ BitVec 1)")
              input_description.children[1].parent = input_description
              replace_boolean_function_input(function_token, input_index,
                                             lispnode_list)

def declare_fun_boolean_input(lispnode_list):
  "replace all declare-fun functions with Bool inputs with BitVec 1 inputs"
  for lispnode in lispnode_list:
    for f in lispnode.find("declare-fun"):
      if len(f.parent.children) > 2:
        function_token = f.parent.children[1]
        for input_index in range(len(f.parent.children[2].children)):
          input_description = f.parent.children[2].children[input_index]
          if input_description == "Bool":
            replacement = LispNode("(_ BitVec 1)")
            replacement.parent = f.parent.children[2]
            f.parent.children[2].children[input_index] = replacement
            replace_boolean_function_input(function_token, input_index,
                                             lispnode_list)

def declare_datatypes(all_lines_list, lispnode_list):
  """ reads through the lispnode list, replacing all instances of
      declare-datatypes with no type arguments with finite value 
      declarations, as BitVectors.
      additionally, because it may be the case that this allows more
      values of the bitvector type than you enumerated, it inserts
      and clauses into all exists clauses of this type stating that
      the value must be at most the maximum possible replacement
      BitVec value. Forall statements are inserted for all functions
      returning values of this type stating that for all other inputs,
      the values returned by these functions must be at most the maximum
      possible replacment BitVec value.
      all_lines_list: the set of all the lines in the file
      lispnode_list: the set of just the lisp nodes in the file"""
  for lispnode in lispnode_list:
    for declare in lispnode.find(LispNode("declare-datatypes")):
      if declare.parent.children[1] == LispNode("()"):
        declare_index = all_lines_list.index(lispnode)
        declare_index_lispnodes = lispnode_list.index(lispnode)
        lispnode_list.remove(lispnode)
        all_lines_list.remove(lispnode)
        declare.parent.is_token = True # this node becomes blank
        declare.parent.token = ""
        for datatype in declare.parent.children[2].children:
          if len(datatype.children) > 1:
            type_name = LispNode(datatype.children[0])
            type_values = map(LispNode, datatype.children[1:])
            n = int(math.ceil(math.log(len(type_values),2)))
            bins = map(lambda x:LispNode("#b"+x), binaries(n))
            # we have to add a clause to all "exists" thingies
            # and a forall for all functions that return these
            for node in lispnode_list:
              for type_name_instance in node.find(type_name):
                if type_name_instance.parent != None:
                  # if there's a delcared function that returns this type
                  declare = type_name_instance.parent
                  if len(declare.children) > 3:
                    if declare.children[0] == "declare-fun":
                      node_index = lispnode_list.index(node)
                      node_all_index = all_lines_list.index(node) 
                      lispnode_list.insert(node_index+1, 
                        LispNode(children = [LispNode("assert"), 
                          LispNode(children = [LispNode("forall"), 
                            LispNode(children = map(
                              lambda x:LispNode(children=[
                                LispNode("input-"+str(x)), 
                                LispNode(declare.children[2].children[x])]), 
                              range(len(declare.children[2].children)))), 
                            LispNode("(bvule ("+str(declare.children[1])+" "+\
                             " ".join(map(lambda x:"input-"+str(x), 
                               range(len(declare.children[2].children))))+") "+\
                             str(bins[len(type_values)-1])+")")])]))
                      if lispnode_list[node_index+1].children[1].children[1] ==\
                         "()":
                        lispnode_list[node_index+1].children[1] = \
                            lispnode_list[node_index+1].children[1].children[2]
                        lispnode_list[node_index+1].children[1].parent = \
                            lispnode_list[node_index+1]
                      all_lines_list.insert(node_all_index+1, 
                           lispnode_list[node_index+1])
                  # if there's an exists of this type
                  if type_name_instance.parent.parent != None:
                    if type_name_instance.parent.parent.parent != None:
                      exists = type_name_instance.parent.parent.parent
                      if len(exists.children) > 2:
                        if exists.children[0] == "exists":
                          exists.children[2] = LispNode(parent = exists, 
                              children = [LispNode("and"), 
                                  LispNode("(bvule "+\
                                  str(type_name_instance.parent.children[0])+\
                                  " "+str(bins[len(type_values)-1])+")"), \
                                  exists.children[2]])
            for node in lispnode_list:
              # replace the defined type with a bitvec
              node.replace(type_name, LispNode("(_ BitVec "+str(n)+")"))
            for i in range(len(type_values)):
              new_constant = LispNode("(define-const "+str(type_values[i])+\
                                     " (_ BitVec "+str(n)+") "+str(bins[i])+")")
              lispnode_list.insert(declare_index_lispnodes, new_constant)
              all_lines_list.insert(declare_index, new_constant)

def define_sort(lispnode_list):
  """reads through the lispnode list, replacing the sorts defined (provided they
     have 0 sort parameters) with their definitions"""
  for l in lispnode_list:
    for p in l.find(LispNode("define-sort")):
      if p.parent.children[2] == LispNode("()"):
        target = LispNode(p.parent.children[1])
        replacement = LispNode(p.parent.children[3])
        # we're going to replace p's parent with the empty token
        p.parent.is_token = True
        p.parent.token = ""
        for node in lispnode_list:
          node.replace(target, replacement)
       

def remove_parens_around_tokens(lispnode_list):
  "replaces any nodes with just a single token child with that token child"
  for node in lispnode_list:
    if node.is_token:
      while (node.parent != None) and (len(node.parent.children)==1):
        node.parent.token=node.token
        node.parent.is_token=True
        node.parent.children=[]
        node = node.parent
    else:
      remove_parens_around_tokens(node.children)

def fix_get_model(file_list):
  "replaces get-model with (get-model), provided its on a line of its own."
  for i in range(len(file_list)):
    if str(file_list[i]).startswith("get-model"):
      file_list[i] = "(get-model)"+(str(file_list[i])[len("get-model"):])

def fix_check_sat(file_list):
  "replaces check-sat with (check-sat), provided its on a line of its own."
  for i in range(len(file_list)):
    if str(file_list[i]).startswith("check-sat"):
      file_list[i] = "(check-sat)"+(str(file_list[i])[len("check-sat"):])

def lisp_file_comments(filename, comment="#", execute_on_lisp = None):
  """ reads input file filename with comment character comment (default #)
      and outputs an array of either strings that are subsections of the 
      file consisting entirely of comments, or processed LISP. It will
      process the lisp by parsing it into a LispNode, and then running
      execute_on_lisp (default identity function) on that LispNode. 
      returns [array with all that stuff], [array of just the processed LISP]"""
  if execute_on_lisp == None:
    execute_on_lisp = lambda x:x
  answer = []
  lispnodes = []
  depth = 0
  open_paren = 0
  content = (reduce(lambda x,y:x+"\n"+y, open(filename,"r"),""))
  i=0
  while i < (len(content)):
    if content[i:].startswith(comment):
      while (i < len(content)) and (content[i] != '\n'):
        i += 1
    else:
      if content[i] == '(':
        depth += 1
        if depth == 1:
          answer.append(content[open_paren:i])
          open_paren = i
      if content[i] == ')':
        depth -= 1
        if depth == 0:
          a=(execute_on_lisp(lisp_parse(content[open_paren:i+1], comment)))
          answer.append(a)
          lispnodes.append(a)
          open_paren = i+1
      i+=1
  answer.append(content[open_paren:])
  return answer, lispnodes

def get_n(lispnode_list):
  "returns the value of n as defined in the smt, 0 if it can't find it"
  for lispnode in lispnode_list:
    for equals in lispnode.find("="):
      if equals.parent.parent.children[0] == "assert" and\
         equals.parent.children[1] == "n":
        return int(str(equals.parent.children[2])[2:], 2)+1
    for function in lispnode.find("define-fun"):
      if function.parent.children[1] == "n":
        return int(str(function.parent.children[4])[2:], 2)+1
    for constant in lispnode.find("define-const"):
      if constant.parent.children[1] == "n":
        return int(str(constant.parent.children[3])[2:], 2)+1
  return 0


def local_max_thresholds(all_lines_list, lispnode_list):
  """adds the requirement that flipping any 1 of thresholds to 0 fails 
     assertions. Must be done after functions to tables but before 
     exists and forall unrolling"""
  all_requirements = LispNode(children = [LispNode("and")] + 
      map(lambda x:LispNode(x.children[1]), 
          filter(lambda y: (len(y.children) > 1) and (y.children[0]=="assert"),
                  lispnode_list)))
  # get the length of the lookup table, and thresholds functions
  len_lookup = 0
  thresholds_all_index = 0
  thresholds_index = 0
  thresholds_bv = LispNode("")
  thresholds = LispNode("")
  for lispnode in lispnode_list:
    for node in lispnode.find("thresholds-bv-version-lookup-table"):
      if node.parent.children[0] == "declare-fun":
        len_lookup = int(str(node.parent.children[3].children[2]))
    for node in lispnode.find("thresholds-bv-version"):
      if node.parent.children[0] == "define-fun":
        thresholds_bv = LispNode(node.parent)
    for node in lispnode.find("thresholds"):
      if node.parent.children[0] == "define-fun":
        thresholds_all_index = all_lines_list.index(lispnode)
        thresholds_index = lispnode_list.index(lispnode)
        thresholds = LispNode(node.parent)
  # create a new function, threshholds-with-table, that is like thresholds but
  # takes as its last input a lookup table
  new_thresholds = LispNode(thresholds)
  new_thresholds.replace("thresholds","thresholds-with-table")
  new_thresholds.replace("thresholds-bv-version","thresholds-bv-version-with-table")
  new_thresholds.children[2].children.append(LispNode(
      "(lookup-table (_ BitVec "+str(len_lookup)+"))", 
      parent = new_thresholds.children[2]))
  for ntbv in new_thresholds.find("thresholds-bv-version-with-table"):
    if ntbv.parent.children[0] == "thresholds-bv-version-with-table":
      ntbv.parent.children.append(LispNode("lookup-table", parent = ntbv))
  # create a function thresholds-bv-version-with-table for use by 
  # thresholds-with-table
  new_thresholds_bv = LispNode(thresholds_bv)
  new_thresholds_bv.replace("thresholds","thresholds-with-table")
  new_thresholds_bv.replace("thresholds-bv-version","thresholds-bv-version-with-table")
  new_thresholds_bv.children[2].children.append(LispNode(
      "(lookup-table (_ BitVec "+str(len_lookup)+"))", 
      parent = new_thresholds_bv.children[2]))
  new_thresholds_bv.children[4].replace("thresholds-bv-version-lookup-table",
                                        "lookup-table") 
  # modify the set of all requirements to take as input a table, and stipulate
  # that for no such table where you've changed one "1" bit to a "0" are all
  # the requirements met
  len_lookup_index = int(math.ceil(math.log(len_lookup, 2)))
  max_lookup_index = "#b"+binaries(len_lookup_index)[len_lookup-1]
  adapted_table = LispNode("(bvand thresholds-bv-version-lookup-table (bvnot "+\
      "(bvshl "+str(bv_all_zero_1_in_ith_place(len_lookup, 0))+" (concat "+\
      str(bv_all_zero_1_in_ith_place(len_lookup-len_lookup_index, len_lookup))+\
      " thresholds-lookup-index))))")
  for thresholds in all_requirements.find("thresholds"):
    if thresholds.parent.children[0] == thresholds:
      thresholds.token="thresholds-with-table"
      thresholds.parent.children.append(LispNode(adapted_table,
                                                 parent=thresholds.parent))
  lispnode_list.insert(thresholds_index, LispNode(children=
  [LispNode("assert"),
   LispNode(children = 
     [LispNode("not"),
      LispNode(children =
        [LispNode("exists"), 
         LispNode("((thresholds-lookup-index (_ BitVec "+str(len_lookup_index)+\
                    ")))"),
         LispNode(children=
           [LispNode("and"), 
            LispNode("(bvule thresholds-lookup-index "+max_lookup_index+")"),
            LispNode("(not (= thresholds-bv-version-lookup-table "+\
                              str(adapted_table)+"))"), 
            all_requirements])])])]))
  # add our functions to the file
  all_lines_list.insert(thresholds_all_index, lispnode_list[thresholds_index])
  lispnode_list.insert(thresholds_index, new_thresholds)
  all_lines_list.insert(thresholds_all_index, new_thresholds)
  lispnode_list.insert(thresholds_index, new_thresholds_bv)
  all_lines_list.insert(thresholds_all_index, new_thresholds_bv)


def local_max_thresholds_iterative(all_lines_list, lispnode_list,model,solver):
  define_funs_from_model(model, lispnode_list)
  thresholds_lookup = LispNode("")
  for lispnode in lispnode_list:
    for node in lispnode.find("thresholds-bv-version-lookup-table"):
      if node.parent.children[0] == "define-fun":
        thresholds_lookup = node.parent.children[4]
  if thresholds_lookup.token.startswith("#x"):
    thresholds_lookup.token = "#b"+hex_to_binary(thresholds_lookup.token[2:])
  for bit in range(2, len(thresholds_lookup.token)):
    if thresholds_lookup.token[bit] == "1":
      print bit
      print thresholds_lookup.token
      thresholds_lookup.token = thresholds_lookup.token[     :bit]+"0"+\
                                thresholds_lookup.token[bit+1:   ]
      #write file, use solver to determine if this is valid
      f_name = ("/tmp/iteration-"+\
               str("-".join(str(datetime.datetime.now()).split()))+".smt2")
      f = open(f_name,"w")
      for x in map(lambda x:str(x).strip(),all_lines_list):
        if (len(x) > 0):
          if (x[0] == "("):
            x = LispNode(x).pretty_print()
        f.write(x)
        f.write("\n")
      f.flush() 
      f.close() 
      model_filename = "/tmp/iteration-model"+\
               str("-".join(str(datetime.datetime.now()).split()))+".smt2"
      os.system(solver+" "+f_name+" > "+ model_filename)
      m = open(model_filename,"r").read()
      m = m.strip()
      if m.startswith("sat"):
        return local_max_thresholds_iterative(all_lines_list, lispnode_list,
                                              LispNode(m[3:]), solver)
      elif m.startswith("unsat"):
        thresholds_lookup.token = thresholds_lookup.token[     :bit]+"1"+\
                                  thresholds_lookup.token[bit+1:   ]
      else:
        print "ITERATIVE SOLVER FAILED:\n"+m
        return thresholds_lookup.token
  return thresholds_lookup.token


def append_analysis(n, all_lines_list, lispnode_list):
  "append the analysis code that will print out the values from thresholds"
  index = -1
  for line in all_lines_list:
    if str(line).startswith("check-sat") or str(line).startswith("(check-sat)"):
      index = all_lines_list.index(line)
  for t in ['Decision', 'Change', 'Availability', 'Truth']:
    for i in range(n):
      bin_i = str(binaries(int(math.ceil(math.log(n,2))))[i])
      for b in sbinaries(n):
        all_lines_list.insert(index,"(assert (= thresholds-"+t+"-"+str(i)+"-"+b+\
           " (thresholds "+t+" #b"+bin_i+" #b"+b+")))")
        all_lines_list.insert(index, "(declare-fun thresholds-"+t+"-"+str(i)+\
           "-"+b+" () Bool)")

def perform_analysis(n,model, html_filename):
  "writes analysis visualization html file, and opens firefox to that file"
  w = open(html_filename, "w")
  w.write("<html>\n<body>\n<table>")
  for t in ['Decision', 'Change', 'Availability', 'Truth']:
    w.write("<tr><td>"+t+"</td></tr>\n")
    w.write("<tr><td></td>")
    for b in sbinaries(n):
      w.write("<td>"+b+"</td>")
    w.write("</tr>\n")
    for i in range(n):
      w.write("<tr><td>"+str(i)+"</td>")
      for b in sbinaries(n):
        possibles = model.find("thresholds-"+t+"-"+str(i)+"-"+b)
        if (len(possibles)>0) and possibles[0].parent.children[4] == "false":
          w.write("<td bgcolor=\"black\">&nbsp;</td>")
        else:
          w.write("<td bgcolor=\"green\">&nbsp;</td>")
      w.write("</tr>\n")
  w.write("</table>\n</body>\n</html>")
  w.close()
  print "html file written.\nOpening firefox . . ."
  os.system("firefox "+html_filename+" &")


def prepend_headers(all_lines_list, lispnode_list):
  "prepend appropriate headers for QF_BV logic"
  lispnode_list.insert(0,LispNode("(set-option :produce-models true)"))
  all_lines_list.insert(0,lispnode_list[0])
  lispnode_list.insert(0,LispNode("(set-logic QF_BV)"))
  all_lines_list.insert(0,lispnode_list[0])
  lispnode_list.insert(0,LispNode("(set-info :smt-lib-version 2.0)"))
  all_lines_list.insert(0,lispnode_list[0])

def replace_true(lispnode_list):
  "replace the token true with (= #b1 #b1)"
  for lispnode in lispnode_list:
    lispnode.replace("true", "(= #b1 #b1)")

def replace_false(lispnode_list):
  "replace the token false with (= #b0 #b1)"
  for lispnode in lispnode_list:
    lispnode.replace("false", "(= #b0 #b1)")

def define_funs_from_model(model, lispnode_list):
  "given a model from a solver, replace all declare-fun s with definitions"
  for define in model.find("define-fun"):
    definition = define.parent
    for lispnode in lispnode_list:
      for declare in lispnode.find(definition.children[1]):
        if declare.parent.children[0] == "declare-fun":
          declare.parent.children = definition.children
          for child in declare.parent.children:
            child.parent = declare.parent
          declare.parent.token = definition.token
          declare.parent.is_token = definition.is_token

def retrieve_and_remove(args, keys, default):
  """if an element of keys is in args, and is not the last element in arg,
     returns the element right after it. Otherwise, returns default."""
  for key in keys:
    if key in args:
      i = args.index(key)
      if len(args) >= i:
        args.pop(i)
        return args.pop(i)
  return default

def main(args):
  help_key = False
  analysis = False
  if len(args) < 1:
    help_key = True
  elif "-h" in args or "-help" in args:
    help_key = True
  if help_key:
    print """
    Pysmt: your friend when converting z3 SMT2 extensions and such to QF_BV
    If you have define-sort or declare-datatypes with no arguments, this may
    help you.
    Likewise, if you have functions with only BitVec or Boolean (or declared
    or defined datatypes) as inputs, this may help you.
    If you meet the above requirements, this may be able to convert your smt2
    file into a QF_BV smt2 file. It will unroll all quantifiers, replace all
    declared datatypes and defined sorts with what you defined them to be,
    replace all boolean function inputs with single bit bitvectors, (and fix
    any usage appropriately), and convert all declared functions to lookup
    tables, allowing the system to solve for the values in the tables. 
    all tags are optional, save for the input file. It will generate output
    files in /tmp/ unless you give it an alternative.

    The resulting QF_BV input to your solver will be expanded by a constant
    factor in the overall length of your file times a constant factor of the
    length of your BitVecs. (Since BitVecs can be declared in a file of size
    logarithmic in their length, this is technically exponential expansion of
    the file.)

    you must supply an input file name as an argument
    
    -help or -h: brings up this dialogue 

    -QF_BV or -q: the filename to which to write the converted QF_BV version

    -solver or -s: the solver to apply to the result (NONE means don't solve)
                   default: z3

    -model or -m: the filename to which to write the solver's output

    -analysis or -a: if this tag is present, we execute analysis specific to 
                     Isaac's research. The remaining tags pertain to this.

    -html or -w: the html file to be opened in firefox and viewed.

    -iterative-optimize or -i: after solver has finished, try switching every
                               response that doesn't meet each threshold to 
                               meeting that threshold, one by one, testing
                               whether this violates the requirements, until
                               you either get one that works, and then start 
                               over, or get through all the response-threshold
                               pairs. In theory, this has the same basic effect
                               as -localmax, but it's slower, and less likely
                               to run out of memory and crash.

    -localmax or -l: requires from the solver that this set of thresholds is
                     locally maximal, which is to say that there there is no 
                     one set of possible responses which presently does not 
                     meet a threshold which can be made to meet that threshold
                     without violating a requirement.
                     DANGER: this option makes z3 (I don't know about other
                             solvers) take MUCH longer.
    
    """
    return 0
  iterative_optimize = False
  if "-iterative-optimize" in args:
    iterative_optimize = True
    args.pop(args.index("-iterative-optimize"))
  if "-i" in args:
    iterative_optimize = True
    args.pop(args.index("-i"))
  if "-analysis" in args:
    analysis = True
    args.pop(args.index("-analysis"))
  if "-a" in args:
    analysis = True
    args.pop(args.index("-a"))
  localmax = False
  if "-localmax" in args:
    localmax = True
    args.pop(args.index("-localmax"))
  if "-l" in args:
    localmax = True
    args.pop(args.index("-l"))
  now = str("-".join(str(datetime.datetime.now()).split()))
  html_filename = retrieve_and_remove(args, ["-html","-w"], "/tmp/pysmt-html-"+\
                                                            now+".html")
  model_filename= retrieve_and_remove(args, ["-model","-m"],"/tmp/pysmt-model-"\
                                                            +now+".smt2")
  qf_bv_filename= retrieve_and_remove(args, ["-QF-BV","-qf-bv","-qf_bv",
      "-QF_BV","-q"], "/tmp/pysmt-QF_BV-"+now+".smt2")
  solver = retrieve_and_remove(args, ["-solver","-s"],"z3")
  input_filename = args[0]
  print "transforming "+input_filename+" to "+qf_bv_filename
  a, l = lisp_file_comments(input_filename, comment=";")
  remove_parens_around_tokens(l)
  declare_datatypes(a,l)
  define_const(l)
  declare_const(l)
  define_sort(l)
  define_fun_no_input(a,l)
  declare_fun_boolean_input(l)
  define_fun_boolean_input(l)
  functions_boolean_output_to_bv(a,l)
  bv_functions_to_tables(a,l)
  remove_parens_around_tokens(l)
  if localmax:
    local_max_thresholds(a,l)
  exists_replace(l)
  forall_single(l)
  forall_unroll(a,l)
  remove_parens_around_tokens(l)
  fix_get_model(a)
  fix_check_sat(a)
  prepend_headers(a,l)
  if analysis and (not iterative_optimize):
    n = get_n(l)
    append_analysis(n,a,l)
  qf_bv_file = open(qf_bv_filename,"w")
  for x in map(lambda x:str(x).strip(),a):
    if (len(x) > 0):
      if (x[0] == "("):
        x = LispNode(x).pretty_print()
      qf_bv_file.write(x)
      qf_bv_file.write("\n")
  qf_bv_file.flush() 
  qf_bv_file.close() 
  print "transformation complete: "+qf_bv_filename
  if solver != "NONE":
    print("attempting to apply solver to produce "+model_filename)
    os.system(solver+" "+qf_bv_filename+" > "+model_filename)
    model = open(model_filename,"r").read()
    model = model.strip()
    if model.startswith("sat"):
      print "sat"
      if iterative_optimize:
        m = LispNode(model[3:])
        iot = local_max_thresholds_iterative(a, l,m,solver)
        open(model_filename,"w").write("sat\n"+m.pretty_print())
        if analysis:
          n = get_n(l)
          append_analysis(n,a,l)
          qf_bv_file = open("/tmp/iterative-analysis-final-"+now+".smt2","w")
          for x in map(lambda x:str(x).strip(),a):
            if (len(x) > 0):
              if (x[0] == "("):
                x = LispNode(x).pretty_print()
                qf_bv_file.write(x)
                qf_bv_file.write("\n")
          qf_bv_file.flush() 
          qf_bv_file.close() 
          os.system(solver+" /tmp/iterative-analysis-final-"+now+".smt2"+" > "+\
                    "/tmp/iterative-analysis-model-"+now+".smt2")
          model = open("/tmp/iterative-analysis-model-"+now+".smt2","r").read()
          model = model.strip()
      if analysis:
        n = get_n(l)
        print "analysis generating html to "+html_filename
        perform_analysis(n,LispNode(model[3:]),html_filename)
        print "done."
    elif model.startswith("unsat"):
      print "unsat"
    else:
      print "solver failed"
      print model


if __name__ == '__main__':
  main(map(str, list(sys.argv)[1:]))
