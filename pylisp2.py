# PyLisp
# a useful library for parsing lisp
# by Isaac Sheff, March 31, 2014

from Queue import Queue




class _SpaceBufferedIterator :
  "An iterator class which puts spaces on either side of any parens"

  def __init__(self, original_iterator):
    "input: another iterator, we'll end up like that, but with the spaces"
    self.buffer = Queue(2) 
    self.original_iterator = iter(original_iterator)

  def __iter__(self): return self

  def next(self):
    "returns the next item"
    if not self.buffer.empty():
      return self.buffer.get()
    c = self.original_iterator.next()
    if not (c in ['(',')']):
      return c
    self.buffer.put(c)
    self.buffer.put(' ')
    return ' '



class _FileIterator:
  "Iterates through a file, one character at a time."
  def __init__(self, file_to_read):
    "takes as input a file to read from"
    self.file_to_read = file_to_read
  def __iter__(self): return self
  def next(self):
    "returns the next character in the file"
    c = self.file_to_read.read(1)
    if not c:
      raise StopIteration("end of file")
    return c

class _CommentRemovalIterator:
  "Just like the input iterator, but without anything on any line after comment"
  def __init__(self, iterator, comment="#"):
    self.iterator = iter(iterator)
    self.comment = comment
  def __iter__(self):
    return self
  def next(self):
    c = self.iterator.next()
    if c != self.comment:
      return c
    while not (self.iterator.next() in "\n\r"):
      pass
    return "\n"

def _file_iter(filename):
  "creates a _FileIterator to iterate through the file one character at a time."
  return _FileIterator(open(filename,"r"))

def _space_buffered_file_iter(filename):
  "iterates through the file one character at a time, spaces inserted around ()"
  return _SpaceBufferedIterator(_file_iter(filename))

class _PushBackIterator:
  """just like the iterator inside, but with a new value on top of the stack
     to be iterated"""
  def __init__(self, value, iterator):
    self.value = value
    self.iterator = iter(iterator)
    self.used_value = False
  def next(self):
    if self.used_value:
      return self.iterator.next()
    self.used_value = True
    return self.value
  def __iter__(self):
    return self

def _lisp_node_from_iterator(iterator):
  """given an iterator, this will make a lisp node reading the iterator as a 
     string. DANGER: this requires spaces around all parentheses. Use
     _SpaceBufferedIterator to make this happen."""
  iterator = iter(iterator)
  children = []
  try:
    c = str(iterator.next())
    # if there are spaces at the beginning, just ignore them
    while c.isspace():
      c = str(iterator.next())
    # something has gone wrong if we encounter a ) at the beginning
    if c == ")":
      raise UnmatchedParenthesesException("unexpected )")
    # this is a token, so just read in characters until you get to a space
    if c != "(":
      token = ""
      while not c.isspace():
        token += c
        try: # or a stop, if you reach stop, that's the end of the token too
          c = str(iterator.next())
        except StopIteration:
          c = " "
      return LispNode(token=token, is_token=True, parseString=None, parent=None,
                      children=None)
    # otherwise, read in children using recursion, eating space or whatever in
    # between. Note that you have to look ahead to see if the next thing is a ),
    # which requires using a _PushBackIterator so the recursive call's iterator
    # can see the character you peaked ahead at.
    c = str(iterator.next())
    while c.isspace():
      c = str(iterator.next())
    while c != ")":
      children.append(_lisp_node_from_iterator(_PushBackIterator(c,iterator)))
      c = str(iterator.next())
      while c.isspace():
        c = str(iterator.next())
    a = LispNode(parseString=None, parent=None, children=children,
                token=None, is_token=False)
    for child in children:
      child.parent = a
    return a
  except StopIteration as s:
    raise UnmatchedParenthesesException(str(s) +" after "+str(map(str, children)))

class _LispNodeIterator:
  "iterates through this LispNode (MUST NOT BE A TOKEN NODE) char by char"
  def __init__(self, lisp_node):
    self.child_iterator = iter(lisp_node.children)
    try:
      self.current_iterator = _PushBackIterator("(",self.child_iterator.next())
    except StopIteration: #this node has no children.
      self.current_iterator = iter("(")
  def __iter__(self):
    return self
  def next(self):
    try:
      try:
        return self.current_iterator.next()
      except StopIteration:
        self.current_iterator = iter(self.child_iterator.next())
        return " "
    except StopIteration:
      self.next = self.current_iterator.next
      self.__iter__ = self.current_iterator.__iter__
      return ")"




# AND NOW, ON TO THE STUFF THE USERS MIGHT ACTUALLY USE
class UnmatchedParenthesesException(Exception):
  " an Exception for when we're parsing bad strings "
  def __init__(self, value):
    self.value = value
  def __str__(self):
    return repr(self.value)

class LispNode:
  """
  You can think of an AST constructed from LISP as consisting of a set of 
  LispNodes, each of which has a parent (except the root), and may have some
  set of children, or may be a token. This is represented by the fields:
  .parent: this Node's parent (default None)
  .children: this Node's children (a python list) (default: [])
  .token: if this node is a token, this is its string value (default: "")
  .is_token: a boolean representing whether this node is a token (default: F)
  """
  def __init__(self, parseString=None, 
                     parent=None, 
                     children=None, 
                     token=None, 
                     is_token=None):
    """Constructor:
       If there is only one argument, parseString, it will parse that as Lisp.
       Otherwise, it takes in a parent node (also possible with ParseString),
       child nodes, a token value and is_token.
       If this is a token, its child nodes are irrelevant.
       If this is not a token, its token value is irrelevant."""
    if children == None:
      children = []
    if token == None:
      token = ""
    if is_token == None:
      is_token = False
    if parseString: # if we're parsing input string into a node structure
      s = _lisp_node_from_iterator(_SpaceBufferedIterator(parseString))
      self.children = s.children
      self.token = s.token
      self.is_token = s.is_token
    else:
      self.children = children
      self.token = token
      self.is_token = (bool(token)) or is_token
    for child in self.children:
      child.parent = self
    self.parent = parent

 
  def __str__(self):
    "returns a (not exactly pretty) lisp version of this node"
    return "".join(self)

  def __eq__(self, other):
    "returns whether the two lisp nodes are equal (different parents OK)"
    # should be equivalent to str(self)==str(other)
    a = iter(self)
    b = iter(other)
    a_i = None
    b_i = None
    while a_i == b_i:
      try:
        a_i = a.next()
      except StopIteration:
        try:
          b_i = b.next()
          return False
        except StopIteration:
          return True
      try:
        b_i = b.next()
      except StopIteration:
        return False
    return False

  def find(self, target):
    "Returns all of the LispNodes that match target in this or its children"
    if self == target:
      return [self]
    return reduce(lambda x,y:x+y.find(target), self.children, [])

  def replace(self, find, replace):
    """all nodes that match find will be replaced with duplicates of replace 
       (works on strings)"""
    for s in self.find(find):
      f = LispNode(replace)
      s.children = f.children
      for child in s.children:
        child.parent = s
      s.token = f.token
      s.is_token = f.is_token

  
  def pretty_print(self, max_width=None, min_width=None):
   "returns a marginally prettier string version. max width default: 80"
   if self.is_token:
     return self.token
   if len(self.children) == 0:
     return "()"
   if max_width == None:
     max_width = 80
   if min_width == None:
     min_width = 40
   if max_width < min_width:
     max_width = min_width
   if len(str(self)) <= max_width:
     return str(self)
   else:
     return "("+self.children[0].pretty_print(max_width-1,min_width) +\
            reduce(lambda x,y:x+"\n  "+\
              y.pretty_print(max_width-2, min_width).replace("\n","\n  "), \
              self.children[1:], "")+"\n)"
  
  def __iter__(self):
    "iterates through this LispNode as if it were a string, char by char"
    if self.is_token:
      return iter(self.token)
    else:
      return _LispNodeIterator(self)


def lisp_parse(content, comment="#"):
  """reads the input content, with single line comments starting with comment,
   parsing the results as a LispNode
   line breaks must be with \\n
   comment defaults to #
   note that to be valid, this must be contained within an ultimate ()"""
  return LispNode(_CommentRemovalIterator(content, comment))

def lisp_file(filename, comment="#"):
  """reads the input filename, with single line comments starting with comment,
   parsing the results as a LispNode
   comment defaults to #
   note that to be valid, this file must be contained within an ultimate ()"""
  return lisp_parse(_file_iter(filename), comment)
