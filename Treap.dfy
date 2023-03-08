include "TreapNode.dfy"

class Treap {
  var root: TreapNode?
  var prioritySet: set<int> //Keeps track of what priority was used.

  method Build(values: array<int>) {}
  method Insert(value: int) {}
  method Delete(value: int) {}
  method Search(value: int) {}

  method RotateLeft(node: TreapNode) {}
  method RotateRight(node: TreapNode) {}

  // To allow for different implementation of RNG
  // to be easily swapped. Change signature if needed
  method RandomNumberGenerator() returns (priority: int) {
    return -1;
  }
}
