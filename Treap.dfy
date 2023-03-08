include "TreapNode.dfy"

class Treap {
  var root: TreapNode?
  var prioritySet: set<int> //Keeps track of what priority was used.

  constructor () {
    this.root := null;
  }

  ghost predicate Valid()
    reads this, root, if root != null then root.repr else {}
  {
    root != null ==> root.Valid()
  }


  method Build(values: array<int>) {}
  method Insert(value: int) {}
  method Delete(value: int) {
  }

  // Initial search entry point
  method Search(value: int) returns (node: TreapNode?)
    requires Valid()
  {
    if(root == null){
      return null;
    }
    var ans := SearchNode(root, value);
    return ans;
  }

  // Recursive search using nodes
  method SearchNode(currRoot: TreapNode, value: int)
    returns (node: TreapNode?)
    requires currRoot.Valid()
    ensures if node != null then node.key == value else true
    decreases currRoot.repr
  {
    if (currRoot.key == value) {
      return currRoot;
    }
    if (currRoot.key < value && currRoot.right != null) {
      var ans := SearchNode(currRoot.right, value);
      return ans;
    }
    if (currRoot.key > value && currRoot.left!= null) {
      var ans := SearchNode(currRoot.left, value);
      return ans;
    }
    return null;
  }

  method RotateLeft(node: TreapNode) {
  }
  method RotateRight(node: TreapNode) {}

  // To allow for different implementation of RNG
  // to be easily swapped. Change signature if needed
  method RandomNumberGenerator() returns (priority: int) {
    return -1;
  }
}

// Used for testing
method Main() {
  var treap := new Treap();
  var result := treap.RandomNumberGenerator();
  print (result);
}
