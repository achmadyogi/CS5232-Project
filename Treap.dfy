include "TreapNode.dfy"

class Treap {
  var root: TreapNode?
  var prioritySet: set<int> //Keeps track of what priority was used.

  constructor () 
  ensures Valid()
  {
    this.root := null;
  }

  ghost predicate Valid()
    reads this, root, if root != null then root.repr else {}
  {
    root != null ==> root.Valid()
  }


  method Build(values: array<int>) {}
  method Insert(value: int) 
    modifies this;
    modifies if this.root != null then this.root.repr else {}
    requires this.root != null ==> this.root.Valid()
    // requires this.root != null ==> this.root in this.root.repr
    // ensures this.root != null ==> this.root.Valid()
  {
    var priority := value * 123 % 1000;
    var node := new TreapNode(value, priority);
    if (this.root != null) {
      this.root.insertNode(node);
    } else {
      this.root := node;
    }
  }

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

  method InOrderTraversal() 
  {
    if (this.root != null) {
      print this.root.key;
    }
  }

  method RotateLeft(node: TreapNode)
    returns (newNode: TreapNode)
    requires node.right != null
    requires node.Valid()
    modifies node.repr
    ensures old(node.repr) == newNode.repr // No change in reachability
    ensures newNode.Valid() // Answer is valid
    ensures newNode == old(node.right)
    ensures newNode.right == old(newNode.right)
    ensures newNode.left == node
    ensures node.right == old(node.right.left)
    ensures node.left == old(node.left)
  {
    newNode := node.right;
    var tempNode := newNode.left;
    newNode.left:= node;
    node.repr := node.repr -newNode.repr;
    node.right:= tempNode;
    if(tempNode != null) {
      // need to add repr of tempNode into node to maintain validity
      node.repr := node.repr + tempNode.repr + {tempNode};
    }
    newNode.repr := newNode.repr + node.repr;
    return newNode;
  }

  method RotateRight(node: TreapNode)
    returns (newNode: TreapNode)
    requires node.left != null
    requires node.Valid()
    modifies node.repr
    ensures newNode.Valid()
    ensures newNode == old(node.left)
    ensures newNode.left== old(newNode.left)
    ensures newNode.right == node
    ensures node.left == old(node.left.right)
    ensures node.right== old(node.right)
  {
    newNode := node.left;
    var tempNode := newNode.right;
    newNode.right := node;
    node.repr := node.repr - newNode.repr;
    node.left := tempNode;
    if(tempNode != null) {
      // need to add repr of tempNode into node to maintain validity
      node.repr := node.repr + tempNode.repr + {tempNode};
    }
    newNode.repr := newNode.repr + node.repr;
    return newNode;
  }

  // To allow for different implementation of RNG
  // to be easily swapped. Change signature if needed
  method RandomNumberGenerator() returns (priority: int) {
    return -1;
  }
}

// Used for testing
method Main() {
  var treap := new Treap();
  treap.Insert(3);
  treap.InOrderTraversal();
  var result := treap.RandomNumberGenerator();
  print (result);
}
