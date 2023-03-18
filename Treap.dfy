include "TreapNode.dfy"

class Treap {

  var root: TreapNode?
  var prioritySet: set<int> //Keeps track of what priority was used.

  ghost var repr: set<object>

  constructor ()
    ensures Valid() && fresh(repr)
  {
    root := null;
    repr := {this};
  }

  ghost predicate Valid()
    reads this, repr
    ensures Valid() ==> this in repr
  {
    this in repr &&
    (
    root != null ==>
      && root in repr
      && root.repr <= repr
      && root.Valid()
         )
  }


  method Build(values: array<int>) {}

  method Delete(value: int)
    modifies repr
    requires Valid()
    ensures Valid()
  {
    if (root != null) {
      root := DeleteNode(root, value);
      if (root != null) {
        repr := repr + root.repr;
      } else {
        repr := {this};
      }
    }
  }

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

  method DeleteNode(currRoot: TreapNode, value: int)
    returns (newNode: TreapNode?)
    modifies currRoot.repr
    requires currRoot.Valid()
    ensures newNode != null ==> newNode.Valid()
    ensures newNode != null ==> fresh(newNode.repr - old(currRoot.repr))
    decreases currRoot.repr
  {
    newNode := currRoot;
    if (newNode.left != null && value < newNode.key) {
      var newLeft := DeleteNode(newNode.left, value);
      newNode.left :=  newLeft;
      if(newLeft != null) {
        newNode.repr := newNode.repr + newNode.left.repr;
      }
    } else if (newNode.right != null && value > newNode.key){
      var newRight := DeleteNode(newNode.right, value);
      newNode.right := newRight;
      if(newRight != null) {
        newNode.repr := newNode.repr + newNode.right.repr;
      }
    } else if (newNode.key == value) {
      // Delete
      if (newNode.IsLeaf()) {
        newNode := null;
      } else if (newNode.left == null) {
        newNode := newNode.right;
      } else if (newNode.right == null){
        newNode := newNode.left;
      } else {
        // Check priority and rotate accordingly
        if (newNode.right.priority >= newNode.left.priority) {
          newNode := RotateLeft(newNode);
          var newNodeLeft := DeleteNode(newNode.left, value);
          newNode.left := newNodeLeft;
          if(newNodeLeft != null) {
            newNode.repr := newNode.repr + newNodeLeft.repr;
          }
        } else {
          newNode := RotateRight(newNode);
          var newNodeRight := DeleteNode(newNode.right, value);
          newNode.right := newNodeRight;
          if(newNodeRight != null) {
            newNode.repr := newNode.repr + newNodeRight.repr;
          }
        }
      }
    }
  }

  // Initial search entry point
  method Search(value: int) returns (node: TreapNode?)
    requires Valid() // Tree is valid before search
    ensures Valid() // Tress is valid after search
    ensures node != null ==> node.key == value // Return node has correct value
    ensures node != null ==> node.Valid() // Return node is valid
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
    ensures node != null ==> node.key == value
    ensures node != null ==> node.Valid()
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

  // Recursive search with parent node returned too, useful for delete
  // method ParentNode(currRoot: TreapNode, targetNode: TreapNode)
  //   returns (parent: TreapNode?)
  //   requires Valid()
  //   requires currRoot.Valid()
  //   requires targetNode.Valid()
  //   ensures parent != null ==> parent.Valid()
  //   ensures parent != null ==> (parent.left == targetNode || parent.right == targetNode)
  //   ensures Valid()
  //   decreases currRoot.repr
  // {
  //   if (currRoot == targetNode) {
  //     return null;
  //   }
  //   if (currRoot.left == targetNode || currRoot.right == targetNode) {
  //     return currRoot;
  //   }
  //   if (targetNode.key > currRoot.key && currRoot.right != null) {
  //     parent := ParentNode(currRoot.right, targetNode);
  //     return parent;
  //   }
  //   if (targetNode.key <= currRoot.key && currRoot.left!= null) {
  //     parent := ParentNode(currRoot.left, targetNode);
  //     return parent;
  //   }
  //   return null;
  // }

  method InOrderTraversal()
  {
    if (this.root != null) {
      print this.root.key;
    }
  }

  static method RotateLeft(node: TreapNode)
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
      assert tempNode.Valid();
      node.repr := node.repr + tempNode.repr;
    }
    newNode.repr := newNode.repr + node.repr;
  }

  static method RotateRight(node: TreapNode)
    returns (newNode: TreapNode)
    requires node.Valid()
    requires node.left != null
    modifies node.repr
    ensures newNode.Valid()
    ensures old(node.repr) == newNode.repr // No change in reachability
    ensures newNode == old(node.left)
    ensures newNode.left == old(newNode.left)
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
      assert tempNode.Valid();
      node.repr := node.repr + tempNode.repr;
    }
    newNode.repr := newNode.repr + node.repr;
  }

  // To allow for different implementation of RNG
  // to be easily swapped. Change signature if needed
  method RandomNumberGenerator() returns (priority: int) {
    return -1;
  }

  // method test()
  //   modifies this
  //   requires Valid()
  //   ensures Valid()
  // {
  //   var root := new TreapNode(5,10);
  //   var left := new TreapNode(2,4);
  //   var right := new TreapNode(7,5);
  //   root.left := left;
  //   root.right := right;
  //   root.repr := {root, left, right};
  //   repr := {this, root, left, right};
  //   assert left.Valid();
  //   assert right.Valid();
  //   assert root.Valid();
  //   this.root := root;
  // }

}

// Used for testing
method Main() {
  var treap := new Treap();
  // treap.test();

  var result1 := treap.Search(10);
  var result2 := treap.Search(5);
  treap.Delete(5);
  treap.Insert(3);
  treap.InOrderTraversal();
  var result := treap.RandomNumberGenerator();
  print (result1);
  print ("\n");
  print (result2);
}
