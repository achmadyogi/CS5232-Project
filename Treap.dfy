include "TreapNode.dfy"

class Treap {
  var root: TreapNode?
  var prioritySet: set<int> //Keeps track of what priority was used.
  ghost var repr: set<object> //Keeps track of what priority was used.

  constructor ()
    ensures Valid()
  {
    this.root := null;
    repr := {this};
  }

  ghost predicate Valid()
    reads this, root, if root != null then root.repr else {}
  {
    && root != null ==> (root.Valid() && root in repr)
  }


  method Build(values: array<int>) {}
  method Insert(value: int) {}

  // method Delete(value: int)
  //   requires Valid()
  //   modifies this
  //   ensures Valid()
  // {
  //   if (root != null) {
  //     var parent, node := SearchParentNode(root, value);
  //     if (node != null) {
  //       DeleteNode(parent, node);
  //     }
  //   }
  // }

  // method DeleteNode(parent: TreapNode?, node: TreapNode)
  //   requires Valid()
  //   requires node.Valid()
  //   requires parent != null ==> parent.Valid()
  //   requires parent != null ==> node == parent.left || node == parent.right
  //   modifies this, parent, node
  //   ensures parent != null ==> parent.Valid()
  //   ensures Valid()
  // {
  //   if(node.IsLeaf()) {
  //     if(parent != null) {
  //       if(parent.left == node) {
  //         parent.repr := parent.repr - parent.left.repr;
  //         parent.left := null;
  //         return;
  //       }
  //       // if(parent.right == node) {
  //       //   parent.right := null;
  //       //   return;
  //       // }
  //     }
  //   }
  // }

  method Delete(value: int)
    modifies this, root, if root != null then root.repr else {}
    requires Valid()
    ensures Valid()
  {
    if (root != null) {
      this.root := DeleteNode(root, value);
      if (root != null) {
        repr := repr + root.repr;
      }
    }
  }

  method editroot()
    modifies this, root, if root != null then root.repr else {}
    requires Valid()
    ensures Valid()
  {
    if(root != null) {
      root := addleft(root);
      repr := repr + root.repr;
    }
  }

  method addleft(node: TreapNode)
    returns (newNode:TreapNode)
    modifies node.repr
    requires node.Valid()
    ensures newNode.Valid()
  {
    newNode := node;
    assert newNode.Valid();
    if (newNode.left == null){
      newNode.left := new TreapNode(1,2);
      newNode.repr := newNode.repr + newNode.left.repr;
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
    assert newNode.Valid();
    if (newNode.left != null && value < newNode.key) {
      assert newNode.left.Valid();
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

  // method BubbleDown(currParent: TreapNode?, node: TreapNode)
  //   requires Valid()
  //   requires node.Valid()
  //   requires currParent != null ==> currParent.Valid()
  //   requires currParent != null ==> (currParent.left == node || currParent.right == node)
  //   modifies this, currParent, node, node.repr
  //   ensures currParent != null && currParent.left == node ==> currParent.repr == old(currParent.repr)
  //   ensures Valid()
  //   {
  //     // node has children
  //     if(!node.IsLeaf()) {
  //       var left := node.left;
  //       var right := node.right;
  //       var newRoot := node;
  //       if(left != null && right != null) {
  //         // rotate right if left priority is bigger
  //         if(left.priority > right.priority) {
  //           newRoot := RotateRight(node);
  //         } else {
  //           newRoot := RotateLeft(node);
  //         }
  //       } else if (right != null) {
  //           newRoot := RotateLeft(node);
  //       } else if (left != null) {
  //           newRoot := RotateRight(node);
  //       }
  //       // if(currParent != null) {
  //       //   if(currParent.left == node) {
  //       //     currParent.left := newRoot;
  //       //   }
  //       // }
  //     }
  //   }

  // Initial search entry point
  method Search(value: int) returns (node: TreapNode?)
    requires Valid() // Tree is valid before search
    ensures Valid() // Tress is valid after search
    ensures if node != null then node.key == value else true // Return node has correct value
    ensures if node != null then node.Valid() else true // Return node is valid
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
  method ParentNode(currRoot: TreapNode, targetNode: TreapNode)
    returns (parent: TreapNode?)
    requires Valid()
    requires currRoot.Valid()
    requires targetNode.Valid()
    ensures parent != null ==> parent.Valid()
    ensures parent != null ==> (parent.left == targetNode || parent.right == targetNode)
    ensures Valid()
    decreases currRoot.repr
  {
    if (currRoot == targetNode) {
      return null;
    }
    if (currRoot.left == targetNode || currRoot.right == targetNode) {
      return currRoot;
    }
    if (targetNode.key > currRoot.key && currRoot.right != null) {
      parent := ParentNode(currRoot.right, targetNode);
      return parent;
    }
    if (targetNode.key <= currRoot.key && currRoot.left!= null) {
      parent := ParentNode(currRoot.left, targetNode);
      return parent;
    }
    return null;
  }

  // ghost method DeleteRepr(currRoot: TreapNode, node: TreapNode)
  //   requires Valid()
  //   requires currRoot.Valid()
  //   modifies currRoot.repr
  //   // ensures Valid()
  //   decreases currRoot.repr
  // {
  //   if(node in currRoot.repr) {
  //     if(currRoot.left != null && node in currRoot.left.repr) {
  //       DeleteRepr(currRoot.left, node);
  //     }
  //     if(currRoot.right != null && node in currRoot.right.repr) {
  //       DeleteRepr(currRoot.right, node);
  //     }
  //     currRoot.repr := currRoot.repr - {node};
  //   }
  // }


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

  method test()
    modifies this
    requires Valid()
    ensures Valid()
  {
    var root := new TreapNode(5,10);
    var left := new TreapNode(2,4);
    var right := new TreapNode(7,5);
    root.left := left;
    root.right := right;
    root.repr := {root, left, right};
    assert left.Valid();
    assert right.Valid();
    assert root.Valid();
    this.root := root;
    // Delete(5);
  }

}

// Used for testing
method Main() {
  var treap := new Treap();
  treap.test();

  var result := treap.Search(10);
  var result2 := treap.Search(5);
  treap.Delete(5);
  print (result);
  print ("\n");
  print (result2);
}
