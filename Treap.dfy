include "TreapNode.dfy"

class Treap {

  var root: TreapNode?
  var prioritySet: set<int> //Keeps track of what priority was used.

  ghost var Repr: set<object>
  ghost var Values : set<int>

  constructor ()
    ensures Valid() && fresh(Repr) && Values == {}
  {
    root := null;
    Repr := {this};
    Values := {};
  }

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    this in Repr &&
    (
    root != null ==>
      && root in Repr
      && root.Repr <= Repr
      && root.Valid()
      && Values == root.Values
         )
    && (root == null ==> Values == {})
  }


  method Build(values: array<int>) {}

  method Insert(value: int)
    modifies Repr
    requires Valid()
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures Values == old(Values) + {value}
  {
    var newRoot := InsertNode(root, value);
    root := newRoot;
    Repr := root.Repr + {this};
    Values := Values + {value};
  }

  method InsertNode(currNode: TreapNode?, value: int)
    returns (newNode: TreapNode)
    requires currNode != null ==> currNode.Valid()
    modifies if currNode != null then currNode.Repr else {}
    ensures currNode == null ==> fresh(newNode.Repr)
    ensures currNode != null ==> fresh(newNode.Repr - old(currNode.Repr))
    ensures newNode.Valid()
    ensures if currNode != null then newNode.Values == old(currNode.Values) + {value} else newNode.Values == {value}
    decreases if currNode != null then currNode.Repr else {}
  {
    if (currNode == null) {
      // TODO Change priority and check no repeats
      var priority := value * 123 % 1000;
      newNode := new TreapNode(value, priority);
      assert newNode.Valid();
      return newNode;
    } else if (value < currNode.key) {
      var newNodeLeft := InsertNode(currNode.left, value);
      currNode.left := newNodeLeft;
      currNode.Repr := currNode.Repr + currNode.left.Repr;
      currNode.Values:= currNode.Values + {value};
      // Do rotation if needed
      newNode := currNode;
      if (currNode.left.priority > currNode.priority) {
        newNode := RotateRight(currNode);
      }
      return newNode;
    } else if (value > currNode.key) {
      var newNodeRight := InsertNode(currNode.right, value);
      currNode.right := newNodeRight;
      currNode.Repr := currNode.Repr + currNode.right.Repr;
      currNode.Values:= currNode.Values + {value};
      // Do rotation if needed
      newNode := currNode;
      assert newNode.Valid();
      if (currNode.right.priority > currNode.priority) {
        newNode := RotateLeft(currNode);
      }
      return newNode;
    }
    newNode := currNode;
  }

  method Delete(value: int)
    modifies Repr
    requires Valid()
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures Values == old(Values) - {value}
  {
    if (root != null) {
      root := DeleteNode(root, value);
      if (root != null) {
        Repr := Repr + root.Repr;
        Values := root.Values;
      } else {
        Repr := {this};
        Values := {};
      }
    }
  }

  method DeleteNode(currRoot: TreapNode, value: int)
    returns (newNode: TreapNode?)
    modifies currRoot.Repr
    requires currRoot.Valid()
    ensures newNode != null ==> newNode.Valid()
    ensures newNode != null ==> fresh(newNode.Repr - old(currRoot.Repr))
    ensures newNode != null ==> newNode.Values == old(currRoot.Values) - {value}
    ensures newNode == null ==> old(currRoot.Values) <= {value}
    decreases currRoot.Repr
  {
    newNode := currRoot;
    if (newNode.left != null && value < newNode.key) {
      var newLeft := DeleteNode(newNode.left, value);
      newNode.Values := newNode.Values - {value};
      newNode.left :=  newLeft;
      if(newLeft != null) {
        newNode.Repr := newNode.Repr + newNode.left.Repr;
      }
    } else if (newNode.right != null && value > newNode.key){
      var newRight := DeleteNode(newNode.right, value);
      newNode.Values := newNode.Values - {value};
      newNode.right := newRight;
      if(newRight != null) {
        newNode.Repr := newNode.Repr + newNode.right.Repr;
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
          newNode.Values := newNode.Values - {value};
          newNode.left := newNodeLeft;
          if(newNodeLeft != null) {
            newNode.Repr := newNode.Repr + newNodeLeft.Repr;
          }
        } else {
          newNode := RotateRight(newNode);
          var newNodeRight := DeleteNode(newNode.right, value);
          newNode.Values := newNode.Values - {value};
          newNode.right := newNodeRight;
          if(newNodeRight != null) {
            newNode.Repr := newNode.Repr + newNodeRight.Repr;
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
    decreases currRoot.Repr
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

  method InOrderTraversal(node: TreapNode?)
    requires node != null ==> node.Valid()
    decreases if node != null then node.Repr else {}
  {
    if (node != null) {
      InOrderTraversal(node.left);
      print (node.key, node.priority);
      print "\n";
      InOrderTraversal(node.right);
    }
  }

  method PreOrderTraversal(node: TreapNode?)
    requires node != null ==> node.Valid()
    decreases if node != null then node.Repr else {}
  {
    if (node != null) {
      print (node.key, node.priority);
      print "\n";
      InOrderTraversal(node.left);
      InOrderTraversal(node.right);
    }
  }

  method RotateLeft(node: TreapNode)
    returns (newNode: TreapNode)
    requires node.right != null
    requires node.Valid()
    modifies node.Repr
    ensures old(node.Values) == newNode.Values// No change in content
    ensures old(node.Repr) == newNode.Repr // No change in reachability
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
    node.Repr := node.Repr - newNode.Repr;
    node.Values := node.Values - newNode.Values;
    node.right:= tempNode;
    if(tempNode != null) {
      // need to add Repr of tempNode into node to maintain validity
      assert tempNode.Valid();
      node.Repr := node.Repr + tempNode.Repr;
      node.Values:= node.Values+ tempNode.Values;
    }
    newNode.Repr := newNode.Repr + node.Repr;
    newNode.Values := newNode.Values + node.Values;
  }

  method RotateRight(node: TreapNode)
    returns (newNode: TreapNode)
    requires node.Valid()
    requires node.left != null
    modifies node.Repr
    ensures newNode.Valid()
    ensures old(node.Values) == newNode.Values// No change in content
    ensures old(node.Repr) == newNode.Repr // No change in reachability
    ensures newNode == old(node.left)
    ensures newNode.left == old(newNode.left)
    ensures newNode.right == node
    ensures node.left == old(node.left.right)
    ensures node.right== old(node.right)
  {
    newNode := node.left;
    var tempNode := newNode.right;
    newNode.right := node;
    node.Repr := node.Repr - newNode.Repr;
    node.Values:= node.Values- newNode.Values;
    node.left := tempNode;
    if(tempNode != null) {
      // need to add Repr of tempNode into node to maintain validity
      assert tempNode.Valid();
      node.Repr := node.Repr + tempNode.Repr;
      node.Values:= node.Values+ tempNode.Values;
    }
    newNode.Repr := newNode.Repr + node.Repr;
    newNode.Values := newNode.Values + node.Values;
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
  treap.Insert(4);
  treap.Insert(2);
  treap.Insert(1);
  treap.Insert(10);
  assert treap.Valid();
  treap.InOrderTraversal(treap.root);

  treap.PreOrderTraversal(treap.root);

  var node4 := treap.Search(4);
  print (node4);
  print "\n";

  treap.Delete(4);
  print (node4);
  print "\n";

  var node4AfterDelete := treap.Search(4);
  print (node4AfterDelete);
  print "\n";

  treap.InOrderTraversal(treap.root);

  treap.Delete(10);
  assert treap.Valid();
  treap.PreOrderTraversal(treap.root);

  // var result := treap.RandomNumberGenerator();
}
