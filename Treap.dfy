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
      && root.ValidHeap()
      && Values == root.Values
         )
    && (root == null ==> Values == {} )
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
    requires currNode != null ==> currNode.ValidHeap()
    modifies if currNode != null then currNode.Repr else {}
    ensures currNode == null ==> fresh(newNode.Repr)
    ensures currNode != null ==> fresh(newNode.Repr - old(currNode.Repr))
    ensures newNode.ValidHeap()
    ensures if currNode != null then newNode.Values == old(currNode.Values) + {value} else newNode.Values == {value}
    ensures newNode.left != null && currNode != null ==> newNode.left.priority <= currNode.priority
    ensures newNode.right != null && currNode != null ==> newNode.right.priority <= currNode.priority
    decreases if currNode != null then currNode.Repr else {}
  {
    if (currNode == null) {
      // TODO Change priority and check no repeats
      var priority := value * 123 % 1000;
      newNode := new TreapNode(value, priority);
      assert newNode.ValidHeap();
      return newNode;
    } else if (value < currNode.key) {
      var newNodeLeft := InsertNode(currNode.left, value);
      // assert newNodeLeft.right != null ==> newNodeLeft.right.priority <= cu
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
    requires currRoot.ValidHeap()
    ensures newNode != null ==> newNode.ValidHeap()
    ensures newNode != null ==> fresh(newNode.Repr - old(currRoot.Repr))
    ensures newNode != null ==> newNode.Values == old(currRoot.Values) - {value}
    ensures newNode == null ==> old(currRoot.Values) <= {value}
    ensures newNode != null ==> newNode.priority <= currRoot.priority
    ensures currRoot.key == value ==> (newNode == old(currRoot.left) || newNode == old(currRoot.right))
    decreases currRoot.Repr
  {
    newNode := currRoot;
    if (newNode.left != null && value < newNode.key) {
      var newLeft := DeleteNode(newNode.left, value);
      newNode.Values := newNode.Values - {value};
      newNode.left :=  newLeft;
      if(newLeft != null) {
        assert newLeft.ValidHeap();
        newNode.Repr := newNode.Repr + newNode.left.Repr;
      }
      return newNode;
    }

    if (newNode.right != null && value > newNode.key){
      var newRight := DeleteNode(newNode.right, value);
      newNode.Values := newNode.Values - {value};
      newNode.right := newRight;
      if(newRight != null) {
        newNode.Repr := newNode.Repr + newNode.right.Repr;
      }
      return newNode;
    }

    if (newNode.key == value) {
      if (newNode.IsLeaf()) {
        newNode := null;
      } else if (newNode.left == null) {
        newNode := newNode.right;
      } else if (newNode.right == null){
        newNode := newNode.left;
      } else {
        // Check priority and rotate accordingly
        if (newNode.right.priority > newNode.left.priority) {
          newNode := RotateLeft(newNode);
          assert newNode.left.ValidHeap();
          var newNodeLeft := DeleteNode(newNode.left, value);
          newNode.Values := newNode.Values - {value};
          if(newNodeLeft != null) {
            newNode.Repr := newNode.Repr + newNodeLeft.Repr;
          }
          newNode.left := newNodeLeft;
        } else {
          newNode := RotateRight(newNode);
          assert newNode.right.ValidHeap();
          var newNodeRight := DeleteNode(newNode.right, value);

          newNode.Values := newNode.Values - {value};
          if(newNodeRight != null) {
            newNode.Repr := newNode.Repr + newNodeRight.Repr;
          }
          newNode.right := newNodeRight;
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
    ensures newNode.right == old(node.right.right)
    ensures newNode.left == node
    ensures node.right == old(node.right.left)
    ensures node.left == old(node.left)
    ensures old(node.ValidHeap()) ==> newNode.left.ValidHeap()
    ensures old(node.ValidHeap()) && newNode.right != null ==> newNode.right.ValidHeap()
    ensures old(node.ValidHeap()) && old(node.left) != null && old(node.left.priority) <= old(node.right.priority) ==> newNode.priority >= newNode.left.left.priority
    ensures old(node.ValidHeap()) && old(node.right.left) != null ==> newNode.priority >= newNode.left.right.priority

    // For insert
    ensures old(node.right.ValidHeap())
            && old(node.left) == null
            && old(node.right.priority) > node.priority
            && (old(node.right.left) != null ==> old(node.right.left.priority) <= node.priority)
            ==> newNode.ValidHeap()

    ensures old(node.right.ValidHeap())
            && (old(node.left) != null && old(node.left.ValidHeap()) && old(node.left.priority) <= old(node.priority))
            && old(node.right.priority) > node.priority
            && (old(node.right.left) != null ==> old(node.right.left.priority) <= node.priority)
            ==> newNode.ValidHeap()
  {
    newNode := node.right;
    var tempNode := newNode.left;
    assert newNode.ValidHeap() ==> newNode.ValidHeap();
    newNode.left:= node;
    node.Repr := node.Repr - newNode.Repr;
    node.Values := node.Values - newNode.Values;
    // node.Priorities:= node.Priorities- newNode.Priorities;
    node.right:= tempNode;
    if(tempNode != null) {
      // need to add Repr of tempNode into node to maintain validity
      assert tempNode.Valid();
      node.Repr := node.Repr + tempNode.Repr;
      node.Values:= node.Values+ tempNode.Values;
      // node.Priorities:= node.Priorities+ tempNode.Priorities;
    }
    newNode.Repr := newNode.Repr + node.Repr;
    newNode.Values := newNode.Values + node.Values;
    // newNode.Priorities:= newNode.Priorities+ node.Priorities;
  }

  method RotateRight(node: TreapNode)
    returns (newNode: TreapNode)
    requires node.Valid()
    requires node.left != null
    modifies node.Repr
    ensures newNode.Valid()
    ensures old(node.Values) == newNode.Values// No change in values
    ensures old(node.Repr) == newNode.Repr // No change in reachability
    ensures newNode == old(node.left)
    ensures newNode.left == old(node.left.left)
    ensures newNode.right == node
    ensures node.left == old(node.left.right)
    ensures node.right== old(node.right)

    // For Delete
    ensures old(node.ValidHeap()) ==> newNode.right.ValidHeap()
    ensures old(node.ValidHeap()) && newNode.left!= null ==> newNode.left.ValidHeap()
    ensures old(node.ValidHeap()) && old(node.right) != null && old(node.left.priority) >= old(node.right.priority) ==> newNode.priority >= newNode.right.right.priority
    ensures old(node.ValidHeap()) && old(node.left.right) != null ==> newNode.priority >= newNode.right.left.priority

    // For insert
    ensures old(node.left.ValidHeap())
            && old(node.right) == null
            && old(node.left.priority) > node.priority
            && (old(node.left.right) != null ==> old(node.left.right.priority) <= node.priority)
            ==> newNode.ValidHeap()

    ensures old(node.left.ValidHeap())
            && (old(node.right) != null && old(node.right.ValidHeap()) && old(node.right.priority) <= old(node.priority))
            && old(node.left.priority) > node.priority
            && (old(node.left.right) != null ==> old(node.left.right.priority) <= node.priority)
            ==> newNode.ValidHeap()
  {
    newNode := node.left;
    var tempNode := newNode.right;
    assert newNode.ValidHeap() ==> newNode.ValidHeap();
    newNode.right := node;
    node.Repr := node.Repr - newNode.Repr;
    node.Values:= node.Values- newNode.Values;
    // node.Priorities := node.Priorities - newNode.Priorities;
    node.left := tempNode;
    if(tempNode != null) {
      // need to add Repr of tempNode into node to maintain validity
      assert tempNode.Valid();
      node.Repr := node.Repr + tempNode.Repr;
      node.Values:= node.Values+ tempNode.Values;
      // node.Priorities:= node.Priorities+ tempNode.Priorities;
    }
    newNode.Repr := newNode.Repr + node.Repr;
    newNode.Values := newNode.Values + node.Values;
    // newNode.Priorities:= newNode.Priorities+ node.Priorities;
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
  print "\n";
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
  print "\n";
  treap.PreOrderTraversal(treap.root);

  treap.Delete(10);
  assert treap.Valid();
  treap.InOrderTraversal(treap.root);
  print "\n";
  treap.PreOrderTraversal(treap.root);
  // var result := treap.RandomNumberGenerator();
}
