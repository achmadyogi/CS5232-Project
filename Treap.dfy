include "TreapNode.dfy"
newtype {:nativeType "byte"} ubyte = x : int | 0 <= x < 256
class Treap {

  var root: TreapNode?

  ghost var Repr: set<object>
  ghost var Values : set<int>
  ghost var Priorities: set<int> //Keeps track of what priority was used.

  constructor ()
    ensures Valid() && fresh(Repr) && Values == {}
  {
    root := null;
    Priorities := {};
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


  static method Build(values: array<int>) returns (treap: Treap)
    requires values.Length != 0
    modifies values;
    ensures treap.Valid()
    ensures fresh(treap.Repr)
  {
    treap := new Treap();
    var i := 0;
    while i < values.Length
      invariant treap.Valid()
      invariant i <= values.Length
      invariant fresh(treap.Repr)
    {
      // assert values[i] !in treap.Values ==> (
      //   forall j :: j in treap.Values ==> (values[i] * 654321/123) % 1000 != (j * 654321/123) % 1000
      // );
      treap.Insert(values[i]);
      i := i + 1;
    }
  }

  method Insert(value: int)
    modifies Repr
    requires Valid()
    // requires value !in Values ==> (
    //   forall i :: i in Values ==> (value * 654321/123) % 1000 != (i * 654321/123) % 1000
    // )
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
    // requires value !in Values ==> (
    //   forall i :: i in Values ==> (value * 654321/123) % 1000 != (i * 654321/123) % 1000
    // )
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
      var priority := RandomNumberGenerator(value);
      // i
      newNode := new TreapNode(value, priority);
      assert newNode.ValidHeap();
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

  static method InOrderTraversal(node: TreapNode?)
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

  static method PreOrderTraversal(node: TreapNode?)
    requires node != null ==> node.Valid()
    decreases if node != null then node.Repr else {}
  {
    if (node != null) {
      print (node.key, node.priority);
      print "\n";
      PreOrderTraversal(node.left);
      PreOrderTraversal(node.right);
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
  method RandomNumberGenerator(val: int) returns (priority: int)
    // requires val !in Values && val < 1000 ==> (
    //   forall i :: i in Values && i < 1000 ==> 
    //   (val * 654321/123) % 1000 != (i * 654321/123) % 1000
    // )
  {
    priority := (val * 654321/123) % 1000;
  }
}

// Used for testing
method Main() {
  print "Insert 3,4,2,1,10\n";
  var treap := new Treap();
  treap.Insert(3);
  treap.Insert(4);
  treap.Insert(2);
  treap.Insert(1);
  treap.Insert(10);
  assert treap.Valid();
  print "In Order Traversal\n";
  Treap.InOrderTraversal(treap.root);
  print "\n";
  print "Pre Order Traversal\n";
  Treap.PreOrderTraversal(treap.root);

  print "\n\n";
  print "      (3, 939)\n";
  print "       /    \\ \n";
  print " (2, 639)   (4,278)\n";
  print "   /           \\ \n";
  print "(1,319)       (10, 196)\n";
  print "\n\n";

  print "Searching a node with key = 4\n";
  var node4 := treap.Search(4);
  if (node4 != null) {
    print "Node found: (",node4.key,",",node4.priority,")\n";
  } else {
    print "null";
  }
  print "\n";

  print "Deleting a node with key = 4\n";
  treap.Delete(4);
  print "\n\n";

  print "Searching a node with key = 4\n";
  var node4AfterDelete := treap.Search(4);
  if (node4AfterDelete != null) {
    print "Node found: (",node4AfterDelete.key,",",node4AfterDelete.priority,")\n";
  } else {
    print "null";
  }
  print "\n";

  print "In Order Traversal\n";
  Treap.InOrderTraversal(treap.root);
  print "\n";

  print "Pre Order Traversal\n";
  Treap.PreOrderTraversal(treap.root);

  print "\n\n";
  print "      (3, 939)\n";
  print "       /    \\ \n";
  print " (2, 639)   (10, 196)\n";
  print "   /           \n";
  print "(1,319)     \n";
  print "\n\n";

  print "Deleting a node with key = 3\n";
  treap.Delete(3);
  assert treap.Valid();

  print "\n";

  print "In Order Traversal\n";
  Treap.InOrderTraversal(treap.root);
  print "\n";

  print "Pre Order Traversal\n";
  Treap.PreOrderTraversal(treap.root);
  print "\n";

  print "\n\n";
  print "      (2, 639)\n";
  print "       /    \\ \n";
  print "  (1,319)   (10, 196)\n";
  print "\n\n";

  // Build
  print "Build a new tree with input values: 3, 4, 2, 1, 10\n";
  var arr := new int[5][3, 4, 2, 1, 10];
  var newTree := Treap.Build(arr);
  print "\n";

  print "In Order Traversal\n";
  Treap.InOrderTraversal(newTree.root);
}
