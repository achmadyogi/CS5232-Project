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
    requires values.Length > 0
    ensures treap.Valid()
    ensures fresh(treap.Repr)
    ensures treap.root != null
    ensures |treap.root.Values| <= values.Length
    ensures forall x :: 0 <= x < values.Length ==> (values[x] in treap.root.Values 
      && values[x] in treap.Values)
  {
    treap := new Treap();
    var i := 0;
    ghost var insertedValues: set<int> := {};
    assert treap.root == null;
    while i < values.Length
      invariant treap.Valid()
      invariant 0 <= i <= values.Length
      invariant fresh(treap.Repr)
      invariant i == 0 || treap.root != null
      invariant |insertedValues| <= i
      invariant treap.Values == insertedValues
      invariant treap.root != null ==> treap.root.Values == insertedValues
      invariant forall x :: 0 <= x < i ==> values[x] in treap.Values && values[x] in treap.root.Values
    {
      assert treap.root != null ==> treap.Values == treap.root.Values;
      treap.Insert(values[i]);
      insertedValues := insertedValues + {values[i]};
      i := i + 1;
    }
  }

  method Insert(value: int)
    modifies Repr
    requires Valid()
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures Values == old(Values) + {value}
    ensures root.Values == old(if root != null then root.Values else {}) + {value}
    ensures Values == root.Values
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

  static method SplitNode(node: TreapNode, val: int) 
    returns (leftNode: TreapNode?, rightNode: TreapNode?)
    requires node.Valid() && node.ValidHeap()
    modifies node.Repr
    modifies if node.left != null then node.left.Repr else {}
    modifies if node.right != null then node.right.Repr else {}
    decreases node.Repr
    ensures leftNode != null ==> leftNode.Valid() && leftNode.ValidHeap()
    ensures rightNode != null ==> rightNode.Valid() && rightNode.ValidHeap()
    ensures old(node.Repr) == (if leftNode != null then leftNode.Repr else {})
      + (if rightNode != null then rightNode.Repr else {})
    ensures old(node.Values) == (if leftNode != null then leftNode.Values else {})
      + (if rightNode != null then rightNode.Values else {})
    ensures leftNode != null && rightNode != null ==> 
      leftNode.Repr !! rightNode.Repr && leftNode.Values !! rightNode.Values
    ensures forall x :: x in (if leftNode != null then leftNode.Values else {}) ==> x <= val
    ensures forall x :: x in (if rightNode != null then rightNode.Values else {}) ==> x > val
    ensures leftNode != null ==> leftNode.priority <= old(node.priority)
    ensures rightNode != null ==> rightNode.priority <= old(node.priority)
  {
    leftNode := null;
    rightNode := null;
    if (node.key == val) {
      if (node.right != null) {
        rightNode := node.right;
        node.Repr := node.Repr - node.right.Repr;
        node.Values := node.Values - node.right.Values;
        node.right := null;
      }
      leftNode := node;
      assert leftNode != null ==> leftNode.Valid() && leftNode.ValidHeap();
      assert rightNode != null ==> rightNode.Valid() && rightNode.ValidHeap();
      return;
    }

    if (node.key > val) {
      // Left
      if (node.left == null) {
        rightNode := node;
        assert leftNode != null ==> leftNode.Valid() && leftNode.ValidHeap();
        assert rightNode != null ==> rightNode.Valid() && rightNode.ValidHeap();
        return;
      } else {
        var left := node.left;
        node.left := null;
        node.Repr := node.Repr - left.Repr;
        node.Values := node.Values - left.Values;
        assert node.Valid() && node.ValidHeap();
        var l, r := SplitNode(left, val);
        assert l != null ==> l.Valid() && l.ValidHeap();
        assert r != null ==> r.Valid() && r.ValidHeap();
        leftNode := l;
        if (r != null) {
          assert forall x :: x in r.Values ==> x in old(left.Values);
          assert r.priority <= old(left.priority);
          node.left := r;
          node.Repr := node.Repr + r.Repr;
          node.Values := node.Values + r.Values;
        }
        rightNode := node;
        assert leftNode != null ==> leftNode.Valid() && leftNode.ValidHeap();
        assert rightNode != null ==> rightNode.Valid() && rightNode.ValidHeap();
      }
    } else {
      // Right
      if (node.right == null) {
        leftNode := node;
        assert leftNode != null ==> leftNode.ValidHeap();
        assert rightNode != null ==> rightNode.ValidHeap();
        return;
      } else {
        var right := node.right;
        node.right := null;
        node.Repr := node.Repr - right.Repr;
        node.Values := node.Values - right.Values;
        assert node.Valid() && node.ValidHeap();
        var l, r := SplitNode(right, val);
        assert l != null ==> l.ValidHeap();
        assert r != null ==> r.ValidHeap();
        rightNode := r;
        if (l != null) {
          assert forall x :: x in l.Values ==> x in old(right.Values);
          assert l.priority <= old(right.priority);
          node.right := l;
          node.Repr := node.Repr + l.Repr;
          node.Values := node.Values + l.Values;
        }
        leftNode := node;
        assert leftNode != null ==> leftNode.ValidHeap();
        assert rightNode != null ==> rightNode.ValidHeap();
      }
    }
  }

    static method Split(tree: Treap, val: int) returns (left: Treap?, right: Treap?)
    requires tree.Valid()
    modifies tree
    modifies if tree.root != null then tree.root.Repr else {}
    ensures left != null ==> left.Valid()
    ensures right != null ==> right.Valid()
    ensures left != null && right != null ==> fresh(right) || fresh(left) // One of the sides must be a new instance
    ensures tree.root != null ==> right != null || left != null // At least one of the sides is not null
    ensures left != null && left.root != null && right != null && right.root != null ==> 
      left.root.Repr !! right.root.Repr && left.root.Values !! right.root.Values
    ensures forall x :: x in (if left != null && left.root != null then left.root.Values else {}) ==> x <= val
    ensures forall x :: x in (if right != null && right.root != null then right.root.Values else {}) ==> x > val
  {
    var root := tree.root;
    tree.Repr := tree.Repr - if root != null then root.Repr else {};
    tree.Values := tree.Values - if root != null then root.Values else {};
    tree.root := null;

    left := null;
    right := null;
    if (root == null) {
      return;
    }

    var leftNode, rightNode := SplitNode(root, val);
    if (leftNode != null) {
      left := new Treap();
      left.root := leftNode;
      left.Repr := left.Repr + leftNode.Repr;
      left.Values := left.Values + leftNode.Values;
    }
    if (rightNode != null) {
      right := new Treap();
      right.root := rightNode;
      right.Repr := right.Repr + rightNode.Repr;
      right.Values := right.Values + rightNode.Values;
    }
  }

  static method Merge(tree1: Treap, tree2: Treap) returns (merged: Treap)
    requires tree1.Valid() && tree2.Valid()
    requires tree1.root != null && tree2.root != null
    requires tree1.root.Repr !! tree2.root.Repr && tree1.root.Values !! tree2.root.Values
    requires forall x, y :: x in tree1.root.Values && y in tree2.root.Values ==> x < y
    modifies tree1, tree2, tree1.root.Repr, tree2.root.Repr;
    ensures fresh(merged)
    ensures merged.Valid()
  {
    merged := new Treap();
    var newRoot := MergeNode(tree1.root, tree2.root);
    merged.root := newRoot;
    merged.Repr := merged.Repr + newRoot.Repr;
    merged.Values := merged.Values + newRoot.Values;
  }

  static method MergeNode(node1: TreapNode, node2:TreapNode) returns (merged: TreapNode)
    requires node1.Valid() && node1.ValidHeap() && node2.Valid() && node2.ValidHeap()
    requires node1.Repr !! node2.Repr && node1.Values !! node2.Values
    requires forall x, y :: x in node1.Values && y in node2.Values ==> x < y
    modifies node1.Repr, node2.Repr
    decreases node1.Repr, node2.Repr
    ensures merged.Values == old(node1.Values) + old(node2.Values)
    ensures merged.Repr == old(node1.Repr) + old(node2.Repr)
    ensures merged.Valid() && merged.ValidHeap()
    ensures merged.priority == node1.priority || merged.priority == node2.priority
  {
    if (node1.priority >= node2.priority) {
      // Pick node1 as a root
      if (node1.right == null) {
        node1.right := node2;
        node1.Repr := node1.Repr + node2.Repr;
        node1.Values := node1.Values + node2.Values;
        assert node1.ValidHeap();
      } else {
        var right := node1.right;
        node1.right := null;
        node1.Repr := node1.Repr - right.Repr;
        node1.Values := node1.Values - right.Values;
        assert node1.ValidHeap();
        var result := MergeNode(right, node2);
        node1.right := result;
        node1.Repr := node1.Repr + result.Repr;
        node1.Values := node1.Values + result.Values;
        assert node1.ValidHeap();
      }
      merged := node1;
    } else {
      // Pick node 2 as a root
      if (node2.left == null) {
        node2.left := node1;
        node2.Repr := node2.Repr + node1.Repr;
        node2.Values := node2.Values + node1.Values;
        assert node1.ValidHeap();
      } else {
        var left := node2.left;
        node2.left := null;
        node2.Repr := node2.Repr - left.Repr;
        node2.Values := node2.Values - left.Values;
        var result := MergeNode(node1, left);
        node2.left := result;
        node2.Repr := node2.Repr + result.Repr;
        node2.Values := node2.Values + result.Values;
        assert node2.ValidHeap();
      }
      merged := node2;
    }
  }

  // static method UnionNode(node1: TreapNode, node2: TreapNode) returns(union: TreapNode)
  //   requires node1.Valid() && node1.ValidHeap() && node2.Valid() && node2.ValidHeap()
  //   modifies node1.Repr, node2.Repr
  //   decreases node1.Repr, node2.Repr
  //   ensures union.Valid() && union.ValidHeap()
  //   ensures union.Repr == old(node1.Repr) + old(node2.Repr)
  //   ensures union.Values == old(node1.Values) + old(node2.Values)
  // {

  //   if (node1.key == node2.key) {
  //     // Use node1 as the root
  //     var left := node1.left;
  //     node1.Repr := node1.Repr - node1.left.Repr;

  //     if (node1.left != null && node2.left != null) {
  //       left := UnionNode(node1.left, node2.left);
  //     } else if (node1.left == null && node2.left != null) {
  //       left := node2.left;
  //     }

  //     var right := node1.right;
  //     if (node1.right != null && node2.right != null) {
  //       right := UnionNode(node1.right, node2.right);
  //     } else if (node1.right == null && node2.right != null) {
  //       left := node2.right;
  //     }

  //     if (left != null) {

  //     }
  //     union := node1;
  //     return;
  //   }

  //   if (node1.priority >= node2.priority) {
  //     // node1 as root -> split node2 using node1's key
  //     var left, right := SplitNode(node2, node1.key);
  //     if (left != null) {
  //       var leftUnion := left;
  //       if (node1.left != null) {
  //         var leftOfNode1 := node1.left;
  //         node1.Repr := node1.Repr - node1.left.Repr;
  //         node1.Values := node1.Values - node1.left.Values;
  //         node1.left := null;
  //         leftUnion := UnionNode(leftOfNode1, left);
  //       }
  //       node1.left := leftUnion;
  //       node1.Repr := node1.Repr + leftUnion.Repr;
  //       node1.Values := node1.Values + leftUnion.Values;
  //     }
  //     if (right != null) {
  //       var rightUnion := right;
  //       if (node1.right != null) {
  //         var rightOfNode1 := node1.right;
  //         node1.Repr := node1.Repr - node1.right.Repr;
  //         node1.Values := node1.Values - node1.right.Values;
  //         node1.right := null;
  //         rightUnion := UnionNode(rightOfNode1, right);
  //       }
  //       node1.right := rightUnion;
  //       node1.Repr := node1.Repr + rightUnion.Repr;
  //       node1.Values := node1.Values + rightUnion.Values;
  //     }
  //     union := node1;
  //   } else {
  //     // node2 as root -> split node1 using node2's key
  //     var left, right := SplitNode(node1, node2.key);
  //     if (left != null) {
  //       var leftUnion := left;
  //       if (node2.left != null) {
  //         var leftOfNode2 := node2.left;
  //         node2.Repr := node2.Repr - node2.left.Repr;
  //         node2.Values := node2.Values - node2.left.Values;
  //         node2.left := null;
  //         leftUnion := UnionNode(leftOfNode2, left);
  //       }
  //       node2.left := leftUnion;
  //       node2.Repr := node2.Repr + leftUnion.Repr;
  //       node2.Values := node2.Values + leftUnion.Values;
  //     }
  //     if (right != null) {
  //       var rightUnion := right;
  //       if (node2.right != null) {
  //         var rightOfNode2 := node2.right;
  //         node2.Repr := node2.Repr - node2.right.Repr;
  //         node2.Values := node2.Values - node2.right.Values;
  //         node2.right := null;
  //         rightUnion := UnionNode(rightOfNode2, right);
  //       }
  //       node2.right := rightUnion;
  //       node2.Repr := node2.Repr + rightUnion.Repr;
  //       node2.Values := node2.Values + rightUnion.Values;
  //     }
  //     union := node2;
  //   }
  // }
}

// Used for testing
method Main() {
  // print "Insert 3,4,2,1,10\n";
  // var treap := new Treap();
  // treap.Insert(3);
  // treap.Insert(4);
  // treap.Insert(2);
  // treap.Insert(1);
  // treap.Insert(10);
  // assert treap.Valid();
  // print "In Order Traversal\n";
  // Treap.InOrderTraversal(treap.root);
  // print "\n";
  // print "Pre Order Traversal\n";
  // Treap.PreOrderTraversal(treap.root);

  // print "\n\n";
  // print "      (3, 939)\n";
  // print "       /    \\ \n";
  // print " (2, 639)   (4,278)\n";
  // print "   /           \\ \n";
  // print "(1,319)       (10, 196)\n";
  // print "\n\n";

  // print "Searching a node with key = 4\n";
  // var node4 := treap.Search(4);
  // if (node4 != null) {
  //   print "Node found: (",node4.key,",",node4.priority,")\n";
  // } else {
  //   print "null";
  // }
  // print "\n";

  // print "Deleting a node with key = 4\n";
  // treap.Delete(4);
  // print "\n\n";

  // print "Searching a node with key = 4\n";
  // var node4AfterDelete := treap.Search(4);
  // if (node4AfterDelete != null) {
  //   print "Node found: (",node4AfterDelete.key,",",node4AfterDelete.priority,")\n";
  // } else {
  //   print "null";
  // }
  // print "\n";

  // print "In Order Traversal\n";
  // Treap.InOrderTraversal(treap.root);
  // print "\n";

  // print "Pre Order Traversal\n";
  // Treap.PreOrderTraversal(treap.root);

  // print "\n\n";
  // print "      (3, 939)\n";
  // print "       /    \\ \n";
  // print " (2, 639)   (10, 196)\n";
  // print "   /           \n";
  // print "(1,319)     \n";
  // print "\n\n";

  // print "Deleting a node with key = 3\n";
  // treap.Delete(3);
  // assert treap.Valid();

  // print "\n";

  // print "In Order Traversal\n";
  // Treap.InOrderTraversal(treap.root);
  // print "\n";

  // print "Pre Order Traversal\n";
  // Treap.PreOrderTraversal(treap.root);
  // print "\n";

  // print "\n\n";
  // print "      (2, 639)\n";
  // print "       /    \\ \n";
  // print "  (1,319)   (10, 196)\n";
  // print "\n\n";

  // Build
  print "Build a new tree with input values: 3, 4, 2, 1, 10\n";
  var arr := new int[10][3, 4, 2, 1, 10, 8, 7, 6, 9, 5];
  var newTree := Treap.Build(arr);
  print "\n";

  print "In Order Traversal\n";
  Treap.InOrderTraversal(newTree.root);
  print "\n";
  Treap.PreOrderTraversal(newTree.root);

  print "\n\n";
  var left, right := Treap.Split(newTree, 5);
  if (left != null && left.root != null) {
    Treap.InOrderTraversal(left.root);
    print "\n";
    Treap.PreOrderTraversal(left.root);
  }
  print "\n\n";
  if (right != null && right.root != null) {
    Treap.InOrderTraversal(right.root);
    print "\n";
    Treap.PreOrderTraversal(right.root);
  }
  print "\n\n";
  // var arr1 := new int[5][3, 4, 2, 1, 5];
  // var arr2 := new int[5][10, 8, 7, 6, 9];
  // var tree1 := Treap.Build(arr1);
  // var tree2 := Treap.Build(arr2);
  // assert tree1.root != null && tree2.root != null;
  // assert tree1.root.Values * tree2.root.Values == {};
  // assert forall x, y :: x in tree1.root.Values && y in tree2.root.Values ==> x < y;
  if (left != null && left.root != null && right != null && right.root != null) {
    var merged := Treap.Merge(left, right);
  }
  // Treap.InOrderTraversal(merged.root);

  // 5 - 4 - 3 - 2 - 1
}
