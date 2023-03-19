include "TreapNode.dfy"

class Treap {
  /** ---- Ghost Information ---- */
  ghost var Values: set<int>
  ghost var Priorities: set<int>
  ghost var Repr: set<object>

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    // This class must be inside set Repr
    && this in Repr
    // Make sure everything is empty if the root is not set
    && (root == null ==> Values == {} && Priorities == {})
    // This tree must hold the same information with the root 
    && (root != null ==> 
        && root in Repr 
        && root.Repr <= Repr
        && this !in root.Repr
        && root.Valid() && root.ValidHeap()
        && Values == root.Values
        && Priorities == root.Priorities)
  }

  /** ---- Class Attributes ---- */
  var root: TreapNode?

  constructor () 
    ensures Valid() && fresh(Repr)
    ensures Values == {} && Priorities == {}
  {
    this.root := null;
    Repr := {this};
    Values := {};
    Priorities := {};
  }

  /** ----- Class Methods ------ */
  method Build(values: array<int>) {}

  method Insert(val: int)
    requires Valid()
    modifies Repr;
    ensures Valid() && fresh(Repr - old(Repr))
  {
    var priority: int := val * 123 % 1000; // TODO: define a proper priority
    if (root == null) {
      root := new TreapNode(val, priority);
      Repr := root.Repr + {this};
      Values := root.Values;
      Priorities := root.Priorities;
    }

    // TODO: assert priority
  }

  static method InsertHelper(val: int, priority: int, node: TreapNode) returns (head: TreapNode?)
    requires node.Valid() && node.ValidHeap()
    modifies node.Repr
    ensures head != null ==> head.Valid() && head.ValidHeap()
    ensures node.Valid() && node.ValidHeap()
    decreases node.Repr
  {
    head := null;
    if (node.value == val) {
      head := node;
    } else {
      if (val < node.value) {
        if (node.left == null && priority > node.priority) {
          var abc := new TreapNode(val, priority);
          node.left := abc;
          node.Repr := {node} + node.left.Repr + if node.right != null then node.right.Repr else {};
          node.Values := {node.value} + node.left.Values + if node.right != null then node.right.Values else {};
          node.Priorities := {node.priority} + node.left.Priorities + if node.right != null then node.right.Priorities else {};
          head := node;
          if (node.left.priority > node.priority) {
            head := RotateRight(node);
          }
          assert node.Valid() && node.ValidHeap();
        } else if (node.left != null) {
          // var leftSide := InsertHelper(val, priority, node.left);
          // if (leftSide != null) {
          //   node.Repr := {node} + leftSide.Repr + if node.right != null then node.right.Repr else {};
          //   node.Values := {node.value} + leftSide.Values + if node.right != null then node.right.Values else {};
          //   node.Priorities := {node.priority} + leftSide.Priorities + if node.right != null then node.right.Priorities else {};
          //   node.left := leftSide;
          //   head := node;
          //   if (node.left.priority > node.priority) {
          //     head := RotateRight(node);
          //   }
          // }
        } 
      } else {
        if (node.right == null && priority > node.priority) {
          var abc := new TreapNode(val, priority);
          node.right := abc;
          node.Repr := {node} + node.right.Repr + if node.left != null then node.left.Repr else {};
          node.Values := {node.value} + node.right.Values + if node.left != null then node.left.Values else {};
          node.Priorities := {node.priority} + node.right.Priorities + if node.left != null then node.left.Priorities else {};
          head := node;
          if (node.right.priority > node.priority) {
            head := RotateLeft(node);
          }
        }
        assert node.Valid() && node.ValidHeap(); 
      } 
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

  // // Recursive search using nodes
  static method SearchNode(currRoot: TreapNode, val: int)
    returns (node: TreapNode?)
    requires currRoot.Valid() && currRoot.ValidHeap()
    ensures if node != null then node.value == val else true
    decreases currRoot.Repr
  {
    if (currRoot.value == val) {
      return currRoot;
    }
    if (currRoot.value < val && currRoot.right != null) {
      var ans := SearchNode(currRoot.right, val);
      return ans;
    }
    if (currRoot.value > val && currRoot.left!= null) {
      var ans := SearchNode(currRoot.left, val);
      return ans;
    }
    return null;
  }

  static method PreOrderTraversal(node: TreapNode?) 
    requires node != null ==> node.Valid() && node.ValidHeap();
    decreases if node != null then node.Repr else {}
  {
    if (node == null) {
      return;
    } else {
      print node.value, "|", node.priority, " ";
      PreOrderTraversal(node.left);
      PreOrderTraversal(node.right);
    }
  }

  static method RotateLeft(node: TreapNode) returns (newNode: TreapNode)
    requires node.Valid() // The heap must NOT be valid
    requires node.ValidRotateLeft()
    modifies node.Repr
    ensures newNode.Valid() && newNode.ValidHeap()
    ensures node.Valid() && node.ValidHeap()
  {
    newNode := node.right;
    var tempNode := newNode.left;

    node.right:= tempNode;
    node.Repr := node.Repr - newNode.Repr;
    node.Repr := node.Repr + if node.right != null then node.right.Repr else {};

    node.Values := node.Values - newNode.Values;
    node.Values := node.Values + if node.right != null then node.right.Values else {};

    node.Priorities := {node.priority} 
                    + (if node.left != null then node.left.Priorities else {})
                    + (if node.right != null then node.right.Priorities else {});

    newNode.left:= node;
    newNode.Repr := newNode.Repr - if tempNode != null then tempNode.Repr else {};
    newNode.Repr := newNode.Repr + node.Repr;

    newNode.Values := newNode.Values - if tempNode != null then tempNode.Values else {};
    newNode.Values := newNode.Values + node.Values;

    newNode.Priorities := {newNode.priority}
                        + newNode.left.Priorities
                        + (if newNode.right != null then newNode.right.Priorities else {});
    return newNode;
  }

  static method RotateRight(node: TreapNode) returns (newNode: TreapNode)
    requires node.Valid() // The heap must NOT be valid
    requires node.ValidRotateRight()
    modifies node.Repr
    ensures newNode.Valid() && newNode.ValidHeap()
    ensures node.Valid() && node.ValidHeap()
  {
    newNode := node.left;
    var tempNode := newNode.right;

    node.left:= tempNode;
    node.Repr := node.Repr - newNode.Repr;
    node.Repr := node.Repr + if node.left != null then node.left.Repr else {};

    node.Values := node.Values - newNode.Values;
    node.Values := node.Values + if node.left != null then node.left.Values else {};

    node.Priorities := {node.priority} 
                    + (if node.right != null then node.right.Priorities else {})
                    + (if node.left != null then node.left.Priorities else {});

    newNode.right:= node;
    newNode.Repr := newNode.Repr - if tempNode != null then tempNode.Repr else {};
    newNode.Repr := newNode.Repr + node.Repr;

    newNode.Values := newNode.Values - if tempNode != null then tempNode.Values else {};
    newNode.Values := newNode.Values + node.Values;

    newNode.Priorities := {newNode.priority}
                        + newNode.right.Priorities
                        + (if newNode.left != null then newNode.left.Priorities else {});
    return newNode;
  }

  // To allow for different implementation of RNG
  // to be easily swapped. Change signature if needed
  method RandomNumberGenerator() returns (priority: int) {
    return -1;
  }
}

// Used for testing
method Main()
{
  var treap := new Treap();
  // assert fresh(treap);
  treap.Insert(3);
  if (treap.root != null) {
    var check := Treap.InsertHelper(4,517, treap.root);
    Treap.PreOrderTraversal(check);
    if (check != null) {
      var search := Treap.SearchNode(check, 4);
      if (search != null) {
        print "\n",search.value,"|",search.priority;
      }
    }
    assert treap.root.Valid() && treap.root.ValidHeap();
    assert check != null ==> check.Valid() && check.ValidHeap();
    treap.Repr := {treap} + treap.root.Repr;
    treap.Values := treap.Values + treap.root.Values;
    treap.Priorities := treap.Priorities + treap.root.Priorities;
    // assert treap.Valid();
  }
  // var result := treap.RandomNumberGenerator();
  // print (result);
}
