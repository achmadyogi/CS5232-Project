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

  method Insert(value: int)
    modifies repr
    requires Valid()
    ensures Valid()
    ensures fresh(repr - old(repr))
  {
    var newRoot := InsertNode(root, value);
    root := newRoot;
    repr := root.repr + {this};
  }

  method InsertNode(currNode: TreapNode?, value: int)
    returns (newNode: TreapNode)
    requires currNode != null ==> currNode.Valid()
    modifies if currNode != null then currNode.repr else {}
    ensures currNode == null ==> fresh(newNode.repr)
    ensures currNode != null ==> fresh(newNode.repr - old(currNode.repr))
    ensures newNode.Valid()
    decreases if currNode != null then currNode.repr else {}
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
      currNode.repr := currNode.repr + currNode.left.repr;
      // Do rotation if needed
      newNode := currNode;
      if (currNode.left.priority > currNode.priority) {
        newNode := RotateRight(currNode);
      }
      return newNode;
    } else {
      var newNodeRight := InsertNode(currNode.right, value);
      currNode.right := newNodeRight;
      currNode.repr := currNode.repr + currNode.right.repr;
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
    modifies repr
    requires Valid()
    ensures Valid()
    ensures fresh(repr - old(repr))
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

  method InOrderTraversal(node: TreapNode?)
    requires node != null ==> node.Valid()
    decreases if node != null then node.repr else {}
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
    decreases if node != null then node.repr else {}
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

  method RotateRight(node: TreapNode)
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
}

// Used for testing
method Main() {
  var treap := new Treap();
  treap.Insert(3);
  treap.Insert(4);
  treap.Insert(2);
  treap.Insert(1);
  treap.Insert(10);
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
  treap.PreOrderTraversal(treap.root);

  // var result := treap.RandomNumberGenerator();
}
