class TreapNode {
  const key: int
  const priority: int
  var left: TreapNode?
  var right: TreapNode?

  // Use to ensure nodes are acyclic, i.e tree structure
  // Ensures recursive methods can terminate
  ghost var Repr: set<TreapNode>
  // Needed to check for BST property
  ghost var Values: set<int>

  ghost predicate Valid()
    reads this, Repr
  {
    && this in Repr // node is reachable to itself
    && ( left != null ==>
         && left in Repr
         && this !in left.Repr
         && left.Repr <= Repr
         && left.Valid()
         && forall x :: x in left.Values ==> x < key  // BST property
                        )
    && ( right != null ==>
         && right in Repr
         && this !in right.Repr
         && right.Repr <= Repr
         && right.Valid()
         && forall x :: x in right.Values ==> x > key  // BST property
                        )
    && ( // Extra check to ensure only one path between 2 nodes.
       (right != null && left != null) ==>
         ((forall x :: x in left.Repr ==> x !in right.Repr) &&
                       (forall y :: y in right.Repr ==> y !in left.Repr)))
    && ((left == null && right == null) ==> Values == {key})
    && ((left != null && right == null) ==> Values == {key} + left.Values)
    && ((left == null && right != null) ==> Values == {key} + right.Values)
    && ((left != null && right != null) ==> Values == {key} + left.Values + right.Values)
  }

  predicate IsLeaf()
    reads this
  {
    && this.left == null
    && this.right == null
  }

  constructor (key:int, priority:int)
    ensures Valid()
    ensures Repr == {this}
    ensures Values == {key}
    ensures fresh(Repr)
  {
    this.key := key;
    this.priority := priority;
    this.left := null;
    this.right := null;
    Repr := {this};
    Values := {key};
  }
}
