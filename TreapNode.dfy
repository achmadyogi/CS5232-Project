class TreapNode {
  const key: int
  const priority: int
  var left: TreapNode?
  var right: TreapNode?

  // Needed to ensure no cycles in between nodes
  ghost var repr: set<TreapNode>

  ghost predicate Valid()
    reads this, repr
  {
    && this in repr // node is reachable to itself
    && ( left != null ==>
         && left in repr
         && this !in left.repr
         && left.repr <= repr
         && left.Valid())
    && ( right != null ==>
         && right in repr
         && this !in right.repr
         && right.repr <= repr
         && right.Valid())
    && ( // Extra check to ensure only one path between 2 nodes.
       (right != null && left != null) ==>
         ((forall x :: x in left.repr ==> x !in right.repr) &&
                       (forall y :: y in right.repr ==> y !in left.repr)))
  }

  predicate IsLeaf()
    reads this
  {
    && this.left == null
    && this.right == null
  }

  constructor (key:int, priority:int)
    ensures Valid()
    ensures repr == {this}
  {
    this.key := key;
    this.priority := priority;
    this.left := null;
    this.right := null;
    repr := {this};
  }
}
