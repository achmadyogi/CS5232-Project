class TreapNode {
  const key: int
  const priority: int
  var left: TreapNode?
  var right: TreapNode?
  var parent: TreapNode?

  // Needed to ensure no cycles in between nodes
  ghost var repr: set<TreapNode>

  ghost predicate Valid()
    reads this, repr
  {
    && this in repr
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
       right != null && right.Valid() && left != null && left.Valid() ==>
         (forall x :: x in left.repr ==> x !in right.repr) &&
         (forall y :: y in right.repr ==> y !in left.repr))
  }

  constructor (key:int, priority:int) {
    this.key := key;
    this.priority := priority;
    this.left := null;
    this.right := null;
    this.parent := null;
    repr := {this};
  }
}
