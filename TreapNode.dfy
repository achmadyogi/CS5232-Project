class TreapNode {
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
    // Validate the left side child
    && (left != null ==>
        && left in Repr
        && left.Repr <= Repr
        && this !in left.Repr
        && left.Valid()
        && forall x :: x in left.Values ==> x < value)
    // Validate the right side child
    && (right != null ==>
        && right in Repr
        && right.Repr <= Repr
        && this !in right.Repr
        && right.Valid()
        && forall x :: x in right.Values ==> value < x)
    && (left == null && right == null ==>
        && Values == {value})
    && (left != null && right == null ==>
        && Values == left.Values + {value})
    && (left == null && right != null ==>
        && Values == right.Values + {value})
    && (left != null && right != null ==> 
        && left.Repr !! right.Repr
        && Values == left.Values + {value} + right.Values)
  }

  ghost predicate ValidHeap()
    reads this, Repr
    requires Valid()
    ensures ValidHeap() ==> this in Repr
  {
    && (left != null ==> 
      && left.ValidHeap()
      && forall y :: y in left.Priorities ==> y <= priority)
    && (right != null ==> 
      && right.ValidHeap()
      && forall y :: y in right.Priorities ==> y <= priority)
    && (left == null && right == null ==> Priorities == {priority})
    && (left != null && right == null ==> Priorities == left.Priorities + {priority})
    && (left == null && right != null ==> Priorities == right.Priorities + {priority})
    && (left != null && right != null ==> Priorities == left.Priorities + {priority} + right.Priorities)

  }

  ghost predicate ValidRotateLeft()
    reads this, Repr
    requires Valid()
  {
    && (right != null
      && priority < right.priority
      && right.ValidHeap())
    && (left != null ==> 
      && (forall x :: x in left.Priorities ==> x <= priority)
      && left.ValidHeap())
    && (Priorities == {priority}
      + (if left != null then left.Priorities else {})
      + (if right != null then right.Priorities else {}))
    && (right != null && right.left != null ==> 
      (forall x :: x in right.left.Priorities ==> x <= priority))
  }

  ghost predicate ValidRotateRight()
    reads this, Repr
    requires Valid()  
  {
    && (left != null
      && priority < left.priority
      && left.ValidHeap())
    && (right != null ==> 
      && (forall x :: x in right.Priorities ==> x <= priority)
      && right.ValidHeap())
    && (Priorities == {priority}
      + (if right != null then right.Priorities else {})
      + (if left != null then left.Priorities else {}))
    && (left != null && left.right != null ==> 
      (forall x :: x in left.right.Priorities ==> x <= priority))
  }

  const value: int
  const priority: int

  var left: TreapNode?
  var right: TreapNode?

  constructor (value:int, priority:int)
    ensures Valid() && ValidHeap() && fresh(Repr)
    ensures Values == {value}
    ensures Priorities == {priority}
  {
    this.value := value;
    this.priority := priority;
    this.left := null;
    this.right := null;

    Repr := {this};
    Values := {value};
    Priorities := {priority};
  }

  predicate IsLeaf()
    reads this
  {
    && this.left == null
    && this.right == null
  }
}
