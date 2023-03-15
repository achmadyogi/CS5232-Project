class Node {
    const key: int;
    const priority: int;

    var parent: Node?
    var left: Node?
    var right: Node?

    ghost var repr: set<Node>;

    ghost predicate valid() 
        reads this, repr
    {
        && this in repr
        && (
            left != null ==> 
            && left in repr
            && this !in left.repr
            && left.repr <= repr
            && left.valid()
        )
        && (
            right != null ==>
            && right in repr
            && this !in right.repr
            && right.repr <= repr
            && right.valid()
        )
        && (
            right != null && right.valid() && left != null && left.valid() ==>
         (forall x :: x in left.repr ==> x !in right.repr) &&
         (forall y :: y in right.repr ==> y !in left.repr)
        )
    }

    constructor(key: int, priority: int) {
        this.key := key;
        this.priority := priority;

        this.parent := null;
        this.left := null;
        this.right := null;

        repr := {this};
    }

    // method insertNode(node: Node?) 
    // {
    //     if (node == null) {return;}
    //     if (node.key < this.key) {
    //         // Go to the left
    //         if (this.left == null) {
    //             this.left := node;
    //         } else {
    //             this.left.insertNode(node);
    //             // TODO: check priority
    //         }
    //     } else {
    //         // Go to the right
    //         if (this.right == null) {
    //             this.right := node;
    //         } else {
    //             this.right.insertNode(node);
    //             // TODO: check priority
    //         }
    //     }
    // }
}