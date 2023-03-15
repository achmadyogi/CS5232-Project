include "Node.dfy"

class Tree {
    var root: Node?

    constructor(values: array<int>) {
        var i := 0;
        while i < values.Length {
            print values[i]," ";
            i := i + 1;
        }
        print "\n";
    }

    method insert(val: int) {
        var priority := val * 123 % 1000;
        var node := new Node(val, priority);
    }

    method insertNode(node: Node?) {
        if (node == null) {return;}
        if (this.root == null) {
            this.root := node;
        }
    }
}