// method PositiveOps(x: int, y: int) returns (less: int, more: int)
//     requires x >= y;
//     // ensures 0 <= less <= more;
// {
//     less := x - y;
//     more := x + y;
// }
include "Tree.dfy"

method Main() {
    // var att, bcc := PositiveOps(10, 2);
    // print att, " ", bcc;
    // assert 10 > 2;
    var vals := new int[] [1,2,4,53,5];
    var tree := new Tree(vals);
}