method MaxSum(x: int, y: int) 
returns (s: int, m: int) 
ensures x > y ==> m == x
ensures y > x ==> m == y
ensures s == x + y
{
    s := x + y;
    if (y > x) {
        m := y;
    } else {
        m := x;
    }
}

method RecostructFromMaxSum(s: int, m: int)
returns (x: int, y: int) 
// ensures x > y ==> m == x
// ensures y > x ==> m == y
requires 2 * m >= s
ensures x == m || y == m
ensures m >= x && m >= y
ensures s == x + y
{
    x := s - m;
    y := m;
}

// method Triple(x: int) returns (r:int)
// ensures r >= 0 {
//     var z: int;
//     // z * z >= 0
//     r := z * z;
//     // r >= 0
// }

method Main() {
    var s: int, m:int := MaxSum(34,71);
    var x: int, y: int := RecostructFromMaxSum(s, m);
    assert s == 105 && m == 71;
}