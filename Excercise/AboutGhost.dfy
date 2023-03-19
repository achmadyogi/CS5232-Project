function pow(n: nat): nat
{
    if n == 0
        then 1
        else (2 * pow(n-1))
}
function Value(s: seq<bool>, base: nat): nat
{
    if s == []
        then 0
        else (if s[0]
                then base + Value(s[1..], 2*base)
                else        Value(s[1..], 2*base)
            )
}
