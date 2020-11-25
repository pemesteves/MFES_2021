method squareRoot(n: nat) returns (r: nat)
    ensures r ∗ r <= n < ( r + 1 ) ∗ ( r + 1 )
{
    r := 0;
    var sqr := 1;
    while sqr <= n
        decreases n - sqr
        invariant sqr == (r + 1) * (r + 1)
        invariant n >= r * r
    {
        r := r + 1;
        sqr := sqr + 2 ∗ r + 1;
    }
}