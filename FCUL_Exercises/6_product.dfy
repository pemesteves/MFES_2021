method product(m: nat, n: int) returns (p: int)
ensures p == m ∗ n;
{
    var i : nat := m;
    p := 0;
    while (i != 0) 
        decreases if i <= 0 then 0 - i else i 
        invariant p == n * (m - i)
        invariant 0 <= i <= m
    {
        p := p + n;
        i := i − 1;
    }
}
