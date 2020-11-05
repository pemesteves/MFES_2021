function pwr(n: nat) : nat 
    decreases n
{
    if n == 0 then 1 else 2 * pwr(n-1)
}

method power(n: nat) returns (j : nat)
    ensures j == pwr(n)
{
    var k := 0;
    j := 1;
    while k < n
        decreases n - k
        invariant 0 <= k <= n && j == pwr(k)
    {
        k := k + 1;
        j := 2 ∗ j;
    }
}