method odd (n: nat) returns (j: int)
    ensures j == 1 + 2 ∗ n
    
    // (b)
    ensures j > n
    ensures j % 2 == 1
    // (b)
{
    var k := 0;
    j := 1;
    while k < n
        decreases n - k
        invariant j == 1 + 2 * k && 0 <= k <= n
    {
        k := k + 1;
        j := j + 2;
    }
}
