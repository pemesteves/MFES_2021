method product(m: nat, n: nat) returns (res: nat)
    ensures res == m ∗ n;
{
    var m1: nat := m; res := 0;
    while m1 != 0 
        decreases if m1 <= 0 then 0 - m1 else m1
        invariant 0 <= m1 <= m
        invariant res == (m - m1) * n
    {
        var n1: nat := n;
        while n1 != 0 
            decreases if n1 <= 0 then 0 - n1 else n1
            invariant 0 <= n1 <= n 
            invariant res == (m - m1) * n + n - n1
        {
            res := res + 1;
            n1 := n1 − 1;
        }
        m1 := m1 − 1;
    }
}
