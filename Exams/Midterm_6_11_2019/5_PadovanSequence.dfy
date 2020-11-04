function P(n: nat): nat 
    decreases n
{ 
    if n <= 2 then 1 else P(n-2) + P(n-3) 
}

method calcP(n: nat) returns (res: nat)     
    ensures res == P(n) 
{
    if n <= 2 { return 1; }
    var a, b, c := 1, 1, 1; // P(0), P(1), P(2)
    var i := 2;

    while i < n
        decreases n - i
        invariant 2 <= i <= n 
        invariant a == P(i-2) && b == P(i-1) && c == P(i)
    {
        a, b, c := b, c, a + b;
        i := i + 1;
    }

    res := c;
}

method test()
{
    var p := calcP(0);
    assert p == 1;

    p := calcP(1);
    assert p == 1;

    p := calcP(2);
    assert p == 1;

    p := calcP(3);
    assert p == 2;

    p := calcP(4);
    assert p == 2;
}