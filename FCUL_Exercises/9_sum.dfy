function sumN(k: int, n: int) : int 
    decreases n - k
{
    if k > n then 0 else if n == k then k else k + sumN(k+1, n)
}

method sum(n: nat) returns(s: nat)
    ensures s == sumN(0, n)
{
    s := 0;
    var i: int := n;
    while i > 0 
        decreases i
        invariant 0 <= i <= n 
        invariant s == sumN(i+1, n)
    {
        s := s + i;
        i := i − 1;
    }
}
