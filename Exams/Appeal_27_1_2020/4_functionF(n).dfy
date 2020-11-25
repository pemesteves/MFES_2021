function F(n: nat): nat 
    decreases n
{ 
    if n <= 2 then n else F(n-1) + F(n-3)
}

method calcF(n: nat) returns (res: nat)  
    ensures res == F(n) 
{
    var a, b, c := 0, 1, 2;
    var i := 0;

  assert 0 <= i <= n && a == F(i) && b == F(i+1) && c == F(i+2);
    while i < n 
        decreases n - i
        invariant 0 <= i <= n && a == F(i) && b == F(i+1) && c == F(i+2)
    {
      ghost var V0 := n - i;
      assert 0 <= i <= n && a == F(i) && b == F(i+1) && c == F(i+2) && i < n && n - i == V0;
        a, b, c := b, c, a + c;        
        i := i + 1;
      assert 0 <= i <= n && a == F(i) && b == F(i+1) && c == F(i+2) && 0 <= n - i < V0;
    }
  
  assert 0 <= i <= n && a == F(i) && b == F(i+1) && c == F(i+2) && i >= n;
  
    res := a;
}