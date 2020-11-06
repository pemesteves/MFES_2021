function R(n: nat): nat 
    decreases n
{
    if n == 0 then 0 else if R(n-1) > n then R(n-1) - n else R(n-1) + n
}

method calcR(n: nat) returns (r: nat)
    ensures r == R(n) 
{
    r := 0;
    var i := 0;
    while i < n 
        decreases n - i
        invariant 0 <= i <= n && r == R(i)
    {
      assert i < n && 0 <= i <= n && r == R(i); //1º
      assert (r > i + 1 && 0 <= i + 1 <= n && r - i - 1 == R(i + 1)) || (r <= i + 1 && 0 <= i + 1 <= n && r + i + 1 == R(i + 1)); //4º
        i := i + 1;
      assert (r > i && 0 <= i <= n && r - i == R(i)) || (r <= i && 0 <= i <= n && r + i == R(i)); //3º
        if r > i {
            r := r - i;
        } 
        else {
            r := r + i;
        }
      assert 0 <= i <= n && r == R(i); //2º
    }
}