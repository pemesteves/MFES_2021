function method fact(n: nat) : nat
  decreases n
{
    if n == 0 then 1 else n * fact(n-1)
}

method factIter(n: nat) returns (f : nat)
    ensures f == fact(n)
{
  f := 1;
  var i := 0;

 assert f == fact(i) && 0 <= i <= n;
  while i < n 
    decreases n - i
    invariant f == fact(i) && 0 <= i <= n
  {
   ghost var V0 := n - i;
   assert i < n && f == fact(i) && 0 <= i <= n 
          && n - i == V0; // !C && I && V == V0
    i := i + 1;
    f := f * i;
   assert f == fact(i) && 0 <= i <= n 
          && 0 <= n - i < V0;
  }
 assert f == fact(i) && 0 <= i <= n && i >= n;
}
