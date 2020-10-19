function fib(n : nat ) : nat
  decreases n
{
    if n < 2 then n else fib(n - 2) + fib(n - 1)
}

method computeFib (n : nat) returns (x : nat)
  ensures x == fib(n)
{
    var i := 0;
    x := 0;
    var y := 1;
    assert x == fib(i) && y == fib(i+1) && 0 <= i <= n; // I
    while  i < n 
      decreases n - i // Variante tem que diminuir
      invariant x == fib(i) && y == fib(i+1) && 0 <= i <= n //Necessário intervalo do iterador
    {
      ghost var V0 := n - i;
      assert i < n && x == fib(i) && y == fib(i+1) && 0 <= i <= n 
             && n - i == V0; // !C && I && V == V0
        x, y := y, x + y; // multiple assignment
        i := i + 1;
      assert x == fib(i) && y == fib(i+1) && 0 <= i <= n 
             && 0 <= n-i < V0; // I && 0 <= V < V0
    }
    assert i >= n && x == fib(i) && y == fib(i+1) && 0 <= i <= n;

    // Prova que o Dafny tenta fazer:
    // i >= n && x == fib(i) && y == fib(i+1) && i <= n ==> x == fib(n)
}
