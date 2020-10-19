/* 
* Formal specification and verification of a simple method 
* for performing integer division.
* FEUP, MIEIC, MFES, 2020/21.
*/

// Computes the quotient 'q' and remainder 'r' of 
// the integer division of a (non-negative) dividend
// 'n' by a (positive) divisor 'd'.
method div(n: nat, d: nat) returns (q: nat, r: nat)
 requires d > 0
 ensures 0 <= r < d && q * d + r == n
{
  q := 0;
  r := n;  
  while r >= d
    decreases r
    invariant q * d + r == n 
  {
    q := q + 1;
    r := r - d;
  }
}

// function method gera código executável e pode ser chamado dentro de ontros métodos
function method abs(n: int) : nat {
    if n < 0 then -n else n
}

method divInt(n: int, d: int) returns (q: int, r: nat)
 requires d != 0
 ensures r < abs(d) && q * d + r == n
{
    q, r := div(abs(n), abs(d));
   assert q * abs(d) + r == abs(n);
    if d < 0 && n < 0 
    {
      assert q * (-d) + r == -n;
      assert q * d - r == n;     
        if r == 0 {
            assert q * d + r == n;
            return;
        }
        else {
            assert (q + 1) * d + (-d - r) == n;
            return q + 1, -d - r;
        }
    }
    else if d < 0 && n >= 0 {
      assert q * (-d) + r == n;
      assert (-q) * d  + r == n;
        return -q, r;
    }
    else if d > 0 && n < 0 {
      assert q * d + r == -n;
      assert -q * d - r == n;
        if r == 0 {
          assert (-q) * d + r == n;
            return -q, r;
        }else {
          assert (-q-1) * d + (d - r) == n;
            return -q - 1, d - r;
        }
    }
}

// A simple test case (checked statically!)
method Main()
{
    var q, r := div(15, 6);
    assert q == 2;
    assert r == 3;
    print "q = ", q, " r=", "\n";
}