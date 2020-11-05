method divide(x: nat, y: nat) returns (q: nat, r: nat)
    requires y > 0;
    ensures q ∗ y + r == x && r >= 0 && r < y;
{
    q := 0;
    r := x;
    while r >= y 
        decreases r - y
        invariant x == q * y + r
    {
        r := r − y;
        q := q + 1;
    }
}