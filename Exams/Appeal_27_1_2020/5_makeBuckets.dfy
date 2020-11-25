type T = nat 

// Given a non-empty array 'a' of natural numbers, generates a new array ‘b’ 
// (buckets) such that b[k] gives the number of occurrences of 'k' in 'a',
// for 0 <= k <= m, where 'm' denotes the maximum value in 'a'.
method makeBuckets(a: array<T>) returns(b: array<nat>) 
    requires a.Length > 0
    ensures 0 < b.Length <= findMax(a[..]) + 1
    ensures forall k :: 0 <= k < a.Length ==> a[k] < b.Length
    ensures forall k :: 0 <= k < b.Length ==> count(k, a[..]) == b[k]
{
    var max := findMax(a[..]);
    b := new T[1 + max];
    forall k | 0 <= k <= max { b[k] := 0; }
    var i := 0;
    while i < a.Length 
        decreases a.Length - i 
        invariant 0 <= i <= a.Length 
        invariant forall j :: 0 <= j < b.Length ==> b[j] == count(j, a[..i])
    {
        b[a[i]] := b[a[i]] + 1; 
        i := i + 1;
    } 
    assert a[..] == a[..a.Length]; // might be useful to help Dafny doing proofs...
}

// Auxiliary function that finds the maximum value in a non-empty sequence.
function method findMax(s: seq<T>) : T
    requires |s| > 0 
    ensures isMax(findMax(s), s)
{
    if |s| == 1 then s[0] else (var m := findMax(s[1..]); if m > s[0] then m else s[0])
}

// Auxiliary predicate that checks if 'x' is a maximum in sequence 's'.
predicate isMax(x: T, s: seq<T>) {
    (exists k :: 0 <= k < |s| && x == s[k]) && (forall k :: 0 <= k < |s| ==> x >= s[k])
}

// Auxiliary function that counts the number of occurrences of 'x' in sequence 's'.
function count(x: T, s: seq<T>) : nat { 
    multiset(s)[x] 
}

// A simple test case (checked statically)
method testMakeBuckets() {
    var a := new nat[6] [1, 1, 3, 3, 3, 5];
    assert a[..] == [1, 1, 3, 3, 3, 5];
    var b := makeBuckets(a);
    assert b[..] == [0, 2, 0, 3, 0, 1]; 
}