// A datatype that stores a value of type T or Nil (no value)
datatype Option<T> = Nil | Some(value: T)

// Function type for hash functions
type HashFunction<!T> = (T) -> nat

// Represents a hash set of elements of type T, that is, a set stored in a hash table.
class {:autocontracts} HashSet<T(==)> {
    // Parameter of the hash set (hash function to be used).
    const hash: HashFunction<T>;

    // Abstract state variable used for specification purposes only
    ghost var elems : set<T>;
    
    // Concrete state variable with internal representation (initially filled with Nil).
    var hashTable: array<Option<T>>;

    // Predicate that formalizes the class invariant.
    predicate Valid() 
        reads this
    { 
        (forall x :: x in elems ==> exists k :: 0 <= k < this.hashTable.Length && this.hashTable[k] == Some(x)) 
        &&
        (forall k :: 0 <= k < this.hashTable.Length ==> exists x :: x in elems && Some(x) == this.hashTable[k])
        &&
        (this.hashTable.Length > 0)
    }
    
    // Receives the hash function to be used and initializes the set as empty.
    constructor (hash: HashFunction<T>)
        ensures this.hash == hash && elems == {}
    
    // Inserts a new element x into this hash set.
    method insert(x : T)
        requires x !in elems
        ensures elems == old(elems) + {x}

    // Method that checks if this hash set contains an element x.
    method contains(x: T) returns (res: bool)
        ensures res <==> x in elems
    {
        var h := hash(x) % hashTable.Length;
        var i := h;
        while i < hashTable.Length
            invariant h <= i <= hashTable.Length
            invariant forall j:: h <= j < i ==> hashTable[j] != Nil && hashTable[j] != Some(x)
        {
            if hashTable[i] == Nil { return false; }
            if hashTable[i] == Some(x) { return true; }
            i := i + 1;
        }
        i := 0;
        while i < h
            invariant 0 <= i <= h
            invariant forall j:: 0 <= j < i ==> hashTable[j] != Nil && hashTable[j] != Some(x)
        {
            if hashTable[i] == Nil { return false; }
            if hashTable[i] == Some(x) { return true; }
            i := i + 1;
        }
        return false;
    }
}

// A simple test case, checked statically by Dafny.
method testHashSet() {
    var h := new HashSet<string>(x => |x|); // the hash function is the string length
    h.insert("Hello");
    assert h.elems == {"Hello"};
    h.insert("World");
    assert h.elems == {"Hello", "World"};
    var found := h.contains("Hello");
    assert found;
    found := h.contains("ANSI");
    assert !found;
}