type T = int // example

class {:autocontracts} BSTNode {
    // Concrete implementation variables.
    var value: T 
    var left: BSTNode?  // elements smaller than 'value' (? - may be null)
    var right: BSTNode? // elements greater than 'value' (? - may be null)

    // Ghost variable used for specification & verification purposes.
    // Holds the set of values in the subtree starting in this node (inclusive). 
    ghost var elems: set<T> 

    // Class invariant with the integrity constraints for the above variables
    predicate Valid() 
    { 
        (elems == {value}
                  + (if left == null then {} else left.elems)
                  + (if right == null then {} else right.elems))
        && (left != null ==> forall x :: x in left.elems ==> x < value)
        && (right != null ==> forall x :: x in right.elems ==> x > value)
    }

    // Check if the subtree starting in this node contains a value 'x'.
    method contains(x: T) returns (res: bool)
      ensures res <==> x in elems
      decreases elems
    {
        if x == value { res := true; } 
        else if x < value && left != null  { res := left.contains(x); } 
        else if x > value && right != null { res := right.contains(x); } 
        else { res := false; }
    }
}