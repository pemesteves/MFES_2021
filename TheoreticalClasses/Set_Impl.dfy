/* 
* Specification, implementation and verification of a Set implemented with an array (resizable).
* Illustrates the usage of ghost variables and abstraction/refinment relations to better separate
* specification (interface) and implementation.
* FEUP, MIEIC, MFES, 2020/21.
*/

type T = int // For demo purposes, but could be other type.
// This is done, instead of declaring Set<T>, because new T[...] would
// need an initializer passed to the constructor.

class {:autocontracts} ArraySet {
  // (Public) ghost variables used for specification purposes only  
  ghost var elems: set<T>;
 
  // (Private) concrete variables with internal representation.
  var list: array<T>;
  var used : nat;

  // (Private) predicate that formalizes the class invariant.  
  predicate Valid() {
    // constraints on concrete representation
    used <= list.Length 
    && (forall i, j :: 0 <= i < j < used ==> list[i] != list[j]) // no duplicates
    // abstraction relation (between concrete and abstract variables)
    && multiset(elems) == multiset(list[..used]) 

    // trick: state the equivalence between elems and multiset(elems),
    // to help Dafny doing several proofs in several places!   
    && (forall x :: x in elems ==> x in multiset(elems))  
    && (forall x :: x in multiset(elems) ==> x in elems)
  }

  // Internal parameter
  static const initialCapacity := 16;

  // (Public) Constructor, initializes this set as empty.
  constructor ()
    ensures elems == {}
  {
    // initialize concrete state variables
    list := new T[initialCapacity]; 
    used := 0;
    // initialize ghost state variable
    elems := {};
  }

  // (Public) Checks if this set contains an element x in time O(n).
  predicate method contains(x: T) 
    ensures contains(x) <==> x in elems  
  {
    // search concrete state variables
    exists i :: 0 <= i < used && list[i] == x
  }

  // (Public) Obtains the size of the set
  function method size(): nat
    ensures size() == |elems|  
  {
    // query concrete state variables
    used
  }

  // (Public) Inserts a new element x into this set in time O(1) (unless resizing is needed).
  method insert(x : T)
    requires x !in elems
    ensures elems == old(elems) + {x}
  {
    // allocate larger array if needed
    if used == list.Length { 
      grow();
    }
    // update concrete variables
	list[used] := x;
    used := used + 1;
    // update ghost variable
    elems := elems + {x};
  }

  // Internal method to reallocate array when needed.
  method grow()
    requires used == list.Length
    ensures used < list.Length
    ensures elems == old(elems)
  {
    var oldList := list;
    list := new T[if used == 0 then initialCapacity else 2 * used];
    forall i | 0 <= i < used {
        list[i] := oldList[i];
    }
    // trick: assertion to help proving post-conditions
    assert list[..used] == old(list[..used]);
  }

  // (Public) Deletes an existing element x from this set in time O(n).
  method delete(x: T)
    requires x in elems
    ensures elems == old(elems) - {x} 
  {
    // update concrete variables
    var i :| 0 <= i < used && list[i] == x;
    list[i] := list[used-1];
    used := used-1;
    // update ghost variable
    elems := elems - {x};
  }
}

// A simple test scenario checked statically.
/*method testSet()
{
  var s := new Set();
  s.insert(2);
  s.insert(5);
  assert s.size() == 2;
  assert s.contains(2);
  assert s.contains(5);
  assert !s.contains(1);
  s.delete(2);
  assert s.size() == 1;
  assert s.contains(5);
  assert !s.contains(2);
  s.delete(5);
  assert !s.contains(5);
  assert s.size() == 0;
}*/



// Examples of test cases with invalid inputs
method testInvalidDelete()
{
  var s := new ArraySet();
  s.insert(1);
  s.delete(2);
}

method testInvalidInsert()
{
  var s := new ArraySet();
  s.insert(1);
  s.insert(1);
}