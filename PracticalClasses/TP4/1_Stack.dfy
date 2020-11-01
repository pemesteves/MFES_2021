type T = int // to allow doing new T[capacity], but can be other type 
 
class {:autocontracts} Stack
{
    const elems: array<T>; // immutable (pointer)
    var size : nat; // used size
 
    predicate Valid()
        reads this
    {
        size <= elems.Length
    }

    constructor (capacity: nat)
        requires capacity > 0
        ensures size == 0
        ensures elems.Length == capacity
    {
        elems := new T[capacity];
        size := 0; 
    }
 
    predicate method isEmpty()
    {
        size == 0
    }
 
    predicate method isFull()
    {
        size == elems.Length
    }
 
    method push(x : T)
        requires size < elems.Length
        // requires !isFull()
        ensures size == old(size) + 1
        ensures elems[old(size)] == x
        ensures forall i :: 0 <= i < old(size) ==> old(elems[i]) == elems[i]
    {
        elems[size] := x;
        size := size + 1;
    }
 
    function method top(): T
        requires size > 0
        // requires !isEmpty()
    {
         elems[size-1]
    }
    
    method pop() 
        requires size > 0
        // requires !isEmpty()
        ensures size == old(size) - 1
        ensures forall i :: 0 <= i < size ==> old(elems[i]) == elems[i]
    {
         size := size-1;
    }

    /*method pop2() returns(x: T) 
        requires size > 0 
        ensures elems[..size] + [x] == old(elems[size])
    {
        size : = size-1;
        return elems[size+1]
    }*/
}
 
// A simple test case.
method Main()
{
    var s := new Stack(3);
    assert s.isEmpty();
    s.push(1);
    s.push(2);
    s.push(3);
    assert s.top() == 3;
    assert s.isFull();
    s.pop();
    assert s.top() == 2;
    print "top = ", s.top(), " \n";
}
