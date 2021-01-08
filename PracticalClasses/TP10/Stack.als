open util/ordering[StackState]

sig Element {}

sig StackState {
    elements: seq Element
}{
    //
}

abstract sig Event {
    pre, post: StackState
}{
    // constraints that should hold for each Event
}

fact firstState {
    // constraints for the first StackState
    first.elements.isEmpty
}

pred Init [s: StackState] {
    s.elements.isEmpty
}

fact trace {
    // initial state
    Init [first]

  	// post-conditions
    // other but the intial states
    // relate all `StackState`s and `Event`s 
    all s: StackState - last | let s1 = s.next |
      	some e: Event { 
        	e.pre = s
			e.post = s1
      	}
}

sig Push extends Event {
    value: Element
}{
    // -- model pushing by relating `pre`, `post`, and `value`
    value = post.elements.first
    // same as below: post.elements = pre.elements.insert [0, value]
    post.elements.rest = pre.elements
}

sig Pop extends Event {
    value: one Element
}{
    // -- model popping
    not pre.elements.isEmpty
    value = pre.elements.first 
    // same as below: post.elements.insert[0, value] = pre.elements
    post.elements = pre.elements.rest
}

assert popThenPush {
    all s: StackState - last | let s1 = s.next |
        (some pre.s1 <: Push and some pre.s <: Pop) implies (pre.s <: Pop).value = (pre.s1 <: Push).value
}
check popThenPush

fact InitEqualsFinal {
    #Pop = #Push
}

assert sameNumberPushesPops {
    #Pop = #Push
}
check sameNumberPushesPops


assert noPopFromEmpty {
    no popEvent: Pop | popEvent.pre.elements.isEmpty
}
check noPopFromEmpty

run {}