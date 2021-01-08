open util/ordering[Time]

sig Time {}

one sig List {
    head : Node lone -> Time
}

sig Node {
    nextNode : Node lone -> Time,
    value: Int
}

pred init[T: Time] {
    no List.head.T
}

pred delete[t, t1: Time, n: Node] {
    n in List.head.t.*(nextNode.t) &&
    n !in List.head.t1.*(nextNode.t1)

    all node : (List.head.t.*(nextNode.t) - n) | 
        node.*(nextNode.t) - n = node.*(nextNode.t1)
}

pred insert[t, t1: Time, n: Node] {

}

fact traces {
    init[first]

    all t, t1 : Time | t.next = t1 implies
        some n : Node | delete[t, t1, n] or insert[t, t1, n]
}

fact invariant {
    let nodes = List.head + Node.nextNode | 
        all t, t1: Time | t.next = t1 implies nodes.t.value <= nodes.t1.value 
}

check {}

run {}