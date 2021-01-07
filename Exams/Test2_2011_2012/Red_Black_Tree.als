abstract sig color {}

sig RED, BLACK extends color {}

sig edge {
    cor : one color,
    id : Int,
    left : lone edge,
    right : lone edge,
}

one sig root extends edge{}

-- fact1: The root is black
fact fact1 {
    root.cor = BLACK
}

-- fact2: All leaves are the same color as the root
fact fact2 {
    all e: edge | e.left + e.right = none => e.cor = root.cor
}

fun maxId: edge {
    {e: edge | all e1: edge | e != e1 && e1.id < e.id}
}

fun path[n1: edge, n2: edge]: set edge {
    n2 in n1.^left => n1.^left else n1.^right
}

fun blacks[n1: edge, n2: edge]: Int {
    {sum e: path[n1, n2] | e.cor = BLACK => 1 else 0}
}

pred sameBlackNodes {
    all disj e1, e2: root.^left + root.^right | e1.left + e1.right + e2.left + e2.right = none => blacks[root, e1] = blacks[root, e2] 
}

-- fact3: Both children of every red node are black
fact fact3 {
    all e: edge | e.cor = RED => e.left.cor = BLACK && e.right.cor = BLACK
}