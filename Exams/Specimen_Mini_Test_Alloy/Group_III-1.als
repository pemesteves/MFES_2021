sig Tree { root: lone Node }
sig Node {
    left, right : lone Node,
    value: one Int,
}

fun parent[n: Node]: Node {
    left.n + right.n
}

pred wellFormedTree {
    // b)
    all n: Node | some n.left + n.right => n.^left != n.^right

    // c)
    all disj n1, n2: Node | parent[n2] = n1 => (not n1 in n2.^(left + right))

    // d)
    all n: Node | not n = Tree.root => (one n1: Node | parent[n] = n1) else parent[n] = none

    // e)
    all n: Node | (one n.left implies n.left.value < n.value) and (one n.right implies n.value < n.right.value)

    // f)
    all disj n1, n2: Node | n1.value != n2.value

    // g)
    all n: Node | 
        let leftNum = #(n.left.*(left+right)) |
        let rightNum = #(n.right.*(left+right)) |
        leftNum > rightNum implies leftNum - rightNum <= 1 else rightNum - leftNum <= 1
}

check wellFormedTree {}

fact {wellFormedTree}

run {} for 4 but 1 Tree