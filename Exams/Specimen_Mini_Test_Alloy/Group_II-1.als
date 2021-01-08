sig Node {}

sig DAG {
    edge: Node->Node
}

pred add (g, g': DAG, e: Node->Node) {
    one e 
    g'.edge = g.edge + e
}

fact acyclic {all g: DAG | no n: Node | n in n.^(g.edge)}

run add for 3 but 2 DAG