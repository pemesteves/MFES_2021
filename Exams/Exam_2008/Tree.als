sig Point {}

sig Edge {
    top: one Point,
    right: lone Point,
    left: lone Point
}

sig Tree{
    root: Point,
    edges: set Edge
}

fun getEdge[p: Point, t: Tree]: set Edge {
    {e: t.edges | e.top = p}
}

pred pointInTree[p: Point, t: Tree] {
    p in t.edges.top  
}

fun getLeaves[t: Tree]: set Point {
    {p: Point | 
        pointInTree[p, t] 
        && no {e: getEdge[p, t] | e.right + e.left != none}
    }
}

pred rootInTree[t: Tree] {
    pointInTree[t.root, t]
}

fun getRightTree[t: Tree]: Tree {
    {t1: Tree |
        t.edges.right != none &&
        t1.root = t.edges.top
    }
}

pred isConnected[t: Tree] {
    all disj p1, p2: Point | 
        pointInTree[p1, t] 
        && pointInTree[p2, t]
        && (
            p2 in getEdge[p1, t].left + getEdge[p1, t].right
            ||
            p1 in getEdge[p2, t].left + getEdge[p2, t].right
        )
}

check isConnected {}