sig Point {}

sig Graph{
    edge: Point -> some Point
}

fun Insere[g: Graph, p1, p2: Point]: Graph {
    (p1 + p2) in (g.edge.Point + g.edge[Point]) =>
        {g1: Graph | g1.edge = g.edge + p1 -> p2}
    else 
        g
}

pred biconnected[g:Graph] {
    no x, y: Point | y not in x.^(g.edge)
}

check {
    all g, g1: Graph, p1, p2: Point | 
        biconnected[g] && Insere[g, p1, p2] = g1
        => biconnected[g1]
}

fun points[g: Graph]: set Point {
    {p:Point | p in (g.edge.Point + g.edge[Point])}
}

fun notdirected[g0: Graph]: Graph{
    {g:Graph| g.edge = g0.edge + ~(g0.edge)}
}

fun complementar[g0: Graph]: Graph{
    {g:Graph | g.edge = points[g0]->points[g0] - notdirected[g0].edge}
}