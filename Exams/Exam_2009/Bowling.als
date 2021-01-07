open util/ordering[Jogadas]

abstract sig Pinos {}

sig p1,p2,p3,p4,p5,p6,p7,p8,p9,p10 extends Pinos{}

sig Jogador {}

sig Jogadas {
    pinos : set Pinos
}

sig Bowling {
    jogo: Jogador one -> Jogadas
}

fun ListJogadores[b: Bowling]: set Jogador {
    b.jogo.Jogadas
}

pred AddJogador [b, b1: Bowling, j: Jogador] {
    j not in b.jogo.Jogadas

    b1.jogo = b.jogo + j -> Pinos
}

fun Vencedor [b: Bowling] : Jogador {
    b.jogo.last
}

fact SeqJogadas {
    all j: Jogadas | all j1: j.next | j1.pinos in j.pinos
}