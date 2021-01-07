enum Vermelhas { Ouros, Copas }

enum Pretas { Paus, Espadas }

enum Estado { Cima, Baixo }

sig Carta {
    valor: Int,
    naipe: Vermelhas + Pretas,
    estado: Estado
}

abstract sig Sequencia { cartas: Int -> Carta }

abstract sig Fila, Fundacao, Pilha, Lixo extends Sequencia {}

one sig F1, F2, F3, F4, F5, F6, F7 extends Fila { }

one sig M1, M2, M3, M4 extends Fundacao { }

fact allFoundationsHaveSameNaipe {
    all m: Fundacao | all disj c1, c2: m.cartas[Int] | c1.naipe = c2.naipe
}

pred EndGame {
    all m: Fundacao | #m.cartas = 13 
}

fun allCardsTurnedUp[f: Fila]: set Carta {
    {c: f.cartas[Int] | c.estado = Cima}
}

pred InitGame {
    all f: Fila | #(allCardsTurnedUp[f]) = 1
}