abstract sig Tipo {}

sig SIMPLES, CENTRO, ANULADA extends Tipo {}

abstract sig Jogador {}

sig A, B extends Jogador {}

sig jogada {
    type : one Tipo,
    value : some Int, // guarda os valores atingidos pelos 3 dardos
    player : one Jogador,
    actualpoints : one Int,
    next : lone jogada // jogada seguinte
}

one sig primeira extends jogada {}

-- fact1: em cada jogada, o jogador lança 3 dardos
fact fact1 {
    all j: jogada | #j.value = 3
}

-- fact2: a sequência de jogada tem alternadamente jogadas dos jogadores <A> e <B>
fact fact2 {
    all j: jogada, j1: j.next | j1.player != j.player
}

fun soma[val: set Int]: Int {
    sum x: val | x
}

pred fimJogo {
    one j: jogada 
        | j.next = none 
          && j.type = CENTRO
          && j.actualpoints = 0
          && (one j1: jogada | j1.next.next = j && j1.player = j.player && soma[j.value] = j1.actualpoints)
}

pred seqJogadas {
    all disj j, j1: jogada | j1 in j.^next => not j in j1.^next

    all j: jogada | j.actualpoints != 0 => j in jogada.*next
}