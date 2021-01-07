open util/ordering[Jornada]

sig Jogador {}

sig Golo {
    marcador: one Jogador
}

sig Equipa {
    jogadores: set Jogador
}

sig Jogo {
    eq1: Equipa one -> set Golo,
    eq2: Equipa one -> set Golo
}

sig Jornada {
    jogos: set Jogo
}

sig Campeonato {
    jornadas: set Jornada
}

pred addGoal[g: Golo, e: Equipa, j, j1: Jogo] {
    e in (j.eq1 + j.eq2).Golo  

    e in j.eq1.Golo => j1.eq1[Equipa] = j.eq1[Equipa] + g else j1.eq1 = j.eq1
    e in j.eq2.Golo => j1.eq2[Equipa] = j.eq2[Equipa] + g else j1.eq2 = j.eq2
}

fun getTeams[c: Campeonato]: set Equipa {
    {e: Equipa | some j: c.jornadas.jogos | e in j.eq1.Golo + j.eq2.Golo}
}

fun getPlayers[c: Campeonato]: set Jogador {
    getTeams[c].jogadores
}

fun getGoals[c: Campeonato, j: Jogador]: set Golo {
    {g: Golo | some j: c.jornadas.jogos | g in j.eq1[Equipa] + j.eq2[Equipa] && g.marcador = j}
}

fact diffTeams {
    all disj j1, j2: Jornada | 
        j2 = j1.next => j1.eq1.Golo + j1.eq2.Golo != j2.eq1.Golo + j2.eq2.Golo
}