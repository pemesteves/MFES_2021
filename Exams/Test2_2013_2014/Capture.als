abstract sig TYPE {}


one sig click, text, select extends TYPE {}

sig PARAMS {}

sig URL {}

sig Acao {
    tipo : one TYPE,
    params : set PARAMS,
    url : lone URL
}

sig TracoEx {
    init : one URL,
    traco : Int one -> Acao
}

fun URLAcao[t: TracoEx]: set Acao {
    {a: t.traco[Int] | one a.url}
}

fun primeiraAcao[t: TracoEx]: Acao {
    {a: t.traco[Int] | a.url = t.init}
}

fact urlPrimeiraAcao {
    all t: TracoEx | primeiraAcao[t].url = t.init
}

fun ultimoValorTraco[t: TracoEx]: Int {
    {tr: t.traco.Acao | all tr1: t.traco.Acao | tr != tr1 && tr > tr1}
}

fun ultimoTraco[t: TracoEx]: Int->Acao {
    ultimoValorTraco[t] -> t.traco[ultimoValorTraco[t]]
}

fun urlUltimaAcao[t: TracoEx]: URL {
    ultimoTraco[t][Int].url
}

fun actionID[a: Acao, t: TracoEx]: Int {
    t.traco.a
}

pred consecutivas[a1, a2: Acao, t: TracoEx] {
    all a: t.traco[Int] | a != a1 && a != a2 && actionID[a, t] < actionID[a1, t] && actionID[a, t] > actionID[a2, t]
}

fact acoesConsecutivas {
    all t: TracoEx, disj a1, a2: t.traco[Int] | consecutivas[a1, a2, t] => a1.url != a2.url
}