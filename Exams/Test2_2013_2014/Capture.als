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

fact acoesConsecutivas {
    all disj a1, a2: Acao | TracoEx.traco.a1 = TracoEx.traco.a2 - 1 => a1.url != a2.url
}