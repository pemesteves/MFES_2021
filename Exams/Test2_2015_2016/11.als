sig Name {}

sig Pessoa {
    n: one Name,
    descendentes : set Pessoa
}

fun getAscendents[p: Pessoa]: set Pessoa {
    {p1: Pessoa | p != p1 and p in p1} 
}

-- a)
fact onlyTwoAscendents{
    all p: Pessoa | #getAscendents[p] <= 2
}

-- b)
fun getFirstPerson: Pessoa {
    {p: Pessoa | all p1: Pessoa | p != p1 and p1 in p.^descendentes}
}