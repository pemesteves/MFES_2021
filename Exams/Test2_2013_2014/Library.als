sig Title {}

sig Person{}

sig Proceeding {
    editors: set Person,
    titlepr : one Title,
    papers: set Paper
}

sig Paper {
    titlepe: Title,
    authors: set Person
}

sig Library {
    proceedings: set Proceeding
}

fact proceedingEditor {
    all p: Proceeding | some p.editors
}

fun removeFromEditor[l: Library, e: Person]: Library {
    {l1: Library | 
        e in l.proceedings.editors &&
        l1.proceedings = l.proceedings - {p: l.proceedings | e in p.editors}
    }
}

fun numProceedings[p: Person]: Int {
    #{authors.p} + #{pr: Proceeding | p in pr.editors}
}

check editorAndAuthor {
    some pr: Proceeding | some p: Person |
        p in pr.editors && authors.p in pr.papers 
}


pred add[tproc: Proceeding, tpaper: Paper.titlepe, a: Person, tproc1: Proceeding] {
    not tpaper in {p: Proceeding | p.titlepr = tproc}.papers.titlepe

    tproc1.editors = tproc.editors
    tproc1.titlepr = tproc.titlepr
    tproc1.papers = tproc.papers + {p: Paper | p.titlepe = tpaper}
}
