sig Institution {}

sig Researcher {
    affiliation: set Institution
}

sig Title {}

sig Paper {
    title: Title,
    authors: some Researcher
}

sig Conference {
    pcMembers: set Researcher,
    papers: set Paper,
    reviewers: papers -> pcMembers
} {
    #papers.title = #papers

    all p: papers | no reviewers[p] & p.authors

    no authors.affiliation & reviewers.affiliation
}

fun authoredPapers[r: Researcher]: set Paper {
    {p: Paper | r in p.authors}
}

fun papersToReview[c: Conference, r: Researcher]: set Paper {
    c.reviewers.r
}

pred assignmentComplete[c: Conference, minReviewers: Int] {
    all p: c.papers | # c.reviewers[p] >= minReviewers
}

pred assignReviewer[c0: Conference, p: Paper, r: Researcher, c1: Conference] {
    c1.reviewers = c0.reviewers + p->r
}