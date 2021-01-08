abstract sig A, B {}
one sig A1, A2, A3 extends A {}
one sig B1, B2 extends B {}

/* A) 

one sig R { r : A some->lone B }{ r[A1] = r[A2] && r[A1] = B1}

*/

/* B)

one sig R { r : A lone->lone B }{ r.B1 = r.B2}

*/

/* C)

one sig R { r : A some->some B }{ r.B1 = r.B2}

*/

/* D)

one sig R { r : A lone->some B }{}

*/

/* E)

one sig R { r : A lone-> B }{ r[A1] = r[A2] && r[A1] = B1}

*/

/* F) */
one sig R { r : A some->lone B }{ r.B1 = r.B2}

run {} for 4