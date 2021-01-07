/**
 * Relational logic revision exercises based on a simple model of a 
 * classroom management system.
 * 
 * The model has 5 unary predicates (sets), Person, Student, Teacher,
 * Group and Class, Student and Teacher a sub-set of Person. There are 
 * two binary predicates, Tutors a sub-set of Person x Person, and 
 * Teaches a sub-set of Person x Teaches. There is also a ternary 
 * predicate Groups, sub-set of Class x Person x Group.
 *
 * Solve the following exercises using Alloy's relational logic, which
 * extends first-order logic with:
 *	- expression comparisons 'e1 in e2' and 'e1 = e2'
 *	- expression multiplicity tests 'some e', 'lone e', 'no e' and 'one e'
 *	- binary relational operators '.', '->', '&', '+', '-', ':>' and '<:' 
 *	- unary relational operators '~', '^' and '*'
 *	- definition of relations by comprehension
 **/

/* The registered persons. */
sig Person  {
	/* Each person tutors a set of persons. */
	Tutors : set Person,
	/* Each person teaches a set of classes. */
	Teaches : set Class
}

/* The registered groups. */
sig Group {}

/* The registered classes. */
sig Class  {
	/* Each class has a set of persons assigned to a group. */
	Groups : Person -> Group
}

/* Some persons are teachers. */
sig Teacher in Person  {}

/* Some persons are students. */
sig Student in Person  {}

/* Every person is a student. */
pred inv1 {
    Person in Student
}

/* There are no teachers. */
pred inv2 {
    no Teacher
}

/* No person is both a student and a teacher. */
pred inv3 {
    no Student & Teacher
}

/* No person is neither a student nor a teacher. */
pred inv4 {
    Person in Student + Teacher 
}

/* There are some classes assigned to teachers. */
pred inv5 {
    some Teacher.Teaches
}

/* Every teacher has classes assigned. */
pred inv6 {
    all t: Teacher | some t.Teaches
}

/* Every class has teachers assigned. */
pred inv7 {
    all c: Class | some Teacher & Teaches.c
}

/* Teachers are assigned at most one class. */
pred inv8 {
    all t: Teacher | lone t.Teaches
}

/* No class has more than a teacher assigned. */
pred inv9 {
    all c: Class | lone Teacher & Teaches.c
}

/* For every class, every student has a group assigned. */
pred inv10 {
    all c: Class, s: Student | some c.Groups[s]
}

/* A class only has groups if it has a teacher assigned. */
pred inv11 {
    all c: Class | some c.Groups implies c in Teacher & Teaches.c
}

/* Each teacher is responsible for some groups. */
pred inv12 {
    all t: Teacher | some t.Teaches.Groups
}

/* Only teachers tutor, and only students are tutored. */
pred inv13 {
    /*all p: Person | 
        (some p.Tutors implies p in Teacher) 
        and 
        (p in Person.Tutors implies p in Student)*/

    Tutors in Teacher -> Student
}

/* Every student in a class is at least tutored by all the teachers
 * assigned to that class. */
pred inv14 {
    all c: Class, s: Student | s in c.Groups.Group implies (Teacher & Teaches.c) -> s in Tutors   
}

/* The tutoring chain of every person eventually reaches a Teacher. */
pred inv15 {
    all p: Person | some (^Tutors).p & Teacher
}

