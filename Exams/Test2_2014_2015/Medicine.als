sig Medicin {
    incompatibilities: set Medicin-this // other medicins incompatible with this one
}

fact incompatibilities_symmetry {
    -- if m1 is incompatible with m2, then the opposite also holds
    incompatibilities = ~incompatibilities
}

sig Doctor { }

sig Patient {
    doctors: some Doctor, -- doctors (1 or more) of this patient (only them can prescribe medicins)
    alergies: set Medicin, -- medicins (0 or more) that this patient is alergic to
    prescriptions: Doctor lone -> set Medicin -- current (active) prescriptions, as a set
    -- of pairs (doctor, medicin prescribed), with each medicin prescribed by at most one doctor
}

fun medicins[p: Patient] : set Medicin {
    p.prescriptions[Doctor]
}

pred safety_invariants[p: Patient] {
    -- a patient cannot be prescribed a medicin to which he/she is alergic
    no p.alergies & medicins[p]

    -- a patient cannot be prescribed mutually incompatible medicins
    all disj m1, m2: medicins[p] | m1 not in m2.incompatibilities

    -- medicins can be prescribed only by the patient's doctors
    p.prescriptions.Medicin in p.doctors
}

-- doctor d prescribes medicin m to patient p, resulting in a new patient state p'
pred prescribe[d: Doctor, m: Medicin, p, p1: Patient] {
    -- pre-conditions (don't use predicate safety_invariants!)
    d in p.doctors
    m not in p.alergies + p.medicins.incompatibilities
    m not in p.medicins

    -- post-conditions (don't use predicate safety_invariants!)
    p1.doctors = p.doctors
    p1.alergies = p.alergies
    p1.prescriptions = p.prescriptions + d -> m
    p1.medicins = p.medicins + m
}

assert prescribe_preserves_safety_invariants {
    all d: Doctor, m: Medicin, p, p': Patient |
    safety_invariants[p] and prescribe[d,m,p,p'] => safety_invariants[p']
}
check prescribe_preserves_safety_invariants