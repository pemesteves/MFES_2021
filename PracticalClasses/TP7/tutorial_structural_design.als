abstract sig Object {}

/*
sig File in Object {}
sig Dir in Object {}

fact { 
    no File & Dir // A File can't be a Dir and a Dir can't be a File
    Object = File + Dir // An Object is a File or a Dir
}
*/

sig Name {}

sig Entry {
    name : one Name,
    content : one Object
}

sig File extends Object {}

sig Dir extends Object {
    entries : set Entry
}

//check { no File & Dir } to check that the first fact is redundant

one sig Root extends Dir {}

fact {
    // Entries cannot be shared between directories
    all x,y : Dir | x != y implies no (x.entries & y.entries)
    // all disj x,y : Dir | no (x.entries & y.entries)
    // all e : Entry | lone entries.e
    // entries in Dir lone -> Entry

  
    // Different entries in the same directory must have different names
    all d : Dir, disj x, y : d.entries | x.name != y.name
    // all d : Dir, n : Name | lone (d.entries & name.n)

    // Directories cannot contain themselves
    // all d : Dir | d not in d.entries.content
    all d : Dir | d not in d.^(entries.content)

    // Entries must belong to exactly one a directory
    entries in Dir one -> Entry
    
    // Every object except the root is contained somewhere
    Entry.content = Object - Root
    
    // Content is injective
    content in Entry lone -> Object
}

assert no_partitions {
    // Every object is reachable from the root
    Object-Root = Root.^(entries.content)
}

check no_partitions for 6

run example {
    some File 
    some Dir-Root 
} for 4