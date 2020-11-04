// File system node
trait Node {

    const name: string; // unique within each folder
    ghost const depth: nat; // starts in 0 at file system root
}

class {:autocontracts} File extends Node { }

class {:autocontracts} Folder extends Node {
    var child: set<Node>; 

    predicate Valid() {
        forall c :: c in child ==> c.depth == depth + 1
        &&
        forall c1, c2 :: c1 in child && c2 in child && c1 != c2 ==> c1.name != c2.name 
    }

    constructor (name: string, parent: Folder?) 
        modifies parent 
        ensures depth == if parent == null then 0 else parent.depth + 1
        ensures |child| == 0
        ensures parent != null ==> this in parent.child
    {
        // this object initialization
        this.name := name;
        this.depth := if parent == null then 0 else parent.depth + 1;
        this.child := {};
        // other objets' updates (after special "new" keyword)
        new;
        if parent != null {
            parent.child := parent.child + {this};
        }
    }
}