/*method Main(args: array<seq<char>>) {
    var i := 0;
    while(i < args.Length)
        decreases args.Length - i;
        invariant 0 <= i <= args.Length;
    {
        print args[i];
        i := i + 1;
    }
}*/

//type T = int // for demo purposes, but could be another type
 
class {:autocontracts} Compression {

    /*predicate Valid()
    {}*/
    
 
    /*constructor () 
    {}*/
 
    method compress(s: string) returns (comp_s: string) 
        ensures s == decompress(comp_s);
    {
        comp_s := "";

        return comp_s;
    }

    method decompress(s: string) returns (decomp_s: string) 
    {
        decomp_s := "";

        return decomp_s;
    }

 
}
 
// A simple test scenario.
method Main()
{

}