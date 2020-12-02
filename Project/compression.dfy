
newtype {:nativeType "uint"}   uint32 = i:int | 0 <= i < 0x100000000
newtype {:nativeType "byte"}   byte   = b:int | 0 <= b < 256

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

function method ToString(n: int) : string 
    requires n >= 0
{   
    if n == 0 then "" else ToString(n / 10) + [(n % 10) as char]
}

function method IsInt(c: char) : bool 
{
    if c <= '9' && c >= '0' then true else false 
}

function method isAlphaChar(c: char) : bool 
{
    if (c <= 'Z' && c >= 'A') || (c <= 'z' && c >= 'a') then true else false 
}

function method GetInt(s: string, n: int) : string 
    decreases |s| - n
    requires n >= 0
{
    if n >= |s| then "" else 
    if IsInt(s[n]) then [s[n]] + GetInt(s, n + 1) 
    else "" 
}

function method ParseInt(s: string, i: int) : int
    decreases i
    requires 0 <= i < |s|
{
    if i == 0 then s[i] as int else (s[i] as int) + 10 * ParseInt(s, i - 1)
}

class {:autocontracts} Compression {

    /*predicate Valid()
    {}*/
    
 
    constructor () 
    {}
 
    method getStringPortionCMP(c: char, occ: int) returns (s: string) 
        requires occ > 0
        ensures occ > 3 ==> |s| == 2 + |ToString(occ)|
        ensures occ <= 3 ==> |s| == occ
    {
        s := "";

        if occ > 3 {
            var tmp_s :=  ToString(occ);
            s := ['\\'] + [c] + tmp_s;
        } else {
            var j := 0;
            while j < occ 
                decreases occ - j
                invariant 0 <= j <= occ
                invariant |s| == j
            {
                s := s + [c];
                j := j + 1;
            }
        }
    }
    method compress(s: string) returns (comp_s: string)
        requires |s| > 0
        ensures |s| >= |comp_s|
    {
        comp_s := "";
        var cnt_occur : int := 1;
        var cur_char : char := s[0];

        var i := 1; // iterates through the string
        
        while i < |s|
            decreases |s| - i
            invariant 1 <= i <= |s|
            invariant cur_char in s 
            invariant 1 <= cnt_occur <= |s|
        {
            if s[i] == cur_char {
                cnt_occur := cnt_occur + 1;
            } else {
                var tmp_s := getStringPortionCMP(cur_char, cnt_occur);
                comp_s := comp_s + tmp_s;

                cur_char := s[i];
                cnt_occur := 1;
            }

            i := i + 1;
        }

        var tmp_s := getStringPortionCMP(cur_char, cnt_occur);
        comp_s := comp_s + tmp_s;
    }

    method decompress(s: string)  returns (decomp_s: string)
        requires |s| > 0
        ensures |s| <= |decomp_s|
    {
        decomp_s := "";

        var i := 0; // iterates through the string

        while i < |s| 
            decreases |s| - i 
            invariant 0 <= i <= |s|
        {
            if(s[i] == '\\') {
                i := i + 1;
                if(i < |s| && isAlphaChar(s[i])) {
                    i := i + 1;
                    var integerString := GetInt(s, i);
                    if(|integerString| > 0) {
                        var integer := ParseInt(integerString, |integerString| - 1);
                        var j := 0;
                        while j < integer
                            decreases integer - j
                            invariant 0 <= j <= integer 
                        {
                            decomp_s := decomp_s + [s[i-1]];
                            j := j + 1;
                        }
                        
                    } else {
                        decomp_s := decomp_s + ['\\'] + [s[i-1]];
                    }
                } else {
                    decomp_s := decomp_s + ['\\'];
                }
            } else {
                decomp_s := decomp_s + [s[i]];
                i := i + 1;
            }
        }
    }

 
}
 
// A simple test scenario.
method Main()
{
    var compression := new Compression();
    var s := "aaabbbbbbccc";
    var comp := compression.compress(s);
    print comp;
    assert multiset(s) == multiset("aaa\\b6ccc");
    var decomp := compression.decompress(comp);
    assert decomp == s;
}