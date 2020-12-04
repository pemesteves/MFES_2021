include "Io.dfy"

method ArrayFromSeq<A>(s: seq<A>) returns (a: array<A>)
  ensures a[..] == s
{
  a := new A[|s|] ( i requires 0 <= i < |s| => s[i] );
}

// Useful to convert Dafny strings into arrays of characters.
method copy(ghost env:HostEnvironment, src_name:array<char>, src:FileStream, dst:FileStream) returns (success:bool)
    requires env.Valid() && env.ok.ok();
		requires src_name[..] == src.Name();
		requires src.Name() in env.files.state() && dst.Name() in env.files.state();
		requires env == src.env == dst.env;
		requires env.ok == src.env.ok == dst.env.ok;
		requires env.files == src.env.files == dst.env.files;
		requires src.IsOpen() && dst.IsOpen();
		requires src != dst;
		requires env.files.state()[dst.Name()] == [];
    modifies env, env.files, env.ok, src, dst, src.env, src.env.ok, src.env.files;
    ensures  env.ok != null && success == env.ok.ok();
    ensures var old_files := old(env.files.state());
			      success
            ==>
            env.files != null &&
            env.files.state() == old_files[old(dst.Name()) := old(env.files.state()[src_name[..]])];    
{
  var ok, src_len := FileStream.FileLength(src_name, env);
  if !ok {
    print "Failed to find the length of src file: ", src, "\n";
    return false;
  }

  var buffer := new byte[src_len];
  ok := src.Read(0, buffer, 0, src_len);
  if !ok {
    print "Failed to read the src file: ", src, "\n";
    return false;
  }
	assert buffer[..] == old(env.files.state()[src_name[..]]);
	
  ok := dst.Write(0, buffer, 0, src_len);
  if !ok {
    print "Failed to write the dst file: ", dst, "\n";
    return false;
  }
	assert buffer[..] == env.files.state()[dst.Name()];
	
  ok := src.Close();
  if !ok {
    print "Failed to close the src file: ", src, "\n";
    return false;
  }
	
  ok := dst.Close();
  if !ok {
    print "Failed to close the dst file: ", dst, "\n";
    return false;
  }

	return true;
}

method {:main} Main(ghost env:HostEnvironment)
  requires env.Valid() && env.ok.ok();
  modifies env, env.files, env.ok;
  ensures var args := old(env.constants.CommandLineArgs());
          var old_files := old(env.files.state());
	        if !(|args| == 4 && args[2] in old_files && args[3] !in old(env.files.state()) && |args[1]| == 1 && (args[1][0] == '0' || args[1][0] == '1')) then
						env == old(env) && env.ok == old(env.ok) && env.ok.ok() == old(env.ok.ok())
					&& env.files == old(env.files) && env.files.state() == old_files 
					else
						env.ok != null && 
						(env.ok.ok() && |args| == 4 && args[2] in old_files && args[3] !in old(env.files.state()) 
						==> env.files != null &&
            env.files.state() == old_files[args[3] := old_files[args[2]]]);
{
    print "Starting Main";

    var num_args := HostConstants.NumCommandLineArgs(env);
    if num_args != 4 {
        print "Expected usage: compression.exe [0|1] [src] [dst]\n";
        return;
    }

    var compression := HostConstants.GetCommandLineArg(1, env);
    if compression.Length != 1 {
        print "The first argument should be 1 for compression or 0 for decompression, but instead got: ", compression, "\n";
        return;
    }

    if !(compression[0] == '0' || compression[0] == '1') {
        print "The first argument should be 1 for compression or 0 for decompression, but instead got: ", compression, "\n";
        return;
    }  

    var isCompression : bool := if compression[0] == '0' then false else true;

    var src := HostConstants.GetCommandLineArg(2, env);
    var dst := HostConstants.GetCommandLineArg(3, env);

    var src_exists := FileStream.FileExists(src, env);
    if !src_exists {
        print "Couldn't find src file: ", src, "\n";
        return;
    }

    var dst_exists := FileStream.FileExists(dst, env);
    if dst_exists {
        print "The dst file: ", dst, " already exists.  I don't dare hurt it.\n";
        return;
    }

    var ok, src_stream := FileStream.Open(src, env);
    if !ok {
        print "Failed to open src file: ", src, "\n";
        return;
    }

    var dst_stream;
    ok, dst_stream := FileStream.Open(dst, env);
    if !ok {
        print "Failed to open dst file: ", dst, "\n";
        return;
    }

    ok := copy(env, src, src_stream, dst_stream);

}


/*
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
*/

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

function method IsAlphaChar(c: char) : bool 
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

function method RepeatChar(c: char, occ: int) : string
    decreases occ
    requires occ >= 0
    ensures |RepeatChar(c, occ)| == occ && forall i :: 0 <= i < occ ==> RepeatChar(c, occ)[i] == c;
{
    if occ == 0 then "" else [c] + RepeatChar(c, occ - 1)
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

    function method helpCompress(s: string, cur_char: char, occ: int, index: int) : string
        decreases |s| - index 
        requires |s| > 0
        requires 0 <= index <= |s| && 0 < occ <= index
        requires forall i :: index - occ <= i < index ==>  s[i] == cur_char
        ensures |helpCompress(s, cur_char, occ, index)| <= |s| 
    {
        if index >= |s| then {
            RepeatChar(cur_char, occ)
        } else if s[index] == cur_char then {
            helpCompress(s, cur_char, occ + 1, index + 1)
        } else if occ <= 3 then {
            RepeatChar(cur_char, occ) + helpCompress(s, s[index], 1, index + 1)
        } else {
            ['\\'] + [cur_char] + ToString(occ) + helpCompress(s, s[index], 1, index + 1)
        }
    }

    method {:verify false} compress(s: string) returns (comp_s: string)
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

    method {:verify false} decompress(s: string)  returns (decomp_s: string)
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
                if(i < |s| && IsAlphaChar(s[i])) {
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
