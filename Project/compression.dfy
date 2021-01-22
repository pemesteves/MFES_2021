include "Io.dfy"

method ArrayFromSeq<A>(s: seq<A>) returns (a: array<A>)
  ensures a[..] == s
{
  a := new A[|s|] ( i requires 0 <= i < |s| => s[i] );
}

method GetStringFromByteArray(b: array?<byte>) returns (s: string) 
    ensures b == null ==> s == ""
    ensures b != null ==> b.Length == |s|
    ensures forall i :: 0 <= i < |s| ==> b[i] as char == s[i] && 0 <= s[i] as int < 256
{
    if b == null {
        return "";
    }

    s := ""; 

    var i := 0;
    while i < b.Length 
        decreases b.Length - i
        invariant 0 <= i <= b.Length
        invariant |s| == i 
        invariant forall j :: 0 <= j < i ==> s[j] == b[j] as char
    {
        s := s + [b[i] as char];
        i := i + 1;
    }
}

method GetByteArrayFromString(s: string) returns (b: array?<byte>) 
    requires forall i :: 0 <= i < |s| ==> 0 as char <= s[i] < 256 as char 
    ensures |s| == 0 ==> b == null
    ensures |s| > 0 ==> b != null && b.Length == |s|
    ensures forall i :: 0 <= i < |s| ==> b[i] as char == s[i]
{
    if |s| == 0 {
        return null;
    }

    b := new byte[|s|];

    var i := 0;
    while i < |s|
        decreases |s| - i
        invariant 0 <= i <= |s| 
        invariant forall j :: 0 <= j < i ==> b[j] as char == s[j]
    {
        b[i] := (s[i] as int) as byte;
        i := i + 1;
    }
}


method {:verify false} callCompression(ghost env:HostEnvironment, src_name:array<char>, src:FileStream, dst:FileStream, isCompression: bool) returns (success:bool)
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
        
    var cmp := new Compression();
    var buffer_string := GetStringFromByteArray(buffer);    
    
    var str := "";
    if |buffer_string| > 0 {
        if isCompression {
            str := cmp.compress(buffer_string);
        } 
        else {
            str := cmp.decompress(buffer_string);
        }
    }

    var cmp_buffer := GetByteArrayFromString(str);

    if cmp_buffer == null {
        print "Source file ", src, " is empty", "\n";
        return false;
    }

    var cmp_buff_leng : int32 := cmp_buffer.Length as int32;

    ok := dst.Write(0, cmp_buffer, 0, cmp_buff_leng);
    if !ok {
        print "Failed to write the dst file: ", dst, "\n";
        return false;
    }
  
  assert cmp_buffer[..] == env.files.state()[dst.Name()];
        
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
{
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

    ok := callCompression(env, src, src_stream, dst_stream, isCompression);
}

function method NumDigits(n: int) : int 
    decreases n
    requires n >= 0
{
    if n <= 9 then 1 else 1 + NumDigits(n / 10)
}

function method ToString(n: int) : string 
    decreases n
    requires n >= 0
    ensures 
        var s := ToString(n);
        |s| == NumDigits(n) && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9' && 0 <= s[i] as int < 256
{   
    if n <= 9 then [n as char + '0']
    else ToString(n / 10) + [(n % 10) as char + '0']
}

predicate method IsInt(c: char) 
    ensures '0' <= c <= '9' <==> IsInt(c) 
{
    if '0' <= c <= '9' then true else false 
}

predicate method IsAlphaChar(c: char) 
    ensures 'A' <= c <= 'Z' || 'a' <= c <= 'z' <==> IsAlphaChar(c)
{
    if ('A' <= c <= 'Z') || ('a' <= c <= 'z') then true else false 
}

function method GetInt(s: string, n: int) : string
    decreases |s| - n
    requires 0 <= n <= |s| 
    requires forall i :: 0 <= i < |s| ==> 0 <= s[i] as int < 256
    ensures 
        var integerString := GetInt(s, n);
        (|integerString| != 0 ==> forall i :: 0 <= i < |integerString| ==> '0' <= integerString[i] <= '9' && 0 <= integerString[i] as int < 256)
        &&
        (|s| >= n + |integerString|)
{
    if n == |s| || s[n] == '\0' then "" 
    else if IsInt(s[n]) then 
        if n + 1 == |s| || s[n + 1] == '\0' then 
            [s[n]]
        else 
            var i := GetInt(s, n + 1);
            if i == "" then ""
            else [s[n]] + i 
    else "" 
}

function method ParseInt(s: string, i: int) : int
    decreases i
    requires 0 <= i < |s|
    requires forall j :: 0 <= j <= i ==> '0' <= s[j] <= '9' 
    ensures ParseInt(s, i) >= 0
{
    if i == 0 then (s[i] - '0') as int else ((s[i]-'0') as int) + 10 * ParseInt(s, i - 1)
}

function method RepeatChar(c: char, occ: int) : string
    decreases occ
    requires occ >= 0
    requires 0 <= c as int < 256
    ensures 
        var s := RepeatChar(c, occ);
        |s| == occ && forall i :: 0 <= i < occ ==> s[i] == c && 0 <= s[i] as int < 256
{
    if occ == 0 then "" else [c] + RepeatChar(c, occ - 1)
}

class Compression {
 
    constructor () 
    {}
 
    function method repeatOccurences(cur_char: char, occ: int) : string
        requires occ > 0
        requires 0 <= cur_char as int < 256
        ensures 
            var s := repeatOccurences(cur_char, occ);
            (occ <= 4 ==> |s| == occ) 
            &&
            (occ > 4 ==> |s| == 3 + |ToString(occ)|)
            &&
            forall i :: 0 <= i < |s| ==> 0 <= s[i] as int < 256
    {
        if occ <= 4 then
            RepeatChar(cur_char, occ)
        else 
            ['\0'] + [cur_char] + ToString(occ) + ['\0']
    }

    function method helpCompress(s: string, cur_char: char, occ: int, index: int) : string
        decreases |s| - index 
        requires 1 <= occ <= |s|
        requires 1 <= index <= |s| && 0 < occ <= index
        requires forall i :: index - occ <= i < index ==>  s[i] == cur_char
        requires forall i :: 0 <= i < |s| ==> 0 <= s[i] as int < 256
        requires 0 <= cur_char as int < 256
        ensures 0 < |helpCompress(s, cur_char, occ, index)|
        ensures 
            var cmp := helpCompress(s, cur_char, occ, index);
            (forall i :: 0 <= i < |cmp| ==> 0 <= cmp[i] as int < 256)
            &&
            (index >= |s| ==> cmp == repeatOccurences(cur_char, occ))
            &&
            (index < |s| ==> 
                (s[index] == cur_char ==> cmp == helpCompress(s, cur_char, occ + 1, index + 1)
                &&
                (s[index] != cur_char ==> cmp == repeatOccurences(cur_char, occ) + helpCompress(s, s[index], 1, index + 1))))
    {
        if index >= |s| then 
            repeatOccurences(cur_char, occ)
        else if s[index] == cur_char then
            helpCompress(s, cur_char, occ + 1, index + 1)
        else 
            repeatOccurences(cur_char, occ) + helpCompress(s, s[index], 1, index + 1)
    }

    function method compress(s: string) : string 
        requires |s| > 0
        requires forall i :: 0 <= i < |s| ==> 0 <= s[i] as int < 256
        ensures 0 < |compress(s)|
        ensures 
            var cmp := compress(s);
            (cmp == helpCompress(s, s[0], 1, 1))
            &&
            forall i :: 0 <= i < |cmp| ==> 0 <= cmp[i] as int < 256 
    {
        helpCompress(s, s[0], 1, 1)
    }


    function method helpDecompress(s: string, fnd_esc: bool, fnd_ch: bool, ch: char, index: int) : string
        decreases |s| - index 
        requires |s| > 0
        requires 1 <= index <= |s| + 1
        requires index > |s| ==> !fnd_ch && !fnd_esc
        requires fnd_ch ==> s[index-1] == ch && index >= 2
        requires fnd_esc ==> if fnd_ch then s[index - 2] == '\0' else s[index - 1] == '\0'
        requires forall i :: 0 <= i < |s| ==> 0 <= s[i] as int < 256
        ensures 
            var dcmp := helpDecompress(s, fnd_esc, fnd_ch, ch, index);
            (forall i :: 0 <= i < |dcmp| ==> 0 <= dcmp[i] as int < 256)
            &&
            (index >= |s| ==> 
                (fnd_esc ==> 
                    (fnd_ch ==> dcmp == ['\0'] + [ch])
                    &&
                    (!fnd_ch ==> dcmp == ['\0'])) 
                &&
                (!fnd_esc ==> dcmp == ""))
            &&
            (index < |s| ==> 
                (fnd_esc ==> 
                    (fnd_ch ==> 
                        var integer := GetInt(s, index);
                        (|integer| > 0 ==> 
                            var occ := ParseInt(integer, |integer| - 1);
                            (occ > 4 ==> dcmp == RepeatChar(ch, occ) + helpDecompress(s, false, false, '\0', index + |integer| + 1))
                            &&
                            (occ <= 4 ==> dcmp == ['\0'] + [ch] + [s[index]] + helpDecompress(s, false, false, '\0', index + |integer| + 1)))
                        &&
                        (|integer| <= 0 ==> dcmp == ['\0'] + [ch] + helpDecompress(s, false, false, '\0', index + 1)))
                    &&
                    (!fnd_ch ==> dcmp == helpDecompress(s, true, true, s[index], index + 1)))
                &&
                (!fnd_esc ==> 
                    (s[index] == '\0' ==> dcmp == helpDecompress(s, true, false, '\0', index + 1))
                    &&
                    (s[index] != '\0' ==> dcmp == [s[index]] + helpDecompress(s, false, false, '\0', index + 1))))
    {
        if index >= |s| then 
            if fnd_esc then 
                if fnd_ch then
                    ['\0'] + [ch]  
                else 
                    ['\0']
            else
                "" 
        else 
            if fnd_esc then 
                if fnd_ch then 
                    var integer := GetInt(s, index);
                    if |integer| > 0 then 
                        var occ := ParseInt(integer, |integer| - 1);
                        if occ > 4 then // If the number is 4 or less, the char won't be repeated
                            RepeatChar(ch, occ) + helpDecompress(s, false, false, '\0', index + |integer| + 1)
                        else 
                            ['\0'] + [ch] + [s[index]] + helpDecompress(s, false, false, '\0', index + |integer| + 1)
                    else 
                        ['\0'] + [ch] + helpDecompress(s, false, false, '\0', index + 1)
                else 
                    helpDecompress(s, true, true, s[index], index + 1)
            else 
                if s[index] == '\0' then 
                    helpDecompress(s, true, false, '\0', index + 1) 
                else 
                    [s[index]] + helpDecompress(s, false, false, '\0', index + 1)
    }

    
    function method decompress(s: string) : string 
        requires |s| > 0
        requires forall i :: 0 <= i < |s| ==> 0 <= s[i] as int < 256
        ensures 
            var dcmp := decompress(s); 
            (s[0] == '\0' ==> helpDecompress(s, true, false, '\0', 1) == dcmp)
            &&
            (s[0] != '\0' ==> [s[0]] + helpDecompress(s, false, false, '\0', 1) == dcmp)
            && 
            forall i :: 0 <= i < |dcmp| ==> 0 <= dcmp[i] as int < 256
    {
        if s[0] == '\0' then
            helpDecompress(s, true, false, '\0', 1)
        else 
            [s[0]] + helpDecompress(s, false, false, '\0', 1)
    } 

    lemma {:verify false} identityFunction(s: string)
        requires |s| > 0
        requires forall i :: 0 <= i < |s| ==> 0 <= s[i] as int < 256
        ensures s == decompress(compress(s));
    {
    }
}

method testCompression() {
    var c := new Compression();
    
    var s := "AAAABBBBCCCC";
    s := c.compress(s);
    assert s == "AAAABBBBCCCC";

    s := "AAAAAABBBBCCCC";
    s := c.compress(s);
    assert s == "\0A6\0BBBBCCCC";

    s := c.decompress(s);
    assert s == "AAAAAABBBBCCCC";

    assert s == c.decompress(c.compress(s));
}