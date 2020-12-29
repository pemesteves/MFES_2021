// Dafny program the program compiled into C#
// To recompile, use 'csc' with: /r:System.Numerics.dll
// and choosing /target:exe or /target:library
// You might also want to include compiler switches like:
//     /debug /nowarn:0164 /nowarn:0219 /nowarn:1717 /nowarn:0162

using System;
using System.Numerics;
[assembly: DafnyAssembly.DafnySourceAttribute(@"
// Dafny 2.2.0.10923
// Command Line Options: compression.dfy Io.dfy IoNative.cs
// the program

class Compression {
  constructor ()
  {
  }

  function method repeatOccurences(cur_char: char, occ: int): string
    requires occ > 0
    requires 0 <= cur_char as int < 256
    ensures var s: seq<char> := repeatOccurences(cur_char, occ); (occ <= 3 ==> |s| == occ) && (occ > 3 ==> |s| == 2 + |ToString(occ)|) && forall i: int :: 0 <= i < |s| ==> 0 <= s[i] as int < 256
    decreases cur_char, occ
  {
    if occ <= 3 then
      RepeatChar(cur_char, occ)
    else
      ['\\'] + [cur_char] + ToString(occ)
  }

  function method helpCompress(s: string, cur_char: char, occ: int, index: int): string
    requires 1 <= occ <= |s|
    requires 1 <= index <= |s| && 0 < occ <= index
    requires forall i: int :: index - occ <= i < index ==> s[i] == cur_char
    requires forall i: int :: 0 <= i < |s| ==> 0 <= s[i] as int < 256
    requires 0 <= cur_char as int < 256
    ensures 0 < |helpCompress(s, cur_char, occ, index)|
    ensures var cmp: seq<char> := helpCompress(s, cur_char, occ, index); (forall i: int :: 0 <= i < |cmp| ==> 0 <= cmp[i] as int < 256) && (index >= |s| ==> (occ <= 3 ==> |cmp| == occ) && (occ > 3 ==> |cmp| == 2 + |ToString(occ)|))
    decreases |s| - index
  {
    if index >= |s| then
      repeatOccurences(cur_char, occ)
    else if s[index] == cur_char then
      helpCompress(s, cur_char, occ + 1, index + 1)
    else
      repeatOccurences(cur_char, occ) + helpCompress(s, s[index], 1, index + 1)
  }

  function method compress(s: string): string
    requires |s| > 0
    requires forall i: int :: 0 <= i < |s| ==> 0 <= s[i] as int < 256
    ensures 0 < |compress(s)|
    ensures var cmp: seq<char> := compress(s); forall i: int :: 0 <= i < |cmp| ==> 0 <= cmp[i] as int < 256
    decreases s
  {
    helpCompress(s, s[0], 1, 1)
  }

  function method helpDecompress(s: string, fnd_esc: bool, fnd_ch: bool, ch: char, index: int): string
    requires |s| > 0
    requires 1 <= index <= |s|
    requires fnd_ch ==> s[index - 1] == ch && index >= 2
    requires fnd_esc ==> if fnd_ch then s[index - 2] == '\\' else s[index - 1] == '\\'
    requires forall i: int :: 0 <= i < |s| ==> 0 <= s[i] as int < 256
    ensures var dcmp: seq<char> := helpDecompress(s, fnd_esc, fnd_ch, ch, index); forall i: int :: 0 <= i < |dcmp| ==> 0 <= dcmp[i] as int < 256
    decreases |s| - index
  {
    if index >= |s| then
      if fnd_esc then
        if fnd_ch then
          ['\\'] + [ch]
        else
          ['\\']
      else
        """"
    else if fnd_esc then
      if fnd_ch then
        var integer: string := GetInt(s, index);
        if |integer| > 0 then
          var occ: int := ParseInt(integer, |integer| - 1);
          if occ > 3 then
            RepeatChar(ch, occ) + helpDecompress(s, false, false, '\0', index + |integer|)
          else
            ['\\'] + [ch] + [s[index]] + helpDecompress(s, false, false, '\0', index + |integer|)
        else
          ['\\'] + [ch] + helpDecompress(s, false, false, '\0', index + 1)
      else if IsAlphaChar(s[index]) then
        helpDecompress(s, true, true, s[index], index + 1)
      else
        ['\\'] + [s[index]] + helpDecompress(s, false, false, '\0', index + 1)
    else if s[index] == '\\' then
      helpDecompress(s, true, false, '\0', index + 1)
    else
      [s[index]] + helpDecompress(s, false, false, '\0', index + 1)
  }

  function method decompress(s: string): string
    requires |s| > 0
    requires forall i: int :: 0 <= i < |s| ==> 0 <= s[i] as int < 256
    ensures var dcmp: seq<char> := decompress(s); forall i: int :: 0 <= i < |dcmp| ==> 0 <= dcmp[i] as int < 256
    decreases s
  {
    helpDecompress(s, s[0] == '\\', false, '\0', 1)
  }
}

method ArrayFromSeq<A>(s: seq<A>) returns (a: array<A>)
  ensures a[..] == s
  decreases s
{
  a := new A[|s|] ((i: int) requires 0 <= i < |s| => s[i]);
}

method GetStringFromByteArray(b: array?<byte>) returns (s: string)
  ensures b == null ==> s == """"
  ensures b != null ==> b.Length == |s|
  ensures forall i: int :: 0 <= i < |s| ==> b[i] as char == s[i] && 0 <= s[i] as int < 256
  decreases b
{
  if b == null {
    return """";
  }
  s := """";
  var i := 0;
  while i < b.Length
    invariant 0 <= i <= b.Length
    invariant |s| == i
    invariant forall j: int :: 0 <= j < i ==> s[j] == b[j] as char
    decreases b.Length - i
  {
    s := s + [b[i] as char];
    i := i + 1;
  }
}

method GetByteArrayFromString(s: string) returns (b: array?<byte>)
  requires forall i: int :: 0 <= i < |s| ==> 0 as char <= s[i] < 256 as char
  ensures |s| == 0 ==> b == null
  ensures |s| > 0 ==> b != null && b.Length == |s|
  ensures forall i: int :: 0 <= i < |s| ==> b[i] as char == s[i]
  decreases s
{
  if |s| == 0 {
    return null;
  }
  b := new byte[|s|];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall j: int :: 0 <= j < i ==> b[j] as char == s[j]
    decreases |s| - i
  {
    b[i] := s[i] as int as byte;
    i := i + 1;
  }
}

method {:verify false} copy(ghost env: HostEnvironment, src_name: array<char>, src: FileStream, dst: FileStream, isCompression: bool)
    returns (success: bool)
  requires env.Valid() && env.ok.ok()
  requires src_name[..] == src.Name()
  requires src.Name() in env.files.state() && dst.Name() in env.files.state()
  requires env == src.env == dst.env
  requires env.ok == src.env.ok == dst.env.ok
  requires env.files == src.env.files == dst.env.files
  requires src.IsOpen() && dst.IsOpen()
  requires src != dst
  requires env.files.state()[dst.Name()] == []
  modifies env, env.files, env.ok, src, dst, src.env, src.env.ok, src.env.files
  decreases env, src_name, src, dst, isCompression
{
  var ok, src_len := FileStream.FileLength(src_name, env);
  if !ok {
    print ""Failed to find the length of src file: "", src, ""\n"";
    return false;
  }
  var buffer := new byte[src_len];
  ok := src.Read(0, buffer, 0, src_len);
  if !ok {
    print ""Failed to read the src file: "", src, ""\n"";
    return false;
  }
  assert buffer[..] == old(env.files.state()[src_name[..]]);
  var cmp := new Compression();
  var buffer_string := GetStringFromByteArray(buffer);
  var str := """";
  if |buffer_string| > 0 {
    if isCompression {
      str := cmp.compress(buffer_string);
    } else {
      str := cmp.decompress(buffer_string);
    }
  }
  var cmp_buffer := GetByteArrayFromString(str);
  if cmp_buffer == null {
    print ""Source file "", src, "" is empty"", ""\n"";
    return false;
  }
  var cmp_buff_leng: int32 := cmp_buffer.Length as int32;
  ok := dst.Write(0, cmp_buffer, 0, cmp_buff_leng);
  if !ok {
    print ""Failed to write the dst file: "", dst, ""\n"";
    return false;
  }
  assert cmp_buffer[..] == env.files.state()[dst.Name()];
  ok := src.Close();
  if !ok {
    print ""Failed to close the src file: "", src, ""\n"";
    return false;
  }
  ok := dst.Close();
  if !ok {
    print ""Failed to close the dst file: "", dst, ""\n"";
    return false;
  }
  return true;
}

method {:main} Main(ghost env: HostEnvironment)
  requires env.Valid() && env.ok.ok()
  modifies env, env.files, env.ok
  decreases env
{
  var num_args := HostConstants.NumCommandLineArgs(env);
  if num_args != 4 {
    print ""Expected usage: compression.exe [0|1] [src] [dst]\n"";
    return;
  }
  var compression := HostConstants.GetCommandLineArg(1, env);
  if compression.Length != 1 {
    print ""The first argument should be 1 for compression or 0 for decompression, but instead got: "", compression, ""\n"";
    return;
  }
  if !(compression[0] == '0' || compression[0] == '1') {
    print ""The first argument should be 1 for compression or 0 for decompression, but instead got: "", compression, ""\n"";
    return;
  }
  var isCompression: bool := if compression[0] == '0' then false else true;
  var src := HostConstants.GetCommandLineArg(2, env);
  var dst := HostConstants.GetCommandLineArg(3, env);
  var src_exists := FileStream.FileExists(src, env);
  if !src_exists {
    print ""Couldn't find src file: "", src, ""\n"";
    return;
  }
  var dst_exists := FileStream.FileExists(dst, env);
  if dst_exists {
    print ""The dst file: "", dst, "" already exists.  I don't dare hurt it.\n"";
    return;
  }
  var ok, src_stream := FileStream.Open(src, env);
  if !ok {
    print ""Failed to open src file: "", src, ""\n"";
    return;
  }
  var dst_stream;
  ok, dst_stream := FileStream.Open(dst, env);
  if !ok {
    print ""Failed to open dst file: "", dst, ""\n"";
    return;
  }
  ok := copy(env, src, src_stream, dst_stream, isCompression);
  var c := new Compression();
  var s := ""AAAABBBBCCCC"";
  print s + ""\n"";
  s := c.compress(s);
  print s + ""\n"";
  s := c.decompress(s);
  print s + ""\n"";
}

function method NumDigits(n: int): int
  requires n >= 0
  decreases n
{
  if n <= 9 then
    1
  else
    1 + NumDigits(n / 10)
}

function method ToString(n: int): string
  requires n >= 0
  ensures var s: seq<char> := ToString(n); |s| == NumDigits(n) && forall i: int :: 0 <= i < |s| ==> '0' <= s[i] <= '9' && 0 <= s[i] as int < 256
  decreases n
{
  if n <= 9 then
    [n as char + '0']
  else
    ToString(n / 10) + [(n % 10) as char + '0']
}

function method IsInt(c: char): bool
  decreases c
{
  if c <= '9' && c >= '0' then
    true
  else
    false
}

function method IsAlphaChar(c: char): bool
  decreases c
{
  if (c <= 'Z' && c >= 'A') || (c <= 'z' && c >= 'a') then
    true
  else
    false
}

function method GetInt(s: string, n: int): string
  requires 0 <= n <= |s|
  requires forall i: int :: 0 <= i < |s| ==> 0 <= s[i] as int < 256
  ensures var integerString: seq<char> := GetInt(s, n); (|integerString| != 0 ==> forall i: int :: 0 <= i < |integerString| ==> '0' <= integerString[i] <= '9' && 0 <= integerString[i] as int < 256) && |s| >= n + |integerString|
  decreases |s| - n
{
  if n == |s| then
    """"
  else if IsInt(s[n]) then
    [s[n]] + GetInt(s, n + 1)
  else
    """"
}

function method ParseInt(s: string, i: int): int
  requires 0 <= i < |s|
  requires forall j: int :: 0 <= j <= i ==> '0' <= s[j] <= '9'
  ensures ParseInt(s, i) >= 0
  decreases i
{
  if i == 0 then
    (s[i] - '0') as int
  else
    (s[i] - '0') as int + 10 * ParseInt(s, i - 1)
}

function method RepeatChar(c: char, occ: int): string
  requires occ >= 0
  requires 0 <= c as int < 256
  ensures var s: seq<char> := RepeatChar(c, occ); |s| == occ && forall i: int :: 0 <= i < occ ==> s[i] == c && 0 <= s[i] as int < 256
  decreases occ
{
  if occ == 0 then
    """"
  else
    [c] + RepeatChar(c, occ - 1)
}

newtype {:nativeType ""byte""} byte = b: int
  | 0 <= b < 256

newtype {:nativeType ""ushort""} uint16 = i: int
  | 0 <= i < 65536

newtype {:nativeType ""int""} int32 = i: int
  | -2147483648 <= i < 2147483648

newtype {:nativeType ""uint""} uint32 = i: int
  | 0 <= i < 4294967296

newtype {:nativeType ""ulong""} uint64 = i: int
  | 0 <= i < 18446744073709551616

newtype {:nativeType ""int""} nat32 = i: int
  | 0 <= i < 2147483648

class HostEnvironment {
  ghost var constants: HostConstants?
  ghost var ok: OkState?
  ghost var files: FileSystemState?

  constructor {:axiom} ()

  predicate Valid()
    reads this
    decreases {this}
  {
    constants != null &&
    ok != null &&
    files != null
  }

  method {:axiom} foo()
    ensures Valid()
}

class HostConstants {
  constructor {:axiom} ()
    requires false

  function {:axiom} CommandLineArgs(): seq<seq<char>>
    reads this
    decreases {this}

  static method {:extern} NumCommandLineArgs(ghost env: HostEnvironment) returns (n: uint32)
    requires env.Valid()
    ensures n as int == |env.constants.CommandLineArgs()|
    decreases env

  static method {:extern} GetCommandLineArg(i: uint64, ghost env: HostEnvironment) returns (arg: array<char>)
    requires env.Valid()
    requires 0 <= i as int < |env.constants.CommandLineArgs()|
    ensures fresh(arg)
    ensures arg[..] == env.constants.CommandLineArgs()[i]
    decreases i, env
}

class OkState {
  constructor {:axiom} ()
    requires false

  function {:axiom} ok(): bool
    reads this
    decreases {this}
}

class FileSystemState {
  constructor {:axiom} ()
    requires false

  function {:axiom} state(): map<seq<char>, seq<byte>>
    reads this
    decreases {this}
}

class FileStream {
  ghost var env: HostEnvironment

  function {:axiom} Name(): seq<char>
    reads this
    decreases {this}

  function {:axiom} IsOpen(): bool
    reads this
    decreases {this}

  constructor {:axiom} ()
    requires false

  static method {:extern} FileExists(name: array<char>, ghost env: HostEnvironment?) returns (result: bool)
    requires env != null && env.Valid()
    requires env.ok.ok()
    ensures result <==> old(name[..]) in env.files.state()
    decreases name, env

  static method {:extern} FileLength(name: array<char>, ghost env: HostEnvironment)
      returns (success: bool, len: int32)
    requires env.Valid()
    requires env.ok.ok()
    requires name[..] in env.files.state()
    modifies env.ok
    ensures env.ok.ok() == success
    ensures success ==> len as int == |env.files.state()[name[..]]|
    decreases name, env

  static method {:extern} Open(name: array<char>, ghost env: HostEnvironment)
      returns (ok: bool, f: FileStream)
    requires env.Valid()
    requires env.ok.ok()
    modifies env.ok, env.files
    ensures env.ok.ok() == ok
    ensures ok ==> fresh(f) && f.env == env && f.IsOpen() && f.Name() == name[..] && env.files.state() == if name[..] in old(env.files.state()) then old(env.files.state()) else old(env.files.state())[name[..] := []]
    decreases name, env

  method {:extern} Close() returns (ok: bool)
    requires env.Valid()
    requires env.ok.ok()
    requires IsOpen()
    modifies this, env.ok
    ensures env == old(env)
    ensures env.ok.ok() == ok
    ensures !IsOpen()

  method {:extern} Read(file_offset: nat32, buffer: array?<byte>, start: int32, num_bytes: int32)
      returns (ok: bool)
    requires env.Valid()
    requires env.ok.ok()
    requires IsOpen()
    requires buffer != null
    requires Name() in env.files.state()
    requires file_offset as int + num_bytes as int <= |env.files.state()[Name()]|
    requires 0 <= start as int <= start as int + num_bytes as int <= buffer.Length
    modifies this, env.ok, env.files, buffer
    ensures env == old(env)
    ensures env.ok.ok() == ok
    ensures ok ==> env.files.state() == old(env.files.state())
    ensures Name() == old(Name())
    ensures ok ==> IsOpen()
    ensures ok ==> buffer[..] == buffer[..start] + env.files.state()[Name()][file_offset .. file_offset as int + num_bytes as int] + buffer[start as int + num_bytes as int..]
    decreases file_offset, buffer, start, num_bytes

  method {:extern} Write(file_offset: nat32, buffer: array?<byte>, start: int32, num_bytes: int32)
      returns (ok: bool)
    requires env.Valid()
    requires env.ok.ok()
    requires IsOpen()
    requires buffer != null
    requires Name() in env.files.state()
    requires file_offset as int <= |env.files.state()[Name()]|
    requires 0 <= start as int <= start as int + num_bytes as int <= buffer.Length
    modifies this, env.ok, env.files
    ensures env == old(env)
    ensures env.ok.ok() == ok
    ensures Name() == old(Name())
    ensures ok ==> IsOpen()
    ensures ok ==> var old_file: seq<byte> := old(env.files.state()[Name()]); env.files.state() == old(env.files.state())[Name() := old_file[..file_offset] + buffer[start .. start as int + num_bytes as int] + if file_offset as int + num_bytes as int > |old_file| then [] else old_file[file_offset as int + num_bytes as int..]]
    decreases file_offset, buffer, start, num_bytes
}
")]

#if ISDAFNYRUNTIMELIB
using System; // for Func
using System.Numerics;
#endif

namespace DafnyAssembly {
  [AttributeUsage(AttributeTargets.Assembly)]
  public class DafnySourceAttribute : Attribute {
    public readonly string dafnySourceText;
    public DafnySourceAttribute(string txt) { dafnySourceText = txt; }
  }
}

namespace Dafny
{
  using System.Collections.Generic;
  // set this option if you want to use System.Collections.Immutable and if you know what you're doing.
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
  using System.Collections.Immutable;
  using System.Linq;
#endif

  public class Set<T>
  {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    readonly ImmutableHashSet<T> setImpl;
    readonly bool containsNull;
    Set(ImmutableHashSet<T> d, bool containsNull) {
      this.setImpl = d;
      this.containsNull = containsNull;
    }
    public static readonly Set<T> Empty = new Set<T>(ImmutableHashSet<T>.Empty, false);
    public static Set<T> FromElements(params T[] values) {
      return FromCollection(values);
    }
    public static Set<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }
      return new Set<T>(d.ToImmutable(), containsNull);
    }
    public static Set<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      if (oneMoreValue == null) {
        containsNull = true;
      } else {
        d.Add(oneMoreValue);
      }
      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }
      return new Set<T>(d.ToImmutable(), containsNull);
    }
    public int Length {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }
    public long LongLength {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }
    public IEnumerable<T> Elements {
      get {
        if (containsNull) {
          yield return default(T);
        }
        foreach (var t in this.setImpl) {
          yield return t;
        }
      }
    }
#else
    readonly HashSet<T> setImpl;
    Set(HashSet<T> s) {
      this.setImpl = s;
    }
    public static readonly Set<T> Empty = new Set<T>(new HashSet<T>());
    public static Set<T> FromElements(params T[] values) {
      return FromCollection(values);
    }
    public static Set<T> FromCollection(IEnumerable<T> values) {
      var s = new HashSet<T>(values);
      return new Set<T>(s);
    }
    public static Set<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
      var s = new HashSet<T>(values);
      s.Add(oneMoreValue);
      return new Set<T>(s);
    }
    public int Length {
      get { return this.setImpl.Count; }
    }
    public long LongLength {
      get { return this.setImpl.Count; }
    }
    public IEnumerable<T> Elements {
      get {
        return this.setImpl;
      }
    }
#endif

    public static Set<T> _DafnyDefaultValue() {
      return Empty;
    }

    /// <summary>
    /// This is an inefficient iterator for producing all subsets of "this".
    /// </summary>
    public IEnumerable<Set<T>> AllSubsets {
      get {
        // Start by putting all set elements into a list, but don't include null
        var elmts = new List<T>();
        elmts.AddRange(this.setImpl);
        var n = elmts.Count;
        var which = new bool[n];
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
        var s = ImmutableHashSet<T>.Empty.ToBuilder();
#else
        var s = new HashSet<T>();
#endif
        while (true) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
          // yield both the subset without null and, if null is in the original set, the subset with null included
          var ihs = s.ToImmutable();
          yield return new Set<T>(ihs, false);
          if (containsNull) {
            yield return new Set<T>(ihs, true);
          }
#else
          yield return new Set<T>(new HashSet<T>(s));
#endif
          // "add 1" to "which", as if doing a carry chain.  For every digit changed, change the membership of the corresponding element in "s".
          int i = 0;
          for (; i < n && which[i]; i++) {
            which[i] = false;
            s.Remove(elmts[i]);
          }
          if (i == n) {
            // we have cycled through all the subsets
            break;
          }
          which[i] = true;
          s.Add(elmts[i]);
        }
      }
    }
    public bool Equals(Set<T> other) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      return containsNull == other.containsNull && this.setImpl.SetEquals(other.setImpl);
#else
      return this.setImpl.Count == other.setImpl.Count && IsSubsetOf(other);
#endif
    }
    public override bool Equals(object other) {
      return other is Set<T> && Equals((Set<T>)other);
    }
    public override int GetHashCode() {
      var hashCode = 1;
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      if (containsNull) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(default(T)) + 3);
      }
#endif
      foreach (var t in this.setImpl) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(t)+3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "{";
      var sep = "";
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      if (containsNull) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
#endif
      foreach (var t in this.setImpl) {
        s += sep + Dafny.Helpers.ToString(t);
        sep = ", ";
      }
      return s + "}";
    }
    public bool IsProperSubsetOf(Set<T> other) {
      return this.Length < other.Length && IsSubsetOf(other);
    }
    public bool IsSubsetOf(Set<T> other) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      if (this.containsNull && !other.containsNull) {
        return false;
      }
#endif
      if (other.setImpl.Count < this.setImpl.Count)
        return false;
      foreach (T t in this.setImpl) {
        if (!other.setImpl.Contains(t))
          return false;
      }
      return true;
    }
    public bool IsSupersetOf(Set<T> other) {
      return other.IsSubsetOf(this);
    }
    public bool IsProperSupersetOf(Set<T> other) {
      return other.IsProperSubsetOf(this);
    }
    public bool IsDisjointFrom(Set<T> other) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      if (this.containsNull && other.containsNull) {
        return false;
      }
      ImmutableHashSet<T> a, b;
#else
      HashSet<T> a, b;
#endif
      if (this.setImpl.Count < other.setImpl.Count) {
        a = this.setImpl; b = other.setImpl;
      } else {
        a = other.setImpl; b = this.setImpl;
      }
      foreach (T t in a) {
        if (b.Contains(t))
          return false;
      }
      return true;
    }
    public bool Contains<G>(G t) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      return t == null ? containsNull : t is T && this.setImpl.Contains((T)(object)t);
#else
      return (t == null || t is T) && this.setImpl.Contains((T)(object)t);
#endif
    }
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    public Set<T> Union(Set<T> other) {
      return new Set<T>(this.setImpl.Union(other.setImpl), containsNull || other.containsNull);
    }
    public Set<T> Intersect(Set<T> other) {
      return new Set<T>(this.setImpl.Intersect(other.setImpl), containsNull && other.containsNull);
    }
    public Set<T> Difference(Set<T> other) {
        return new Set<T>(this.setImpl.Except(other.setImpl), containsNull && !other.containsNull);
    }
#else
    public Set<T> Union(Set<T> other) {
      if (this.setImpl.Count == 0)
        return other;
      else if (other.setImpl.Count == 0)
        return this;
      HashSet<T> a, b;
      if (this.setImpl.Count < other.setImpl.Count) {
        a = this.setImpl; b = other.setImpl;
      } else {
        a = other.setImpl; b = this.setImpl;
      }
      var r = new HashSet<T>();
      foreach (T t in b)
        r.Add(t);
      foreach (T t in a)
        r.Add(t);
      return new Set<T>(r);
    }
    public Set<T> Intersect(Set<T> other) {
      if (this.setImpl.Count == 0)
        return this;
      else if (other.setImpl.Count == 0)
        return other;
      HashSet<T> a, b;
      if (this.setImpl.Count < other.setImpl.Count) {
        a = this.setImpl; b = other.setImpl;
      } else {
        a = other.setImpl; b = this.setImpl;
      }
      var r = new HashSet<T>();
      foreach (T t in a) {
        if (b.Contains(t))
          r.Add(t);
      }
      return new Set<T>(r);
    }
    public Set<T> Difference(Set<T> other) {
      if (this.setImpl.Count == 0)
        return this;
      else if (other.setImpl.Count == 0)
        return this;
      var r = new HashSet<T>();
      foreach (T t in this.setImpl) {
        if (!other.setImpl.Contains(t))
          r.Add(t);
      }
      return new Set<T>(r);
    }
#endif
  }

  public class MultiSet<T>
  {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    readonly ImmutableDictionary<T, int> dict;
#else
    readonly Dictionary<T, int> dict;
#endif
    readonly BigInteger occurrencesOfNull;  // stupidly, a Dictionary in .NET cannot use "null" as a key
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    MultiSet(ImmutableDictionary<T, int>.Builder d, BigInteger occurrencesOfNull) {
      dict = d.ToImmutable();
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static readonly MultiSet<T> Empty = new MultiSet<T>(ImmutableDictionary<T, int>.Empty.ToBuilder(), BigInteger.Zero);
#else
    MultiSet(Dictionary<T, int> d, BigInteger occurrencesOfNull) {
      this.dict = d;
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static MultiSet<T> Empty = new MultiSet<T>(new Dictionary<T, int>(0), BigInteger.Zero);
#endif
    public static MultiSet<T> FromElements(params T[] values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var d = new Dictionary<T, int>(values.Length);
#endif
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          var i = 0;
          if (!d.TryGetValue(t, out i)) {
            i = 0;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }
    public static MultiSet<T> FromCollection(ICollection<T> values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var d = new Dictionary<T, int>();
#endif
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          var i = 0;
          if (!d.TryGetValue(t, out i)) {
            i = 0;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }
    public static MultiSet<T> FromSeq(Sequence<T> values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var d = new Dictionary<T, int>();
#endif
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values.Elements) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          var i = 0;
          if (!d.TryGetValue(t, out i)) {
            i = 0;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }
    public static MultiSet<T> FromSet(Set<T> values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var d = new Dictionary<T, int>();
#endif
      var containsNull = false;
      foreach (T t in values.Elements) {
        if (t == null) {
          containsNull = true;
        } else {
          d[t] = 1;
        }
      }
      return new MultiSet<T>(d, containsNull ? BigInteger.One : BigInteger.Zero);
    }

    public static MultiSet<T> _DafnyDefaultValue() {
      return Empty;
    }

    public bool Equals(MultiSet<T> other) {
      return other.IsSubsetOf(this) && this.IsSubsetOf(other);
    }
    public override bool Equals(object other) {
      return other is MultiSet<T> && Equals((MultiSet<T>)other);
    }
    public override int GetHashCode() {
      var hashCode = 1;
      if (occurrencesOfNull > 0) {
        var key = Dafny.Helpers.GetHashCode(default(T));
        key = (key << 3) | (key >> 29) ^ occurrencesOfNull.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "multiset{";
      var sep = "";
      for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
      foreach (var kv in dict) {
        var t = Dafny.Helpers.ToString(kv.Key);
        for (int i = 0; i < kv.Value; i++) {
          s += sep + t;
          sep = ", ";
        }
      }
      return s + "}";
    }
    public bool IsProperSubsetOf(MultiSet<T> other) {
      return !Equals(other) && IsSubsetOf(other);
    }
    public bool IsSubsetOf(MultiSet<T> other) {
      if (other.occurrencesOfNull < this.occurrencesOfNull) {
        return false;
      }
      foreach (T t in dict.Keys) {
        if (!other.dict.ContainsKey(t) || other.dict[t] < dict[t])
          return false;
      }
      return true;
    }
    public bool IsSupersetOf(MultiSet<T> other) {
      return other.IsSubsetOf(this);
    }
    public bool IsProperSupersetOf(MultiSet<T> other) {
      return other.IsProperSubsetOf(this);
    }
    public bool IsDisjointFrom(MultiSet<T> other) {
      if (occurrencesOfNull > 0 && other.occurrencesOfNull > 0) {
        return false;
      }
      foreach (T t in dict.Keys) {
        if (other.dict.ContainsKey(t))
          return false;
      }
      foreach (T t in other.dict.Keys) {
        if (dict.ContainsKey(t))
          return false;
      }
      return true;
    }

    public bool Contains<G>(G t) {
      return t == null ? occurrencesOfNull > 0 : t is T && dict.ContainsKey((T)(object)t);
    }
    public MultiSet<T> Union(MultiSet<T> other) {
      if (dict.Count + occurrencesOfNull == 0)
        return other;
      else if (other.dict.Count + other.occurrencesOfNull == 0)
        return this;
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var r = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var r = new Dictionary<T, int>();
#endif
      foreach (T t in dict.Keys) {
        var i = 0;
        if (!r.TryGetValue(t, out i)) {
          i = 0;
        }
        r[t] = i + dict[t];
      }
      foreach (T t in other.dict.Keys) {
        var i = 0;
        if (!r.TryGetValue(t, out i)) {
          i = 0;
        }
        r[t] = i + other.dict[t];
      }
      return new MultiSet<T>(r, occurrencesOfNull + other.occurrencesOfNull);
    }
    public MultiSet<T> Intersect(MultiSet<T> other) {
      if (dict.Count == 0 && occurrencesOfNull == 0)
        return this;
      else if (other.dict.Count == 0 && other.occurrencesOfNull == 0)
        return other;
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var r = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var r = new Dictionary<T, int>();
#endif
      foreach (T t in dict.Keys) {
        if (other.dict.ContainsKey(t)) {
          r.Add(t, other.dict[t] < dict[t] ? other.dict[t] : dict[t]);
        }
      }
      return new MultiSet<T>(r, other.occurrencesOfNull < occurrencesOfNull ? other.occurrencesOfNull : occurrencesOfNull);
    }
    public MultiSet<T> Difference(MultiSet<T> other) { // \result == this - other
      if (dict.Count == 0 && occurrencesOfNull == 0)
        return this;
      else if (other.dict.Count == 0 && other.occurrencesOfNull == 0)
        return this;
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var r = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var r = new Dictionary<T, int>();
#endif
      foreach (T t in dict.Keys) {
        if (!other.dict.ContainsKey(t)) {
          r.Add(t, dict[t]);
        } else if (other.dict[t] < dict[t]) {
          r.Add(t, dict[t] - other.dict[t]);
        }
      }
      return new MultiSet<T>(r, other.occurrencesOfNull < occurrencesOfNull ? occurrencesOfNull - other.occurrencesOfNull : BigInteger.Zero);
    }

    public IEnumerable<T> Elements {
      get {
        for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
          yield return default(T);
        }
        foreach (var item in dict) {
          for (int i = 0; i < item.Value; i++) {
            yield return item.Key;
          }
        }
      }
    }

    public IEnumerable<T> ElementsWithoutDuplicates {
      get {
        if (!occurrencesOfNull.IsZero) {
          yield return default(T);
        }
        foreach (var item in dict) {
          yield return item.Key;
        }
      }
    }
  }

  public class Map<U, V>
  {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    readonly ImmutableDictionary<U, V> dict;
#else
    readonly Dictionary<U, V> dict;
#endif
    readonly bool hasNullValue;  // true when "null" is a key of the Map
    readonly V nullValue;  // if "hasNullValue", the value that "null" maps to

#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    Map(ImmutableDictionary<U, V>.Builder d, bool hasNullValue, V nullValue) {
      dict = d.ToImmutable();
      this.hasNullValue = hasNullValue;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(ImmutableDictionary<U, V>.Empty.ToBuilder(), false, default(V));
#else
    Map(Dictionary<U, V> d, bool hasNullValue, V nullValue) {
      this.dict = d;
      this.hasNullValue = hasNullValue;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(new Dictionary<U, V>(), false, default(V));
#endif

    public static Map<U, V> FromElements(params Pair<U, V>[] values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
#else
      var d = new Dictionary<U, V>(values.Length);
#endif
      var hasNullValue = false;
      var nullValue = default(V);
      foreach (Pair<U, V> p in values) {
        if (p.Car == null) {
          hasNullValue = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullValue, nullValue);
    }
    public static Map<U, V> FromCollection(List<Pair<U, V>> values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
#else
      var d = new Dictionary<U, V>(values.Count);
#endif
      var hasNullValue = false;
      var nullValue = default(V);
      foreach (Pair<U, V> p in values) {
        if (p.Car == null) {
          hasNullValue = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullValue, nullValue);
    }
    public int Length {
      get { return dict.Count + (hasNullValue ? 1 : 0); }
    }
    public long LongLength {
      get { return dict.Count + (hasNullValue ? 1 : 0); }
    }
    public static Map<U, V> _DafnyDefaultValue() {
      return Empty;
    }

    public bool Equals(Map<U, V> other) {
      if (hasNullValue != other.hasNullValue || dict.Count != other.dict.Count) {
        return false;
      } else if (hasNullValue && !Dafny.Helpers.AreEqual(nullValue, other.nullValue)) {
        return false;
      }
      foreach (U u in dict.Keys) {
        V v1 = dict[u];
        V v2;
        if (!other.dict.TryGetValue(u, out v2)) {
          return false; // other dictionary does not contain this element
        }
        if (!Dafny.Helpers.AreEqual(v1, v2)) {
          return false;
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      return other is Map<U, V> && Equals((Map<U, V>)other);
    }
    public override int GetHashCode() {
      var hashCode = 1;
      if (hasNullValue) {
        var key = Dafny.Helpers.GetHashCode(default(U));
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(nullValue);
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(kv.Value);
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "map[";
      var sep = "";
      if (hasNullValue) {
        s += sep + Dafny.Helpers.ToString(default(U)) + " := " + Dafny.Helpers.ToString(nullValue);
        sep = ", ";
      }
      foreach (var kv in dict) {
        s += sep + Dafny.Helpers.ToString(kv.Key) + " := " + Dafny.Helpers.ToString(kv.Value);
        sep = ", ";
      }
      return s + "]";
    }
    public bool IsDisjointFrom(Map<U, V> other) {
      if (hasNullValue && other.hasNullValue) {
        return false;
      }
      foreach (U u in dict.Keys) {
        if (other.dict.ContainsKey(u))
          return false;
      }
      foreach (U u in other.dict.Keys) {
        if (dict.ContainsKey(u))
          return false;
      }
      return true;
    }
    public bool Contains<G>(G u) {
      return u == null ? hasNullValue : u is U && dict.ContainsKey((U)(object)u);
    }
    public V Select(U index) {
      // evidently, the following will throw some exception if "index" in not a key of the map
      return index == null && hasNullValue ? nullValue : dict[index];
    }
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    public Map<U, V> Update(U index, V val) {
      var d = dict.ToBuilder();
      if (index == null) {
        return new Map<U, V>(d, true, val);
      } else {
        d[index] = val;
        return new Map<U, V>(d, hasNullValue, nullValue);
      }
    }
#else
    public Map<U, V> Update(U index, V val) {
      if (index == null) {
        return new Map<U, V>(dict, true, val);
      } else {
        var d = new Dictionary<U, V>(dict);
        d[index] = val;
        return new Map<U, V>(d, hasNullValue, nullValue);
      }
    }
#endif
    public IEnumerable<U> Domain {
      get {
        return dict.Keys;
      }
    }
    public Set<U> Keys
    {
      get
      {
        if (hasNullValue) {
          return Dafny.Set<U>.FromCollectionPlusOne(dict.Keys, default(U));
        } else {
          return Dafny.Set<U>.FromCollection(dict.Keys);
        }
      }
    }
    public Set<V> Values
    {
      get
      {
        if (hasNullValue) {
          return Dafny.Set<V>.FromCollectionPlusOne(dict.Values, nullValue);
        } else {
          return Dafny.Set<V>.FromCollection(dict.Values);
        }
      }
    }
    public Set<@_System.@__tuple_h2<U, V>> Items
    {
      get
      {
        HashSet<@_System.@__tuple_h2<U, V>> result = new HashSet<@_System.@__tuple_h2<U, V>>();
        if (hasNullValue) {
          result.Add(new @_System.@__tuple_h2<U, V>(new @_System.@__tuple_h2____hMake2<U, V>(default(U), nullValue)));
        }
        foreach (KeyValuePair<U, V> kvp in dict) {
          result.Add(new @_System.@__tuple_h2<U,V>(new @_System.@__tuple_h2____hMake2<U, V>(kvp.Key, kvp.Value)));
        }
        return Dafny.Set<@_System.@__tuple_h2<U, V>>.FromCollection(result);
      }
    }
  }

  public class Sequence<T>
  {
    readonly T[] elmts;
    public Sequence(T[] ee) {
      elmts = ee;
    }
    public static Sequence<T> Empty {
      get {
        return new Sequence<T>(new T[0]);
      }
    }
    public static Sequence<T> FromElements(params T[] values) {
      return new Sequence<T>(values);
    }
    public static Sequence<char> FromString(string s) {
      return new Sequence<char>(s.ToCharArray());
    }
    public static Sequence<T> _DafnyDefaultValue() {
      return Empty;
    }
    public int Length {
      get { return elmts.Length; }
    }
    public long LongLength {
      get { return elmts.LongLength; }
    }
    public T[] Elements {
      get {
        return elmts;
      }
    }
    public IEnumerable<T> UniqueElements {
      get {
        var st = Set<T>.FromElements(elmts);
        return st.Elements;
      }
    }
    public T Select(ulong index) {
      return elmts[index];
    }
    public T Select(long index) {
      return elmts[index];
    }
    public T Select(uint index) {
      return elmts[index];
    }
    public T Select(int index) {
      return elmts[index];
    }
    public T Select(BigInteger index) {
      return elmts[(int)index];
    }
    public Sequence<T> Update(long index, T t) {
      T[] a = (T[])elmts.Clone();
      a[index] = t;
      return new Sequence<T>(a);
    }
    public Sequence<T> Update(ulong index, T t) {
      return Update((long)index, t);
    }
    public Sequence<T> Update(BigInteger index, T t) {
      return Update((long)index, t);
    }
    public bool Equals(Sequence<T> other) {
      int n = elmts.Length;
      return n == other.elmts.Length && EqualUntil(other, n);
    }
    public override bool Equals(object other) {
      return other is Sequence<T> && Equals((Sequence<T>)other);
    }
    public override int GetHashCode() {
      if (elmts == null || elmts.Length == 0)
        return 0;
      var hashCode = 0;
      for (var i = 0; i < elmts.Length; i++) {
        hashCode = (hashCode << 3) | (hashCode >> 29) ^ Dafny.Helpers.GetHashCode(elmts[i]);
      }
      return hashCode;
    }
    public override string ToString() {
      if (elmts is char[]) {
        var s = "";
        foreach (var t in elmts) {
          s += t.ToString();
        }
        return s;
      } else {
        var s = "[";
        var sep = "";
        foreach (var t in elmts) {
          s += sep + Dafny.Helpers.ToString(t);
          sep = ", ";
        }
        return s + "]";
      }
    }
    bool EqualUntil(Sequence<T> other, int n) {
      for (int i = 0; i < n; i++) {
        if (!Dafny.Helpers.AreEqual(elmts[i], other.elmts[i]))
          return false;
      }
      return true;
    }
    public bool IsProperPrefixOf(Sequence<T> other) {
      int n = elmts.Length;
      return n < other.elmts.Length && EqualUntil(other, n);
    }
    public bool IsPrefixOf(Sequence<T> other) {
      int n = elmts.Length;
      return n <= other.elmts.Length && EqualUntil(other, n);
    }
    public Sequence<T> Concat(Sequence<T> other) {
      if (elmts.Length == 0)
        return other;
      else if (other.elmts.Length == 0)
        return this;
      T[] a = new T[elmts.Length + other.elmts.Length];
      System.Array.Copy(elmts, 0, a, 0, elmts.Length);
      System.Array.Copy(other.elmts, 0, a, elmts.Length, other.elmts.Length);
      return new Sequence<T>(a);
    }
    public bool Contains<G>(G g) {
      if (g == null || g is T) {
        var t = (T)(object)g;
        int n = elmts.Length;
        for (int i = 0; i < n; i++) {
          if (Dafny.Helpers.AreEqual(t, elmts[i]))
            return true;
        }
      }
      return false;
    }
    public Sequence<T> Take(long m) {
      if (elmts.LongLength == m)
        return this;
      T[] a = new T[m];
      System.Array.Copy(elmts, a, m);
      return new Sequence<T>(a);
    }
    public Sequence<T> Take(ulong n) {
      return Take((long)n);
    }
    public Sequence<T> Take(BigInteger n) {
      return Take((long)n);
    }
    public Sequence<T> Drop(long m) {
      if (m == 0)
        return this;
      T[] a = new T[elmts.Length - m];
      System.Array.Copy(elmts, m, a, 0, elmts.Length - m);
      return new Sequence<T>(a);
    }
    public Sequence<T> Drop(ulong n) {
      return Drop((long)n);
    }
    public Sequence<T> Drop(BigInteger n) {
      if (n.IsZero)
        return this;
      return Drop((long)n);
    }
  }
  public struct Pair<A, B>
  {
    public readonly A Car;
    public readonly B Cdr;
    public Pair(A a, B b) {
      this.Car = a;
      this.Cdr = b;
    }
  }
  public partial class Helpers {
    public static bool AreEqual<G>(G a, G b) {
      return a == null ? b == null : a.Equals(b);
    }
    public static int GetHashCode<G>(G g) {
      return g == null ? 1001 : g.GetHashCode();
    }
    public static string ToString<G>(G g) {
      return g == null ? "null" : g.ToString();
    }
    public static G Default<G>() {
      System.Type ty = typeof(G);
      System.Reflection.MethodInfo mInfo = ty.GetMethod("_DafnyDefaultValue");
      if (mInfo != null) {
        G g = (G)mInfo.Invoke(null, null);
        return g;
      } else {
        return default(G);
      }
    }
    public static System.Predicate<BigInteger> PredicateConverter_byte(System.Predicate<byte> pred) {
      return x => pred((byte)x);
    }
    public static System.Predicate<BigInteger> PredicateConverter_sbyte(System.Predicate<sbyte> pred) {
      return x => pred((sbyte)x);
    }
    public static System.Predicate<BigInteger> PredicateConverter_ushort(System.Predicate<ushort> pred) {
      return x => pred((ushort)x);
    }
    public static System.Predicate<BigInteger> PredicateConverter_short(System.Predicate<short> pred) {
      return x => pred((short)x);
    }
    public static System.Predicate<BigInteger> PredicateConverter_uint(System.Predicate<uint> pred) {
      return x => pred((uint)x);
    }
    public static System.Predicate<BigInteger> PredicateConverter_int(System.Predicate<int> pred) {
      return x => pred((int)x);
    }
    public static System.Predicate<BigInteger> PredicateConverter_ulong(System.Predicate<ulong> pred) {
      return x => pred((ulong)x);
    }
    public static System.Predicate<BigInteger> PredicateConverter_long(System.Predicate<long> pred) {
      return x => pred((long)x);
    }
    // Computing forall/exists quantifiers
    public static bool QuantBool(bool frall, System.Predicate<bool> pred) {
      if (frall) {
        return pred(false) && pred(true);
      } else {
        return pred(false) || pred(true);
      }
    }
    public static bool QuantChar(bool frall, System.Predicate<char> pred) {
      for (int i = 0; i < 0x10000; i++) {
        if (pred((char)i) != frall) { return !frall; }
      }
      return frall;
    }
    public static bool QuantInt(BigInteger lo, BigInteger hi, bool frall, System.Predicate<BigInteger> pred) {
      for (BigInteger i = lo; i < hi; i++) {
        if (pred(i) != frall) { return !frall; }
      }
      return frall;
    }
    public static bool QuantSingle<U>(U u, bool frall, System.Predicate<U> pred) {
      return pred(u);
    }
    public static bool QuantSet<U>(Dafny.Set<U> set, bool frall, System.Predicate<U> pred) {
      foreach (var u in set.Elements) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    public static bool QuantMultiSet<U>(Dafny.MultiSet<U> multiset, bool frall, System.Predicate<U> pred) {
      foreach (var u in multiset.ElementsWithoutDuplicates) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    public static bool QuantSubSets<U>(Dafny.Set<U> set, bool frall, System.Predicate<Dafny.Set<U>> pred) {
      foreach (var u in set.AllSubsets) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    public static bool QuantMap<U,V>(Dafny.Map<U,V> map, bool frall, System.Predicate<U> pred) {
      foreach (var u in map.Domain) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    public static bool QuantSeq<U>(Dafny.Sequence<U> seq, bool frall, System.Predicate<U> pred) {
      foreach (var u in seq.Elements) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    public static bool QuantDatatype<U>(IEnumerable<U> set, bool frall, System.Predicate<U> pred) {
      foreach (var u in set) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    // Enumerating other collections
    public delegate Dafny.Set<T> ComprehensionDelegate<T>();
    public delegate Dafny.Map<U, V> MapComprehensionDelegate<U, V>();
    public static IEnumerable<bool> AllBooleans {
      get {
        yield return false;
        yield return true;
      }
    }
    public static IEnumerable<char> AllChars {
      get {
        for (int i = 0; i < 0x10000; i++) {
          yield return (char)i;
        }
      }
    }
    public static IEnumerable<BigInteger> AllIntegers {
      get {
        yield return new BigInteger(0);
        for (var j = new BigInteger(1);; j++) {
          yield return j;
          yield return -j;
        }
      }
    }
    public static IEnumerable<BigInteger> IntegerRange(Nullable<BigInteger> lo, Nullable<BigInteger> hi) {
      if (lo == null) {
        for (var j = (BigInteger)hi; true; ) {
          j--;
          yield return j;
        }
      } else if (hi == null) {
        for (var j = (BigInteger)lo; true; j++) {
          yield return j;
        }
      } else {
        for (var j = (BigInteger)lo; j < hi; j++) {
          yield return j;
        }
      }
    }
    public static IEnumerable<T> SingleValue<T>(T e) {
      yield return e;
    }
    // pre: b != 0
    // post: result == a/b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanDivision_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanDivision_int(a, b);
    }
    public static short EuclideanDivision_short(short a, short b) {
      return (short)EuclideanDivision_int(a, b);
    }
    public static int EuclideanDivision_int(int a, int b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (int)(((uint)(a)) / ((uint)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((int)(((uint)(a)) / ((uint)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((int)(((uint)(-(a + 1))) / ((uint)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((int)(((uint)(-(a + 1))) / ((uint)(unchecked(-b))))) + 1;
        }
      }
    }
    public static long EuclideanDivision_long(long a, long b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (long)(((ulong)(a)) / ((ulong)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((long)(((ulong)(a)) / ((ulong)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((long)(((ulong)(-(a + 1))) / ((ulong)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((long)(((ulong)(-(a + 1))) / ((ulong)(unchecked(-b))))) + 1;
        }
      }
    }
    public static BigInteger EuclideanDivision(BigInteger a, BigInteger b) {
      if (0 <= a.Sign) {
        if (0 <= b.Sign) {
          // +a +b: a/b
          return BigInteger.Divide(a, b);
        } else {
          // +a -b: -(a/(-b))
          return BigInteger.Negate(BigInteger.Divide(a, BigInteger.Negate(b)));
        }
      } else {
        if (0 <= b.Sign) {
          // -a +b: -((-a-1)/b) - 1
          return BigInteger.Negate(BigInteger.Divide(BigInteger.Negate(a) - 1, b)) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return BigInteger.Divide(BigInteger.Negate(a) - 1, BigInteger.Negate(b)) + 1;
        }
      }
    }
    // pre: b != 0
    // post: result == a%b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanModulus_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanModulus_int(a, b);
    }
    public static short EuclideanModulus_short(short a, short b) {
      return (short)EuclideanModulus_int(a, b);
    }
    public static int EuclideanModulus_int(int a, int b) {
      uint bp = (0 <= b) ? (uint)b : (uint)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (int)(((uint)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        uint c = ((uint)(unchecked(-a))) % bp;
        return (int)(c == 0 ? c : bp - c);
      }
    }
    public static long EuclideanModulus_long(long a, long b) {
      ulong bp = (0 <= b) ? (ulong)b : (ulong)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (long)(((ulong)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        ulong c = ((ulong)(unchecked(-a))) % bp;
        return (long)(c == 0 ? c : bp - c);
      }
    }
    public static BigInteger EuclideanModulus(BigInteger a, BigInteger b) {
      var bp = BigInteger.Abs(b);
      if (0 <= a.Sign) {
        // +a: a % b'
        return BigInteger.Remainder(a, bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        var c = BigInteger.Remainder(BigInteger.Negate(a), bp);
        return c.IsZero ? c : BigInteger.Subtract(bp, c);
      }
    }
    public static Sequence<T> SeqFromArray<T>(T[] array) {
      return new Sequence<T>((T[])array.Clone());
    }
    // In .NET version 4.5, it it possible to mark a method with "AggressiveInlining", which says to inline the
    // method if possible.  Method "ExpressionSequence" would be a good candidate for it:
    // [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    public static U ExpressionSequence<T, U>(T t, U u)
    {
      return u;
    }

    public static U Let<T, U>(T t, Func<T,U> f) {
      return f(t);
    }

    public delegate Result Function<Input,Result>(Input input);

    public static A Id<A>(A a) {
      return a;
    }

    public static bool BigOrdinal_IsLimit(BigInteger ord) {
      return ord == 0;
    }
    public static bool BigOrdinal_IsSucc(BigInteger ord) {
      return 0 < ord;
    }
    public static BigInteger BigOrdinal_Offset(BigInteger ord) {
      return ord;
    }
    public static bool BigOrdinal_IsNat(BigInteger ord) {
      return true;  // at run time, every ORDINAL is a natural number
    }
  }

  public struct BigRational
  {
    public static readonly BigRational ZERO = new BigRational(0);

    // We need to deal with the special case "num == 0 && den == 0", because
    // that's what C#'s default struct constructor will produce for BigRational. :(
    // To deal with it, we ignore "den" when "num" is 0.
    BigInteger num, den;  // invariant 1 <= den || (num == 0 && den == 0)
    public override string ToString() {
      if (num.IsZero || den.IsOne) {
        return string.Format("{0}.0", num);
      } else {
        return string.Format("({0}.0 / {1}.0)", num, den);
      }
    }
    public BigRational(int n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(BigInteger n, BigInteger d) {
      // requires 1 <= d
      num = n;
      den = d;
    }
    public BigInteger ToBigInteger() {
      if (num.IsZero || den.IsOne) {
        return num;
      } else if (0 < num.Sign) {
        return num / den;
      } else {
        return (num - den + 1) / den;
      }
    }
    /// <summary>
    /// Returns values such that aa/dd == a and bb/dd == b.
    /// </summary>
    private static void Normalize(BigRational a, BigRational b, out BigInteger aa, out BigInteger bb, out BigInteger dd) {
      if (a.num.IsZero) {
        aa = a.num;
        bb = b.num;
        dd = b.den;
      } else if (b.num.IsZero) {
        aa = a.num;
        dd = a.den;
        bb = b.num;
      } else {
        var gcd = BigInteger.GreatestCommonDivisor(a.den, b.den);
        var xx = a.den / gcd;
        var yy = b.den / gcd;
        // We now have a == a.num / (xx * gcd) and b == b.num / (yy * gcd).
        aa = a.num * yy;
        bb = b.num * xx;
        dd = a.den * yy;
      }
    }
    public int CompareTo(BigRational that) {
      // simple things first
      int asign = this.num.Sign;
      int bsign = that.num.Sign;
      if (asign < 0 && 0 <= bsign) {
        return -1;
      } else if (asign <= 0 && 0 < bsign) {
        return -1;
      } else if (bsign < 0 && 0 <= asign) {
        return 1;
      } else if (bsign <= 0 && 0 < asign) {
        return 1;
      }
      BigInteger aa, bb, dd;
      Normalize(this, that, out aa, out bb, out dd);
      return aa.CompareTo(bb);
    }
    public override int GetHashCode() {
      return num.GetHashCode() + 29 * den.GetHashCode();
    }
    public override bool Equals(object obj) {
      if (obj is BigRational) {
        return this == (BigRational)obj;
      } else {
        return false;
      }
    }
    public static bool operator ==(BigRational a, BigRational b) {
      return a.CompareTo(b) == 0;
    }
    public static bool operator !=(BigRational a, BigRational b) {
      return a.CompareTo(b) != 0;
    }
    public static bool operator >(BigRational a, BigRational b) {
      return a.CompareTo(b) > 0;
    }
    public static bool operator >=(BigRational a, BigRational b) {
      return a.CompareTo(b) >= 0;
    }
    public static bool operator <(BigRational a, BigRational b) {
      return a.CompareTo(b) < 0;
    }
    public static bool operator <=(BigRational a, BigRational b) {
      return a.CompareTo(b) <= 0;
    }
    public static BigRational operator +(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa + bb, dd);
    }
    public static BigRational operator -(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa - bb, dd);
    }
    public static BigRational operator -(BigRational a) {
      return new BigRational(-a.num, a.den);
    }
    public static BigRational operator *(BigRational a, BigRational b) {
      return new BigRational(a.num * b.num, a.den * b.den);
    }
    public static BigRational operator /(BigRational a, BigRational b) {
      // Compute the reciprocal of b
      BigRational bReciprocal;
      if (0 < b.num.Sign) {
        bReciprocal = new BigRational(b.den, b.num);
      } else {
        // this is the case b.num < 0
        bReciprocal = new BigRational(-b.den, -b.num);
      }
      return a * bReciprocal;
    }
  }
}

namespace @_System
{

  public abstract class Base___tuple_h2<@T0, @T1> { }
  public class __tuple_h2____hMake2<@T0, @T1> : Base___tuple_h2<@T0, @T1>
  {
    public readonly @T0 @_0;
    public readonly @T1 @_1;
    public __tuple_h2____hMake2(@T0 @_0, @T1 @_1)
    {
      this.@_0 = @_0;
      this.@_1 = @_1;
    }
    public override bool Equals(object other)
    {
      var oth = other as _System.@__tuple_h2____hMake2<@T0, @T1>;
      return oth != null && this.@_0.Equals(oth.@_0) && Dafny.Helpers.AreEqual(this.@_1, oth.@_1);
    }
    public override int GetHashCode()
    {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.@_0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.@_1));
      return (int)hash;
    }
    public override string ToString()
    {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this.@_0);
      s += ", ";
      s += Dafny.Helpers.ToString(this.@_1);
      s += ")";
      return s;
    }
  }
  public struct @__tuple_h2<@T0, @T1>
  {
    Base___tuple_h2<@T0, @T1> _d;
    public Base___tuple_h2<@T0, @T1> _D
    {
      get
      {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @__tuple_h2(Base___tuple_h2<@T0, @T1> d) { this._d = d; }
    static Base___tuple_h2<@T0, @T1> theDefault;
    public static Base___tuple_h2<@T0, @T1> Default
    {
      get
      {
        if (theDefault == null) {
          theDefault = new _System.@__tuple_h2____hMake2<@T0, @T1>(default(@T0), default(@T1));
        }
        return theDefault;
      }
    }
    public override bool Equals(object other)
    {
      return other is @__tuple_h2<@T0, @T1> && _D.Equals(((@__tuple_h2<@T0, @T1>)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is____hMake2 { get { return _D is __tuple_h2____hMake2<@T0, @T1>; } }
    public @T0 dtor__0 { get { return ((__tuple_h2____hMake2<@T0, @T1>)_D).@_0; } }
    public @T1 dtor__1 { get { return ((__tuple_h2____hMake2<@T0, @T1>)_D).@_1; } }
  }
} // end of namespace _System
namespace Dafny {
  internal class ArrayHelpers {
      public static T[] InitNewArray1<T>(T z, BigInteger size0) {
        int s0 = (int)size0;
        T[] a = new T[s0];
        for (int i0 = 0; i0 < s0; i0++)
          a[i0] = z;
        return a;
      }
  }
}
namespace @_System {



  public abstract class Base___tuple_h0 { }
  public class __tuple_h0____hMake0 : Base___tuple_h0 {
    public __tuple_h0____hMake0() {
    }
    public override bool Equals(object other) {
      var oth = other as _System.@__tuple_h0____hMake0;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      return s;
    }
  }
  public struct @__tuple_h0 {
    Base___tuple_h0 _d;
    public Base___tuple_h0 _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @__tuple_h0(Base___tuple_h0 d) { this._d = d; }
    static Base___tuple_h0 theDefault;
    public static Base___tuple_h0 Default {
      get {
        if (theDefault == null) {
          theDefault = new _System.@__tuple_h0____hMake0();
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @__tuple_h0 && _D.Equals(((@__tuple_h0)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is____hMake0 { get { return _D is __tuple_h0____hMake0; } }
    public static System.Collections.Generic.IEnumerable<@__tuple_h0> AllSingletonConstructors {
      get {
        yield return new @__tuple_h0(new __tuple_h0____hMake0());
        yield break;
      }
    }
  }
} // end of namespace _System
namespace @__default {

  public partial class @Compression {
    public void @__ctor()
    {
      var _this = this;
    TAIL_CALL_START: ;
    }
    public Dafny.Sequence<char> @repeatOccurences(char @cur__char, BigInteger @occ) {
      if ((@occ) <= (new BigInteger(3))) {
        return @__default.@RepeatChar(@cur__char, @occ);
      } else {
        return ((Dafny.Sequence<char>.FromElements('\\')).@Concat(Dafny.Sequence<char>.FromElements(@cur__char))).@Concat(@__default.@ToString(@occ));
      }
    }
    public Dafny.Sequence<char> @helpCompress(Dafny.Sequence<char> @s, char @cur__char, BigInteger @occ, BigInteger @index) {
      if ((@index) >= (new BigInteger((@s).Length))) {
        return (this).@repeatOccurences(@cur__char, @occ);
      } else {
        if (((@s).Select(@index)) == (@cur__char)) {
          return (this).@helpCompress(@s, @cur__char, (@occ) + (new BigInteger(1)), (@index) + (new BigInteger(1)));
        } else {
          return ((this).@repeatOccurences(@cur__char, @occ)).@Concat((this).@helpCompress(@s, (@s).Select(@index), new BigInteger(1), (@index) + (new BigInteger(1))));
        }
      }
    }
    public Dafny.Sequence<char> @compress(Dafny.Sequence<char> @s) {
      return (this).@helpCompress(@s, (@s).Select(new BigInteger(0)), new BigInteger(1), new BigInteger(1));
    }
    public Dafny.Sequence<char> @helpDecompress(Dafny.Sequence<char> @s, bool @fnd__esc, bool @fnd__ch, char @ch, BigInteger @index) {
      if ((@index) >= (new BigInteger((@s).Length))) {
        if (@fnd__esc) {
          if (@fnd__ch) {
            return (Dafny.Sequence<char>.FromElements('\\')).@Concat(Dafny.Sequence<char>.FromElements(@ch));
          } else {
            return Dafny.Sequence<char>.FromElements('\\');
          }
        } else {
          return Dafny.Sequence<char>.FromString("");
        }
      } else {
        if (@fnd__esc) {
          if (@fnd__ch) {
            Dafny.Sequence<char> @_400_integer = @__default.@GetInt(@s, @index);
            if ((new BigInteger((@_400_integer).Length)) > (new BigInteger(0))) {
              BigInteger @_401_occ = @__default.@ParseInt(@_400_integer, (new BigInteger((@_400_integer).Length)) - (new BigInteger(1)));
              if ((@_401_occ) > (new BigInteger(3))) {
                return (@__default.@RepeatChar(@ch, @_401_occ)).@Concat((this).@helpDecompress(@s, false, false, '\0', (@index) + (new BigInteger((@_400_integer).Length))));
              } else {
                return (((Dafny.Sequence<char>.FromElements('\\')).@Concat(Dafny.Sequence<char>.FromElements(@ch))).@Concat(Dafny.Sequence<char>.FromElements((@s).Select(@index)))).@Concat((this).@helpDecompress(@s, false, false, '\0', (@index) + (new BigInteger((@_400_integer).Length))));
              }
            } else {
              return ((Dafny.Sequence<char>.FromElements('\\')).@Concat(Dafny.Sequence<char>.FromElements(@ch))).@Concat((this).@helpDecompress(@s, false, false, '\0', (@index) + (new BigInteger(1))));
            }
          } else {
            if (@__default.@IsAlphaChar((@s).Select(@index))) {
              return (this).@helpDecompress(@s, true, true, (@s).Select(@index), (@index) + (new BigInteger(1)));
            } else {
              return ((Dafny.Sequence<char>.FromElements('\\')).@Concat(Dafny.Sequence<char>.FromElements((@s).Select(@index)))).@Concat((this).@helpDecompress(@s, false, false, '\0', (@index) + (new BigInteger(1))));
            }
          }
        } else {
          if (((@s).Select(@index)) == ('\\')) {
            return (this).@helpDecompress(@s, true, false, '\0', (@index) + (new BigInteger(1)));
          } else {
            return (Dafny.Sequence<char>.FromElements((@s).Select(@index))).@Concat((this).@helpDecompress(@s, false, false, '\0', (@index) + (new BigInteger(1))));
          }
        }
      }
    }
    public Dafny.Sequence<char> @decompress(Dafny.Sequence<char> @s) {
      return (this).@helpDecompress(@s, ((@s).Select(new BigInteger(0))) == ('\\'), false, '\0', new BigInteger(1));
    }
  }

  public partial class @__default {
    public static void @ArrayFromSeq<@A>(Dafny.Sequence<@A> @s, out @A[] @a)
    {
      @a = new @A[0];
    TAIL_CALL_START: ;
      var _nw0 = new @A[(int)(new BigInteger((@s).Length))];
      var _arrayinit0 = Dafny.Helpers.Id<@Func<Dafny.Sequence<@A>,@Func<BigInteger,@A>>>((@_402_s) => (@_403_i) => (@_402_s).Select(@_403_i))(@s);
      for (int _arrayinit_00 = 0; _arrayinit_00 < _nw0.Length; _arrayinit_00++) {
        _nw0[_arrayinit_00] = _arrayinit0(_arrayinit_00);
      }
      @a = _nw0;
    }
    public static void @GetStringFromByteArray(byte[] @b, out Dafny.Sequence<char> @s)
    {
      @s = Dafny.Sequence<char>.Empty;
    TAIL_CALL_START: ;
      if ((@b) == (object) ((byte[])null))
      {
        Dafny.Sequence<char> _rhs0 = Dafny.Sequence<char>.FromString("");
        @s = _rhs0;
        return;
      }
      Dafny.Sequence<char> _rhs1 = Dafny.Sequence<char>.FromString("");
      @s = _rhs1;
      BigInteger @_404_i = BigInteger.Zero;
      BigInteger _rhs2 = new BigInteger(0);
      @_404_i = _rhs2;
      while ((@_404_i) < (new BigInteger((@b).@Length)))
      {
        Dafny.Sequence<char> _rhs3 = (@s).@Concat(Dafny.Sequence<char>.FromElements((char)((@b)[(int)(@_404_i)])));
        @s = _rhs3;
        BigInteger _rhs4 = (@_404_i) + (new BigInteger(1));
        @_404_i = _rhs4;
      }
    }
    public static void @GetByteArrayFromString(Dafny.Sequence<char> @s, out byte[] @b)
    {
      @b = (byte[])null;
    TAIL_CALL_START: ;
      if ((new BigInteger((@s).Length)) == (new BigInteger(0)))
      {
        byte[] _rhs5 = (byte[])null;
        @b = _rhs5;
        return;
      }
      var _nw1 = new byte[(int)(new BigInteger((@s).Length))];
      @b = _nw1;
      BigInteger @_405_i = BigInteger.Zero;
      BigInteger _rhs6 = new BigInteger(0);
      @_405_i = _rhs6;
      while ((@_405_i) < (new BigInteger((@s).Length)))
      {
        var _arr0 = @b;
        var _index0 = @_405_i;
        byte _rhs7 = (byte)((@s).Select(@_405_i));
        _arr0[(int)_index0] = _rhs7;
        BigInteger _rhs8 = (@_405_i) + (new BigInteger(1));
        @_405_i = _rhs8;
      }
    }
    public static void @copy(char[] @src__name, @FileStream @src, @FileStream @dst, bool @isCompression, out bool @success)
    {
      @success = false;
    TAIL_CALL_START: ;
      bool @_406_ok = false;
      int @_407_src__len = 0;
      bool _out0;
      int _out1;
      @FileStream.@FileLength(@src__name, out _out0, out _out1);
      @_406_ok = _out0;
      @_407_src__len = _out1;
      if (!(@_406_ok))
      {
        System.Console.Write(Dafny.Sequence<char>.FromString("Failed to find the length of src file: "));
        System.Console.Write(@src);
        System.Console.Write(Dafny.Sequence<char>.FromString("\n"));
        bool _rhs9 = false;
        @success = _rhs9;
        return;
      }
      byte[] @_408_buffer = (byte[])null;
      var _nw2 = new byte[(int)(@_407_src__len)];
      @_408_buffer = _nw2;
      bool _out2;
      (@src).@Read(0, @_408_buffer, 0, @_407_src__len, out _out2);
      @_406_ok = _out2;
      if (!(@_406_ok))
      {
        System.Console.Write(Dafny.Sequence<char>.FromString("Failed to read the src file: "));
        System.Console.Write(@src);
        System.Console.Write(Dafny.Sequence<char>.FromString("\n"));
        bool _rhs10 = false;
        @success = _rhs10;
        return;
      }
      { }
      @Compression @_409_cmp = default(@Compression);
      var _nw3 = new @Compression();
      @_nw3.@__ctor();
      @_409_cmp = _nw3;
      Dafny.Sequence<char> @_410_buffer__string = Dafny.Sequence<char>.Empty;
      Dafny.Sequence<char> _out3;
      @__default.@GetStringFromByteArray(@_408_buffer, out _out3);
      @_410_buffer__string = _out3;
      Dafny.Sequence<char> @_411_str = Dafny.Sequence<char>.Empty;
      Dafny.Sequence<char> _rhs11 = Dafny.Sequence<char>.FromString("");
      @_411_str = _rhs11;
      if ((new BigInteger((@_410_buffer__string).Length)) > (new BigInteger(0)))
      {
        if (@isCompression)
        {
          Dafny.Sequence<char> _rhs12 = (@_409_cmp).@compress(@_410_buffer__string);
          @_411_str = _rhs12;
        }
        else
        {
          Dafny.Sequence<char> _rhs13 = (@_409_cmp).@decompress(@_410_buffer__string);
          @_411_str = _rhs13;
        }
      }
      byte[] @_412_cmp__buffer = (byte[])null;
      byte[] _out4;
      @__default.@GetByteArrayFromString(@_411_str, out _out4);
      @_412_cmp__buffer = _out4;
      if ((@_412_cmp__buffer) == (object) ((byte[])null))
      {
        System.Console.Write(Dafny.Sequence<char>.FromString("Source file "));
        System.Console.Write(@src);
        System.Console.Write(Dafny.Sequence<char>.FromString(" is empty"));
        System.Console.Write(Dafny.Sequence<char>.FromString("\n"));
        bool _rhs14 = false;
        @success = _rhs14;
        return;
      }
      int @_413_cmp__buff__leng = 0;
      int _rhs15 = (int)(@_412_cmp__buffer).Length;
      @_413_cmp__buff__leng = _rhs15;
      bool _out5;
      (@dst).@Write(0, @_412_cmp__buffer, 0, @_413_cmp__buff__leng, out _out5);
      @_406_ok = _out5;
      if (!(@_406_ok))
      {
        System.Console.Write(Dafny.Sequence<char>.FromString("Failed to write the dst file: "));
        System.Console.Write(@dst);
        System.Console.Write(Dafny.Sequence<char>.FromString("\n"));
        bool _rhs16 = false;
        @success = _rhs16;
        return;
      }
      { }
      bool _out6;
      (@src).@Close(out _out6);
      @_406_ok = _out6;
      if (!(@_406_ok))
      {
        System.Console.Write(Dafny.Sequence<char>.FromString("Failed to close the src file: "));
        System.Console.Write(@src);
        System.Console.Write(Dafny.Sequence<char>.FromString("\n"));
        bool _rhs17 = false;
        @success = _rhs17;
        return;
      }
      bool _out7;
      (@dst).@Close(out _out7);
      @_406_ok = _out7;
      if (!(@_406_ok))
      {
        System.Console.Write(Dafny.Sequence<char>.FromString("Failed to close the dst file: "));
        System.Console.Write(@dst);
        System.Console.Write(Dafny.Sequence<char>.FromString("\n"));
        bool _rhs18 = false;
        @success = _rhs18;
        return;
      }
      bool _rhs19 = true;
      @success = _rhs19;
      return;
    }
    public static void @Main()
    {
    TAIL_CALL_START: ;
      uint @_414_num__args = 0;
      uint _out8;
      @HostConstants.@NumCommandLineArgs(out _out8);
      @_414_num__args = _out8;
      if ((@_414_num__args) != (4U))
      {
        System.Console.Write(Dafny.Sequence<char>.FromString("Expected usage: compression.exe [0|1] [src] [dst]\n"));
        return;
      }
      char[] @_415_compression = (char[])null;
      char[] _out9;
      @HostConstants.@GetCommandLineArg(1UL, out _out9);
      @_415_compression = _out9;
      if ((new BigInteger((@_415_compression).@Length)) != (new BigInteger(1)))
      {
        System.Console.Write(Dafny.Sequence<char>.FromString("The first argument should be 1 for compression or 0 for decompression, but instead got: "));
        System.Console.Write(@_415_compression);
        System.Console.Write(Dafny.Sequence<char>.FromString("\n"));
        return;
      }
      if (!((((@_415_compression)[(int)(new BigInteger(0))]) == ('0')) || (((@_415_compression)[(int)(new BigInteger(0))]) == ('1'))))
      {
        System.Console.Write(Dafny.Sequence<char>.FromString("The first argument should be 1 for compression or 0 for decompression, but instead got: "));
        System.Console.Write(@_415_compression);
        System.Console.Write(Dafny.Sequence<char>.FromString("\n"));
        return;
      }
      bool @_416_isCompression = false;
      bool _rhs20 = (((@_415_compression)[(int)(new BigInteger(0))]) == ('0')) ? (false) : (true);
      @_416_isCompression = _rhs20;
      char[] @_417_src = new char[0];
      char[] _out10;
      @HostConstants.@GetCommandLineArg(2UL, out _out10);
      @_417_src = _out10;
      char[] @_418_dst = new char[0];
      char[] _out11;
      @HostConstants.@GetCommandLineArg(3UL, out _out11);
      @_418_dst = _out11;
      bool @_419_src__exists = false;
      bool _out12;
      @FileStream.@FileExists(@_417_src, out _out12);
      @_419_src__exists = _out12;
      if (!(@_419_src__exists))
      {
        System.Console.Write(Dafny.Sequence<char>.FromString("Couldn't find src file: "));
        System.Console.Write(@_417_src);
        System.Console.Write(Dafny.Sequence<char>.FromString("\n"));
        return;
      }
      bool @_420_dst__exists = false;
      bool _out13;
      @FileStream.@FileExists(@_418_dst, out _out13);
      @_420_dst__exists = _out13;
      if (@_420_dst__exists)
      {
        System.Console.Write(Dafny.Sequence<char>.FromString("The dst file: "));
        System.Console.Write(@_418_dst);
        System.Console.Write(Dafny.Sequence<char>.FromString(" already exists.  I don't dare hurt it.\n"));
        return;
      }
      bool @_421_ok = false;
      @FileStream @_422_src__stream = default(@FileStream);
      bool _out14;
      @FileStream _out15;
      @FileStream.@Open(@_417_src, out _out14, out _out15);
      @_421_ok = _out14;
      @_422_src__stream = _out15;
      if (!(@_421_ok))
      {
        System.Console.Write(Dafny.Sequence<char>.FromString("Failed to open src file: "));
        System.Console.Write(@_417_src);
        System.Console.Write(Dafny.Sequence<char>.FromString("\n"));
        return;
      }
      @FileStream @_423_dst__stream = default(@FileStream);
      bool _out16;
      @FileStream _out17;
      @FileStream.@Open(@_418_dst, out _out16, out _out17);
      @_421_ok = _out16;
      @_423_dst__stream = _out17;
      if (!(@_421_ok))
      {
        System.Console.Write(Dafny.Sequence<char>.FromString("Failed to open dst file: "));
        System.Console.Write(@_418_dst);
        System.Console.Write(Dafny.Sequence<char>.FromString("\n"));
        return;
      }
      bool _out18;
      @__default.@copy(@_417_src, @_422_src__stream, @_423_dst__stream, @_416_isCompression, out _out18);
      @_421_ok = _out18;
      @Compression @_424_c = default(@Compression);
      var _nw4 = new @Compression();
      @_nw4.@__ctor();
      @_424_c = _nw4;
      Dafny.Sequence<char> @_425_s = Dafny.Sequence<char>.Empty;
      Dafny.Sequence<char> _rhs21 = Dafny.Sequence<char>.FromString("AAAABBBBCCCC");
      @_425_s = _rhs21;
      System.Console.Write((@_425_s).@Concat(Dafny.Sequence<char>.FromString("\n")));
      Dafny.Sequence<char> _rhs22 = (@_424_c).@compress(@_425_s);
      @_425_s = _rhs22;
      System.Console.Write((@_425_s).@Concat(Dafny.Sequence<char>.FromString("\n")));
      Dafny.Sequence<char> _rhs23 = (@_424_c).@decompress(@_425_s);
      @_425_s = _rhs23;
      System.Console.Write((@_425_s).@Concat(Dafny.Sequence<char>.FromString("\n")));
    }
    public static BigInteger @NumDigits(BigInteger @n) {
      if ((@n) <= (new BigInteger(9))) {
        return new BigInteger(1);
      } else {
        return (new BigInteger(1)) + (@__default.@NumDigits(Dafny.Helpers.EuclideanDivision(@n, new BigInteger(10))));
      }
    }
    public static Dafny.Sequence<char> @ToString(BigInteger @n) {
      if ((@n) <= (new BigInteger(9))) {
        return Dafny.Sequence<char>.FromElements((char)(((char)(@n)) + ('0')));
      } else {
        return (@__default.@ToString(Dafny.Helpers.EuclideanDivision(@n, new BigInteger(10)))).@Concat(Dafny.Sequence<char>.FromElements((char)(((char)(Dafny.Helpers.EuclideanModulus(@n, new BigInteger(10)))) + ('0'))));
      }
    }
    public static bool @IsInt(char @c) {
      if (((@c) <= ('9')) && ((@c) >= ('0'))) {
        return true;
      } else {
        return false;
      }
    }
    public static bool @IsAlphaChar(char @c) {
      if ((((@c) <= ('Z')) && ((@c) >= ('A'))) || (((@c) <= ('z')) && ((@c) >= ('a')))) {
        return true;
      } else {
        return false;
      }
    }
    public static Dafny.Sequence<char> @GetInt(Dafny.Sequence<char> @s, BigInteger @n) {
      if ((@n) == (new BigInteger((@s).Length))) {
        return Dafny.Sequence<char>.FromString("");
      } else {
        if (@__default.@IsInt((@s).Select(@n))) {
          return (Dafny.Sequence<char>.FromElements((@s).Select(@n))).@Concat(@__default.@GetInt(@s, (@n) + (new BigInteger(1))));
        } else {
          return Dafny.Sequence<char>.FromString("");
        }
      }
    }
    public static BigInteger @ParseInt(Dafny.Sequence<char> @s, BigInteger @i) {
      if ((@i) == (new BigInteger(0))) {
        return (char)(((@s).Select(@i)) - ('0'));
      } else {
        return ((char)(((@s).Select(@i)) - ('0'))) + ((new BigInteger(10)) * (@__default.@ParseInt(@s, (@i) - (new BigInteger(1)))));
      }
    }
    public static Dafny.Sequence<char> @RepeatChar(char @c, BigInteger @occ) {
      if ((@occ) == (new BigInteger(0))) {
        return Dafny.Sequence<char>.FromString("");
      } else {
        return (Dafny.Sequence<char>.FromElements(@c)).@Concat(@__default.@RepeatChar(@c, (@occ) - (new BigInteger(1))));
      }
    }
  }

  public class @byte {
    public static System.Collections.Generic.IEnumerable<byte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (byte)j; }
    }
  }

  public class @uint16 {
    public static System.Collections.Generic.IEnumerable<ushort> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ushort)j; }
    }
  }

  public class @int32 {
    public static System.Collections.Generic.IEnumerable<int> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (int)j; }
    }
  }

  public class @uint32 {
    public static System.Collections.Generic.IEnumerable<uint> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (uint)j; }
    }
  }

  public class @uint64 {
    public static System.Collections.Generic.IEnumerable<ulong> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ulong)j; }
    }
  }

  public class @nat32 {
    public static System.Collections.Generic.IEnumerable<int> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (int)j; }
    }
  }

  public partial class @HostEnvironment {
  }

  public partial class @HostConstants {
  }

  public partial class @OkState {
  }

  public partial class @FileSystemState {
  }

  public partial class @FileStream {
  }
} // end of namespace @__default
