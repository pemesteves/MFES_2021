/*
 *
 * Rui Maranhao -- rui@computer.org
 */

include "Io.dfy"

// Useful to convert Dafny strings into arrays of characters.
method ArrayFromSeq<A>(s: seq<A>) returns (a: array<A>)
  ensures a[..] == s
{
  a := new A[|s|] ( i requires 0 <= i < |s| => s[i] );
}

method {:main} Main(ghost env: HostEnvironment?)
  requires env != null && env.Valid() && env.ok.ok();
  modifies env.ok
  modifies env.files
{
    //var constants := env.constants;
    /*var numArgs : uint32 := HostConstants.NumCommandLineArgs(env);

    print numArgs;*/

    /*var fname := ArrayFromSeq("foo.txt");
    var f: FileStream;
    var ok: bool;
    ok, f := FileStream.Open(fname, env);

    // Try commenting out the following line to see that you are forced to handle errors!
    if !ok { print "open failed\n"; return; }

    // This is "hello world!" in ascii.
    // The library requires the data to be an array of bytes, but Dafny has no char->byte conversions :(
    var data: array<byte> := ArrayFromSeq([104, 101, 108, 108, 111, 32, 119, 111, 114, 108, 100, 33, 10]);

    ok := f.Write(0, data, 0, data.Length as int32);
*/
   /* if numArgs != 4 {
      print "Usage: ./compression [0|1] sourceFile destFile\n";
      return;
    }*/
    /*
    var i := 0;
    while (i < numArgs) 
      decreases numArgs - i
      invariant 0 <= numArgs as int <= |env.constants.CommandLineArgs()|
    {
      var args := HostConstants.GetCommandLineArg(numArgs, env);

    }*/

    //var cmdArgs := env.constants.CommandLineArgs();
  

    print "done!\n";
}
