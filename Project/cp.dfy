/*  
 * Copy Utility.
 *
 * Rui Maranhao -- rui@computer.org
 */

include "Io.dfy"

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
	        if !(|args| >= 3 && args[1] in old_files && args[2] !in old(env.files.state())) then
						env == old(env) && env.ok == old(env.ok) && env.ok.ok() == old(env.ok.ok())
					&& env.files == old(env.files) && env.files.state() == old_files 
					else
						env.ok != null && 
						(env.ok.ok() && |args| >= 3 && args[1] in old_files && args[2] !in old(env.files.state()) 
						==> env.files != null &&
            env.files.state() == old_files[args[2] := old_files[args[1]]]);          
{
  var num_args := HostConstants.NumCommandLineArgs(env);
  if num_args < 3 {
    print "Expected usage: cp.exe [src] [dst]\n";
    return;
  }

  var src := HostConstants.GetCommandLineArg(1, env);
  var dst := HostConstants.GetCommandLineArg(2, env);

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
