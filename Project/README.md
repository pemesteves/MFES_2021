# Verified Compression Algorithm

Implementation of a Run-Length Encoding Algorithm in Dafny.

## Compile & Run

Run docker:

`docker run -v path_to_folder:/home/local -it dafny`

Change the directory to the home/local directory (directory where you have the Dafny files)

`cd home/local`

Compile the project:

`dafny compression.dfy Io.dfy IoNative.cs`

Open a terminal outside docker and run the executable:

`./compression.exe 0 src_file dest_file`

or

`./compression.exe 1 src_file dest_file`

## Test

I have included a test file: test.txt.

You can test de program by running: `./compression.exe 1 test.txt new_file.txt`

If you run the the executable with 0 and the new file, the result should be equal to the original file:

`./compression.exe 0 new_file.txt original_file.txt`