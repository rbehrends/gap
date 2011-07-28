#############################################################################
##
#W  process.gd                  GAP Library                      Frank Celler
##
#Y  Copyright (C)  1996,  Lehrstuhl D für Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St Andrews, Scotland
#Y  Copyright (C) 2002 The GAP Group
##
##  This file contains the operations for process.
##
Revision.process_gd :=
    "@(#)$Id: process.gd,v 4.25 2011/06/15 16:48:48 gap Exp $";


#############################################################################
##  <#GAPDoc Label="[1]{process}">
##  &GAP; can call other programs, such programs are called <E>processes</E>.
##  There are two kinds of processes:
##  first there are processes that are started, run and return a result,
##  while &GAP; is suspended until the process terminates.
##  Then there are processes that will run in parallel to &GAP; as
##  subprocesses and &GAP; can communicate and control the processes using
##  streams (see&nbsp;<Ref Func="InputOutputLocalProcess"/>).
##  <#/GAPDoc>
##


#############################################################################
##
#O  Process( <dir>, <prg>, <stream-in>, <stream-out>, <options> )
##
##  <#GAPDoc Label="Process">
##  <ManSection>
##  <Oper Name="Process" Arg='dir, prg, stream-in, stream-out, options'/>
##
##  <Description>
##  <Ref Oper="Process"/> runs a new process and returns when the process terminates.
##  It returns the return value of the process if the operating system
##  supports such a concept.
##  <P/>
##  The first argument <A>dir</A> is a directory object (see&nbsp;<Ref Sect="Directories"/>)
##  which will be the current directory (in the usual UNIX or MSDOS sense)
##  when the program is run.
##  This will only matter if the program accesses files (including running
##  other programs) via relative path names.
##  In particular, it has nothing to do with finding the binary to run.
##  <P/>
##  In general the directory will either be the current directory, which is
##  returned by <Ref Func="DirectoryCurrent"/>
##  &ndash;this was the behaviour of &GAP;&nbsp;3&ndash;
##  or a temporary directory returned by <Ref Func="DirectoryTemporary"/>.
##  If one expects that the process creates temporary or log files the latter
##  should be used because &GAP; will attempt to remove these directories
##  together with all the files in them when quitting.
##  <P/>
##  If a program of a &GAP; package which does not only consist of &GAP;
##  code needs to be launched in a directory relative to certain data
##  libraries, then the first entry of <Ref Func="DirectoriesPackageLibrary"/> 
##  should be used.
##  The argument of <Ref Func="DirectoriesPackageLibrary"/> should be the path to the
##  data library relative to the package directory.
##  <P/>
##  If a program calls other programs and needs to be launched in a directory
##  containing the executables for such a &GAP; package then the first entry
##  of <Ref Func="DirectoriesPackagePrograms"/> should be used.
##  <P/>
##  The latter two alternatives should only be used if absolutely necessary
##  because otherwise one risks accumulating log or core files in the package
##  directory.
##  <P/>
##  <Log><![CDATA[
##  gap> path := DirectoriesSystemPrograms();;
##  gap> ls := Filename( path, "ls" );;
##  gap> stdin := InputTextUser();;
##  gap> stdout := OutputTextUser();;
##  gap> Process( path[1], ls, stdin, stdout, ["-c"] );;
##  awk    ls     mkdir
##  gap> # current directory, here the root directory
##  gap> Process( DirectoryCurrent(), ls, stdin, stdout, ["-c"] );;
##  bin    lib    trans  tst    CVS    grp    prim   thr    two
##  src    dev    etc    tbl    doc    pkg    small  tom
##  gap> # create a temporary directory
##  gap> tmpdir := DirectoryTemporary();;
##  gap> Process( tmpdir, ls, stdin, stdout, ["-c"] );;
##  gap> PrintTo( Filename( tmpdir, "emil" ) );
##  gap> Process( tmpdir, ls, stdin, stdout, ["-c"] );;
##  emil
##  ]]></Log>
##  <P/>
##  <A>prg</A> is the filename of the program to launch,
##  for portability it should be the result of
##  <Ref Func="Filename" Label="for a directory and a string"/>
##  and should pass <Ref Func="IsExecutableFile"/>.
##  Note that <Ref Func="Process"/> does <E>no</E> searching through a list
##  of directories, this is done by
##  <Ref Func="Filename" Label="for a directory and a string"/>.
##  <P/>
##  <A>stream-in</A> is the input stream that delivers the characters to the
##  process.
##  For portability it should either be <Ref Func="InputTextNone"/> 
##  (if the process reads no characters), <Ref Func="InputTextUser"/>, 
##  the result of a call to <Ref Oper="InputTextFile"/>
##  from which no characters have been read, or the result of a call to
##  <Ref Oper="InputTextString"/>.
##  <P/>
##  <Ref Func="Process"/> is free to consume <E>all</E> the input even if the program itself
##  does not require any input at all.
##  <P/>
##  <A>stream-out</A> is the output stream which receives the characters from the
##  process.
##  For portability it should either be <Ref Func="OutputTextNone"/> (if the process
##  writes no characters), <Ref Func="OutputTextUser"/>, the result of a call to
##  <Ref Oper="OutputTextFile"/> to which no characters have been written, or the result
##  of a call to <Ref Oper="OutputTextString"/>.
##  <P/>
##  <A>options</A> is a list of strings which are passed to the process as command
##  line argument.
##  Note that no substitutions are performed on the strings,
##  i.e., they are passed immediately to the process and are not processed by
##  a command interpreter (shell).
##  Further note that each string is passed as one argument,
##  even if it contains <E>space</E> characters.
##  Note that input/output redirection commands are <E>not</E> allowed as
##  <A>options</A>.
##  <P/>
##  In order to find a system program use <Ref Func="DirectoriesSystemPrograms"/>
##  together with <Ref Oper="Filename" Label="for a directory and a string"/>.
##  <P/>
##  <Example><![CDATA[
##  gap> path := DirectoriesSystemPrograms();;
##  gap> date := Filename( path, "date" );
##  "/bin/date"
##  ]]></Example>
##  <P/>
##  The next example shows how to execute <C>date</C> with no argument and no input, 
##  and collect the output into a string stream.
##  <P/>
##  <Log><![CDATA[
##  gap> str := "";; a := OutputTextString(str,true);;
##  gap> Process( DirectoryCurrent(), date, InputTextNone(), a, [] );
##  0
##  gap> CloseStream(a);
##  gap> Print(str);
##  Fri Jul 11 09:04:23 MET DST 1997
##  ]]></Log>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
UNBIND_GLOBAL( "Process" );
DeclareOperation( "Process",
    [ IsDirectory, IsString, IsInputStream, IsOutputStream, IsList ] );

#############################################################################
##
#F  TmpNameAllArchs( )
##
##  returns a temporary file name based on the output of a call to TmpName
##  but with adjusted temporary directory path for Window architectures
##
DeclareGlobalFunction("TmpNameAllArchs");

#############################################################################
##
#F ShortFileNameWindows(<name>)
##
##  returns a short file name (http://en.wikipedia.org/wiki/8.3_filename)
##  for use under Windows. Paths can contain either / or \ separators,
##  either will be permitted.
DeclareGlobalFunction("ShortFileNameWindows");

#############################################################################
##
#F  Exec( <cmd>, <option1>, ..., <optionN> )  . . . . . . . execute a command
##
##  <#GAPDoc Label="Exec">
##  <ManSection>
##  <Func Name="Exec" Arg='cmd, option1, ..., optionN'/>
##
##  <Description>
##  <Ref Func="Exec"/> runs a shell in the current directory to execute the command given
##  by the string <A>cmd</A> with options <A>option1</A>, ..., <A>optionN</A>.
##  <P/>
##  <Log><![CDATA[
##  gap> Exec( "date" );
##  Thu Jul 24 10:04:13 BST 1997
##  ]]></Log>
##  <P/>
##  <A>cmd</A> is interpreted by the shell and therefore we can make use of the
##  various features that a shell offers as in following example.
##  <P/>
##  <Log><![CDATA[
##  gap> Exec( "echo \"GAP is great!\" > foo" );
##  gap> Exec( "cat foo" );
##  GAP is great!
##  gap> Exec( "rm foo" );
##  ]]></Log>
##  <P/>
##  <Ref Func="Exec"/> calls the more general operation <Ref Oper="Process"/>.
##  The function <Ref Func="Edit"/> should be used to call an editor from 
##  within &GAP;.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
DeclareGlobalFunction( "Exec" );

#############################################################################
##
#F  Restart([<cmd>])
##
##  <#GAPDoc Label="Restart">
##  <ManSection>
##  <Func Name="Restart" Arg='[cmd]'/>
##
##  <Description>
##  The function <Ref Func="Restart"/> starts &GAP; again from scratch (as if
##  the &GAP; process was terminated and a new &GAP; process was started).
##  All variables are lost.
##  <P/>
##  If given,
##  the string <A>cmd</A> is appended to the command line and will give
##  further options.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
DeclareGlobalFunction("Restart");

#############################################################################
##
#F  LoadWorkspace(<ws>)
##
##  <#GAPDoc Label="LoadWorkspace">
##  <ManSection>
##  <Func Name="LoadWorkspace" Arg='ws'/>
##
##  <Description>
##  The function <Ref Func="LoadWorkspace"/> loads the existing workspace
##  <A>ws</A> into the present &GAP; process.
##  The behaviour is the same as if terminating the current &GAP; session
##  and restarting a new session with the loaded workspace.
##  In particularly, all previously defined variables are lost.
##  <P/>
##  <Log><![CDATA[
##  gap> LoadWorkspace("savefile");
##  ... Loading workspace ...
##  GAP4, Version: 4.number of day, i686-pc-linux-gnu-gcc
##   [...]
##  gap> a;
##  1
##  ]]></Log>
##  <P/>
##  <Index>loading a saved workspace</Index>
##  <C>-L <A>filename</A></C>
##  <P/>
##  A saved workspace can be loaded by starting &GAP; with the option
##  <C>-L</C> (see&nbsp;<Ref Sect="Command Line Options"/>).
##  This will start &GAP; and load the workspace.
##  <P/>
##  <Log><![CDATA[
##  you@unix> gap -L savefile
##  gap> a;
##  1
##  ]]></Log>
##  <P/>
##  Please note that paths to workspaces have to be given in full,
##  expansion of the tilde to denote a home directory will <E>not</E> work.
##  <P/>
##  Under UNIX, it is possible to compress savefiles using <C>gzip</C>.
##  Compression typically reduces the size of a workspace by a factor 3 or 4.
##  <P/>
##  These workspaces then can be loaded into &GAP; as if they were
##  uncompressed (omit the <C>.gz</C> ending). &GAP; will try to locate
##  <C>gzip</C> on the system and uncompress the file
##  automatically while reading it.
##  <Log><![CDATA[
##  you@unix> gzip -9 savefile
##  you@unix> gap -L savefile
##  gap> a;
##  1
##  ]]></Log>
##  <P/>
##  We cannot guarantee that saved workspaces are portable between different
##  system architectures or over different versions of &GAP; or its library.
##  <P/>
##  If compiled modules had been loaded into &GAP; before the workspace
##  was saved, they will be loaded into the new &GAP; session during the
##  workspace loading process. If they are not available then the load
##  will fail. Additional compiled modules will <E>not</E> be used, even if
##  they are available, although they may be loaded later using
##  <Ref Func="Reread"/>.
##  <Ref Func="SaveWorkspace"/> may sometimes produce warning messages, as in
##  <P/>
##  <Log><![CDATA[
##  gap> SaveWorkspace("b5");
##  #W bad bag id 4 found, 0 saved
##  #W bad bag id 20 found, 0 saved
##  true
##  ]]></Log>
##  <P/>
##  A small number of such messages can probably be ignored (they arise
##  because the garbage collector may not always collect all dead objects,
##  and dead objects may contain data that <Ref Func="SaveWorkspace"/> does
##  not know how to process).
##  <P/>
##  &GAP; packages which had been loaded before the workspace was saved
##  are loaded also when the workspace is loaded.
##  Packages which had been available but not loaded before the workspace
##  was saved are available also when the workspace is loaded,
##  provided these packages have not been upgraded.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
DeclareGlobalFunction("LoadWorkspace");


#############################################################################
##
#E

