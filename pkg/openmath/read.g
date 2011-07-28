#############################################################################
##
#W    read.g              OpenMath Package             Andrew Solomon
#W                                                     Marco Costantini
##
#H    @(#)$Id: read.g,v 1.36 2010/09/22 11:03:47 alexk Exp $
##
#Y    Copyright (C) 1999, 2000, 2001, 2006
#Y    School Math and Comp. Sci., University of St.  Andrews, Scotland
#Y    Copyright (C) 2004, 2005, 2006 Marco Costantini
##
##    read.g file
##

Revision.("openmath/read.g") :=
    "@(#)$Id: read.g,v 1.36 2010/09/22 11:03:47 alexk Exp $";

## the *.gd and *.g files are read by init.g


#################################################################
## Module 1.2.b
## This module converts the OpenMath XML into a tree and parses it;
## requires the function OMsymLookup (and the function 
## ParseTreeXMLString from package GapDoc) and provides 
## the function OMgetObjectXMLTree

if IsBound( ParseTreeXMLString )  then
    ReadPackage("openmath", "/gap/xmltree.gi");
else
    MakeReadWriteGlobal( "OMgetObjectXMLTree" );
    OMgetObjectXMLTree := ReturnFail;
fi;


#############################################################################
## Module 2: conversion from Gap to OpenMath
## (Modules 1 and 2 are independent)


#################################################################
## Module 2.1
## This module is concerned with outputting OpenMath; provides
## OMPutObject and OMPrint

ReadPackage("openmath", "/gap/omputxml.gi");
ReadPackage("openmath", "/gap/omputbin.gi");
ReadPackage("openmath", "/gap/omput.gi");
if IsExistingFile( Concatenation( GAPInfo.PackagesInfo.("openmath")[1].InstallationPath,"/private/private.gi") ) then
	Read( Concatenation( GAPInfo.PackagesInfo.("openmath")[1].InstallationPath,"/private/private.gi") );
fi;

#################################################################
## Module 1.2.a
## This module reads token/values off the stream and builds GAP objects;
## uses the external binary gpipe, 
## requires the function OMsymLookup and provides OMpipeObject
## Directories bin, include, OMCv1.3c, src belongs to this module.

ReadPackage("openmath", "/gap/lex.g");
ReadPackage("openmath", "/gap/parse.gi");

#############################################################################
#E
