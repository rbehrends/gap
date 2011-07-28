#############################################################################
##
#W  glzmodmz.gd                    GAP library                    Stefan Kohl
#W                                                           Alexander Hulpke
##
#H  @(#)$Id: glzmodmz.gd,v 1.4 2011/06/21 16:52:49 gap Exp $
##
#Y  Copyright (C) 2011 The GAP Group
##
##  This file contains declarations for constructing clasical groups over
##  residue class rings.
Revision.glzmodmz_gd :=
    "@(#)$Id: glzmodmz.gd,v 1.4 2011/06/21 16:52:49 gap Exp $";

#############################################################################
##
#F  SizeOfGLdZmodmZ( d, m ) . . . . . . . . . .  Size of the group GL(d,Z/mZ) 
##
##  Computes the order of the group `GL( <d>, Integers mod <m> )' for
##  positive integers <d> and <m> > 1.
##
DeclareGlobalFunction( "SizeOfGLdZmodmZ" );

#############################################################################
##
#F  ConstructFormPreservingGroup(oper [,sign] d, R )
##
##  constructs the classical group sefined by <A>oper</A> over a prime field
##  over the residue class ring <A>R</A>, which must be modulo an odd prime
##  power.
DeclareGlobalFunction("ConstructFormPreservingGroup");

#############################################################################
##
#E  glzmodmz.gd . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
