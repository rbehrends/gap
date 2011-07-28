#############################################################################
##
#W  basicfp.gi                 GAP Library                   Alexander Hulpke
##
#Y  Copyright (C)  2009,  The GAP group
##
##  This file contains the methods for the construction of the basic fp group
##  types.
##
Revision.basicfp_gi :=
    "@(#)$Id: basicfp.gi,v 1.4 2011/06/17 16:29:44 gap Exp $";


    
#############################################################################
##
#M  AbelianGroupCons( <IsFpGroup and IsFinite>, <ints> )
##
InstallMethod( AbelianGroupCons, "fp group", true,
    [ IsFpGroup and IsFinite, IsList ], 0,
function( filter, ints )
local   f,g,i,j,rels,gfam,fam;

  if Length(ints)=0 or not ForAll( ints, IsInt )  then
      Error( "<ints> must be a list of integers" );
  fi;

  f   := FreeGroup(IsSyllableWordsFamily, Length(ints));
  g   := GeneratorsOfGroup(f);
  rels:=[];
  for i in [1..Length(ints)] do
    for j in [1..i-1] do
      Add(rels,Comm(g[i],g[j]));
    od;
    if ints[i]<>0 then
      Add(rels,g[i]^ints[i]);
    fi;
  od;

  g:=f/rels;

  if ForAll(ints,IsPosInt) then
    SetSize( g, Product(ints) );
  fi;

  fam:=FamilyObj(One(f));
  gfam:=FamilyObj(One(g));
  gfam!.redorders:=ints;
  SetFpElementNFFunction(gfam,function(x)
    local u,e,i,j,n;
    u:=UnderlyingElement(x);
    e:=ExtRepOfObj(u); # syllable form

    # bring in correct order and reduction
    n:=ListWithIdenticalEntries(Length(gfam!.redorders),0);
    for i in [1,3..Length(e)-1] do
      j:=e[i];
      if gfam!.redorders[j]<infinity then
	n[j]:=n[j]+e[i+1] mod gfam!.redorders[j];
      else
	n[j]:=n[j]+e[i+1];
      fi;
    od;

    e:=[];
    for i in [1..Length(gfam!.redorders)] do
      if n[i]>0 then
	Add(e,i);
	Add(e,n[i]);
      fi;
    od;

    return ObjByExtRep(fam,e);
  end);

  SetReducedMultiplication(g);
  SetIsAbelian( g, true );

  return g;
end );

#############################################################################
##
#M  CyclicGroupCons( <IsFpGroup>, <n> )
##
InstallOtherMethod( CyclicGroupCons, "fp group", true,
    [ IsFpGroup,IsObject ], 0,
function( filter, n )
local f,g,fam,gfam;
  if n=infinity then
    return FreeGroup("a");
  elif not IsPosInt(n) then
    TryNextMethod();
  fi;
  f:=FreeGroup( IsSyllableWordsFamily, "a" );
  g:=f/[f.1^n];
  SetSize(g,n);
  fam:=FamilyObj(One(f));
  gfam:=FamilyObj(One(g));
  SetFpElementNFFunction(gfam,function(x)
    local u,e;
    u:=UnderlyingElement(x);
    e:=ExtRepOfObj(u); # syllable form
    if e[2]>=0 and e[2]<n then
      return u;
    elif e[2] mod n=0 then
      return One(f);
    else
      e:=[e[1],e[2] mod n];
      return ObjByExtRep(fam,e);
    fi;
  end);

  SetReducedMultiplication(g);
  return g;
end );


#############################################################################
##
#M  DihedralGroupCons( <IsFpGroup and IsFinite>, <n> )
##
InstallMethod( DihedralGroupCons,
    "fp group",
    true,
    [ IsFpGroup and IsFinite,
      IsInt and IsPosRat ],
    0,

function( filter, n )
local f,rels,g;

  if n mod 2 = 1  then
      TryNextMethod();
  elif n = 2 then return
      CyclicGroup( IsFpGroup, 2 );
  fi;
  f   := FreeGroup( IsSyllableWordsFamily, "r", "s" );
  rels:= [f.1^(n/2),f.2^2,f.1^f.2*f.1];
  g   := f/rels;
  SetReducedMultiplication(g);
  SetSize(g,n);
  return g;

end );

#############################################################################
##
#M  QuaternionGroupCons( <IsFpGroup and IsFinite>, <n> )
##
InstallMethod( QuaternionGroupCons,
    "fp group",
    true,
    [ IsFpGroup and IsFinite,
      IsInt and IsPosRat ],
    0,
function( filter, n )
local f,rels,g;
  if 0 <> n mod 4  then
      TryNextMethod();
  elif n = 4 then return
      CyclicGroup( IsFpGroup, 4 );
  fi;
  f   := FreeGroup( IsSyllableWordsFamily, "r", "s" );
  rels:= [ f.1^2/f.2^(n/4), f.2^(n/2), f.2^f.1*f.2 ];
  g   := f/rels;
  SetSize(g,n);
  if n <= 10^4 then SetReducedMultiplication(g); fi;
  return g;
end );

#############################################################################
##
#M  ElementaryAbelianGroupCons( <IsFpGroup and IsFinite>, <n> )
##
InstallMethod( ElementaryAbelianGroupCons,
    "fp group",
    true,
    [ IsFpGroup and IsFinite,
      IsInt and IsPosRat ],
    0,

function( filter, n )
    if n = 1  then
        return CyclicGroupCons( IsFpGroup, 1 );
    elif not IsPrimePowerInt(n)  then
        Error( "<n> must be a prime power" );
    fi;
    n:= AbelianGroupCons( IsFpGroup, Factors(n) );
    SetIsElementaryAbelian( n, true );
    return n;
end );

