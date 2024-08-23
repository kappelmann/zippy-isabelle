(*  Title:      HOCLP/pair_zipper.ML
    Author:     Kevin Kappelmann
*)
signature PAIR_ZIPPER =
sig
  structure Z1 : ZIPPER
  structure Z2 : ZIPPER
  sharing type Z1.C.cat = Z2.C.cat

  include ZIPPER
  where type ('i, 'a) content = ('i, 'a) Z1.content * ('i, 'a) Z2.content
  where type ('i, 'a) zcontext = ('i, 'a) Z1.zcontext * ('i, 'a) Z2.zcontext
  where type ('i, 'a) zipper = ('i, 'a) Z1.zipper * ('i, 'a) Z2.zipper
  where type ('i, 'a) container = ('i, 'a) Z1.container * ('i, 'a) Z2.container
end

functor Pair_Bi_Zipper_Pair_Zipper(type ('i, 'a, 'b) content; structure Z : PAIR_ZIPPER)
  : PAIR_BI_ZIPPER =
struct
structure Base = struct type ('i, 'a, 'b) content = ('i, 'a, 'b) content end
structure Z1 = Bi_Zipper_Zipper(open Base; structure Z = Z.Z1)
structure Z2 = Bi_Zipper_Zipper(open Base; structure Z = Z.Z2)
structure Z = Bi_Zipper_Zipper(open Base; structure Z = Z)
open Z
end

functor Pair_Zipper_Pair_Bi_Zipper(Z : PAIR_BI_ZIPPER) : PAIR_ZIPPER =
struct
structure Z1 = Zipper_Bi_Zipper(Z.Z1)
structure Z2 = Zipper_Bi_Zipper(Z.Z2)
structure Z = Zipper_Bi_Zipper(Z)
open Z
end

functor Pair_Zipper(
  structure A : IARROW_BASE
  structure Z1 : ZIPPER
  sharing type Z1.C.cat = A.cat
  structure Z2 : ZIPPER
  sharing type Z2.C.cat = Z1.C.cat
) = Pair_Zipper_Pair_Bi_Zipper(Pair_Bi_Zipper(
  structure A = A
  structure Base = struct type ('i, 'a, 'b) content = 'a end
  structure Z1 = Bi_Zipper_Zipper(open Base; structure Z = Z1)
  structure Z2 = Bi_Zipper_Zipper(open Base; structure Z = Z2)
))
