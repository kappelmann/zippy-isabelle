(*  Title:      HOCLP/pair_zipper.ML
    Author:     Kevin Kappelmann
*)
signature PAIR_ZIPPER =
sig
  structure Z1 : ZIPPER
  structure Z2 : ZIPPER
  sharing type Z1.cat = Z2.cat

  include ZIPPER
  where type ('i, 'a) content = ('i, 'a) Z1.content * ('i, 'a) Z2.content
  where type ('i, 'a) zcontext = ('i, 'a) Z1.zcontext * ('i, 'a) Z2.zcontext
  where type ('i, 'a) zipper = ('i, 'a) Z1.zipper * ('i, 'a) Z2.zipper
  where type ('i, 'a) container = ('i, 'a) Z1.container * ('i, 'a) Z2.container
end

functor Pair_QZipper_Pair_Zipper(type ('i, 'a, 'b, 'c, 'd) content; structure Z : PAIR_ZIPPER)
  : PAIR_QZIPPER =
struct
structure Base = struct type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) content end
structure Z1 = QZipper_Zipper(open Base; structure Z = Z.Z1)
structure Z2 = QZipper_Zipper(open Base; structure Z = Z.Z2)
structure Z = QZipper_Zipper(open Base; structure Z = Z)
open Z
end

functor Pair_Zipper_Pair_QZipper(Z : PAIR_QZIPPER) : PAIR_ZIPPER =
struct
structure Z1 = Zipper_QZipper(Z.Z1)
structure Z2 = Zipper_QZipper(Z.Z2)
structure Z = Zipper_QZipper(Z)
open Z
end

functor Pair_Zipper(
  structure A : LAZY_IARROW_BASE
  structure Z1 : ZIPPER
  where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) A.T.lcat
  structure Z2 : ZIPPER
  where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) Z1.cat
) = Pair_Zipper_Pair_QZipper(Pair_QZipper(
  structure A = A
  structure Base = struct type ('i, 'a, 'b, 'c, 'd) content = 'a end
  structure Z1 = QZipper_Zipper(open Base; structure Z = Z1)
  structure Z2 = QZipper_Zipper(open Base; structure Z = Z2)
))
