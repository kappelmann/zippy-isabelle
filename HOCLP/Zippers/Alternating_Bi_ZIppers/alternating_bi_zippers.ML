(*  Title:      HOCLP/alternating_bi_zippers.ML
    Author:     Kevin Kappelmann
*)
signature ALTERNATING_BI_ZIPPERS =
sig
  structure Z1 : BI_ZIPPER
  structure Z2 : BI_ZIPPER

  structure Down1 : BI_MOVE
  where type ('i, 'a, 'b) from = ('i, 'a, 'b) Z1.zipper
  where type ('i, 'a, 'b) to = ('i, 'b, 'a) Z2.zipper
  sharing type Down1.T.cat = Z2.Init.T.cat

  structure Down2 : BI_MOVE
  where type ('i, 'a, 'b) from = ('i, 'a, 'b) Z2.zipper
  where type ('i, 'a, 'b) to = ('i, 'b, 'a) Z1.zipper
  sharing type Down2.T.cat = Z1.Init.T.cat

  structure Up1 : BI_MOVE
  where type ('i, 'a, 'b) from = ('i, 'a, 'b) Z1.zipper
  where type ('i, 'a, 'b) to = ('i, 'b, 'a) Z2.zipper

  structure Up2 : BI_MOVE
  where type ('i, 'a, 'b) from = ('i, 'a, 'b) Z2.zipper
  where type ('i, 'a, 'b) to = ('i, 'b, 'a) Z1.zipper
end
