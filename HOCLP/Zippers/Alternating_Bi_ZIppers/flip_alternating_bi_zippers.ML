(*  Title:      HOCLP/flip_alternating_bi_zippers.ML
    Author:     Kevin Kappelmann
*)
functor Flip_Alternating_Bi_Zippers(AZ : ALTERNATING_BI_ZIPPERS) :
    ALTERNATING_BI_ZIPPERS
    where type ('i, 'a, 'b) Z1.content = ('i, 'a, 'b) AZ.Z2.content
    where type ('i, 'a, 'b) Z1.zcontext = ('i, 'a, 'b) AZ.Z2.zcontext
    where type ('i, 'a, 'b) Z1.zipper = ('i, 'a, 'b) AZ.Z2.zipper
    where type ('i, 'a, 'b) Z1.container = ('i, 'a, 'b) AZ.Z2.container
    where type ('i, 'j, 'a, 'b) Z1.T.cat = ('i, 'j, 'a, 'b) AZ.Z2.T.cat
    where type ('i, 'a, 'b) Z2.content = ('i, 'a, 'b) AZ.Z1.content
    where type ('i, 'a, 'b) Z2.zcontext = ('i, 'a, 'b) AZ.Z1.zcontext
    where type ('i, 'a, 'b) Z2.zipper = ('i, 'a, 'b) AZ.Z1.zipper
    where type ('i, 'a, 'b) Z2.container = ('i, 'a, 'b) AZ.Z1.container
    where type ('i, 'j, 'a, 'b) Z2.T.cat = ('i, 'j, 'a, 'b) AZ.Z1.T.cat
    where type ('i, 'j, 'a, 'b) Up1.T.cat = ('i, 'j, 'a, 'b) AZ.Up2.T.cat
    where type ('i, 'j, 'a, 'b) Up2.T.cat = ('i, 'j, 'a, 'b) AZ.Up1.T.cat
  =
struct
structure Z1 = AZ.Z2
structure Z2 = AZ.Z1
structure Down1 = AZ.Down2
structure Down2 = AZ.Down1
structure Up1 = AZ.Up2
structure Up2 = AZ.Up1
end
