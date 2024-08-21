(*  Title:      HOCLP/flip_alternating_bi_zippers.ML
    Author:     Kevin Kappelmann
*)
functor Flip_Alternating_Bi_Zippers(AZ : ALTERNATING_BI_ZIPPERS) :
    ALTERNATING_BI_ZIPPERS
    where type ('i, 'a, 'b) Z1.content = ('i, 'a, 'b) AZ.Z2.content
    where type ('i, 'a, 'b) Z1.zcontext = ('i, 'a, 'b) AZ.Z2.zcontext
    where type ('i, 'a, 'b) Z1.zipper = ('i, 'a, 'b) AZ.Z2.zipper
    where type ('i, 'a, 'b) Z1.container = ('i, 'a, 'b) AZ.Z2.container
    where type ('i, 'j, 'a) Z1.K.M.t = ('i, 'j, 'a) AZ.Z2.K.M.t
    where type ('i, 'a, 'b) Z2.content = ('i, 'a, 'b) AZ.Z1.content
    where type ('i, 'a, 'b) Z2.zcontext = ('i, 'a, 'b) AZ.Z1.zcontext
    where type ('i, 'a, 'b) Z2.zipper = ('i, 'a, 'b) AZ.Z1.zipper
    where type ('i, 'a, 'b) Z2.container = ('i, 'a, 'b) AZ.Z1.container
    where type ('i, 'j, 'a) Z2.K.M.t = ('i, 'j, 'a) AZ.Z1.K.M.t
    where type ('i, 'j, 'a) Up1.K.M.t = ('i, 'j, 'a) AZ.Up2.K.M.t
    where type ('i, 'j, 'a) Up2.K.M.t = ('i, 'j, 'a) AZ.Up1.K.M.t
  =
struct
structure Z1 = AZ.Z2
structure Z2 = AZ.Z1
structure Down1 = AZ.Down2
structure Down2 = AZ.Down1
structure Up1 = AZ.Up2
structure Up2 = AZ.Up1
end
