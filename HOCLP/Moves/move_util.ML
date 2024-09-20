(*  Title:      HOCLP/move_util.ML
    Author:     Kevin Kappelmann
*)
signature MOVE_UTIL =
sig
  include MOVE_BASE
  structure AE : IARROW_EXCEPTION
  where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) T.cat
  structure AC : IARROW_CHOICE
  where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) T.cat
  structure SC : ISEMI_CATEGORY
  where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) T.cat
  structure AF : IARROW_FOLD
  where type ('i, 'j, 'a, 'b) AE.cat = ('i, 'j, 'a, 'b) T.cat
end

functor Move_Util(
    structure AE : IARROW_EXCEPTION
    structure AC : IARROW_CHOICE_BASE
    sharing type AC.cat = AE.cat
  ) : MOVE_UTIL =
struct

structure MB = Move_Base(Lazy_ICategory_Base(AE))
open MB
structure AE = AE
structure AC = IArrow_Choice(AC)
structure SC = ISemi_Category(AE)
structure AF = IArrow_Fold(structure AE = AE; structure AC = AC)

end
