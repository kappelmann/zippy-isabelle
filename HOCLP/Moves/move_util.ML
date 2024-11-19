(*  Title:      HOCLP/move_util.ML
    Author:     Kevin Kappelmann
*)
signature MOVE_UTIL =
sig
  include MOVE_BASE
  structure C : CATEGORY
  sharing type C.cat = cat
  structure A : ARROW
  sharing type A.cat = cat
  structure AA : ARROW_APPLY
  sharing type A.cat = cat
  structure AE : ARROW_EXCEPTION_REC
  sharing type AE.cat = cat
  structure AC : ARROW_CHOICE
  sharing type AC.cat = cat
  structure SC : SEMI_CATEGORY
  sharing type SC.cat = cat
  structure L : LAZY_COMP
  sharing type L.cat = C.cat
  structure AF : ARROW_FOLD
  sharing type AF.cat = cat
end

functor Move_Util(
    structure C : CATEGORY
    structure A : ARROW
    sharing type A.cat = C.cat
    structure AA : ARROW_APPLY
    sharing type AA.cat = C.cat
    structure AE : ARROW_EXCEPTION_REC
    sharing type AE.cat = C.cat
    structure AC : ARROW_CHOICE
    sharing type AC.cat = C.cat
    structure L : LAZY_COMP
    sharing type L.cat = C.cat
  ) : MOVE_UTIL =
struct

structure MB = Move_Base(A)
open MB
structure C = C
structure A = A
structure AA = AA
structure AE = AE
structure AC = AC
structure SC = Semi_Category(C)
structure L = L
structure AF = Arrow_Fold_Exception_Choice(structure A = A; structure AE = AE; structure AC = AC;
  structure L = L)

end
