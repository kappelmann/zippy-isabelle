(*  Title:  lazy_icategory.ML
    Author: Kevin Kappelmann

Lazy indexed categories.
*)
signature TLAZY_ICAT =
sig
type ('i, 'o, 'a, 'b) cat
type ('i, 'o, 'a, 'b) lcat = unit -> ('i, 'o, 'a, 'b) cat
end

functor TLazy_ICat(type ('i, 'o, 'a, 'b) cat) : TLAZY_ICAT =
struct
type ('i, 'o, 'a, 'b) cat = ('i, 'o, 'a, 'b) cat
type ('i, 'o, 'a, 'b) lcat = unit -> ('i, 'o, 'a, 'b) cat
end

signature LAZY_ISEMI_CATEGORY_BASE =
sig
  structure T : TLAZY_ICAT
  include ISEMI_CATEGORY_BASE
  where type ('i, 'o, 'a, 'b) cat = ('i, 'o, 'a, 'b) T.lcat
end

functor Lazy_ISemi_Category_Base(SC : ISEMI_CATEGORY_BASE) : LAZY_ISEMI_CATEGORY_BASE =
struct
structure T = TLazy_ICat(type ('i, 'o, 'a, 'b) cat = ('i, 'o, 'a, 'b) SC.cat)
type ('i, 'o, 'a, 'b) cat = ('i, 'o, 'a, 'b) T.lcat
fun comp f g _ = Lazy_Cat_Util.lift2 SC.comp f g
fun comp_lazy f g _ = Lazy_Cat_Util.lift2 SC.comp_lazy f g
end

signature LAZY_ICATEGORY_BASE =
sig
  structure T : TLAZY_ICAT
  include ICATEGORY_BASE
  where type ('i, 'o, 'a, 'b) cat = ('i, 'o, 'a, 'b) T.lcat
end

functor Lazy_ICategory_Base(C : ICATEGORY_BASE) : LAZY_ICATEGORY_BASE =
struct
structure SC = Lazy_ISemi_Category_Base(C)
open SC
fun id _ = C.id
end

signature LAZY_IARROW_BASE =
sig
  structure T : TLAZY_ICAT
  include IARROW_BASE
  where type ('i, 'o, 'a, 'b) cat = ('i, 'o, 'a, 'b) T.lcat
end

functor Lazy_IArrow_Base(A : IARROW_BASE) : LAZY_IARROW_BASE =
struct
structure C = Lazy_ICategory_Base(A)
open C
fun arr f _ = A.arr f
fun (f *** g) _ = Lazy_Cat_Util.lift2 (curry A.***) f g
end

signature LAZY_IARROW =
sig
  structure T : TLAZY_ICAT
  include IARROW
  where type ('i, 'o, 'a, 'b) cat = ('i, 'o, 'a, 'b) T.lcat
end

functor Lazy_IArrow(A : IARROW) : LAZY_IARROW =
struct
structure AB = Lazy_IArrow_Base(A)
open AB
fun first f _ = Lazy_Cat_Util.lift1 A.first f
fun second f _ = Lazy_Cat_Util.lift1 A.second f
fun (f &&& g) _ = Lazy_Cat_Util.lift2 (curry A.&&&) f g
fun K x _ = A.K x
fun curry f x _ = Lazy_Cat_Util.lift1 A.curry f x
end

signature LAZY_IARROW_APPLY_BASE =
sig
  structure T : TLAZY_ICAT
  include IARROW_APPLY_BASE
  where type ('i, 'o, 'a, 'b) cat = ('i, 'o, 'a, 'b) T.lcat
end

functor Lazy_IArrow_Apply_Base(AA : IARROW_APPLY_BASE) : LAZY_IARROW_APPLY_BASE =
struct
structure A = Lazy_IArrow_Base(AA)
open A
fun app _ =  AA.comp AA.app (AA.*** (AA.arr (fn f => f ()), AA.id ()))
end

signature LAZY_IARROW_APPLY_BASE =
sig
  structure T : TLAZY_ICAT
  include IARROW_APPLY_BASE
  where type ('i, 'o, 'a, 'b) cat = ('i, 'o, 'a, 'b) T.lcat
end

functor Lazy_IArrow_Apply_Base(AA : IARROW_APPLY_BASE) : LAZY_IARROW_APPLY_BASE =
struct
structure A = Lazy_IArrow_Base(AA)
open A
fun app _ =  AA.comp AA.app (AA.*** (AA.arr (fn f => f ()), AA.id ()))
end

signature LAZY_IARROW_ZERO_BASE =
sig
  structure T : TLAZY_ICAT
  include IARROW_ZERO_BASE
  where type ('i, 'o, 'a, 'b) cat = ('i, 'o, 'a, 'b) T.lcat
end

functor Lazy_IArrow_Zero_Base(AZ : IARROW_ZERO_BASE) : LAZY_IARROW_ZERO_BASE =
struct
structure A = Lazy_IArrow_Base(AZ)
open A
fun zero _ = AZ.zero
end

signature LAZY_IARROW_PLUS_BASE =
sig
  structure T : TLAZY_ICAT
  include IARROW_PLUS_BASE
  where type ('i, 'o, 'a, 'b) cat = ('i, 'o, 'a, 'b) T.lcat
end

functor Lazy_IArrow_Plus_Base(AP : IARROW_PLUS_BASE) : LAZY_IARROW_PLUS_BASE =
struct
structure A = Lazy_IArrow_Zero_Base(AP)
open A
fun plus f g _ = Lazy_Cat_Util.lift2 AP.plus f g
end

signature LAZY_IARROW_OR_BASE =
sig
  structure T : TLAZY_ICAT
  include IARROW_OR_BASE
  where type ('i, 'o, 'a, 'b) cat = ('i, 'o, 'a, 'b) T.lcat
end

functor Lazy_IArrow_Or_Base(AO : IARROW_OR_BASE) : LAZY_IARROW_OR_BASE =
struct
structure A = Lazy_IArrow_Zero_Base(AO)
open A
fun or f g _ = Lazy_Cat_Util.lift2 AO.or f g
end

signature LAZY_IARROW_EXCEPTION_BASE =
sig
  structure T : TLAZY_ICAT
  include IARROW_EXCEPTION_BASE
  where type ('i, 'o, 'a, 'b) cat = ('i, 'o, 'a, 'b) T.lcat
end

functor Lazy_IArrow_Exception_Base(AE : IARROW_EXCEPTION_BASE) : LAZY_IARROW_EXCEPTION_BASE =
struct
structure A = Lazy_IArrow_Base(AE)
open A
type exn = AE.exn
fun throw _ = AE.throw
fun catch f fe _= Lazy_Cat_Util.lift2 AE.catch f fe
end

signature LAZY_IARROW_EXCEPTION =
sig
  structure T : TLAZY_ICAT
  include IARROW_EXCEPTION
  where type ('i, 'o, 'a, 'b) cat = ('i, 'o, 'a, 'b) T.lcat
end

functor Lazy_IArrow_Exception(AE : IARROW_EXCEPTION) : LAZY_IARROW_EXCEPTION =
struct
structure A = Lazy_IArrow_Exception_Base(AE)
open A
fun catch' f fe _= Lazy_Cat_Util.lift2 AE.catch' f fe
fun try f _= Lazy_Cat_Util.lift1 AE.try f
fun repeat f _= Lazy_Cat_Util.lift1 AE.repeat f
end

signature LAZY_IARROW_CHOICE_BASE =
sig
  structure T : TLAZY_ICAT
  include IARROW_CHOICE_BASE
  where type ('i, 'o, 'a, 'b) cat = ('i, 'o, 'a, 'b) T.lcat
end

functor Lazy_IArrow_Choice_Base(AC : IARROW_CHOICE_BASE) : LAZY_IARROW_CHOICE_BASE =
struct
structure A = Lazy_IArrow_Base(AC)
open A
fun cases f g _ = Lazy_Cat_Util.lift2 AC.cases f g
fun merge f g _ = Lazy_Cat_Util.lift2 AC.merge f g
end

signature LAZY_IARROW_CHOICE =
sig
  structure T : TLAZY_ICAT
  include IARROW_CHOICE
  where type ('i, 'o, 'a, 'b) cat = ('i, 'o, 'a, 'b) T.lcat
end

functor Lazy_IArrow_Choice(AC : IARROW_CHOICE) : LAZY_IARROW_CHOICE =
struct
structure A = Lazy_IArrow_Choice_Base(AC)
open A
fun opt f g _ = Lazy_Cat_Util.lift2 AC.opt f g
end
