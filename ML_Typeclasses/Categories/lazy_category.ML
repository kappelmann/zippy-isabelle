(*  Title:  lazy_category.ML
    Author: Kevin Kappelmann

Lazy categories.
*)
signature TLAZY_CAT =
sig
  type ('p1, 'a, 'b) cat
  type ('p1, 'a, 'b) lcat = unit -> ('p1, 'a, 'b) cat
end

signature LAZY_CAT_UTIL =
sig
  val lift : 'a -> unit -> 'a
  val unlift : (unit -> 'a) -> 'a
  val lift1 : ('a -> 'b) -> (unit -> 'a) -> 'b
  val unlift1 : ((unit -> 'a) -> 'b) -> 'a -> 'b
  val lift2 : ('a -> 'b -> 'c) -> (unit -> 'a) -> (unit -> 'b) -> 'c
  val unlift2 : ((unit -> 'a) -> (unit -> 'b) -> 'c) -> 'a -> 'b -> 'c
  val lift3 : ('a -> 'b -> 'c -> 'd) -> (unit -> 'a) -> (unit -> 'b) -> (unit -> 'c) -> 'd
  val unlift3 : ((unit -> 'a) -> (unit -> 'b) -> (unit -> 'c) -> 'd) -> 'a -> 'b -> 'c -> 'd
  val lift4 : ('a -> 'b -> 'c -> 'd -> 'e) -> (unit -> 'a) -> (unit -> 'b) -> (unit -> 'c) ->
    (unit -> 'd) -> 'e
  val unlift4 : ((unit -> 'a) -> (unit -> 'b) -> (unit -> 'c) -> (unit -> 'd) -> 'e) ->
    'a -> 'b -> 'c -> 'd -> 'e
end

structure Lazy_Cat_Util : LAZY_CAT_UTIL =
struct
fun lift x _ = x
fun unlift x = x ()
fun lift1 f x = f (x ())
fun unlift1 f x = f (K x)
fun lift2 f x y = f (x ()) (y ())
fun unlift2 f x y = f (K x) (K y)
fun lift3 f x y z = f (x ()) (y ()) (z ())
fun unlift3 f x y z = f (K x) (K y) (K z)
fun lift4 f x y z w = f (x ()) (y ()) (z ()) (w ())
fun unlift4 f x y z w = f (K x) (K y) (K z) (K w)
end

functor TLazy_Cat(type ('p1, 'a, 'b) cat) : TLAZY_CAT =
struct
type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) cat
type ('p1, 'a, 'b) lcat = unit -> ('p1, 'a, 'b) cat
end

signature LAZY_SEMI_CATEGORY_BASE =
sig
  structure T : TLAZY_CAT
  include SEMI_CATEGORY_BASE
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) T.lcat
end

functor Lazy_Semi_Category_Base(SC : SEMI_CATEGORY_BASE) : LAZY_SEMI_CATEGORY_BASE =
struct
structure T = TLazy_Cat(type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) SC.cat)
type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) T.lcat
fun comp f g _ = Lazy_Cat_Util.lift2 SC.comp f g
end

signature LAZY_LAZY_COMP =
sig
  structure T : TLAZY_CAT
  include LAZY_COMP
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) T.lcat
end

functor Lazy_Lazy_Comp(L : LAZY_COMP) : LAZY_LAZY_COMP =
struct
structure SC = Lazy_Semi_Category_Base(L)
open SC
fun comp_lazy f g _ = Lazy_Cat_Util.lift2 L.comp_lazy f g
end

signature LAZY_CATEGORY_BASE =
sig
  structure T : TLAZY_CAT
  include CATEGORY_BASE
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) T.lcat
end

functor Lazy_Category_Base(C : CATEGORY_BASE) : LAZY_CATEGORY_BASE =
struct
structure SC = Lazy_Semi_Category_Base(C)
open SC
fun id _ = C.id
end

signature LAZY_CATEGORY =
sig
  structure T : TLAZY_CAT
  include CATEGORY
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) T.lcat
end

functor Lazy_Category(C : CATEGORY) : LAZY_CATEGORY =
struct
structure LC = Lazy_Category_Base(C)
open LC
fun repeatn n f _ = Lazy_Cat_Util.lift1 (C.repeatn n) f
end

signature LAZY_ARROW_BASE =
sig
  structure T : TLAZY_CAT
  include ARROW_BASE
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) T.lcat
end

functor Lazy_Arrow_Base(A : ARROW_BASE) : LAZY_ARROW_BASE =
struct
structure C = Lazy_Category_Base(A)
open C
fun arr f _ = A.arr f
fun (f *** g) _ = Lazy_Cat_Util.lift2 (curry A.***) f g
end

signature LAZY_ARROW =
sig
  structure T : TLAZY_CAT
  include ARROW
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) T.lcat
end

functor Lazy_Arrow(A : ARROW) : LAZY_ARROW =
struct
structure AB = Lazy_Arrow_Base(A)
open AB
fun first f _ = Lazy_Cat_Util.lift1 A.first f
fun second f _ = Lazy_Cat_Util.lift1 A.second f
fun (f &&& g) _ = Lazy_Cat_Util.lift2 (curry A.&&&) f g
fun K x _ = A.K x
fun curry f x _ = Lazy_Cat_Util.lift1 A.curry f x
end

signature LAZY_ARROW_APPLY_BASE =
sig
  structure T : TLAZY_CAT
  include ARROW_APPLY_BASE
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) T.lcat
end

functor Lazy_Arrow_Apply_Base(AA : ARROW_APPLY_BASE) : LAZY_ARROW_APPLY_BASE =
struct
structure A = Lazy_Arrow_Base(AA)
open A
fun app _ =  AA.comp AA.app (AA.*** (AA.arr (fn f => f ()), AA.id ()))
end

signature LAZY_ARROW_APPLY =
sig
  structure T : TLAZY_CAT
  include ARROW_APPLY
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) T.lcat
end

functor Lazy_Arrow_Apply(AA : ARROW_APPLY) : LAZY_ARROW_APPLY =
struct
structure A = Lazy_Arrow_Apply_Base(AA)
open A
fun uncurry f _ =  AA.uncurry (fn x => f x ())
fun app' x _ = AA.comp (AA.app' x) (AA.arr Lazy_Cat_Util.unlift)
end

signature LAZY_ARROW_ZERO_BASE =
sig
  structure T : TLAZY_CAT
  include ARROW_ZERO_BASE
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) T.lcat
end

functor Lazy_Arrow_Zero_Base(AZ : ARROW_ZERO_BASE) : LAZY_ARROW_ZERO_BASE =
struct
structure A = Lazy_Arrow_Base(AZ)
open A
fun zero _ = AZ.zero
end

signature LAZY_ARROW_PLUS_BASE =
sig
  structure T : TLAZY_CAT
  include ARROW_PLUS_BASE
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) T.lcat
end

functor Lazy_Arrow_Plus_Base(AP : ARROW_PLUS_BASE) : LAZY_ARROW_PLUS_BASE =
struct
structure A = Lazy_Arrow_Zero_Base(AP)
open A
fun plus f g _ = Lazy_Cat_Util.lift2 AP.plus f g
end

signature LAZY_ARROW_OR_BASE =
sig
  structure T : TLAZY_CAT
  include ARROW_OR_BASE
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) T.lcat
end

functor Lazy_Arrow_Or_Base(AO : ARROW_OR_BASE) : LAZY_ARROW_OR_BASE =
struct
structure A = Lazy_Arrow_Zero_Base(AO)
open A
fun or f g _ = Lazy_Cat_Util.lift2 AO.or f g
end

signature LAZY_ARROW_EXCEPTION_BASE =
sig
  structure T : TLAZY_CAT
  include ARROW_EXCEPTION_BASE
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) T.lcat
end

functor Lazy_Arrow_Exception_Base(AE : ARROW_EXCEPTION_BASE) : LAZY_ARROW_EXCEPTION_BASE =
struct
structure A = Lazy_Arrow_Base(AE)
open A
type exn = AE.exn
fun throw _ = AE.throw
fun catch f fe _= Lazy_Cat_Util.lift2 AE.catch f fe
end

signature LAZY_ARROW_EXCEPTION =
sig
  structure T : TLAZY_CAT
  include ARROW_EXCEPTION
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) T.lcat
end

functor Lazy_Arrow_Exception(AE : ARROW_EXCEPTION) : LAZY_ARROW_EXCEPTION =
struct
structure A = Lazy_Arrow_Exception_Base(AE)
open A
fun throw' e = Lazy_Cat_Util.lift (AE.throw' e)
fun catch' f fe _ = Lazy_Cat_Util.lift2 AE.catch' f fe
fun try f _ = Lazy_Cat_Util.lift1 AE.try f
end

signature LAZY_ARROW_EXCEPTION_REC =
sig
  structure T : TLAZY_CAT
  include ARROW_EXCEPTION_REC
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) T.lcat
end

functor Lazy_Arrow_Exception_Rec(AE : ARROW_EXCEPTION_REC) : LAZY_ARROW_EXCEPTION_REC =
struct
structure A = Lazy_Arrow_Exception(AE)
open A
fun repeat f _ = Lazy_Cat_Util.lift1 AE.repeat f
fun try_step f fe _ = Lazy_Cat_Util.lift2 AE.try_step f fe
end

signature LAZY_ARROW_CHOICE_BASE =
sig
  structure T : TLAZY_CAT
  include ARROW_CHOICE_BASE
  where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) T.lcat
end

functor Lazy_Arrow_Choice_Base(AC : ARROW_CHOICE_BASE) : LAZY_ARROW_CHOICE_BASE =
struct
structure A = Lazy_Arrow_Base(AC)
open A
fun cases f g _ = Lazy_Cat_Util.lift2 AC.cases f g
fun merge f g _ = Lazy_Cat_Util.lift2 AC.merge f g
end
