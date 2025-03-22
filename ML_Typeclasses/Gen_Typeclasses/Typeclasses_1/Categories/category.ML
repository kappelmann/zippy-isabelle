(*  Title:  category.ML
    Author: Kevin Kappelmann

Basic typeclasses related to category theory, inspired by the Haskell base package.

See typeclass_base.ML for an explanation of the 'pi type variables.
*)
infix 1 >>>
infix 1 ***
infix 1 &&&

signature \<^eval>\<open>sfx_ParaT_nargs "SEMICATEGORY_BASE"\<close> =
sig
  type (@{ParaT_args} 'a, 'b) cat
  val comp : (@{ParaT_args} 'b, 'c) cat -> (@{ParaT_args} 'a, 'b) cat -> (@{ParaT_args} 'a, 'c) cat
end

signature \<^eval>\<open>sfx_ParaT_nargs "SEMI_CATEGORY"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "SEMICATEGORY_BASE"\<close>
  val >>> : (@{ParaT_args} 'a, 'b) cat * (@{ParaT_args} 'b, 'c) cat -> (@{ParaT_args} 'a, 'c) cat
  val o : (@{ParaT_args} 'b, 'c) cat * (@{ParaT_args} 'a, 'b) cat -> (@{ParaT_args} 'a, 'c) cat
end

functor \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(SC : \<^eval>\<open>sfx_ParaT_nargs "SEMICATEGORY_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "SEMI_CATEGORY"\<close> =
struct

open SC
fun f >>> g = comp g f
fun f o g = comp f g

end

signature \<^eval>\<open>sfx_ParaT_nargs "CATEGORY_BASE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "SEMICATEGORY_BASE"\<close>

  (*unit argument to fight ML's value restriction*)
  val id : unit -> (@{ParaT_args} 'a, 'a) cat
end

signature \<^eval>\<open>sfx_ParaT_nargs "CATEGORY"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "CATEGORY_BASE"\<close>
  val repeatn : int -> (@{ParaT_args} 'a, 'a) cat -> (@{ParaT_args} 'a, 'a) cat
end

functor \<^eval>\<open>sfx_ParaT_nargs "Category"\<close>(C : \<^eval>\<open>sfx_ParaT_nargs "CATEGORY_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "CATEGORY"\<close> =
struct
open C
fun repeatn n f = if n <= 0 then id () else comp (repeatn (n - 1) f) f
end

signature \<^eval>\<open>sfx_ParaT_nargs "ARROW_BASE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "CATEGORY_BASE"\<close>
  val arr : ('a -> 'b) -> (@{ParaT_args} 'a, 'b) cat
  val *** : (@{ParaT_args} 'a, 'b) cat * (@{ParaT_args} 'c, 'd) cat ->
    (@{ParaT_args} ('a * 'c), ('b * 'd)) cat
end

signature \<^eval>\<open>sfx_ParaT_nargs "ARROW"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "ARROW_BASE"\<close>

  val first : (@{ParaT_args} 'a, 'b) cat -> (@{ParaT_args} ('a * 'c), ('b * 'c)) cat
  val second : (@{ParaT_args} 'a, 'b) cat -> (@{ParaT_args} ('c * 'a), ('c * 'b)) cat

  val &&& : (@{ParaT_args} 'a, 'b) cat * (@{ParaT_args} 'a, 'c) cat -> (@{ParaT_args} 'a, ('b * 'c)) cat

  val K : 'a -> (@{ParaT_args} 'b, 'a) cat
  val curry : (@{ParaT_args} ('a * 'b), 'c) cat -> 'a -> (@{ParaT_args} 'b, 'c) cat
end

functor \<^eval>\<open>sfx_ParaT_nargs "Arrow"\<close>(A : \<^eval>\<open>sfx_ParaT_nargs "ARROW_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "ARROW"\<close> =
struct

open A
fun first f = f *** id ()
fun second f = id () *** f

fun f &&& g = comp (f *** g) (arr (fn b => (b, b)))

fun K x = arr (fn _ => x)
fun curry f i = comp f (K i &&& id ())

end

signature \<^eval>\<open>sfx_ParaT_nargs "ARROW_APPLY_BASE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "ARROW_BASE"\<close>
  val app : (@{ParaT_args} (@{ParaT_args} 'a, 'b) cat * 'a, 'b) cat
end

signature \<^eval>\<open>sfx_ParaT_nargs "ARROW_APPLY"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "ARROW_APPLY_BASE"\<close>
  val uncurry : ('a -> (@{ParaT_args} 'b, 'c) cat) -> (@{ParaT_args} ('a * 'b), 'c) cat
  val app' : 'a -> (@{ParaT_args} (@{ParaT_args} 'a, 'b) cat, 'b) cat
end

functor \<^eval>\<open>sfx_ParaT_nargs "Arrow_Apply"\<close>(A : \<^eval>\<open>sfx_ParaT_nargs "ARROW_APPLY_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "ARROW_APPLY"\<close> =
struct

open A
local structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(A) open SC
in
fun uncurry f = arr (apfst f) >>> app
fun app' x = arr (rpair x) >>> app
end

end

signature \<^eval>\<open>sfx_ParaT_nargs "ARROW_ARROW_APPLY"\<close> =
sig
  structure A : \<^eval>\<open>sfx_ParaT_nargs "ARROW"\<close>
  structure AA : \<^eval>\<open>sfx_ParaT_nargs "ARROW_APPLY"\<close>
  where type (@{ParaT_args} 'a, 'b) cat = (@{ParaT_args} 'a, 'b) A.cat
end

signature \<^eval>\<open>sfx_ParaT_nargs "ARROW_ZERO_BASE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "ARROW_BASE"\<close>
  val zero : unit -> (@{ParaT_args} 'a, 'b) cat
end

signature \<^eval>\<open>sfx_ParaT_nargs "ARROW_PLUS_BASE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "ARROW_ZERO_BASE"\<close>
  val plus : (@{ParaT_args} 'a, 'b) cat -> (@{ParaT_args} 'a, 'b) cat -> (@{ParaT_args} 'a, 'b) cat
end

signature \<^eval>\<open>sfx_ParaT_nargs "ARROW_OR_BASE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "ARROW_ZERO_BASE"\<close>
  val or : (@{ParaT_args} 'a, 'b) cat -> (@{ParaT_args} 'a, 'b) cat -> (@{ParaT_args} 'a, 'b) cat
end

signature \<^eval>\<open>sfx_ParaT_nargs "ARROW_EXCEPTION_BASE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "ARROW_BASE"\<close>
  type @{ParaT_args encl = "(" ")"} exn

  val throw : (@{ParaT_args} @{ParaT_args encl = "(" ")"} exn, 'a) cat
  val catch : (@{ParaT_args} 'a, 'b) cat ->
    (@{ParaT_args} 'a * @{ParaT_args encl = "(" ")"} exn, 'b) cat -> (@{ParaT_args} 'a, 'b) cat
end

signature \<^eval>\<open>sfx_ParaT_nargs "ARROW_EXCEPTION"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "ARROW_EXCEPTION_BASE"\<close>

  val throw' : @{ParaT_args encl = "(" ")"} exn -> (@{ParaT_args} 'a, 'b) cat
  val catch' : (@{ParaT_args} 'a, 'b) cat -> (@{ParaT_args} 'a, 'b) cat -> (@{ParaT_args} 'a, 'b) cat
  val try : (@{ParaT_args} 'a, 'a) cat -> (@{ParaT_args} 'a, 'a) cat
end

functor \<^eval>\<open>sfx_ParaT_nargs "Arrow_Exception"\<close>(
    A : \<^eval>\<open>sfx_ParaT_nargs "ARROW_EXCEPTION_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "ARROW_EXCEPTION"\<close> =
struct

open A

fun throw' x = comp throw (arr (K x))
fun catch' f g = catch f (comp g (arr fst))
fun try f = catch' f (id ())

end

signature \<^eval>\<open>sfx_ParaT_nargs "ARROW_CHOICE_BASE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "ARROW_BASE"\<close>
  val cases : (@{ParaT_args} 'a, 'c) cat -> (@{ParaT_args} 'b, 'd) cat ->
    (@{ParaT_args} ('a, 'b) Either.either, ('c, 'd) Either.either) cat
  val merge : (@{ParaT_args} 'a, 'c) cat -> (@{ParaT_args} 'b, 'c) cat ->
    (@{ParaT_args} ('a, 'b) Either.either, 'c) cat
end

signature \<^eval>\<open>sfx_ParaT_nargs "ARROW_CHOICE"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "ARROW_CHOICE_BASE"\<close>
  val opt : (@{ParaT_args} unit, 'b) cat -> (@{ParaT_args} 'a, 'b) cat -> (@{ParaT_args} 'a option, 'b) cat
end

functor \<^eval>\<open>sfx_ParaT_nargs "Arrow_Choice"\<close>(
    A : \<^eval>\<open>sfx_ParaT_nargs "ARROW_CHOICE_BASE"\<close>
  ) : \<^eval>\<open>sfx_ParaT_nargs "ARROW_CHOICE"\<close> =
struct
open A
fun opt fnone fsome = comp (merge fnone fsome) (arr Either.of_opt)
end
