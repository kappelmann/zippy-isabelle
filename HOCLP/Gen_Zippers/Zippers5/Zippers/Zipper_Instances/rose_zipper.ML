(*  Title:      HOCLP/rose_zipper.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>T_Args.suffix_Poly_nargs "ROSE_ZIPPER"\<close> =
sig
  structure LI : GLIST
  type 'a rose
  val dest_rose : 'a rose -> ('a * 'a rose) LI.t
  val rose : ('a * 'a rose) LI.t -> 'a rose
  val cons : 'a * 'a rose -> 'a rose -> 'a rose
  include \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER"\<close>
  where type @{T_args} ZO.content = @{PolyT_arg 0}
  where type @{T_args} ZO.zcontext = @{PolyT_arg 0} rose *
    (((@{PolyT_arg 0} * @{PolyT_arg 0} rose) LI.t *
    (@{PolyT_arg 0} * @{PolyT_arg 0} rose) LI.t * @{PolyT_arg 0} option) LI.t)
  where type @{T_args} ZM.container = @{PolyT_arg 0} rose
  val cons_sibling_zcontext : @{PolyT_arg 0} * @{PolyT_arg 0} rose -> @{T_args} ZO.zcontext ->
    @{T_args} ZO.zcontext
  val cons_child_zcontext : @{PolyT_arg 0} * @{PolyT_arg 0} rose -> @{T_args} ZO.zcontext ->
    @{T_args} ZO.zcontext
end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Rose_Zipper"\<close>(
    structure A : KLEISLI_ARROW
    structure L : LENS
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) A.cat
    structure LI : GLIST
    where type 'a t = 'a list
    where type 'p1 M.exn = unit
    sharing type LI.M.t = A.K.M.t
  ) : \<^eval>\<open>T_Args.suffix_Poly_nargs "ROSE_ZIPPER"\<close> =
struct

structure LI = LI

datatype 'a rose = Rose of ('a * 'a rose) LI.t
fun dest_rose (Rose xs) = xs
fun rose xs = Rose xs
fun cons x (Rose xs) = Rose (LI.cons x xs)

structure ZO = \<^eval>\<open>T_Args.suffix_Poly_nargs "Zipper" ^ "_Optics_Zipper_Data"\<close>(
struct
  structure ZD = Zipper_Data
  structure A = A
  structure L = L
  type @{T_args} content = @{PolyT_arg 0}
  type @{T_args} zcontext = @{PolyT_arg 0} rose *
    (((@{PolyT_arg 0} * @{PolyT_arg 0} rose) LI.t *
    (@{PolyT_arg 0} * @{PolyT_arg 0} rose) LI.t * @{PolyT_arg 0} option) LI.t)
end
)

structure ZM = \<^eval>\<open>T_Args.suffix_Poly_nargs "Zipper" ^ "_Moves"\<close>(
  structure M = Move_Base(A.K.M)
  structure AC = Kleisli_Arrow_Choice(M.M)
  structure SC = Semi_Category(A) open SC A ZO
  type @{T_args} container = @{PolyT_arg 0} rose
  fun zip x = x |> (arr dest_rose
    >>> LI.dest
    >>> arr (fn ((x, cs), xs) => pair x (cs, [([], xs, NONE)]))
    >>> zipper)
  fun unzip x = x |> (
    let
      fun mk [(rev_pref, suff, _)] children v = Rose (rev rev_pref @ [(v, children)] @ suff)
        | mk ((rev_pref, suff, SOME c) :: xs) children v =
            mk xs (Rose (rev rev_pref @ [(v, children)] @ suff)) c
    in
      get_content &&& get_zcontext
      >>> arr (fn (c, (children, xs)) => mk xs children c)
    end)
  fun dest_zipper x = x |> (get_content &&& get_zcontext
    >>> arr (fn (c, (ch, xs)) => (ch, (c, xs))))
  fun dest_zipper_flip x = x |> (dest_zipper >>> arr (fn (ch, (c, xs)) => (xs, (c, ch))))
  fun up x = x |> (dest_zipper_flip
    >>> first LI.dest
    >>> arr (fn (((rev_pref, suff, p), xs), (c, ch)) =>
      Option.map (rpair (rose (rev rev_pref @ [(c, ch)] @ suff), xs)) p)
    >>> AC.opt LI.M.throw zipper)
  fun down x = x |> (dest_zipper
    >>> first (arr dest_rose >>> LI.dest)
    >>> arr (fn (((c, ch), cs), (p, xs)) => pair c (ch, (LI.cons (LI.empty, cs, SOME p) xs)))
    >>> zipper)
  fun left x = x |> (dest_zipper_flip
    >>> first LI.dest
    >>> first (arr (fn ((rev_pref, suff, p), xs) => (rev_pref, (suff, p, xs))))
    >>> first (first LI.dest)
    >>> arr (fn ((((r, rch), rs), (suff, p, xs)), (c, ch)) =>
      pair r (rch, LI.cons (rs, LI.cons (c, ch) suff , p) xs))
    >>> zipper)
  fun right x = x |> (dest_zipper_flip
    >>> first LI.dest
    >>> first (arr (fn ((rev_pref, suff, p), xs) => (suff, (rev_pref, p, xs))))
    >>> first (first LI.dest)
    >>> arr (fn ((((s, sch), ss), (rev_pref, p, xs)), (c, ch)) =>
      pair s (sch, LI.cons (LI.cons (c, ch) rev_pref, ss, p) xs))
    >>> zipper)
)

structure Z = \<^eval>\<open>T_Args.suffix_Poly_nargs "Zipper"\<close>(
  structure ZO = ZO; structure ZM = ZM)
open Z

fun cons_sibling_zcontext c =
  apsnd (fn ((rev_pref, suff, p) :: xs) => (rev_pref @ [c], suff, p) :: xs)
fun cons_child_zcontext c = apfst (cons c)

end
