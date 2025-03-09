(*  Title:      HOCLP/zipper_moves_list_enumerable..ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Zipper" ^ "_Moves_List_Enumerable"\<close>(
    structure L : GLIST
    structure E : \<^eval>\<open>T_Args.suffix_Poly_nargs "ENUMERABLE"\<close>
    sharing type E.M.t = L.M.t
    val init_data : (@{ParaT_args}, @{T_args} E.data L.t, @{T_args} E.init_data) E.move
  ) :
    \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_MOVES"\<close>
    where type @{T_args} container = @{T_args} E.init_data
    where type @{T_args} zipper = @{T_args} E.data L.t
    where type ('p1, 'a) M.t = ('p1, 'a) E.M.t
  =
\<^eval>\<open>T_Args.suffix_Poly_nargs "Zipper" ^ "_Moves"\<close>(
  structure M = E
  type @{T_args} container = @{T_args} E.init_data
  type @{T_args} zipper = @{T_args} E.data L.t

  local structure SC = Semi_Category(E); structure A = Kleisli_Arrow(E.M) open SC A
  in
  fun zip x = x |> (E.First.move >>> arr (fn x => L.cons x L.empty))
  val unzip = init_data

  fun horizontal_move pos_move x = x |> (L.dest >>> first pos_move >>> arr (uncurry L.cons))

  fun right x = x |> horizontal_move E.Next.move
  fun left x = x |> horizontal_move E.Prev.move
  fun down x = x |> ((init_data >>> E.First.move) &&& id ()
    >>> arr (uncurry L.cons))
  fun up x = x |> (L.dest >>> arr snd)
  end
)