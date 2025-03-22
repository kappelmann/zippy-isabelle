(*  Title:      HOCLP/zipper_moves_list_enumerable..ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>sfx_T_nargs "Zipper_Moves_List_Enumerable"\<close>(
    structure L : \<^eval>\<open>sfx_ParaT_nargs "GLIST"\<close>
    structure E : \<^eval>\<open>sfx_T_nargs "ENUMERABLE"\<close>
    sharing type E.M.t = L.M.t
    val init_data : (@{ParaT_args} @{AllT_args} E.data L.t, @{AllT_args} E.init_data) E.move
  ) :
    \<^eval>\<open>sfx_T_nargs "ZIPPER_MOVES"\<close>
    where type @{AllT_args} container = @{AllT_args} E.init_data
    where type @{AllT_args} zipper = @{AllT_args} E.data L.t
    where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) E.M.t
  =
\<^eval>\<open>sfx_T_nargs "Zipper_Moves"\<close>(
  structure M = E
  type @{AllT_args} container = @{AllT_args} E.init_data
  type @{AllT_args} zipper = @{AllT_args} E.data L.t

  local structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(E)
    structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow"\<close>(E.M) open SC A
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