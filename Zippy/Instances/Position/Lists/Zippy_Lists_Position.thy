\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Zippy_Lists_Position
  imports
    Zippy_Lists_Base
    Zippy_Position
    Zippy_Actions
begin

ML_file\<open>zippy_lists_position_mixin_base.ML\<close>

ML\<open>
  structure M = \<^eval>\<open>sfx_ParaT_nargs "Monad_Exception_Monad_Or"\<close>(
    \<^eval>\<open>sfx_ParaT_nargs "Option_Monad_Or_Trans"\<close>(
    \<^eval>\<open>sfx_ParaT_nargs "Identity_Monad"\<close>))
  structure MEU = Zippy_Monad_Exception_Util(M)
  structure Z = Zippy_Lists_Base(M)
  structure Z = Zippy_Lists_Position_Mixin_Base(Z)
  structure ZN = Zippy_Node(structure Z = Z; structure AE = MEU.AE)

  structure PACTION =
  struct
    structure Base = Zippy_PAction_Mixin_Base(
      structure L = ZN.NODE_CO4
      type prio = int)
    open Base
    structure PACTION = Zippy_PAction_Mixin(
    structure PACTION = Base
    structure AE = MEU.AE)
    open PACTION Base
  end
\<close>

ML\<open>
  val pact = PACTION.no_paction ()
  val n1 = Z.ZCORE.N4.node (PACTION.DATAM.data_more () pact, NONE) |> the
  val n2 = Z.ZCORE.N4.node (PACTION.DATAM.data_more () pact, NONE) |> the
  val test =
    (Z.Z4.ZM.Zip.move
    |> Z.comp Z.Z4.ZM.Down.move
    (* |> Z.comp PACTION.get_run_paction *)
    )
    (([n1, n2], NONE), ([], 0))
\<close>

ML\<open>
  structure PACTION2 =
  struct
    structure Base = Zippy_PAction_Mixin_Base(
      structure L = PACTION.MORE
      type prio = int)
    open Base
    structure PACTION = Zippy_PAction_Mixin(
    structure PACTION = Base
    structure AE = MEU.AE)
    open PACTION Base
  end
\<close>

ML\<open>
  val pact = PACTION.no_paction ()
  val pact2 = PACTION2.no_paction ()
  val n1 = Z.ZCORE.N4.node (PACTION.DATAM.data_more
    (PACTION2.DATAM.data_more () pact2)
    pact, NONE) |> the
  (* val n2 = Z.ZCORE.N4.node (PACTION.DATAM.data_more () pact |> the, NONE) |> the *)
  val test =
    (Z.Z4.ZM.Zip.move
    (* |> Z.comp Z.Z4.ZM.Down.move *)
    |> Z.comp PACTION2.get_run_paction
    )
    (([n1, n1], NONE), ([], 0))
\<close>

end
