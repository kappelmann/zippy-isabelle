\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory ML_State_Seq
  imports
    ML_State
begin

ML\<open>
  structure Seq_Monad = Seq_Monad_Trans(Identity_Monad)
  structure State_Seq = State_Trans(structure M = Seq_Monad; structure SR = Pair_State_Result_Base)
  structure State_Stack_Seq = State_Stack(State_Seq)

  infix 1 Seq_THEN
  fun fs1 Seq_THEN fs2 = Seq.THEN (fs1, fs2)

  infix 1 State_Seq_THEN
  fun stsq State_Seq_THEN ifstsq = State_Seq.bind stsq ifstsq

  infix 1 SS_THEN

  (*abbreviations for large monadic code*)
  structure State_Seq_Abbrevs = struct
    structure SS = State_Seq
    structure SSS = State_Stack_Seq
    val op SS_THEN = op State_Seq_THEN
    structure Seq_Monad = Monad(Seq_Monad)
  end
\<close>

end