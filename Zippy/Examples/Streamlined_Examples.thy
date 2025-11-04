\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Streamlined_Examples
  imports
    HOL.List
    Zippy.Zippy_Instance_Auto_HOL
begin

paragraph \<open>Summary\<close>
text \<open>Some streamlined proofs using Zippy.\<close>

lemma strict_sorted_iff: "sorted_wrt (<) l \<longleftrightarrow> sorted l \<and> distinct l"
(*NEW*)
by (zippy induct l where clasimp iff: antisym_conv1)
(*ORIG*)
(* by (induction l) (auto iff: antisym_conv1) *)

lemma tl_Nil: "tl xs = [] \<longleftrightarrow> xs = [] \<or> (\<exists>x. xs = [x])"
(*NEW*)
by (zippy cases xs)
(*ORIG*)
(* by (cases xs) auto *)

lemma list_nonempty_induct:
  "\<lbrakk> xs \<noteq> []; \<And>x. P [x]; \<And>x xs. xs \<noteq> [] \<Longrightarrow> P xs \<Longrightarrow> P (x # xs)\<rbrakk> \<Longrightarrow> P xs"
(*NEW*)
by (zippy induct xs rule: induct_list012)
(*ORIG*)
(* by(induction xs rule: induct_list012) auto *)

lemma list_induct2:
  "length xs = length ys \<Longrightarrow> P [] [] \<Longrightarrow>
   (\<And>x xs y ys. length xs = length ys \<Longrightarrow> P xs ys \<Longrightarrow> P (x#xs) (y#ys))
   \<Longrightarrow> P xs ys"
(*NEW*)
by (zippy induct xs arbitrary: ys where cases (pat) "_ :: _ list")
(*ORIG*)
(* proof (induct xs arbitrary: ys)
  case (Cons x xs ys) then show ?case by (cases ys) simp_all
qed simp *)

lemma list_induct3:
  "length xs = length ys \<Longrightarrow> length ys = length zs \<Longrightarrow> P [] [] [] \<Longrightarrow>
   (\<And>x xs y ys z zs. length xs = length ys \<Longrightarrow> length ys = length zs \<Longrightarrow> P xs ys zs \<Longrightarrow> P (x#xs) (y#ys) (z#zs))
   \<Longrightarrow> P xs ys zs"
(*NEW*)
by (induct xs arbitrary: ys zs)
(zippy cases (pat) ("_ :: _ list", "[]") where run run: Zippy.Run.Breadth_First.all')
(*ORIG*)
(* proof (induct xs arbitrary: ys zs)
  case Nil then show ?case by simp
next
  case (Cons x xs ys zs) then show ?case by (cases ys, simp_all)
    (cases zs, simp_all)
qed *)

lemma list_induct2':
  "\<lbrakk> P [] [];
  \<And>x xs. P (x#xs) [];
  \<And>y ys. P [] (y#ys);
   \<And>x xs y ys. P xs ys  \<Longrightarrow> P (x#xs) (y#ys) \<rbrakk>
 \<Longrightarrow> P xs ys"
(*NEW*)
by (zippy induct xs arbitrary: ys where cases (pat) ("_ :: _ list", "[]" "_ _"))
(*ORIG*)
(* by (induct xs arbitrary: ys) *)
(* (case_tac x, auto) *)

lemma dropWhile_neq_rev: "\<lbrakk>distinct xs; x \<in> set xs\<rbrakk> \<Longrightarrow>
  dropWhile (\<lambda>y. y \<noteq> x) (rev xs) = x # rev (takeWhile (\<lambda>y. y \<noteq> x) xs)"
(*NEW*)
by (zippy induct xs where subst dropWhile_append2)
(*ORIG*)
(* proof (induct xs)
  case (Cons a xs)
  then show ?case
    by(auto, subst dropWhile_append2, auto)
qed simp *)

lemma rev_eq_append_conv: "rev xs = ys @ zs \<longleftrightarrow> xs = rev zs @ rev ys"
(*NEW*)
by (zippy subst rev_rev_ident[symmetric])
(*ORIG*)
(* by (metis rev_append rev_rev_ident) *)

lemma split_list_first: "x \<in> set xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> set ys"
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons a xs)
  show ?case
    (*NEW*)
    using Cons by (cases "x = a")
    (zippy intro: Cons_eq_appendI where run run: "Zippy.Run.Depth_First.all 8")
  (*ORIG*)
  (* proof cases
    assume "x = a" thus ?case using Cons by fastforce
  next
    assume "x \<noteq> a" thus ?case using Cons by(fastforce intro!: Cons_eq_appendI)
  qed *)
qed

lemma take_map: "take n (map f xs) = map f (take n xs)"
(*ORIG*)
by (zippy induct n arbitrary: xs where cases (pat) "_ :: _ list")
(*NEW*)
(* proof (induct n arbitrary: xs)
  case 0
  then show ?case by simp
next
  case Suc
  then show ?case by (cases xs) simp_all
qed *)

lemma drop_map: "drop n (map f xs) = map f (drop n xs)"
(*NEW*)
by (zippy induct n arbitrary: xs where cases (pat) "_ :: _ list")
(*ORIG*)
(* proof (induct n arbitrary: xs)
  case 0
  then show ?case by simp
next
  case Suc
  then show ?case by (cases xs) simp_all
qed *)

lemma set_take_subset_set_take:
  "m \<le> n \<Longrightarrow> set(take m xs) \<le> set(take n xs)"
(*NEW*)
by (induct xs arbitrary: m n)
(zippy cases (pat) "_ :: nat" where simp add: take_Cons where run run: Zippy.Run.Breadth_First.all')
(*ORIG*)
(* proof (induct xs arbitrary: m n)
  case (Cons x xs m n) then show ?case
    by (cases n) (auto simp: take_Cons)
qed simp *)

lemma filter_insort:
  "sorted (map f xs) \<Longrightarrow> P x \<Longrightarrow> filter P (insort_key f x xs) = insort_key f x (filter P xs)"
  by (induct xs)
  (*NEW*)
  (zippy subst insort_is_Cons)
  (*ORIG*)
  (* (auto, subst insort_is_Cons, auto) *)

end

