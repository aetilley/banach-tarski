import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

import BanachTarski.Common

set_option warningAsError false
set_option linter.all false
set_option maxHeartbeats 1000000


abbrev ZMAT:= Matrix (Fin 3) (Fin 3) ℤ
abbrev Z3_raw := (Fin 3) → ℤ

def to_MAT (A : ZMAT) : MAT :=
  A.map (Int.castRingHom ℝ)

lemma to_MAT_inj : Function.Injective (to_MAT) := by
  exact Matrix.map_injective (RingHom.injective_int (Int.castRingHom ℝ))

lemma to_MAT_transp : to_MAT (Matrix.transpose A) = Matrix.transpose (to_MAT A) := by
  simp only [to_MAT]
  simp [Matrix.transpose_map]

lemma to_MAT_mul : to_MAT (A * B) = (to_MAT A) * (to_MAT B):= by
  simp only [to_MAT]
  rw [Matrix.map_mul]

lemma to_MAT_prod (L: List ZMAT) : to_MAT (L.prod) = (List.map to_MAT L).prod := by
  induction L with
  | nil => simp; simp [to_MAT]
  | cons x xs ih => rw [List.prod_cons]; simp [to_MAT_mul]; apply congrArg; exact ih


lemma to_MAT_pow  : to_MAT (A^N) = (to_MAT A)^N := by
  let L := List.map (fun _  ↦ A) (List.range N)
  let ML := List.map to_MAT L
  calc to_MAT (A^N)
  _ = to_MAT (A^(L.length)) := by simp [L]
  _ = to_MAT L.prod := by
    rw [←List.prod_eq_pow_card]
    intro x xinL
    simp [L] at xinL
    exact xinL.right
  _ = ML.prod := by exact to_MAT_prod L
  _ = (to_MAT A) ^ ML.length := by
    rw [List.prod_eq_pow_card]
    intro x xinML
    simp [ML] at xinML
    simp [L] at xinML
    exact (xinML.right).symm
  _ = (to_MAT A) ^ N := by
    simp [ML]
    apply congrArg
    simp [L]


 def mod7_Z (v: Z3_raw) : Z3_raw :=
![((v 0) % 7 : ℤ),
  ((v 1) % 7 : ℤ),
  ((v 2) % 7 : ℤ)]

lemma mod7_Z_additive (v u : Z3_raw) : mod7_Z (v + u) = mod7_Z (mod7_Z v + mod7_Z u) := by
  simp [mod7_Z]

lemma mod7_Z_idempotent(v : Z3_raw) : mod7_Z (mod7_Z (v)) = mod7_Z v := by
  simp [mod7_Z]


lemma mod_lemma_Z (A: ZMAT) (v: Z3_raw) : mod7_Z (Matrix.mulVec A (mod7_Z v)) = mod7_Z (Matrix.mulVec A v) := by
  have rrr : ∃(a1 a2 a3: ℤ), v = (mod7_Z v) + ((7:ℤ) • (![a1, a2, a3]:Z3_raw)) := by
    use ((v 0) - ((mod7_Z v) 0)) / 7
    use ((v 1) - ((mod7_Z v) 1)) / 7
    use ((v 2) - ((mod7_Z v) 2)) / 7
    ext i
    fin_cases i
    <;> simp
    <;> rw [Int.mul_ediv_cancel']
    <;> ring
    <;> simp [mod7_Z]
    <;> exact Int.dvd_self_sub_emod

  obtain ⟨w1, w2, w3, prr⟩ := rrr
  nth_rewrite 2 [prr]
  simp only [Matrix.mulVec_add]
  rw [mod7_Z_additive]
  have zz: mod7_Z (Matrix.mulVec A ((7:ℤ) • (![↑w1, ↑w2, ↑w3]: Z3_raw))) = 0 := by
    rw [Matrix.mulVec_smul]
    simp [mod7_Z]
  rw [zz]
  simp
  rw [mod7_Z_idempotent]


lemma drop_eq_last {α} : ∀(M : Nat), ∀(L : List α), ∀{X : α},
  -- TODO: change this to a list induction, not induction on M
    (L.length = M + 1) ∧
    (L.getLast? = some X) ->
    L.drop M = [X] := by

  rintro M
  induction' M with M pM

  rintro L X ⟨hlen, hlast⟩

  have : ∃ Linit, L = Linit ++ [X] := by
    simpa [List.getLast?_eq_some_iff] using hlast

  obtain ⟨Linit, pLinit⟩ :=this

  simp
  rw [pLinit]
  simp

  have sublen : Linit.length = 0 := by
    have lem: L.length = Linit.length + 1 := by rw [pLinit]; exact List.length_append
    rw [hlen] at lem
    linarith [lem]

  exact List.length_eq_zero_iff.mp sublen

  -- now compute drop on an append

  rintro L X ⟨hlen, hlast⟩

  have head_tail: ∃ head: α, ∃ tail : List α,  L= head::tail := by
    exact List.exists_cons_of_length_eq_add_one hlen
  let ⟨head, tail, pht ⟩ := head_tail
  rw [pht]
  rw [List.drop_succ_cons]
  have inter:_:= calc (M + 1 + 1)
    _ = L.length := hlen.symm
    _ = (head::tail).length := by rw [pht]
    _ = tail.length + 1 := List.length_cons


  have len_lem: tail.length = M + 1 := by linarith [inter]

  have last_lem: tail.getLast? = some X := by
    rw [pht] at hlast
    rw [List.getLast?_cons] at hlast
    have netail: ¬  (tail = [] ):= by
      by_contra empt
      have is_zero: tail.length = 0 := by
        apply List.isEmpty_iff_length_eq_zero.mp
        simp [empt]
      rw [is_zero] at len_lem
      linarith

    simp at hlast
    have not_none:_ := mt List.getLast?_eq_none_iff.mp netail

    have r0:_ := Option.getD_eq_iff.mp hlast
    rcases r0 with l | r
    exact l
    --
    absurd not_none r.left
    trivial


  have res:_ := pM tail ⟨len_lem, last_lem⟩
  exact res


lemma diagonal_const_comm(d: ℝ) (k:ℕ) (M: MAT) :
(Matrix.diagonal (fun _ ↦ d))^k * M = M * (Matrix.diagonal (fun _ ↦ d))^k := by
  have flem : (fun _:Fin 3 ↦ d)^k = (fun _:Fin 3 ↦ d^k) := by
    ext x
    simp

  calc (Matrix.diagonal (fun _ ↦ d))^k * M
  _ = (Matrix.diagonal ((fun _ ↦ d)^k)) * M := by rw [Matrix.diagonal_pow (fun _:(Fin 3) ↦ d) k]
  _ = (Matrix.diagonal (fun _ ↦ d^k)) * M := by rw [flem]
  _ = (Matrix.diagonal ((fun _ ↦ d^k * (1:ℝ)))) * M := by simp
  _ = (Matrix.diagonal (d^k • (fun _ ↦ (1:ℝ)))) * M := by rfl
  _ = (d^k • (1:MAT)) • M := by rw [Matrix.diagonal_smul]; simp
  _ = d^k • M * 1 := by simp
  _ = d^k • (M * 1) := by simp
  _ = M * ((d^k) • 1) := by rw [←Matrix.mul_smul]
  _ = M * ((d^k) • Matrix.diagonal (fun _ ↦ (1:ℝ))) := by simp
  _ = M * (Matrix.diagonal (d^k • fun _ ↦ (1:ℝ))) := by rw [←Matrix.diagonal_smul]
  _ = M * (Matrix.diagonal (fun _ ↦ d^k * (1:ℝ))) := by rfl
  _ = M * (Matrix.diagonal (fun _ ↦ d^k)) := by simp
  _ = M * (Matrix.diagonal ((fun _ ↦ d)^k)) := by rw [←flem]
  _ = M * (Matrix.diagonal (fun _ ↦ d))^k := by rw [←Matrix.diagonal_pow (fun _:(Fin 3) ↦ d) k]


-- TODO: this should be a List induction on mats.  Get rid of the N param.
lemma zip_lemma: ∀ N: ℕ, ∀ mats: List MAT, ∀ d: ℝ ,
    (mats.length = N) → (Matrix.diagonal (fun _ ↦ d)^N * mats.prod =
    (List.map (fun M ↦ (Matrix.diagonal (fun _ ↦ d))* M) mats).prod) := by
    intro N
    induction' N with N ih
    intro mats d
    intro lhs
    simp
    have empty :_:= List.length_eq_zero_iff.mp lhs
    simp [empty]
    --
    intro mats d
    intro lhs

    have hprop : ∃H: MAT, ∃T: List MAT, mats = H::T := by exact List.exists_cons_of_length_eq_add_one lhs
    obtain ⟨H, T, pH⟩ := hprop
    have Tlen0: mats.length = T.length + 1 := by
      rw [pH]
      simp


    set D:= (Matrix.diagonal (fun x: Fin 3 ↦ d)) with Ddef
    set dmap := fun M:MAT ↦ D * M
    have res: _:= calc (Matrix.diagonal fun x ↦ d) ^ (N + 1) * mats.prod
      _ = D^(N+1) * mats.prod := by rw [←Ddef]
      _ = (D^N * D) * mats.prod := by rw [pow_add]; simp
      _ = (D * D^N) * mats.prod := by rw [diagonal_const_comm d N D]
      _ = (D * D^N) * (H::T).prod := by rw [pH]
      _ = (D * D^N) * (H * T.prod) := by exact List.prod_cons
      _ = ((D * D^N) * H) * T.prod := by rw [←mul_assoc]
      _ = (D * (D^N * H)) * T.prod := by rw [mul_assoc D]
      _ = (D * (H * D^N)) * T.prod := by rw [diagonal_const_comm d N H]
      _ = ((D * H) * D^N) * T.prod := by rw [←mul_assoc]
      _ = (D * H) * (D^N * T.prod) := by rw [mul_assoc]
      _ = (D * H) * (List.map dmap T).prod := by rw [ih]; linarith [Tlen0]
      _ = (dmap H) * (List.map dmap T).prod := by simp [dmap]
      _ = ((dmap H)::(List.map dmap T)).prod := by rw [←List.prod_cons]
      _ = (List.map dmap (H::T)).prod :=  by rw [List.map_cons]
      _ = (List.map dmap mats).prod :=  by simp [pH]

    simp [D]
    exact res

  def sev_mat_Z := Matrix.diagonal (fun _ : Fin 3 ↦ (7:ℤ))
  def sev_mat := to_MAT (sev_mat_Z)
  noncomputable def seventh_mat := Matrix.diagonal (fun _ : Fin 3 ↦ (7⁻¹:ℝ))

  lemma sev_mat_Z_mod_is_zero_lemma (N:ℕ): N ≠ 0 → mod7_Z (Matrix.col (sev_mat_Z ^ N) 0) = 0 := by
    intro Nnz
    simp [sev_mat_Z]
    rw [Matrix.diagonal_pow]
    have l: (fun (x:Fin 3) ↦ (7:ℤ)) ^ N = fun (x:Fin 3) ↦ (7:ℤ)^N := by
      ext x
      simp
    rw [l]
    simp
    simp [Pi.single]
    simp [mod7_Z]
    left
    exact Nnz

  lemma inv7lemma: (sev_mat^N) * (seventh_mat^N) = 1 := by
    simp [sev_mat, seventh_mat]
    rw [Matrix.diagonal_pow]
    simp [sev_mat_Z]
    simp [to_MAT]
    rw [Matrix.diagonal_pow]
    rw [Matrix.diagonal_mul_diagonal]
    simp

lemma sevsevlem: (7:ℝ)⁻¹ • (7:ℝ)⁻¹  • (fun (m: Fin 3) ↦ (49:ℝ)) = fun (_:Fin 3) ↦ (1:ℝ) := by
  ext x
  simp
  norm_num

lemma isreduced_of_take_of_reduced {α : Type u} (L : List (α × Bool)) (n: ℕ) :
  FreeGroup.IsReduced L → FreeGroup.IsReduced (L.take n):= by
    intro Lisreduced
    apply FreeGroup.isReduced_iff_not_step.mpr
    intro L2
    set T:= List.take n L with defT
    set D:= List.drop n L with defD
    by_contra is_step
    let L3 := L2 ++ D
    have biggerstep: FreeGroup.Red.Step L L3 := by
      rw [←List.take_append_drop n L]
      simp only [L3]
      rw [←defT]
      rw [←defD]
      apply FreeGroup.Red.Step.append_right
      exact is_step
    exact (FreeGroup.isReduced_iff_not_step.mp Lisreduced L3) biggerstep

lemma isreduced_of_drop_of_reduced {α : Type u} (L : List (α × Bool)) (n: ℕ) :
  FreeGroup.IsReduced L → FreeGroup.IsReduced (L.drop n):= by
    intro Lisreduced
    apply FreeGroup.isReduced_iff_not_step.mpr
    intro L2
    set T:= List.take n L with defT
    set D:= List.drop n L with defD
    by_contra is_step
    let L3 := T ++ L2
    have biggerstep: FreeGroup.Red.Step L L3 := by
      rw [←List.take_append_drop n L]
      simp only [L3]
      rw [←defT]
      rw [←defD]
      apply FreeGroup.Red.Step.append_left
      exact is_step
    exact (FreeGroup.isReduced_iff_not_step.mp Lisreduced L3) biggerstep




lemma isreduced_of_append_of_reduced_mismatching_boundary {α : Type u}
  {L M : List (α × Bool)} (p1 p2: (α × Bool)) (pl: L.getLast? = some p1) (ph: M.head? = some p2) :
    (FreeGroup.IsReduced L) ∧ (FreeGroup.IsReduced M) ∧ (p1.1 = p2.1 →  p1.2 = p2.2) → (FreeGroup.IsReduced (L ++ M)) := by
  rintro ⟨lisred, misred, arediff⟩
  simp [FreeGroup.IsReduced]
  apply List.isChain_append.mpr
  constructor
  exact lisred
  constructor
  exact misred
  intro x xlast
  simp at xlast
  intro y yfirst
  simp at yfirst
  rw [pl] at xlast
  rw [ph] at yfirst
  have p1isx:_:= Option.some_inj.mp xlast
  have p2isy:_:= Option.some_inj.mp yfirst
  rw [←p1isx, ←p2isy]
  exact arediff




-------

def TailPred_f (w: List chartype) (n: ℕ): Bool :=
  n ≤ w.length && w.drop (w.length - n) = List.replicate n ((0 : Fin 2), false)

abbrev lSet_type_f (w: List chartype): Type := Fin (w.length + 1)


def S_f (w: List chartype): Finset (lSet_type_f w) :=
  Finset.filter (fun n => TailPred_f w (n.val : ℕ)) Finset.univ

lemma TP_holds_of_zero_f (w: List chartype) : TailPred_f w 0 := by
  simp [TailPred_f]

lemma ne_S_f (w: List chartype): (S_f w).Nonempty := by
  have mm: (Fin.ofNat (w.length + 1) 0) ∈ S_f w := by
    simp [S_f]
    exact TP_holds_of_zero_f w
  exact Set.nonempty_of_mem mm

def max_fin_f (w: List chartype) : (lSet_type_f w) :=
  Finset.max' (S_f w) (ne_S_f w)

def n_trail_sinv_f (w: List chartype) : ℤ := ((max_fin_f w) : ℤ)

def trailing_as_nat_f (w : List chartype): ℕ := Int.toNat (n_trail_sinv_f w)

def leading_s_as_nat_f (w: List chartype): ℕ := trailing_as_nat_f (FreeGroup.invRev w)

def leading_others_as_nat_f (w: List chartype) : ℕ := Int.toNat (w.length - (n_trail_sinv_f w))

--



def all_sinv_f (w: List chartype): Prop :=  n_trail_sinv_f w = w.length
def last_is_sigma_f (w: List chartype): Prop := w.getLast? = some (0, true)

--
def all_s_f (w: List chartype): Prop := w = List.replicate w.length (0, true)
def first_is_sinv_f (w: List chartype): Prop := w.head? = some (0, false)

lemma if_not_all_sinv_w (w: List chartype) : (w ≠ []) ∧ (FreeGroup.IsReduced w) ∧
¬(all_sinv_f w) ∧ ¬(last_is_sigma_f w) →
∃ wc : List chartype,
  w = (wc ++ List.replicate (trailing_as_nat_f w) (0, false))  ∧
  (FreeGroup.IsReduced wc) ∧
  ∃b: Bool, (wc.getLast?) = some (1, b)  := by

  intro ⟨notone, is_reduced, notall, last_not_sigma⟩

  --

  set max_fin := max_fin_f w with mfdef
  set n_trail_sinvs := n_trail_sinv_f w with nts_def
  set trailing_as_nat : ℕ := trailing_as_nat_f w with trailing_def
  set leading_others_as_nat : ℕ := leading_others_as_nat_f w with leading_def

  have nts_pos : n_trail_sinvs ≥ 0 := by
    simp [n_trail_sinvs, n_trail_sinv_f]


  set all_sinv := all_sinv_f w with asdef
  set some_trailing_sinv := n_trail_sinvs > 0 with sts_def
  set  last_is_sigma := w.getLast? = some (0, true) with lis_def


  set S := S_f w with Sdef
  set ne_S := ne_S_f w with ne_S_def
  set TailPred := TailPred_f w with TPdef


  rcases (em some_trailing_sinv) with some_trail_sinv | no_trail_sinv

  use w.take leading_others_as_nat
  have lannz: ¬ (leading_others_as_nat = 0) := by
    simp [all_sinv] at notall
    simp [leading_others_as_nat, leading_others_as_nat_f]
    simp [n_trail_sinv_f]
    simp [all_sinv_f] at notall
    simp [n_trail_sinv_f] at notall
    apply Fin.lt_last_iff_ne_last.mpr
    by_contra badeq
    rw [badeq] at notall
    simp at notall



  have first_part: w = (w.take leading_others_as_nat ++ List.replicate trailing_as_nat (0, false))  := by

    simp [leading_others_as_nat, leading_others_as_nat_f]
    simp [n_trail_sinv_f]



    have ss: max_fin = S.max' ne_S := rfl
    have cond:_ := (Finset.max'_eq_iff S ne_S max_fin).mp ss
    simp [S, S_f] at cond
    simp [TailPred_f] at cond
    let cond1 := cond.left.right
    nth_rewrite 1 [←List.take_append_drop (w.length - max_fin) w]
    apply congrArg
    rw [cond1]
    rfl

  constructor
  exact first_part

  --

  set case := (List.take leading_others_as_nat w).getLast? with cset
  rcases (em case.isNone) with case_is_none | case_is_some
  exfalso
  simp [case] at case_is_none
  simp [lannz] at case_is_none
  exact notone case_is_none

  --

  constructor
  exact isreduced_of_take_of_reduced w leading_others_as_nat is_reduced


  --
  simp at case_is_some
  have issome:_:= Option.isSome_iff_ne_none.mpr case_is_some
  have existssome :_:= Option.isSome_iff_exists.mp issome
  obtain ⟨r, pr⟩ := existssome

  have opts :_:= wopts r

  rcases opts with st | sf | tt | tf

  exfalso
  rw [st] at pr
  rw [pr] at cset
  have bad: w = (List.take (leading_others_as_nat-1) w) ++ [(0, true)] ++ List.replicate trailing_as_nat (0, false) := by
    nth_rewrite 1 [first_part]
    apply congrArg (fun L ↦ L ++ List.replicate trailing_as_nat (0, false))
    have swt: leading_others_as_nat = leading_others_as_nat.pred + 1 := by
      rcases (Nat.eq_zero_or_eq_succ_pred leading_others_as_nat) with z | nz
      exfalso; exact lannz z
      exact nz

    nth_rewrite 1 [swt]
    rw [List.take_succ]
    simp
    rw [cset]
    rw [List.getLast?_take]
    simp [lannz]
    rw [Option.or_of_isSome]
    simp
    simp [leading_others_as_nat, leading_others_as_nat_f]
    simp [n_trail_sinv_f]
    change w.length - (↑(max_fin_f w) + 1) < w.length
    have gtl : 0 < (↑(max_fin_f w)) + (1:ℕ) := by
      exact Nat.succ_pos ↑(max_fin_f w)
    apply Nat.sub_lt_self gtl
    simp [all_sinv, all_sinv_f, n_trail_sinv_f] at notall
    omega





  have swll: trailing_as_nat = trailing_as_nat.pred + 1 := by
    rcases (Nat.eq_zero_or_eq_succ_pred trailing_as_nat) with z | nz
    simp [some_trailing_sinv] at some_trail_sinv
    simp [trailing_as_nat, trailing_as_nat_f]
    omega
    --
    rw [nz]
    simp

  have badbad: ¬ (FreeGroup.IsReduced w) := by


    by_contra isred
    have :_:= FreeGroup.isReduced_iff_not_step.mp isred

    rw [swll] at bad
    rw [List.replicate_succ] at bad
    let L2 := ((List.take (leading_others_as_nat - 1) w) ++ (List.replicate trailing_as_nat.pred (0, false)))
    have somestep: FreeGroup.Red.Step w L2 := by
      rw [bad]
      simp [L2]
      apply (FreeGroup.Red.Step.append_left_iff (List.take (leading_others_as_nat - 1) w) ).mpr
      apply FreeGroup.Red.Step.cons_not

    exact (this L2) somestep



  exact badbad is_reduced


  --
  exfalso
  rw [sf] at pr
  rw [pr] at cset


  have wrong_bound: (n_trail_sinvs + 1) ≤ w.length ∧
    w.drop (w.length - (max_fin + 1)) = List.replicate (max_fin + 1) (0, false) := by

    constructor
    simp [all_sinv, all_sinv_f, n_trail_sinv_f] at notall
    simp [n_trail_sinvs, n_trail_sinv_f]
    omega
    --
    have triv0: w.length - (max_fin + 1) = (w.length - max_fin) - 1 := by omega

    rw [triv0]

    have ltlem: max_fin < w.length := by
      simp [all_sinv] at notall
      simp [all_sinv_f, n_trail_sinv_f] at notall
      omega

    have ss: max_fin = S.max' ne_S := rfl
    have cond:_ := (Finset.max'_eq_iff S ne_S max_fin).mp ss
    simp [S, S_f] at cond
    simp [TailPred_f] at cond
    let cond1 := cond.left.right
    rw [List.replicate_succ]
    rw [←cond1]
    rw [List.drop_sub_one]
    have yyy:  ((0, false) :: List.drop (w.length - ↑max_fin) w)  =  ([(0, false)] ++ List.drop (w.length - ↑max_fin) w):= rfl
    rw [yyy]
    apply congrArg (fun L ↦ L ++ List.drop (w.length - ↑max_fin) w)
    simp
    rw [cset]
    simp [leading_others_as_nat]
    rw [List.getLast?_take]
    simp [all_sinv, all_sinv_f, n_trail_sinv_f] at notall
    simp [leading_others_as_nat_f]
    simp [n_trail_sinv_f]
    simp [max_fin]
    have bndlem: ¬(w.length ≤ ↑(max_fin_f w) ) := by omega
    simp [bndlem]
    rw [Option.or_of_isSome]
    simp
    omega
    have bblem: ↑max_fin < w.length := by
      exact ltlem
    omega



  have ss: max_fin = S.max' ne_S := rfl
  have cond:_ := (Finset.max'_eq_iff S ne_S max_fin).mp ss
  simp [S, S_f] at cond
  simp [TailPred_f] at cond
  let cond2 := cond.right
  have badbad :_ := cond2 (max_fin + 1)
  have first_pred: ↑(max_fin + 1) ≤ w.length := by exact Fin.is_le (max_fin + 1)
  have worse :_:= badbad first_pred
  have second_pred: List.drop (w.length - ↑(max_fin + 1)) w = List.replicate ↑(max_fin + 1) (0, false)  := by
    have intm: _:= cond.left.right
    have triv2: ↑(max_fin + 1) = (↑max_fin) + (1:ℕ) := by
      simp [all_sinv] at notall
      simp [all_sinv_f, n_trail_sinv_f] at notall
      have uu: max_fin.val < w.length := by
        apply Fin.val_lt_last
        by_contra iop
        simp [max_fin] at iop
        rw [iop] at notall
        simp at notall
      exact Fin.val_add_one_of_lt uu

    have triv1: w.length - ↑(max_fin + 1) = (w.length - ↑max_fin) - 1 := by omega
    rw [triv1]
    rw [triv2]

    rw [List.replicate_succ]
    rw [←intm]

    rw [List.drop_sub_one]
    have yyy:  ((0, false) :: List.drop (w.length - ↑max_fin) w)  =  ([(0, false)] ++ List.drop (w.length - ↑max_fin) w):= rfl
    rw [yyy]
    apply congrArg (fun L ↦ L ++ List.drop (w.length - ↑max_fin) w)
    simp
    rw [cset]
    simp [leading_others_as_nat, leading_others_as_nat_f]
    simp [n_trail_sinv_f]
    rw [List.getLast?_take]
    have easy:  ¬(w.length - ↑max_fin = 0 ) := by
      by_contra badeq
      simp [all_sinv] at notall
      simp [all_sinv_f, n_trail_sinv_f] at notall
      omega

    simp [max_fin] at easy
    simp [easy]
    rw [Option.or_of_isSome]
    simp
    omega
    --
    omega

  have even_worse :_:= worse second_pred
  rw [Fin.add_one_le_iff] at even_worse
  simp [all_sinv] at notall
  simp [all_sinv_f, n_trail_sinv_f] at notall
  exact notall (congrArg (fun x ↦ x.val) even_worse)
  --
  use true
  rwa [tt] at pr
  use false
  rwa [tf] at pr




  ----
  -- else no_trailing_sinv
  simp [some_trailing_sinv] at no_trail_sinv
  use w
  constructor
  simp [trailing_as_nat, trailing_as_nat_f]
  exact no_trail_sinv
  --
  constructor
  exact is_reduced
  -- by cases -on getlast, using last_not_sigma and no_trail_sinv.
  rcases (em (w.getLast?.isNone))  with last_is_none | last_not_none
  simp at last_is_none
  exfalso
  exact notone last_is_none
  --
  have enone:  w.getLast? ≠ none := by apply mt (Option.isNone_iff_eq_none.mpr) last_not_none
  have issome:_:= Option.isSome_iff_ne_none.mpr enone
  have existssome :_:= Option.isSome_iff_exists.mp issome
  obtain ⟨r, pr⟩ := existssome   --
  rcases (wopts r) with d1 | d2 | d3 | d4
  --
  rw [d1] at pr
  simp [last_is_sigma_f] at last_not_sigma
  exfalso
  exact last_not_sigma pr
  --
  exfalso
  rw [d2] at pr

  have badel: (1 ≤ w.length) ∧ (List.drop (w.length - 1) w = List.replicate 1 (0, false)) := by
    constructor
    by_contra notgt1
    simp at notgt1
    exact notone notgt1
    --
    simp [List.replicate_one]
    rw [List.drop_length_sub_one]
    simp
    rw [List.getLast?_eq_getLast] at pr
    exact Option.some.inj pr
    --
    exact notone
    --
    exact notone

  have tsts:  S.max' ne_S= max_fin := rfl
  have cond:_ := (Finset.max'_eq_iff S ne_S  max_fin).mp tsts
  simp [S, S_f, TailPred_f] at cond
  have bnd :_:= cond.right 1

  simp [lSet_type_f] at bnd
  have melem :1 % (w.length + 1) = 1 := by
    have wnz: (w.length + 1) ≠ 0 := by
      exact Ne.symm (Nat.zero_ne_add_one w.length )
    apply (Nat.mod_eq_iff_lt wnz).mpr
    linarith

  rw [melem] at bnd

  have bad: 1 ≤ max_fin := bnd badel.left badel.right


  simp [n_trail_sinvs] at no_trail_sinv
  simp [n_trail_sinv_f] at no_trail_sinv
  simp [max_fin] at bad
  rw [no_trail_sinv] at bad
  have :_:= Fin.le_iff_val_le_val.mp bad
  simp at this
  exact notone this

  --
  use true
  rw [d3] at pr
  exact pr

  ---
  use false
  rw [d4] at pr
  exact pr

   --

lemma all_sinv_equiv (w: List chartype) : all_sinv_f w → w = List.replicate (w.length) (0, false) := by
  simp [all_sinv_f, n_trail_sinv_f]
  intro predi
  have tsts:  ((S_f w).max') (ne_S_f w)= (max_fin_f w ):= rfl
  have cond:_ := (Finset.max'_eq_iff (S_f w) (ne_S_f w)  (max_fin_f w)).mp tsts
  simp [S_f, TailPred_f] at cond
  rw [predi] at cond
  have res:_:= cond.left.right
  simp at res
  exact res



lemma leading_trailing: trailing_as_nat_f (FreeGroup.invRev w) = leading_s_as_nat_f w := by
  simp [leading_s_as_nat_f]








lemma isReduced_of_replicate {a : chartype}: ∀{k: ℕ}, FreeGroup.IsReduced (List.replicate k a) := by
  simp [FreeGroup.IsReduced]
  intro k
  induction k with
  | zero => simp
  | succ n ih =>
    cases n with
    | zero => simp
    | succ m =>
      apply List.IsChain.cons_cons
      simp
      exact ih

lemma isReduced_of_invRev_of_isReduced {w: List chartype} :
(FreeGroup.IsReduced w) → (FreeGroup.IsReduced (FreeGroup.invRev w)) := by
  intro w_isred
  have :_:= FreeGroup.isReduced_iff_not_step.mp w_isred
  apply FreeGroup.isReduced_iff_not_step.mpr
  intro L2
  have ininl2: L2 = FreeGroup.invRev (FreeGroup.invRev L2) := by rw [FreeGroup.invRev_invRev]
  rw [ininl2]
  by_contra is_step
  have res :_:= FreeGroup.Red.step_invRev_iff.mp is_step
  exact this (FreeGroup.invRev L2) res


lemma reduce_invRev_right_cancel {L: List chartype} :
FreeGroup.reduce ( L ++ FreeGroup.invRev L) = [] := by
   have ininlem: ( L ++ FreeGroup.invRev L) =
   ( FreeGroup.invRev (FreeGroup.invRev (L ++ FreeGroup.invRev L))) := by exact FreeGroup.invRev_invRev.symm
   rw [ininlem]
   rw [FreeGroup.reduce_invRev]
   rw [FreeGroup.invRev_append]
   rw [FreeGroup.reduce_invRev_left_cancel]
   simp


lemma collapse_replics_1 (nf nt: ℕ) :  FreeGroup.reduce (
    List.replicate (nf) (σchar, false) ++
    List.replicate (nt) (σchar, true)
  ) = if nf = nt
  then [] else
  if (nf > nt) then List.replicate (nf - nt) (σchar, false)
  else List.replicate (nt - nf) (σchar, true)
  := by
    set A := List.replicate nf (σchar, false) with Adef
    set B := List.replicate nt (σchar, true) with Bdef
    rcases (em (nf=nt)) with eq | neq
    simp [eq]
    have invlem: A = FreeGroup.invRev B := by
      simp [A, B]
      simp [FreeGroup.invRev]
      exact eq

    rw [invlem]
    exact FreeGroup.reduce_invRev_left_cancel
    --
    simp [neq]
    rcases (em (nt < nf )) with tlf | flt
    simp [tlf]
    have xyz1:  A = List.replicate (nf - nt) (σchar, false) ++ (FreeGroup.invRev B) := by
      simp [A, B]
      simp [FreeGroup.invRev]
      omega
    rw [xyz1]
    rw [List.append_assoc]
    rw [←FreeGroup.reduce_append_reduce_reduce]
    rw [FreeGroup.reduce_invRev_left_cancel]
    simp
    --
    simp [flt]
    have xyz2:  B = (FreeGroup.invRev A) ++ List.replicate (nt - nf) (σchar, true) := by
      simp [A, B]
      simp [FreeGroup.invRev]
      omega

    rw [xyz2]
    rw [←List.append_assoc]
    rw [←FreeGroup.reduce_append_reduce_reduce]
    have trt: FreeGroup.reduce (A ++ FreeGroup.invRev A) = [] := by exact reduce_invRev_right_cancel
    rw [trt]
    simp




lemma collapse_replics_2 (n: ℕ): FreeGroup.reduce (
  (List.replicate n (σchar, false)) ++
  (List.replicate (n + 1) (σchar, true))
  ) = [(σchar, true)] := by
    rw [(collapse_replics_1 n (n+1))]
    simp


lemma if_not_all_init_s_w (w: List chartype) : (w ≠ []) ∧ (FreeGroup.IsReduced w) ∧
¬(all_s_f w) ∧ ¬(first_is_sinv_f w) →
∃ wc : List chartype,
  w = (List.replicate (leading_s_as_nat_f w) (0, true) ++ wc)  ∧
  (FreeGroup.IsReduced wc) ∧
  ∃b: Bool, (wc.head?) = some (1, b)  := by
  intro ⟨notone, is_reduced, notall, first_not_sinv⟩
  set w_inv := FreeGroup.invRev w with w_inv_def
  have cond1: w_inv ≠ []:= by
    simp [w_inv]
    by_contra isempt
    apply congrArg FreeGroup.invRev at isempt
    simp at isempt
    exact notone isempt

  have cond2: FreeGroup.IsReduced w_inv := by
    simp [w_inv]
    have redtwic: FreeGroup.reduce (FreeGroup.invRev w) = (FreeGroup.invRev w) := by
      calc FreeGroup.reduce (FreeGroup.invRev w)
      _ = FreeGroup.invRev (FreeGroup.reduce w) := FreeGroup.reduce_invRev
      _ = FreeGroup.invRev w := by rw [FreeGroup.isReduced_iff_reduce_eq.mp (is_reduced)]
    exact FreeGroup.isReduced_iff_reduce_eq.mpr redtwic

  have cond3: ¬ (all_sinv_f w_inv) := by
    by_contra all_sigs'
    simp [w_inv] at all_sigs'
    have all_sigs : _:= all_sinv_equiv (FreeGroup.invRev w) all_sigs'
    simp [all_s_f] at notall
    apply congrArg FreeGroup.invRev at all_sigs
    simp [FreeGroup.invRev_invRev] at all_sigs
    rw [all_sigs] at notall
    simp at notall
    simp [FreeGroup.invRev] at notall

  have cond4: ¬last_is_sigma_f w_inv := by
    by_contra last_is_s
    simp [last_is_sigma_f] at last_is_s
    simp [w_inv] at last_is_s
    simp [FreeGroup.invRev] at last_is_s
    simp [first_is_sinv_f] at first_not_sinv
    exact first_not_sinv last_is_s

  have :_:= if_not_all_sinv_w (w_inv) ⟨cond1, cond2, cond3, cond4⟩
  obtain ⟨wc_inv, p_wc_inv⟩ := this

  use FreeGroup.invRev wc_inv


  constructor
  calc w
    _ = FreeGroup.invRev w_inv := by simp [w_inv]
    _ = FreeGroup.invRev (wc_inv ++ List.replicate (trailing_as_nat_f w_inv) (0, false)) := by nth_rewrite 1 [p_wc_inv.left]; rfl
    _ = FreeGroup.invRev (List.replicate (trailing_as_nat_f w_inv) (0, false)) ++ FreeGroup.invRev (wc_inv) := FreeGroup.invRev_append
    _ = List.replicate (leading_s_as_nat_f w) (0, true) ++ FreeGroup.invRev wc_inv := by simp [FreeGroup.invRev]; exact leading_trailing

  constructor
  exact isReduced_of_invRev_of_isReduced (p_wc_inv.right.left)

  obtain ⟨c, pc⟩ := p_wc_inv.right.right
  use ¬c
  simp
  simp [FreeGroup.invRev]
  exact pc
  ---



--- Without loss of generality we can assume a member of the kernel ends in σ
lemma wolog_zero {G: Type} [Group G] (h: FG2 →* G) (a: FG2):
 (a ≠ 1) ∧ (h a = 1) → ∃a2: FG2, (a2 ≠ 1) ∧ (h a2 = 1) ∧ (FreeGroup.toWord a2).getLast? = some (0, true) := by

  rintro ⟨aneq1, image_is_one⟩

  set w: List chartype := FreeGroup.toWord a with w_same
  set max_fin := max_fin_f w with mfdef
  set n_trail_sinvs := n_trail_sinv_f w with nts_def
  set trailing_as_nat : ℕ := trailing_as_nat_f w with trailing_def

  have nts_pos : n_trail_sinvs ≥ 0 := by
    simp [n_trail_sinvs, n_trail_sinv_f]


  set all_sinv := all_sinv_f w with asdef
  set some_trailing_sinv := n_trail_sinvs > 0 with sts_def
  set  last_is_sigma := w.getLast? = some (0, true) with lis_def


  set S := S_f w with Sdef
  set ne_S := ne_S_f w with ne_S_def
  set TailPred := TailPred_f w with TPdef


  have w_isreduced: FreeGroup.IsReduced w := by
    have sim: FreeGroup.IsReduced (FreeGroup.toWord a) := FreeGroup.isReduced_toWord
    rwa [←w_same] at sim

  have notone :  w ≠ ([]: List chartype) := by
    intro cont
    simp [w] at cont
    exact aneq1 cont

  have wlen: w.length ≠ 0  := (mt List.length_eq_zero_iff.mp) notone





  have if_all_sinv: all_sinv → ((w.head?) = some (0, false)) := by
    intro is_all
    simp [all_sinv, all_sinv_f, n_trail_sinv_f] at is_all
    simp [max_fin_f] at is_all
    let typed_length := Fin.ofNat (w.length + 1) w.length
    have cond:_ := (Finset.max'_eq_iff S ne_S typed_length).mp
    have pred: S.max' ne_S = typed_length := by
      ext
      rw [is_all]
      simp [typed_length]

    have max_has_property:_ := (cond pred).left
    simp [S, S_f, TailPred_f] at max_has_property
    have drp : _ := max_has_property.right
    simp [typed_length] at drp
    rw [drp]
    rw [List.head?_replicate]
    simp [notone]


  -------------------------
  -- Our new kernel element
  -------------------------


  have dec_all_sinv : Decidable all_sinv := Classical.propDecidable all_sinv
  have dec_last_is_sigma : Decidable last_is_sigma := Classical.propDecidable last_is_sigma

  let a2: FG2 :=  dite last_is_sigma (fun _ => a) (fun _ =>
    dite all_sinv (fun _ => a⁻¹) (fun _ => σ ^ (-n_trail_sinvs - 1) * a * σ ^ (n_trail_sinvs + 1)))

  have still_in_kernel: h a2 = 1 := by

    simp [a2]

    rcases (em last_is_sigma) with last_is_sig | last_not_sig
    simp [last_is_sig]
    exact image_is_one
    --
    rcases (em all_sinv) with all | notall
    simp [last_not_sig]
    simp [all]
    exact image_is_one
    --
    simp [notall]
    simp [last_not_sig]
    rw [image_is_one]
    simp
    rw [←zpow_add (h σ)]
    norm_num

  set w2 := FreeGroup.toWord a2 with w2_same

  have w2_isreduced: FreeGroup.IsReduced w2 := by
    have sim: FreeGroup.IsReduced (FreeGroup.toWord a2) := FreeGroup.isReduced_toWord
    rwa [←w2_same] at sim

  have check_same: a2 = FreeGroup.mk w2 := FreeGroup.mk_toWord.symm


  set N := w2.length with w2_len_lem


  have end_lemma: w2.getLast? =  some (0, true) := by

    simp [w2]
    simp [a2]
    rcases (em last_is_sigma) with last_is_sig | last_not_sig
    simp [last_is_sig]
    simp [last_is_sigma] at last_is_sig
    simp [w] at last_is_sig
    exact last_is_sig


    rcases (em all_sinv) with all | notall


    --
    simp [all]
    simp [last_not_sig]

    change (FreeGroup.invRev w).getLast? = some (0, true)
    simp [FreeGroup.invRev]


    rw [if_all_sinv all]
    --
    simp [notall]
    simp [last_not_sig]



    have last_not_sigma: ¬last_is_sigma_f w := by
      simp [last_is_sigma_f]
      simpa [last_is_sigma] using last_not_sig



    --

    have res:_:= if_not_all_sinv_w w ⟨notone, w_isreduced, notall, last_not_sigma⟩
    rw [←trailing_def] at res

    obtain ⟨wc, pwc⟩ := res
    rw [mul_assoc]
    simp [FreeGroup.toWord_mul]
    rw [←w_same]
    rw [pwc.left]
    rw [List.append_assoc wc]
    have eqpows: σ ^ (n_trail_sinvs + 1) = σ ^ (trailing_as_nat + 1) := by rfl
    rw [eqpows]
    simp
    simp [σchar]
    nth_rewrite 2 [←FreeGroup.reduce_append_reduce_reduce]

    have rrr: FreeGroup.reduce wc = wc := by
      apply FreeGroup.isReduced_iff_reduce_eq.mp
      exact pwc.right.left

    rw [rrr]


    have replemma2: FreeGroup.reduce ((List.replicate trailing_as_nat ((0 : Fin 2), false)) ++
      (List.replicate (trailing_as_nat + 1) ((0 : Fin 2), true))) = [((0 : Fin 2), true)] := by
      exact collapse_replics_2 trailing_as_nat
    rw [replemma2]


    have redlem2: FreeGroup.reduce (wc ++ [(0, true)]) = wc ++ [(0, true)] := by
      apply FreeGroup.isReduced_iff_reduce_eq.mp
      obtain ⟨b, pb⟩ := pwc.right.right
      apply isreduced_of_append_of_reduced_mismatching_boundary (1, b) (0, true)
      exact pb
      --
      simp
      --
      constructor
      exact pwc.right.left
      constructor
      simp
      simp


    simp [redlem2]


    have powlem: σ ^ (-n_trail_sinvs - 1) = σ⁻¹ ^ (trailing_as_nat + 1) := by
      change σ ^ (-n_trail_sinvs - 1) = σ⁻¹ ^ ((trailing_as_nat + 1): ℤ)
      rw [inv_zpow']
      simp [trailing_as_nat, trailing_as_nat_f]
      simp [n_trail_sinvs, n_trail_sinv_f]
      apply congrArg
      linarith


    rw [powlem]
    rw [FreeGroup.toWord_pow]
    simp
    simp [FreeGroup.invRev]
    simp [σchar]


    set wr := wc ++ [(0, true)] with wr_def
    have wr_is_reduced : FreeGroup.IsReduced wr := by
      simp [wr]
      apply FreeGroup.isReduced_iff_reduce_eq.mpr
      exact redlem2

    rcases (em (¬first_is_sinv_f wr)) with no_first_not_sinv | yes_first_is_sinv


    have cond1 : wr ≠ [] := by simp [wr]
    have cond2 : FreeGroup.IsReduced wr := by exact wr_is_reduced

    have cond3 : ¬(all_s_f wr) := by
      by_contra act_all
      simp [wr] at act_all

      simp [all_s_f] at act_all
      rw [List.replicate_succ'] at act_all
      apply List.append_inj at act_all
      simp at act_all
      have pwc3: ∃ b, wc.getLast? = some (1, b) := pwc.right.right
      rw [act_all] at pwc3
      rw [List.getLast?_replicate] at pwc3
      simp at pwc3




    have cond4 : ¬(first_is_sinv_f wr) := by exact no_first_not_sinv


    have res2:_:= if_not_all_init_s_w wr ⟨cond1, cond2, cond3, cond4⟩
    obtain ⟨wd, wdp⟩ := res2


    rw [wdp.left]
    rw [←List.append_assoc]
    rw [←FreeGroup.reduce_append_reduce_reduce]

    have redlemagain: ∃k: ℕ, ∃b:Bool, FreeGroup.reduce
          (List.replicate (trailing_as_nat + 1) ((0:Fin 2), false) ++
          List.replicate (leading_s_as_nat_f wr) ((0: Fin 2), true)) =
          List.replicate k (0, b) := by
            let a:= trailing_as_nat + 1
            let b := leading_s_as_nat_f wr
            rw [←σ_def]
            rw [collapse_replics_1 a b]
            rcases (em (a = b)) with c1 | c2
            simp [c1]
            --
            simp [c2]
            rcases (em (b < a)) with d1 | d2
            simp [d1]
            simp [d2]

    obtain ⟨k, b, pkb⟩ := redlemagain
    rw [pkb]
    have isredalready: FreeGroup.reduce (List.replicate k (0, b) ++ FreeGroup.reduce wd) =
      List.replicate k (0, b) ++ FreeGroup.reduce wd := by
        rcases (em (k = 0)) with k_is_zero | k_nonzero
        simp [k_is_zero]
        --
        apply FreeGroup.isReduced_iff_reduce_eq.mp
        obtain ⟨b', pb'⟩ := wdp.right.right
        apply isreduced_of_append_of_reduced_mismatching_boundary (0, b) (1, b')
        simp [List.getLast?_replicate]
        exact k_nonzero
        rw [FreeGroup.isReduced_iff_reduce_eq.mp wdp.right.left]
        exact pb'
        constructor
        exact isReduced_of_replicate
        --
        constructor
        apply FreeGroup.isReduced_iff_reduce_eq.mpr
        simp
        simp







    rw [isredalready]

    have wdredstep : FreeGroup.reduce (wd) = wd := by
      exact FreeGroup.isReduced_iff_reduce_eq.mp (wdp.right.left)

    rw [wdredstep]
    have wdne: wd ≠ [] := by
      by_contra bad
      rw [bad] at wdp
      simp at wdp


    rw [List.getLast?_append_of_ne_nil _ wdne]
    have samelast : wd.getLast? = wr.getLast? := by
      rw [wdp.left]
      symm
      apply List.getLast?_append_of_ne_nil
      exact wdne


    rw [samelast]

    simp [wr]

    ------
    --yes_first_is_sinv : ¬¬first_is_sinv_f wc
    have ared: FreeGroup.reduce (List.replicate (trailing_as_nat + 1) (0, false) ++ wr) =
    (List.replicate (trailing_as_nat + 1) (0, false) ++ wr) := by
      simp [first_is_sinv_f] at yes_first_is_sinv
      apply FreeGroup.isReduced_iff_reduce_eq.mp
      apply isreduced_of_append_of_reduced_mismatching_boundary (0, false) (0,false)
      apply List.getLast?_replicate
      exact yes_first_is_sinv
      constructor
      exact isReduced_of_replicate
      constructor
      exact wr_is_reduced
      simp

    rw [ared]

    have wrne: wr ≠ [] := by
      simp [wr]

    rw [List.getLast?_append_of_ne_nil _ wrne]
    simp [wr]

  have a2_ne_one : a2 ≠ 1 := by
    by_contra badeq
    apply congrArg FreeGroup.toWord at badeq
    rw [←w2_same] at badeq
    simp at badeq
    rw [badeq] at end_lemma
    simp at end_lemma

  exact ⟨a2, a2_ne_one, still_in_kernel, end_lemma⟩
