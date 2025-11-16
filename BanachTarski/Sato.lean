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

-- The Sato Subgroup of SO3

def M_s: MAT := !![
  6, 2, 3;
  2, 3, -6;
  -3, 6, 2;
  ]

def M_t : MAT := !![
  2, -6, 3;
  6, 3, 2;
  -3, 2, 6;
]


noncomputable def M_s_normed: MAT := ((1/7):ℝ) • M_s
lemma M_s_normed_is_special : M_s_normed ∈ SO3 := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  constructor
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i j
  simp [M_s_normed, M_s, Matrix.transpose]
  fin_cases i <;> fin_cases j <;> norm_num
  <;> simp [Matrix.vecMul]
  <;> norm_num
  --
  --simp [Matrix.det_apply, M_s_normed, M_s]
  rw [Matrix.det_fin_three]
  rw [M_s_normed, M_s]
  norm_num
  simp
  norm_num



noncomputable def M_t_normed: MAT := ((1/7):ℝ) • M_t
lemma M_t_normed_is_special : M_t_normed ∈ SO3 := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  constructor
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i j
  simp [M_t_normed, M_t, Matrix.transpose]
  fin_cases i <;> fin_cases j <;> norm_num
  <;> simp [Matrix.vecMul]
  <;> norm_num
  --
  --simp [Matrix.det_apply, M_s_normed, M_s]
  rw [Matrix.det_fin_three]
  rw [M_t_normed, M_t]
  norm_num
  simp
  norm_num

noncomputable def s_op_n: SO3 := ⟨M_s_normed, M_s_normed_is_special⟩
noncomputable def t_op_n: SO3 := ⟨M_t_normed, M_t_normed_is_special⟩

noncomputable def s_i_op_n: SO3 := s_op_n⁻¹
noncomputable def t_i_op_n: SO3 := t_op_n⁻¹


def M_s_i: MAT := !![
  6, 2, -3;
  2, 3, 6;
  3, -6, 2;
  ]

example: s_i_op_n.val =  (7 :ℝ)⁻¹ • M_s_i := by
  simp [s_i_op_n]
  simp [Inv.inv]
  simp [star]
  simp [Matrix.transpose]
  simp [s_op_n]
  simp [M_s_normed]
  simp [M_s, M_s_i]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Div.div] <;> rfl


def M_t_i : MAT := !![
  2, 6, -3;
  -6, 3, 2;
  3, 2, 6;
]

example: t_i_op_n.val =  (7 :ℝ)⁻¹ • M_t_i := by
  simp [t_i_op_n]
  simp [Inv.inv]
  simp [star]
  simp [Matrix.transpose]
  simp [t_op_n]
  simp [M_t_normed]
  simp [M_t, M_t_i]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Div.div] <;> rfl


-- The Sato Subgroup of SO3
def sato_generators: Set SO3 := {s_op_n, t_op_n}
def SATO: Subgroup SO3 := Subgroup.closure sato_generators


lemma s_mem: s_op_n ∈ SATO := by
  simp [SATO]
  apply Subgroup.mem_closure_of_mem
  simp [sato_generators]

lemma t_mem: t_op_n ∈ SATO := by
  simp [SATO]
  apply Subgroup.mem_closure_of_mem
  simp [sato_generators]

noncomputable def sato_s: SATO := ⟨s_op_n, s_mem⟩
noncomputable def sato_t: SATO := ⟨t_op_n, t_mem⟩

def sato_generators_ss: Set SATO := {sato_s, sato_t}
noncomputable def sato_fg3_iso_seed: Fin 2 → SATO := ![sato_s, sato_t]

noncomputable def to_sato: FG2 →* SATO := FreeGroup.lift sato_fg3_iso_seed


lemma to_sato_range: (to_sato).range = Subgroup.closure sato_generators_ss := by
  have lem : sato_generators_ss = Set.range sato_fg3_iso_seed := by
    simp [sato_generators_ss, sato_fg3_iso_seed]
    exact Set.pair_comm sato_s sato_t



  rw [lem]
  apply FreeGroup.range_lift_eq_closure


theorem to_sato_is_surjective: Function.Surjective to_sato := by
  -- There's gotta be a better way.

  rw [← MonoidHom.range_eq_top]

  rw [to_sato_range]
  have h : sato_generators_ss = ((↑) : SATO → SO3) ⁻¹' sato_generators := by
    ext x
    simp [sato_generators_ss, sato_generators, Set.mem_preimage]
    constructor
    simp [sato_s, sato_t]
    · rintro (rfl | rfl)
      · simp
      · simp
    · intro hx
      have : x.val ∈ sato_generators := hx
      cases hx with
      | inl h =>
        have : x = ⟨s_op_n, s_mem⟩ := Subtype.ext h
        left; exact this
      | inr h =>
        have : x = ⟨t_op_n, t_mem⟩ := Subtype.ext h
        right; exact this
  rw [h]
  exact Subgroup.closure_closure_coe_preimage


noncomputable def mod7 (v: R3_raw) : R3_raw := ![((Int.floor (v 0)).natMod 7 : ℝ), ((Int.floor (v 1)).natMod 7 : ℝ), ((Int.floor (v 2)).natMod 7 : ℝ)]

lemma mod_lemma (A: MAT) (v: R3_raw) : mod7 (Matrix.mulVec A (mod7 v)) = mod7 (Matrix.mulVec A v) := by
  ext x
  fin_cases x
  <;> simp
  simp [mod7]
  simp only [Matrix.mulVec]
  simp only [dotProduct]
  --nth_rewrite 2 [Finset.sum_nat_mod (Finset.range 3) (7:ℕ) (fun (x: Fin 3) ↦ (A 0 x * v x)) ]
  sorry
  sorry
  sorry


lemma drop_eq_last {α} : ∀(M : Nat), ∀(L : List α), ∀{X : α},
    (L.length = M + 1) ∧
    (L.getLast? = some X) ->
    L.drop M = [X] := by

  rintro M
  induction' M with M pM

  rintro L X ⟨hlen, hlast⟩

  have : ∃ Linit, L = Linit ++ [X] := by
    -- standard library lemma: getLast?_eq_some_iff
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


def Vs: Set R3_raw := {
  ![3,1,2],
  ![5,4,1],
  ![6,2,4]
}

def Vt: Set R3_raw := {
  ![3,2,6],
  ![5,1,3],
  ![6,4,5]
}


def Vtinv: Set R3_raw := {
  ![3,5,1],
  ![5,6,4],
  ![6,3,2]
}

def Vsinv: Set R3_raw := {
  ![1,5,4],
  ![2,3,1],
  ![4,6,2]
}


lemma l1: ∀v ∈ Vs ∪ Vt ∪ Vtinv,  mod7 (Matrix.mulVec M_s v) ∈ Vs := by
  simp [M_s]
  simp [Vs]
  rintro v ((inVs | inVt) | inVtinv)

  rcases inVs with a | b | c
  rw [a]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]
  norm_num
  rfl
  --
  rw [b]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]
  --
  rw [c]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]
  norm_num
  --
  rcases inVt with a | b | c
  rw [a]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]
  norm_num
  rfl
  --
  rw [b]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]
  norm_num
  constructor
  rfl
  rfl
  --
  rw [c]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]
  norm_num
  --
  rcases inVtinv with a | b | c
  rw [a]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]
  norm_num

  --
  rw [b]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]
  --
  rw [c]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]

  --


lemma l2: ∀v ∈ Vsinv ∪ Vt ∪ Vtinv, mod7 (Matrix.mulVec M_s_i v) ∈ Vsinv := by
  simp [M_s_i]
  simp [Vsinv]
  rintro v ((inVsinv | inVt) | inVtinv)

  rcases inVsinv with a | b | c
  rw [a]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]
  norm_num
  rfl
  --
  rw [b]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]
  norm_num
  rfl
  --
  rw [c]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]
  norm_num
  --
  rcases inVt with a | b | c
  rw [a]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]
  norm_num

  --
  rw [b]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]
  norm_num
  constructor

  --
  rw [c]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]
  norm_num
  --
  rcases inVtinv with a | b | c
  rw [a]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]
  norm_num
  rfl

  --
  rw [b]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]
  norm_num
  --
  rw [c]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]

  --



lemma l3: ∀v ∈ Vt ∪ Vs ∪ Vsinv, mod7 (Matrix.mulVec M_t v) ∈ Vt := by
  simp [M_t]
  simp [Vt]
  rintro v ((inVt | inVs) | inVsinv)

  rcases inVt with a | b | c
  rw [a]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]
  norm_num

  --
  rw [b]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]
  norm_num
  --
  rw [c]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]
  norm_num
  --
  rcases inVs with a | b | c
  rw [a]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]
  norm_num

  --
  rw [b]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]
  norm_num
  constructor
  rfl
  rfl


  --
  rw [c]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]
  norm_num
  --
  rcases inVsinv with a | b | c
  rw [a]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]
  norm_num
  rfl

  --
  rw [b]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]
  norm_num
  rfl
  --
  rw [c]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]
  norm_num
  rfl
  --



lemma l4: ∀v ∈ Vtinv ∪ Vs ∪ Vsinv, mod7 (Matrix.mulVec M_t_i v) ∈ Vtinv := by
  simp [M_t_i]
  simp [Vtinv]
  rintro v ((inVinv | inVs) | inVsinv)

  rcases inVinv with a | b | c
  rw [a]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]
  norm_num
  rfl

  --
  rw [b]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]
  norm_num
  rfl
  --
  rw [c]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]
  norm_num
  rfl
  --
  rcases inVs with a | b | c
  rw [a]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]
  norm_num
  rfl

  --
  rw [b]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]
  norm_num
  rfl

  --
  rw [c]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]
  norm_num
  rfl
  --
  rcases inVsinv with a | b | c
  rw [a]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]
  norm_num

  --
  rw [b]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]
  norm_num
  rfl
  --
  rw [c]
  simp
  norm_num
  simp [mod7]
  simp [Int.natMod]
  norm_num
  rfl
  --


theorem to_sato_is_injective: Function.Injective to_sato := by
  apply (injective_iff_map_eq_one to_sato).mpr
  intro a
  contrapose!
  intro aneq1
  set w: List chartype := FreeGroup.toWord a with w_same
  have notone :  w ≠ ([]: List chartype) := by
    intro cont
    simp [w] at cont
    exact aneq1 cont


  have wlen: w.length ≠ 0  := (mt List.length_eq_zero_iff.mp) notone

  intro image_is_one

  have newlen : NeZero w.length := by
    dsimp [NeZero]
    apply neZero_iff.mpr
    exact (mt (List.length_eq_zero_iff.mp)) notone

  let TailPred (n:ℕ) : Bool :=
    n ≤ w.length && w.drop (w.length - n) = List.replicate n (0, false)

  let lSet_type :=Fin (w.length + 1)

  let S : Finset (lSet_type) := Finset.filter (fun n => TailPred ↑n) Finset.univ


  have zero_holds: TailPred 0 := by simp [TailPred]
  have ne: S.Nonempty := by
    --have trr: (0: (Fin w.length)) ∈ S := simp
    have mm: (Fin.ofNat (w.length + 1) 0) ∈ S := by
      simp [S]
      exact zero_holds

    exact Set.nonempty_of_mem mm


  let max_fin := Finset.max' S ne
  let n_trail_sinvs := (max_fin : ℤ)
  have nts_pos : n_trail_sinvs ≥ 0 := sorry

  let all_sinv := n_trail_sinvs = w.length

  let a2: FG2 :=  if (all_sinv) then a⁻¹ else σ ^ (-n_trail_sinvs - 1) * a * σ ^ (n_trail_sinvs + 1)

  have still: to_sato a2 = 1 := by
    simp [a2]
    rcases (em all_sinv) with all | notall
    simp [all]
    exact image_is_one
    --
    simp [notall]
    rw [image_is_one]
    simp
    rw [←zpow_add (to_sato σ)]
    norm_num

  set w2 := FreeGroup.toWord a2 with w2_same

  have w2_isreduced: FreeGroup.IsReduced w2 := by
    have sim: FreeGroup.IsReduced (FreeGroup.toWord a2) := FreeGroup.isReduced_toWord
    rwa [←w2_same] at sim

  have check_same: a2 = FreeGroup.mk w2 := FreeGroup.mk_toWord.symm


  let my_prod:= List.prod (w2.map fun x =>
    cond x.2 (sato_fg3_iso_seed x.1) (sato_fg3_iso_seed x.1)⁻¹)

  have case_image_is_my_prod : (to_sato a2) = my_prod := by
      simp [to_sato]
      rw [check_same]
      exact FreeGroup.lift_mk


  have w2_len_nonzero: w2.length ≠ 0 := by
    by_contra bad
    simp [w2] at bad
    simp [a2] at bad
    rcases (em all_sinv) with all | notall
    simp [all] at bad
    exact aneq1 bad

    ---
    simp [notall] at bad
    let trailing_as_nat : ℕ := Int.toNat n_trail_sinvs

    have lemm_a : ∃ c : FG2, a = c * ((σ⁻¹)^n_trail_sinvs) ∧ ((FreeGroup.toWord c).getLast?) != some (0, false) := sorry
    obtain ⟨c, pc⟩ := lemm_a
    rw [pc.left] at bad
    rw [mul_assoc] at bad
    rw [inv_zpow] at bad
    rw [←zpow_neg] at bad
    rw [zpow_add] at bad
    rw [mul_assoc c (σ ^ (-n_trail_sinvs)) ] at bad
    rw [←mul_assoc (σ ^ (-n_trail_sinvs)) ] at bad
    rw [←zpow_add] at bad
    norm_num at bad
    have little: -n_trail_sinvs - 1 = - (n_trail_sinvs + 1) := by linarith
    have res: c * σ = σ ^ (n_trail_sinvs + 1) := by
      rw [little] at bad
      rw [zpow_neg] at bad
      have mutbad:_ := congrArg (fun X => σ ^ (n_trail_sinvs + 1) * X) bad
      simp at mutbad
      exact mutbad

    have res2: c =  σ ^ n_trail_sinvs := by
      apply mul_right_cancel res

    have res2: a =   σ ^ n_trail_sinvs * σ ^ (-n_trail_sinvs) := by
      rw [pc.left]
      rw [res2]
      simp

    have res4: a = 1 := by
      rw [res2]
      simp

    exact aneq1 res4

  set N := w2.length with w2_len_lem
  have alllem: all_sinv → ((w.head?) = some (0, false)) := by
    intro is_all
    simp [all_sinv] at is_all
    simp [n_trail_sinvs] at is_all
    simp [max_fin] at is_all
    let typed_length := Fin.ofNat (w.length + 1) w.length
    have cond:_ := (Finset.max'_eq_iff S ne typed_length).mp
    have pred: S.max' ne = typed_length := by
      ext
      rw [is_all]
      simp [typed_length]

    have max_has_property:_ := (cond pred).left
    simp [S] at max_has_property
    simp [TailPred] at max_has_property
    have drp : _ := max_has_property.right
    simp [typed_length] at drp
    rw [drp]
    rw [List.head?_replicate]
    rw [w2_len_lem] at w2_len_nonzero
    simp [notone]

  have w2nonempty: w2 ≠ [] := (mt List.length_eq_zero_iff.mpr) w2_len_nonzero
  have w2nonempty2: ¬ (w2 = []) := by rwa [ne_eq] at w2nonempty
  have winvnonempty:  (FreeGroup.invRev w ≠ []) := by

    rw [←FreeGroup.invRev_length] at wlen
    exact (mt List.length_eq_zero_iff.mpr) wlen

  let DEFAULT := ((0:Fin 2), false)
  have end_lemma: w2.getLast? =  some (0, true) := by
    simp [w2]
    simp [a2]
    rcases (em all_sinv) with all | notall
    --
    simp [all]

    change (FreeGroup.invRev w).getLast? = some (0, true)
    simp [FreeGroup.invRev]


    rw [alllem all]
    --
    simp [notall]

    set intermed := (σ ^ (-n_trail_sinvs - 1) * a * σ ^ (n_trail_sinvs + 1)).toWord with intermed_def

    have p0:intermed = FreeGroup.reduce ((σ ^ (-n_trail_sinvs - 1) ).toWord ++ (a * σ ^ (n_trail_sinvs + 1)).toWord ) := by

      simp [intermed]
      rw [mul_assoc]
      rw [FreeGroup.toWord_mul]

    have p111:intermed = FreeGroup.reduce ((σ ^ (-n_trail_sinvs - 1)).toWord ++ FreeGroup.reduce (
      a.toWord ++ (σ ^ (n_trail_sinvs + 1)).toWord)) := by
      rwa [FreeGroup.toWord_mul] at p0

    have quick0 : n_trail_sinvs = Int.toNat n_trail_sinvs := Int.natCast_toNat_eq_self.mpr nts_pos

    have lemm_a : ∃ c : FG2, a = c * ((σ⁻¹)^n_trail_sinvs) ∧ ∃b: Bool, ((FreeGroup.toWord c).getLast? = some (1, b)) := sorry
    obtain ⟨c, pc⟩ := lemm_a

    have p2: intermed = FreeGroup.reduce ((σ ^ (-n_trail_sinvs - 1)).toWord ++ FreeGroup.toWord (c * σ))  := by
      rw [pc.left] at p111
      rw [←FreeGroup.toWord_mul] at p111
      rw [inv_zpow'] at p111
      rw [mul_assoc c] at p111
      rw [←zpow_add σ (-n_trail_sinvs) (n_trail_sinvs + 1) ] at p111
      simp at p111
      exact p111

    have p3: intermed = FreeGroup.reduce (((σ ^ (-n_trail_sinvs - 1)).toWord ++ c.toWord) ++ [(0, true)])  := by sorry



    have lemm_c : ∃ d : List chartype, ∃ T: ℕ, c.toWord = List.replicate T (0, true) ++ d ∧ (d.head?) != some (0, true) := sorry
    obtain ⟨d, T, pd⟩ := lemm_c

    let redd := (σ ^ (T -n_trail_sinvs - 1)).toWord ++ d ++ [(0, true)]

    have p3_5: intermed = FreeGroup.reduce redd  := by sorry


    let pre_im : FG2 := (σ ^ (-n_trail_sinvs - 1)) * c * σ

    have in_range: redd = FreeGroup.toWord pre_im := by

      simp [pre_im]


      sorry


    have p4: intermed = redd  := by sorry

    change intermed.getLast? = some (0, true)

    rw [p4]

    rw [List.getLast?_append]
    rw [List.getLast?_append]
    simp




  let Invariant (header: chartype) (op:MAT) : Prop :=

    let c1 := mod7 ((Matrix.col (op: MAT) 0))

    (header = (0, true) → c1 ∈ Vs) ∧
    (header = (1, true) → c1 ∈ Vt) ∧
    (header = (1, false) → c1 ∈ Vtinv) ∧
    (header = (0, false) → c1 ∈ Vsinv)

  let sev_mat := Matrix.diagonal (fun _ : Fin 3 ↦ (7:ℝ))

  let trunc_prod (i: ℕ): MAT := List.prod ((w2.drop (N - 1 - i)).map fun x =>
    let m := cond x.2 (sato_fg3_iso_seed x.1) (sato_fg3_iso_seed x.1)⁻¹
    (sev_mat) • (m: MAT))


  let header (i: ℕ) : chartype := w2.getD (N -i - 1) DEFAULT

  have claim : ∀ i : ℕ, (i < N) → Invariant (header i) (trunc_prod i) := by
    intro i i_le_N

    induction' i with i ih

    have triv1: (trunc_prod 0) = M_s := by
      simp [trunc_prod]

      let d: List MAT := (List.map (fun x ↦ sev_mat * (↑↑(bif x.2 then sato_fg3_iso_seed x.1 else (sato_fg3_iso_seed x.1)⁻¹))) w2)
      have simpler:  d = (List.map (fun x ↦ sev_mat * (↑↑(bif x.2 then sato_fg3_iso_seed x.1 else (sato_fg3_iso_seed x.1)⁻¹))) w2) := rfl
      rw [←simpler]
      have xl1: d.length = N - 1 + 1 := by
        simp [simpler]
        omega

      have xl2: d.getLast? = some M_s := by
        simp [d]
        left
        right
        constructor
        exact end_lemma
        --
        simp [sato_fg3_iso_seed]
        simp [sato_s]
        simp [s_op_n]
        simp [M_s_normed]
        simp [sev_mat]
        simp [Matrix.diagonal]
        sorry

      rw [drop_eq_last (N - 1) d ⟨xl1, xl2⟩]
      simp

    have triv2: header 0 = (0, true) := by
      simp [header]
      rw [List.getLast?_eq_getElem?] at end_lemma
      simp [N]
      apply Option.getD_eq_iff.mpr
      left
      exact end_lemma

    rw [triv2]
    rw [triv1]
    simp [Invariant]
    simp [M_s]
    simp only [Matrix.col_def]
    simp [Matrix.transpose]
    simp [Vs]
    right
    right
    ext i
    simp [mod7]
    fin_cases i <;> norm_num <;> rfl
    --

    simp [Invariant]
    let h := header (i + 1)
    let h_prev := header (i)
    simp at h
    let m7prev := mod7 (Matrix.col (trunc_prod ↑i) 0)

    have adj_lemma : ∀{i : Fin 2}, ∀{v : Bool}, h = (i, v) → (h_prev ≠ (i, not v)) := by
      intro j vt
      simp [h, h_prev]
      simp only [header]
      intro lhs
      intro bad
      let A:= w2.take (N - i - 2)
      let B:= w2.drop (N - i)
      let L2 := A ++ B
      let L3 := A ++ (j, vt) :: (j, not vt) :: B
      have same_lens : w2.length = L3.length :=  by

        simp [L3, A, B]
        have min1: N - i - 2 ≤ w2.length := by simp [N]; omega
        have min11: min (N - i - 2) w2.length = N - i - 2 := by simp [min1]
        simp [min11]
        rw [add_comm]
        nth_rewrite 1 [←add_zero w2.length]
        norm_num
        omega

      have w2_decomp: w2 = L3 := by

        simp [L3]
        simp [A]

        nth_rewrite 1 [←List.take_append_drop (N-i -2) w2]
        rw [List.append_cancel_left_eq]
        simp [B]
        nth_rewrite 1 [←List.cons_getElem_drop_succ]
        nth_rewrite 1 [←List.cons_getElem_drop_succ]
        simp
        constructor


        have h_conv : w2.getD ((N - (i+ 1)) - 1) DEFAULT = w2[N - i - 2] := by
          rw [List.getD_eq_getElem?_getD, List.getD_getElem?]
          have ll :N - (i+1) - 1 < w2.length  := by simp [N] ; omega
          simp [ll]
          rfl



        rw [← h_conv]
        exact lhs

        constructor



        have h_conv : w2.getD (N - i - 1) DEFAULT = w2[N - i - 2 + 1] := by
          rw [List.getD_eq_getElem?_getD, List.getD_getElem?]
          have ll :N - i - 1 < w2.length  := by simp [N] ; omega
          simp [ll]
          have eee : N -i - 2 + 1 = N - i - 1 := by omega
          simp [eee]

        rw [← h_conv]
        exact bad
        --

        have lx :  N - i - 2 + 1 + 1 = N - i := by omega

        rw [lx]
        simp [N]
        omega
        simp [N]
        omega


      have bb: FreeGroup.Red.Step w2 L2 := by
        rw [w2_decomp]
        have step: FreeGroup.Red.Step ((j, vt) :: (j, not vt) :: B) B :=
          FreeGroup.Red.Step.cons_not
        exact FreeGroup.Red.Step.append_left step
      have trouble:_:= FreeGroup.isReduced_iff_not_step.mp w2_isreduced
      exact (trouble L2) bb


    constructor
    -- header = (0, true)
    intro lhs
    have lim1: h_prev ≠ (0, false) := adj_lemma lhs
    simp [h_prev] at lim1
    simp [Invariant] at ih

    have ihtrig := ih (by linarith [i_le_N])
    have prev_lem: m7prev ∈ Vs ∪ Vt ∪ Vtinv := by
      simp [m7prev]
      rcases (wopts h_prev) with a | b | c | d
      simp [h_prev] at a
      left
      left
      exact ihtrig.left a
      ---
      simp [h_prev] at b
      absurd lim1 b
      trivial
      --
      simp [h_prev] at c
      left
      right
      exact ihtrig.right.left c
      --
      simp [h_prev] at d
      right
      exact ihtrig.right.right.left d

    have red: mod7 (Matrix.col (trunc_prod (↑i + 1)) 0) = mod7 (Matrix.mulVec M_s m7prev) := by
      have lem: trunc_prod (↑i + 1) = M_s * trunc_prod ↑i := by
        simp [trunc_prod]


        let d: List MAT := (List.map (fun x ↦ sev_mat * (↑↑(bif x.2 then sato_fg3_iso_seed x.1 else (sato_fg3_iso_seed x.1)⁻¹))) w2)
        have simpler:  d = (List.map (fun x ↦ sev_mat * (↑↑(bif x.2 then sato_fg3_iso_seed x.1 else (sato_fg3_iso_seed x.1)⁻¹))) w2) := rfl
        rw [←simpler]


        have lemm1: N - 1 - i = Nat.succ (Nat.pred (N - 1 - i)) :=  by
          have int0: N -1 -i ≠ 0 := by
            by_contra con
            sorry
          exact (Nat.succ_pred_eq_of_ne_zero  int0).symm

        set D := Nat.pred (N - 1 - i)  with ddef
        have pD2: N - 1 - (i+1) = D := by
          simp [D]
          omega
        rw [pD2, lemm1]

        have more: (List.drop D d) = M_s::(List.drop (D+1) d):= by
          rw [List.drop_add_one_eq_tail_drop]
          set DD := List.drop D d with dddef
          apply List.eq_cons_of_mem_head?
          simp [header] at lhs
          have sm: N - (i + 1) - 1 = D := by omega
          have sm2: N - 1 -i - 1 = D := by omega
          rw [sm] at lhs
          simp [DD]
          simp [D]
          simp [d]
          left
          right
          constructor
          rw [sm2]
          have more0:_:= Option.getD_eq_iff.mp lhs
          rcases more0 with L | R
          exact L
          --
          have evenmore: _:= List.getElem?_eq_none_iff.mp R.left
          simp [D] at evenmore
          simp [N] at evenmore
          exfalso
          omega
          --
          simp [sev_mat, sato_fg3_iso_seed, M_s, sato_s, s_op_n, M_s_normed]
          ext i j
          fin_cases i, j
          <;> simp






        rw [more]
        rfl

      simp [m7prev]
      rw [mod_lemma]
      rw [lem]
      rfl

    rw [red]
    exact l1 m7prev prev_lem

    constructor
    sorry
    constructor
    sorry
    sorry


  have last : Invariant (header (N-1)) (trunc_prod (N - 1)) := by
    exact claim (N-1) (by omega)

  let seventh_mat := ((1/7:ℝ)^N • (1: MAT))

  have equal_prods: my_prod = (seventh_mat)  * trunc_prod (N - 1) := by
    simp [my_prod]
    simp [trunc_prod]
    sorry

  have seven_floor : ⌊(7:ℝ)^N⌋ = (7:ℕ)^N := sorry


  have is_zero_lemma: mod7 (Matrix.col (sev_mat ^ N) 0) = 0 := by
    rw [Matrix.diagonal_pow]
    ext i
    fin_cases i
    <;> norm_num
    <;> simp [Pi.single]
    <;> simp [mod7]
    <;> rw [seven_floor]
    <;> dsimp

    change Int.toNat (7^N % 7) = 0
    simp
    have better: (7:ℕ)^N % 7 = 0 := by
      apply Nat.mod_eq_zero_of_dvd
      norm_num
      exact w2_len_nonzero
    have almost := Nat.le_of_eq better
    sorry
















































  have thus: to_sato a2 ≠ (1: SATO) := by
    by_contra isid
    rw [isid] at case_image_is_my_prod
    rw [←case_image_is_my_prod] at equal_prods
    have weird: sev_mat ^ N = trunc_prod (N-1) := sorry
    rw [← weird] at last
    simp [Invariant] at last

    rcases wopts (header (N-1)) with  c1 | c2 | c3 | c4
    have bad1 : _ := last.left c1
    rw [is_zero_lemma] at bad1
    simp [Vs] at bad1
    rcases bad1 with b1 | b2 | b3
    have := congrArg (fun f ↦ f 0) b1
    simp at this
    have := congrArg (fun f ↦ f 0) b2
    simp at this
    have := congrArg (fun f ↦ f 0) b3
    simp at this
    --
    have bad2 : _ := last.right.right.right c2
    rw [is_zero_lemma] at bad2
    simp [Vsinv] at bad2
    rcases bad2 with b1 | b2 | b3
    have := congrArg (fun f ↦ f 0) b1
    simp at this
    have := congrArg (fun f ↦ f 0) b2
    simp at this
    have := congrArg (fun f ↦ f 0) b3
    simp at this
    --
    have bad3 : _ := last.right.left c3
    rw [is_zero_lemma] at bad3
    simp [Vt] at bad3
    rcases bad3 with b1 | b2 | b3
    have := congrArg (fun f ↦ f 0) b1
    simp at this
    have := congrArg (fun f ↦ f 0) b2
    simp at this
    have := congrArg (fun f ↦ f 0) b3
    simp at this
    --
    have bad4 : _ := last.right.right.left c4
    rw [is_zero_lemma] at bad4
    simp [Vtinv] at bad4
    rcases bad4 with b1 | b2 | b3
    have := congrArg (fun f ↦ f 0) b1
    simp at this
    have := congrArg (fun f ↦ f 0) b2
    simp at this
    have := congrArg (fun f ↦ f 0) b3
    simp at this




  exact thus still





theorem to_sato_is_bijective: Function.Bijective to_sato := ⟨to_sato_is_injective, to_sato_is_surjective⟩

noncomputable def iso_forward_equiv := Equiv.ofBijective to_sato to_sato_is_bijective

noncomputable def sato_fg3_iso: FG2 ≃* SATO := MulEquiv.mk' iso_forward_equiv to_sato.map_mul'
