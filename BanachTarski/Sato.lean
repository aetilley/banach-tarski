import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

import BanachTarski.Common
import BanachTarski.SatoUtils

set_option warningAsError false
set_option linter.all false
set_option maxHeartbeats 1000000


-- The Sato Subgroup of SO3

def M_s_Z: ZMAT := !![
  6, 2, 3;
  2, 3, -6;
  -3, 6, 2;
  ]

def M_t_Z : ZMAT := !![
  2, -6, 3;
  6, 3, 2;
  -3, 2, 6;
]

def M_s_Z_trans: ZMAT := !![
  6, 2, -3;
  2, 3, 6;
  3, -6, 2;
]

def M_t_Z_trans: ZMAT := !![
  2, 6, -3;
  -6, 3, 2;
  3, 2, 6;
]

lemma M_s_Z_transpose_def : Matrix.transpose M_s_Z = M_s_Z_trans := by
  simp [M_s_Z, M_s_Z_trans, Matrix.transpose]
  ext i j
  fin_cases i, j
  <;> simp


lemma M_t_Z_transpose_def : Matrix.transpose M_t_Z = M_t_Z_trans := by
  simp [M_t_Z, M_t_Z_trans, Matrix.transpose]
  ext i j
  fin_cases i, j
  <;> simp



lemma fnlem_s: M_s_Z * M_s_Z_trans = Matrix.diagonal 49 := by
  simp [M_s_Z, M_s_Z_trans, Matrix.diagonal]
  ext i j
  fin_cases i, j
  <;> simp



lemma fnlem_t: M_t_Z * M_t_Z_trans = Matrix.diagonal 49 := by
  simp [M_t_Z, M_t_Z_trans, Matrix.diagonal]
  ext i j
  fin_cases i, j
  <;> simp



def M_s: MAT := to_MAT M_s_Z
def M_t: MAT := to_MAT M_t_Z
lemma ms_def : M_s = to_MAT M_s_Z := rfl
lemma mt_def : M_t = to_MAT M_t_Z := rfl


noncomputable def M_s_normed: MAT := ((1/7):ℝ) • M_s
noncomputable def M_t_normed: MAT := ((1/7):ℝ) • M_t
lemma M_s_normed_transpose_def: Matrix.transpose M_s_normed = ((1/7):ℝ) • to_MAT M_s_Z_trans := by
  simp only [M_s_normed]
  rw [Matrix.transpose_smul]
  apply congrArg (fun x => ((1/7):ℝ) • x)
  simp only [M_s]
  rw [←to_MAT_transp]
  apply congrArg to_MAT
  exact M_s_Z_transpose_def


lemma M_t_normed_transpose_def: Matrix.transpose M_t_normed = ((1/7):ℝ) • to_MAT M_t_Z_trans := by
  simp only [M_t_normed]
  rw [Matrix.transpose_smul]
  apply congrArg (fun x => ((1/7):ℝ) • x)
  simp only [M_t]
  rw [←to_MAT_transp]
  apply congrArg to_MAT
  exact M_t_Z_transpose_def


lemma M_s_normed_is_special : M_s_normed ∈ SO3 := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  constructor
  rw [Matrix.mem_orthogonalGroup_iff]
  rw [M_s_normed_transpose_def]
  simp [M_s_normed]
  simp [M_s]
  rw [←to_MAT_mul]
  rw [fnlem_s]
  norm_num
  simp [to_MAT]
  rw [←Matrix.diagonal_smul]
  rw [←Matrix.diagonal_smul]
  rw [sevsevlem]
  simp
  --
  rw [Matrix.det_fin_three]
  rw [M_s_normed, M_s, M_s_Z, to_MAT]
  norm_num
  simp
  norm_num


lemma M_t_normed_is_special : M_t_normed ∈ SO3 := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  constructor
  rw [Matrix.mem_orthogonalGroup_iff]
  rw [M_t_normed_transpose_def]
  simp [M_t_normed]
  simp [M_t]
  rw [←to_MAT_mul]
  rw [fnlem_t]
  norm_num
  simp [to_MAT]
  rw [←Matrix.diagonal_smul]
  rw [←Matrix.diagonal_smul]
  rw [sevsevlem]
  simp
  --
  rw [Matrix.det_fin_three]
  rw [M_t_normed, M_t, M_t_Z, to_MAT]
  norm_num
  simp
  norm_num

noncomputable def s_op_n: SO3 := ⟨M_s_normed, M_s_normed_is_special⟩
noncomputable def t_op_n: SO3 := ⟨M_t_normed, M_t_normed_is_special⟩

noncomputable def s_i_op_n: SO3 := s_op_n⁻¹
lemma s_i_op_n_def : s_i_op_n = s_op_n⁻¹ := rfl
noncomputable def t_i_op_n: SO3 := t_op_n⁻¹
lemma t_i_op_n_def : t_i_op_n = t_op_n⁻¹ := rfl


def M_s_i_Z: ZMAT := !![
  6, 2, -3;
  2, 3, 6;
  3, -6, 2;
  ]

def M_s_i : MAT := to_MAT M_s_i_Z

lemma msi_def: M_s_i = to_MAT M_s_i_Z := rfl

lemma msinv_lem : M_s_i * M_s = Matrix.diagonal (fun _ : (Fin 3) ↦ (49:ℝ)) := by

  simp [M_s_i, M_s, M_s_Z, M_s_i_Z, Matrix.diagonal]
  rw [←to_MAT_mul]
  ext i j
  fin_cases i, j
  <;> simp
  <;> simp [to_MAT]



lemma msinv_lem2 : M_s * M_s_i = Matrix.diagonal (fun _ : (Fin 3) ↦ (49:ℝ)) := by
  simp [M_s_i, M_s, M_s_Z, M_s_i_Z, Matrix.diagonal]
  rw [←to_MAT_mul]
  ext i j
  fin_cases i, j
  <;> simp
  <;> simp [to_MAT]



lemma s_i_op_n_equiv : s_i_op_n.val =  (7 :ℝ)⁻¹ • M_s_i := by
  simp [s_i_op_n]
  simp [Inv.inv]
  simp [star]
  simp [Matrix.transpose]
  simp [s_op_n]
  simp [M_s_normed]
  simp [M_s, M_s_i, M_s_Z, to_MAT, M_s_i_Z]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> rfl

lemma s_i_op_n_equiv_2 : (7:ℝ) • s_i_op_n.val = M_s_i := by
  simp [s_i_op_n_equiv]


def M_t_i_Z : ZMAT := !![
  2, 6, -3;
  -6, 3, 2;
  3, 2, 6;
]

def M_t_i : MAT := to_MAT M_t_i_Z
lemma mti_def: M_t_i = to_MAT M_t_i_Z := rfl


lemma mtinv_lem : M_t_i * M_t = Matrix.diagonal (fun _ : (Fin 3) ↦ (49:ℝ)) := by
  simp [M_t_i, M_t, M_t_Z, M_t_i_Z, Matrix.diagonal]
  rw [←to_MAT_mul]
  ext i j
  fin_cases i, j
  <;> simp
  <;> simp [to_MAT]



lemma mtinv_lem2 : M_t * M_t_i = Matrix.diagonal (fun _ : (Fin 3) ↦ (49:ℝ)) := by
  simp [M_t_i, M_t, M_t_Z, M_t_i_Z, Matrix.diagonal]
  rw [←to_MAT_mul]
  ext i j
  fin_cases i, j
  <;> simp
  <;> simp [to_MAT]

lemma t_i_op_n_equiv: t_i_op_n.val =  (7 :ℝ)⁻¹ • M_t_i := by
  simp [t_i_op_n]
  simp [Inv.inv]
  simp [star]
  simp [Matrix.transpose]
  simp [t_op_n]
  simp [M_t_normed]
  simp [M_t, M_t_i, to_MAT, M_t_Z, M_t_i_Z]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> rfl

lemma t_i_op_n_equiv_2 : (7:ℝ) • t_i_op_n.val = M_t_i := by
  simp [t_i_op_n_equiv]

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


def Vs: Set Z3_raw := {
  ![3,1,2],
  ![5,4,1],
  ![6,2,4]
}

def Vt: Set Z3_raw := {
  ![3,2,6],
  ![5,1,3],
  ![6,4,5]
}


def Vtinv: Set Z3_raw := {
  ![3,5,1],
  ![5,6,4],
  ![6,3,2]
}

def Vsinv: Set Z3_raw := {
  ![1,5,4],
  ![2,3,1],
  ![4,6,2]
}

lemma l1: ∀v ∈ Vs ∪ Vt ∪ Vtinv,  mod7_Z (Matrix.mulVec M_s_Z v) ∈ Vs := by
  simp [M_s_Z]
  simp [Vs]
  rintro v ((inVs | inVt) | inVtinv)

  rcases inVs with a | b | c
  rw [a]
  norm_num
  simp [mod7_Z]
  --
  rw [b]
  simp
  norm_num
  simp [mod7_Z]
  --
  rw [c]
  simp
  norm_num
  simp [mod7_Z]
  --
  rcases inVt with a | b | c
  rw [a]
  simp
  norm_num
  simp [mod7_Z]
  --
  rw [b]
  simp
  norm_num
  simp [mod7_Z]
  --
  rw [c]
  simp
  norm_num
  simp [mod7_Z]
  --
  rcases inVtinv with a | b | c
  rw [a]
  simp
  norm_num
  simp [mod7_Z]
  --
  rw [b]
  simp
  norm_num
  simp [mod7_Z]

  --
  rw [c]
  simp
  norm_num
  simp [mod7_Z]


lemma l2: ∀v ∈ Vsinv ∪ Vt ∪ Vtinv, mod7_Z (Matrix.mulVec M_s_i_Z v) ∈ Vsinv := by
  simp [M_s_i_Z]
  simp [Vsinv]
  rintro v ((inVsinv | inVt) | inVtinv)

  rcases inVsinv with a | b | c
  rw [a]
  norm_num
  simp [mod7_Z]
  --
  rw [b]
  simp
  norm_num
  simp [mod7_Z]
  --
  rw [c]
  simp
  norm_num
  simp [mod7_Z]

  --
  rcases inVt with a | b | c
  rw [a]
  norm_num
  simp [mod7_Z]
  --
  rw [b]
  simp
  norm_num
  simp [mod7_Z]
  --
  rw [c]
  simp
  norm_num
  simp [mod7_Z]
  --
  rcases inVtinv with a | b | c
  rw [a]
  norm_num
  simp [mod7_Z]
  --
  rw [b]
  simp
  norm_num
  simp [mod7_Z]
  --
  rw [c]
  simp
  norm_num
  simp [mod7_Z]

  --


lemma l3: ∀v ∈ Vt ∪ Vs ∪ Vsinv, mod7_Z (Matrix.mulVec M_t_Z v) ∈ Vt := by
  simp [M_t_Z]
  simp [Vt]
  rintro v ((inVt | inVs) | inVsinv)

  rcases inVt with a | b | c
  rw [a]
  norm_num
  simp [mod7_Z]
  --
  rw [b]
  simp
  norm_num
  simp [mod7_Z]
  --
  rw [c]
  simp
  norm_num
  simp [mod7_Z]
  --
  rcases inVs with a | b | c
  rw [a]
  norm_num
  simp [mod7_Z]
  --
  rw [b]
  simp
  norm_num
  simp [mod7_Z]
  --
  rw [c]
  simp
  norm_num
  simp [mod7_Z]
  --
  rcases inVsinv with a | b | c
  rw [a]
  norm_num
  simp [mod7_Z]
  --
  rw [b]
  simp
  norm_num
  simp [mod7_Z]
  --
  rw [c]
  simp
  norm_num
  simp [mod7_Z]
  --


lemma l4: ∀v ∈ Vtinv ∪ Vs ∪ Vsinv, mod7_Z (Matrix.mulVec M_t_i_Z v) ∈ Vtinv := by
  simp [M_t_i_Z]
  simp [Vtinv]
  rintro v ((inVinv | inVs) | inVsinv)

  rcases inVinv with a | b | c
  rw [a]
  norm_num
  simp [mod7_Z]
  --
  rw [b]
  simp
  norm_num
  simp [mod7_Z]
  --
  rw [c]
  simp
  norm_num
  simp [mod7_Z]
  --
  rcases inVs with a | b | c
  rw [a]
  norm_num
  simp [mod7_Z]
  --
  rw [b]
  simp
  norm_num
  simp [mod7_Z]
  --
  rw [c]
  simp
  norm_num
  simp [mod7_Z]
  --
  rcases inVsinv with a | b | c
  rw [a]
  norm_num
  simp [mod7_Z]
  --
  rw [b]
  simp
  norm_num
  simp [mod7_Z]
  --
  rw [c]
  simp
  norm_num
  simp [mod7_Z]
  --


theorem to_sato_is_injective: Function.Injective to_sato := by
  apply (injective_iff_map_eq_one to_sato).mpr
  intro a
  contrapose!
  intro aneq1
  intro image_is_one

  have wlog : ∃b: FG2, (b ≠ 1) ∧ (to_sato b = 1) ∧ (FreeGroup.toWord b).getLast? = some (0, true) :=
    wolog_zero to_sato a ⟨aneq1, image_is_one⟩

  obtain ⟨a2, a2_not_one, a2_image_one, a2_ends_with_sigma⟩ := wlog

  set w2 := FreeGroup.toWord a2 with w2_def
  have a2_eq_mk_w2: a2 = FreeGroup.mk w2 := FreeGroup.mk_toWord.symm
  set N := w2.length with N_def
  have Nnezero: N ≠ 0 := by
    by_contra isz
    rw [List.length_eq_zero_iff.mp isz] at a2_ends_with_sigma
    simp at a2_ends_with_sigma


  let Invariant (header: chartype) (op:ZMAT) : Prop :=

    let c1 := mod7_Z ((Matrix.col op 0))

    (header = (0, true) → c1 ∈ Vs) ∧
    (header = (1, true) → c1 ∈ Vt) ∧
    (header = (1, false) → c1 ∈ Vtinv) ∧
    (header = (0, false) → c1 ∈ Vsinv)

  set tp_list : List ZMAT := w2.map fun x => (
    match x with
    | (0, true) => M_s_Z
    | (0, false) => M_s_i_Z
    | (1, true) => M_t_Z
    | (1, false) => M_t_i_Z
  ) with tplist_def

  let trunc_prod (i: ℕ): ZMAT := List.prod ((w2.drop (N - 1 - i)).map fun x =>
    match x with
    | (0, true) => M_s_Z
    | (0, false) => M_s_i_Z
    | (1, true) => M_t_Z
    | (1, false) => M_t_i_Z
  )

  let DEFAULT := ((0:Fin 2), false)

  let header (i: ℕ) : chartype := w2.getD (N -i - 1) DEFAULT

  have claim : ∀ i : ℕ, (i < N) → Invariant (header i) (trunc_prod i) := by
    intro i i_le_N

    induction' i with i ih

    have triv1: (trunc_prod 0) = M_s_Z := by
      simp [trunc_prod]

      rw [←tplist_def]
      simp [tp_list]

      have xl1: tp_list.length = N - 1 + 1 := by
        simp [tplist_def]
        omega

      have xl2: tp_list.getLast? = some M_s_Z := by
        simp [tp_list]
        left
        right
        exact a2_ends_with_sigma

      rw [drop_eq_last (N - 1) tp_list ⟨xl1, xl2⟩]
      simp

    have triv2: header 0 = (0, true) := by
      simp [header]
      rw [List.getLast?_eq_getElem?] at a2_ends_with_sigma
      simp [N]
      apply Option.getD_eq_iff.mpr
      left
      exact a2_ends_with_sigma

    rw [triv2]
    rw [triv1]
    simp [Invariant]
    simp [M_s_Z]
    simp only [Matrix.col_def]
    simp [Matrix.transpose]
    simp [Vs]
    right
    right
    ext i
    simp [mod7_Z]
    --

    simp [Invariant]
    let h := header (i + 1)
    let h_prev := header (i)
    simp at h
    let m7prev := mod7_Z (Matrix.col (trunc_prod ↑i) 0)

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

      have w2_isreduced: FreeGroup.IsReduced w2 := by
        have sim: FreeGroup.IsReduced (FreeGroup.toWord a2) := FreeGroup.isReduced_toWord
        rwa [←w2_def] at sim

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

    have red: mod7_Z (Matrix.col (trunc_prod (↑i + 1)) 0) = mod7_Z (Matrix.mulVec M_s_Z m7prev) := by
      have lem: trunc_prod (↑i + 1) = M_s_Z * trunc_prod ↑i := by
        simp [trunc_prod]


        let d: List MAT := (List.map (fun x ↦ sev_mat * ((bif x.2 then ((sato_fg3_iso_seed x.1):MAT) else ((sato_fg3_iso_seed x.1)⁻¹:MAT)))) w2)
        have simpler:  d = (List.map (fun x ↦ sev_mat * ((bif x.2 then ((sato_fg3_iso_seed x.1):MAT) else ((sato_fg3_iso_seed x.1)⁻¹:MAT)))) w2) := rfl

        rw [←tplist_def]


        have lemm1: N - 1 - i = Nat.succ (Nat.pred (N - 1 - i)) :=  by
          have int0: N -1 -i ≠ 0 := by omega
          exact (Nat.succ_pred_eq_of_ne_zero  int0).symm

        set D := Nat.pred (N - 1 - i)  with ddef
        have pD2: N - 1 - (i+1) = D := by
          simp [D]
          omega
        rw [pD2, lemm1]

        have more: (List.drop D tp_list) = M_s_Z::(List.drop (D+1) tp_list):= by
          rw [List.drop_add_one_eq_tail_drop]
          set DD := List.drop D d with dddef
          apply List.eq_cons_of_mem_head?
          simp [header] at lhs
          have sm: N - (i + 1) - 1 = D := by omega
          have sm2: N - 1 -i - 1 = D := by omega
          rw [sm] at lhs
          simp [D]
          simp [tplist_def]
          left
          right
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

        rw [more]
        rfl

      simp [m7prev]
      rw [mod_lemma_Z]
      rw [lem]
      rfl

    rw [red]
    exact l1 m7prev prev_lem

    constructor
    intro lhs
    -- header = (1, true)
    have lim1: h_prev ≠ (1, false) := adj_lemma lhs
    simp [h_prev] at lim1
    simp [Invariant] at ih


    have ihtrig := ih (by linarith [i_le_N])
    have prev_lem0: m7prev ∈ Vs ∪ Vt ∪ Vsinv := by
      simp [m7prev]
      rcases (wopts h_prev) with a | b | c | d
      --
      left
      left
      exact ihtrig.left a
      ---
      simp [h_prev] at b
      right
      exact ihtrig.right.right.right b

      --
      simp [h_prev] at c
      left
      right
      exact ihtrig.right.left c
      --
      simp [h_prev] at d
      absurd lim1 d
      trivial
    have prev_lem: m7prev ∈ Vt ∪ Vs ∪ Vsinv := by rwa [Set.union_comm Vs Vt] at prev_lem0

    have red: mod7_Z (Matrix.col (trunc_prod (↑i + 1)) 0) = mod7_Z (Matrix.mulVec M_t_Z m7prev) := by
      have lem: trunc_prod (↑i + 1) = M_t_Z * trunc_prod ↑i := by
        simp [trunc_prod]

        rw [←tplist_def]


        have lemm1: N - 1 - i = Nat.succ (Nat.pred (N - 1 - i)) :=  by
          have int0: N -1 -i ≠ 0 := by omega
          exact (Nat.succ_pred_eq_of_ne_zero  int0).symm

        set D := Nat.pred (N - 1 - i)  with ddef
        have pD2: N - 1 - (i+1) = D := by
          simp [D]
          omega
        rw [pD2, lemm1]

        have more: (List.drop D tp_list) = M_t_Z::(List.drop (D+1) tp_list):= by
          rw [List.drop_add_one_eq_tail_drop]
          set DD := List.drop D tp_list with dddef
          apply List.eq_cons_of_mem_head?
          simp [header] at lhs
          have sm: N - (i + 1) - 1 = D := by omega
          have sm2: N - 1 -i - 1 = D := by omega
          rw [sm] at lhs
          simp [DD]
          simp [D]
          simp [tplist_def]
          right
          right
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

        rw [more]
        rfl

      simp [m7prev]
      rw [mod_lemma_Z]
      rw [lem]
      rfl
    rw [red]
    exact l3 m7prev prev_lem

    constructor
    intro lhs

    -- header = (1, false)
    have lim1: h_prev ≠ (1, true) := adj_lemma lhs
    simp [h_prev] at lim1
    simp [Invariant] at ih


    have ihtrig := ih (by linarith [i_le_N])
    have prev_lem0: m7prev ∈ Vs ∪ Vsinv ∪ Vtinv:= by
      simp [m7prev]
      rcases (wopts h_prev) with a | b | c | d
      --
      left
      left
      exact ihtrig.left a
      ---
      left
      right
      exact ihtrig.right.right.right b

      --
      simp [h_prev] at c
      absurd lim1 c
      trivial
      --
      right
      exact ihtrig.right.right.left d
    have prev_lem: m7prev ∈  Vtinv ∪ Vs ∪ Vsinv := by
      rw [Set.union_comm (Vs ∪ Vsinv) Vtinv] at prev_lem0
      rw [←Set.union_assoc] at prev_lem0
      exact prev_lem0

    have red: mod7_Z (Matrix.col (trunc_prod (↑i + 1)) 0) = mod7_Z (Matrix.mulVec M_t_i_Z m7prev) := by
      have lem: trunc_prod (↑i + 1) = M_t_i_Z * trunc_prod ↑i := by
        simp [trunc_prod]
        rw [←tplist_def]


        have lemm1: N - 1 - i = Nat.succ (Nat.pred (N - 1 - i)) :=  by
          have int0: N -1 -i ≠ 0 := by omega
          exact (Nat.succ_pred_eq_of_ne_zero  int0).symm

        set D := Nat.pred (N - 1 - i)  with ddef
        have pD2: N - 1 - (i+1) = D := by
          simp [D]
          omega
        rw [pD2, lemm1]

        have more: (List.drop D tp_list) = M_t_i_Z::(List.drop (D+1) tp_list):= by
          rw [List.drop_add_one_eq_tail_drop]
          set DD := List.drop D tp_list with dddef
          apply List.eq_cons_of_mem_head?
          simp [header] at lhs
          have sm: N - (i + 1) - 1 = D := by omega
          have sm2: N - 1 -i - 1 = D := by omega
          rw [sm] at lhs
          simp [DD]
          simp [D]
          simp [tp_list]
          right
          left
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
        rw [more]
        rfl

      simp [m7prev]
      rw [mod_lemma_Z]
      rw [lem]
      rfl
    rw [red]
    exact l4 m7prev prev_lem

    --
    intro lhs
    -- header (i + 1) = (0, false)

    have lim1: h_prev ≠ (0, true) := adj_lemma lhs
    simp [h_prev] at lim1
    simp [Invariant] at ih

    have ihtrig := ih (by linarith [i_le_N])
    have prev_lem0: m7prev ∈ Vt ∪ Vsinv ∪ Vtinv:= by
      simp [m7prev]
      rcases (wopts h_prev) with a | b | c | d
      --
      absurd lim1 a
      trivial
      --
      left
      right
      exact ihtrig.right.right.right b
      ---
      left
      left
      exact ihtrig.right.left c
      --
      right
      exact ihtrig.right.right.left d

    have prev_lem: m7prev ∈  Vsinv ∪ Vt ∪ Vtinv := by
      rw [Set.union_comm Vt Vsinv] at prev_lem0
      exact prev_lem0

    have red: mod7_Z (Matrix.col (trunc_prod (↑i + 1)) 0) = mod7_Z (Matrix.mulVec M_s_i_Z m7prev) := by
      have lem: trunc_prod (↑i + 1) = M_s_i_Z * trunc_prod ↑i := by
        simp [trunc_prod]


        rw [←tplist_def]


        have lemm1: N - 1 - i = Nat.succ (Nat.pred (N - 1 - i)) :=  by
          have int0: N -1 -i ≠ 0 := by omega
          exact (Nat.succ_pred_eq_of_ne_zero  int0).symm

        set D := Nat.pred (N - 1 - i)  with ddef
        have pD2: N - 1 - (i+1) = D := by
          simp [D]
          omega
        rw [pD2, lemm1]

        have more: (List.drop D tp_list) = M_s_i_Z::(List.drop (D+1) tp_list):= by
          rw [List.drop_add_one_eq_tail_drop]
          set DD := List.drop D tp_list with dddef
          apply List.eq_cons_of_mem_head?
          simp [header] at lhs
          have sm: N - (i + 1) - 1 = D := by omega
          have sm2: N - 1 -i - 1 = D := by omega
          rw [sm] at lhs
          simp [DD]
          simp [D]
          simp [tp_list]
          left
          left
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

        rw [more]
        rfl

      simp [m7prev]
      rw [mod_lemma_Z]
      rw [lem]
      rfl
    rw [red]
    exact l2 m7prev prev_lem


  have last : Invariant (header (N-1)) (trunc_prod (N - 1)) := by
    apply claim (N-1)
    exact Nat.sub_one_lt Nnezero


  let pre_prod:= (w2.map fun x => ((cond x.2 (sato_fg3_iso_seed x.1) (sato_fg3_iso_seed x.1)⁻¹)))
  set pre_prod_MAT:= (w2.map fun x => ((cond x.2 ((sato_fg3_iso_seed x.1):MAT) ((sato_fg3_iso_seed x.1):MAT)⁻¹))) with ppm_def

  have len_ppm : pre_prod_MAT.length = N := by
    simp [pre_prod_MAT]
    exact N_def.symm

  let my_prod:= List.prod (pre_prod)
  let my_prod_MAT:= List.prod (pre_prod_MAT)

  have case_image_is_my_prod : (to_sato a2) = my_prod := by
      simp [to_sato]
      rw [a2_eq_mk_w2]
      exact FreeGroup.lift_mk

  have case_image_is_my_prod_MAT : ((to_sato a2): MAT) = my_prod_MAT := by
    simp [case_image_is_my_prod]
    simp [my_prod, my_prod_MAT]
    apply congrArg List.prod
    simp [pre_prod, pre_prod_MAT]
    simp [sato_fg3_iso_seed]
    simp [sato_s, sato_t]
    constructor
    intro lhs
    exact (so3_invs_coe s_op_n).symm
    intro lhs
    exact (so3_invs_coe t_op_n).symm


  have equal_prods: (sev_mat ^N) * my_prod_MAT = to_MAT (trunc_prod (N - 1)) := by

    simp [trunc_prod]
    rw [to_MAT_prod]
    --
    simp [my_prod_MAT]
    simp [sev_mat, sev_mat_Z]

    simp [to_MAT]
    have inter:_ := zip_lemma N pre_prod_MAT (7:ℝ) len_ppm
    rw [inter]

    simp [pre_prod_MAT]
    apply congrArg List.prod
    simp
    simp [sato_fg3_iso_seed]
    simp [sato_s, sato_t]
    constructor
    constructor
    intro _
    rw [←mul_one (to_MAT M_s_i_Z)]
    have xyz: (1:MAT) = (s_op_n:MAT) * (s_op_n:MAT)⁻¹ := by
      rw [so3_invs_coe s_op_n]
      have cm: s_op_n.val * s_op_n⁻¹.val = (s_op_n * s_op_n⁻¹).val := rfl
      rw [cm]
      simp

    rw [xyz]
    rw [←mul_assoc]
    apply congrArg (fun M ↦ M * (s_op_n:MAT)⁻¹)
    rw [←msi_def]
    simp [s_op_n]
    simp [M_s_normed]
    rw [msinv_lem]
    norm_num
    rw [←Matrix.diagonal_smul]
    apply congrArg
    ext x
    simp
    norm_num
    ---
    intro _
    rw [←mul_one (to_MAT M_s_Z)]
    have xyz: (1:MAT) = (s_op_n:MAT)⁻¹ * (s_op_n:MAT) := by
      rw [so3_invs_coe s_op_n]
      have cm: (s_op_n⁻¹).val * s_op_n.val = (s_op_n⁻¹ * s_op_n).val := rfl
      rw [cm]
      simp

    rw [xyz]
    rw [←mul_assoc]
    apply congrArg (fun M ↦ M * (s_op_n:MAT))
    rw [←ms_def]
    rw [so3_invs_coe s_op_n]
    rw [←s_i_op_n_def]
    rw [s_i_op_n_equiv]
    simp
    rw [msinv_lem2]
    norm_num
    rw [←Matrix.diagonal_smul]
    apply congrArg
    ext x
    simp
    norm_num
    --
    constructor
    intro _
    rw [←mul_one (to_MAT M_t_i_Z)]
    have xyz: (1:MAT) = (t_op_n:MAT) * (t_op_n:MAT)⁻¹ := by
      rw [so3_invs_coe t_op_n]
      have cm: t_op_n.val * t_op_n⁻¹.val = (t_op_n * t_op_n⁻¹).val := rfl
      rw [cm]
      simp

    rw [xyz]
    rw [←mul_assoc]
    apply congrArg (fun M ↦ M * (t_op_n⁻¹:MAT))
    rw [←mti_def]
    simp [t_op_n]
    simp [M_t_normed]
    rw [mtinv_lem]
    norm_num
    rw [←Matrix.diagonal_smul]
    apply congrArg
    ext x
    simp
    norm_num
    --
    intro _
    rw [←mul_one (to_MAT M_t_Z)]
    have xyz: (1:MAT) = (t_op_n:MAT)⁻¹ * (t_op_n:MAT) := by
      rw [so3_invs_coe t_op_n]
      have cm: t_op_n⁻¹.val * t_op_n.val = (t_op_n⁻¹ * t_op_n).val := rfl
      rw [cm]
      simp

    rw [xyz]
    rw [←mul_assoc]
    apply congrArg (fun M ↦ M * (t_op_n:MAT))
    rw [←mt_def]
    rw [so3_invs_coe t_op_n]
    rw [←t_i_op_n_def]
    rw [t_i_op_n_equiv]
    simp
    rw [mtinv_lem2]
    norm_num
    rw [←Matrix.diagonal_smul]
    apply congrArg
    ext x
    simp
    norm_num


  have thus: to_sato a2 ≠ (1: SATO) := by
    by_contra isid
    have uh : ((to_sato a2) : MAT) = 1 := by simp [isid]
    rw [uh] at case_image_is_my_prod_MAT

    rw [←case_image_is_my_prod_MAT] at equal_prods

    simp at equal_prods
    have weird1: sev_mat ^ N = to_MAT (trunc_prod (N-1)) := by exact equal_prods
    have weird: sev_mat_Z ^ N = (trunc_prod (N-1)) := by
      simp only [sev_mat] at weird1
      rw [←to_MAT_pow] at weird1
      apply to_MAT_inj
      exact weird1

    rw [← weird] at last
    simp [Invariant] at last


    rcases wopts (header (N-1)) with  c1 | c2 | c3 | c4
    have bad1 : _ := last.left c1
    rw [sev_mat_Z_mod_is_zero_lemma N] at bad1
    simp [Vs] at bad1
    rcases bad1 with b1 | b2 | b3
    have := congrArg (fun f ↦ f 0) b1
    simp at this
    have := congrArg (fun f ↦ f 0) b2
    simp at this
    have := congrArg (fun f ↦ f 0) b3
    simp at this
    exact Nnezero
    --
    have bad2 : _ := last.right.right.right c2
    rw [sev_mat_Z_mod_is_zero_lemma N] at bad2
    simp [Vsinv] at bad2
    rcases bad2 with b1 | b2 | b3
    have := congrArg (fun f ↦ f 0) b1
    simp at this
    have := congrArg (fun f ↦ f 0) b2
    simp at this
    have := congrArg (fun f ↦ f 0) b3
    simp at this
    exact Nnezero
    --
    have bad3 : _ := last.right.left c3
    rw [sev_mat_Z_mod_is_zero_lemma N] at bad3
    simp [Vt] at bad3
    rcases bad3 with b1 | b2 | b3
    have := congrArg (fun f ↦ f 0) b1
    simp at this
    have := congrArg (fun f ↦ f 0) b2
    simp at this
    have := congrArg (fun f ↦ f 0) b3
    simp at this
    exact Nnezero

    --
    have bad4 : _ := last.right.right.left c4
    rw [sev_mat_Z_mod_is_zero_lemma N] at bad4
    simp [Vtinv] at bad4
    rcases bad4 with b1 | b2 | b3
    have := congrArg (fun f ↦ f 0) b1
    simp at this
    have := congrArg (fun f ↦ f 0) b2
    simp at this
    have := congrArg (fun f ↦ f 0) b3
    simp at this
    exact Nnezero

  exact thus a2_image_one


theorem to_sato_is_bijective: Function.Bijective to_sato := ⟨to_sato_is_injective, to_sato_is_surjective⟩

noncomputable def iso_forward_equiv := Equiv.ofBijective to_sato to_sato_is_bijective

noncomputable def sato_fg3_iso: FG2 ≃* SATO := MulEquiv.mk' iso_forward_equiv to_sato.map_mul'

-- First, define the SMul instance for SATO
instance SATO_smul_R3 : SMul SATO R3 where
  smul g x := (g : SO3) • x


instance SATO_action_on_R3: MulAction SATO R3 := inferInstance

lemma SATO_smul_def (g : SATO) (v : R3) :
  g • v = to_R3 (Matrix.mulVec (g.val : MAT) v.ofLp) := rfl
