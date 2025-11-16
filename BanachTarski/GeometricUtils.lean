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


  -- theorem aleph0_lt_continuum : ℵ₀ < 𝔠 :=
#check Cardinal.le_aleph0_iff_subtype_countable
#check Set.to_countable

def IccT := {x: ℝ // x ∈ (Set.Icc (0 : ℝ) (Real.pi/2 : ℝ))}

instance interval_uncountable : Uncountable IccT := by
  by_contra notunc
  have type_countable:_ := not_uncountable_iff.mp notunc
  have icc_countable :_:= Set.countable_coe_iff.mp type_countable
  have bad :_ := Cardinal.Real.Icc_countable_iff.mp icc_countable
  linarith [Real.pi_pos]

noncomputable def to_s2_r3: IccT → R3 := fun θ ↦ to_R3 ![Real.cos θ.val, Real.sin θ.val, 0]

def is_s2 (θ : IccT) : to_s2_r3 θ ∈ S2 := by
  simp [to_s2_r3]
  simp [S2]
  simp [to_R3]
  simp [norm]
  norm_num
  rw [Fin.sum_univ_three]
  norm_num
  simp


noncomputable def to_s2: IccT → S2 := fun θ ↦ ⟨to_s2_r3 θ, is_s2 θ⟩

lemma ih : Function.Injective to_s2 := by
  simp [Function.Injective]
  intro a b haeqhb
  simp [to_s2, to_s2_r3] at haeqhb
  simp [to_R3] at haeqhb
  have ios:_:= Real.injOn_sin
  simp [Set.InjOn] at ios
  have ap:_ := a.property
  have bp:_ := b.property
  simp only [Set.Icc] at ap
  have c1 :_:= (Set.mem_setOf.mp ap).left
  have c2 :_:= (Set.mem_setOf.mp ap).right
  have c1 :_:= (Set.mem_setOf.mp bp).left
  have c2 :_:= (Set.mem_setOf.mp bp).right
  have a1: -(Real.pi / 2) ≤ a.val := by linarith
  have a2: a.val ≤ (Real.pi / 2)  := by linarith
  have b1: -(Real.pi / 2) ≤ b.val := by linarith
  have b2: b.val ≤ (Real.pi / 2)  := by linarith
  exact Subtype.ext (ios a1 a2 b1 b2 haeqhb.right)

lemma s2_uncountable: Uncountable (S2) := by
  apply Function.Injective.uncountable ih

lemma lb_card_s2 : Cardinal.aleph0 < Cardinal.mk S2 := Cardinal.aleph0_lt_mk_iff.mpr s2_uncountable

lemma identity_matrix_mem_SO3 : (1 : MAT) ∈ SO3 := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  constructor
  · rw [Matrix.mem_orthogonalGroup_iff]
    simp [Matrix.transpose_one]
  · simp [Matrix.det_one]


lemma so3_fixes_norm: ∀g : SO3, ∀x : R3, ‖g • x‖ = ‖x‖ := sorry
lemma so3_fixes_s2: ∀g : SO3, (f g) '' S2 ⊆ S2 := sorry



def tspace_full := R3 →ₗ[ℝ] R3
def tspace := R3_raw →ₗ[ℝ] R3_raw

lemma fixed_lemma (g: SO3) : Nat.card ({x ∈ S2 | g • x = x}) = 2 := by
  let gmap: tspace := Matrix.toLin' g
  -- sketch
  -- have _: {x : R3_raw | g • x = x} = (LinearMap.ker (gmap-(1: tspace))).carrier :=
  -- have _: Module.finrank ℝ (LinearMap.ker (gmap-(1: tspace))) = 1 :=
  -- have _: ∃v: R3_raw, LinearMap.ker (gmap - 1 : tspace) = {x | ∃s:ℝ,  x = s • v} :=
  sorry


def K_mat (a: R3): MAT := !![
  0, -(a 2), (a 1);
  (a 2), 0, -(a 0);
  -(a 1), (a 0), 0;
]

-- Rodrigues' formula for the rotation matrix :  I + (sin θ)K + (1-cosθ)K²
noncomputable def rot_mat (ax: S2) (θ:ℝ) : MAT := (1:MAT) + (Real.sin θ)•(K_mat ax) + (1 - Real.cos θ)•((K_mat ax) ^ 2)

noncomputable def rot (ax: R3) (θ:ℝ) : SO3 := by
  -- First normalize the axis to be on S2
  let ax_norm := (1 / ‖ax‖) • ax
  have ax_norm_mem_S2 : ax_norm ∈ S2 := sorry  -- Need to prove normalization gives unit vector
  let M := rot_mat ⟨ax_norm, ax_norm_mem_S2⟩ θ
  -- Now prove M ∈ SO3 using the systematic approach:
  refine ⟨M, ?_⟩
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  constructor
  · rw [Matrix.mem_orthogonalGroup_iff]
    -- M * Mᵀ = 1
    sorry
  · -- M.det = 1
    sorry

lemma rot_lemma: ∀ {axis : R3} {θ:ℝ}, (f (rot axis θ)) '' S2 ⊆ S2 := sorry


def ToEquivSO3 (g: SO3) : R3 ≃ R3 := sorry
  -- Matrix.toLin'...

def isIsoSO3 (g: SO3) (y: R3 ≃ R3) : Isometry (y) := sorry

  -- Matrix.toLin'...

-- Group of Isometries of R3.
abbrev G3: Type := R3 ≃ᵢ R3
-- The standard action given by matrix multiplication.
instance : MulAction G3 R3 where
  smul g v := g v
  one_smul v := by
    have lem : (1:G3) v = v := by
      rw [IsometryEquiv.coe_one]
      simp
    exact lem
  mul_smul x y v := by
    have lem: (y.trans x) v = x (y v) := by simp
    exact lem


def orbit {X : Type*} {G: Type*} [Group G] [MulAction G X] (g: G) (S: Set X): Set X :=
⋃ i, (f g)^[i] '' S


def SO3_in_G3_carrier: Set G3 := {⟨y, is_iso⟩ | ∃g: SO3,  y = ToEquivSO3 g ∧ is_iso = (isIsoSO3 g y)}
def SO3_in_G3: Subgroup G3 := sorry

def SO3_into_G3: SO3 ≃* SO3_in_G3 := sorry

def SO3_G3_action_equiv : (∀x: R3, ∀g : SO3, (SO3_into_G3 g) • x  = g • x) := sorry

noncomputable def normed:  R3 → R3 := fun x ↦ (1 / ‖x‖) • x

def B3: Set R3 := Metric.closedBall (0: R3) 1
def B3min: Set R3 := B3 \ {0}

def S2_sub := {S : Set R3 // S ⊆ S2}
def cone (S: S2_sub) := {x : R3 | ∃ (s : ℝ) (v : R3), (x = s • v) ∧ (v ∈ S.val) ∧ (0 < s)}
def trunc_cone (S: S2_sub) := cone S ∩ B3

lemma b3min_is_trunc_cone_s2 : B3min = trunc_cone ⟨S2, by simp⟩ := by
  ext x
  constructor
  intro xinb3min
  simp [trunc_cone]
  constructor
  simp [B3min, B3] at xinb3min
  use ‖x‖, ‖x‖⁻¹ • x
  constructor
  rw [smul_inv_smul₀]
  by_contra znorm
  simp at znorm
  exact xinb3min.right znorm


  constructor
  simp [S2]
  simp [norm_smul]
  apply inv_mul_cancel₀
  by_contra zeronorm
  simp at zeronorm
  exact xinb3min.right zeronorm
  --
  by_contra bad
  simp at bad
  exact xinb3min.right bad
  exact xinb3min.left
  --

  intro xintcone
  simp [B3min, B3]
  simp [trunc_cone] at xintcone
  obtain ⟨s, v, psv⟩ := xintcone.left
  rw [psv.left]
  simp [norm_smul]

  have nveq1: ‖v‖ = 1 := by
    by_contra notone
    have bad: _:= psv.right.left
    simp [S2] at bad
    absurd notone bad
    trivial

  rw [nveq1]
  simp
  constructor
  apply abs_le.mpr
  constructor
  linarith
  simp [B3] at xintcone
  rw [psv.left] at xintcone
  simp [norm_smul] at xintcone
  rw [nveq1] at xintcone
  simp at xintcone
  apply le_of_abs_le
  exact xintcone.right
  --
  constructor
  by_contra sz
  rw [sz] at psv
  simp at psv
  by_contra eqz
  rw [eqz] at nveq1
  simp at nveq1


lemma trunc_cone_sub_ball (S: S2_sub) : trunc_cone S ⊆ B3min  := by
  simp [trunc_cone]
  rintro x ⟨xinl, xinr⟩
  simp [B3min]
  constructor
  exact xinr
  simp [cone] at xinl
  obtain ⟨s,v, psv⟩ := xinl
  by_contra xzero
  rw [xzero] at psv
  have  sprop:_:= S.prop
  have :_:=sprop psv.right.left
  simp [S2] at this
  have bad:_:= eq_zero_or_eq_zero_of_smul_eq_zero (psv.left).symm
  rcases bad with sb | vb
  linarith
  rw [vb] at this
  simp at this


lemma cone_lemma (S : S2_sub) : ∀ x : R3, x ∈ cone S ↔ (normed x ∈ S.val) := by
  intro x
  constructor
  intro lhs
  simp [cone] at lhs
  obtain ⟨s, v, psv⟩ := lhs
  simp [normed]
  have nveq1: ‖v‖ = 1 := by
    by_contra notone
    have bad: _:= S.prop psv.right.left
    simp [S2] at bad
    absurd notone bad
    trivial

  have isv: ‖x‖⁻¹ • x = v := by
    rw [psv.left]
    simp [norm_smul]
    rw [nveq1]
    simp
    simp [abs_of_pos psv.right.right]
    apply inv_smul_smul₀
    linarith
  rw [isv]
  exact psv.right.left
  --

  intro normed_in_S
  have normnotzero: ‖x‖ ≠ 0 := by
    by_contra iszero
    simp [normed] at normed_in_S
    rw [iszero] at normed_in_S
    simp at normed_in_S
    have sprop:_:= S.prop
    have bad:_:=sprop normed_in_S
    simp [S2] at bad
  simp [cone]
  simp [normed] at normed_in_S
  use ‖x‖, ‖x‖⁻¹ • x
  constructor
  rw [smul_inv_smul₀]
  exact normnotzero
  constructor
  exact normed_in_S
  by_contra bad
  simp at bad
  rw [bad] at normnotzero
  simp at normnotzero

lemma trunc_cone_lemma (S : S2_sub) : ∀ x : R3, x ∈ trunc_cone S → (normed x ∈ S.val) := by
  intro x
  intro lhs
  have: x ∈ cone S := by
    simp [trunc_cone] at lhs
    exact lhs.left
  exact (cone_lemma S x).mp this



lemma disj_lemma (n: ℕ) (fam: Fin n → S2_sub)
(disj: ∀ (i j : Fin n), i ≠ j → Disjoint (fam i).val (fam j).val) :
∀ (i j : Fin n), i ≠ j → Disjoint (trunc_cone (fam i)) (trunc_cone (fam j)) := by
    intro i j inej
    apply Set.disjoint_iff.mpr
    intro x ⟨xini, xinj⟩
    simp
    have badi: normed x ∈ (fam i).val := by
      exact (trunc_cone_lemma ( fam i) x) xini
    have badj: normed x ∈ (fam j).val := by
      exact (trunc_cone_lemma ( fam j) x) xinj
    exact (Set.disjoint_iff.mp (disj i j inej)) ⟨badi, badj⟩

lemma cover_lemma (n: ℕ) (fam: Fin n → S2_sub) (T : S2_sub)
(cover: (⋃ i, (fam i).val) = T.val): (⋃ i, trunc_cone (fam i)) = trunc_cone T:= by
  ext x
  constructor
  --
  intro xincones
  simp at xincones
  obtain ⟨i, pi⟩ := xincones
  have lem : normed x ∈ (fam i).val := (trunc_cone_lemma (fam i) x) pi
  by_contra xnitct
  have small:  ‖x‖ ≤ 1 := by
    simp [trunc_cone] at pi
    simp [B3] at pi
    exact pi.right
  have noteven:  x ∉ cone T := by
    by_contra xincone
    have inb3: x∈ B3 := by simp [B3]; exact small
    exact xnitct ⟨xincone, inb3⟩
  have bad: (normed x) ∉ T.val := by
    by_contra nx_in_tval
    exact noteven ((cone_lemma T x).mpr nx_in_tval)
  rw [←cover] at bad
  rw [Set.mem_iUnion] at bad
  simp at bad
  exact (bad i) lem
  --

  intro xincone
  simp [trunc_cone] at xincone
  have intval: normed x ∈ T.val := (trunc_cone_lemma T x) xincone
  rw [←cover] at intval; simp at intval
  obtain ⟨i, pi⟩ := intval
  have piece : x ∈ cone (fam i) := by exact (cone_lemma (fam i) x).mpr pi
  have piece_t: x ∈ trunc_cone (fam i) := ⟨piece, xincone.right⟩
  simp
  use i


instance : SMulCommClass ℝ (↥SO3) R3 where
  smul_comm:  ∀ (m : ℝ) (n : SO3) (a : R3), m • n • a = n • m • a := by sorry

lemma map_lemma (n: ℕ) (map: Fin n -> SO3) (famA: Fin n → S2_sub) (famB: Fin n → S2_sub)
(map_prop: ∀ (i: Fin n), f (map i)'' (famA i).val = (famB i).val) :
∀ (i: Fin n), f (map i) '' trunc_cone (famA i) = trunc_cone (famB i)  := by
  intro i
  have tops:_ :=map_prop i

  ext x
  constructor
  intro xinmi
  simp [trunc_cone]
  simp [cone]
  simp [trunc_cone] at xinmi
  simp [cone] at xinmi
  obtain ⟨s, v, psv⟩ := xinmi
  constructor
  use s
  use f (map i) v
  constructor
  simp [f]
  simp [f] at psv
  rw [smul_comm]
  exact psv.right.symm
  --

  constructor
  rw [←tops]
  apply (Set.mem_image (f (map i)) (famA i).val (f (map i) v)).mpr
  use v
  constructor
  exact psv.left.left.left
  rfl
  exact psv.left.left.right
  simp [B3]
  rw [←psv.right]
  simp [f]
  rw [so3_fixes_norm]
  simp [B3] at psv
  exact psv.left.right

  --
  intro xinpiece
  simp [trunc_cone, cone]
  simp [trunc_cone, cone] at xinpiece
  obtain ⟨s, w, psw ⟩ := xinpiece.left
  use s

  use f (map i)⁻¹ w
  simp [f]
  constructor
  constructor
  constructor
  rw [←tops] at psw
  have this: w ∈ f (map i) '' (famA i).val := psw.right.left
  exact Set.mem_smul_set_iff_inv_smul_mem.mp this
  --
  exact psw.right.right
  --
  have cm:  s • (map i)⁻¹ • w = (map i)⁻¹ • s • w := smul_comm s (map i)⁻¹ w
  rw [cm]
  simp [B3]
  rw [so3_fixes_norm ((map i)⁻¹) (s • w)]
  rw [←psw.left]
  simp [B3] at xinpiece
  exact xinpiece.right
  --
  rw [smul_comm s]
  simp
  exact psw.left.symm


-- The rotation around a line through (0,0,.5) in the x z plane parallel to the x-axis.
noncomputable def axis_rot (axis: R3): ℝ -> SO3 := (fun θ ↦ rot axis θ)
def skew_rot (θ: ℝ): G3 := sorry

def Bad {X : Type*} {G: Type*} [Group G] [MulAction G X] (F: ℝ → G) (S: Set X): Set ℝ :=
{θ: ℝ | ∃n:ℕ, n > 0 ∧ ∃s∈S, (f (F θ))^[n] s ∈ S}

lemma countable_bad_rots: ∀S: Set R3, ∀ axis:R3, S ⊆ S2 ∧ Countable S → Countable (Bad (axis_rot axis) S) := sorry
lemma countable_bad_skew_rot: Countable (Bad skew_rot {origin}) := sorry

lemma srot_containment: ∀r:ℝ, orbit (skew_rot r) {origin} ⊆ B3 :=sorry
