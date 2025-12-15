import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Analysis.InnerProductSpace.PiL2

import BanachTarski.Common

set_option warningAsError false
set_option linter.all false

set_option maxHeartbeats 2000000

instance  R3_dim_3: Fact (Module.finrank ℝ R3 = 2 + 1) := by
  simp
  trivial

lemma s2_nonzero (ax: S2) : ax ≠ (0:R3) := by
  have ax_prop := ax.property
  simp only [S2] at ax_prop
  simp only [Metric.sphere] at ax_prop
  by_contra isz
  rw [isz] at ax_prop
  simp at ax_prop


noncomputable def ax_space (ax: S2): Submodule ℝ R3 := (ℝ ∙ ax.val)
noncomputable def orth (ax: S2): Submodule ℝ R3 := (ℝ ∙ ax.val)ᗮ

noncomputable def orth_B (ax : S2): OrthonormalBasis (Fin 2) ℝ (orth ax) :=
  OrthonormalBasis.fromOrthogonalSpanSingleton 2 (by exact s2_nonzero ax)

--protected def mk (hon : Orthonormal 𝕜 v) (hsp : ⊤ ≤ Submodule.span 𝕜 (Set.range v)) :
--    OrthonormalBasis ι 𝕜 E :=
noncomputable def ax_B (ax : S2): OrthonormalBasis (Fin 1) ℝ (ax_space ax) :=
  -- (There's gotta be a better way.)
  --theorem mem_span_of_mem {s : Set M} {x : M} (hx : x ∈ s) : x ∈ span R s := subset_span hx
  have ismem: ax.val ∈ ax_space ax := by
    apply Submodule.mem_span_of_mem
    simp
  let gen: ax_space ax := ⟨ax, ismem⟩
  let v: Fin 1 → (ax_space ax) := ![gen]
  let hon: Orthonormal ℝ v := by
    simp [Orthonormal]
    simp [v]
    simp [gen]

  let hsp: ⊤ ≤ Submodule.span ℝ (Set.range v) := by
    simp [v]
    simp [gen]
    rw [←Submodule.span_setOf_mem_eq_top]
    simp
    apply congrArg
    ext x
    constructor
    --
    intro lhs
    simp at lhs
    rw [lhs]
    rfl
    --
    intro lhs
    change (↑x) = (ax.val) at lhs
    simp
    exact Subtype.ext lhs


  OrthonormalBasis.mk hon hsp

noncomputable def plane_o (ax: S2): Orientation ℝ (orth ax) (Fin 2) := (orth_B ax).toBasis.orientation

instance  orth_dim_2 (ax: S2): Fact (Module.finrank ℝ (orth ax) = 2) := by
  apply fact_iff.mpr
  simp [orth]
  apply Submodule.finrank_orthogonal_span_singleton
  exact s2_nonzero ax



noncomputable def rot_iso_plane_equiv (ax: S2) (θ:ℝ) : (orth ax) ≃ₗᵢ[ℝ] (orth ax)  := (plane_o ax).rotation θ
noncomputable def rot_iso_plane_to_st (ax: S2) (θ:ℝ) : (orth ax) →ₗᵢ[ℝ] (orth ax)  :=
  (rot_iso_plane_equiv ax θ).toLinearIsometry

lemma triv_rot_inner (ax: S2): (rot_iso_plane_to_st ax 0) = 1 := by
  simp [rot_iso_plane_to_st]
  simp [rot_iso_plane_equiv]
  apply LinearIsometry.ext
  intro x
  simp

noncomputable def operp (ax: S2) (v: R3):= (orth ax).orthogonalProjection v
noncomputable def spar (ax: S2) (v: R3) := (ℝ ∙ ax.val).starProjection v

lemma operp_add (ax: S2) : operp ax (u + v) = (operp ax u) + (operp ax v) := sorry
lemma spar_add (ax: S2) : spar ax (u + v) = (spar ax u) + (spar ax v) := sorry

lemma operp_spar (ax: S2) : operp ax (spar ax v) = 0 := sorry
lemma spar_operp (ax: S2) : (spar ax (operp ax v)) = 0 := sorry
lemma spar_spar (ax: S2) : (spar ax (spar ax v)) = spar ax v := sorry

lemma spar_of_orth (ax: S2) (x: R3) : x ∈ orth ax → spar ax x = 0 := sorry
lemma spar_of_ax_space (ax: S2) (x: R3) : x ∈ ax_space ax → spar ax x = x := sorry
lemma operp_of_ax_space (ax: S2) (x: R3) : x ∈ ax_space ax → operp ax x = 0 := sorry

lemma rips_add (ax: S2) (v: orth ax): (rot_iso_plane_to_st ax S (rot_iso_plane_to_st ax T v)) =
  (rot_iso_plane_to_st ax (S + T) v) := sorry


noncomputable def up (ax:S2) := (Submodule.subtypeₗᵢ (orth ax))
lemma up_mem (ax: S2) (v: orth ax) : (up ax v) ∈ orth ax := sorry

noncomputable def operp_up (ax:S2) (v : orth ax) : operp ax ((up ax) v)  = v := sorry
lemma spar_up_rot (ax: S2) (v: orth ax) : spar ax ((up ax) v) = 0 := sorry



lemma el_by_parts (ax: S2) (x: R3):  x = ↑((operp ax x)) + spar ax x := by
  simp [operp, spar, orth]

noncomputable def ang_diff (axis: S2) (s t: R3) : Real.Angle :=
  (plane_o axis).oangle (operp axis s) (operp axis t)


noncomputable def rot_by_parts (ax: S2) (θ: ℝ):= fun v ↦ (
    (((up ax).comp (rot_iso_plane_to_st ax θ)) (operp ax v)) + (spar ax v)
  )

lemma triv_rot_by_parts (ax: S2): (rot_by_parts ax 0) = (id: R3 →R3) := by
  funext w
  simp [rot_by_parts]
  rw [triv_rot_inner]
  simp
  exact (el_by_parts ax w).symm



lemma rot_by_parts_comp (ax :S2) (θ τ: ℝ):
  rot_by_parts ax θ (rot_by_parts ax τ x) = rot_by_parts ax (θ + τ) x := by
    simp [rot_by_parts]
    simp [operp_add]
    simp [spar_add]
    simp [operp_up]
    simp [operp_spar]
    simp [spar_up_rot]
    simp [spar_spar]
    rw [rips_add]


noncomputable def rot_iso (ax: S2) (θ:ℝ) : R3 ≃ₗᵢ[ℝ] R3  := {
  toFun := rot_by_parts ax θ
  invFun := rot_by_parts ax (-θ)
  left_inv := by
    simp [Function.LeftInverse]
    intro x
    rw [rot_by_parts_comp]
    simp
    rw [triv_rot_by_parts]
    simp

  right_inv := by
    simp [Function.RightInverse]
    intro x
    rw [rot_by_parts_comp]
    simp
    rw [triv_rot_by_parts]
    simp

  map_add' := by
    intro x y
    simp [rot_by_parts, operp, spar]
    grind

  map_smul' := by
    intro m x
    simp [rot_by_parts, operp, spar]

  norm_map' := by
    intro x
    simp
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
    rw [Submodule.norm_sq_eq_add_norm_sq_projection  (rot_by_parts ax θ x) (orth ax)]
    rw [Submodule.norm_sq_eq_add_norm_sq_projection  x (orth ax)]
    have zero_lem1: (orth ax).starProjection (spar ax x) = 0 := by
      simp [orth, spar]
      have  idem :(Submodule.span ℝ {ax.val}).starProjection  ((Submodule.span ℝ {ax.val}).starProjection x)
        = ((Submodule.span ℝ {ax.val}).starProjection ) x := by
          apply Submodule.starProjection_eq_self_iff.mpr
          simp
      rw [idem]
      simp
    congr 1
    --
    apply congrArg (fun x ↦ x^2)
    simp [rot_by_parts]



    rw [zero_lem1]
    simp [operp]
    simp [up]
    simp [Submodule.norm_coe]
    --
    apply congrArg (fun x ↦ x^2)
    simp [rot_by_parts]
    rw [zero_lem1]
    simp
    simp [spar]
    congr 1
    simp [up]
    simp [orth]

}

lemma rot_iso_comp (ax :S2) (θ τ: ℝ):
  rot_iso ax θ (rot_iso ax τ x) = rot_iso ax (θ + τ) x := by sorry


lemma triv_rot_iso (ax: S2): rot_iso ax 0 = 1 := by
  have isidsym: (rot_iso ax 0) = (fun x: R3 ↦ x) := by
    funext w
    simp [rot_iso]
    simp [rot_by_parts]
    rw [triv_rot_inner]
    simp [up]
    exact (el_by_parts ax w).symm
  apply LinearIsometryEquiv.ext
  intro x
  rw [isidsym]
  simp


instance  orth_dim_3 : Fact (Module.finrank ℝ R3 = 3) := by
  simp
  trivial

noncomputable def Basis3: OrthonormalBasis (Fin 3) ℝ R3 :=
  (stdOrthonormalBasis ℝ R3).reindex <| finCongr orth_dim_3.out



/-- If a linear map `f : M₁ → M₂` respects direct sum decompositions of `M₁` and `M₂`, then it has a
block diagonal matrix with respect to bases compatible with the direct sum decompositions. -/
--lemma toMatrix_directSum_collectedBasis_eq_blockDiagonal' {R M₁ M₂ : Type*} [CommSemiring R]
--    [AddCommMonoid M₁] [Module R M₁] {N₁ : ι → Submodule R M₁} (h₁ : IsInternal N₁)
--    [AddCommMonoid M₂] [Module R M₂] {N₂ : ι → Submodule R M₂} (h₂ : IsInternal N₂)
--    {κ₁ κ₂ : ι → Type*} [∀ i, Fintype (κ₁ i)] [∀ i, Finite (κ₂ i)] [∀ i, DecidableEq (κ₁ i)]
--    [Fintype ι] (b₁ : (i : ι) → Basis (κ₁ i) R (N₁ i)) (b₂ : (i : ι) → Basis (κ₂ i) R (N₂ i))
--    {f : M₁ →ₗ[R] M₂} (hf : ∀ i, MapsTo f (N₁ i) (N₂ i)) :
--    toMatrix (h₁.collectedBasis b₁) (h₂.collectedBasis b₂) f =
--    Matrix.blockDiagonal' fun i ↦ toMatrix (b₁ i) (b₂ i) (f.restrict (hf i)) := by
--


def mod_dim: (Fin 2) → Type
  | ⟨0,_⟩ => Fin 2
  | ⟨1,_⟩ => Fin 1

instance mod_dim_fintype (i : Fin 2) : Fintype (mod_dim i) :=
  match i with
  | ⟨0, _⟩ => Fin.fintype 2
  | ⟨1, _⟩ => Fin.fintype 1

instance mod_dim_decidableEq (i : Fin 2) : DecidableEq (mod_dim i) :=
  match i with
  | ⟨0, _⟩ => by
    simp [mod_dim]
    exact instDecidableEqFin 2
  | ⟨1, _⟩ => by
    simp [mod_dim]
    exact instDecidableEqFin 1

noncomputable def submods (ax: S2): Fin 2 → Submodule ℝ R3 := ![orth ax, ax_space ax]

lemma internal_pr (ax: S2): DirectSum.IsInternal (submods ax):= by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  --
  have inter: (ax_space ax) ⊓ (orth ax)  = ⊥ := by
    simp [orth]
    simp [ax_space]
    exact (ax_space ax).inf_orthogonal_eq_bot

  simp [iSupIndep]
  constructor
  simp [Disjoint]
  intro x
  simp [submods]
  intro lhs
  intro lhs2
  apply le_iSup_iff.mp at lhs2
  have th:= lhs2 (ax_space ax)
  simp at th
  have bad:  x ≤ ⊥ := by
    rw [←inter]
    simp
    constructor
    --
    exact th
    exact lhs
  simpa using bad
  --
  simp [Disjoint]
  intro x
  simp [submods]
  intro lhs
  intro lhs2
  apply le_iSup_iff.mp at lhs2
  have th:= lhs2 (orth ax)
  simp at th
  have bad:  x ≤ ⊥ := by
    rw [←inter]
    simp
    constructor
    --
    exact lhs
    exact th
  simpa using bad

  --
  simp [iSup]
  simp [submods]
  simp [ax_space, orth]
  exact Submodule.sup_orthogonal_of_hasOrthogonalProjection



noncomputable def sm_bases (ax: S2) : (i : Fin 2) → (Module.Basis (mod_dim i) ℝ (submods ax i))
| ⟨0, _⟩ => (orth_B ax).toBasis
| ⟨1, _⟩ => (ax_B ax).toBasis


lemma hf (ax: S2): ∀ i, Set.MapsTo (rot_iso ax θ).toLinearMap (submods ax i) (submods ax i) := by
  intro i
  fin_cases i
  simp
  simp [submods]
  simp [rot_iso]
  simp [Set.MapsTo]
  simp [rot_by_parts]
  intro x
  intro lhs
  rw [spar_of_orth ax x lhs]
  simp
  exact up_mem ax ((rot_iso_plane_to_st ax θ) (operp ax x))
  --
  simp [Set.MapsTo]
  intro x
  intro lhs
  simp [submods]
  simp [submods] at lhs
  simp [rot_iso]
  simp [rot_by_parts]
  rw [operp_of_ax_space ax x lhs]
  simp
  have :_:= spar_of_ax_space ax x lhs
  rw [this]
  exact lhs








def BLOCK_MAT := Matrix ((i : Fin 2) × mod_dim i) ((i : Fin 2) × mod_dim i) ℝ

noncomputable def rot_mat_block (ax: S2) (θ:ℝ) : BLOCK_MAT :=
 (LinearMap.toMatrix
  ((internal_pr ax).collectedBasis (sm_bases ax))
  ((internal_pr ax).collectedBasis (sm_bases ax)))
  (rot_iso ax θ).toLinearEquiv


lemma rot_mat_block_prop (ax: S2) (θ:ℝ):
  rot_mat_block ax θ =
  Matrix.blockDiagonal'
  fun i ↦ LinearMap.toMatrix (sm_bases ax i) (sm_bases ax i) ((rot_iso ax θ).restrict (hf ax i)) := by

  exact LinearMap.toMatrix_directSum_collectedBasis_eq_blockDiagonal'
    (internal_pr ax) (internal_pr ax) (sm_bases ax) (sm_bases ax) (hf ax)




lemma rot_mat_is_special (ax : S2) (θ: ℝ): rot_mat ax θ ∈ SO3 := by
    rw [Matrix.mem_specialOrthogonalGroup_iff]
    constructor
    simp only [rot_mat]
    exact OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary
      (Basis3.map (rot_iso ax θ)) Basis3
    ---

    let mats (T: ℝ):= rot_mat ax T
    set M := mats θ with M_def
    --let maps (T:ℝ):  R3 →L[ℝ] R3  := LinearMap.toContinuousLinearMap (Matrix.toLin Basis3.toBasis Basis3.toBasis (mats T))
    let maps (T:ℝ) := (Matrix.toLin Basis3.toBasis Basis3.toBasis (mats T))


    have samedet: ∀ T:ℝ, (maps T).det = (mats T).det := by
      simp [mats, maps]
    rw [←samedet]

    have unitdet_lm  (T: ℝ) : (maps T).det = 1 ∨ (maps T).det = -1 := by
      rw [samedet]
      simp [mats]
      exact unitdet ax T

    sorry




noncomputable def rot (ax: S2) (θ:ℝ) : SO3 :=
  ⟨rot_mat ax θ, rot_mat_is_special ax θ⟩
