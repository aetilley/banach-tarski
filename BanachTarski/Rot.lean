import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Algebra.Group.Action.Defs
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

lemma el_by_parts (ax: S2) (x: R3):  x = ↑((operp ax x)) + spar ax x := by
  simp [operp, spar, orth]

noncomputable def ang_diff (axis: S2) (s t: R3) : Real.Angle :=
  (plane_o axis).oangle (operp axis s) (operp axis t)


noncomputable def rot_by_parts (ax: S2) (θ: ℝ):= fun v ↦ (
    (((Submodule.subtypeₗᵢ (orth ax)).comp (rot_iso_plane_to_st ax θ)) (operp ax v)) + (spar ax v)
  )

lemma triv_rot_by_parts (ax: S2): (rot_by_parts ax 0) = (id: R3 →R3) := by
  funext w
  simp [rot_by_parts]
  rw [triv_rot_inner]
  simp
  exact (el_by_parts ax w).symm


lemma rbp_lemma (ax: S2) (θ: ℝ) (x: R3): (rot_by_parts ax θ) x = ↑((rot_iso_plane_to_st ax θ) (operp ax x)) + spar ax x := by
  simp [rot_by_parts]

lemma rot_by_parts_comp (ax :S2) (θ τ: ℝ): rot_by_parts ax θ (rot_by_parts ax τ x) = rot_by_parts ax (θ + τ) x := sorry

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
    simp [Submodule.norm_coe]
    --
    apply congrArg (fun x ↦ x^2)
    simp [rot_by_parts]
    rw [zero_lem1]
    simp
    simp [spar]
    congr 1
    simp [orth]

}

instance  orth_dim_3 : Fact (Module.finrank ℝ R3 = 3) := by
  simp
  trivial

noncomputable def Basis3: OrthonormalBasis (Fin 3) ℝ R3 :=
  (stdOrthonormalBasis ℝ R3).reindex <| finCongr orth_dim_3.out


noncomputable def rot_mat (ax: S2) (θ:ℝ) : MAT :=
  let Lmap := (rot_iso ax θ)
  let M_obasis := Basis3.map Lmap
  M_obasis.toBasis.toMatrix Basis3.toBasis

lemma triv_rot_mat (ax: S2) : rot_mat ax 0 = 1 := sorry

lemma unitdet (ax: S2) (θ: ℝ)  :
  (rot_mat ax θ).det = 1 ∨ (rot_mat ax θ).det = -1 := by
  simp only [rot_mat]
  rw [←Module.Basis.det_apply]
  let T:= Basis3.map (rot_iso ax θ)
  have detlem: T.toBasis.det ⇑Basis3.toBasis  = (1:ℝ) ∨ T.toBasis.det ⇑Basis3.toBasis  = (-1:ℝ) :=
    OrthonormalBasis.det_to_matrix_orthonormalBasis_real T Basis3
  simpa [T] using detlem

instance R3funtop: TopologicalSpace (R3 →ₗ[ℝ] R3) := sorry
instance R3modtop: IsModuleTopology ℝ (R3 →ₗ[ℝ] R3) := sorry
instance contaddR3 : ContinuousAdd (R3 →ₗ[ℝ] R3) := sorry
instance mt2: IsModuleTopology ℝ (Matrix (Fin 3) (Fin 3) ℝ) := sorry

lemma rot_mat_is_special (ax : S2) (θ: ℝ): rot_mat ax θ ∈ SO3 := by
    rw [Matrix.mem_specialOrthogonalGroup_iff]
    constructor
    simp only [rot_mat]
    exact OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary
      (Basis3.map (rot_iso ax θ)) Basis3
    ---

    let mats (T: ℝ):= rot_mat ax T
    set M := mats θ with M_def
    let maps (T:ℝ):  R3 →L[ℝ] R3  := LinearMap.toContinuousLinearMap (Matrix.toLin Basis3.toBasis Basis3.toBasis (mats T))

    have samedet: ∀ T:ℝ, (maps T).det = (mats T).det := by
      simp [mats, maps]
    rw [←samedet]

    have unitdet_lm  (T: ℝ) : (maps T).det = 1 ∨ (maps T).det = -1 := by
      rw [samedet]
      simp [mats]
      exact unitdet ax T

    let map_det : (R3 →L[ℝ] R3) → ℝ := ContinuousLinearMap.det

    let case_map := maps θ

    change (ContinuousLinearMap.det case_map) = (1:ℝ)


    let clmdet: (R3 →L[ℝ] R3 )→ ℝ := ContinuousLinearMap.det

    let fcomp := clmdet ∘ maps
    have same: case_map.det = fcomp θ := by
      simp [fcomp]
      simp [case_map]
      simp [clmdet]

    rw [same]

    have cont_clmdet : Continuous clmdet := by exact ContinuousLinearMap.continuous_det

    have cont_mapper : Continuous maps := by
      simp [maps]
      let F1 : (R3 →ₗ[ℝ] R3) ≃ₗ[ℝ] R3 →L[ℝ] R3 := LinearMap.toContinuousLinearMap
      let F2 :_ := fun M ↦ (Matrix.toLin Basis3.toBasis Basis3.toBasis) M
      let F3 : ℝ → MAT := fun T ↦ mats T
      change Continuous (F1 ∘ F2 ∘ F3)
      have f1cont : Continuous F1 := by
        simp [F1]
        apply IsModuleTopology.continuous_of_linearMap

      have f2cont:  Continuous F2 := by
        simp [F2]
        apply IsModuleTopology.continuous_of_linearMap

      have f3cont: Continuous F3 := by
        simp [F3]
        simp [mats]
        simp [rot_mat]
        sorry



      exact f1cont.comp (f2cont.comp f3cont)



    have cont_fcomp: Continuous fcomp := by
      simp [fcomp]
      exact Continuous.comp cont_clmdet cont_mapper

    have posdet: fcomp 0 = 1 := by
      simp [fcomp]
      have izz: (maps 0) = (ContinuousLinearMap.id ℝ R3) := by
        simp [maps]
        simp [mats]
        rw [triv_rot_mat]
        simp
        rfl
      rw [izz]
      simp [clmdet, ContinuousLinearMap.det]



    have isunit: ∀θ:ℝ, fcomp θ = 1 ∨ fcomp θ = -1 := by
      simp [fcomp]
      simp only [clmdet]
      exact unitdet_lm


    by_contra bad
    have detcases: fcomp θ= 1 ∨ fcomp θ = -1 := by
      exact isunit θ
    have negdet: fcomp θ = -1 := by
      grind


    have hasmore: Set.Icc (fcomp θ) (fcomp 0) ⊆ Set.range fcomp :=
      (intermediate_value_univ θ 0) cont_fcomp

    rw [negdet, posdet] at hasmore
    have zeroin: (0:ℝ) ∈ (Set.Icc (-1) 1) := by simp
    have zeroin: (0:ℝ) ∈ Set.range fcomp:= hasmore zeroin
    simp at zeroin
    obtain ⟨τ, pτ⟩ := zeroin
    have :_:= isunit τ
    simp at this
    have :_:= isunit τ
    rw [pτ] at this
    simp at this


noncomputable def rot (ax: S2) (θ:ℝ) : SO3 :=
  ⟨rot_mat ax θ, rot_mat_is_special ax θ⟩
