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

lemma unitdet (ax: S2) (θ: ℝ)  :
  (rot_mat ax θ).det = 1 ∨ (rot_mat ax θ).det = -1 := by
  simp only [rot_mat]
  rw [←Module.Basis.det_apply]
  let T:= Basis3.map (rot_iso ax θ)
  have detlem: T.toBasis.det ⇑Basis3.toBasis  = (1:ℝ) ∨ T.toBasis.det ⇑Basis3.toBasis  = (-1:ℝ) :=
    OrthonormalBasis.det_to_matrix_orthonormalBasis_real T Basis3
  simpa [T] using detlem


lemma rot_mat_is_special (ax : S2) (θ: ℝ): rot_mat ax θ ∈ SO3 := by
    rw [Matrix.mem_specialOrthogonalGroup_iff]
    constructor
    simp only [rot_mat]
    exact OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary
      (Basis3.map (rot_iso ax θ)) Basis3
    ---

    --
    --theorem OrthonormalBasis.det_to_matrix_orthonormalBasis_real :
    --  a.toBasis.det b = 1 ∨ a.toBasis.det b = -1 := by
    --have rot_det: LinearMap.det (rot_iso_plane_to_st ax θ).toLinearMap = (1 : ℝ) := by
    --  simp [rot_iso_plane_to_st]
    --  simp [rot_iso_plane_equiv]
    --  exact (plane_o ax).det_rotation θ



    let map := Matrix.toLin Basis3.toBasis Basis3.toBasis M
    have samedet: map.det = M.det := by
      simp [M, map]

    rw [←samedet]




noncomputable def rot (ax: S2) (θ:ℝ) : SO3 :=
  ⟨rot_mat ax θ, rot_mat_is_special ax θ⟩







    #check Module.Basis.det_map
    #check LinearMap.det_toMatrix

    --

    --
    -- If `q` is a complement of `p`, then `p × q` is isomorphic to `E`. -/
    -- def prodEquivOfIsCompl (h : IsCompl p q) : (p × q) ≃ₗ[R] E := by
    #check Submodule.prodEquivOfIsCompl

    #check LinearMap.det_prodMap
    #check LinearMap.IsProj.eq_conj_prodMap
    sorry






  ⟨M, M_is_special⟩
