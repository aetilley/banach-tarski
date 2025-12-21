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
instance  orth_dim_2 (ax: S2): Fact (Module.finrank ℝ (orth ax) = 2) := by
  apply fact_iff.mpr
  simp [orth]
  apply Submodule.finrank_orthogonal_span_singleton
  exact s2_nonzero ax

def choice_set (ax :S2): Set (orth ax) := {x: (orth ax) | x ≠ 0}

lemma orth_nonempty (ax: S2): ∃ y, y∈ (choice_set ax) := by
  by_contra bad
  simp at bad
  simp [choice_set] at bad
  have isbot_orth: (orth ax) = ⊥ := by exact (Submodule.eq_bot_iff (orth ax)).mpr bad
  have istop_ax : (ax_space ax) = ⊤ := by
    exact Submodule.orthogonal_eq_bot_iff.mp isbot_orth
  simp [ax_space] at istop_ax
  apply congrArg (fun S: (Submodule ℝ R3) ↦ Module.finrank ℝ S) at istop_ax
  simp at istop_ax
  set gen : Set R3 := {ax.val}
  have : (Module.finrank ℝ  (Submodule.span ℝ gen)) ≤ gen.toFinset.card  := finrank_span_le_card gen
  rw [istop_ax] at this
  simp [gen] at this



noncomputable def x_B_c (ax : S2): choice_set ax :=
  ⟨Classical.choose (orth_nonempty ax), Classical.choose_spec (orth_nonempty ax)⟩

noncomputable def x_B (ax : S2): (orth ax) :=
  let nr:= 1/ ‖(x_B_c ax).val‖
  nr • ((x_B_c ax).val)

lemma x_B_nz (ax: S2) : (x_B ax) ≠ 0 := by
  let nr:= 1/ ‖(x_B_c ax).val‖
  change nr • (x_B_c ax).val ≠ 0
  let prop := (x_B_c ax).property
  simp only [choice_set] at prop
  by_contra bad
  simp at bad
  rcases bad with c1 | c2
  --
  simp [nr] at c1
  rw [c1] at prop
  simp at prop

  rw [c2] at prop
  simp at prop



-- Not sure if this is optimal, to get our rightAnglerotation basis below, we need
-- an orientation, and to get an orientation we seem to need a basis.
noncomputable def tmp_basis (ax : S2): OrthonormalBasis (Fin 2) ℝ (orth ax) :=
  OrthonormalBasis.fromOrthogonalSpanSingleton 2 (by exact s2_nonzero ax)

noncomputable def plane_o (ax: S2): Orientation ℝ (orth ax) (Fin 2) := (tmp_basis ax).toBasis.orientation


noncomputable def orth_B (ax : S2): Module.Basis (Fin 2) ℝ (orth ax) :=
  (plane_o ax).basisRightAngleRotation (x_B ax) (x_B_nz ax)

noncomputable def ax_B (ax : S2): Module.Basis (Fin 1) ℝ (ax_space ax) :=
  have ismem: ax.val ∈ ax_space ax := by
    apply Submodule.mem_span_of_mem
    simp
  let gen: ax_space ax := ⟨ax, ismem⟩
  let v: Fin 1 → (ax_space ax) := ![gen]
  let hon: LinearIndependent ℝ v := by
    simp
    have :_:= ax.property
    simp only [S2] at this
    simp only [Metric.sphere] at this
    simp [v]
    simp [gen]
    by_contra bad
    rw [bad] at this
    simp at this

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


  Module.Basis.mk hon hsp

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

lemma operp_add (ax: S2) : operp ax (u + v) = (operp ax u) + (operp ax v) := by
  simp [operp]

lemma spar_add (ax: S2) : spar ax (u + v) = (spar ax u) + (spar ax v) := by
  simp [spar]


lemma operp_spar (ax: S2) : operp ax (spar ax v) = 0 := by
  simp [operp, spar]
  simp [orth]

lemma spar_spar (ax: S2) : (spar ax (spar ax v)) = spar ax v := by
  simp [spar]
  set V := (Submodule.span ℝ {ax.val}).starProjection v with vdef
  have : (Submodule.span ℝ {ax.val}).starProjection V = V :=by
    apply Submodule.starProjection_eq_self_iff.mpr
    rw [vdef]
    simp
  exact this

lemma spar_operp (ax: S2) : (spar ax (operp ax v)) = 0 := by
  simp [operp]
  simp [orth]
  simp [spar]
  set V := (Submodule.span ℝ {ax.val}).starProjection v with vdef
  have : (Submodule.span ℝ {ax.val}).starProjection V = V :=by
    apply Submodule.starProjection_eq_self_iff.mpr
    rw [vdef]
    simp
  simp [this]


lemma spar_of_orth (ax: S2) (x: R3) : x ∈ orth ax → spar ax x = 0 := by
  intro lhs
  simp [orth] at lhs
  simp [spar]
  apply (Submodule.starProjection_apply_eq_zero_iff (Submodule.span ℝ {ax.val})).mpr
  exact lhs



lemma spar_of_ax_space (ax: S2) (x: R3) : x ∈ ax_space ax → spar ax x = x := by
  simp [ax_space, spar]
  intro lhs
  have := Submodule.mem_span_singleton.mp lhs
  obtain ⟨a, pa⟩ := this
  rw [←pa]
  simp
  apply congrArg
  apply Submodule.starProjection_eq_self_iff.mpr
  simp


lemma operp_of_ax_space (ax: S2) (x: R3) : x ∈ ax_space ax → operp ax x = 0 := by
  simp [ax_space, operp]
  intro lhs
  simp [orth]
  exact lhs

lemma rips_add (ax: S2) (v: orth ax):
  (rot_iso_plane_to_st ax S (rot_iso_plane_to_st ax T v)) =
  (rot_iso_plane_to_st ax (S + T) v) := by
  simp [rot_iso_plane_to_st, rot_iso_plane_equiv]


noncomputable def up (ax:S2) := (Submodule.subtypeₗᵢ (orth ax))
lemma up_mem (ax: S2) (v: orth ax) : (up ax v) ∈ orth ax := by
  simp [up]


lemma operp_up (ax:S2) (v : orth ax) : operp ax ((up ax) v)  = v := by
  simp [up, operp]


lemma operp_up_2 (ax:S2) (v : orth ax) : operp ax (↑v)  = v := by
  simp [operp]

lemma spar_up_2 (ax: S2) (v: orth ax) : spar ax (↑v) = 0 := by
  have : ↑v ∈ orth ax := by simp
  exact spar_of_orth ax v this


lemma spar_up_rot (ax: S2) (v: orth ax) : spar ax ((up ax) v) = 0 := by
  simp only [up]
  have vinorth : (((orth ax).subtypeₗᵢ) v) ∈ (orth ax) := by
    simp
  have := spar_of_orth ax ((orth ax).subtypeₗᵢ v) vinorth
  exact this


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
  rot_iso ax θ (rot_iso ax τ x) = rot_iso ax (θ + τ) x := by
  simp [rot_iso]
  simp [rot_by_parts_comp]



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

noncomputable def Basis3: OrthonormalBasis (Fin 3) ℝ R3 := EuclideanSpace.basisFun (Fin 3) ℝ

----------------
-- The following blockDiagonal results are unused.  I was hopeful that I could use this
-- to show that my rot_mat below was correct but I'm having a hell of a time unpacking
-- these the resulting block matrices.

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
| ⟨0, _⟩ => (orth_B ax)
| ⟨1, _⟩ => (ax_B ax)


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



def PROD_BLOCK := Matrix ((i : Fin 2) × mod_dim i) ((i : Fin 2) × mod_dim i) ℝ


noncomputable def rot_mat_block_1 (ax: S2) (θ:ℝ) : PROD_BLOCK :=
 (LinearMap.toMatrix
  ((internal_pr ax).collectedBasis (sm_bases ax))
  ((internal_pr ax).collectedBasis (sm_bases ax)))
  (rot_iso ax θ).toLinearEquiv



noncomputable def rot_mat_block_2 (ax: S2) (θ:ℝ) : PROD_BLOCK:=
  Matrix.blockDiagonal'
  fun i ↦ LinearMap.toMatrix (sm_bases ax i) (sm_bases ax i) ((rot_iso ax θ).restrict (hf ax i))


lemma rot_mat_block_prop (ax: S2) (θ:ℝ): rot_mat_block_1 ax θ = rot_mat_block_2 ax θ := by
  simp [rot_mat_block_1, rot_mat_block_2]
  exact LinearMap.toMatrix_directSum_collectedBasis_eq_blockDiagonal'
    (internal_pr ax) (internal_pr ax) (sm_bases ax) (sm_bases ax) (hf ax)



lemma block_1_lem (ax: S2) :
  LinearMap.toMatrix (sm_bases ax 0) (sm_bases ax 0) ((rot_iso ax θ).restrict (hf ax 0)) =
  !![θ.cos, -θ.sin; θ.sin, θ.cos]  := by

  have restr_lem: (rot_iso ax θ).restrict (hf ax 0) =
    (rot_iso_plane_to_st ax θ).toLinearMap := by

    apply LinearMap.ext
    intro x
    simp [submods] at x
    simp [rot_iso_plane_to_st]
    simp [rot_iso_plane_equiv]
    simp [rot_iso]
    rw [LinearMap.restrict_apply]
    simp
    simp [rot_by_parts]
    simp [spar_up_2]
    simp [rot_iso_plane_to_st]
    simp [rot_iso_plane_equiv]
    simp [up]
    simp [operp_up_2]
    rfl

  rw [restr_lem]
  simp [sm_bases]
  simp [rot_iso_plane_to_st]
  simp [rot_iso_plane_equiv]

  let x: (orth ax) := x_B ax
  have hx: x≠ 0 := x_B_nz ax

  have inter:  ((plane_o ax).rotation θ).toLinearIsometry.toLinearMap =
    Matrix.toLin
      ((plane_o ax).basisRightAngleRotation x hx)
      ((plane_o ax).basisRightAngleRotation x hx)
      !![θ.cos, -θ.sin; θ.sin, θ.cos] := (plane_o ax).rotation_eq_matrix_toLin θ hx

  have sameorth: (orth_B ax) = ((plane_o ax).basisRightAngleRotation x hx ) := by
    simp [orth_B]
    simp [x]

  rw [sameorth]
  rw [inter]
  set B:= ((plane_o ax).basisRightAngleRotation x hx) with Bdef
  set R:= !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]
  exact LinearMap.toMatrix_toLin B B R

lemma block_2_lem (ax: S2) :
  LinearMap.toMatrix (sm_bases ax 1) (sm_bases ax 1) ((rot_iso ax θ).restrict (hf ax 1)) = !![1;] := by

  have restr_lem: (rot_iso ax θ).restrict (hf ax 1) = 1 := by
    apply LinearMap.ext
    simp [submods]
    intro x
    intro px
    rw [LinearMap.restrict_apply]
    simp [rot_iso]
    simp [rot_by_parts]
    simp [up]
    rw [spar_of_ax_space ax x px]
    rw [operp_of_ax_space ax x px]
    simp


  rw [restr_lem]
  simp [sm_bases]
  ext i j
  fin_cases i, j
  simp

------------

lemma block_repr (ax: S2) (θ : ℝ) :
   (LinearMap.toMatrix
  ((internal_pr ax).collectedBasis (sm_bases ax))
  ((internal_pr ax).collectedBasis (sm_bases ax)))
  (rot_iso ax θ).toLinearMap
  =
  Matrix.blockDiagonal' (fun i ↦
  match i with
  | ⟨0, _⟩ =>  !![θ.cos, -θ.sin; θ.sin, θ.cos]
  | ⟨1, _⟩ =>  !![1;]
  ) := by
  have :_:=rot_mat_block_prop (ax: S2) (θ:ℝ)
  simp [rot_mat_block_1] at this
  simp [rot_mat_block_2] at this
  have eq_funs: (fun i ↦ (LinearMap.toMatrix (sm_bases ax i) (sm_bases ax i)) (((rot_iso ax θ).toLinearEquiv).restrict (hf ax i)))
    = (fun i ↦ match i with
      | ⟨0, _⟩ => (LinearMap.toMatrix (sm_bases ax 0) (sm_bases ax 0)) (((rot_iso ax θ).toLinearEquiv).restrict (hf ax 0))
      | ⟨1, _⟩ => (LinearMap.toMatrix (sm_bases ax 1) (sm_bases ax 1)) (((rot_iso ax θ).toLinearEquiv).restrict (hf ax 1))
    ) := by
    funext w
    fin_cases w
    simp
    simp

  rw [eq_funs] at this

  rw [block_1_lem] at this
  rw [block_2_lem] at this

  exact this



---------

noncomputable def rot_mat_inner (ax: S2) (θ:ℝ) : MAT :=
    !![
      θ.cos, -θ.sin, 0;
      θ.sin, θ.cos, 0;
      0, 0, 1;
    ]

noncomputable def rot_mat_inner_trans (ax: S2) (θ:ℝ) : MAT :=
    !![
      θ.cos, θ.sin, 0;
      -θ.sin, θ.cos, 0;
      0, 0, 1;
    ]

lemma rmi_trans_equiv (ax: S2) (θ: ℝ) :
(rot_mat_inner ax θ).transpose = (rot_mat_inner_trans ax θ) := by
  simp [rot_mat_inner, rot_mat_inner_trans]
  ext i j
  fin_cases i, j
  <;> simp



lemma rot_mat_inner_is_special (ax:S2) (θ: ℝ) : rot_mat_inner ax θ ∈ SO3 := by
  apply Matrix.mem_specialOrthogonalGroup_iff.mpr
  constructor
  rw [Matrix.mem_orthogonalGroup_iff]
  rw [rmi_trans_equiv]
  simp only [rot_mat_inner, rot_mat_inner_trans]
  rw [Matrix.mul_fin_three]
  simp
  repeat  rw [←sq]
  rw [Real.sin_sq_add_cos_sq θ]
  rw [add_comm (Real.cos θ ^ 2)]
  rw [Real.sin_sq_add_cos_sq θ]
  rw [mul_comm]
  simp
  rw [Matrix.one_fin_three]
  -----
  --
  simp [rot_mat_inner]
  rw [Matrix.det_fin_three]
  simp
  repeat  rw [←sq]
  rw [add_comm]
  exact Real.sin_sq_add_cos_sq θ


def COB (ax: S2) : OrthonormalBasis (Fin 3) ℝ R3 := sorry

noncomputable def COB_mat (ax: S2) : MAT := LinearMap.toMatrix Basis3.toBasis (COB ax).toBasis 1

lemma cob_mat_other_repr (ax: S2): COB_mat ax = (COB ax).toBasis.toMatrix Basis3 := by
  simp [COB_mat]
  exact LinearMap.toMatrix_id_eq_basis_toMatrix Basis3.toBasis (COB ax).toBasis

lemma COB_mat_is_ortho (ax:S2) : COB_mat ax ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [cob_mat_other_repr ax]
  apply OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary


noncomputable def rot_mat (ax: S2) (θ:ℝ) : MAT :=
  let cob := COB_mat ax
  cob⁻¹ * (rot_mat_inner ax θ) * cob


lemma rot_mat_is_special(ax: S2) (θ:ℝ) : rot_mat ax θ ∈ SO3 := by
  simp [rot_mat]
  have innerspecial := Matrix.mem_specialOrthogonalGroup_iff.mp (rot_mat_inner_is_special ax θ)
  apply Matrix.mem_specialOrthogonalGroup_iff.mpr
  have cob_is_orth: (COB_mat ax ) ∈ Matrix.orthogonalGroup (Fin 3) ℝ := COB_mat_is_ortho ax
  constructor
  apply mul_mem
  apply mul_mem

  have pprop := (⟨(COB_mat ax), cob_is_orth⟩:Matrix.orthogonalGroup (Fin 3) ℝ )⁻¹.property
  rw [←unitary_invs_coe ] at pprop
  simpa using pprop
  ---
  exact innerspecial.left
  --
  exact cob_is_orth
  --
  simp
  rw [mul_comm]
  rw [←mul_assoc]
  have : Matrix.det (COB_mat ax) * (Matrix.det (COB_mat ax))⁻¹ = 1 := by
    apply mul_inv_cancel₀
    have:  (COB_mat ax).det = 1 ∨ (COB_mat ax).det = -1 := by
      rw [cob_mat_other_repr]
      rw [←Module.Basis.det_apply]
      have detlem: (COB ax).toBasis.det Basis3.toBasis  = (1:ℝ) ∨ (COB ax).toBasis.det Basis3.toBasis   = (-1:ℝ) :=
        OrthonormalBasis.det_to_matrix_orthonormalBasis_real (COB ax) Basis3
      exact detlem
    by_contra eqz
    rw [eqz] at this
    simp at this

  rw [this]
  simp
  exact innerspecial.right



noncomputable def rot (ax: S2) (θ:ℝ) : SO3 := ⟨rot_mat ax θ, rot_mat_is_special ax θ⟩



lemma triv_rot (ax: S2): rot ax 0 = 1 := by
  simp [rot]
  simp [rot_mat]
  have inner_eq_1: rot_mat_inner ax 0 = (1: MAT) := by
    simp [rot_mat_inner]
    simp [Matrix.one_fin_three]
  simp [inner_eq_1]
  set C:= COB_mat ax with Cdef
  have isorth: C ∈ Matrix.orthogonalGroup (Fin 3) ℝ := COB_mat_is_ortho ax
  let el := (⟨C, isorth⟩: Matrix.orthogonalGroup (Fin 3) ℝ)
  have cdef: C = el.val := by rfl
  have pr := (el⁻¹).property
  rw [cdef]
  rw [unitary_invs_coe]
  simp

lemma rot_mat_inner_comp_add (ax: S2) (s t : ℝ): rot_mat_inner ax s * rot_mat_inner ax t = rot_mat_inner ax (s + t) := by
  simp [rot_mat_inner]
  constructor
  constructor
  rw [Real.cos_add]
  ring
  --
  rw [Real.sin_add]
  ring
  --
  constructor
  rw [Real.sin_add]
  --
  rw [Real.cos_add]
  ring


lemma rot_mat_comp_add (ax: S2) (s t : ℝ): rot_mat ax s * rot_mat ax t = rot_mat ax (s + t) := by
  simp [rot_mat]
  rw [←mul_assoc ((COB_mat ax)⁻¹ * rot_mat_inner ax s * COB_mat ax)]
  rw [←mul_assoc ((COB_mat ax)⁻¹ * rot_mat_inner ax s * COB_mat ax)]
  have :COB_mat ax * (COB_mat ax)⁻¹ = 1 := by
    set el := COB_mat ax
    have : el ∈ Matrix.orthogonalGroup (Fin 3) ℝ:= by exact COB_mat_is_ortho ax
    let E: Matrix.orthogonalGroup (Fin 3) ℝ:= ⟨el, this⟩
    change E.val * E.val⁻¹ = 1
    rw [unitary_invs_coe]
    simp

  rw [mul_assoc ((COB_mat ax)⁻¹ * rot_mat_inner ax s )]
  rw [this]
  simp
  rw [mul_assoc (COB_mat ax)⁻¹]
  rw [rot_mat_inner_comp_add]


lemma rot_comp_add (ax: S2) (s t : ℝ): f (rot ax s) ∘ f (rot ax t) = (f (rot ax (s + t)) : R3 → R3):= by
  funext w
  simp [f]
  rw [smul_smul]
  simp [rot]
  simp [rot_mat_comp_add]


lemma rot_pow_lemma (ax: S2) (θ: ℝ) (N: ℕ):
  ((f (rot ax θ)): R3 → R3)^[N] = ((f (rot ax ((N: ℝ) * θ))): R3 → R3) := by
  induction' N with n pn
  simp
  simp [triv_rot]
  funext w
  simp [f]
  --
  rw [Function.iterate_succ]
  rw [pn]
  rw [rot_comp_add]
  have :↑n * θ + θ =↑(n + 1) * θ := by
    norm_num
    linarith

  rw [this]



lemma rot_iso_pow_lemma (ax: S2) (θ: ℝ) (N: ℕ):
(rot_iso ax θ)^[N] = (rot_iso ax (N * θ)) := by
  induction' N with n pn
  simp
  rw [triv_rot_iso]
  simp
  --
  rw [Function.iterate_succ]
  rw [pn]
  funext w
  rw [Function.comp_apply]
  rw [rot_iso_comp]
  have :↑n * θ + θ =↑(n + 1) * θ := by
    norm_num
    linarith
  rw [this]


theorem orth_toMatrix_mulVec_repr (B C : OrthonormalBasis (Fin 3) ℝ R3 ) (f : R3 →ₗ[ℝ] R3) (x : R3) :
  Matrix.mulVec (LinearMap.toMatrix B.toBasis C.toBasis f) (B.repr x).ofLp = (C.repr (f x)).ofLp := by
    ext i
    rw [← Matrix.toLin'_apply, LinearMap.toMatrix, LinearEquiv.trans_apply, Matrix.toLin'_toMatrix',
    LinearEquiv.arrowCongr_apply]
    congr
    simp


lemma inner_as_to_matrix (ax: S2): rot_mat_inner ax T =
  LinearMap.toMatrix (COB ax).toBasis (COB ax).toBasis (rot_iso ax T).toLinearMap := by
  apply Matrix.ext_of_mulVec_single
  intro i
  simp
  sorry
  --theorem LinearMap.toMatrix_apply (f : M₁ →ₗ[R] M₂) (i : m) (j : n) :
  --  LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i := by


lemma same_thing(ax: S2) (S: Set R3) (s : R3) : rot ax T • s = (rot_iso ax T) s := by
  simp only [HSMul.hSMul, SMul.smul]
  simp [rot]

  simp [rot_mat]
  rw [←Matrix.mulVec_mulVec]
  rw [←Matrix.mulVec_mulVec]

  simp [COB_mat]
  have sreprof: s = Basis3.repr s := by
    simp [Basis3]
    rfl

  rw [sreprof]
  rw [←mul_assoc ((LinearMap.toMatrix Basis3.toBasis (COB ax).toBasis) 1)⁻¹]
  rw [←Matrix.mulVec_mulVec]
  rw [orth_toMatrix_mulVec_repr Basis3 (COB ax) (1: R3 →ₗ[ℝ] R3) ]
  simp
  rw [←Matrix.mulVec_mulVec]

  rw [inner_as_to_matrix]


  rw [orth_toMatrix_mulVec_repr  (COB ax) (COB ax)  (rot_iso ax T).toLinearMap ]
  simp


  have : ((LinearMap.toMatrix Basis3.toBasis (COB ax).toBasis) 1)⁻¹ =
  (LinearMap.toMatrix (COB ax).toBasis Basis3.toBasis 1) := by

    have :  (LinearMap.id: (R3 →ₗ[ℝ] R3)) = 1 := rfl
    rw [←this]
    rw [LinearMap.toMatrix_id_eq_basis_toMatrix Basis3.toBasis (COB ax).toBasis]
    rw [LinearMap.toMatrix_id_eq_basis_toMatrix (COB ax).toBasis Basis3.toBasis]

    have := Module.Basis.invertibleToMatrix (COB ax).toBasis Basis3.toBasis
    symm
    set M12 := (Basis3.toBasis.toMatrix (COB ax).toBasis )  with M12def
    set M21 := ((COB ax).toBasis.toMatrix Basis3.toBasis)  with M21def

    rw [←mul_one M12]
    have idd: 1 = M21 * M21⁻¹  := by
      simp
    rw [idd]
    rw [←mul_assoc]
    nth_rewrite 2 [←one_mul M21⁻¹]
    apply congrArg (fun x ↦ x * M21⁻¹)
    rw [M12def, M21def]
    set B1 := Basis3.toBasis
    set B2 := (COB ax).toBasis
    rw [Module.Basis.toMatrix_mul_toMatrix_flip]

  rw [this]

  rw [orth_toMatrix_mulVec_repr  (COB ax) Basis3 (1: R3 →ₗ[ℝ] R3) ]
  simp
  simp [Basis3]
  rfl
