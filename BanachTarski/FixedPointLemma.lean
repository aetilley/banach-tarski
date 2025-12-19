import Mathlib
import BanachTarski.Common


set_option linter.all false

#check Module.End.hasEigenvalue_iff
#check Module.End.mem_eigenspace_iff
-- Need 1 ) Det is product of eigenvalues
-- 2) All eigenvalues are norm 1 (easy)
-- 3) 1 only appears w/ mult 1
-- 4) dim of eigenspace is mult of eigenvalue
#check Matrix.mem_spectrum_of_isRoot_charpoly
#check Matrix.charpoly_degree_eq_dim

noncomputable def as_complex (M: MAT) : Matrix (Fin 3) (Fin 3) ℂ := (algebraMap ℝ ℂ).mapMatrix M

lemma det_as_prod (g: SO3): (Matrix.charpoly (as_complex g.val)).roots.prod = 1 := by
  have l1:(as_complex (g.val)).det = (Matrix.charpoly (as_complex g.val)).roots.prod  := by
    apply Matrix.det_eq_prod_roots_charpoly
  have l3: (g.val).det = 1 := by
    exact (Matrix.mem_specialOrthogonalGroup_iff.mp g.property).right
  have l4 : (as_complex (g.val)).det = 1:= by
    simp only [as_complex]
    rw [←RingHom.map_det]
    rw [l3]
    simp

  exact Eq.trans l1.symm l4

lemma charpoly_deg_3 (g: SO3): (Matrix.charpoly (as_complex g.val)).degree = 3 := by
  rw [Matrix.charpoly_degree_eq_dim]
  simp

def kermap_raw (g: SO3) : R3_raw →ₗ[ℝ] R3_raw := Matrix.toLin' (g.val - 1)

noncomputable def ofLp_linear : R3 →ₗ[ℝ] R3_raw := (WithLp.linearEquiv 2 ℝ R3_raw).toLinearMap

noncomputable def to_R3_linear : R3_raw →ₗ[ℝ] R3 := (WithLp.linearEquiv 2 ℝ R3_raw).symm.toLinearMap

noncomputable def kermap (g: SO3) : R3 →ₗ[ℝ] R3 := to_R3_linear.comp ((kermap_raw g).comp ofLp_linear)

noncomputable def K (g: SO3): Submodule ℝ R3 := LinearMap.ker (kermap g)

lemma dim_ker (g: SO3): g ≠1 → Module.finrank ℝ (K g) = 1 := sorry

def nz (g: SO3): K g := sorry
lemma is_nz (g: SO3): (nz g) ≠ 0 := sorry

lemma isspan (g: SO3): g≠1 → Submodule.span ℝ {nz g} = (⊤: Submodule ℝ (K g)) := by
  intro notone
  exact (finrank_eq_one_iff_of_nonzero (nz g) (is_nz g)).mp (dim_ker g notone)

lemma fixed_lemma (g: SO3) : g≠1 → Nat.card ({x ∈ S2 | g • x = x}) = 2 := by
  intro notone
  apply Nat.card_eq_two_iff.mpr

  let el: R3 := (nz g).val
  let el_neg: R3 := -el
  have el_nz : el ≠ 0 := by
    simp [el]
    exact is_nz g
  have el_neg_nz : el_neg ≠ 0 := by
    simp [el_neg]
    exact el_nz
  let el_normed := normed el
  let el_normed_neg := normed el_neg
  have rev_el: el = ‖el‖ • el_normed  := by
    simp [el_normed]
    simp [normed]
    simp [smul_smul]
    rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr el_nz)]
    simp


  have rev_el_neg: el_neg = ‖el_neg‖ • el_normed_neg := by
    simp [el_normed_neg]
    simp [el_neg]
    simp [normed]
    simp [smul_smul]
    rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr el_nz)]
    simp

  have prop: (g.val).mulVec el.ofLp - el.ofLp = 0 := by
    have prop :_:=  (nz g).property
    simp only [K] at prop
    simp only [kermap] at prop
    rw [LinearMap.mem_ker] at prop
    rw [LinearMap.comp_apply] at prop
    rw [LinearMap.comp_apply] at prop
    simp [ofLp_linear] at prop
    change to_R3_linear ((kermap_raw g) (el).ofLp) = 0 at prop
    simp [to_R3_linear] at prop
    simp [kermap_raw] at prop
    exact prop


  have el_normed_in_s2 : el_normed ∈ S2 := normed_in_S2 el_nz
  have el_normed_neg_in_s2 : el_normed_neg ∈ S2 := normed_in_S2 el_neg_nz
  have el_normed_fixed : g • el_normed = el_normed := by
    simp [el_normed]
    simp [normed]
    rw [smul_comm]
    apply congrArg
    rw [sub_eq_iff_eq_add] at prop
    simp at prop
    rw [SO3_smul_def g el]
    rw [prop]
    rfl

  have el_normed_neg_fixed : g • el_normed_neg = el_normed_neg := by
    simp [el_normed_neg, el_neg]
    simp [normed]
    rw [smul_comm]
    apply congrArg
    rw [sub_eq_iff_eq_add] at prop
    simp at prop
    rw [SO3_smul_def g el]
    rw [prop]
    rfl

  have conj:  el_normed ∈ S2 ∧ g • el_normed = el_normed := ⟨el_normed_in_s2, el_normed_fixed⟩
  have conj_neg:  el_normed_neg ∈ S2 ∧ g • el_normed_neg = el_normed_neg :=
    ⟨el_normed_neg_in_s2, el_normed_neg_fixed⟩
  let F: {x | x ∈ S2 ∧ g • x = x} := ⟨el_normed, conj⟩
  let Fneg: {x | x ∈ S2 ∧ g • x = x} := ⟨el_normed_neg, conj_neg⟩
  use F, Fneg
  constructor
  ---
  simp [F, Fneg, el_normed, el_normed_neg, el_neg, normed]
  by_contra bad
  apply congrArg (fun x ↦ x + (‖el‖⁻¹ • el)) at bad
  simp at bad
  have  two: (2: ℝ) • ‖el‖⁻¹ • el  = 0 := by
    rw [two_smul]
    exact bad

  simp at two
  exact el_nz two
  --
  apply Set.eq_univ_iff_forall.mpr
  intro v
  have vprop: _:= v.prop
  simp only [S2, Metric.sphere]  at vprop
  let k:= v.val
  have inker: k ∈ K g := by
    simp [K]
    simp [kermap]
    simp [ofLp_linear]
    simp [to_R3_linear]
    simp [kermap_raw]
    have vpr := vprop.right
    rw [SO3_smul_def g  v ] at vpr
    simp [to_R3] at vpr
    apply congrArg WithLp.ofLp at vpr
    simp at vpr
    rw [vpr]
    dsimp [k]
    simp


  have ininsp: ⟨k, inker⟩ ∈  Submodule.span ℝ {nz g} := by
    rw [isspan g notone]
    simp

  have :_:= Submodule.mem_span_singleton.mp ininsp
  obtain ⟨a, pa⟩ := this
  have cast: a • el = k := by
    apply congrArg (fun x ↦ x.val) at pa
    simp at pa
    exact pa
  rw [rev_el] at cast
  have cast_old := cast
  apply congrArg (fun w ↦ ‖w‖) at cast
  rw [norm_smul] at cast
  rw [norm_smul] at cast
  have normk: ‖k‖ = 1 := by
    dsimp [k]
    have :_:=vprop.left
    rw [←this]
    simp


  rw [normk] at cast
  have nn: ‖‖el‖‖  = ‖el‖:=by
    norm_num
  rw [nn] at cast
  have obv:  ‖el_normed‖ = 1 := by
    simp [el_normed]
    simp [normed]
    simp [norm_smul]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr el_nz)

  rw [obv] at cast
  simp at cast
  have cs: a = ‖el‖⁻¹ ∨ a = -‖el‖⁻¹ := by
    rcases abs_cases a with pos0 | neg0
    rw [pos0.left] at cast
    left
    apply eq_inv_of_mul_eq_one_left
    exact cast
    --
    right
    rw [neg0.left] at cast
    rw [←neg_mul_eq_neg_mul] at cast
    rw [neg_eq_iff_eq_neg] at cast
    apply congrArg (fun x ↦ x * ‖el‖⁻¹) at cast
    simp at cast
    rw [mul_assoc] at cast
    rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr el_nz)] at cast
    simp at cast
    exact cast

  rcases cs with pos | neg
  ------
  rw [pos] at cast_old
  rw [smul_smul] at cast_old
  rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr el_nz)] at cast_old
  simp at cast_old
  have : v = F := by
    simp [F]
    simp [cast_old]
    rfl
  rw [this]
  simp
  ---------
  rw [neg] at cast_old
  rw [smul_smul] at cast_old
  rw [neg_mul] at cast_old
  rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr el_nz)] at cast_old
  simp at cast_old
  rw [neg_eq_iff_eq_neg] at cast_old
  have:  el_normed_neg = k := by
    simp [el_normed_neg]
    simp [el_normed] at cast_old
    simp [el_neg]
    simp [normed]
    simp [normed] at cast_old
    rw [cast_old]
    simp

  have : v = Fneg := by
    simp [Fneg]
    simp [this]
    rfl
  rw [this]
  simp
