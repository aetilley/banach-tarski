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

def K (g: SO3) := LinearMap.ker (Matrix.toLin' (g.val - 1))
lemma dim_ker (g: SO3): Module.finrank ℝ (K g) = 1 := sorry

def nz (g: SO3): K g := sorry
lemma is_nz (g: SO3): (nz g) ≠ 0 := sorry

lemma isspan (g: SO3): Submodule.span ℝ {nz g} = (⊤: Submodule ℝ (K g)) :=
  (finrank_eq_one_iff_of_nonzero (nz g) (is_nz g)).mp (dim_ker g)

lemma fixed_lemma (g: SO3) : g≠1 → Nat.card ({x ∈ S2 | g • x = x}) = 2 := sorry
