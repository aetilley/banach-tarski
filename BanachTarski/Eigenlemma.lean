import Mathlib
import BanachTarski.Common


set_option linter.all false

#check Module.End.hasEigenvalue_iff
#check Module.End.mem_eigenspace_iff
-- Need 1 ) Det is product of eigenvalues
-- 2) All eigenvalues are norm 1 (easy)
-- 3) 1 only appears w/ mult 1
-- 4) dim of eigenspace is mult of eigenvalue

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





lemma fixed_lemma (g: SO3) : g≠1 → Nat.card ({x ∈ S2 | g • x = x}) = 2 := sorry
