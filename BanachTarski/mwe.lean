import Mathlib

abbrev R3 :=  EuclideanSpace ℝ (Fin 3)
-- Context.  Take this for granted
def Foo : R3 ≃ₗᵢ[ℝ] R3 := sorry
def S1 : Submodule ℝ R3 := sorry
def S2 : Submodule ℝ R3 := sorry
def B1 : Module.Basis (Fin 2) ℝ S1 := sorry
def B2 : Module.Basis (Fin 1) ℝ S2 := sorry
def θ : ℝ := sorry


noncomputable def submods : (i: Fin 2) → (Submodule ℝ R3) := ![S1, S2]
lemma internal_pr: DirectSum.IsInternal submods := sorry

def mod_dim : (Fin 2) → Type
  | ⟨0,_⟩ => Fin 2
  | ⟨1,_⟩ => Fin 1

instance mod_dim_fintype (i : Fin 2) : Fintype (mod_dim i) := sorry
instance mod_dim_decidableEq (i : Fin 2) : DecidableEq (mod_dim i) := sorry


noncomputable def bases_func : (i : Fin 2) → (Module.Basis (mod_dim i) ℝ (submods i))
  | ⟨0, _⟩ => B1
  | ⟨1, _⟩ => B2

lemma known: LinearMap.toMatrix
  (internal_pr.collectedBasis bases_func)
  (internal_pr.collectedBasis bases_func)
  Foo.toLinearMap =
    Matrix.blockDiagonal' (fun i ↦
      match i with
      | ⟨0, _⟩ =>  !![θ.cos, -θ.sin; θ.sin, θ.cos]
      | ⟨1, _⟩ =>  !![1;]
      ) := sorry


-- You get to fill this in.  Should be something like
-- the union of B0 and B1
def COB : Module.Basis (Fin 3) ℝ R3 := sorry

-- Prove me
lemma goal: LinearMap.toMatrix COB COB Foo.toLinearMap =
    !![
      θ.cos, -θ.sin, 0;
      θ.sin, θ.cos, 0;
      0, 0, 1;
    ] := sorry
