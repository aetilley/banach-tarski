import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

set_option warningAsError false
set_option linter.all false

abbrev FG2 := FreeGroup (Fin 2)

abbrev chartype := Fin 2 × Bool


def σchar := (0: Fin 2)

lemma σ_def : σchar = (0: Fin 2) := rfl
def τchar := (1: Fin 2)
lemma τ_def : τchar = (1: Fin 2) := rfl
abbrev σ := FreeGroup.of (σchar)
abbrev τ := FreeGroup.of (τchar)

def f {X : Type*} {G: Type*} [Group G] [MulAction G X] (g : G): X → X := fun x: X ↦ g • x

abbrev MAT:= Matrix (Fin 3) (Fin 3) ℝ
abbrev R3_raw := (Fin 3) → ℝ
abbrev R3 :=  EuclideanSpace ℝ (Fin 3)

def origin := (0: R3)
def S2 : Set R3 := Metric.sphere (0: R3) 1
abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

lemma so3_invs_coe : ∀g:SO3, (g.val)⁻¹ = g⁻¹.val := by
  intro g
  apply Matrix.inv_eq_left_inv
  rw [←MulMemClass.coe_mul]
  simp

lemma unitary_invs_coe : ∀g: Matrix.orthogonalGroup (Fin 3) ℝ , (g.val)⁻¹ = g⁻¹.val := by
  intro g
  apply Matrix.inv_eq_left_inv
  rw [←MulMemClass.coe_mul]
  simp

instance so3_has_inv (g: SO3) : Invertible (g:MAT) := by
  have g_special := g.property
  simp only [SO3] at g_special
  rw [Matrix.mem_specialOrthogonalGroup_iff] at g_special
  rw [Matrix.mem_orthogonalGroup_iff] at g_special
  exact Matrix.invertibleOfRightInverse g.val g.val.transpose g_special.left



lemma so3_closed_under_inverse (g: MAT) : g∈ SO3 → g⁻¹ ∈ SO3 := by
  intro lhs
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  rw [Matrix.mem_orthogonalGroup_iff]
  have a_tr:_:= Matrix.mem_specialOrthogonalGroup_iff.mp lhs
  constructor
  rw [Matrix.mem_orthogonalGroup_iff] at a_tr
  have part :_:= congrArg (fun x ↦ g⁻¹ *x) a_tr.left
  simp at part
  rw [←mul_assoc] at part
  have invg : _:= so3_has_inv ⟨g, lhs⟩
  rw [Matrix.inv_mul_of_invertible] at part
  have part2 :_:= congrArg (fun x ↦ x * (Matrix.transpose g)⁻¹) part
  simp at part2
  symm
  rw [Matrix.transpose_nonsing_inv]
  exact part2
  --
  simp
  exact a_tr.right



-- The standard action given by matrix multiplication.
instance SO3_action_on_MAT: MulAction SO3 R3_raw where
  smul g v  := (Matrix.mulVec (g : Matrix (Fin 3) (Fin 3) ℝ) v)
  one_smul v := Matrix.one_mulVec v
  mul_smul x y v := (Matrix.mulVec_mulVec v (x : Matrix (Fin 3) (Fin 3) ℝ) (y : Matrix (Fin 3) (Fin 3) ℝ)).symm

instance SO3_action_on_R3: MulAction SO3 R3 := inferInstance

lemma SO3_smul_def (g : SO3) (v : R3) :
  g • v = Matrix.mulVec (g : MAT) v := rfl



def R3_mat_vec_mul (m: MAT) (v: R3) : R3 := WithLp.toLp 2 (Matrix.mulVec m v)
def to_R3 (v: R3_raw) := WithLp.toLp 2 v

lemma wopts: ∀ w : (Fin 2 × Bool), (w= (0, true) ∨ w = (0, false) ∨ w = (1, true) ∨ w = (1, false)) := by
  intro ⟨w1, w2⟩
  fin_cases w1, w2
  left
  simp
  right
  left
  simp
  right
  right
  left
  simp
  right
  right
  right
  simp
