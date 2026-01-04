import Mathlib

/-- Defs used throughout. -/

-- -- Misc
def f {X : Type*} {G : Type*} [Group G] [MulAction G X] (g : G) : X → X := fun x : X ↦ g • x

lemma fcomp {X : Type*} {G : Type*} [Group G] [MulAction G X] (g h : G) :
(fun x : X ↦ (g * h) • x) = (fun x : X ↦ g • x) ∘ (fun x : X ↦ h • x) := by
  simp [mul_smul g h]
  rfl

lemma finj {X : Type*} {G : Type*} [Group G] [MulAction G X] (g : G) :
Function.Injective (fun x ↦ g • x : X → X) := by
  intro a b eq
  simp at eq
  exact eq


-- -- Free Group Defs
abbrev FG2 := FreeGroup (Fin 2)
def σchar := (0: Fin 2)
def τchar := (1: Fin 2)
lemma σ_def : σchar = (0: Fin 2) := rfl
lemma τ_def : τchar = (1: Fin 2) := rfl
abbrev σ := FreeGroup.of (σchar)
abbrev τ := FreeGroup.of (τchar)

-- The type of element of FreeGroup.toWord
abbrev chartype := Fin 2 × Bool

instance finite_chartype : Finite chartype := inferInstance

instance countable_chartype : Countable chartype := by apply Finite.to_countable

instance countable_of_fg2 : Countable FG2 := by
  have lists_countable: Countable (List chartype) := _root_.List.countable
  obtain ⟨lists_to_nat, lists_to_nat_is_inj⟩ :=
    (countable_iff_exists_injective (List chartype)).mp lists_countable
  apply (countable_iff_exists_injective FG2).mpr
  let foo: FG2 → ℕ := lists_to_nat ∘ FreeGroup.toWord
  use foo
  exact Function.Injective.comp lists_to_nat_is_inj FreeGroup.toWord_injective

lemma wopts : ∀ w : chartype,
(w= (0, true) ∨ w = (0, false) ∨ w = (1, true) ∨ w = (1, false)) := by
  intro ⟨w1, w2⟩
  fin_cases w1, w2
  · left; simp
  · right; left; simp
  · right; right; left; simp
  · right; right; right; simp

lemma split2 (i : Fin 2) : i = 0 ∨ i = 1 := by
  rcases (em (i=0)) with yes | no
  · exact Or.inl yes
  · exact Or.inr (Fin.eq_one_of_ne_zero i no)

-- -- Central Geometric Defs.
abbrev MAT := Matrix (Fin 3) (Fin 3) ℝ
abbrev R3_raw := (Fin 3) → ℝ
abbrev R3 :=  EuclideanSpace ℝ (Fin 3)
def to_R3 (v : R3_raw) : R3 := WithLp.toLp 2 v

def origin := (0: R3)
def S2 : Set R3 := Metric.sphere (0: R3) 1
abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

-- Useful Properties and instances
lemma so3_invs_coe : ∀ g : SO3, (g.val)⁻¹ = g⁻¹.val := by
  intro g
  apply Matrix.inv_eq_left_inv
  rw [←MulMemClass.coe_mul]
  simp

lemma unitary_invs_coe : ∀ g : Matrix.orthogonalGroup (Fin 3) ℝ , (g.val)⁻¹ = g⁻¹.val := by
  intro g
  apply Matrix.inv_eq_left_inv
  rw [←MulMemClass.coe_mul]
  simp

instance so3_has_inv (g : SO3) : Invertible (g : MAT) := by
  have g_special := g.property
  simp only [SO3] at g_special
  rw [Matrix.mem_specialOrthogonalGroup_iff] at g_special
  rw [Matrix.mem_orthogonalGroup_iff] at g_special
  exact Matrix.invertibleOfRightInverse g.val g.val.transpose g_special.left

lemma so3_closed_under_inverse (g : MAT) : g ∈ SO3 → g⁻¹ ∈ SO3 := by
  intro lhs
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  rw [Matrix.mem_orthogonalGroup_iff]
  have a_tr:_:= Matrix.mem_specialOrthogonalGroup_iff.mp lhs
  constructor
  · rw [Matrix.mem_orthogonalGroup_iff] at a_tr
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
  · simp
    exact a_tr.right

instance SO3_action_on_MAT : MulAction SO3 R3_raw where
  smul g v  := (Matrix.mulVec (g : Matrix (Fin 3) (Fin 3) ℝ) v)
  one_smul v := Matrix.one_mulVec v
  mul_smul x y v := (
    Matrix.mulVec_mulVec v (x : Matrix (Fin 3) (Fin 3) ℝ) (y : Matrix (Fin 3) (Fin 3) ℝ)).symm

instance SO3_action_on_R3 : MulAction SO3 R3 := inferInstance

lemma SO3_smul_def (g : SO3) (v : R3) :
  g • v = to_R3 (Matrix.mulVec (g : MAT) v.ofLp) := rfl

noncomputable def normed : R3 → R3 := fun x ↦ (1 / ‖x‖) • x
lemma normed_in_S2:v ≠ 0 → normed v ∈ S2 := by
  intro nonz
  simp [normed, S2]
  rw [norm_smul]
  simp
  have _ :Invertible ‖v‖ := by
    apply invertibleOfNonzero
    exact mt norm_eq_zero.mp nonz
  apply inv_mul_cancel_of_invertible

-- Some Lemmas about modular arithmetic.

lemma ml {i j : ℕ} {m n : Fin (i * j)} : m ≠ n → m.divNat ≠ n.divNat ∨
  (m.divNat = n.divNat ∧ m.modNat ≠ n.modNat) := by

  contrapose!
  intro lhs
  let eqdiv := lhs.left
  let eqmod := lhs.right eqdiv
  have eq: (m.divNat, m.modNat) = (n.divNat, n.modNat) := by
    apply Prod.ext
    · exact eqdiv
    · exact eqmod

  have resm : _ := finProdFinEquiv.right_inv m
  have resn : _ := finProdFinEquiv.right_inv n
  calc m
  _ = finProdFinEquiv.toFun (finProdFinEquiv.invFun m) := by rw [resm]
  _ = finProdFinEquiv.toFun ((m.divNat, m.modNat)) := by simp
  _ = finProdFinEquiv.toFun ((n.divNat, n.modNat)) := by rw [eq]
  _ = finProdFinEquiv.toFun (finProdFinEquiv.invFun n) := by simp
  _ = n := by rw [resn]


lemma ml2 {i j : ℕ} {m n : Fin (i * j)} : m ≠ n → m.modNat ≠ n.modNat ∨
  (m.modNat = n.modNat ∧ m.divNat ≠ n.divNat) := by
  intro mneqn
  have res :_ := ml mneqn
  tauto
