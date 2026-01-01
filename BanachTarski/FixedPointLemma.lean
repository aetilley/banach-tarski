import Mathlib
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.UnitaryGroup

import BanachTarski.Common
import BanachTarski.IdlemAristotle

open scoped Matrix.Norms.L2Operator


set_option linter.all false
set_option maxHeartbeats 3000000

noncomputable def ofLp_linear : R3 →ₗ[ℝ] R3_raw := (WithLp.linearEquiv 2 ℝ R3_raw).toLinearMap

noncomputable def to_R3_linear : R3_raw →ₗ[ℝ] R3 := (WithLp.linearEquiv 2 ℝ R3_raw).symm.toLinearMap


noncomputable def g_end_raw (g: SO3): Module.End ℝ R3_raw := Matrix.toLin' g.val
noncomputable def g_end (g: SO3) : Module.End ℝ R3 := to_R3_linear.comp ((g_end_raw g).comp ofLp_linear)

def kermap_raw (g: SO3) : R3_raw →ₗ[ℝ] R3_raw := Matrix.toLin' (g.val - 1)
noncomputable def kermap (g: SO3) : R3 →ₗ[ℝ] R3 := to_R3_linear.comp ((kermap_raw g).comp ofLp_linear)

noncomputable def K (g: SO3): Submodule ℝ R3 := LinearMap.ker (kermap g)

lemma same_char_0 (g: SO3): LinearMap.charpoly (g_end g) = (g.val).charpoly := by
  let e := (WithLp.linearEquiv 2 ℝ R3_raw).symm
  have h_conj : g_end g = e.conj (g_end_raw g) := by
    simp [g_end, g_end_raw, LinearEquiv.conj_apply, e, to_R3_linear, ofLp_linear]
    rfl
  rw [h_conj]
  rw [LinearEquiv.charpoly_conj e (g_end_raw g)]
  rw [← Matrix.charpoly_toLin' g.val]
  simp [g_end_raw]

lemma mapMatrix_is_map  (g: SO3): Matrix.charpoly ((algebraMap ℝ ℂ).mapMatrix g.val) =
  Matrix.charpoly (g.val.map (algebraMap ℝ ℂ)) := by
  rfl

lemma same_char (g: SO3) : (LinearMap.charpoly (g_end g)).map (algebraMap ℝ ℂ) = cpoly g := by
  simp [cpoly]

  simp only [as_complex]
  rw [mapMatrix_is_map]
  rw [Matrix.charpoly_map]
  apply congrArg
  exact same_char_0 g

lemma cpoly_coef_real (g: SO3) : ∀i: ℕ, ∃x: ℝ, x = (cpoly g).coeff i := by
  intro i
  rw [←same_char g]
  use (LinearMap.charpoly (g_end g)).coeff i
  rw [Polynomial.coeff_map]
  simp


lemma det_as_prod (g: SO3): (cpoly g).roots.prod = 1 := by
  have l1:(as_complex (g.val)).det = (cpoly g).roots.prod  := by
    apply Matrix.det_eq_prod_roots_charpoly
  have l3: (g.val).det = 1 := by
    exact (Matrix.mem_specialOrthogonalGroup_iff.mp g.property).right
  have l4 : (as_complex (g.val)).det = 1:= by
    simp only [as_complex]
    rw [←RingHom.map_det]
    rw [l3]
    simp

  exact Eq.trans l1.symm l4

lemma charpoly_deg_3 (g: SO3): (cpoly g).degree = 3 := by
  simp [cpoly]


lemma charpoly_natdeg_3 (g: SO3): (cpoly g).natDegree = 3 := by
  simp [cpoly]


lemma num_roots_eq_deg (g: SO3): (cpoly g).roots.card = (cpoly g).natDegree := by
  apply IsAlgClosed.card_roots_eq_natDegree

lemma num_roots_eq_3 (g: SO3): (cpoly g).roots.card = 3 := by
  rw [num_roots_eq_deg]
  exact charpoly_natdeg_3 g

abbrev C3 := Matrix (Fin 3) (Fin 3) ℂ

lemma eig_norms (g: SO3) (z:ℂ) : z ∈ (cpoly g).roots → ‖z‖ = 1 := by
  intro lhs
  have isrt: Polynomial.IsRoot (cpoly g) z := by
    apply Polynomial.isRoot_of_mem_roots
    exact lhs

  have this1: z ∈ spectrum ℂ (as_complex g.val) := Matrix.mem_spectrum_of_isRoot_charpoly isrt
  have gunitary: (as_complex g.val) ∈ unitary C3 := by
    apply Unitary.mem_iff.mpr
    have gprop := g.prop
    simp only [SO3] at gprop
    have other := Matrix.mem_specialOrthogonalGroup_iff.mp gprop
    have orth_mem1 := other.left
    have orth_mem2 := other.left
    rw [Matrix.mem_orthogonalGroup_iff] at orth_mem1
    rw [Matrix.mem_orthogonalGroup_iff'] at orth_mem2
    have conjTranspose_eq_transpose : (as_complex g.val).conjTranspose = Matrix.transpose (as_complex g.val) := by
      simp only [as_complex, Matrix.conjTranspose, RingHom.mapMatrix_apply]
      ext i j
      simp [Matrix.transpose]
    have mapMatrix_transpose : Matrix.transpose ((algebraMap ℝ ℂ).mapMatrix g.val) =
        (algebraMap ℝ ℂ).mapMatrix (g.val.transpose) := by
        ext i j
        simp [RingHom.mapMatrix_apply, Matrix.transpose]
    constructor
    · rw [Matrix.star_eq_conjTranspose]
      rw [conjTranspose_eq_transpose]
      simp only [as_complex]
      rw [mapMatrix_transpose]
      simp only [RingHom.mapMatrix_apply]
      rw [←Matrix.map_mul]
      have : (1 : MAT).map (algebraMap ℝ ℂ) = (1:C3) := by
        ext i j
        simp [Matrix.one_apply]
        split_ifs <;> simp
      rw [←this, orth_mem2]
    · rw [Matrix.star_eq_conjTranspose]
      rw [conjTranspose_eq_transpose]
      simp only [as_complex]
      rw [mapMatrix_transpose]
      simp only [RingHom.mapMatrix_apply]
      rw [←Matrix.map_mul]
      have : (1 : MAT).map (algebraMap ℝ ℂ) = (1:C3) := by
        ext i j
        simp [Matrix.one_apply]
        split_ifs <;> simp
      rw [←this, orth_mem1]


  have : z ∈ Metric.sphere (0:ℂ) 1 := spectrum.subset_circle_of_unitary gunitary this1
  simp [Metric.sphere] at this
  exact this


open ComplexConjugate
def CONJ : ℂ →+* ℂ := conj


lemma flem (g: SO3): z ∈ (cpoly g).roots  → z = CONJ z → (z = 1 ∨ z = -1) := by
  intro lhs
  intro lhs2
  simp [CONJ] at lhs2
  symm at lhs2
  have :_:= Complex.conj_eq_iff_real.mp lhs2
  obtain ⟨r, pr⟩ :=  this
  have normone: ‖z‖ = 1    := eig_norms g z lhs
  rw [pr] at normone
  simp at normone
  rw [pr]
  rcases abs_cases r with c1 | c2
  left
  rw [←c1.left]
  simp [normone]
  --
  right
  rw [←neg_eq_iff_eq_neg]
  rw [c2.left] at normone
  apply Complex.ext
  simp
  exact normone
  --
  simp



lemma flem2 (g: SO3): z ∈ (cpoly g).roots  → (z ≠ 1 ∧ z ≠ -1) → (z ≠ CONJ z) := by
  intro lhs
  intro lhs2
  by_contra are_eq
  have :_:= flem g lhs are_eq
  tauto


lemma conj_roots (g: SO3): (cpoly g).roots = (cpoly g).roots.map CONJ := by
  have l0: cpoly g = (cpoly g).map CONJ := by
    ext i
    simp
    obtain ⟨x, px⟩ := cpoly_coef_real g i
    rw [←px]
    simp [CONJ]

  have l1: (cpoly g).roots = ((cpoly g).map CONJ).roots := by nth_rewrite 1 [l0]; rfl
  have l2: (cpoly g).roots.map CONJ = ((cpoly g).map CONJ).roots  := by
    have deglem :_:= charpoly_natdeg_3 g
    apply Polynomial.roots_map_of_map_ne_zero_of_card_eq_natDegree
    --
    simp
    by_contra bad
    rw [bad] at deglem
    simp at deglem
    --
    exact num_roots_eq_deg g

  exact Eq.trans l1 l2.symm

lemma conj_roots_2 (g: SO3) (z : ℂ): z ∈ (cpoly g).roots → CONJ z ∈ (cpoly g).roots := by
  intro lhs
  have so :CONJ z ∈(cpoly g).roots.map CONJ := by
    apply Multiset.mem_map.mpr
    use z
  rwa [conj_roots]

--theorem count_map_eq_count' [DecidableEq β] (f : α → β) (s : Multiset α) (hf : Function.Injective f)
--    (x : α) : (s.map f).count (f x) = s.count x := by

lemma conj_roots_3 (g: SO3) (z : ℂ):
  (cpoly g).roots.count z = (cpoly g).roots.count (CONJ z) := by
    set R:= (cpoly g).roots with R_def
    have tmp: (R.map CONJ).count (CONJ z) = R.count z := by
      apply Multiset.count_map_eq_count'
      simp [CONJ]
      exact RingHom.injective (starRingEnd ℂ)
    rw [←tmp]
    apply congrArg
    exact Eq.symm (conj_roots g)


lemma conj_roots_4 (g: SO3): z ∈ (cpoly g).roots  → (z ≠ 1 ∧ z ≠ -1) → ((cpoly g).roots.count z = 1) := by


  let P := fun w ↦ w = (z:ℂ) ∨ w = CONJ z
  set S:= (cpoly g).roots with Sdef

  intro zin notones
  by_contra  bad
  have bnd: Multiset.count z S ≥ 2 := by
    have c1: Multiset.count z S ≠ 0 := by
      simp only [S]
      apply mt Multiset.count_eq_zero.mp
      by_contra bad
      exact bad zin

    have c2: Multiset.count z S ≠ 1 := by exact bad
    omega

  have bndcnj: Multiset.count (CONJ z) S ≥ 2 := by
    rw [←conj_roots_3]
    exact bnd
  have a1: Multiset.card (Multiset.filter P S) ≤ Multiset.card S := by
    apply Multiset.card_le_card
    simp

  let Pconj := fun w ↦ w = (z:ℂ) ∧ w = CONJ z
  have a6:  Multiset.filter (· = z) S + Multiset.filter (· = CONJ z) S =
    Multiset.filter P S + Multiset.filter Pconj S := by
    simp [P, Pconj]
    exact Multiset.filter_add_filter (· = z) (· = CONJ z) S

  have a7:  Multiset.filter P S = Multiset.filter (· = z) S + Multiset.filter (· = CONJ z) S := by
    have a71: Multiset.filter Pconj S = 0 := by
      simp [Pconj]
      intro a lhs1 lhs2
      rw [lhs2]
      apply flem2 g
      exact zin
      exact notones
    rw [a71] at a6
    simp at a6
    symm at a6
    exact a6

  have a8 : Multiset.card (Multiset.filter P S) ≥ 4 := by
    rw [a7]
    rw [Multiset.card_add]
    have yy1: Multiset.filter (fun x ↦ x = z) S = Multiset.filter (fun x ↦ z = x) S := by
      apply Multiset.filter_congr
      intro x lhs
      tauto
    have yy2: Multiset.filter (fun x ↦ x = CONJ z) S = Multiset.filter (fun x ↦ CONJ z = x) S := by
      apply Multiset.filter_congr
      intro x lhs
      tauto
    rw [yy1, yy2]
    rw [←Multiset.count_eq_card_filter_eq]
    rw [←Multiset.count_eq_card_filter_eq]
    linarith


  have := le_trans a8  a1
  rw [num_roots_eq_3] at this
  simp at this




lemma conj_mul_roots (g: SO3) : z ∈ (cpoly g).roots → z * CONJ z = 1 := by
  intro lhs
  simp [CONJ]
  rw [Complex.mul_conj]
  rw [Complex.normSq_eq_norm_sq]
  simp
  left
  exact eig_norms g z lhs


lemma cast_root_mult1 (g: SO3): Polynomial.rootMultiplicity (1: ℝ) (g.val).charpoly =
  Polynomial.rootMultiplicity (1:ℂ) (Polynomial.map (algebraMap ℝ ℂ) (g.val).charpoly) := by
  have inmap: Function.Injective (algebraMap ℝ ℂ) := by
    exact RCLike.ofReal_injective
  rw  [Polynomial.eq_rootMultiplicity_map inmap (1:ℝ)]
  simp


open Polynomial
lemma same_mult (g: SO3) : rootMultiplicity 1 (LinearMap.charpoly (g_end g)) =
  rootMultiplicity 1 (map (algebraMap ℝ ℂ) (LinearMap.charpoly (g_end g))) := by
  rw [same_char]
  simp [cpoly]
  simp only [as_complex]
  rw [mapMatrix_is_map]
  rw [Matrix.charpoly_map]
  rw [same_char_0]
  exact cast_root_mult1 g




lemma idlem (g: SO3):  (cpoly g).roots.count 1 = 3 → g = 1 := by
  exact idlemAristotle g

lemma tight_space_lemma (g: SO3) :
  ((cpoly g).roots.count 1 ) + ((cpoly g).roots.count (-1))  ≥ 2
  →
  ∀w ∈ (cpoly g).roots, w = 1 ∨ w = -1 := by
  intro lhs
  by_contra other
  rw [not_forall] at other
  obtain ⟨w, pw⟩ := other
  rw [_root_.not_imp] at pw
  let P := fun w ↦ w = (1:ℂ) ∨ w = -1
  --theorem filter_add_not (s : Multiset α) : filter p s + filter (fun a => ¬p a) s = s := by
  set S:= (cpoly g).roots with Sdef
  have a1 : Multiset.filter P S + Multiset.filter (fun a ↦ ¬P a) S = S :=
    Multiset.filter_add_not P S
  have a2: Multiset.card (Multiset.filter P S + Multiset.filter (fun a ↦ ¬P a) S)  =
    Multiset.card (Multiset.filter P S) + Multiset.card (Multiset.filter (fun a ↦ ¬P a) S) := by
    apply Multiset.card_add
  have a3: Multiset.card S =
    Multiset.card (Multiset.filter P S) +
    Multiset.card (Multiset.filter (fun a ↦ ¬P a) S) := by
    nth_rewrite 1 [←a1]
    exact a2
  let Pconj := fun w ↦ w = (1:ℂ) ∧ w = -1
  have a6:  Multiset.filter (· = 1) S + Multiset.filter (· = -1) S =
    Multiset.filter P S + Multiset.filter Pconj S := by
    simp [P, Pconj]
    exact Multiset.filter_add_filter (· = 1) (· = -1) S

  have a7:  Multiset.filter P S = Multiset.filter (· = 1) S + Multiset.filter (· = -1) S := by
    have a71: Multiset.filter Pconj S = 0 := by
      simp [Pconj]
      intro a lhs1 lhs2
      rw [lhs2]
      norm_num

    rw [a71] at a6
    simp at a6
    symm at a6
    exact a6



  have a4: Multiset.card (Multiset.filter P S) ≥ 2  := by
    apply congrArg Multiset.card at a7
    simp at a7
    nth_rewrite 2 [←Multiset.countP_eq_card_filter] at a7
    nth_rewrite 2 [←Multiset.countP_eq_card_filter] at a7
    have a41 : Multiset.countP (fun x ↦ x = 1) S = Multiset.count 1 S  := by
      simp [Multiset.count]
      apply Multiset.countP_congr Sdef
      intro x _
      norm_num
      tauto

    have a42 : Multiset.countP (fun x ↦ x = -1) S = Multiset.count (-1) S  := by
      simp [Multiset.count]
      apply Multiset.countP_congr Sdef
      intro x _
      norm_num
      tauto

    rw [a41, a42] at a7
    rw [a7]
    exact lhs

  have a5: Multiset.card (Multiset.filter (fun a ↦ ¬P a) S) ≥ 2  := by
    have a51 : [w, CONJ w] ≤ Multiset.filter (fun a ↦ ¬P a) S  := by
      apply Multiset.le_iff_count.mpr
      intro a
      simp
      --have : List.count w [w, CONJ w] = 1

      have nodup: [w, CONJ w].Nodup := by
        simp
        apply flem2 g
        exact pw.left
        exact (not_or.mp pw.right)


      have a511: List.count w [w, CONJ w] = 1:= by
        apply List.count_eq_one_of_mem nodup
        simp


      have a512: List.count (CONJ w) [w, CONJ w] = 1:= by
        apply List.count_eq_one_of_mem nodup
        simp

      rcases (em (a = w)) with aw1 | aw2
      rw [aw1]
      rw [a511]
      apply Multiset.one_le_count_iff_mem.mpr
      simp
      constructor
      exact pw.left
      simp [P]
      exact (not_or.mp pw.right)

      rcases (em (a = CONJ w)) with acw1 | acw2
      rw [acw1]
      rw [a512]
      apply Multiset.one_le_count_iff_mem.mpr
      simp
      constructor
      exact conj_roots_2 g w pw.left
      simp [P]
      constructor
      by_contra bad
      apply congrArg CONJ at bad
      simp [CONJ] at bad
      exact pw.right (Or.inl bad)
      --
      by_contra bad
      apply congrArg CONJ at bad
      simp [CONJ] at bad
      exact pw.right (Or.inr bad)
      --
      have bb:List.count a [w, CONJ w] = 0 := by
        apply List.count_eq_zero.mpr
        simp
        constructor
        exact aw2
        exact acw2
      rw [bb]
      simp


    have a52: _:= Multiset.card_le_card a51
    simp at a52
    exact a52

  have a6: Multiset.card S ≥ 4 := by linarith
  simp only  [S] at a6
  rw [num_roots_eq_3] at a6
  simp at a6



lemma tight_space_lemma_2 (g: SO3) :
  ((cpoly g).roots.count 1 ) + ((cpoly g).roots.count (-1))  ≥ 2
  →
  ((cpoly g).roots.count 1 ) + ((cpoly g).roots.count (-1))  = 3 := by
  set S:= (cpoly g).roots with Sdef
  set P := fun w ↦ w = (1:ℂ) ∨ w = -1 with Pdef
  intro lhs
  --Multiset.filter_eq_self.{u_1} {α : Type u_1} {p : α → Prop} [DecidablePred p] {s : Multiset α} :
  --Multiset.filter p s = s ↔ ∀ a ∈ s, p a
  have b1: Multiset.filter P S = S := by
    apply Multiset.filter_eq_self.mpr
    exact tight_space_lemma g lhs

  let Pconj := fun w ↦ w = (1:ℂ) ∧ w = -1
  have a6:  Multiset.filter (· = 1) S + Multiset.filter (· = -1) S =
    Multiset.filter P S + Multiset.filter Pconj S := by
    simp [P, Pconj]
    exact Multiset.filter_add_filter (· = 1) (· = -1) S

  have a7:  Multiset.filter P S = Multiset.filter (· = 1) S + Multiset.filter (· = -1) S := by
    have a71: Multiset.filter Pconj S = 0 := by
      simp [Pconj]
      intro a lhs1 lhs2
      rw [lhs2]
      norm_num

    rw [a71] at a6
    simp at a6
    symm at a6
    exact a6

  have a41 : Multiset.countP (fun x ↦ x = 1) S = Multiset.count 1 S  := by
    simp [Multiset.count]
    apply Multiset.countP_congr Sdef
    intro x _
    norm_num
    tauto

  have a42 : Multiset.countP (fun x ↦ x = -1) S = Multiset.count (-1) S  := by
    simp [Multiset.count]
    apply Multiset.countP_congr Sdef
    intro x _
    norm_num
    tauto

  have : Multiset.card S = Multiset.count 1 S + Multiset.count (-1) S  := by
    nth_rewrite 1 [←b1, ←a41, ←a42]
    rw [a7]
    rw [Multiset.card_add]
    rw [Multiset.countP_eq_card_filter]
    rw [Multiset.countP_eq_card_filter]



  simp only [S] at this
  rw [num_roots_eq_3] at this
  symm
  exact this

lemma spec_lem (g: SO3) : g ≠ 1 → ((cpoly g).roots.count 1) = 1 := by

  intro gnotone
  let count := (cpoly g).roots.count 1
  have count_le_card : count ≤ 3 := by
    rw [←num_roots_eq_3]
    apply Multiset.count_le_card

  by_contra bad
  rcases (em (count = 3)) with (eq3 | neq3)
  · exact gnotone ((idlem g) eq3)
  have count_ne1: count ≠ 1 := by
    by_contra countone
    simp only [count] at countone
    exact bad countone
  let mcount := (cpoly g).roots.count (-1)
  have mcount_le_card : (mcount ≤ 3) := by
    rw [←num_roots_eq_3]
    apply Multiset.count_le_card
  rcases (em (mcount = 3)) with (meq3 | mneq3)
  have : (cpoly g).roots.prod = -1 := by
    have const: (cpoly g).roots = Multiset.ofList [-1,-1,-1] := by
      have that:mcount = (cpoly g).roots.card := by
        rwa [num_roots_eq_3]
      have :_:=  Multiset.count_eq_card.mp that
      apply Multiset.ext.mpr
      intro a
      rcases (em (a ∈ (cpoly g).roots)) with isroot | notroot
      have is_m1 :_ := this a isroot
      rw [←is_m1]
      simp [mcount] at meq3
      simp
      exact meq3
      have : Multiset.count a (cpoly g).roots = 0 := Multiset.count_eq_zero.mpr notroot
      rw [this]
      simp
      symm
      apply List.count_eq_zero.mpr
      by_contra inconst
      simp at inconst
      rw [inconst] at notroot
      have :_ :=Multiset.count_eq_zero.mpr notroot
      simp only [mcount] at meq3
      rw [this] at meq3
      norm_num at meq3


    rw [const]
    simp

  rw [det_as_prod g] at this
  norm_num at this
  --
  have mnottwo: mcount ≠ 2 := by
    by_contra mistwo
    have contrabad: ((cpoly g).roots.count 1) = 1 := by
      have : Multiset.count 1 (cpoly g).roots + Multiset.count (-1) (cpoly g).roots = 3 := by
        apply tight_space_lemma_2 g
        simp only [mcount] at mistwo
        rw [mistwo]
        simp
      simp only [mcount] at mistwo
      rw [mistwo] at this
      simp at this
      simp
      exact this
    exact bad contrabad
    --
  have mnotone: mcount ≠ 1 := by
    by_contra misone
    have negdet: (cpoly g).roots.prod = -1 := by
      rcases (em ((cpoly g).roots.count 1 ≥ 1)) with d1 | d2
      have css: ∀w ∈ (cpoly g).roots, w = 1 ∨ w = -1 := by
        apply tight_space_lemma g
        simp only [mcount] at misone
        rw [misone]
        simp
        simp at d1
        exact d1
      have css2: Multiset.count 1 (cpoly g).roots + Multiset.count (-1) (cpoly g).roots = 3 := by
        apply tight_space_lemma_2 g
        simp only [mcount] at misone
        rw [misone]
        simp
        simp at d1
        exact d1
      simp only [mcount] at misone
      rw [misone] at css2
      simp at css2
      have form : (cpoly g).roots = Multiset.ofList [-1, 1, 1] := by
        have form_le : (cpoly g).roots ≤ Multiset.ofList [-1, 1, 1]  := by
          apply Multiset.le_iff_count.mpr
          intro a
          rcases (em (a ∈ (cpoly g).roots)) with isroot | notroot
          rcases css a isroot with e1 | e2
          rw [e1]
          simp
          rw [css2]
          norm_num
          --
          rw [e2]
          rw [misone]
          norm_num
          have :_ := Multiset.count_eq_zero_of_notMem notroot
          rw [this]
          norm_num

        apply Multiset.eq_of_le_of_card_le form_le
        simp
        rw [num_roots_eq_3 g]

      rw [form]
      simp
      --
      have this: Multiset.count 1 (cpoly g).roots  = 0:= by
        linarith
      let cset := {x:ℂ | x ∈ (cpoly g).roots  ∧ (x ≠ 1  ∧ x ≠ -1)}
      have ne : ∃ z, z ∈ cset := by
        by_contra bbad
        simp at bbad
        simp only [cset] at bbad
        have: (cpoly g).roots ≤ Multiset.ofList [-1] := by
          apply Multiset.le_iff_count.mpr
          intro b
          rcases (em (b ∈ (cpoly g).roots)) with isroot | notroot
          have that:_:= bbad b
          have tt: ¬ (b ≠ 1 ∧ b ≠ -1) := by
            by_contra bbb
            exact that ⟨isroot, bbb⟩
          simp at tt
          rcases (em (b=1)) with f1 | f2
          rw [f1]
          rw [this]
          norm_num
          --
          rw [tt f2]
          simp only [mcount] at misone
          rw [misone]
          norm_num
          have :_ := Multiset.count_eq_zero_of_notMem notroot
          rw [this]
          norm_num

        have :_:=  Multiset.card_le_card this
        simp at this
        rw [num_roots_eq_3 g] at this
        norm_num at this


      set c := Classical.choose ne
      have cspec := Classical.choose_spec ne
      change c ∈ cset at cspec
      simp only [cset] at cspec
      have :_:= flem2 g cspec.left cspec.right
      have form : (cpoly g).roots = Multiset.ofList [-1, c, CONJ c] := by
        symm
        apply Multiset.eq_of_le_of_card_le
        apply Multiset.le_iff_count.mpr
        intro a
        have nodup: [-1, c, CONJ c].Nodup := by
          simp
          constructor
          constructor
          by_contra isone
          symm at isone
          exact cspec.right.right isone
          --
          by_contra bad
          have:  -1 = CONJ (-1) := by
            simp [CONJ]
          rw [this] at bad
          apply congrArg CONJ at bad
          simp at bad
          simp [CONJ] at bad
          symm at bad
          exact cspec.right.right bad
          --
          exact this
          --

        rcases (em (a = -1)) with imo | nimo
        rw [imo]
        have : List.count (-1) [-1, c, CONJ c] = 1  := by
          apply List.count_eq_one_of_mem nodup
          simp
        simp [this]
        simp [mcount] at misone
        rw [misone]
        --
        rcases (em (a = c)) with imc | nimc
        rw [imc]
        have : List.count (c) [-1, c, CONJ c] = 1  := by
          apply List.count_eq_one_of_mem nodup
          simp
        simp [this]
        have := Multiset.count_pos.mpr cspec.left
        rw [Polynomial.count_roots] at this
        linarith
        --
        rcases (em (a = CONJ c)) with imcc | nimcc
        rw [imcc]
        have : List.count (CONJ c) [-1, c, CONJ c] = 1  := by
          apply List.count_eq_one_of_mem nodup
          simp
        simp
        rw [this]
        have : CONJ c ∈  (cpoly g).roots := by
          apply conj_roots_2 g c
          exact cspec.left

        have := Multiset.count_pos.mpr this
        rw [Polynomial.count_roots] at this
        linarith
        simp
        have :List.count a [-1, c, CONJ c]=0 := by
          apply List.count_eq_zero.mpr
          simp
          constructor
          exact nimo
          constructor
          exact nimc
          exact nimcc
        rw [this]
        simp

        --
        simp
        rw [num_roots_eq_3 g]


      rw [form]
      simp
      apply conj_mul_roots
      exact cspec.left
    rw [det_as_prod g] at negdet
    norm_num at negdet

  have no_min_one: mcount = 0 := by
    omega

  let cset := {x:ℂ | x ∈ (cpoly g).roots  ∧ x ≠ 1 ∧ x ≠ -1}
  have ne : ∃ z, z ∈ cset := by
        by_contra bbad
        simp at bbad
        simp only [cset] at bbad
        have simpl: ∀ (x : ℂ),  x ∈ (cpoly g).roots → 1 = x := by
          intro x
          intro lhs
          have aa:= bbad x
          have bb: x ≠ -1 := by
            simp only [mcount] at no_min_one
            have that:= Multiset.count_eq_zero.mp no_min_one
            by_contra ism1
            rw [ism1] at lhs
            exact that lhs

          by_contra ne1
          have back: x ≠ 1 := by exact fun a ↦ ne1 (id (Eq.symm a))
          exact aa ⟨lhs, back, bb⟩
        have other:_:= Multiset.count_eq_card.mpr simpl
        rw [num_roots_eq_3] at other
        simp only [count] at neq3
        apply neq3 other





  set c := Classical.choose ne
  have cspec := Classical.choose_spec ne
  change c ∈ cset at cspec
  simp only [cset] at cspec
  have conjtoo:_:= conj_roots_2 g c (cspec.left)
  have conjdiff_c : CONJ c ≠ c := (flem2 g cspec.left cspec.right).symm

  have countnot2: count ≠ 2 := by
    by_contra countistwo
    simp only [count] at countistwo
    have horns:∀ w ∈ (cpoly g).roots, w = 1 ∨ w = -1 := by
      apply tight_space_lemma g
      rw [countistwo]
      simp
    have havemin: -1 ∈ (cpoly g).roots := by
      let cset := {x:ℂ | x ∈ (cpoly g).roots  ∧ x ≠ 1}
      have ne : ∃ z, z ∈ cset := by
        by_contra allone
        simp only [cset] at allone

        have simpl: ∀ (x : ℂ),  x ∈ (cpoly g).roots → 1 = x := by
          intro x
          intro lhs
          symm
          by_contra ne1
          have : ∃ z, z ∈ {x | x ∈ (cpoly g).roots ∧ x ≠ 1} := by
            use x
            exact ⟨lhs, ne1⟩
          exact allone this

        have other:_:= Multiset.count_eq_card.mpr simpl
        rw [num_roots_eq_3] at other
        simp only [count] at neq3
        apply neq3 other

      set c := Classical.choose ne
      have cspec := Classical.choose_spec ne
      change c ∈ cset at cspec
      simp only [cset] at cspec
      have :_:=horns c cspec.left
      rcases  this with e1 | e2
      exfalso
      rw [e1] at cspec
      simp at cspec
      rw [e2] at cspec
      exact cspec.left
    simp only [mcount] at no_min_one

    have bbad:_:= Multiset.count_ne_zero.mpr havemin
    rw [no_min_one] at bbad
    norm_num at bbad

  have countnot0: count ≠ 0 := by
    by_contra countiszero
    let cset2 := {x:ℂ | x ∈ (cpoly g).roots  ∧ x ≠ 1  ∧ x ≠ -1 ∧ x ≠ c ∧ x ≠ CONJ c}
    have ne2 : ∃ z, z ∈ cset2 := by
      by_contra bbbad
      simp at bbbad
      simp only [cset2] at bbbad
      have : (cpoly g).roots ≤ Multiset.ofList [c, CONJ c] := by
        apply Multiset.le_iff_count.mpr
        intro a
        rcases (em (a = 1)) with a1 | a2
        --
        rw [a1]
        simp only [count] at countiszero
        rw [countiszero]
        simp
        --
        rcases (em (a = -1)) with ma1 | ma2
        rw [ma1]
        simp only [mcount] at no_min_one
        rw [no_min_one]
        simp
        --
        have cmult:((cpoly g).roots.count c = 1) := by
          apply conj_roots_4
          exact cspec.left
          exact cspec.right
        rcases (em (a = c)) with ca1 | ca2
        rw [ca1]
        rw [cmult]
        simp
        --
        rcases (em (a = CONJ c)) with cca1 | cca2
        rw [cca1]
        have cmultc:((cpoly g).roots.count (CONJ c) = 1) := by
          rw [←conj_roots_3]
          exact cmult
        rw [cmultc]
        simp
        --
        have : Multiset.count a (cpoly g).roots = 0 := by
          apply Multiset.count_eq_zero.mpr
          by_contra isroot
          exact bbbad a ⟨isroot, a2, ma2, ca2, cca2⟩
        rw [this]
        simp

      have := Multiset.card_le_card this
      rw [num_roots_eq_3] at this
      simp at this



    set c2 := Classical.choose ne2
    have cspec2 := Classical.choose_spec ne2
    change c2 ∈ cset2 at cspec2
    simp only [cset2] at cspec2
    have conjtoo2:_:= conj_roots_2 g c2 (cspec2.left)
    let big:= Multiset.ofList [c, CONJ c, c2, CONJ c2]
    have nodup: [c, CONJ c, c2, CONJ c2].Nodup := by
      simp
      constructor
      constructor
      by_contra eq
      symm at eq
      exact conjdiff_c eq
      --
      constructor
      by_contra eqcs
      symm at eqcs
      exact cspec2.right.right.right.left eqcs
      --
      by_contra eqcs
      apply congrArg CONJ at eqcs
      simp [CONJ] at eqcs
      change CONJ c = c2 at eqcs
      symm at eqcs
      exact cspec2.right.right.right.right eqcs
      --
      constructor
      constructor
      --
      by_contra bbb
      symm at bbb
      exact cspec2.right.right.right.right bbb
      ---
      by_contra bbb
      simp [CONJ] at bbb
      have so: c = c2 := by
        apply star_inj.mp
        exact bbb

      symm at so
      exact cspec2.right.right.right.left so
      ---
      apply flem2 g
      exact cspec2.left
      --
      constructor
      exact cspec2.right.left
      --
      exact cspec2.right.right.left



    have bigsub : big ≤ (cpoly g).roots := by
      simp [big]
      apply Multiset.le_iff_count.mpr
      intro w
      rw [Multiset.coe_count]
      rcases (em (w = c ∨ w = c2 ∨ w = CONJ c ∨ w = CONJ c2) ) with r1 | r2
      rcases r1 with r11 | r12 | r13 | r14
      rw [r11]
      have :List.count c ↑[c, CONJ c, c2, CONJ c2] = 1 := by
        apply List.count_eq_one_of_mem
        exact nodup
        --
        simp
      rw [this]
      apply Multiset.one_le_count_iff_mem.mpr
      exact cspec.left
      --
      rw [r12]
      have :List.count c2 ↑[c, CONJ c, c2, CONJ c2] = 1 := by
        apply List.count_eq_one_of_mem
        exact nodup
        --
        simp
      rw [this]
      apply Multiset.one_le_count_iff_mem.mpr
      exact cspec2.left
      --
      rw [r13]
      have :List.count (CONJ c) ↑[c, CONJ c, c2, CONJ c2] = 1 := by
        apply List.count_eq_one_of_mem
        exact nodup
        --
        simp
      rw [this]
      apply Multiset.one_le_count_iff_mem.mpr
      exact conjtoo
      --
      rw [r14]
      have :List.count (CONJ c2) ↑[c, CONJ c, c2, CONJ c2] = 1 := by
        apply List.count_eq_one_of_mem
        exact nodup
        --
        simp
      rw [this]
      apply Multiset.one_le_count_iff_mem.mpr
      exact conjtoo2
      ---
      have : List.count w [c, CONJ c, c2, CONJ c2] = 0 := by
        apply List.count_eq_zero.mpr
        simp
        tauto

      rw [this]
      simp

    have card_bound: big.card ≤ (cpoly g).roots.card  := by
      apply Multiset.card_le_card
      simp [bigsub]
    have : 4 ≤ (cpoly g).roots.card  := by
      simp [big] at card_bound
      exact card_bound
    linarith [this, (num_roots_eq_3 g)]


  omega


---------







lemma K_id (g: SO3): K g = ((g_end g).eigenspace 1) := by
  ext w
  simp [K, Module.End.eigenspace]
  simp [kermap, g_end]
  simp [to_R3_linear, ofLp_linear]
  constructor
  ----
  intro lhs
  simp [kermap_raw] at lhs
  simp [g_end_raw]
  rw [sub_eq_iff_eq_add] at lhs
  simp at lhs
  rw [lhs]
  ----
  intro lhs
  simp [kermap_raw]
  rw [sub_eq_iff_eq_add]
  simp
  simp [g_end_raw] at lhs
  apply congrArg WithLp.ofLp at lhs
  simp at lhs
  exact lhs



lemma dim_ker (g: SO3): g ≠1 → Module.finrank ℝ (K g) ≤ 1 := by
  intro gnotone
  have bnd: Module.finrank ℝ (K g)  ≤ (g_end g).charpoly.rootMultiplicity 1 := by
    rw [K_id]
    exact LinearMap.finrank_eigenspace_le (g_end g) 1
  have :_:= spec_lem g gnotone
  simp at this
  rw [←same_char g] at this
  rw [←same_mult g] at this
  rw [this] at bnd
  exact bnd



lemma fixed_lemma (g: SO3) : g≠1 → ({x ∈ S2 | g • x = x} = ∅ ∨ Nat.card ({x ∈ S2 | g • x = x}) = 2) := by
  intro notone
  have bnd: _:= dim_ker g notone
  rcases (Nat.le_one_iff_eq_zero_or_eq_one.mp bnd) with dim0 | dim1
  left
  have zerocons:_:= Module.finrank_eq_zero_iff.mp dim0
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x
  by_contra xins
  have xinsr := xins.right
  have inK: x ∈ K g := by
    simp [K]
    simp [kermap]
    simp [to_R3_linear, ofLp_linear]
    simp [kermap_raw]
    rw [sub_eq_iff_eq_add]
    simp
    rw [SO3_smul_def g x] at xinsr
    have : (to_R3 ((g.val).mulVec x.ofLp)).ofLp = x.ofLp := by
      apply congrArg WithLp.ofLp at xinsr
      exact xinsr
    simp [to_R3] at this
    exact this

  set X: K g:= ⟨x, inK⟩ with Xdef
  have apped: _:=zerocons X
  obtain ⟨a, pa⟩ := apped
  have isz :_:= (smul_eq_zero_iff_right pa.left).mp pa.right
  simp at isz
  apply congrArg (fun x ↦ x.val) at isz
  rw [Xdef] at isz
  simp at isz
  rw [isz] at xins
  simp [S2] at xins

  --

  right
  apply Nat.card_eq_two_iff.mpr


  let cset := {x | x ∈ K g  ∧ x ≠ 0}
  have ne  : ∃ z, z ∈ cset  := by
    haveI : NoZeroSMulDivisors ℝ (K g) := inferInstance
    have pos : 0 < Module.finrank ℝ (K g) := by
      rw [dim1]
      norm_num
    have : ∃x : K g, x ≠ 0 := by
      apply (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := K g)).mp
      exact pos
    obtain ⟨x, hx⟩ := this
    use x.val
    simp [cset]
    exact hx


  let nz : K g :=
    let c := Classical.choose ne
    have cspec := Classical.choose_spec ne
    ⟨c, cspec.left⟩


  have is_nz : nz  ≠ 0 := by
    simp [nz]
    exact (Classical.choose_spec ne).right

  have isspan :
    (Submodule.span ℝ {nz} = (⊤: Submodule ℝ (K g))) := by
    exact (finrank_eq_one_iff_of_nonzero nz is_nz).mp (dim1)

  let el: R3 := nz.val
  let el_neg: R3 := -el
  have el_nz : el ≠ 0 := by
    simp [el]
    exact is_nz
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
    have prop :_:=  nz.property
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

  have cconj:  el_normed ∈ S2 ∧ g • el_normed = el_normed := ⟨el_normed_in_s2, el_normed_fixed⟩
  have cconj_neg:  el_normed_neg ∈ S2 ∧ g • el_normed_neg = el_normed_neg :=
    ⟨el_normed_neg_in_s2, el_normed_neg_fixed⟩
  let F: {x | x ∈ S2 ∧ g • x = x} := ⟨el_normed, cconj⟩
  let Fneg: {x | x ∈ S2 ∧ g • x = x} := ⟨el_normed_neg, cconj_neg⟩
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


  have ininsp: ⟨k, inker⟩ ∈  Submodule.span ℝ {nz} := by
    rw [isspan]
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
