import Mathlib
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Charpoly.Basic

import BanachTarski.Common


set_option linter.all false
set_option maxHeartbeats 1000000


noncomputable def as_complex (M: MAT) : Matrix (Fin 3) (Fin 3) ℂ := (algebraMap ℝ ℂ).mapMatrix M

noncomputable def cpoly (g: SO3) := Matrix.charpoly (as_complex g.val)

lemma cpoly_coef_real (g: SO3) : ∀i: ℕ, ∃x: ℝ, x = (cpoly g).coeff i := by sorry




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




#check Matrix.mem_spectrum_of_isRoot_charpoly
lemma eig_norms (g: SO3) (z:ℂ) : z ∈ (cpoly g).roots → ‖z‖ = 1 := sorry
#check Complex.mul_conj

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



#check Complex.mul_conj
lemma conj_mul_roots (g: SO3) : z ∈ (cpoly g).roots → z * CONJ z = 1 := by
  intro lhs
  simp [CONJ]
  rw [Complex.mul_conj]
  rw [Complex.normSq_eq_norm_sq]
  simp
  left
  exact eig_norms g z lhs
lemma idlem (g: SO3):  (cpoly g).roots.count 1 = 3 → g = 1 := sorry

lemma tight_space_lemma (g: SO3) :
  ((cpoly g).roots.count 1 ) + ((cpoly g).roots.count (-1))  ≥ 2
  →
  ∀w ∈ (cpoly g).roots, w = 1 ∨ w = -1 := sorry

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
      have : ∀w ∈ (cpoly g).roots, w = 1 ∨ w = -1 := by
        apply tight_space_lemma g
        simp only [mcount] at mistwo
        rw [mistwo]
        simp
      by_contra notone
      sorry
    exact bad contrabad
    --
  have mnotone: mcount ≠ 1 := by
    by_contra misone
    have negdet: (cpoly g).roots.prod = -1 := by
      rcases (em ((cpoly g).roots.count 1 ≥ 1)) with d1 | d2
      have : ∀w ∈ (cpoly g).roots, w = 1 ∨ w = -1 := by
        apply tight_space_lemma g
        simp only [mcount] at misone
        rw [misone]
        simp
        simp at d1
        exact d1
      have form : (cpoly g).roots = Multiset.ofList [-1, 1, 1] := sorry
      rw [form]
      simp
      --
      have this: Multiset.count 1 (cpoly g).roots  = 0:= by
        linarith
      let cset := {x:ℂ | x ∈ (cpoly g).roots  ∧ (x ≠ 1  ∧ x ≠ -1)}
      have ne : ∃ z, z ∈ cset := sorry
      set c := Classical.choose ne
      have cspec := Classical.choose_spec ne
      change c ∈ cset at cspec
      simp only [cset] at cspec
      have :_:= flem2 g cspec.left cspec.right
      have form : (cpoly g).roots = Multiset.ofList [-1, c, CONJ c] := sorry
      rw [form]
      simp
      apply conj_mul_roots
      exact cspec.left
    rw [det_as_prod g] at negdet
    norm_num at negdet

  have no_min_one: mcount = 0 := by
    omega

  let cset := {x:ℂ | x ∈ (cpoly g).roots  ∧ x ≠ 1 ∧ x ≠ -1}
  have ne : ∃ z, z ∈ cset := sorry
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
      have ne : ∃ z, z ∈ cset := sorry
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
    let cset2 := {x:ℂ | x ∈ (cpoly g).roots  ∧ x ≠ 1  ∧ x ≠ -1 ∧ x ≠ c}
    have ne2 : ∃ z, z ∈ cset2 := sorry
    set c2 := Classical.choose ne2
    have cspec2 := Classical.choose_spec ne2
    change c2 ∈ cset2 at cspec2
    simp only [cset2] at cspec2
    have conjtoo2:_:= conj_roots_2 g c2 (cspec2.left)
    let big:= Multiset.ofList [c, CONJ c, c2, CONJ c2]
    have nodup: [c, CONJ c, c2, CONJ c2].Nodup := sorry
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

noncomputable def ofLp_linear : R3 →ₗ[ℝ] R3_raw := (WithLp.linearEquiv 2 ℝ R3_raw).toLinearMap

noncomputable def to_R3_linear : R3_raw →ₗ[ℝ] R3 := (WithLp.linearEquiv 2 ℝ R3_raw).symm.toLinearMap


noncomputable def g_end_raw (g: SO3): Module.End ℝ R3_raw := Matrix.toLin' g.val
noncomputable def g_end (g: SO3) : Module.End ℝ R3 := to_R3_linear.comp ((g_end_raw g).comp ofLp_linear)

def kermap_raw (g: SO3) : R3_raw →ₗ[ℝ] R3_raw := Matrix.toLin' (g.val - 1)
noncomputable def kermap (g: SO3) : R3 →ₗ[ℝ] R3 := to_R3_linear.comp ((kermap_raw g).comp ofLp_linear)

noncomputable def K (g: SO3): Submodule ℝ R3 := LinearMap.ker (kermap g)


open Polynomial
lemma same_char (g: SO3) : (LinearMap.charpoly (g_end g)).map (algebraMap ℝ ℂ) = cpoly g := by
  simp [cpoly]
  simp only [as_complex]
  sorry


lemma same_mult (g: SO3) : rootMultiplicity 1 (LinearMap.charpoly (g_end g)) =
  rootMultiplicity 1 (map (algebraMap ℝ ℂ) (LinearMap.charpoly (g_end g))) := by
    simp
    sorry



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



#check LinearMap.finrank_range_add_finrank_ker
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
