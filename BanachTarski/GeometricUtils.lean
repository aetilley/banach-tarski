import Mathlib


import BanachTarski.Rot
import BanachTarski.Common



-- The interval [0, π/2]
def IccT := {x: ℝ // x ∈ (Set.Icc (0 : ℝ) (Real.pi/2 : ℝ))}

instance interval_uncountable : Uncountable IccT := by
  by_contra notunc
  have type_countable:_ := not_uncountable_iff.mp notunc
  have icc_countable :_:= Set.countable_coe_iff.mp type_countable
  have bad :_ := Cardinal.Real.Icc_countable_iff.mp icc_countable
  linarith [Real.pi_pos]

noncomputable def to_s2_r3 : IccT → R3 := fun θ ↦ to_R3 ![Real.cos θ.val, Real.sin θ.val, 0]

def is_s2 (θ : IccT) : to_s2_r3 θ ∈ S2 := by
  simp [to_s2_r3]
  simp [S2]
  simp [to_R3]
  simp [norm]
  norm_num
  rw [Fin.sum_univ_three]
  norm_num
  simp

noncomputable def to_s2 : IccT → S2 := fun θ ↦ ⟨to_s2_r3 θ, is_s2 θ⟩

lemma ih : Function.Injective to_s2 := by
  simp [Function.Injective]
  intro a b haeqhb
  simp [to_s2, to_s2_r3] at haeqhb
  simp [to_R3] at haeqhb
  have ios:_:= Real.injOn_sin
  simp [Set.InjOn] at ios
  have ap:_ := a.property
  have bp:_ := b.property
  simp only [Set.Icc] at ap
  have c1 :_:= (Set.mem_setOf.mp ap).left
  have c2 :_:= (Set.mem_setOf.mp ap).right
  have c1 :_:= (Set.mem_setOf.mp bp).left
  have c2 :_:= (Set.mem_setOf.mp bp).right
  have a1: -(Real.pi / 2) ≤ a.val := by linarith
  have a2: a.val ≤ (Real.pi / 2)  := by linarith
  have b1: -(Real.pi / 2) ≤ b.val := by linarith
  have b2: b.val ≤ (Real.pi / 2)  := by linarith
  exact Subtype.ext (ios a1 a2 b1 b2 haeqhb.right)

lemma s2_uncountable : Uncountable (S2) := by
  apply Function.Injective.uncountable ih

lemma lb_card_s2 : Cardinal.aleph0 < Cardinal.mk S2 := Cardinal.aleph0_lt_mk_iff.mpr s2_uncountable

abbrev MAT1 := Matrix (Fin 3) (Fin 1) ℝ

def v2m (v : R3_raw) : MAT1 := !![(v 0); (v 1); (v 2);]

lemma dot_as_matmul (u v : R3_raw) : u  ⬝ᵥ v = (((v2m u).transpose) * (v2m v)) 0 0 := by
  simp only [dotProduct]
  simp only [v2m]
  simp only [Matrix.mul_apply]
  rw [Fin.sum_univ_three]
  rw [Fin.sum_univ_three]
  simp




lemma v2m_equiv (M : MAT) (v : R3_raw) : v2m (Matrix.mulVec M v) = M * (v2m v) := by
  simp [v2m]
  ext i j
  fin_cases j
  fin_cases i
  <;> simp
  <;> simp only [Matrix.mul_apply]
  <;> simp only [Matrix.mulVec]
  <;> simp only [dotProduct]
  <;> rw [Fin.sum_univ_three]
  <;> rw [Fin.sum_univ_three]
  <;> simp



lemma dp_nonneg (v : R3_raw) : v ⬝ᵥ v ≥ 0 := by
  simp [dotProduct]
  rw [Fin.sum_univ_three]
  repeat rw [←sq]
  apply add_nonneg
  · apply add_nonneg
    · exact sq_nonneg (v 0)
    · exact sq_nonneg (v 1)
  · exact sq_nonneg (v 2)



lemma so3_cancel_lem {g : SO3} : (g.val.transpose) * g = 1 := by
  have g_special:_:= g.property
  simp only [SO3] at g_special
  rw [Matrix.mem_specialOrthogonalGroup_iff] at g_special
  rw [Matrix.mem_orthogonalGroup_iff] at g_special
  have sss:_:= Matrix.inv_eq_right_inv g_special.left
  have isinv : Invertible g.val := by
    apply Matrix.invertibleOfRightInverse
    exact g_special.left

  have triv : (g.val)⁻¹ * g.val = 1 := by
    exact Matrix.inv_mul_of_invertible g.val

  rw [sss] at triv
  exact triv

lemma so3_fixes_norm : ∀g : SO3, ∀x : R3, ‖g • x‖ = ‖x‖ := by
  intro g x
  rw [norm_eq_sqrt_real_inner]

  rw [norm_eq_sqrt_real_inner]

  apply congrArg

  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp

  change ((Matrix.mulVec g x.ofLp): R3_raw) ⬝ᵥ ((Matrix.mulVec g x.ofLp): R3_raw) = ‖x‖ ^ 2

  let P : R3_raw := (g : MAT).mulVec x.ofLp

  rw [dot_as_matmul]

  rw [v2m_equiv]
  rw [Matrix.transpose_mul]
  rw [Matrix.mul_assoc]
  nth_rewrite 2 [←Matrix.mul_assoc]

  rw [so3_cancel_lem]

  simp
  rw [←dot_as_matmul]

  rw [norm_eq_sqrt_real_inner]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp
  rw [Real.sq_sqrt]
  exact dp_nonneg x.ofLp


lemma so3_fixes_s2 : ∀g : SO3, (f g) '' S2 ⊆ S2 := by
  intro g z
  simp
  intro x
  simp [S2]
  intro lhs1 lhs2
  rw [←lhs2]
  simp [f]
  rw [so3_fixes_norm g]
  exact lhs1


------------------

lemma triv_so3 : (f (1 : SO3)) = (fun x : R3 ↦ x) := by
  ext x
  simp [f]

def orbit {X : Type*} {G : Type*} [Group G] [MulAction G X] (g : G) (S : Set X) : Set X :=
⋃ i, (f g)^[i] '' S


lemma rot_containment_S2 : ∀ {axis : S2} {θ : ℝ}, (f (rot axis θ)) '' S2 ⊆ S2 := by
  intro axis θ
  simp only [f]
  exact so3_fixes_s2 (rot axis θ)

lemma rot_containment_general (axis : S2) (subset_of_s2 : S ⊆ S2) :
  (∀r : ℝ, (orbit (rot axis r) S ⊆ S2)) := by
  intro r
  simp [orbit]
  intro i
  induction i with
  | zero =>
    simp
    exact subset_of_s2
  | succ i pi =>
    intro s s_in_S
    simp
    rw [←Function.iterate_succ_apply]
    rw [Function.iterate_succ_apply']
    let w := ((f (rot axis r))^[i] s)
    have lem: w ∈ S2 := by
      exact pi s_in_S
    have mem:f (rot axis r) w ∈ f (rot axis r) '' S2 := Set.mem_image_of_mem (f (rot axis r)) lem
    have lem2: f (rot axis r) w ∈ S2 := rot_containment_S2 mem
    exact lem2

--------


def BadEl {X : Type*} {G : Type*} [Group G] [MulAction G X] (g : G) (S : Set X) : Prop :=
  ∃n : ℕ, n > 0 ∧ ∃s ∈ S, (f g)^[n] s ∈ S

def Bad {X : Type*} {G : Type*} [Group G] [MulAction G X] (F : ℝ → G) (S : Set X) : Set ℝ :=
{θ : ℝ | (BadEl (F θ) S)}


lemma collapse_iter {X : Type*} {G : Type*} [Group G] [MulAction G X] (g h : G) (n : ℕ) :
-- Note: ` (f (g * g * h⁻¹))^[n] = (f h) ∘ (f g)^[n] ∘ (f (h⁻¹))
(@f X G _ _ (h * g * h⁻¹))^[n] = (@f X G _ _ h) ∘ (@f X G _ _ g) ^[n] ∘ (@f X G _ _ (h⁻¹)) := by
  induction n with
  | zero =>
    simp
    ext x
    simp [f]
  | succ k ih =>
    ext x
    simp
    rw [ih]
    simp [f]
    apply congrArg
    rw [smul_smul]
    rw [←mul_assoc]
    rw [←mul_assoc]
    simp
    rw [←smul_smul]



lemma conj_bad_el {X : Type*} {G : Type*} [Group G] [MulAction G X] (g h : G) (S : Set X) :
   (BadEl g S) ↔ (BadEl (h * g * h⁻¹) ((f h) '' S)) := by
    constructor
    · intro lhs
      simp [BadEl] at lhs
      simp [BadEl]
      obtain ⟨n, npos, s, sinS, ps⟩ := lhs
      use n
      constructor
      · exact npos
      · rw [collapse_iter]
        use s
        constructor
        · exact sinS
        · simp [f]
          exact ps
    · intro lhs
      simp [BadEl] at lhs
      simp [BadEl]
      obtain ⟨n, npos, s, sinS, ps⟩ := lhs
      use n
      constructor
      · exact npos
      · rw [collapse_iter] at ps
        simp [f] at ps
        use s


def BadAtN {X : Type*} {G : Type*} [Group G] [MulAction G X] (F : ℝ → G) (S : Set X) (s t : S)
  (n : ℕ) : Set ℝ :=
  {θ : ℝ | (f (F θ))^[n+1] s.val = t.val}

def BadAtN_rot (ax : S2) (S : Set R3) (s t : S) (n : ℕ) : Set ℝ :=
  {θ : ℝ | (f (rot ax θ))^[n+1] s.val = t.val}


def BadAtN_rot_iso (ax : S2) (S : Set R3) (s t : S) (n : ℕ) : Set ℝ :=
  {θ : ℝ | (rot_iso ax θ)^[n+1] s.val = t.val}




lemma rot_iso_comp_add (ax : S2) (t1 t2 : ℝ) :
  (rot_iso ax t1) ∘ (rot_iso ax t2) = (rot_iso ax (t1 + t2)) := by
    funext w
    simp [rot_iso]
    exact rot_by_parts_comp ax t1 t2

lemma rot_iso_power_lemma (axis : S2) (r : ℝ) (n : ℕ) :
(rot_iso axis r)^[n] = (rot_iso axis ((n: ℝ)*r)) := by
  induction n with
  | zero =>
    simp
    rw [triv_rot_iso axis]
    rfl
  | succ k ih =>
    rw [Function.iterate_succ']
    rw [ih]
    rw [rot_iso_comp_add ]
    apply congrArg
    apply congrArg

    simp only [Nat.cast_add, Nat.cast_one]
    linarith

lemma rot_iso_fixed_gen (axis : S2) (v w : R3) :
(((operp axis v) ≠ 0) ) ∧ (rot_iso axis t) v = w →
  ∃k : ℤ, t = (ang_diff axis v w).toReal + (k : ℝ) * 2 * Real.pi := by

    rintro ⟨nzv, lhs⟩

    simp [rot_iso] at lhs
    simp [rot_by_parts] at lhs
    apply congrArg (operp axis) at lhs
    rw [operp_add] at lhs
    rw [operp_up] at lhs
    rw [operp_spar] at lhs
    simp at lhs
    simp [rot_iso_plane_to_st] at lhs
    simp [rot_iso_plane_equiv] at lhs
    simp [ang_diff]
    have l2:  (1:ℝ) • ((plane_o axis).rotation ↑t) (operp axis v) = operp axis w  := by
      simp
      exact lhs

    have nzw : (operp axis w) ≠ 0 := by
      by_contra iszer
      rw [iszer] at lhs
      simp at lhs
      exact nzv lhs

    --
    have  : (plane_o axis).oangle (operp axis v) (operp axis w) = ↑t := by

      apply ((plane_o axis).oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero nzv nzw ↑t).mpr
      use 1
      constructor
      · simp
      exact l2.symm
    rw [this]
    rw [Real.Angle.toReal_coe]

    use (toIocDiv Real.two_pi_pos (-Real.pi) t )
    -- theorem toIcoMod_add_toIcoDiv_zsmul (a b : α) : toIcoMod hp a b + toIcoDiv hp a b • p = b
    have : toIocMod Real.two_pi_pos (-Real.pi) t +
      toIocDiv Real.two_pi_pos (-Real.pi) t • (2 * Real.pi) = t  := by
        apply toIocMod_add_toIocDiv_zsmul

    symm
    rw [zsmul_eq_mul] at this
    rw [mul_assoc]
    exact this



lemma rot_iso_fixed (axis : S2) (v : R3) :
  ((operp axis v) ≠ 0) ∧ (rot_iso axis t) v = v → ∃k : ℤ, t = k * 2 * Real.pi := by
  intro ⟨nzv, eqq⟩
  have :_:= rot_iso_fixed_gen axis v v ⟨nzv, eqq⟩
  have z: (ang_diff axis v v) = 0 := by
    simp [ang_diff]
  rw [z] at this
  simp at this
  exact this






lemma BadAtN_rot_iso_equiv (axis : S2) : ∀S : Set R3, ∀(s t : S), ∀n : ℕ, S ⊆ S2 →
  (operp axis s) ≠ 0 → (BadAtN_rot_iso axis S s t n) ⊆
  {θ : ℝ | ∃k : ℤ, ((n + 1 : ℝ) * θ) = k * (2 * Real.pi) + (ang_diff axis s t).toReal} := by
  rintro S s t n s_sub_s2 nzs
  simp [BadAtN_rot_iso]
  intro θ
  rw [←Function.iterate_succ_apply ((rot_iso axis θ)) n s.val]


  rw [rot_iso_power_lemma]
  intro lhs
  have :_:= rot_iso_fixed_gen axis s t ⟨nzs, lhs⟩
  obtain ⟨k, pk⟩ := this
  use k
  simp at pk
  rw [pk]
  linarith

lemma same_bad (ax : S2) (S : Set R3) (s t : S) (n : ℕ) :
BadAtN_rot ax S s t n = BadAtN_rot_iso ax S s t n := by
  simp [BadAtN_rot, BadAtN_rot_iso]
  ext θ
  simp
  rw [←Function.iterate_succ_apply]
  rw [←Function.iterate_succ_apply]
  rw [rot_pow_lemma]
  rw [rot_iso_pow_lemma]
  simp
  simp [f]
  set T := (↑n + 1) * θ  with Tdef
  rw [same_thing ax]


def BadAt {X : Type*} {G : Type*} [Group G] [MulAction G X] (F : ℝ → G) (S : Set X) (s t : S) :
  Set ℝ :=
  ⋃ n : ℕ,  BadAtN F S s t n

lemma bad_as_union {X : Type*} {G : Type*} [Group G] [MulAction G X] (F : ℝ → G) (S : Set X) :
  Bad F S = (⋃ s :S, ⋃ t : S, (BadAt F S s t)) := by
    simp only [Bad]
    ext x
    constructor
    · intro lhs
      simp at lhs
      simp [BadEl] at lhs
      obtain ⟨n, ⟨npos, ⟨s, sinS, ps⟩⟩⟩ := lhs
      simp
      use s
      use sinS
      use (f (F x))^[n] s
      use ps
      simp [BadAt]
      use n-1
      simp [BadAtN]
      have nform: n.pred.succ = n := by
        apply Nat.succ_pred
        linarith

      rw [←nform]
      simp
    · intro lhs
      simp [BadAt] at lhs
      simp [BadEl]
      obtain ⟨s, sinS, t, tinS, pst⟩ := lhs
      obtain ⟨n, xinbadat⟩ := pst
      use n + 1
      constructor
      · simp
      · use s
        constructor
        · exact sinS
        · simp [BadAtN] at xinbadat
          rw [Function.iterate_succ]
          simp
          rw [xinbadat]
          exact tinS



lemma bad_as_union_rot (axis : S2) : ∀S : Set R3, S ⊆ S2 →
  Bad (rot axis) S = ⋃ s :S, ⋃ t : S, ⋃ n : ℕ, BadAtN (rot axis) S s t n  := by
  intro S s_sub_s2
  rw [bad_as_union]
  simp [BadAt]



lemma BadAtN_rot_iso_countable (axis : S2) (S : Set R3) : ∀ (s t : S),
(S ⊆ S2 ∧ (axis.val ∉ S ∧ -axis.val ∉ S)) →
(BadAtN_rot_iso axis S s t n).Countable := by

    rintro s t ⟨s_sub_s2, axis_nin_s⟩
    have better:
      {θ : ℝ | ∃k : ℤ, ((n + 1 : ℝ) * θ) =
        k * (2 * Real.pi) + (ang_diff axis s t).toReal}.Countable := by


      let foo (k : ℤ) := ((k : ℝ) * (2 * Real.pi) + (ang_diff axis s t).toReal)/ (n + 1 : ℝ)
      have imlem : {θ | ∃ k : ℤ, (↑n + 1) * θ =
        ↑k * (2 * Real.pi) + ↑(ang_diff axis ↑s ↑t).toReal} =
        foo '' (Set.univ: Set ℤ) := by

        ext t
        simp
        simp [foo]
        field_simp
        constructor
        · intro lhs
          obtain ⟨k, pk⟩ := lhs
          use k
          rw [pk]
          linarith
        · intro lhs
          obtain ⟨k, pk⟩ := lhs
          use k
          rw [←pk]
          simp
          linarith

      rw [imlem]
      apply Set.Countable.image
      exact Set.countable_univ

    have nzs : (operp axis s) ≠ 0 := by
      by_contra bad
      simp [operp] at bad
      simp [orth] at bad
      apply  Submodule.mem_span_singleton.mp at bad
      obtain ⟨a, pa⟩ := bad
      have paold := pa
      apply congrArg (‖·‖) at pa
      simp [norm_smul] at pa
      have ins2:_:= s_sub_s2 s.property
      simp only [S2] at ins2
      simp only [Metric.sphere] at ins2
      simp at ins2
      rw [ins2 ] at pa
      rcases eq_or_eq_neg_of_abs_eq pa with pos | neg
      · rw [pos] at paold
        simp at paold
        rw [paold] at axis_nin_s
        simp at axis_nin_s
      · rw [neg] at paold
        simp at paold
        rw [paold] at axis_nin_s
        simp at axis_nin_s


    have sub:_ := BadAtN_rot_iso_equiv axis S s t n s_sub_s2 nzs

    exact better.mono sub





lemma countable_bad_rots : ∀S : Set R3, ∀ axis : S2,
  S ⊆ S2 ∧ Countable S ∧ (axis.val ∉ S ∧ -axis.val ∉ S)  →
  Countable (Bad (rot axis) S) := by

  rintro S axis ⟨s_sub_s2, countable_s, noaxes⟩

  rw [bad_as_union_rot axis S s_sub_s2]
  apply Set.countable_iUnion
  intro s
  apply Set.countable_iUnion
  intro t
  apply Set.countable_iUnion
  intro n
  change (BadAtN_rot axis S s t n).Countable
  rw [same_bad]
  exact BadAtN_rot_iso_countable axis S s t ⟨s_sub_s2, noaxes⟩


--------


def ToEquivSO3 (g : SO3) : R3 ≃ R3 :=
  let lin_eq := Matrix.toLinearEquiv' g.val (so3_has_inv g)
  {
    toFun := fun x : R3 => to_R3 (lin_eq.toFun x.ofLp)
    invFun := fun x : R3 => to_R3 (lin_eq.invFun x.ofLp)
    left_inv := by
      intro x
      simp only [to_R3]
      rw [lin_eq.left_inv]
    right_inv := by
      intro x
      simp only [to_R3]
      rw [lin_eq.right_inv]
  }



-- Group of Isometries of R3.
abbrev G3 : Type := R3 ≃ᵢ R3


lemma so3_diff_lin (g : SO3) (x y : R3) : ((g • x) -  g • y) =  g • (x - y) := by
  simp only [HSMul.hSMul, SMul.smul]
  simp
  rw [←WithLp.toLp_sub]
  apply congrArg
  simp [Matrix.mulVec_sub]


lemma isometry_of_so3 (g : SO3) : Isometry ((f g) : R3 → R3) := by
  simp [Isometry]
  intro x y
  rw [edist_dist]
  rw [edist_dist]
  apply congrArg
  simp [f]
  rw [dist_eq_norm_sub]
  rw [so3_diff_lin]
  rw [so3_fixes_norm]
  rw [←dist_eq_norm_sub]

def SO3_into_G3 : SO3 → G3 := fun (g : SO3) ↦ ⟨(ToEquivSO3 g), isometry_of_so3 g⟩



def SO3_in_G3 : Subgroup G3 where
  carrier: Set G3 := SO3_into_G3 '' (Set.univ: Set SO3)
  mul_mem' := by
    intro x y xinDom yinDom
    simp [SO3_into_G3] at *
    obtain ⟨ax, bx, pabx⟩ := xinDom
    obtain ⟨ay, bi, paby⟩ := yinDom
    let p := ax * ay
    use p
    have memprod: p ∈ SO3 := SO3.mul_mem bx bi
    use memprod
    simp [p]
    rw [←pabx]
    rw [←paby]
    apply IsometryEquiv.ext_iff.mpr
    intro z
    simp
    simp [ToEquivSO3]
    apply congrArg
    simp [to_R3]



  one_mem' := by
    simp
    use 1
    use SO3.one_mem
    simp [SO3_into_G3]
    apply IsometryEquiv.ext_iff.mpr
    intro z
    simp
    simp [ToEquivSO3]
    simp [to_R3]


  inv_mem' := by
    intro x xinDom
    simp [SO3_into_G3] at *
    obtain ⟨ax, bx, pabx⟩ := xinDom
    use ax⁻¹
    have invax : Invertible ax := so3_has_inv ⟨ax, bx⟩
    have rws: ax⁻¹ ∈ SO3 := so3_closed_under_inverse ax bx
    use rws
    rw [←pabx]
    apply eq_inv_iff_mul_eq_one.mpr
    apply IsometryEquiv.ext_iff.mpr
    simp
    intro y
    simp [ToEquivSO3]
    simp [to_R3]


def hmo : SO3 →* SO3_in_G3 := {

  toFun:= fun (g : SO3) ↦ ⟨SO3_into_G3 g, (by apply Subgroup.mem_carrier.mp; simp [SO3_in_G3])⟩

  map_one' := by
    simp [SO3_into_G3]
    apply IsometryEquiv.ext_iff.mpr
    intro x
    simp
    simp [ToEquivSO3]
    simp [to_R3]

  map_mul' := by
    intro x y
    simp [SO3_into_G3]
    apply IsometryEquiv.ext_iff.mpr
    intro z
    simp
    simp [ToEquivSO3]
    apply congrArg
    simp [to_R3]
}

theorem hmo_is_injective : Function.Injective hmo  := by
  simp [Function.Injective]
  intro a pa b pb eq_images
  simp [hmo] at eq_images
  simp [SO3_into_G3] at eq_images
  simp [ToEquivSO3] at eq_images
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  let vlp := to_R3 v
  let fa := (fun x:R3 ↦ to_R3 (a.mulVec x.ofLp))
  let fb := (fun x:R3 ↦ to_R3 (b.mulVec x.ofLp))
  have eqf: fa = fb := eq_images.left
  have eqim:_:=  congrFun eqf vlp
  simp [fa, fb] at eqim
  simp [vlp] at eqim
  simp [to_R3] at eqim
  exact eqim


theorem hmo_is_surjective : Function.Surjective hmo  := by
  simp [Function.Surjective]
  intro a pa
  simp [SO3_in_G3] at pa
  simp [hmo]
  exact pa

theorem hmo_is_bijective : Function.Bijective hmo := ⟨hmo_is_injective, hmo_is_surjective⟩

noncomputable def SO3_to_G3_iso_forward_equiv := Equiv.ofBijective hmo hmo_is_bijective

noncomputable def SO3_embed_G3 : SO3 ≃* SO3_in_G3 :=
  MulEquiv.mk' SO3_to_G3_iso_forward_equiv hmo.map_mul'



-- Given by function evaluation
instance : MulAction G3 R3 where
  smul g v := g v
  one_smul v := by
    have lem : (1:G3) v = v := by
      rw [IsometryEquiv.coe_one]
      simp
    exact lem
  mul_smul x y v := by
    have lem: (y.trans x) v = x (y v) := by simp
    exact lem

lemma SO3_G3_action_equiv : (∀x : R3, ∀g : SO3, (SO3_into_G3 g) • x  = g • x) := by
  intro x g; rfl

-------------------------


def B3 : Set R3 := Metric.closedBall (0 : R3) 1
def B3min : Set R3 := B3 \ {0}

def S2_sub := {S : Set R3 // S ⊆ S2}
def cone (S : S2_sub) := {x : R3 | ∃ (s : ℝ) (v : R3), (x = s • v) ∧ (v ∈ S.val) ∧ (0 < s)}
def trunc_cone (S : S2_sub) := cone S ∩ B3

lemma b3min_is_trunc_cone_s2 : B3min = trunc_cone ⟨S2, by simp⟩ := by
  ext x
  constructor
  · intro xinb3min
    simp [trunc_cone]
    constructor
    · simp [B3min, B3] at xinb3min
      use ‖x‖, ‖x‖⁻¹ • x
      constructor
      · rw [smul_inv_smul₀]
        by_contra znorm
        simp at znorm
        exact xinb3min.right znorm
      · constructor
        · simp [S2]
          simp [norm_smul]
          apply inv_mul_cancel₀
          by_contra zeronorm
          simp at zeronorm
          exact xinb3min.right zeronorm
        · by_contra bad
          simp at bad
          exact xinb3min.right bad
    · exact xinb3min.left
  · intro xintcone
    simp [B3min, B3]
    simp [trunc_cone] at xintcone
    obtain ⟨s, v, psv⟩ := xintcone.left
    rw [psv.left]
    simp [norm_smul]


    have nveq1: ‖v‖ = 1 := by
      by_contra notone
      have bad: _:= psv.right.left
      simp [S2] at bad
      absurd notone bad
      trivial

    rw [nveq1]
    simp
    constructor
    · apply abs_le.mpr
      constructor
      · linarith
      · simp [B3] at xintcone
        rw [psv.left] at xintcone
        simp [norm_smul] at xintcone
        rw [nveq1] at xintcone
        simp at xintcone
        apply le_of_abs_le
        exact xintcone.right
    · constructor
      · by_contra sz
        rw [sz] at psv
        simp at psv
      · by_contra eqz
        rw [eqz] at nveq1
        simp at nveq1


lemma trunc_cone_sub_ball (S : S2_sub) : trunc_cone S ⊆ B3min  := by
  simp [trunc_cone]
  rintro x ⟨xinl, xinr⟩
  simp [B3min]
  constructor
  · exact xinr
  simp [cone] at xinl
  obtain ⟨s,v, psv⟩ := xinl
  by_contra xzero
  rw [xzero] at psv
  have  sprop:_:= S.prop
  have :_:=sprop psv.right.left
  simp [S2] at this
  have bad:_:= eq_zero_or_eq_zero_of_smul_eq_zero (psv.left).symm
  rcases bad with sb | vb
  · linarith
  · rw [vb] at this
    simp at this


lemma cone_lemma (S : S2_sub) : ∀ x : R3, x ∈ cone S ↔ (normed x ∈ S.val) := by
  intro x
  constructor
  · intro lhs
    simp [cone] at lhs
    obtain ⟨s, v, psv⟩ := lhs
    simp [normed]
    have nveq1: ‖v‖ = 1 := by
      by_contra notone
      have bad: _:= S.prop psv.right.left
      simp [S2] at bad
      absurd notone bad
      trivial

    have isv: ‖x‖⁻¹ • x = v := by
      rw [psv.left]
      simp [norm_smul]
      rw [nveq1]
      simp
      simp [abs_of_pos psv.right.right]
      apply inv_smul_smul₀
      linarith
    rw [isv]
    exact psv.right.left
  · intro normed_in_S
    have normnotzero: ‖x‖ ≠ 0 := by
      by_contra iszero
      simp [normed] at normed_in_S
      rw [iszero] at normed_in_S
      simp at normed_in_S
      have sprop:_:= S.prop
      have bad:_:=sprop normed_in_S
      simp [S2] at bad
    simp [cone]
    simp [normed] at normed_in_S
    use ‖x‖, ‖x‖⁻¹ • x
    constructor
    · rw [smul_inv_smul₀]
      exact normnotzero
    · constructor
      · exact normed_in_S
      · by_contra bad
        simp at bad
        rw [bad] at normnotzero
        simp at normnotzero

lemma trunc_cone_lemma (S : S2_sub) : ∀ x : R3, x ∈ trunc_cone S → (normed x ∈ S.val) := by
  intro x lhs
  have: x ∈ cone S := by
    simp [trunc_cone] at lhs
    exact lhs.left
  exact (cone_lemma S x).mp this


lemma disj_lemma (n : ℕ) (fam : Fin n → S2_sub)
  (disj : ∀ (i j : Fin n), i ≠ j → Disjoint (fam i).val (fam j).val) :
∀ (i j : Fin n), i ≠ j → Disjoint (trunc_cone (fam i)) (trunc_cone (fam j)) := by
    intro i j inej
    apply Set.disjoint_iff.mpr
    intro x ⟨xini, xinj⟩
    simp
    have badi: normed x ∈ (fam i).val := by
      exact (trunc_cone_lemma ( fam i) x) xini
    have badj: normed x ∈ (fam j).val := by
      exact (trunc_cone_lemma ( fam j) x) xinj
    exact (Set.disjoint_iff.mp (disj i j inej)) ⟨badi, badj⟩

lemma cover_lemma (n : ℕ) (fam : Fin n → S2_sub) (T : S2_sub)
  (cover : (⋃ i, (fam i).val) = T.val) : (⋃ i, trunc_cone (fam i)) = trunc_cone T := by
  ext x
  constructor
  · intro xincones
    simp at xincones
    obtain ⟨i, pi⟩ := xincones
    have lem : normed x ∈ (fam i).val := (trunc_cone_lemma (fam i) x) pi
    by_contra xnitct
    have small:  ‖x‖ ≤ 1 := by
      simp [trunc_cone] at pi
      simp [B3] at pi
      exact pi.right
    have noteven:  x ∉ cone T := by
      by_contra xincone
      have inb3: x∈ B3 := by simp [B3]; exact small
      exact xnitct ⟨xincone, inb3⟩
    have bad: (normed x) ∉ T.val := by
      by_contra nx_in_tval
      exact noteven ((cone_lemma T x).mpr nx_in_tval)
    rw [←cover] at bad
    rw [Set.mem_iUnion] at bad
    simp at bad
    exact (bad i) lem
  · intro xincone
    simp [trunc_cone] at xincone
    have intval: normed x ∈ T.val := (trunc_cone_lemma T x) xincone
    rw [←cover] at intval; simp at intval
    obtain ⟨i, pi⟩ := intval
    have piece : x ∈ cone (fam i) := by exact (cone_lemma (fam i) x).mpr pi
    have piece_t: x ∈ trunc_cone (fam i) := ⟨piece, xincone.right⟩
    simp
    use i


instance : SMulCommClass ℝ (↥SO3) R3 where
  smul_comm:  ∀ (k : ℝ) (g : SO3) (v : R3), k • g • v = g • k • v := by
    intro k g v
    calc k • g • v
    _ = k • (WithLp.toLp 2 (Matrix.mulVec g v)) := by rfl
    _ = (WithLp.toLp 2 (k • Matrix.mulVec g v)) := by simp
    _ = (WithLp.toLp 2 (Matrix.mulVec g (k • v))) :=  by
      rw [(Matrix.mulVec_smul g.val k v).symm]; rfl
    _ = g • k • v := by rfl



lemma map_lemma (n : ℕ) (map : Fin n -> SO3) (famA : Fin n → S2_sub) (famB : Fin n → S2_sub)
  (map_prop : ∀ (i : Fin n), f (map i)'' (famA i).val = (famB i).val) :
∀ (i: Fin n), f (map i) '' trunc_cone (famA i) = trunc_cone (famB i)  := by
  intro i
  have tops:_ :=map_prop i

  ext x
  constructor
  · intro xinmi
    simp [trunc_cone]
    simp [cone]
    simp [trunc_cone] at xinmi
    simp [cone] at xinmi
    obtain ⟨s, v, psv⟩ := xinmi
    constructor
    · use s
      use f (map i) v
      constructor
      · simp [f]
        simp [f] at psv
        rw [smul_comm]
        exact psv.right.symm
      · constructor
        · rw [←tops]
          apply (Set.mem_image (f (map i)) (famA i).val (f (map i) v)).mpr
          use v
          constructor
          · exact psv.left.left.left
          · rfl
        · exact psv.left.left.right
    · simp [B3]
      rw [←psv.right]
      simp [f]
      rw [so3_fixes_norm]
      simp [B3] at psv
      exact psv.left.right
  · intro xinpiece
    simp [trunc_cone, cone]
    simp [trunc_cone, cone] at xinpiece
    obtain ⟨s, w, psw ⟩ := xinpiece.left
    use s
    use f (map i)⁻¹ w
    simp [f]
    constructor
    · constructor
      · constructor
        · rw [←tops] at psw
          have this: w ∈ f (map i) '' (famA i).val := psw.right.left
          exact Set.mem_smul_set_iff_inv_smul_mem.mp this
        · exact psw.right.right
      · have cm:  s • (map i)⁻¹ • w = (map i)⁻¹ • s • w := smul_comm s (map i)⁻¹ w
        rw [cm]
        simp [B3]
        rw [so3_fixes_norm ((map i)⁻¹) (s • w)]
        rw [←psw.left]
        simp [B3] at xinpiece
        exact xinpiece.right
    · rw [smul_comm s]
      simp
      exact psw.left.symm


def x_axis_vec : R3 := to_R3 ![1, 0, 0]
lemma x_axis_on_sphere : x_axis_vec ∈ S2 := by
  simp [S2, x_axis_vec, to_R3]
  simp [norm]
  simp [Fin.sum_univ_three]
def x_axis : S2 := ⟨x_axis_vec, x_axis_on_sphere⟩



-- This should be rotation around a line through (0,0,.5) in the x z plane parallel to the x-axis.
noncomputable def skew_rot (θ : ℝ) : G3 :=
  let offset : R3 := to_R3 ![0, 0, 0.5]
  let shift (p : R3) : R3 := p + offset
  let unshift (p : R3) : R3 := p - offset


  {
    toFun := shift ∘ (rot_iso x_axis θ) ∘ unshift
    invFun := shift ∘ (rot_iso x_axis (-θ)) ∘ unshift
    left_inv := by
      intro x
      simp
      simp [shift, unshift]
      rw [rot_iso_comp]
      rw [rot_iso_comp]
      simp
      rw [triv_rot_iso]
      simp


    right_inv := by
      intro x
      simp
      simp [shift, unshift]
      repeat  rw [rot_iso_comp]
      simp
      rw [triv_rot_iso]
      simp


    isometry_toFun := by
      rw [Isometry]
      intro x1 x2
      rw [Isometry.comp]
      · simp [shift]
        exact isometry_add_right offset
      · intro x1 x2
        rw [Isometry.comp]
        · simp [Isometry]
        · simp [unshift]
          change Isometry (fun p ↦ p + -offset)
          exact isometry_add_right (-offset)

  }

lemma f_triv_g3 : (f (skew_rot r)) = skew_rot r := rfl


lemma skew_rot_comp_add (t1 t2 : ℝ) : (skew_rot t1) ∘ (skew_rot t2) = skew_rot (t1 + t2) := by
  simp [skew_rot]
  ext x ind
  simp
  rw [←rot_iso_comp_add x_axis t1 t2]
  simp



lemma skew_rot_power_lemma (r : ℝ) : ((skew_rot r))^[n] = (skew_rot (n*r)) := by
  induction n with
  | zero =>
    simp
    simp [skew_rot]
    rw [triv_rot_iso x_axis]
    simp [to_R3]
    ext x i
    fin_cases i
    <;> simp
  | succ k ih =>
    rw [Function.iterate_succ']
    rw [ih]
    rw [skew_rot_comp_add]
    apply congrArg
    apply congrArg
    simp [Nat.cast_add]
    linarith



lemma origin_cont (T : ℝ) : ‖(skew_rot T) origin‖ ≤ 1 := by

  have half_lem : ‖ to_R3 ![0, 0, 0.5]‖ ≤ (0.5 : ℝ) := by
    simp [norm]
    simp [to_R3]
    simp [Fin.sum_univ_three]
    norm_num

  have i1: ‖rot_iso (x_axis) T  (origin - to_R3 ![0, 0, 0.5])‖ ≤ (0.5 : ℝ) := by
    have norm_pres: ‖(rot_iso (x_axis) T) (origin - to_R3 ![0, 0, 0.5])‖ =
      ‖origin - to_R3 ![0, 0, 0.5]‖ := by rw [(rot_iso (x_axis) T).norm_map ]
    rw [norm_pres]
    simp [origin, to_R3]
    exact half_lem

  calc
    ‖(skew_rot T) origin‖ = ‖((rot_iso x_axis T)  (origin - to_R3 ![0, 0, 0.5]))
      + to_R3 ![0, 0, 0.5]‖ := by simp [skew_rot];
    _ ≤ ‖(rot_iso x_axis T) (origin - to_R3 ![0, 0, 0.5])‖ + ‖to_R3 ![0, 0, 0.5]‖ := by
      apply norm_add_le
    _ ≤ (0.5 : ℝ) + (0.5 : ℝ) := by linarith [i1, half_lem]
    _ = (1 : ℝ) := by norm_num


lemma srot_containment : ∀r : ℝ, orbit (skew_rot r) {origin} ⊆ B3 := by
  intro r
  simp only [orbit]
  simp only [B3]
  intro p pinunion
  simp  at pinunion
  obtain ⟨n, pn ⟩ := pinunion
  rw [f_triv_g3] at pn
  rw [skew_rot_power_lemma] at pn
  set T := n * r with Ndef
  rw [←pn]
  simp
  exact origin_cont T



lemma rot_iso_fixed_back (axis : S2) (v : R3) (k : ℤ) : (rot_iso axis (2 * Real.pi * k)) v = v := by
  simp [rot_iso]
  simp [rot_by_parts]
  simp [rot_iso_plane_to_st, rot_iso_plane_equiv]

  have angcoe: Real.Angle.coe (2 * Real.pi * ↑k) = (0:ℝ) := by
    apply Real.Angle.angle_eq_iff_two_pi_dvd_sub.mpr
    simp
  rw [angcoe]
  simp
  exact (el_by_parts axis v).symm


def origin_in_s : ({origin} : Set R3) := ⟨origin, (by simp)⟩

lemma BadAtN_skew_rot :
  (BadAtN skew_rot {origin} origin_in_s origin_in_s n) =
      {θ : ℝ | ∃k : ℤ, ((n + 1 : ℝ) * θ) / (2 * Real.pi) = k} := by
      simp [BadAtN]
      simp [origin_in_s]
      ext θ
      simp
      rw [←Function.iterate_succ_apply (f (skew_rot θ)) n origin]
      rw [f_triv_g3]
      rw [skew_rot_power_lemma]
      simp [skew_rot]
      constructor
      · intro lhs
        apply congrArg (fun x ↦ x - to_R3 ![0, 0, 0.5]) at lhs
        simp at lhs
        rw [←map_sub (rot_iso x_axis ((↑n + 1) * θ))] at lhs

        have nzv : ((operp x_axis (origin - to_R3 ![0, 0, 0.5])) ≠ 0) := by
          rw [operp, origin]
          simp
          simp [orth]
          simp [to_R3]
          simp [x_axis, x_axis_vec]
          by_contra inspan
          obtain ⟨a, pa⟩ := Submodule.mem_span_singleton.mp inspan
          simp [to_R3] at pa
          norm_num at pa
          have h0 := congrArg (fun v => v 2) pa
          simp at h0

        have :_ := (rot_iso_fixed x_axis (origin -(to_R3 ![0, 0, 0.5]))) ⟨nzv, lhs⟩
        obtain ⟨k, pk⟩ := this
        use k
        rw [pk]
        field_simp
      · intro lhs
        have asgood: (rot_iso x_axis ((↑n + 1) * θ)) (origin - to_R3 ![0, 0, 0.5])  =
          origin - to_R3 ![0, 0, 0.5] := by
          obtain ⟨k, pk⟩ := lhs
          field_simp at pk
          rw [pk]
          exact rot_iso_fixed_back x_axis (origin - to_R3 ![0, 0, 0.5]) k

        apply congrArg (fun x ↦ x + to_R3 ![0, 0, 0.5]) at asgood
        simp at asgood
        exact asgood


lemma BadAtN_skew_rot_countable :
  Set.Countable (BadAtN skew_rot {origin} origin_in_s origin_in_s n) := by
    rw [BadAtN_skew_rot]
    let foo (k : ℤ) := (k : ℝ) * (2 * Real.pi) / (n + 1 : ℝ)
    have imlem : {θ | ∃ k : ℤ, (↑n + 1) * θ / (2 * Real.pi) = ↑k} = foo '' (Set.univ : Set ℤ) := by
      ext t
      simp
      simp [foo]
      field_simp
      tauto
    rw [imlem]
    apply Set.Countable.image
    exact Set.countable_univ




lemma bad_as_union_skew_rot :
  Bad skew_rot ({origin}) = ⋃ n : ℕ, BadAtN (skew_rot) {origin} origin_in_s origin_in_s n  := by
  rw [bad_as_union]
  simp [BadAt]
  simp [origin_in_s]


lemma countable_bad_skew_rot : Countable (Bad skew_rot {origin}) := by
  rw [bad_as_union_skew_rot]
  apply Set.countable_iUnion
  intro n
  exact BadAtN_skew_rot_countable
