import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Data.Countable.Defs
import Mathlib.SetTheory.Cardinal.Basic

import BanachTarski.Common
import BanachTarski.Sato
import BanachTarski.GeometricUtils


set_option warningAsError false
set_option linter.all false

def Equidecomposible {X : Type*} (G: Type*) [Group G] [MulAction G X] (E F : Set X): Prop :=
  ∃ n: Nat,
  ∃ As: Fin n → Set X,
  ∃ Bs: Fin n → Set X,
  (∀ i j : Fin n, (i ≠ j) → Disjoint (As i) (As j)) ∧
  (∀ i j : Fin n, (i ≠ j) → Disjoint (Bs i) (Bs j)) ∧
  (⋃ i : Fin n, (As i)) = E ∧
  (⋃ i : Fin n, (Bs i)) = F ∧
  ∃ g: Fin n → G,
  (∀ i : Fin n, ((fun (x: X) ↦ (g i) • x) '' (As i)) = Bs i)


lemma ml {i j: ℕ} {m n: Fin (i * j)} : m ≠ n → m.divNat ≠ n.divNat ∨
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


lemma ml2 {i j: ℕ} {m n: Fin (i * j)} : m ≠ n → m.modNat ≠ n.modNat ∨
  (m.modNat = n.modNat ∧ m.divNat ≠ n.divNat) := by
  intro mneqn
  have res :_ := ml mneqn
  tauto



lemma fcomp {X : Type*} {G: Type*} [Group G] [MulAction G X] (g h : G) :
(fun x:X ↦ (g * h) • x) = (fun x : X ↦ g • x) ∘ (fun x: X ↦ h • x) := by
  simp [mul_smul g h]
  rfl

lemma finj {X : Type*} {G: Type*} [Group G] [MulAction G X] (g: G) :
Function.Injective (fun x ↦ g • x : X → X) := by
  intro a b eq
  simp at eq
  exact eq

lemma equidecomposibility_trans {X : Type*} {G: Type*} [Group G] [MulAction G X] :
∀ {L M N  : Set X}, Equidecomposible G L M → Equidecomposible G M N → Equidecomposible G L N := by

  intro L M N equiLM equiMN
  obtain ⟨nLM, ALs, BMs, pdAL, pdBM, coverAL, coverBM, gLM, pmapLM⟩ := equiLM
  obtain ⟨nMN, AMs, BNs, pdAM, pdBN, coverAM, coverBN, gMN, pmapMN⟩ := equiMN


  let n := nLM * nMN
  let A (i: Fin nLM) (j: Fin nMN) := (ALs i) ∩ (f ((gLM i)⁻¹) '' AMs j)
  let B (i: Fin nLM) (j: Fin nMN) := (f (gMN j) '' (BMs i)) ∩ BNs j

  -- Todo:  I absolutely hate this way of inferring the divisor/modulus from
  -- fintype.  See if there is a better practice.
  let As (k: Fin n) := A (k.divNat) (k.modNat)
  let Bs (k: Fin n) := B (k.divNat) (k.modNat)

  have pdA: (∀ i j : Fin n, (i ≠ j) → Disjoint (As i) (As j))  := by
    intro i j inej
    apply Set.disjoint_iff.mpr
    intro bad ⟨pbadi, pbadj⟩
    simp
    simp [As, A] at pbadi
    simp [As, A] at pbadj
    obtain (diff_div | diff_mod) :_ := ml inej
    --case 1
    have djaldiv : _ := pdAL i.divNat j.divNat diff_div
    have notgood :_ := Set.disjoint_iff.mp  djaldiv
    exact notgood ⟨pbadi.left, pbadj.left⟩
    --case 2

    obtain ⟨pre_i, p_pre_i⟩ := pbadi.right
    obtain ⟨pre_j, p_pre_j⟩ := pbadj.right
    rw [←diff_mod.left] at p_pre_j

    let g := @f X G _ _ ((gLM i.divNat)⁻¹)

    have equal_images : g pre_i = g pre_j := calc g pre_i
      _ = bad :=  p_pre_i.right
      _ = g pre_j := p_pre_j.right.symm

    have equal_preimages: pre_i = pre_j := smul_left_cancel (gLM i.divNat)⁻¹ equal_images
    rw [←equal_preimages] at p_pre_j

    have djammod: _ := pdAM i.modNat j.modNat diff_mod.right
    have notgood :_ := Set.disjoint_iff.mp djammod
    exact notgood ⟨p_pre_i.left, p_pre_j.left⟩


  have pdB: (∀ i j : Fin n, (i ≠ j) → Disjoint (Bs i) (Bs j))  := by
    intro i j inej
    apply Set.disjoint_iff.mpr
    intro bad ⟨pbadi, pbadj⟩
    simp
    simp [Bs, B] at pbadi
    simp [Bs, B] at pbadj
    obtain (diff_mod | diff_div) :_ := ml2 inej
    --case 1
    have djbndiv:_:= pdBN i.modNat j.modNat diff_mod
    have notgood: _:= Set.disjoint_iff.mp djbndiv
    exact notgood ⟨pbadi.right, pbadj.right⟩
    --case 2
    rw [←diff_div.left] at pbadj
    obtain ⟨pre_i, p_pre_i⟩ := pbadi.left
    obtain ⟨pre_j, p_pre_j⟩ := pbadj.left
    let g := @f X G _ _ (gMN i.modNat)
    have equal_images : g pre_i = g pre_j := calc g pre_i
      _ = bad :=  p_pre_i.right
      _ = g pre_j := p_pre_j.right.symm
    have equal_preimages: pre_i = pre_j := smul_left_cancel (gMN i.modNat) equal_images
    rw [← equal_preimages] at p_pre_j
    have djbmdiv :_ := pdBM i.divNat j.divNat diff_div.right
    have notgood: _:= Set.disjoint_iff.mp djbmdiv
    exact notgood ⟨p_pre_i.left, p_pre_j.left⟩


  have coverA : (⋃ i : Fin n, (As i)) = L := by
    simp [As, A]
    ext x
    constructor

    -- LTR
    intro inunion
    simp [Set.mem_iUnion] at inunion
    obtain ⟨j, pj⟩ := inunion
    have inas : x ∈ ⋃ i, ALs i  := by
      simp
      exact ⟨j.divNat, pj.left⟩
    rw [coverAL] at inas
    exact inas

    -- RTL

    intro xinL
    rw [←coverAL] at xinL

    obtain ⟨S, pi⟩ := xinL
    simp at pi
    obtain ⟨y, py⟩ := pi.left
    let mem := pi.right
    rw [←py] at mem

    let z:= f (gLM y) x

    have pr: z ∈ f (gLM y) '' (ALs y) := by
      simp
      use x

    simp only [f] at pr
    rw [pmapLM y] at pr
    have zinun : z ∈ ⋃ i, BMs i := by
      simp
      exact ⟨y, pr⟩
    have zinM: z ∈ M := by rwa [coverBM] at zinun
    rw [←coverAM] at zinM
    obtain ⟨T, pT⟩ := zinM
    simp at pT
    obtain ⟨w, pw⟩ := pT.left
    let mem2 := pT.right
    rw [←pw] at mem2

    have rhs: x ∈ f (gLM y)⁻¹ '' AMs w := by
      simp
      use z
      simp [z]
      simp [f]
      simp [z] at mem2
      simp [f] at mem2
      exact mem2

    let d :Fin n := finProdFinEquiv.toFun (y, w)
    have invres: (y, w) = finProdFinEquiv.invFun d := by simp [d]
    have invres2: (y, w) = (d.divNat, d.modNat) := by simp [invres]
    injection invres2.symm with dy dw
    rw [Set.mem_iUnion]
    use d
    simp only [dy, dw]
    exact ⟨mem, rhs⟩


  have coverB : (⋃ i : Fin n, (Bs i)) = N := by
    simp [Bs, B]
    ext x
    constructor
    --LTR
    intro inunion
    simp [Set.mem_iUnion] at inunion
    obtain ⟨j, pj⟩ := inunion
    have inbs : x ∈ ⋃ i, BNs i  := by
      simp
      exact ⟨j.modNat, pj.right⟩
    rw [coverBN] at inbs
    exact inbs
    --RTL
    intro xinN
    rw [←coverBN] at xinN
    simp at xinN
    obtain ⟨m, pm⟩ := xinN
    let rhs := pm
    rw [←pmapMN m] at pm

    simp at pm
    obtain ⟨pre_x, p_pre_x⟩ := pm
    have prexinM: pre_x∈ M := by
      rw [←coverAM]
      simp
      exact ⟨m, p_pre_x.left⟩

    rw [←coverBM] at prexinM
    simp at prexinM
    obtain ⟨d, pd⟩ := prexinM
    have lhs: x ∈ f (gMN m) '' BMs d := by
      simp
      use pre_x
      simp [f]
      exact ⟨pd, p_pre_x.right⟩
    simp only [Set.mem_iUnion]

    let a :Fin n := finProdFinEquiv.toFun (d, m)
    have invres: (d, m) = finProdFinEquiv.invFun a := by simp [a]
    have invres2: (d, m) = (a.divNat, a.modNat) := by simp [invres]
    injection invres2.symm with dy dw
    use a
    rw [dy, dw]
    exact ⟨lhs, rhs⟩


  let g: Fin n → G := fun k ↦ (gMN k.modNat) * (gLM k.divNat)
  let pmap_LN:   (∀ i : Fin n, ((fun (x: X) ↦ (g i) • x) '' (As i)) = Bs i) := by
    intro i
    simp [g]
    simp [As, Bs]
    dsimp [A, B]
    have star_elim:_:= @fcomp X _ _ _ (gMN i.modNat) (gLM i.divNat)
    rw [star_elim]

    let comp: X→X := ((fun x ↦ gMN i.modNat • x) ∘ (fun x ↦ gLM i.divNat • x))
    let s:= ALs i.divNat
    let t:= f (gLM i.divNat)⁻¹ '' AMs i.modNat
    have comp_injective : Function.Injective comp := by
      intro x y cxeqcy
      simp [comp]at cxeqcy
      exact cxeqcy

    have lem2: comp '' (s ∩ t) = (comp '' s) ∩ (comp '' t) := Set.image_inter comp_injective
    simp only [s, t, comp, f] at lem2
    dsimp at lem2
    simp [f]
    rw [lem2]
    -- Simp keeps collapsing compositions
    have annoying1: (fun a:X ↦ (gMN i.modNat) • (gLM i.divNat) • a) = comp := by rfl

    rw [annoying1]
    rw [Set.image_comp]

    have lem3:_ := pmapLM i.divNat
    rw [lem3]
    have rest :  ((fun a ↦ gMN i.modNat • a) ∘ fun a ↦ gLM i.divNat • a) ''
    ((fun a ↦ (gLM i.divNat)⁻¹ • a) '' AMs i.modNat) = BNs i.modNat := by
      rw [Set.image_comp]
      rw [← Set.image_comp (fun a ↦ gLM i.divNat • a)]
      simp
      exact pmapMN i.modNat

    rw [rest]


  exact  ⟨n, As, Bs, pdA, pdB, coverA, coverB, g, pmap_LN⟩



lemma equidecomposibility_symm {X : Type*} {G: Type*} [Group G] [MulAction G X]:
∀ {M N: Set X}, Equidecomposible G M N → Equidecomposible G N M := by
  rintro M N ⟨n, As, Bs, pdAs, pdBs, coverAs, coverBs, g, pmap⟩

  let g_inv:= fun (k: Fin n) ↦ (g k)⁻¹
  let pmap_inv:   (∀ i : Fin n, ((fun (x: X) ↦ (g i)⁻¹ • x) '' (Bs i)) = As i) := by
    intro i
    rw [←pmap i]
    rw [←Set.image_comp]
    simp

  exact ⟨n, Bs, As, pdBs, pdAs, coverBs, coverAs, g_inv, pmap_inv⟩


def Paradoxical {X : Type*} (G: Type*) [Group G] [MulAction G X] (E: Set X): Prop :=
  Set.Nonempty E ∧
  ∃ C D:  Set X,
  (C ⊆ E) ∧ (D ⊆ E) ∧ (Disjoint C D) ∧
  (Equidecomposible G C E) ∧ (Equidecomposible G D E)



lemma paradoxical_of_equidecomposible_of_paradoxical {X : Type*} (G: Type*) [Group G] [MulAction G X] (E F : Set X):
Paradoxical G E → Equidecomposible G E F → Paradoxical G F := by
  intro paraE equiEF
  obtain ⟨neE, C, D, csube, dsube, disjcd, equiCE, equiDE⟩ := paraE
  let ⟨n, As, Bs, pdAs, pdBs, coverAs, coverBs, g, pmap⟩ := equiEF

  constructor
  -- Nonempty F
  obtain ⟨e, pe⟩ := neE
  obtain ⟨ie, pie⟩ := by
    rw [←coverAs] at pe
    rwa [Set.mem_iUnion] at pe
  have inter:_ := pmap ie
  have inter2: (g ie • e) ∈ (fun x ↦ g ie • x) '' As ie := by
    simp [pie]
  let f:= g ie • e

  have inter3: f ∈ Bs ie := by rwa [inter] at inter2

  have inter4: f ∈ F := by
    rw [←coverBs, Set.mem_iUnion]
    exact ⟨ie, inter3⟩
  exact ⟨f, inter4⟩

  -- ∃ C D, C ⊆ F ∧ D ⊆ F ∧ ...
  let gC := ⋃ i, (fun (x : X) ↦ (g i) • x) '' (C ∩ (As i))
  let gD := ⋃ i, (fun (x : X) ↦ (g i) • x) '' (D ∩ (As i))
  use gC, gD

  -- gC ⊆ F ∧ gD ⊆ F ∧ Disjoint gC gD ∧ Equidecomposible G gC F ∧ Equidecomposible G gD F
  constructor
  -- gC ⊆ F
  intro gc gc_in_gC
  rw [← coverBs, Set.mem_iUnion]
  dsimp [gC] at gc_in_gC
  simp only [Set.mem_iUnion] at gc_in_gC
  obtain ⟨i, ⟨x, px⟩⟩ := gc_in_gC
  simp at px
  have inter0: gc ∈ ((fun x ↦ (g i) • x) '' (As i)) := by
    simp
    tauto
  rw [pmap i] at inter0
  exact ⟨i, inter0⟩

  constructor
  -- gD ⊆ F
  intro gd gd_in_gD
  rw [← coverBs, Set.mem_iUnion]
  dsimp [gD] at gd_in_gD
  simp only [Set.mem_iUnion] at gd_in_gD
  obtain ⟨i, ⟨x, px⟩⟩ := gd_in_gD
  simp at px
  have inter0: gd ∈ ((fun x ↦ (g i) • x) '' (As i)) := by
    simp
    tauto
  rw [pmap i] at inter0
  exact ⟨i, inter0⟩

  constructor
  -- Disjoint gC gD

  apply Set.disjoint_iff.mpr
  intro y ⟨y_in_gC, y_in_gD⟩
  simp [gC] at y_in_gC
  simp [gD] at y_in_gD
  let ⟨i_c, c, pc⟩ := y_in_gC
  let ⟨i_d, d, pd⟩ := y_in_gD
  have bc :_ := pmap i_c
  have bd :_ := pmap i_d
  have jc : y ∈ (fun x ↦ g i_c • x) '' As i_c  := by
    simp
    tauto
  have jd : y ∈ (fun x ↦ g i_d • x) '' As i_d  := by
    simp
    tauto
  have cB : y ∈ Bs i_c := by rw [pmap i_c] at jc; exact jc
  have dB : y ∈ Bs i_d := by rw [pmap i_d] at jd; exact jd
  have notBdis: ¬ Disjoint (Bs i_c) (Bs i_d) := Set.not_disjoint_iff.mpr ⟨y, cB, dB⟩
  have iceqid: i_c = i_d := by
    by_contra p
    apply mt (pdBs i_c i_d) notBdis p
  rw [←iceqid] at pd
  let h := g i_c
  have hceqhd: h • c = h • d := Eq.trans pc.right pd.right.symm
  -- There must be a theorem for this
  have c_eq_d: _ := calc c
    _ = h⁻¹ • (h • c) := (inv_smul_smul h c).symm
    _ = h⁻¹ • (h • d) := by rw [hceqhd]
    _ = d := inv_smul_smul h d
  rw [←c_eq_d] at pd
  have cinCD : c ∈ C ∩ D := ⟨pc.left.left, pd.left.left⟩
  apply (Set.disjoint_iff.mp disjcd) cinCD


  constructor

  -- let gC := ⋃ i, (fun (x : X) ↦ (g i) • x) '' (C ∩ (As i))
  -- Equidecomposible G gC F
  -- We go gC to C, C to E, E to F
  let ACs := fun i ↦ C ∩ (As i)
  let BGCs := fun i ↦ gC ∩ (Bs i)
  have pdACs :  (∀ i j : Fin n, (i ≠ j) → Disjoint (ACs i) (ACs j))  := by
    intro i j inej
    apply Set.disjoint_iff.mpr
    simp [ACs]
    have lem:_:= pdAs i j inej
    apply Set.disjoint_iff.mp at lem
    simp at lem
    ext x
    constructor
    intro lhs
    have bad: x ∈ As i ∩ As j := ⟨lhs.left.right, lhs.right.right⟩
    rw [lem] at bad
    exact bad
    simp


  have pdBGCs :  (∀ i j : Fin n, (i ≠ j) → Disjoint (BGCs i) (BGCs j))  := by
    intro i j inej
    apply Set.disjoint_iff.mpr
    simp [BGCs]
    have lem:_:= pdBs i j inej
    apply Set.disjoint_iff.mp at lem
    simp at lem
    ext x
    constructor
    intro lhs
    have bad : x ∈ Bs i ∩ Bs j := ⟨lhs.left.right, lhs.right.right⟩
    rw [lem] at bad
    exact bad
    simp


  have coverACs : (⋃ i : Fin n, (ACs i)) = C := by
    simp [ACs]
    exact calc ⋃ i, C ∩ As i
    _ = C ∩ (⋃ i, As i) := by rw [Set.inter_iUnion C As]
    _ = C ∩ E := by rw [←coverAs]
    _ = C := by apply Set.inter_eq_left.mpr; exact csube



  have coverBGCs : (⋃ i : Fin n, (BGCs i)) = gC := by
    simp [BGCs]

    have gcsubf: gC ⊆ F := by
      intro x xingc
      simp [gC] at xingc
      obtain ⟨ind, px, pind⟩ := xingc

      have mem : x ∈ f (g ind) '' (As ind) := by
        simp
        use px
        simp [f]
        simp [pind]

      simp only [f] at mem
      rw [pmap ind] at mem
      rw [←coverBs]
      simp
      exact ⟨ind, mem⟩

    exact calc ⋃ i, gC ∩ Bs i
    _ = gC ∩ (⋃ i, Bs i) := by rw [Set.inter_iUnion gC Bs]
    _ = gC ∩ F := by rw [←coverBs]
    _ = gC := by apply Set.inter_eq_left.mpr; exact gcsubf


  have pmap_restrict_c:   (∀ i : Fin n, ((fun (x: X) ↦ (g i) • x) '' (ACs i)) = BGCs i) := by
    intro k
    simp [ACs, BGCs]
    have gkinj: Function.Injective (fun a ↦ (g k) • a: X → X) := by
      intro a b eq
      simp at eq
      exact eq

    rw [Set.image_inter gkinj]
    rw [pmap k]
    simp [gC]
    ext x
    constructor
    intro lhs
    constructor
    simp only [Set.mem_iUnion]
    use k
    rw [Set.image_inter gkinj]
    rw [pmap k]
    exact lhs
    exact lhs.right
    intro cond2
    have bigu := cond2.left
    simp only [Set.mem_iUnion] at bigu
    obtain ⟨i, pi⟩ := bigu
    have iisk : i = k := by
      by_contra bad
      have xinbsi: x ∈ (Bs i) := by
        rw [←pmap i]
        simp
        simp at pi
        tauto
      have disjBs :_:= pdBs i k bad
      have badbad: x ∈ Bs i ∩ Bs k := ⟨xinbsi, cond2.right⟩
      have sobad : _ := Set.disjoint_iff.mp disjBs
      exact sobad badbad
    rw [iisk] at pi
    rw [Set.image_inter gkinj] at pi
    rw [←pmap k]
    exact pi


  have equiCgC: Equidecomposible G C gC := ⟨n, ACs, BGCs, pdACs, pdBGCs, coverACs, coverBGCs, g, pmap_restrict_c⟩

  have equiCF: Equidecomposible G C F := equidecomposibility_trans equiCE equiEF
  have equigCC : Equidecomposible G gC C := equidecomposibility_symm equiCgC
  exact equidecomposibility_trans  equigCC equiCF


  -- let gD := ⋃ i, (fun (x : X) ↦ (g i) • x) '' (D ∩ (As i))
  -- Equidecomposible G gD F
  -- We go gD to D, D to E, E to F
  let ADs := fun i ↦ D ∩ (As i)
  let BGDs := fun i ↦ gD ∩ (Bs i)
  have pdADs :  (∀ i j : Fin n, (i ≠ j) → Disjoint (ADs i) (ADs j))  := by
    intro i j inej
    apply Set.disjoint_iff.mpr
    simp [ADs]
    have lem:_:= pdAs i j inej
    apply Set.disjoint_iff.mp at lem
    simp at lem
    ext x
    constructor
    intro lhs
    have bad: x ∈ As i ∩ As j := ⟨lhs.left.right, lhs.right.right⟩
    rw [lem] at bad
    exact bad
    simp


  have pdBGDs :  (∀ i j : Fin n, (i ≠ j) → Disjoint (BGDs i) (BGDs j))  := by
    intro i j inej
    apply Set.disjoint_iff.mpr
    simp [BGDs]
    have lem:_:= pdBs i j inej
    apply Set.disjoint_iff.mp at lem
    simp at lem
    ext x
    constructor
    intro lhs
    have bad : x ∈ Bs i ∩ Bs j := ⟨lhs.left.right, lhs.right.right⟩
    rw [lem] at bad
    exact bad
    simp


  have coverADs : (⋃ i : Fin n, (ADs i)) = D := by
    simp [ADs]
    exact calc ⋃ i, D ∩ As i
    _ = D ∩ (⋃ i, As i) := by rw [Set.inter_iUnion D As]
    _ = D ∩ E := by rw [←coverAs]
    _ = D := by apply Set.inter_eq_left.mpr; exact dsube



  have coverBGDs : (⋃ i : Fin n, (BGDs i)) = gD := by
    simp [BGDs]

    have gcsubf: gD ⊆ F := by
      intro x xingc
      simp [gD] at xingc
      obtain ⟨ind, px, pind⟩ := xingc

      have mem : x ∈ f (g ind) '' (As ind) := by
        simp
        use px
        simp [f]
        simp [pind]

      simp only [f] at mem
      rw [pmap ind] at mem
      rw [←coverBs]
      simp
      exact ⟨ind, mem⟩

    exact calc ⋃ i, gD ∩ Bs i
    _ = gD ∩ (⋃ i, Bs i) := by rw [Set.inter_iUnion gD Bs]
    _ = gD ∩ F := by rw [←coverBs]
    _ = gD := by apply Set.inter_eq_left.mpr; exact gcsubf


  have pmap_restrict_d:   (∀ i : Fin n, ((fun (x: X) ↦ (g i) • x) '' (ADs i)) = BGDs i) := by
    intro k
    simp [ADs, BGDs]
    have gkinj: Function.Injective (fun a ↦ (g k) • a: X → X) := finj (g k)
    rw [Set.image_inter gkinj]
    rw [pmap k]
    simp [gD]
    ext x
    constructor
    intro lhs
    constructor
    simp only [Set.mem_iUnion]
    use k
    rw [Set.image_inter gkinj]
    rw [pmap k]
    exact lhs
    exact lhs.right
    intro cond2
    have bigu := cond2.left
    simp only [Set.mem_iUnion] at bigu
    obtain ⟨i, pi⟩ := bigu
    have iisk : i = k := by
      by_contra bad
      have xinbsi: x ∈ (Bs i) := by
        rw [←pmap i]
        simp
        simp at pi
        tauto
      have disjBs :_:= pdBs i k bad
      have badbad: x ∈ Bs i ∩ Bs k := ⟨xinbsi, cond2.right⟩
      have sobad : _ := Set.disjoint_iff.mp disjBs
      exact sobad badbad
    rw [iisk] at pi
    rw [Set.image_inter gkinj] at pi
    rw [←pmap k]
    exact pi


  have equiDgD: Equidecomposible G D gD := ⟨n, ADs, BGDs, pdADs, pdBGDs, coverADs, coverBGDs, g, pmap_restrict_d⟩

  have equiDF: Equidecomposible G D F := equidecomposibility_trans equiDE equiEF
  have  equigDD: Equidecomposible G gD D := equidecomposibility_symm equiDgD
  exact equidecomposibility_trans equigDD equiDF

lemma equidecomposible_of_supergroup_of_equidecomposible {X : Type*} (G: Type*) [Group G] [MulAction G X] (E F: Set X):
∀ H: Subgroup G, (Equidecomposible H E F → Equidecomposible G E F):= by
  intro H
  rintro ⟨n, As, Bs, pdA, pdB, coverA, coverB, g, pmap⟩
  let g_cast := fun n ↦ ((g n) : G)
  exact ⟨n, As, Bs, pdA, pdB, coverA, coverB, g_cast, pmap⟩


lemma paradoxical_of_supergroup_of_paradoxical {X : Type*} (G: Type*) [Group G] [MulAction G X] (H: Subgroup G) (E: Set X):
Paradoxical H E → Paradoxical G E:= by
  rintro ⟨neE, C, D, csube, dsube, disjcd, equiHCE, equiHDE⟩
  have equiGCE: Equidecomposible G C E := equidecomposible_of_supergroup_of_equidecomposible G C E H equiHCE
  have equiGDE: Equidecomposible G D E := equidecomposible_of_supergroup_of_equidecomposible G D E H equiHDE
  exact ⟨neE, C, D, csube, dsube, disjcd, equiGCE, equiGDE⟩


def SelfParadoxical (G: Type*) [Group G] : Prop := Paradoxical G (Set.univ: Set G)

theorem paradoxical_preserved_by_iso {X Y: Type*} {G H: Type*} [Group G] [Group H] [MulAction G X] [MulAction H Y] (E: Set X)(iso: G ≃*H )(f: X ≃ Y):
(∀x: X, ∀g : G, (iso g) • (f x)  = f (g • x)) → Paradoxical G E → Paradoxical H (f '' E) := by

  intro good_behavior
  rintro ⟨neE, C, D, csube, dsube, disjcd, equiGCE, equiGDE⟩

  let imE := f '' E
  have neimE : Set.Nonempty imE := by
    apply Set.Nonempty.image
    exact neE

  let imC := f '' C
  let imD := f '' D
  let imcsubime: imC ⊆ imE :=  by
    --oddly while there is Set.image_subset_image_iff, there
    -- is no one-directional version (that does not require Injectiveness)
    apply Set.image_subset_iff.mpr
    intro c cinC
    have this:_ := csube cinC
    simp
    simp [imE]
    exact this

  let imdsubime: imD ⊆ imE :=  by
    --oddly while there is Set.image_subset_image_iff, there
    -- is no one-directional version (that does not require Injectiveness)
    apply Set.image_subset_iff.mpr
    intro d dinD
    have this:_ := dsube dinD
    simp
    simp [imE]
    exact this

  let disjimcimd : Disjoint imC imD := by
    let inj : (Function.Injective f) := Equiv.injective f
    apply (Set.disjoint_image_iff inj).mpr
    exact disjcd


  obtain ⟨n, CAs, CBs, pdCA, pdCB, coverCA, coverCB, gC, pmapC⟩ := equiGCE
  obtain ⟨m, DAs, DBs, pdDA, pdDB, coverDA, coverDB, gD, pmapD⟩ := equiGDE

  let fCAs := fun k ↦ f '' (CAs k)
  let fCBs := fun k ↦ f '' (CBs k)
  let fDAs := fun k ↦ f '' (DAs k)
  let fDBs := fun k ↦ f '' (DBs k)
  let igC := fun k ↦ iso (gC k)
  let igD := fun k ↦ iso (gD k)

  have pdfCA :  ∀ (i j : Fin n), i ≠ j → Disjoint (fCAs i) (fCAs j) := by
    intro i j ineqj
    apply (Set.disjoint_image_iff (Equiv.injective f)).mpr
    exact pdCA i j ineqj

  have pdfDA :  ∀ (i j : Fin m), i ≠ j → Disjoint (fDAs i) (fDAs j) := by
    intro i j ineqj
    apply (Set.disjoint_image_iff (Equiv.injective f)).mpr
    exact pdDA i j ineqj

  have pdfCB :  ∀ (i j : Fin n), i ≠ j → Disjoint (fCBs i) (fCBs j) := by
    intro i j ineqj
    apply (Set.disjoint_image_iff (Equiv.injective f)).mpr
    exact pdCB i j ineqj

  have pdfDB :  ∀ (i j : Fin m), i ≠ j → Disjoint (fDBs i) (fDBs j) := by
    intro i j ineqj
    apply (Set.disjoint_image_iff (Equiv.injective f)).mpr
    exact pdDB i j ineqj

  have coverfCA: ⋃ i, fCAs i = imC := by
    simp [fCAs, imC]
    rw [←coverCA]
    apply Set.image_iUnion.symm

  have coverfDA: ⋃ i, fDAs i = imD := by
    simp [fDAs, imD]
    rw [←coverDA]
    apply Set.image_iUnion.symm

  have coverfCB: ⋃ i, fCBs i = imE := by
    simp [fCBs, imE]
    rw [←coverCB]
    apply Set.image_iUnion.symm

  have coverfDB: ⋃ i, fDBs i = imE := by
    simp [fDBs, imE]
    rw [←coverDB]
    apply Set.image_iUnion.symm


  have ipmapfC: ∀ (i : Fin n), (fun x ↦ igC i • x) '' fCAs i = fCBs i := by
    intro i
    have old: (fun x ↦ gC i • x) '' CAs i = CBs i := pmapC i
    ext y
    constructor
    intro yinL
    simp at yinL
    obtain ⟨y1, py1⟩ := yinL
    simp [fCBs]
    simp [fCAs] at py1
    have gby1 :_:= good_behavior (f.symm y1) (gC i)
    simp [igC] at py1
    simp at gby1
    rw [py1.right] at gby1
    rw [gby1]
    simp
    rw [←old]
    simp
    exact py1.left
    --
    intro yinfcbs
    simp [fCAs]
    simp [fCBs] at yinfcbs
    rw [←old] at yinfcbs
    simp at yinfcbs
    obtain ⟨x, px⟩ := yinfcbs
    use f x
    simp
    constructor
    exact px.left
    have gbi :_:= (good_behavior x (gC i))
    simp [igC]
    rw [gbi]
    simp [px.right]


  have ipmapfD: ∀ (i : Fin m), (fun x ↦ igD i • x) '' fDAs i = fDBs i := by
    intro i
    have old: (fun x ↦ gD i • x) '' DAs i = DBs i := pmapD i
    ext y
    constructor
    intro yinL
    simp at yinL
    obtain ⟨y1, py1⟩ := yinL
    simp [fDBs]
    simp [fDAs] at py1
    have gby1 :_:= good_behavior (f.symm y1) (gD i)
    simp [igD] at py1
    simp at gby1
    rw [py1.right] at gby1
    rw [gby1]
    simp
    rw [←old]
    simp
    exact py1.left
    --
    intro yinfcbs
    simp [fDAs]
    simp [fDBs] at yinfcbs
    rw [←old] at yinfcbs
    simp at yinfcbs
    obtain ⟨x, px⟩ := yinfcbs
    use f x
    simp
    constructor
    exact px.left
    have gbi :_:= (good_behavior x (gD i))
    simp [igD]
    rw [gbi]
    simp [px.right]

  have equiHimCimE: Equidecomposible H imC imE := ⟨n, fCAs, fCBs, pdfCA, pdfCB, coverfCA, coverfCB, igC, ipmapfC⟩
  have equiHimDimE: Equidecomposible H imD imE := ⟨m, fDAs, fDBs, pdfDA, pdfDB, coverfDA, coverfDB, igD, ipmapfD⟩

  exact ⟨neimE, imC, imD, imcsubime, imdsubime, disjimcimd, equiHimCimE, equiHimDimE⟩


theorem self_paradoxical_preserved_by_iso {G H: Type*} [Group G] [Group H] : SelfParadoxical G → G ≃* H → SelfParadoxical H := by
  simp [SelfParadoxical]
  intro selfparaG
  intro iso
  let g_univ:= (Set.univ : Set G)
  have cond1: ∀x: G, ∀g : G, (iso g) • (iso x)  = iso (g • x) := by
    intro x g
    simp
  have this: Paradoxical H (iso '' g_univ):= paradoxical_preserved_by_iso g_univ iso iso.toEquiv cond1 selfparaG
  have image_res: iso '' g_univ = (Set.univ: Set H) := by
    ext x
    constructor
    intro lhs
    simp
    intro rhs
    simp
    use (iso.invFun x)
    simp
    simp [g_univ]

  rwa [image_res] at this








lemma split2 (i: Fin 2): i = 0 ∨ i = 1 := by
  rcases (em (i=0)) with yes | no
  exact Or.inl yes
  exact Or.inr (Fin.eq_one_of_ne_zero i no)


lemma free_group_of_rank_two_is_self_paradoxical: SelfParadoxical FG2 := by

  let Dom := (Set.univ: Set FG2)

  constructor
  -- Nonempty ↑Set.univ
  use (1:FG2)
  simp

  -- ∃ C D, C ⊆ Set.univ ∧ D ⊆ Set.univ ∧ Disjoint C D ∧ Equidecomposible FG2 C Set.univ ∧ Equidecomposible FG2 D Set.univ

  -- let σDom := (fun x ↦ σ * x) '' Dom
  let σDom := {x ∈ Dom | ∃ (tail: List chartype), x.toWord = List.cons (σchar, true) tail}
  let τDom := {x ∈ Dom | ∃ (tail: List chartype), x.toWord = List.cons (τchar, true) tail}
  let σinvDom := {x ∈ Dom | ∃ (tail: List chartype), x.toWord = List.cons (σchar, false) tail}
  let τinvDom := {x ∈ Dom | ∃ (tail: List chartype), x.toWord = List.cons (τchar, false) tail}
  -- let σtimesσinvDom := (fun x ↦ σ * x) '' σinvDom
  -- let τtimesτinvDom := (fun x ↦ τ * x) '' σinvDom
  let C:= σDom ∪ σinvDom
  let D:= τDom ∪ τinvDom
  use C, D


  constructor
  -- C ⊆ Dom
  simp

  constructor
  -- D ⊆ Dom
  simp

  constructor
  -- Disjoint C D
  apply Set.disjoint_iff.mpr


  rintro x ⟨(x_in_sDom | x_in_sinvDom), (x_in_tDom | x_in_tinvDom)⟩

  --1
  simp [σDom] at x_in_sDom
  simp [τDom] at x_in_tDom
  obtain ⟨ts, ps⟩ := x_in_sDom.right
  obtain ⟨tt, pt⟩ := x_in_tDom.right
  simp [σchar, τchar] at ps pt
  rw [ps] at pt
  simp at pt

  --2
  simp [σDom] at x_in_sDom
  simp [τinvDom] at x_in_tinvDom
  obtain ⟨ts, ps⟩ := x_in_sDom.right
  obtain ⟨tt, pt⟩ := x_in_tinvDom.right
  simp [σchar, τchar] at ps pt
  rw [ps] at pt
  simp at pt

  --3

  simp [σinvDom] at x_in_sinvDom
  simp [τDom] at x_in_tDom
  obtain ⟨ts, ps⟩ := x_in_sinvDom.right
  obtain ⟨tt, pt⟩ := x_in_tDom.right
  simp [σchar, τchar] at ps pt
  rw [ps] at pt
  simp at pt

  --4
  simp [σinvDom] at x_in_sinvDom
  simp [τinvDom] at x_in_tinvDom
  obtain ⟨ts, ps⟩ := x_in_sinvDom.right
  obtain ⟨tt, pt⟩ := x_in_tinvDom.right
  simp [σchar, τchar] at ps pt
  rw [ps] at pt
  simp at pt

  constructor

  have disσ: σDom ∩ σinvDom = ∅ := by
    simp [σDom, σinvDom]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x xinboth
    simp at xinboth
    obtain ⟨x1, px1⟩ := xinboth.left.right
    obtain ⟨x2, px2⟩ := xinboth.right.right
    rw [px2] at px1
    have head_eq := (List.cons.inj px1).1
    have bool_eq := (Prod.mk.inj head_eq).2
    exact Bool.false_ne_true bool_eq





-- Equidecomposible FG2 C Dom
  let n := 2
  let As := ![σDom, σinvDom]
  let σσinvDom := (fun x ↦ σ * x) '' σinvDom
  let Bs := ![σDom, σσinvDom]
  have pdAs :  (∀ i j : Fin n, (i ≠ j) → Disjoint (As i) (As j)) := by
      intro i j ineqj
      apply Set.disjoint_iff.mpr
      simp
      have branchi : i = 0 ∨ i = 1 := split2 i
      have branchj : j = 0 ∨ j = 1 := split2 j
      obtain i0 | i1 := branchi
      obtain j0 | j1 := branchj
      --
      simp [i0, j0] at ineqj
      --
      simp [i0, j1]
      simp [As]
      exact disσ
      --
      obtain j0 | j1 := branchj
      simp [i1, j0]
      simp [As]
      rwa [Set.inter_comm] at disσ
      --
      simp [i1, j1] at ineqj

  have disσσ: σDom ∩ σσinvDom  = ∅ := by
    simp only [σDom, σσinvDom]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x xinboth
    simp at xinboth
    simp only [σinvDom] at xinboth
    obtain ⟨x1, px1⟩ := xinboth.left.right
    obtain ⟨x2, px2⟩ := xinboth.right.right

    have stepx2: FreeGroup.Red.Step ([(σchar, true)] ++ (σchar, false)::x2)  x2 := by
      exact FreeGroup.Red.Step.cons_not

    have whole_is_reduced : FreeGroup.IsReduced (FreeGroup.toWord (σ⁻¹ * x) ) := by
      exact FreeGroup.isReduced_toWord

    have x2_is_reduced: FreeGroup.IsReduced x2 := by
      rw [px2] at whole_is_reduced
      by_contra cont0
      have ugly:_:= (mt (FreeGroup.isReduced_iff_not_step.mpr)) cont0
      simp at ugly
      obtain ⟨l, pl⟩ := ugly
      have badred: FreeGroup.Red ((σchar, false)::x2) ((σchar, false)::l) :=
        FreeGroup.Red.cons_cons (FreeGroup.Red.Step.to_red pl)
      have badeq: (σchar, false)::l = (σchar, false)::x2 :=
        (FreeGroup.IsReduced.red_iff_eq whole_is_reduced).mp badred

      have so: l.length = x2.length := by
        have better: l = x2 :=  (List.cons_eq_cons.mp badeq).right
        rw [better]
      have diff_len : _:= FreeGroup.Red.Step.length pl
      linarith [so, diff_len]


    have bad :_ := calc FreeGroup.toWord x
      _ = FreeGroup.toWord (σ * (σ⁻¹ * x)) := by simp
      _ = FreeGroup.reduce (FreeGroup.toWord (σ) ++ FreeGroup.toWord (σ⁻¹ * x)) := by exact FreeGroup.toWord_mul σ (σ⁻¹ * x)
      _ = FreeGroup.reduce ([((σchar), true)] ++ FreeGroup.toWord (σ⁻¹ * x)) := by rw [show σ = FreeGroup.of σchar from rfl, FreeGroup.toWord_of σchar, show σchar = (0: Fin 2) from rfl]
      _ = FreeGroup.reduce ([(σchar, true)] ++ (σchar, false)::x2 ) := by rw [px2]
      _ = FreeGroup.reduce (x2) := by apply FreeGroup.reduce.Step.eq stepx2
      _ = x2:= by apply FreeGroup.IsReduced.reduce_eq x2_is_reduced

    have bad3: x2 = (0, true) :: x1 := Eq.trans bad.symm px1
    have bad4: FreeGroup.toWord (σ⁻¹ * x) = (0, false)::(0, true)::x1 := by
      rwa [bad3] at px2

    have step: FreeGroup.Red.Step (FreeGroup.toWord (σ⁻¹ * x)) x1 := by
      rw [bad4]
      exact FreeGroup.Red.Step.cons_not
    let L1 := (0, false) :: (0, not false) ::x1


    exact ((FreeGroup.isReduced_iff_not_step.mp whole_is_reduced) x1) step



  have pdBs :  (∀ i j : Fin n, (i ≠ j) → Disjoint (Bs i) (Bs j)) := by
      intro i j ineqj
      apply Set.disjoint_iff.mpr
      simp
      have branchi : i = 0 ∨ i = 1 := split2 i
      have branchj : j = 0 ∨ j = 1 := split2 j
      obtain i0 | i1 := branchi
      obtain j0 | j1 := branchj
      --
      simp [i0, j0] at ineqj
      --
      simp [i0, j1]
      simp [Bs]
      exact disσσ
      --
      obtain j0 | j1 := branchj
      simp [i1, j0]

      simp [Bs]
      rwa [Set.inter_comm] at disσσ
      --
      simp [i1, j1] at ineqj



  have coverACs : (⋃ i : Fin n, (As i)) = C := by
      simp [As]
      ext x
      constructor
      rintro ⟨i, pi⟩
      simp at pi
      obtain ⟨y, py⟩ := pi.left
      have branchy : y = 0 ∨ y = 1 := split2 y
      obtain y0 | y1 := branchy
      simp [y0] at py
      rw [←py] at pi
      simp [C]
      exact Or.inl pi.right
      simp [y1] at py
      rw [←py] at pi
      simp [C]
      exact Or.inr pi.right
      --
      intro xinC
      simp [C] at xinC
      rcases xinC with left|right
      simp
      use 0
      simp
      exact left
      simp
      use 1
      simp
      exact right

  have σcoverlem: ∀ x∈Dom, x ∈ σDom ∨ x ∈ σσinvDom := by
    intro x xinDom
    rcases (em (x = 1)) with isone | notone
    have resone: x ∈ σσinvDom := by
      simp [σσinvDom]
      simp [isone]
      simp [σinvDom]
      constructor
      simp [Dom]
      use []
      simp [FreeGroup.invRev]
    right
    exact resone

    set w := FreeGroup.toWord x with wdef
    have notempt :w ≠ [] := by
      rw [wdef]
      apply mt (FreeGroup.toWord_eq_nil_iff.mp)
      exact notone

    set h:= List.head w notempt with hdef
    let xform: w = h::(w.tail) := by
      apply List.eq_cons_of_mem_head?
      simp
      rw [hdef]
      apply List.head?_eq_head notempt
    rw [wdef] at xform

    rcases wopts h with c1 | c2 |c3 |c4
    left
    simp [σDom]
    constructor
    exact xinDom
    use w.tail
    rw [←wdef]
    apply List.eq_cons_of_mem_head?
    simp
    rw [c1] at hdef
    rw [List.head?_eq_head notempt]
    rw [←hdef]
    simp [σchar]

    --
    right
    simp [σσinvDom]
    simp [σinvDom]
    constructor
    simp [Dom]
    use x.toWord


    rw [FreeGroup.toWord_mul]
    simp
    simp [FreeGroup.invRev]
    rw [xform]
    simp
    simp [c2]
    --
    right
    simp [σσinvDom]
    simp [σinvDom]
    constructor
    simp [Dom]
    use x.toWord
    rw [FreeGroup.toWord_mul]
    simp
    simp [FreeGroup.invRev]
    rw [xform]
    simp
    simp [c3]
    tauto
    --
    right
    simp [σσinvDom]
    simp [σinvDom]
    constructor
    simp [Dom]
    use x.toWord
    rw [FreeGroup.toWord_mul]
    simp
    simp [FreeGroup.invRev]
    rw [xform]
    simp
    simp [c4]



  have coverBGCs : (⋃ i : Fin n, (Bs i)) = Dom := by
      simp [Bs]
      ext x
      constructor
      rintro ⟨i, pi⟩
      simp at pi
      obtain ⟨y, py⟩ := pi.left
      have branchy : y = 0 ∨ y = 1 := split2 y
      obtain y0 | y1 := branchy
      simp [y0] at py
      rw [←py] at pi
      simp [Dom]
      simp [Dom]
      --
      intro xinDom
      rcases (σcoverlem x xinDom) with left | right
      simp
      use 0
      simp
      exact left
      simp
      use 1
      simp
      exact right



  have siginv_lem : (fun x ↦ σ⁻¹ * x) ⁻¹' σinvDom = σσinvDom := by
    simp [σσinvDom, σinvDom]



  let g: Fin n → FG2 := ![1, σ]

  have pmap_c:   (∀ i : Fin n, ((fun (x: FG2) ↦ (g i) * x) '' (As i)) = Bs i) := by
    intro i
    rcases split2 i with vzero | vone
    simp [As, Bs]
    simp [vzero]
    simp [g]
    ---
    simp [As, Bs]
    simp [vone]
    simp [g]
    exact siginv_lem







  have equiCDom: Equidecomposible FG2 C Dom := ⟨n, As, Bs, pdAs, pdBs, coverACs, coverBGCs, g, pmap_c⟩
  exact equiCDom



-- Equidecomposible FG2 D Dom
  let n := 2
  let As := ![τDom, τinvDom]
  let ττinvDom := (fun x ↦ τ * x) '' τinvDom
  let Bs := ![τDom, ττinvDom]
  have disτ: τDom ∩ τinvDom = ∅ := by
    simp [τDom, τinvDom]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x xinboth
    simp at xinboth
    obtain ⟨x1, px1⟩ := xinboth.left.right
    obtain ⟨x2, px2⟩ := xinboth.right.right
    rw [px2] at px1
    have head_eq := (List.cons.inj px1).1
    have bool_eq := (Prod.mk.inj head_eq).2
    exact Bool.false_ne_true bool_eq





  have pdAs :  (∀ i j : Fin n, (i ≠ j) → Disjoint (As i) (As j)) := by
      intro i j ineqj
      apply Set.disjoint_iff.mpr
      simp
      have branchi : i = 0 ∨ i = 1 := split2 i
      have branchj : j = 0 ∨ j = 1 := split2 j
      obtain i0 | i1 := branchi
      obtain j0 | j1 := branchj
      --
      simp [i0, j0] at ineqj
      --
      simp [i0, j1]
      simp [As]
      exact disτ
      --
      obtain j0 | j1 := branchj
      simp [i1, j0]
      simp [As]
      rwa [Set.inter_comm] at disτ
      --
      simp [i1, j1] at ineqj

  have disττ: τDom ∩ ττinvDom  = ∅ := by
    simp only [τDom, ττinvDom]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x xinboth
    simp at xinboth
    simp only [τinvDom] at xinboth
    obtain ⟨x1, px1⟩ := xinboth.left.right
    obtain ⟨x2, px2⟩ := xinboth.right.right

    have stepx2: FreeGroup.Red.Step ([(τchar, true)] ++ (τchar, false)::x2)  x2 := by
      exact FreeGroup.Red.Step.cons_not

    have whole_is_reduced : FreeGroup.IsReduced (FreeGroup.toWord (τ⁻¹ * x) ) := by
      exact FreeGroup.isReduced_toWord

    have x2_is_reduced: FreeGroup.IsReduced x2 := by
      rw [px2] at whole_is_reduced
      by_contra cont0
      have ugly:_:= (mt (FreeGroup.isReduced_iff_not_step.mpr)) cont0
      simp at ugly
      obtain ⟨l, pl⟩ := ugly
      have badred: FreeGroup.Red ((τchar, false)::x2) ((τchar, false)::l) :=
        FreeGroup.Red.cons_cons (FreeGroup.Red.Step.to_red pl)
      have badeq: (τchar, false)::l = (τchar, false)::x2 :=
        (FreeGroup.IsReduced.red_iff_eq whole_is_reduced).mp badred

      have so: l.length = x2.length := by
        have better: l = x2 :=  (List.cons_eq_cons.mp badeq).right
        rw [better]
      have diff_len : _:= FreeGroup.Red.Step.length pl
      linarith [so, diff_len]


    have bad :_ := calc FreeGroup.toWord x
      _ = FreeGroup.toWord (τ * (τ⁻¹ * x)) := by simp
      _ = FreeGroup.reduce (FreeGroup.toWord (τ) ++ FreeGroup.toWord (τ⁻¹ * x)) := by exact FreeGroup.toWord_mul τ (τ⁻¹ * x)
      _ = FreeGroup.reduce ([((τchar), true)] ++ FreeGroup.toWord (τ⁻¹ * x)) := by rw [show τ = FreeGroup.of τchar from rfl, FreeGroup.toWord_of τchar, show τchar = (1: Fin 2) from rfl]
      _ = FreeGroup.reduce ([(τchar, true)] ++ (τchar, false)::x2 ) := by rw [px2]
      _ = FreeGroup.reduce (x2) := by apply FreeGroup.reduce.Step.eq stepx2
      _ = x2:= by apply FreeGroup.IsReduced.reduce_eq x2_is_reduced

    have bad3: x2 = (1, true) :: x1 := Eq.trans bad.symm px1
    have bad4: FreeGroup.toWord (τ⁻¹ * x) = (1, false)::(1, true)::x1 := by
      rwa [bad3] at px2

    have step: FreeGroup.Red.Step (FreeGroup.toWord (τ⁻¹ * x)) x1 := by
      rw [bad4]
      exact FreeGroup.Red.Step.cons_not
    let L1 := (0, false) :: (0, not false) ::x1


    exact ((FreeGroup.isReduced_iff_not_step.mp whole_is_reduced) x1) step


  have pdBs :  (∀ i j : Fin n, (i ≠ j) → Disjoint (Bs i) (Bs j)) := by
      intro i j ineqj
      apply Set.disjoint_iff.mpr
      simp
      have branchi : i = 0 ∨ i = 1 := split2 i
      have branchj : j = 0 ∨ j = 1 := split2 j
      obtain i0 | i1 := branchi
      obtain j0 | j1 := branchj
      --
      simp [i0, j0] at ineqj
      --
      simp [i0, j1]
      simp [Bs]
      exact disττ
      --
      obtain j0 | j1 := branchj
      simp [i1, j0]

      simp [Bs]
      rwa [Set.inter_comm] at disττ
      --
      simp [i1, j1] at ineqj

  have coverADs : (⋃ i : Fin n, (As i)) = D := by

      simp [As]
      ext x
      constructor
      rintro ⟨i, pi⟩
      simp at pi
      obtain ⟨y, py⟩ := pi.left
      have branchy : y = 0 ∨ y = 1 := split2 y
      obtain y0 | y1 := branchy
      simp [y0] at py
      rw [←py] at pi
      simp [D]
      exact Or.inl pi.right
      simp [y1] at py
      rw [←py] at pi
      simp [D]
      exact Or.inr pi.right
      --
      intro xinC
      simp [D] at xinC
      rcases xinC with left|right
      simp
      use 0
      simp
      exact left
      simp
      use 1
      simp
      exact right


  have τcoverlem: ∀ x∈Dom, x ∈ τDom ∨ x ∈ ττinvDom := by
    intro x xinDom
    rcases (em (x = 1)) with isone | notone
    have resone: x ∈ ττinvDom := by
      simp [ττinvDom]
      simp [isone]
      simp [τinvDom]
      constructor
      simp [Dom]
      use []
      simp [FreeGroup.invRev]
    right
    exact resone

    set w := FreeGroup.toWord x with wdef
    have notempt :w ≠ [] := by
      rw [wdef]
      apply mt (FreeGroup.toWord_eq_nil_iff.mp)
      exact notone

    set h:= List.head w notempt with hdef
    let xform: w = h::(w.tail) := by
      apply List.eq_cons_of_mem_head?
      simp
      rw [hdef]
      apply List.head?_eq_head notempt
    rw [wdef] at xform

    rcases wopts h with c1 | c2 |c3 |c4
    right
    simp [ττinvDom]
    simp [τinvDom]
    constructor
    simp [Dom]
    use x.toWord


    rw [FreeGroup.toWord_mul]
    simp
    simp [FreeGroup.invRev]
    rw [xform]
    simp
    simp [c1]
    simp [τchar]

    --
    right
    simp [ττinvDom]
    simp [τinvDom]
    constructor
    simp [Dom]
    use x.toWord


    rw [FreeGroup.toWord_mul]
    simp
    simp [FreeGroup.invRev]
    rw [xform]
    simp
    simp [c2]
    --
    left
    simp [τDom]
    constructor
    exact xinDom
    use w.tail
    rw [←wdef]
    apply List.eq_cons_of_mem_head?
    simp
    rw [c3] at hdef
    rw [List.head?_eq_head notempt]
    rw [←hdef]
    simp [τchar]

    --
    right
    simp [ττinvDom]
    simp [τinvDom]
    constructor
    simp [Dom]
    use x.toWord
    rw [FreeGroup.toWord_mul]
    simp
    simp [FreeGroup.invRev]
    rw [xform]
    simp
    simp [c4]


  have coverBGDs : (⋃ i : Fin n, (Bs i)) = Dom := by
      simp [Bs]
      ext x
      constructor
      rintro ⟨i, pi⟩
      simp at pi
      obtain ⟨y, py⟩ := pi.left
      have branchy : y = 0 ∨ y = 1 := split2 y
      obtain y0 | y1 := branchy
      simp [y0] at py
      rw [←py] at pi
      simp [Dom]
      simp [Dom]
      --
      intro xinDom
      rcases (τcoverlem x xinDom) with left | right
      simp
      use 0
      simp
      exact left
      simp
      use 1
      simp
      exact right


  have tauinv_lem : (fun x ↦ τ⁻¹ * x) ⁻¹' τinvDom = ττinvDom := by
    simp [ττinvDom, τinvDom]

  let g: Fin n → FG2 := ![1, τ]
  have pmap_d:   (∀ i : Fin n, ((fun (x: FG2) ↦ (g i) * x) '' (As i)) = Bs i) := by
    intro i
    rcases split2 i with vzero | vone
    simp [As, Bs]
    simp [vzero]
    simp [g]
    ---
    simp [As, Bs]
    simp [vone]
    simp [g]
    exact tauinv_lem


  have equiDDom: Equidecomposible FG2 D Dom := ⟨n, As, Bs, pdAs, pdBs, coverADs, coverBGDs, g, pmap_d⟩
  exact equiDDom


instance finite_chartype: Finite chartype := inferInstance

instance countable_chartype: Countable chartype := by apply Finite.to_countable

instance countable_of_fg2: Countable FG2 := by
  have lists_countable: Countable (List chartype) := _root_.List.countable
  obtain ⟨lists_to_nat, lists_to_nat_is_inj⟩ := (countable_iff_exists_injective (List chartype)).mp lists_countable
  apply (countable_iff_exists_injective FG2).mpr
  let foo: FG2 → ℕ  := lists_to_nat ∘ FreeGroup.toWord
  use foo
  exact Function.Injective.comp lists_to_nat_is_inj FreeGroup.toWord_injective



def FixedPoints {X : Type*} (G: Type*) [Group G] [MulAction G X] (E: Set X): Set X := ⋃ g ∈ (Set.univ: Set G), {x ∈ E | g • x = x}

theorem paradoxical_of_action_of_self_paradoxical {X : Type*} (G: Type*) [Group G] [MulAction G G] [MulAction G X] (Dom: Set X):
  (∀g:G, (f g) '' Dom ⊆ Dom) → SelfParadoxical G → (¬∃ fp: X, fp ∈ FixedPoints G Dom) → Set.Nonempty Dom → Paradoxical G Dom := by
    intro eclosed
    intro ⟨nEmp, A, B, asube, bsube, disjab, equiADom, equiBDom⟩ nofixed nonemptyDom
    obtain ⟨m, As, Cs, pdAs, pdCs, coverAs, coverCs, gA, pmap_a⟩ := equiADom
    obtain ⟨n, Bs, Ds, pdBs, pdDs, coverBs, coverDs, gB, pmap_b⟩ := equiBDom

    let orbits := { (MulAction.orbit G x) | x ∈ Dom}
    have orbit_containment: ∀O ∈ orbits, O ⊆ Dom := by
      intro O Oinorbits
      intro y yinO
      simp [orbits] at Oinorbits
      obtain ⟨x, px⟩ := Oinorbits
      rw [←px.right] at yinO
      simp [MulAction.orbit] at yinO
      obtain ⟨g, pg⟩ := yinO
      have that: y ∈ f g '' Dom := by
        simp
        use x
        constructor
        exact px.left
        exact pg
      exact (eclosed g) that


    let orbits_type := {S : Set X // S ∈ orbits}
    let id: orbits_type → Set X := fun x ↦ x.val

    have nonempty :  ∀ (x : orbits_type), ∃ (y:X), y ∈ (id x) := by
      intro x
      simp [id]
      let p := x.property
      obtain ⟨z, px ⟩ := p
      have triv: (1:G) • z ∈ MulAction.orbit G z := by simp
      rw [px.right] at triv
      use (1:G) • z

    have choice_function_exists:  ∃ f : orbits_type → X, ∀ (x : orbits_type), f x ∈ id x := Classical.axiom_of_choice nonempty
    obtain ⟨choice, pchoice⟩ := choice_function_exists

    let choice_set := Set.range choice
    have cssubDom: choice_set ⊆ Dom := by
      simp [choice_set]
      intro x xinchoice
      simp  at xinchoice
      obtain ⟨y, py⟩ := xinchoice
      have res:_:= pchoice y
      simp [id] at res
      have cont:_ := orbit_containment y
      simp [orbits] at cont
      have more:_ := cont res
      rwa [py] at more


    have pdinter: ∀ (g h : G), (g ≠ h) → Disjoint (f g '' choice_set) (f h '' choice_set) := by
      intro g h gneh
      apply Set.disjoint_iff.mpr
      intro x ⟨ingimage, inhimage⟩
      simp at ingimage
      simp at inhimage
      obtain ⟨yg, pyg⟩ := ingimage
      obtain ⟨yh, pyh⟩ := inhimage
      have ygindom: yg ∈ Dom := by
        exact cssubDom pyg.left

      have yhindom: yh ∈ Dom := by
        exact cssubDom pyh.left

      have lem: g • yg = h • yh := by
        simp [f] at pyg pyh
        rw [pyg.right, pyh.right]

      have lem2: (h⁻¹ * g ) • yg = yh := calc (h⁻¹ * g) • yg
        _ = h⁻¹ • g • yg := by simp [smul_smul]
        _ = h⁻¹ • h • yh := by rw [lem]
        _ = yh := by simp

      have same: yh ∈ MulAction.orbit G yg := by
        simp [MulAction.orbit]
        use h⁻¹ * g

      have res0:  MulAction.orbit G yg = MulAction.orbit G yh := by simp [MulAction.orbit_eq_iff.mpr same]


      let orb_yg := MulAction.orbit G yg
      let orb_yg_t : orbits_type := ⟨orb_yg, (by simp [orbits]; use yg)⟩

      let orb_yh := MulAction.orbit G yh
      let orb_yh_t : orbits_type := ⟨orb_yh, (by simp [orbits]; use yh)⟩

      have eq_orbs: orb_yg_t = orb_yh_t := Subtype.ext res0

      have eq: yg = yh := calc yg
        _ = choice (orb_yg_t) := by
          have know: ∃ y : orbits_type, choice y = yg := by (simp [choice_set] at pyg; exact pyg.left)
          obtain ⟨y, p_yp_is_choice_y⟩ := know
          have so0: (choice y) ∈ (y: Set X) := by apply (pchoice y)
          have so1: yg ∈ (y: Set X) := by rwa [p_yp_is_choice_y] at so0
          have so: y = orb_yg_t := by
            have y_prop: _ := y.property
            obtain ⟨w, pw⟩ := y_prop
            rw  [←pw.right] at so1
            have same_orbs : MulAction.orbit G yg = MulAction.orbit G w := MulAction.orbit_eq_iff.mpr so1
            have vals_match : orb_yg = y.val := by rw [←same_orbs] at pw; exact pw.right
            exact Eq.symm (Subtype.ext vals_match)
          rw [so] at p_yp_is_choice_y
          exact Eq.symm p_yp_is_choice_y

        _ = choice (orb_yh_t) := by rw [eq_orbs]

        _ = yh := by
          have know: ∃ y : orbits_type, choice y = yh := by (simp [choice_set] at pyh; exact pyh.left)
          obtain ⟨y, p_yp_is_choice_y⟩ := know
          have so0: (choice y) ∈ (y: Set X) := by apply (pchoice y)
          have so1: yh ∈ (y: Set X) := by rwa [p_yp_is_choice_y] at so0
          have so: y = orb_yh_t := by
            have y_prop: _ := y.property
            obtain ⟨w, pw⟩ := y_prop
            rw  [←pw.right] at so1
            have same_orbs : MulAction.orbit G yh = MulAction.orbit G w := MulAction.orbit_eq_iff.mpr so1
            have vals_match : orb_yh = y.val := by rw [←same_orbs] at pw; exact pw.right
            exact Eq.symm (Subtype.ext vals_match)
          rw [so] at p_yp_is_choice_y
          exact p_yp_is_choice_y

      simp [eq] at lem2
      have bad : yh ∈ FixedPoints G Dom := by
        simp [FixedPoints]
        constructor
        exact yhindom
        use h⁻¹ * g
      exact nofixed ⟨yh, bad⟩


    let star: Set G → Set X := fun (S: Set G) ↦ ⋃ g ∈ S, f g '' choice_set
    have star_in_dom: ∀ H : Set G, star H ⊆ Dom := by
      intro H
      intro x xin
      simp [star] at xin
      obtain ⟨g, ginH, y, yinchoice, piy⟩ := xin
      rw [←piy]
      have yindom: y ∈ Dom := cssubDom yinchoice
      have better: f g y ∈ f g '' Dom := by
        simp
        use y
      exact (eclosed g) better

    let As' := fun k: Fin m ↦ star (As k)
    let Bs' := fun k: Fin n ↦ star (Bs k)
    let gA' := gA

    let gB' := gB
    let C: Set X := ⋃ i, As' i
    let D: Set X := ⋃ i, Bs' i

    have csube: C ⊆ Dom := by
      simp [C]
      intro i
      simp [As', star_in_dom]
    have dsube: D ⊆ Dom := by
      simp [D]
      intro i
      simp [Bs', star_in_dom]

    have disjcd: Disjoint C D := by
      simp [C, D]
      simp [As', Bs']
      simp [star]
      intro i
      intro j
      intro gbi gbi_in_bsi
      intro gai gai_in_asi
      have neq: gai ≠ gbi := by
        by_contra badeq
        let x := gai
        have xinA: x ∈ A := by
          rw [←coverAs]
          simp [Set.mem_iUnion]
          use j
        have xinB: x ∈ B := by
          rw [←coverBs]
          simp [Set.mem_iUnion]
          use i
          simp [x]
          rw [badeq]
          exact gbi_in_bsi

        exact Set.disjoint_iff.mp disjab ⟨xinA, xinB⟩

      exact pdinter gai gbi neq

    -- let star: Set G → Set X := fun (S: Set G) ↦ ⋃ g ∈ S, f g '' choice_set
    -- let As' := fun k: Fin m ↦ star (As k)
    -- let Bs' := fun k: Fin n ↦ star (Bs k)

    have equiCE : Equidecomposible G C Dom := by
      let Xs' k := (f (gA k)) '' (As' k)
      have pdAs': (∀ i j : Fin m, (i ≠ j) → Disjoint (As' i) (As' j)) := by
        intro i j inej
        apply Set.disjoint_iff.mpr
        simp only [As']
        simp only [star]
        intro x xinBoth
        simp
        simp [Set.mem_iUnion] at xinBoth
        obtain ⟨g1, g1inG, c1, c1inc, pg1⟩ := xinBoth.left
        obtain ⟨g2, g2inG, c2, c2inc, pg2⟩ := xinBoth.right
        have sameg: g1 = g2 := by
          by_contra g1neg2
          have dischoice: _ := pdinter g1 g2 g1neg2
          have choicedisj : _ := Set.disjoint_iff.mp dischoice

          have xinim1 : x ∈ ((f g1) '' choice_set) := by
            simp
            use c1

          have xinim2 : x ∈ ((f g2) '' choice_set) := by
            simp
            use c2

          exact choicedisj ⟨xinim1, xinim2⟩
        have Asdisj:_:= pdAs i j inej
        rw [←sameg] at g2inG
        exact (Set.disjoint_iff.mp Asdisj) ⟨g1inG, g2inG⟩


      have pdXs': (∀ i j : Fin m, (i ≠ j) → Disjoint (Xs' i) (Xs' j)) := by
        intro i j inej
        apply Set.disjoint_iff.mpr
        simp only [Xs']
        intro x xinBoth
        simp
        simp at xinBoth
        obtain ⟨a1, a1inA, pa1⟩ := xinBoth.left
        obtain ⟨a2, a2inA, pa2⟩ := xinBoth.right
        simp [As', star] at a1inA
        simp [As', star ] at a2inA
        obtain ⟨g1, g1inG, c1, c1incs, pg1⟩ := a1inA
        obtain ⟨g2, g2inG, c2, c2incs, pg2⟩ := a2inA
        rw [← pg1] at pa1
        rw [← pg2] at pa2
        have eqggs : (gA i) * g1 = (gA j) * g2 := by
          by_contra ggsne
          have disjgg:_:= pdinter ((gA i) * g1) ((gA j) * g2) ggsne
          have eqdisj:_ := Set.disjoint_iff.mp disjgg
          have xinl : x ∈ (f ((gA i) * g1)) '' choice_set := by
            simp
            use c1
            constructor
            exact c1incs
            simp [f]
            simp [f] at pa1
            rw [←mul_smul] at pa1
            exact pa1

          have xinr : x ∈ (f ((gA j) * g2)) '' choice_set := by
            simp
            use c2
            constructor
            exact c2incs
            simp [f]
            simp [f] at pa2
            rw [←mul_smul] at pa2
            exact pa2
          exact eqdisj ⟨xinl, xinr⟩

        let y := (gA i) * g1
        have yincsi: y ∈ (Cs i) := by
          rw [← pmap_a i]
          simp [y]
          exact g1inG
        have yincsj: y ∈ (Cs j) := by
          rw [← pmap_a j]
          simp [y]
          rw [eqggs]
          simp
          exact g2inG
        have disjcs := pdCs i j inej
        exact Set.disjoint_iff.mp disjcs ⟨yincsi, yincsj⟩


      have coverAs' : (⋃ i : Fin m, (As' i)) = C := by
        simp [As', C]


      have coverXs' : (⋃ i : Fin m, (Xs' i)) = Dom := by
        simp [Xs']
        simp [As']
        simp [star]
        ext x
        constructor
        intro xinunion
        simp [Set.mem_iUnion] at xinunion
        obtain ⟨i, g, ginasi, c, cincs, pigc⟩ := xinunion
        have int : f g c ∈ Dom := by
          have that: f g c ∈ f g '' Dom := by
            simp
            use c
            constructor
            exact cssubDom cincs
            rfl
          exact (eclosed (g)) that
        have int2 : x ∈ f (gA i) '' Dom := by
          rw [←pigc]
          simp
          use (f g c)
        exact (eclosed (gA i)) int2
        --
        intro xindom
        simp [Set.mem_iUnion]
        let orbit_set := MulAction.orbit G x
        have orbit_prop : orbit_set ∈ orbits := by
          simp [orbits]
          simp [orbit_set]
          use x
        let orbit: orbits_type := ⟨orbit_set, orbit_prop⟩
        set c := choice (orbit) with cdef
        have pc :_:= pchoice orbit
        rw [←cdef] at pc
        simp [id] at pc
        simp [orbit] at pc
        simp [orbit_set] at pc
        simp [MulAction.orbit] at pc

        obtain ⟨g, pg⟩ := pc

        have that: ∃ g : G, f g c = x := by
          use g⁻¹
          simp [f]
          rw [←pg]
          simp

        obtain ⟨g, pg⟩ := that
        have ginuniv: g ∈ Set.univ := by simp
        rw [←coverCs] at ginuniv
        simp [Set.mem_iUnion] at ginuniv
        obtain ⟨i, pi⟩ := ginuniv
        rw [←pmap_a i] at pi
        simp at pi
        use i
        use ((gA i)⁻¹ * g)
        constructor
        exact pi
        use c
        constructor
        simp [choice_set]
        use orbit
        rw [←pg]
        simp [f]
        rw [←mul_smul]
        simp


      have pmap_A:   (∀ i : Fin m, (f (gA i) '' (As' i)) = (Xs' i)) := by
        intro i
        simp [As', Xs']

      exact ⟨m, As', Xs', pdAs', pdXs', coverAs', coverXs', gA, pmap_A⟩


    have equiDE : Equidecomposible G D Dom := by
      let Ys' k := (f (gB k)) '' (Bs' k)
      have pdBs': (∀ i j : Fin n, (i ≠ j) → Disjoint (Bs' i) (Bs' j)) := by
        intro i j inej
        apply Set.disjoint_iff.mpr
        simp only [Bs']
        simp only [star]
        intro x xinBoth
        simp
        simp [Set.mem_iUnion] at xinBoth
        obtain ⟨g1, g1inG, c1, c1inc, pg1⟩ := xinBoth.left
        obtain ⟨g2, g2inG, c2, c2inc, pg2⟩ := xinBoth.right
        have sameg: g1 = g2 := by
          by_contra g1neg2
          have dischoice: _ := pdinter g1 g2 g1neg2
          have choicedisj : _ := Set.disjoint_iff.mp dischoice

          have xinim1 : x ∈ ((f g1) '' choice_set) := by
            simp
            use c1

          have xinim2 : x ∈ ((f g2) '' choice_set) := by
            simp
            use c2

          exact choicedisj ⟨xinim1, xinim2⟩
        have Bsdisj:_:= pdBs i j inej
        rw [←sameg] at g2inG
        exact (Set.disjoint_iff.mp Bsdisj) ⟨g1inG, g2inG⟩


      have pdYs' :  (∀ i j : Fin n, (i ≠ j) → Disjoint (Ys' i) (Ys' j)) := by
        intro i j inej
        apply Set.disjoint_iff.mpr
        simp only [Ys']
        intro x xinBoth
        simp
        simp at xinBoth
        obtain ⟨b1, b1inB, pb1⟩ := xinBoth.left
        obtain ⟨b2, b2inB, pb2⟩ := xinBoth.right
        simp [Bs', star] at b1inB
        simp [Bs', star ] at b2inB
        obtain ⟨g1, g1inG, c1, c1incs, pg1⟩ := b1inB
        obtain ⟨g2, g2inG, c2, c2incs, pg2⟩ := b2inB
        rw [← pg1] at pb1
        rw [← pg2] at pb2
        have eqggs : (gB i) * g1 = (gB j) * g2 := by
          by_contra ggsne
          have disjgg:_:= pdinter ((gB i) * g1) ((gB j) * g2) ggsne
          have eqdisj:_ := Set.disjoint_iff.mp disjgg
          have xinl : x ∈ (f ((gB i) * g1)) '' choice_set := by
            simp
            use c1
            constructor
            exact c1incs
            simp [f]
            simp [f] at pb1
            rw [←mul_smul] at pb1
            exact pb1

          have xinr : x ∈ (f ((gB j) * g2)) '' choice_set := by
            simp
            use c2
            constructor
            exact c2incs
            simp [f]
            simp [f] at pb2
            rw [←mul_smul] at pb2
            exact pb2
          exact eqdisj ⟨xinl, xinr⟩

        let y := (gB i) * g1
        have yincsi: y ∈ (Ds i) := by
          rw [← pmap_b i]
          simp [y]
          exact g1inG
        have yincsj: y ∈ (Ds j) := by
          rw [← pmap_b j]
          simp [y]
          rw [eqggs]
          simp
          exact g2inG
        have disjcs := pdDs i j inej
        exact Set.disjoint_iff.mp disjcs ⟨yincsi, yincsj⟩


      have coverBs' : (⋃ i : Fin n, (Bs' i)) = D := by
        simp [Bs', D]

      have coverYs' : (⋃ i : Fin n, (Ys' i)) = Dom := by

        simp [Ys']
        simp [Bs']
        simp [star]
        ext x
        constructor
        intro xinunion
        simp [Set.mem_iUnion] at xinunion
        obtain ⟨i, g, ginbsi, c, cincs, pigc⟩ := xinunion
        have int : f g c ∈ Dom := by
          have that: f g c ∈ f g '' Dom := by
            simp
            use c
            constructor
            exact cssubDom cincs
            rfl
          exact (eclosed (g)) that
        have int2 : x ∈ f (gB i) '' Dom := by
          rw [←pigc]
          simp
          use (f g c)
        exact (eclosed (gB i)) int2
        --
        intro xindom
        simp [Set.mem_iUnion]
        let orbit_set := MulAction.orbit G x
        have orbit_prop : orbit_set ∈ orbits := by
          simp [orbits]
          simp [orbit_set]
          use x
        let orbit: orbits_type := ⟨orbit_set, orbit_prop⟩
        set c := choice (orbit) with cdef
        have pc :_:= pchoice orbit
        rw [←cdef] at pc
        simp [id] at pc
        simp [orbit] at pc
        simp [orbit_set] at pc
        simp [MulAction.orbit] at pc

        obtain ⟨g, pg⟩ := pc

        have that: ∃ g : G, f g c = x := by
          use g⁻¹
          simp [f]
          rw [←pg]
          simp

        obtain ⟨g, pg⟩ := that
        have ginuniv: g ∈ Set.univ := by simp
        rw [←coverDs] at ginuniv
        simp [Set.mem_iUnion] at ginuniv
        obtain ⟨i, pi⟩ := ginuniv
        rw [←pmap_b i] at pi
        simp at pi
        use i
        use ((gB i)⁻¹ * g)
        constructor
        exact pi
        use c
        constructor
        simp [choice_set]
        use orbit
        rw [←pg]
        simp [f]
        rw [←mul_smul]
        simp

      have pmap_B:   (∀ i : Fin n, (f (gB i) '' (Bs' i)) = (Ys' i)) := by
        intro i
        simp [Bs', Ys']

      exact ⟨n, Bs', Ys', pdBs', pdYs', coverBs', coverYs', gB, pmap_B⟩


    exact ⟨nonemptyDom, C, D, csube, dsube, disjcd, equiCE, equiDE⟩



theorem hausdorff_paradox: ∃ D : Set R3, (D ⊆ S2 ∧ Countable D ∧ Paradoxical SO3 (S2 \ D)) := by

  have self_para_embed : SelfParadoxical SATO :=
    self_paradoxical_preserved_by_iso free_group_of_rank_two_is_self_paradoxical sato_fg3_iso

  have subgroup_countable : Countable SATO := Countable.of_equiv FG2 sato_fg3_iso

  have each_fixed_countable : ∀g ∈ SATO, Countable {x ∈ S2 | g • x = x} := by
    intro g g_in_embed
    let case := {x | x ∈ S2 ∧ g • x = x}
    have num_fixed : Nat.card case = 2 := fixed_lemma (g:SO3)
    have is_finite: Finite case := by
      exact (Nat.card_ne_zero.mp (by simp [num_fixed])).right
    exact Finite.to_countable

  -- The set of fixed points
  let D: Set R3 := ⋃ g ∈ SATO, {x ∈ S2 | g • x = x}
  have dsubS2 : D ⊆ S2 := by simp [D]
  have countable_d: Countable D := by
    apply Set.Countable.biUnion
    exact subgroup_countable
    exact each_fixed_countable


  have p_closure : ∀ (g : SATO), (f g) '' (S2 \ D) ⊆ (S2 \ D) := by
    intro g
    simp
    intro x  xinS2mD
    simp
    by_contra bad
    set im := g • x with imdef
    have im_in_s2: im ∈ S2 := by
      have closed:_:= so3_fixes_s2 g.val
      simp [im]
      simp [f] at closed
      have bad:_:= closed (xinS2mD.left)
      simp at bad
      exact bad

    have im_in_D: im ∈ D := by
      by_contra imnotinD
      exact bad ⟨im_in_s2, imnotinD⟩
    have dfining:  ∃h:SATO, h • im = im := by
      simp [D] at im_in_D
      obtain ⟨a, aprop, pa⟩ := im_in_D.right
      use ⟨⟨a, aprop ⟩, pa.left⟩
      simp
      exact pa.right

    --have imdeffull := im = g • x
    obtain ⟨h, ph⟩ := dfining
    rw [imdef] at ph
    let h' := g⁻¹ * h * g
    have also : h' • x = x := calc h' • x
      _ = ((g⁻¹ * h) * g) • x := by simp [h']
      _ = (g⁻¹ * h) • (g • x) := by exact mul_smul (g⁻¹ * h) g x
      _ = (g⁻¹  • (h  • (g • x) )):= by exact mul_smul g⁻¹ h im
      _ = (g⁻¹) • (g • x) := by rw [ph]
      _ = (g⁻¹ * g) • x := by exact (mul_smul g⁻¹ g x).symm
      _ = 1 • x := by simp
      _ = x := by simp

    have bad2 : x ∈ D := by
      simp [D]
      constructor
      exact xinS2mD.left
      use h'
      use h'.val.prop
      simp
      exact also

    exact xinS2mD.right bad2


  have ub_card_D: (Cardinal.mk D) ≤ Cardinal.aleph0  := by
    exact Cardinal.le_aleph0_iff_set_countable.mpr countable_d


  have nonempty_s2md: Set.Nonempty (S2 \ D) := by
    apply Cardinal.diff_nonempty_of_mk_lt_mk
    exact lt_of_le_of_lt ub_card_D lb_card_s2


  have nofixed: (¬∃ fp, fp ∈ (FixedPoints SATO (S2 \ D))) := by
    rintro ⟨fp, pfp ⟩
    rw [FixedPoints, Set.mem_iUnion] at pfp
    obtain ⟨g, gp⟩ := pfp
    rw [Set.mem_iUnion] at gp
    simp at gp
    let g_prop: _ := g.property
    have fp_in_D: fp ∈ D:= by
      simp [D]
      constructor
      · exact gp.left.left
      · use g
        use by simp
        constructor
        simp
        exact gp.right
    exact gp.left.right fp_in_D


  -- Get Paradoxical on the subtype
  have para_subtype : Paradoxical SATO (S2 \ D) :=
    paradoxical_of_action_of_self_paradoxical
    SATO
    (S2 \ D)
    p_closure
    self_para_embed
    nofixed
    nonempty_s2md


  have para: Paradoxical SO3 (S2 \ D) := paradoxical_of_supergroup_of_paradoxical SO3 SATO (S2 \ D) para_subtype

  exact ⟨D, dsubS2, countable_d, para⟩


lemma absorption_lemma {X : Type*} (G: Type*) [Group G] [MulAction G X] (E : Set X)(S: Set X):
    (∃ D : Set X, (D ⊆ E) ∧ (S ⊆ D) ∧ ∃ρ : G, (f ρ) '' D = D \ S ) → Equidecomposible G E  (E \ S) := by

    rintro ⟨D, DsubE, SsubD, ρ, rho_d⟩

    let As := ![(E \ D), D]
    let Bs := ![(E \ D), D \ S]
    have pdA : ∀i j : Fin 2, (i ≠ j) → Disjoint (As i) (As j) := by
      intro i j ineqj
      apply Set.disjoint_iff.mpr
      simp
      have branchi : i = 0 ∨ i = 1 := split2 i
      have branchj : j = 0 ∨ j = 1 := split2 j
      obtain i0 | i1 := branchi
      obtain j0 | j1 := branchj
      --
      simp [i0, j0] at ineqj
      --
      simp [i0, j1]
      simp [As]
      --
      obtain j0 | j1 := branchj
      simp [i1, j0]
      simp [As]
      --
      simp [i1, j1] at ineqj



    have pdB : ∀i j : Fin 2, (i ≠ j) → Disjoint (Bs i) (Bs j) := by
      intro i j ineqj
      apply Set.disjoint_iff.mpr
      simp
      have branchi : i = 0 ∨ i = 1 := split2 i
      have branchj : j = 0 ∨ j = 1 := split2 j
      obtain i0 | i1 := branchi
      obtain j0 | j1 := branchj
      --
      simp [i0, j0] at ineqj
      --
      simp [i0, j1]
      simp [Bs]
      ext x
      constructor
      intro lhs
      simp
      absurd lhs.left.right lhs.right.left
      trivial
      simp
      --
      obtain j0 | j1 := branchj
      simp [i1, j0]
      simp [Bs]
      ext x
      constructor
      intro lhs
      simp
      absurd (lhs.left.left)
      exact lhs.right.right
      simp
      --
      simp [i1, j1] at ineqj


    have coverA: ⋃ i, As i = E := by
      simp [As]
      ext x
      constructor
      rintro ⟨i, pi⟩
      simp at pi
      rcases pi.left with left | right
      rw [left] at pi
      exact DsubE pi.right
      rw [right] at pi
      exact pi.right.left
      --
      intro inE
      rcases (em (x∈D)) with left | right
      simp
      exact Or.inr left
      simp
      exact Or.inl ⟨inE, right⟩


    have coverB: ⋃ i, Bs i = (E \ S) := by
      simp [Bs]
      ext x
      constructor
      rintro ⟨i, pi⟩
      simp at pi
      rcases pi.left with left | right
      rw [left] at pi
      have lem : x ∈ E := DsubE pi.right.left
      have lem2 :_ := pi.right.right
      simp [lem]
      exact lem2
      rw [right] at pi
      have notlem : x ∉ S := by
        intro xinS
        exact pi.right.right (SsubD xinS)
      exact ⟨pi.right.left, notlem⟩

     --
      intro xinEmS
      rcases (em (x∈D)) with inD | notinD
      simp
      exact Or.inr ⟨inD, xinEmS.right⟩
      simp
      exact Or.inl ⟨xinEmS.left, notinD⟩

    let g:= ![(1:G), ρ]

    have pmap: ∀i:Fin 2, (fun x ↦ (g i) • x) '' (As i) = (Bs i) := by
      intro i
      have lem: i = 0 ∨ i = 1 := split2 i
      rcases lem with zero | one
      simp [As, Bs]
      simp [g]
      simp [zero]
      simp [one]
      simp [g]
      simp [As, Bs]
      exact rho_d

    exact ⟨2, As, Bs, pdA, pdB, coverA, coverB, g, pmap⟩

lemma absorption_lemma_2 {X : Type*} (G: Type*) [Group G] [MulAction G X] (E : Set X)(S: Set X):
    (∃ρ : G, (∀i:ℕ, (f ρ)^[i] '' S ⊆ E) ∧ (∀ i :ℕ , Disjoint S  ((f ρ)^[i+1] '' S))) → Equidecomposible G E  (E \ S) := by
    rintro ⟨ρ, sube, disj⟩
    let D := ⋃ k, (f ρ)^[k] '' S
    have pD: (∃ D : Set X, (D ⊆ E) ∧ (S ⊆ D) ∧ ∃ρ : G, (f ρ) '' D = D \ S ) := by
      use D
      constructor
      --  D ⊆ E
      simp [D]
      intro i
      apply Set.image_subset_iff.mp
      exact sube i
      --
      constructor
      simp [D]
      intro d dinS
      simp
      use 0
      simp
      exact dinS
      --
      use ρ
      ext y
      constructor
      intro yinimg
      simp [D] at yinimg
      obtain ⟨i, pi⟩ := yinimg
      obtain ⟨x, px⟩ := pi
      have lem2: y = (f ρ) (f ρ)^[i] x := px.right.symm
      have yinD: y ∈ D := by
        simp [D]
        use i + 1
        use x
        constructor
        exact px.left
        rw [Function.iterate_succ_apply' (f ρ) i x]
        exact lem2.symm
      have ynotinS : y ∉ S := by
        intro yinS
        have dlem:_ := (disj i)
        simp at dlem
        let s:= ((fun a ↦ (f ρ)^[i] (f ρ a)) '' S)
        have slem: y ∈ s := by
          simp [s]
          use x
          constructor
          exact px.left
          have l1: (f ρ)^[i.succ] x = y := by
            let r := px.right
            rw [←Function.iterate_succ_apply' (f ρ) i x] at r
            exact r
          rw [Function.iterate_succ_apply (f ρ) i x] at l1
          exact l1

        simp [Set.disjoint_iff] at dlem
        have bad: y ∈ S ∩ s := by
          exact ⟨yinS, slem⟩
        have badbad: y ∈ (∅: Set X) := by
          rw [←dlem]
          exact bad
        simp at badbad

      exact ⟨yinD, ynotinS⟩

      --

      intro yindms
      simp [D] at yindms
      obtain ⟨i, x, pi⟩ := yindms.left
      have ipos: i ≠ 0 := by
        intro iiszero
        rw [iiszero] at pi
        simp at pi
        rw [pi.right] at pi
        exact yindms.right pi.left
      have othersucc : ∃j: ℕ, (i = j + 1) := by exact Nat.exists_eq_succ_of_ne_zero ipos
      obtain ⟨j, pj⟩  := othersucc
      rw [pj] at pi
      simp [D]
      use j
      use x
      constructor
      · exact pi.left
      rw [Function.iterate_succ_apply' (f ρ) j] at pi
      exact pi.right



    exact absorption_lemma G E S pD



lemma absorption_lemma_3 {X : Type*} (G: Type*) [Group G] [MulAction G X] (E : Set X)(S: Set X):
    (∃ F: ℝ → G, Countable (Bad F S) ∧ (∀r:ℝ, (orbit (F r) S ⊆ E )) ) → Equidecomposible G E  (E \ S) := by

  rintro ⟨F, countable_bad, containment⟩

  have s_sub_e : S⊆E := by
    intro s s_in_S
    let g := F 0
    have lem: orbit g S ⊆ E := containment 0
    simp [orbit] at lem
    exact (lem 0) s_in_S


  have lem_angle: Set.Nonempty ((Set.univ: Set ℝ) \ Bad F S) := by

    have bad_ub : Cardinal.mk (Bad F S) ≤ Cardinal.aleph0 :=
      Cardinal.le_aleph0_iff_set_countable.mpr countable_bad

    have uncountable_reals: Uncountable ↑(Set.univ: Set ℝ) := by
      rw [← not_countable_iff]
      intro h
      have : Set.Countable (Set.univ: Set ℝ) := Set.countable_coe_iff.mpr h
      exact Cardinal.not_countable_real this

    have card_reals : Cardinal.aleph0 < Cardinal.mk (Set.univ: Set ℝ) :=
      Cardinal.aleph0_lt_mk_iff.mpr uncountable_reals

    apply Cardinal.diff_nonempty_of_mk_lt_mk
    exact lt_of_le_of_lt bad_ub card_reals



  let ρ_angle := Classical.choose lem_angle
  let ρ_spec := Classical.choose_spec lem_angle
  have not_bad: ρ_angle ∉ Bad F S := by
    simp [ρ_angle]
    exact ρ_spec.right

  let ρ := F ρ_angle

  have cond1: (∀i:ℕ, (f ρ)^[i] '' S ⊆ E) := by
    have lem0:_ := containment ρ_angle
    simp [orbit] at lem0
    intro i
    have lem1:_:= lem0 i
    simp [ρ]
    exact lem1

  have cond2: (∀ i :ℕ , Disjoint S  ((f ρ)^[i+1] '' S)) := by
    intro i
    simp
    apply Set.disjoint_iff.mpr
    intro bad ⟨bad_in_left, bad_in_right⟩
    simp
    have trouble: ρ_angle ∈ Bad F S:= by
      simp [Bad]
      use i + 1
      constructor
      norm_num
      simp at bad_in_right
      obtain ⟨x, px⟩ := bad_in_right
      use x
      constructor
      exact px.left
      rw [←Function.iterate_succ_apply (f ρ) i x] at px
      rw [←px.right] at bad_in_left
      simp only [ρ] at bad_in_left
      exact bad_in_left

    exact not_bad trouble

  exact absorption_lemma_2 G E S ⟨ρ, cond1, cond2⟩

lemma S2_equidecomposible_of_S2_minus_countable:
∀ S : Set R3, (S ⊆ S2 ∧ Countable S → Equidecomposible SO3 (S2 \ S) S2) := by

  intro S
  rintro ⟨subset_of_s2, countable_S⟩

  let mS := {-x | x ∈ S}

  have countable_mS: Countable mS := by
    simp [mS]
    apply Set.Countable.image countable_S


  let S2plus := S ∪ mS
  have ub_card_plus : (Cardinal.mk S2plus) ≤ Cardinal.aleph0 := by
    simp [S2plus]
    apply Set.countable_union.mpr
    constructor
    exact countable_S
    exact countable_mS


  have lem: Set.Nonempty (S2 \ S2plus) := by
    apply Cardinal.diff_nonempty_of_mk_lt_mk
    exact lt_of_le_of_lt ub_card_plus lb_card_s2

  let spec := Classical.choose_spec lem

  let axis: S2 := ⟨Classical.choose lem, (spec).left⟩
  have polelem1: axis.val ∉ S := by
    by_contra bad
    have so: axis.val ∈ S2plus := Or.inl bad
    simp [axis] at so
    exact spec.right so



  have polelem2: -axis.val ∉ S := by
    by_contra bad
    have inv_bad: axis.val ∈ mS := by
      simp [mS]
      use -axis
      constructor
      exact bad
      simp

    have so: axis.val ∈ S2plus := Or.inr inv_bad
    simp [axis] at so
    exact spec.right so



  let axis_spec := (Classical.choose_spec lem).left
  let F:= (fun θ ↦ rot axis θ)
  have countbad: Countable (Bad F S) := countable_bad_rots S axis ⟨subset_of_s2, countable_S, polelem1, polelem2⟩

  have orbit_containment: (∀r:ℝ, (orbit (F r) S ⊆ S2 )) := by
    intro r
    simp [orbit]
    intro i
    induction' i with i pi
    --
    simp
    exact subset_of_s2
    --
    intro s s_in_S
    simp
    rw [←Function.iterate_succ_apply]
    rw [Function.iterate_succ_apply']
    let w := ((f (F r))^[i] s)
    have lem: w ∈ S2 := by
      exact pi s_in_S
    have mem:f (F r) w ∈ f (F r) '' S2 := Set.mem_image_of_mem (f (F r)) lem
    have lem2: f (F r) w ∈ S2 := rot_lemma mem
    exact lem2

  exact equidecomposibility_symm (
    absorption_lemma_3 SO3 S2 S ⟨(fun θ ↦ rot axis θ), countbad, orbit_containment⟩
    )


theorem banach_tarski_paradox_s2: Paradoxical SO3 S2 := by
  obtain ⟨D, hausD_sub, hausD_countable, hausD_para⟩ := hausdorff_paradox
  have equi: Equidecomposible SO3 (S2 \ D) S2 := S2_equidecomposible_of_S2_minus_countable D ⟨hausD_sub, hausD_countable⟩
  exact paradoxical_of_equidecomposible_of_paradoxical SO3 (S2 \ D) S2 hausD_para equi






theorem banach_tarski_paradox_B3_minus_origin: Paradoxical SO3 B3min := by

  obtain ⟨_, E, F, esubs2, fsubs2, disjef, equiES2, equiFS2⟩ := banach_tarski_paradox_s2

  -- Get the equidecomposibility decompositions
  obtain ⟨m, As, Bs, pdAs, pdBs, coverAs, coverBs, gAB, ABmap⟩ := equiES2
  obtain ⟨n, Cs, Ds, pdCs, pdDs, coverCs, coverDs, gCD, CDmap⟩ := equiFS2

  let As_as_S2 : Fin m → S2_sub := fun k ↦ ⟨As k, (by
        have lem:_ := Set.subset_iUnion As k
        rw [coverAs] at lem

        exact subset_trans lem esubs2
      )⟩
  let Bs_as_S2 : Fin m → S2_sub := fun k ↦ ⟨Bs k, (by
        have lem:_ := Set.subset_iUnion Bs k
        rwa [coverBs] at lem
      )⟩
  let Cs_as_S2 : Fin n → S2_sub := fun k ↦ ⟨Cs k, (by
        have lem:_ := Set.subset_iUnion Cs k
        rw [coverCs] at lem

        exact subset_trans lem fsubs2
      )⟩
  let Ds_as_S2 : Fin n → S2_sub := fun k ↦ ⟨Ds k, (by
        have lem:_ := Set.subset_iUnion Ds k
        rwa [coverDs] at lem
      )⟩

  let As' := fun (k : Fin m) ↦ trunc_cone (As_as_S2 k)
  let Bs' := fun (k : Fin m) ↦ trunc_cone (Bs_as_S2 k)

  let Cs' := fun (k : Fin n) ↦ trunc_cone (Cs_as_S2 k)
  let Ds' := fun (k : Fin n) ↦ trunc_cone (Ds_as_S2 k)

  let E' := trunc_cone ⟨E, esubs2⟩
  let F' := trunc_cone ⟨F, fsubs2⟩
  let S2' := trunc_cone ⟨S2, by simp⟩

  have pdAs': ∀ (i j : Fin m), (i≠j → Disjoint (As' i) (As' j)) := by
    exact disj_lemma m As_as_S2 pdAs

  have pdBs': ∀ (i j : Fin m), (i≠j → Disjoint (Bs' i) (Bs' j)) := by
    exact disj_lemma m Bs_as_S2 pdBs

  have pdCs': ∀ (i j : Fin n), (i≠j → Disjoint (Cs' i) (Cs' j)) := by
    exact disj_lemma n Cs_as_S2 pdCs

  have pdDs': ∀ (i j : Fin n), (i≠j → Disjoint (Ds' i) (Ds' j)) := by
    exact disj_lemma n Ds_as_S2 pdDs

  have coverAs' : ⋃ i, As' i = E' := cover_lemma m As_as_S2 ⟨E, esubs2⟩ coverAs
  have coverBs'' : ⋃ i, Bs' i = S2' := cover_lemma m Bs_as_S2 ⟨S2, by simp⟩ coverBs
  have coverBs' : ⋃ i, Bs' i = B3min := by
    simp [S2'] at coverBs''
    rwa [←b3min_is_trunc_cone_s2] at coverBs''
  have coverCs' : ⋃ i, Cs' i = F' := cover_lemma n Cs_as_S2 ⟨F, fsubs2⟩ coverCs
  have coverDs'' : ⋃ i, Ds' i = S2' := cover_lemma n Ds_as_S2 ⟨S2, by simp⟩ coverDs
  have coverDs' : ⋃ i, Ds' i = B3min := by
    simp [S2'] at coverDs''
    rwa [←b3min_is_trunc_cone_s2] at coverDs''

  -- Our original maps still work
  let gAB_lambdas := fun k: Fin m ↦ fun x: R3 ↦ (gAB k) • x
  let gCD_lambdas := fun k: Fin n ↦ fun x: R3 ↦ (gCD k) • x
  let AB'map : ∀ (i: Fin m), (fun (x: R3) ↦ (gAB i) • x) '' As' i = Bs' i := map_lemma m gAB As_as_S2 Bs_as_S2 ABmap
  let CD'map : ∀ (i: Fin n), (fun (x: R3) ↦ (gCD i) • x) '' Cs' i = Ds' i := map_lemma n gCD Cs_as_S2 Ds_as_S2 CDmap

  let equiE'S2': Equidecomposible SO3 E' B3min := ⟨m, As', Bs', pdAs', pdBs', coverAs', coverBs', gAB, AB'map⟩
  let equiF'S2': Equidecomposible SO3 F' B3min := ⟨n, Cs', Ds', pdCs', pdDs', coverCs', coverDs', gCD, CD'map⟩

  have b3min_nonempty: Set.Nonempty B3min := by
    let hp: R3 := !₂[0, 0, 1]
    have has_mem : hp ∈ B3min  := by
      have nomem: hp ∉ ({origin}: Set R3) := by
        have lem: hp ≠ origin := by
          apply ne_of_apply_ne (fun v : R3 => v 2)
          simp [hp, origin]
        simp [lem]
      have mem: hp ∈ B3 := by
        apply Metric.mem_closedBall.mpr
        simp [hp, dist_eq_norm]
        rw [EuclideanSpace.norm_eq]
        rw [Fin.sum_univ_three]
        simp
      exact ⟨mem, nomem⟩
    use hp

  have e'sub_b3min: E' ⊆ B3min := by
    simp [E']
    exact trunc_cone_sub_ball ⟨E, esubs2⟩

  have f'sub_b3min: F' ⊆ B3min := by
    simp [F']
    exact trunc_cone_sub_ball ⟨F, fsubs2⟩

  have disE'F': Disjoint E' F' := by
    apply Set.disjoint_iff.mpr
    intro x ⟨xini, xinj⟩
    simp
    have badi: normed x ∈ E := by
      exact (trunc_cone_lemma ⟨E, esubs2⟩ x) xini
    have badj: normed x ∈ F := by
      exact (trunc_cone_lemma  ⟨F, fsubs2⟩ x) xinj
    exact (Set.disjoint_iff.mp disjef ) ⟨badi, badj⟩

  exact ⟨b3min_nonempty, E', F', e'sub_b3min, f'sub_b3min, disE'F', equiE'S2', equiF'S2'⟩




theorem banach_tarski_paradox_B3: Paradoxical G3 B3 := by

  have pso3b3m : Paradoxical SO3_in_G3 B3min := by
    have that :_ :=paradoxical_preserved_by_iso B3min SO3_into_G3 (Equiv.refl R3) SO3_G3_action_equiv banach_tarski_paradox_B3_minus_origin
    simp at that
    exact that


  have pg3b3m : Paradoxical G3 B3min := paradoxical_of_supergroup_of_paradoxical G3 SO3_in_G3 B3min pso3b3m


  have countbad: Countable (Bad skew_rot {origin})  := countable_bad_skew_rot


  have orbit_containment: (∀r:ℝ, (orbit (skew_rot r) {origin} ⊆ B3 )) := srot_containment

  have equi : Equidecomposible G3 B3 B3min := by exact absorption_lemma_3 G3 B3 {origin} ⟨skew_rot, countbad, orbit_containment⟩

  exact paradoxical_of_equidecomposible_of_paradoxical G3 B3min B3 pg3b3m (equidecomposibility_symm equi)
