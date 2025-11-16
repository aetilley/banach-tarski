import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

set_option warningAsError false

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


lemma ml {i j: ℕ} {m n: Fin (i * j)} : m ≠ n → m.divNat ≠ n.divNat ∨ (m.divNat = n.divNat ∧ m.modNat ≠ n.modNat) := by

  contrapose!
  intro lhs
  let eqdiv := lhs.left
  let eqmod := lhs.right eqdiv
  have eq: (m.divNat, m.modNat) = (n.divNat, n.modNat) := by
    apply Prod.ext
    exact eqdiv
    exact eqmod

  have resm : _ := finProdFinEquiv.right_inv m
  have resn : _ := finProdFinEquiv.right_inv n
  calc m
  _ = finProdFinEquiv.toFun (finProdFinEquiv.invFun m) := by rw [resm]
  _ = finProdFinEquiv.toFun ((m.divNat, m.modNat)) := by simp
  _ = finProdFinEquiv.toFun ((n.divNat, n.modNat)) := by rw [eq]
  _ = finProdFinEquiv.toFun (finProdFinEquiv.invFun n) := by simp
  _ = n := by rw [resn]


lemma ml2 {i j: ℕ} {m n: Fin (i * j)} : m ≠ n → m.modNat ≠ n.modNat ∨ (m.modNat = n.modNat ∧ m.divNat ≠ n.divNat) := by
  intro mneqn
  have res :_ := ml mneqn
  tauto


def f {X : Type*} {G: Type*} [Group G] [MulAction G X] (g : G): X → X := fun x: X ↦ g • x

lemma fcomp {X : Type*} {G: Type*} [Group G] [MulAction G X] (g h : G): (fun x:X ↦ (g * h) • x) = (fun x : X ↦ g • x) ∘ (fun x: X ↦ h • x) := by
  simp [mul_smul g h]
  rfl

lemma finj {X : Type*} {G: Type*} [Group G] [MulAction G X] (g: G): Function.Injective (fun x ↦ g • x : X → X) := by
  intro a b eq
  simp [f] at eq
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
    have rest :  ((fun a ↦ gMN i.modNat • a) ∘ fun a ↦ gLM i.divNat • a) '' ((fun a ↦ (gLM i.divNat)⁻¹ • a) '' AMs i.modNat) = BNs i.modNat := by
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

theorem paradoxical_preserved_by_iso {X: Type*} {G H: Type*} [Group G] [Group H] [MulAction G X] [MulAction H X] (E: Set X)(i: G ≃*H ):
(∀x: X, ∀g : G, (i g) • x  = g • x) → Paradoxical G E → Paradoxical H E := sorry

theorem self_paradoxical_preserved_by_iso {G H: Type*} [Group G] [Group H] :
SelfParadoxical G → G ≃* H → SelfParadoxical H := sorry

abbrev FG2 := FreeGroup (Fin 2)

abbrev chartype := Fin 2 × Bool

lemma split2 (i: Fin 2): i = 0 ∨ i = 1 := by
  rcases (em (i=0)) with yes | no
  exact Or.inl yes
  exact Or.inr (Fin.eq_one_of_ne_zero i no)

def σchar := (0: Fin 2)
def τchar := (1: Fin 2)
def σ := FreeGroup.of (σchar)
def τ := FreeGroup.of (τchar)

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
    simp [σDom, σσinvDom]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x xinboth
    simp at xinboth
    simp [σinvDom] at xinboth
    obtain ⟨x1, px1⟩ := xinboth.left.right
    obtain ⟨x2, px2⟩ := xinboth.right.right
    -- second can't start with sigma
    sorry



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
      simp [As, Bs]
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

  have coverlem: ∀ x∈Dom, x ∈ σDom ∨ x ∈ σσinvDom := sorry
  have coverBGCs : (⋃ i : Fin n, (Bs i)) = Dom := by
      simp [As, Bs]
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
      rcases (coverlem x xinDom) with left | right
      simp
      use 0
      simp
      exact left
      simp
      use 1
      simp
      exact right



  have siginv_lem : (fun x ↦ σ⁻¹ * x) ⁻¹' σinvDom = σσinvDom := sorry

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
    simp [τDom, ττinvDom]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x xinboth
    simp at xinboth
    simp [τinvDom] at xinboth
    obtain ⟨x1, px1⟩ := xinboth.left.right
    obtain ⟨x2, px2⟩ := xinboth.right.right
    rw [FreeGroup.toWord_mul] at px2
    rw [px1] at px2
    simp [τ] at px2
    sorry


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

      simp [As, Bs]
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


  have τcoverlem: ∀ x∈Dom, x ∈ τDom ∨ x ∈ ττinvDom := sorry
  have coverBGDs : (⋃ i : Fin n, (Bs i)) = Dom := by
      simp [As, Bs]
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


  have tauinv_lem : (fun x ↦ τ⁻¹ * x) ⁻¹' τinvDom = ττinvDom := sorry
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
    have orbit_containment: ∀O ∈ orbits, O ⊆ Dom := sorry
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
    have pdinter: ∀ (g h : G), (g ≠ h) → Disjoint (f g '' choice_set) (f h '' choice_set) := by
      intro g h gneh
      apply Set.disjoint_iff.mpr
      intro x ⟨ingimage, inhimage⟩
      simp at ingimage
      simp at inhimage
      obtain ⟨yg, pyg⟩ := ingimage
      obtain ⟨yh, pyh⟩ := inhimage
      have ygindom: yg ∈ Dom := sorry
      have yhindom: yh ∈ Dom := sorry

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
    have star_in_dom: ∀ H : Set G, star H ⊆ Dom := sorry
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
      have neq: gai ≠ gbi := sorry
      exact pdinter gai gbi neq


    have equiCE : Equidecomposible G C Dom := by
      let Xs' k := (f (gA k)) '' (As' k)
      have pdAs': (∀ i j : Fin m, (i ≠ j) → Disjoint (As' i) (As' j)) := sorry
      have pdXs' :  (∀ i j : Fin m, (i ≠ j) → Disjoint (Xs' i) (Xs' j)) := sorry
      have coverAs' : (⋃ i : Fin m, (As' i)) = C := sorry
      have coverXs' : (⋃ i : Fin m, (Xs' i)) = Dom := sorry
      have pmap_A:   (∀ i : Fin m, (f (gA i) '' (As' i)) = (Xs' i)) := sorry
      exact ⟨m, As', Xs', pdAs', pdXs', coverAs', coverXs', gA, pmap_A⟩


    have equiDE : Equidecomposible G D Dom := by
      let Ys' k := (f (gB k)) '' (Bs' k)
      have pdBs': (∀ i j : Fin n, (i ≠ j) → Disjoint (Bs' i) (Bs' j)) := sorry
      have pdYs' :  (∀ i j : Fin n, (i ≠ j) → Disjoint (Ys' i) (Ys' j)) := sorry
      have coverBs' : (⋃ i : Fin n, (Bs' i)) = D := sorry
      have coverYs' : (⋃ i : Fin n, (Ys' i)) = Dom := sorry
      have pmap_B:   (∀ i : Fin n, (f (gB i) '' (Bs' i)) = (Ys' i)) := sorry
      exact ⟨n, Bs', Ys', pdBs', pdYs', coverBs', coverYs', gB, pmap_B⟩


    exact ⟨nonemptyDom, C, D, csube, dsube, disjcd, equiCE, equiDE⟩

abbrev R3 := EuclideanSpace ℝ (Fin 3)
def S2: Set R3 := Metric.sphere (0: R3) 1
abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ


-- The standard action given by matrix multiplication.
instance SO3_action_on_R3 : MulAction SO3 R3 where
  smul g v := Matrix.mulVec (g : Matrix (Fin 3) (Fin 3) ℝ) v
  one_smul v := Matrix.one_mulVec v
  mul_smul x y v := (Matrix.mulVec_mulVec v (x : Matrix (Fin 3) (Fin 3) ℝ) (y : Matrix (Fin 3) (Fin 3) ℝ)).symm


abbrev MAT:= Matrix (Fin 3) (Fin 3) ℝ

lemma identity_matrix_mem_SO3 : (1 : MAT) ∈ SO3 := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  constructor
  · rw [Matrix.mem_orthogonalGroup_iff]
    simp [Matrix.transpose_one, Matrix.mul_one]
  · simp [Matrix.det_one]


-- The Sato Subgroup of SO3

def M_s: MAT := !![
  6, 2, 3;
  2, 3, -6;
  -3, 6, 2;
  ]

def M_t : MAT := !![
  2, -6, 3;
  6, 3, 2;
  -3, 2, 6;
]


noncomputable def M_s_normed: MAT := ((1/7):ℝ) • M_s
lemma M_s_normed_is_special : M_s_normed ∈ SO3 := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  constructor
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i j
  simp [M_s_normed, M_s, Matrix.transpose]
  fin_cases i <;> fin_cases j <;> norm_num
  <;> simp [Matrix.vecMul]
  <;> norm_num
  --
  --simp [Matrix.det_apply, M_s_normed, M_s]
  rw [Matrix.det_fin_three]
  rw [M_s_normed, M_s]
  norm_num
  simp
  norm_num



noncomputable def M_t_normed: MAT := ((1/7):ℝ) • M_t
lemma M_t_normed_is_special : M_t_normed ∈ SO3 := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  constructor
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i j
  simp [M_t_normed, M_t, Matrix.transpose]
  fin_cases i <;> fin_cases j <;> norm_num
  <;> simp [Matrix.vecMul]
  <;> norm_num
  --
  --simp [Matrix.det_apply, M_s_normed, M_s]
  rw [Matrix.det_fin_three]
  rw [M_t_normed, M_t]
  norm_num
  simp
  norm_num

noncomputable def s_op_n: SO3 := ⟨M_s_normed, M_s_normed_is_special⟩
noncomputable def t_op_n: SO3 := ⟨M_t_normed, M_t_normed_is_special⟩

noncomputable def s_i_op_n: SO3 := s_op_n⁻¹
noncomputable def t_i_op_n: SO3 := t_op_n⁻¹


def M_s_i: MAT := !![
  6, 2, -3;
  2, 3, 6;
  3, -6, 2;
  ]

example: s_i_op_n.val =  (7 :ℝ)⁻¹ • M_s_i := by
  simp [s_i_op_n]
  simp [Inv.inv]
  simp [star]
  simp [Matrix.transpose]
  simp [s_op_n]
  simp [M_s_normed]
  simp [M_s, M_s_i]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Div.div] <;> rfl


def M_t_i : MAT := !![
  2, 6, -3;
  -6, 3, 2;
  3, 2, 6;
]

example: t_i_op_n.val =  (7 :ℝ)⁻¹ • M_t_i := by
  simp [t_i_op_n]
  simp [Inv.inv]
  simp [star]
  simp [Matrix.transpose]
  simp [t_op_n]
  simp [M_t_normed]
  simp [M_t, M_t_i]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Div.div] <;> rfl


-- The Sato Subgroup of SO3
def sato_generators: Set SO3 := {s_op_n, t_op_n}
def SATO: Subgroup SO3 := Subgroup.closure sato_generators
lemma s_mem: s_op_n ∈ SATO := by
  simp [SATO]
  apply Subgroup.mem_closure_of_mem
  simp [sato_generators]

lemma t_mem: t_op_n ∈ SATO := by
  simp [SATO]
  apply Subgroup.mem_closure_of_mem
  simp [sato_generators]

noncomputable def sato_s: SATO := ⟨s_op_n, s_mem⟩
noncomputable def sato_t: SATO := ⟨t_op_n, t_mem⟩

def sato_generators_ss: Set SATO := {sato_s, sato_t}
noncomputable def sato_fg3_iso_seed: Fin 2 → SATO := ![sato_s, sato_t]

noncomputable def to_sato: FG2 →* SATO := FreeGroup.lift sato_fg3_iso_seed


lemma to_sato_range: (to_sato).range = Subgroup.closure sato_generators_ss := by
  have lem : sato_generators_ss = Set.range sato_fg3_iso_seed :=sorry
  rw [lem]
  apply FreeGroup.lift.range_eq_closure


theorem to_sato_is_surjective: Function.Surjective to_sato := by
  -- There's gotta be a better way.

  rw [← MonoidHom.range_eq_top]

  rw [to_sato_range]
  have h : sato_generators_ss = ((↑) : SATO → SO3) ⁻¹' sato_generators := by
    ext x
    simp [sato_generators_ss, sato_generators, Set.mem_preimage]
    constructor
    simp [sato_s, sato_t]
    · rintro (rfl | rfl)
      · simp
      · simp
    · intro hx
      have : x.val ∈ sato_generators := hx
      cases hx with
      | inl h =>
        have : x = ⟨s_op_n, s_mem⟩ := Subtype.ext h
        left; exact this
      | inr h =>
        have : x = ⟨t_op_n, t_mem⟩ := Subtype.ext h
        right; exact this
  rw [h]
  exact Subgroup.closure_closure_coe_preimage

theorem to_sato_is_injective: Function.Injective to_sato := by
  apply (injective_iff_map_eq_one to_sato).mpr
  intro a
  contrapose!
  intro aneq1
  let w := FreeGroup.toWord a
  have notone :  w ≠ ([]: List chartype) := by
    intro cont
    simp [w] at cont
    exact aneq1 cont

  intro image_is_one

  have pad: ∀ (n:ℤ), (s_op_n)^(-n) * (to_sato a) * (s_op_n)^n = 1 := sorry
  let n_trail_sinvs: ℤ := sorry
  let a2: FG2 := sorry -- FreeGroup.mk σ ^ (-n_trail_sinvs - 1) * a * σ ^ (n_trail_sinvs + 1)
  have still: to_sato a2 = 1 := sorry
  let w2 := FreeGroup.toWord a2
  have check_same: a2 = FreeGroup.mk w2 := FreeGroup.mk_toWord.symm

  have w2_rev := List.reverse w2
  have not_empty: w2_rev ≠ [] := sorry
  have w2_ends_in_sigma : ((w2_rev.head) not_empty)  = (σchar, true) := sorry


  let my_prod:= List.prod (w2.map fun x =>
    cond x.2 (sato_fg3_iso_seed x.1) (sato_fg3_iso_seed x.1)⁻¹)

  have compo : (to_sato a2) = my_prod := by
      simp [to_sato]
      rw [check_same]
      exact FreeGroup.lift.mk


  let N := w2.length

  let Vs: Set R3 := {
    ![3,1,2],
    ![5,4,1],
    ![6,2,4]
  }

  let Vt: Set R3 := {
    ![3,2,6],
    ![5,1,3],
    ![6,4,5]
  }


  let Vtinv: Set R3 := {
    ![3,5,1],
    ![5,6,4],
    ![6,3,2]
  }

  let Vsinv: Set R3 := {
    ![1,5,4],
    ![2,3,1],
    ![4,6,2]
  }

  let mod7 (v: R3) : R3 := ![((v 0) % 7), ((v 1) % 7), ((v 2) % 7)]

  have l1: ∀v ∈ Vs ∪ Vt ∪ Vtinv,  Matrix.mulVec sato_s v ∈ Vs := sorry
  have l2: ∀v ∈ Vsinv ∪ Vt ∪ Vtinv,  Matrix.mulVec (sato_s)⁻¹ v ∈ Vsinv := sorry
  have l3: ∀v ∈ Vt ∪ Vs ∪ Vsinv,  Matrix.mulVec sato_t v ∈ Vt := sorry
  have l4: ∀v ∈ Vtinv ∪ Vs ∪ Vsinv,  Matrix.mulVec (sato_t)⁻¹ v ∈ Vtinv := sorry


  let Invariant (header: chartype) (op:SATO) : Prop :=

    let c1 := mod7 (Matrix.col (op: MAT) 0)

    (c1 ∈ Vs ↔ header = (0, true)) ∧
    (c1 ∈ Vt ↔ header = (1, true)) ∧
    (c1 ∈ Vtinv ↔ header = (1, false)) ∧
    (c1 ∈ Vsinv ↔ header = (0, false))


  let trunc_prod (i: ℕ): SATO := List.prod ((w2.drop (N - i - 1)).map fun x =>
    cond x.2 (sato_fg3_iso_seed x.1) (sato_fg3_iso_seed x.1)⁻¹)

  let header (i: Fin N) : chartype := w2.get i


  have claim : ∀ i : Fin N, Invariant (header i) (trunc_prod i.val) := by
    intro i
    induction' i.1 with i pi
    have triv: (trunc_prod 0) = sato_s := sorry
    rw [triv]
    sorry
    sorry

  have duh: N-1 < N :=sorry

  have last : Invariant _ (trunc_prod (N - 1)) := claim ⟨N-1, duh⟩

  have more : trunc_prod (N - 1) = my_prod := sorry
  have fin : Invariant (header ⟨N-1,duh⟩) (to_sato a2) := sorry

  have thus: to_sato a2 ≠ (1: SATO) := sorry

  exact thus still























theorem to_sato_is_bijective: Function.Bijective to_sato := ⟨to_sato_is_injective, to_sato_is_surjective⟩

noncomputable def iso_forward_equiv := Equiv.ofBijective to_sato to_sato_is_bijective

noncomputable def sato_fg3_iso: FG2 ≃* SATO := MulEquiv.mk' iso_forward_equiv to_sato.map_mul'





lemma fixed_lemma (g: SO3) : Nat.card ({x ∈ S2 | g • x = x}) = 2 := by
  let tspace := R3 →ₗ[ℝ] R3
  let gmap: tspace := Matrix.toLin' g

  have _: {x : R3 | g • x = x} = (LinearMap.ker (gmap-(1: tspace))).carrier := sorry
  have _: Module.finrank ℝ (LinearMap.ker (gmap-(1: tspace))) = 1 := sorry
  have _: ∃v: R3, LinearMap.ker (gmap - 1 : tspace) = {x | ∃s:ℝ,  x = s • v} := sorry
  sorry

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


  have action_preserves : ∀ (g : SATO) (x : R3), x ∈ S2 \ D → (g : SO3) • x ∈ S2 \ D := by sorry

  have nonempty_s2md: Set.Nonempty (S2 \ D) := sorry

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
        simp [gp]
        sorry
    exact gp.left.right fp_in_D


  have p_closure: ∀g:SATO, (f g) '' (S2 \ D) ⊆ (S2 \ D) := sorry

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
      simp [As, Bs]
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
      use 1
      simp
      exact left
      simp
      use 0
      simp
      exact ⟨inE, right⟩


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
      use 1
      simp
      exact  ⟨inD, xinEmS.right⟩

      simp
      use 0
      simp
      exact ⟨xinEmS.left, notinD⟩

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
      intro xinimg
      simp [D] at xinimg
      obtain ⟨x, ps⟩ := xinimg
      obtain ⟨i, pi⟩ := ps.left
      have lem: x ∈ (f ρ)^[i] '' S := by exact pi
      obtain ⟨w, pw⟩ := pi
      rw [←pw.right] at ps
      have lem2: y = (f ρ) (f ρ)^[i] w := ps.right.symm
      have yinD: y ∈ D := by
        simp [D]
        use i + 1
        use w
        constructor
        exact pw.left
        rw [Function.iterate_succ_apply' (f ρ) i w]
        exact lem2.symm
      have ynotinS : y ∉ S := by
        intro yinS
        have dlem:_ := (disj i)
        simp at dlem
        let s:= ((fun a ↦ (f ρ)^[i] (f ρ a)) '' S)
        have slem: y ∈ s := by
          simp [s]
          use w
          constructor
          exact pw.left
          have l1: (f ρ)^[i.succ] w = y := by
            let r := ps.right
            rw [←Function.iterate_succ_apply' (f ρ) i w] at r
            exact r
          rw [Function.iterate_succ_apply (f ρ) i w] at l1
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
      use (f ρ)^[j] x
      constructor
      use j
      use x
      exact ⟨pi.left, rfl⟩
      have lem2: (f ρ)^[j.succ] x = y := by exact pi.right
      rw [Function.iterate_succ_apply' (f ρ) j] at lem2
      exact lem2



    exact absorption_lemma G E S pD

def Bad {X : Type*} {G: Type*} [Group G] [MulAction G X] (F: ℝ → G) (S: Set X): Set ℝ :=
{θ: ℝ | ∃n:ℕ, n > 0 ∧ ∃s∈S, (f (F θ))^[n] s ∈ S}

def orbit {X : Type*} {G: Type*} [Group G] [MulAction G X] (g: G) (S: Set X): Set X :=
⋃ i, (f g)^[i] '' S


lemma absorption_lemma_3 {X : Type*} (G: Type*) [Group G] [MulAction G X] (E : Set X)(S: Set X):
    (∃ F: ℝ → G, Countable (Bad F S) ∧ (∀r:ℝ, (orbit (F r) S ⊆ E )) ) → Equidecomposible G E  (E \ S) := by

  rintro ⟨F, countable_bad, containment⟩

  have s_sub_e : S⊆E := by
    intro s s_in_S
    let g := F 0
    have lem: orbit g S ⊆ E := containment 0
    simp [orbit] at lem
    exact (lem 0) s_in_S

  have unc_reals : ¬ Set.Countable (Set.univ: Set ℝ) := Cardinal.not_countable_real
  have la: ¬Set.Countable ((Set.univ: Set ℝ) \ Bad F S) := sorry
  have lem_angle: Set.Nonempty ((Set.univ: Set ℝ) \ Bad F S) := sorry
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


def K_mat (a: R3): MAT := !![
  0, -(a 2), (a 1);
  (a 2), 0, -(a 0);
  -(a 1), (a 0), 0;
]

-- Rodrigues' formula for the rotation matrix :  I + (sin θ)K + (1-cosθ)K²
noncomputable def rot_mat (ax: S2) (θ:ℝ) : MAT := (1:MAT) + (Real.sin θ)•(K_mat ax) + (1 - Real.cos θ)•((K_mat ax) ^ 2)

noncomputable def rot (ax: R3) (θ:ℝ) : SO3 := by
  -- First normalize the axis to be on S2
  let ax_norm := (1 / ‖ax‖) • ax
  have ax_norm_mem_S2 : ax_norm ∈ S2 := sorry  -- Need to prove normalization gives unit vector
  let M := rot_mat ⟨ax_norm, ax_norm_mem_S2⟩ θ
  -- Now prove M ∈ SO3 using the systematic approach:
  refine ⟨M, ?_⟩
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  constructor
  · rw [Matrix.mem_orthogonalGroup_iff]
    -- M * Mᵀ = 1
    sorry
  · -- M.det = 1
    sorry

lemma rot_lemma: ∀ {axis : R3} {θ:ℝ}, (f (rot axis θ)) '' S2 ⊆ S2 := sorry

lemma S2_equidecomposible_of_S2_minus_countable:
∀ S : Set R3, (S ⊆ S2 ∧ Countable S → Equidecomposible SO3 (S2 \ S) S2) := by

  intro S
  rintro ⟨subset_of_s2, countable_S⟩
  have lem_unc : ¬ Set.Countable S2 := sorry
  have lem_unc2 : ¬ Set.Countable (S2 \ S) := sorry
  have lem: Set.Nonempty (S2 \ S) := sorry
  let axis: R3 := Classical.choose lem
  let axis_spec := (Classical.choose_spec lem).left
  let F:= (fun θ ↦ rot axis θ)
  let Bad := {θ: ℝ | ∃n:ℕ, n > 0 ∧ ∃s∈S, (f (F θ))^[n] s ∈ S}
  have countbad: Countable Bad := sorry

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

def B3: Set R3 := Metric.closedBall (0: R3) 1
def B3min: Set R3 := B3 \ {0}

noncomputable def normed:  R3 → R3 := fun x ↦ (1 / ‖x‖) • x

def S2_sub := {S : Set R3 // S ⊆ S2}
def cone (S: S2_sub) := {x : R3 | ∃ (s : ℝ) (v : R3), (x = s • v) ∧ (v ∈ S.val) ∧ (0 < s) ∧ (s ≤ 1)}
lemma cone_sub_ball : ∀ S: S2_sub, cone S ⊆ B3min := sorry

lemma cone_lemma (S : S2_sub) : ∀ x : R3, x ∈ cone S ↔ (normed x ∈ S.val) := sorry

lemma disj_lemma (n: ℕ) (fam: Fin n → S2_sub)
(disj: ∀ (i j : Fin n), i ≠ j → Disjoint (fam i).val (fam j).val) :
∀ (i j : Fin n), i ≠ j → Disjoint (cone (fam i)) (cone (fam j)) := by
    intro i j inej
    apply Set.disjoint_iff.mpr
    intro x ⟨xini, xinj⟩
    simp
    have badi: normed x ∈ (fam i).val := by
      exact (cone_lemma ( fam i) x).mp xini
    have badj: normed x ∈ (fam j).val := by
      exact (cone_lemma ( fam j) x).mp xinj
    exact (Set.disjoint_iff.mp (disj i j inej)) ⟨badi, badj⟩

lemma cover_lemma (n: ℕ) (fam: Fin n → S2_sub) (T : S2_sub)
(cover: (⋃ i, (fam i).val) = T.val): (⋃ i, cone (fam i)) = cone T:= by
  ext x
  constructor
  --
  intro xincones
  simp at xincones
  obtain ⟨i, pi⟩ := xincones
  have lem : normed x ∈ (fam i).val := (cone_lemma (fam i) x).mp pi
  have last : normed x ∈ T.val := by rw [←cover];  simp; use i
  exact (cone_lemma T x).mpr last

  intro xincone
  have intval: normed x ∈ T.val := (cone_lemma T x).mp xincone
  rw [←cover] at intval; simp at intval
  obtain ⟨i, pi⟩ := intval
  have piece : x ∈ cone (fam i) := by exact (cone_lemma (fam i) x).mpr pi
  simp
  use i

lemma map_lemma (n: ℕ) (map: Fin n -> (R3 → R3))
(famA: Fin n → S2_sub) (famB: Fin n → S2_sub)
(map_prop: ∀ (i: Fin n), (map i) '' (famA i).val = (famB i).val) :
∀ (i: Fin n), (map i) '' cone (famA i) = cone (famB i)  := sorry


lemma b3min_is_cone_s2 : B3min = cone ⟨S2, by simp⟩ := by sorry


def origin := (0: R3)
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

  let As' := fun (k : Fin m) ↦ cone (As_as_S2 k)
  let Bs' := fun (k : Fin m) ↦ cone (Bs_as_S2 k)

  let Cs' := fun (k : Fin n) ↦ cone (Cs_as_S2 k)
  let Ds' := fun (k : Fin n) ↦ cone (Ds_as_S2 k)

  let E' := cone ⟨E, esubs2⟩
  let F' := cone ⟨F, fsubs2⟩
  let S2' := cone ⟨S2, by simp⟩

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
    rwa [←b3min_is_cone_s2] at coverBs''
  have coverCs' : ⋃ i, Cs' i = F' := cover_lemma n Cs_as_S2 ⟨F, fsubs2⟩ coverCs
  have coverDs'' : ⋃ i, Ds' i = S2' := cover_lemma n Ds_as_S2 ⟨S2, by simp⟩ coverDs
  have coverDs' : ⋃ i, Ds' i = B3min := by
    simp [S2'] at coverDs''
    rwa [←b3min_is_cone_s2] at coverDs''

  -- Our original maps still work
  let gAB_lambdas := fun k: Fin m ↦ fun x: R3 ↦ (gAB k) • x
  let gCD_lambdas := fun k: Fin n ↦ fun x: R3 ↦ (gCD k) • x
  let AB'map : ∀ (i: Fin m), (fun (x: R3) ↦ (gAB i) • x) '' As' i = Bs' i := map_lemma m gAB_lambdas As_as_S2 Bs_as_S2 ABmap
  let CD'map : ∀ (i: Fin n), (fun (x: R3) ↦ (gCD i) • x) '' Cs' i = Ds' i := map_lemma n gCD_lambdas Cs_as_S2 Ds_as_S2 CDmap

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
        simp [hp, dist_eq_norm, EuclideanSpace.norm_eq]
        rw [Fin.sum_univ_three]
        simp [hp]
      exact ⟨mem, nomem⟩
    use hp

  have e'sub_b3min: E' ⊆ B3min := by
    simp [E']
    exact cone_sub_ball ⟨E, esubs2⟩

  have f'sub_b3min: F' ⊆ B3min := by
    simp [F']
    exact cone_sub_ball ⟨F, fsubs2⟩

  have disE'F': Disjoint E' F' := by
    apply Set.disjoint_iff.mpr
    intro x ⟨xini, xinj⟩
    simp
    have badi: normed x ∈ E := by
      exact (cone_lemma ⟨E, esubs2⟩ x).mp xini
    have badj: normed x ∈ F := by
      exact (cone_lemma  ⟨F, fsubs2⟩ x).mp xinj
    exact (Set.disjoint_iff.mp disjef ) ⟨badi, badj⟩

  exact ⟨b3min_nonempty, E', F', e'sub_b3min, f'sub_b3min, disE'F', equiE'S2', equiF'S2'⟩


-- Group of Isometries of R3.
abbrev G3: Type := R3 ≃ᵢ R3
-- The standard action given by matrix multiplication.
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


def SO3_in_G3: Subgroup G3 := sorry

def SO3_into_G3: SO3 ≃* SO3_in_G3 := sorry

def SO3_G3_action_equiv : (∀x: R3, ∀g : SO3, (SO3_into_G3 g) • x  = g • x) := sorry


-- The rotation around a line through (0,0,.5) in the x z plane parallel to the x-axis.
def skew_rot (θ: ℝ): G3 := sorry

lemma srot_containment: ∀r:ℝ, orbit (skew_rot r) {origin} ⊆ B3 :=sorry

theorem banach_tarski_paradox_B3: Paradoxical G3 B3 := by

  have pg3b3m : Paradoxical SO3_in_G3 B3min :=
    paradoxical_preserved_by_iso B3min SO3_into_G3 SO3_G3_action_equiv banach_tarski_paradox_B3_minus_origin
  have pg3b3m : Paradoxical G3 B3min := paradoxical_of_supergroup_of_paradoxical G3 SO3_in_G3 B3min pg3b3m


  have countbad: Countable (Bad skew_rot {origin})  := sorry


  have orbit_containment: (∀r:ℝ, (orbit (skew_rot r) {origin} ⊆ B3 )) := srot_containment

  have equi : Equidecomposible G3 B3 B3min := by exact absorption_lemma_3 G3 B3 {origin} ⟨skew_rot, countbad, orbit_containment⟩

  exact paradoxical_of_equidecomposible_of_paradoxical G3 B3min B3 pg3b3m (equidecomposibility_symm equi)
