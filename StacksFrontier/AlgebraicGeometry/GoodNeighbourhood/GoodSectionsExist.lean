module

public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.BoundaryBadLocus
public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.AmpleSectionMeetsCurve
public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.PartialIdeal
public import StacksFrontier.AlgebraicGeometry.Variety.Bertini.ProjectiveDivisorReduction
public import StacksFrontier.AlgebraicGeometry.AmplePositivePower.Basic

/-!
# Good sections exist

Let `X̄` be a normal integral projective scheme over an algebraically closed field `k`, `W ⊆ X̄`
an open smooth of relative dimension `d ≥ 1` over `k` and `x ∈ W` a closed point. Then some
invertible module on `X̄` has good sections through `x`
(`AlgebraicGeometry.GoodNeighbourhood.GoodSections`): this is
`AlgebraicGeometry.GoodNeighbourhood.existsGoodSections`, the Bertini input of SGA 4,
Exposé XI, Proposition 3.3.

## Main definitions

* `AlgebraicGeometry.GoodNeighbourhood.CutInvariant`: what holds after `j` cuts.

## Main results

* `AlgebraicGeometry.GoodNeighbourhood.exists_cutInvariant`: the `d - 1` sections exist.
* `AlgebraicGeometry.GoodNeighbourhood.existsGoodSections`: good sections exist.
-/


@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Ample Stacks.ProjectiveFromSections Stacks.SectionsVanishingOnSubscheme Stacks.Chow

universe u

namespace AlgebraicGeometry.GoodNeighbourhood

attribute [local instance] Stacks.SectionsVanishingOnSubscheme.isInvertible_of_isInvertibleModule

section PartialIdeal

variable {X : Scheme.{u}} (L : X.Modules)
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] {c : ℕ}

/-- `V(v₁, …, v_m)` only depends on the first `m` sections. -/
theorem partialIdeal_congr {v v' : Fin c → Γ(L, ⊤)} (m : ℕ)
    (h : ∀ i : Fin c, i.val < m → v i = v' i) : partialIdeal L v m = partialIdeal L v' m := by
  simp only [partialIdeal]
  refine iSup_congr fun i => iSup_congr fun hi => ?_
  rw [h i hi]

/-- `V(v₁, …, v_m) ⊆ V(v_j)` for `j < m`. -/
theorem zeroScheme_le_partialIdeal (v : Fin c → Γ(L, ⊤)) (m : ℕ) (j : Fin c) (hj : j.val < m) :
    zeroScheme X L (v j) ≤ partialIdeal L v m :=
  le_iSup₂_of_le (f := fun (j : Fin c) (_ : j.val < m) => zeroScheme X L (v j)) j hj le_rfl

end PartialIdeal

/-- A point of a closed subscheme lies on its support. -/
theorem subschemeι_mem_support {X : Scheme.{u}} (T : X.IdealSheafData) (η : T.subscheme) :
    T.subschemeι η ∈ T.support := by
  change T.subschemeι η ∈ (T.support : Set X)
  rw [← Scheme.IdealSheafData.range_subschemeι]
  exact ⟨η, rfl⟩

/-- **A scheme is smooth of relative dimension `d` at the points of an open smooth of relative
dimension `d`**, in the spelling `SubschemeSmoothAt` for the closed subscheme `⊥`. -/
theorem subschemeSmoothAt_bot_of_mem {X S : Scheme.{u}} (f : X ⟶ S) (W : X.Opens) (d : ℕ)
    [SmoothOfRelativeDimension d (W.ι ≫ f)] {x : X} (hx : x ∈ W) :
    SubschemeSmoothAt f (⊥ : X.IdealSheafData) d x := by
  have : IsIso (⊥ : X.IdealSheafData).subschemeι :=
    (Scheme.isIso_subschemeι_iff_eq_bot _).mpr rfl
  set ρ := (⊥ : X.IdealSheafData).subschemeι
  have hρx : ρ (inv ρ x) = x := by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  refine ⟨inv ρ x, hρx, ρ ⁻¹ᵁ W, show ρ (inv ρ x) ∈ W by rw [hρx]; exact hx, ?_⟩
  have heq : (ρ ⁻¹ᵁ W).ι ≫ ρ ≫ f = (ρ ∣_ W) ≫ W.ι ≫ f := by
    rw [← reassoc_of% (morphismRestrict_ι ρ W)]
  rw [heq]
  have h' : SmoothOfRelativeDimension (0 + d) ((ρ ∣_ W) ≫ W.ι ≫ f) := inferInstance
  simpa only [zero_add] using h'

section Cuts

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))

/-- The members of `V_n` vanish on `V(I)`: their zero schemes contain it. -/
theorem zeroScheme_vsec_le {L : X.Modules} [IsInvertibleModule X L] (I : X.IdealSheafData)
    (n : ℤ) (v : vanishingSections k p I L n) :
    zeroScheme X (tensorPowModule X L n) (vsec p n v) ≤ I :=
  OrderDual.toDual_le_toDual.mp ((zeroScheme_isGreatest_vanishingClosedSubscheme X _ _).2
    ((mem_vanishingSections_iff k p I L n v).mp v.2))

/-- **What holds after `j` cuts.** For sections `s₁, …, s_{d-1}` of `ℒ^{⊗ n}` and closed
subschemes `B`, `Y`: the points of `B ∩ V(s₁, …, s_j)` have dimension at most `d - 2 - j`, the
points of `Y ∩ V(s₁, …, s_j)` dimension at most `d - 1 - j`, and each `s_{m+1}` with `m < j` cuts
the smooth loci of `V(s₁, …, s_m)` and of `Y ∩ V(s₁, …, s_m)` well. -/
def CutInvariant (n : ℤ) {L : X.Modules} [IsInvertibleModule X L] (B Y : X.IdealSheafData)
    (d j : ℕ) (s : Fin (d - 1) → Γ(tensorPowModule X L n, ⊤)) : Prop :=
  (∀ z ∈ (B ⊔ partialIdeal (tensorPowModule X L n) s j).support,
    relativeDimension (fieldChowSituation k).dimensionFunction p z + 2 + j ≤ d) ∧
  (∀ z ∈ (Y ⊔ partialIdeal (tensorPowModule X L n) s j).support,
    relativeDimension (fieldChowSituation k).dimensionFunction p z + 1 + j ≤ d) ∧
  ∀ m : Fin (d - 1), m.val < j →
    CutGood p n (partialIdeal (tensorPowModule X L n) s m) (d - m - 1) (s m) ∧
    CutGood p n (Y ⊔ partialIdeal (tensorPowModule X L n) s m) (d - m - 2) (s m)

/-- **Before any cut** the invariant is the dimension bound on `B` and `Y`. -/
theorem cutInvariant_zero (n : ℤ) {L : X.Modules} [IsInvertibleModule X L]
    (B Y : X.IdealSheafData) (d : ℕ)
    (hB : ∀ z ∈ B.support, relativeDimension (fieldChowSituation k).dimensionFunction p z + 2 ≤ d)
    (hY : ∀ z ∈ Y.support, relativeDimension (fieldChowSituation k).dimensionFunction p z + 1 ≤ d)
    (s : Fin (d - 1) → Γ(tensorPowModule X L n, ⊤)) : CutInvariant p n B Y d 0 s := by
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun m hm => absurd hm (Nat.not_lt_zero _)⟩
  · rw [partialIdeal_zero, sup_bot_eq] at hz
    have := hB z hz
    omega
  · rw [partialIdeal_zero, sup_bot_eq] at hz
    have := hY z hz
    omega

/-- **One more cut.** If the invariant holds after `j < d - 1` cuts by members of `V_n`, then it
holds after `j + 1` cuts by some members of `V_n`. -/
theorem exists_cutInvariant_succ [IsAlgClosed k] [IsProper p] {L : X.Modules}
    [IsInvertibleModule X L] (n : ℤ) (I : X.IdealSheafData) (c : X)
    (hc : IsClosed ({c} : Set X)) (hI : ∀ y ∈ I.support, y = c)
    (hgen : GeneratesOffSupport k p I L n)
    (himm : ∀ (N : ℕ) (b : Module.Basis (Fin (N + 1)) k (vanishingSections k p I L n)),
      IsImmersion (toProjectiveSpaceOfVanishingSections k p b hgen))
    {q : ℕ} {b' : Module.Basis (Fin (q + 1)) k
      (Stacks.Bertini.globalSections k p (tensorPowModule X L n))}
    {hb' : (ambientFamilyDivisors k p (L := L) n).GeneratesBy b'}
    (himm' : (ambientFamilyDivisors k p (L := L) n).IsImmersive b' hb')
    (hfin : Module.finrank k (subschemeSections k p I (L := L) n) ≤ 1)
    (B Y : X.IdealSheafData) (hcB : c ∉ B.support) (hcY : c ∉ Y.support) (d j : ℕ)
    (hj : j < d - 1) (v : Fin (d - 1) → vanishingSections k p I L n)
    (hv : CutInvariant p n B Y d j (fun i => vsec p n (v i))) :
    ∃ v' : Fin (d - 1) → vanishingSections k p I L n,
      CutInvariant p n B Y d (j + 1) (fun i => vsec p n (v' i)) := by
  classical
  have : LocallyOfFiniteType p := inferInstance
  obtain ⟨a, ⟨h1, h2⟩, h3, h4⟩ :=
    (((exists_cutGood p n I c hc hI hgen himm himm'
      (partialIdeal (tensorPowModule X L n) (fun i => vsec p n (v i)) j) (d - j - 1)
      (fun _ => hfin.trans (by omega))).and
    (exists_cutGood p n I c hc hI hgen himm himm'
      (Y ⊔ partialIdeal (tensorPowModule X L n) (fun i => vsec p n (v i)) j) (d - j - 2)
      (fun _ => hfin.trans (by omega)))).and
    ((generalIn_notMem_support_genericPoints p I n hgen
      (B ⊔ partialIdeal (tensorPowModule X L n) (fun i => vsec p n (v i)) j)).and
    (generalIn_notMem_support_genericPoints p I n hgen
      (Y ⊔ partialIdeal (tensorPowModule X L n) (fun i => vsec p n (v i)) j)))).exists
  set jj : Fin (d - 1) := ⟨j, hj⟩
  refine ⟨Function.update v jj a, ?_⟩
  have hupd : ∀ i : Fin (d - 1), i ≠ jj →
      vsec p n (Function.update v jj a i) = vsec p n (v i) := fun i hi => by
    rw [Function.update_of_ne hi]
  have hT : ∀ m ≤ j, partialIdeal (tensorPowModule X L n)
      (fun i => vsec p n (Function.update v jj a i)) m =
        partialIdeal (tensorPowModule X L n) (fun i => vsec p n (v i)) m :=
    fun m hm => partialIdeal_congr _ m fun i hi => hupd i fun h => by
      rw [h] at hi
      exact absurd hi (by simp only [jj]; omega)
  have hT1 : partialIdeal (tensorPowModule X L n)
      (fun i => vsec p n (Function.update v jj a i)) (j + 1) =
        partialIdeal (tensorPowModule X L n) (fun i => vsec p n (v i)) j ⊔
          zeroScheme X (tensorPowModule X L n) (vsec p n a) := by
    rw [partialIdeal_succ _ _ j hj, hT j le_rfl]
    change _ ⊔ zeroScheme X (tensorPowModule X L n) (vsec p n (Function.update v jj a jj)) = _
    rw [Function.update_self]
  obtain ⟨hB, hY, hcut⟩ := hv
  have hoff : ∀ (J : X.IdealSheafData), c ∉ J.support → ∀ (A : X.IdealSheafData)
      (η : (J ⊔ A).subscheme), (J ⊔ A).subschemeι η ∉ I.support := by
    intro J hcJ A η hη
    have hmem := subschemeι_mem_support (J ⊔ A) η
    rw [Scheme.IdealSheafData.support_sup] at hmem
    exact hcJ (hI _ hη ▸ hmem.1)
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun m hm => ?_⟩
  · rw [hT1, ← sup_assoc, Scheme.IdealSheafData.support_sup] at hz
    have := relativeDimension_le_sub_one_of_mem_zeroScheme p _ ((d : ℤ) - 2 - j)
      (fun y hy => by have := hB y hy; omega) _
      (fun η hη => h3 η hη (hoff B hcB _ η)) z hz.1 hz.2
    omega
  · rw [hT1, ← sup_assoc, Scheme.IdealSheafData.support_sup] at hz
    have := relativeDimension_le_sub_one_of_mem_zeroScheme p _ ((d : ℤ) - 1 - j)
      (fun y hy => by have := hY y hy; omega) _
      (fun η hη => h4 η hη (hoff Y hcY _ η)) z hz.1 hz.2
    omega
  · by_cases hmj : m.val < j
    · beta_reduce
      rw [hT m.val hmj.le, hupd m (fun h => by rw [h] at hmj; exact lt_irrefl _ hmj)]
      exact hcut m hmj
    · have hm' : m = jj := Fin.ext (by simp only [jj]; omega)
      subst hm'
      rw [hT j le_rfl]
      change CutGood p n _ _ (vsec p n (Function.update v jj a jj)) ∧
        CutGood p n _ _ (vsec p n (Function.update v jj a jj))
      rw [Function.update_self]
      exact ⟨h1, h2⟩

/-- **The `d - 1` sections exist**: given the dimension bounds on `B` and `Y`, for every
`j ≤ d - 1` the invariant holds after `j` cuts by some members of `V_n`. -/
theorem exists_cutInvariant [IsAlgClosed k] [IsProper p] {L : X.Modules}
    [IsInvertibleModule X L] (n : ℤ) (I : X.IdealSheafData) (c : X)
    (hc : IsClosed ({c} : Set X)) (hI : ∀ y ∈ I.support, y = c)
    (hgen : GeneratesOffSupport k p I L n)
    (himm : ∀ (N : ℕ) (b : Module.Basis (Fin (N + 1)) k (vanishingSections k p I L n)),
      IsImmersion (toProjectiveSpaceOfVanishingSections k p b hgen))
    {q : ℕ} {b' : Module.Basis (Fin (q + 1)) k
      (Stacks.Bertini.globalSections k p (tensorPowModule X L n))}
    {hb' : (ambientFamilyDivisors k p (L := L) n).GeneratesBy b'}
    (himm' : (ambientFamilyDivisors k p (L := L) n).IsImmersive b' hb')
    (hfin : Module.finrank k (subschemeSections k p I (L := L) n) ≤ 1)
    (B Y : X.IdealSheafData) (hcB : c ∉ B.support) (hcY : c ∉ Y.support) (d : ℕ)
    (hB : ∀ z ∈ B.support, relativeDimension (fieldChowSituation k).dimensionFunction p z + 2 ≤ d)
    (hY : ∀ z ∈ Y.support, relativeDimension (fieldChowSituation k).dimensionFunction p z + 1 ≤ d) :
    ∀ j ≤ d - 1, ∃ v : Fin (d - 1) → vanishingSections k p I L n,
      CutInvariant p n B Y d j (fun i => vsec p n (v i)) := by
  intro j hj
  induction j with
  | zero => exact ⟨fun _ => 0, cutInvariant_zero p n B Y d hB hY _⟩
  | succ j ih =>
    obtain ⟨v, hv⟩ := ih (by omega)
    exact exists_cutInvariant_succ p n I c hc hI hgen himm himm' hfin B Y hcB hcY d j
      (by omega) v hv

end Cuts

/-- **Good sections exist** (the Bertini input of SGA 4, Exposé XI, Proposition 3.3). For every
normal integral projective `X̄` over an algebraically closed field `k`, every open `W ⊆ X̄` smooth
of relative dimension `d ≥ 1` over `k` and every closed point `x ∈ W`, some invertible module on
`X̄` has good sections through `x` (`AlgebraicGeometry.GoodNeighbourhood.GoodSections`). -/
theorem existsGoodSections (k : Type u) [Field k] [IsAlgClosed k] : ExistsGoodSections k := by
  intro X p d hproj hint hnorm W hW hd x hxW hx
  classical
  have : IsProper p := isProper_of_isProjectiveMorphism p hproj
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  have : Nonempty X := ⟨x⟩
  have : LocallyOfFiniteType p := inferInstance
  obtain ⟨L, hLinv, -, hL⟩ :=
    Stacks.Algebraization.exists_isRelativelyAmple_of_isProjective k p hproj.isProjective
  let : IsInvertibleModule X L := hLinv
  set Ix := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) with hIxdef
  have hsuppx : (Ix.support : Set X) = {x} := Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hIx : ∀ y ∈ Ix.support, y = x := fun y hy => by
    have h : y ∈ (Ix.support : Set X) := hy
    rw [hsuppx] at h
    exact h
  have hxIx : x ∈ Ix.support := by
    change x ∈ (Ix.support : Set X)
    rw [hsuppx]
    rfl
  have hnot : ∀ y : X, y ∉ (⊤ : X.IdealSheafData).support := fun y hy => by
    change y ∈ ((⊤ : X.IdealSheafData).support : Set X) at hy
    rw [Scheme.IdealSheafData.support_top, TopologicalSpace.Closeds.coe_bot] at hy
    exact hy
  set Y := Scheme.IdealSheafData.vanishingIdeal
    (⟨(W : Set X)ᶜ, W.isOpen.isClosed_compl⟩ : Closeds X) with hYdef
  have hmemY : ∀ z : X, z ∉ W → z ∈ Y.support := fun z hz => by
    change z ∈ (Y.support : Set X)
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hz
  have hxY : x ∉ Y.support := fun h => by
    have h' : x ∈ (Y.support : Set X) := h
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at h'
    exact h' hxW
  set B := Scheme.IdealSheafData.vanishingIdeal
    (notSmoothLocus p (⊥ : X.IdealSheafData) d ⊔ notSmoothLocus p Y (d - 1)) with hBdef
  have hmemB : ∀ z : X, z ∈ B.support ↔
      z ∈ notSmoothLocus p (⊥ : X.IdealSheafData) d ∨ z ∈ notSmoothLocus p Y (d - 1) := by
    intro z
    change z ∈ (B.support : Set X) ↔ _
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hB : ∀ z ∈ B.support,
      relativeDimension (fieldChowSituation k).dimensionFunction p z + 2 ≤ d := by
    intro z hz
    rcases (hmemB z).1 hz with h | h
    · exact relativeDimension_add_two_le_of_not_subschemeSmoothAt_bot p W d z
        ((mem_notSmoothLocus_iff p _ d).1 h).2
    · obtain ⟨hzY, hns⟩ := (mem_notSmoothLocus_iff p Y (d - 1)).1 h
      exact relativeDimension_add_two_le_of_not_subschemeSmoothAt_vanishingIdeal p W d hzY hns
  have hY : ∀ z ∈ Y.support,
      relativeDimension (fieldChowSituation k).dimensionFunction p z + 1 ≤ d :=
    fun z hz => relativeDimension_add_one_le_of_mem_support_vanishingIdeal p W d hz
  have hxB : x ∉ B.support := fun h => by
    rcases (hmemB x).1 h with h | h
    · exact ((mem_notSmoothLocus_iff p _ d).1 h).2 (subschemeSmoothAt_bot_of_mem p W d hxW)
    · exact hxY ((mem_notSmoothLocus_iff p Y (d - 1)).1 h).1
  have hnn : ∀ z : X, 0 ≤ relativeDimension (fieldChowSituation k).dimensionFunction p z :=
    fun z => Stacks.Chow.BertiniChain.relativeDimension_nonneg_of_field k p z
  obtain ⟨m₁, hm₁⟩ := exists_bound_generatesOffSupport_and_isImmersion k p Ix hL
  obtain ⟨m₂, hm₂⟩ :=
    exists_bound_generatesOffSupport_and_isImmersion k p (⊤ : X.IdealSheafData) hL
  obtain ⟨m₃, hm₃⟩ := exists_bound_isImmersive_ambientFamilyDivisors k p hL
  set N : ℕ := max 1 (max m₁.toNat (max m₂.toNat m₃.toNat)) with hNdef
  have hN1 : 1 ≤ N := le_max_left _ _
  have hN₁ : m₁ ≤ (N : ℤ) := (Int.self_le_toNat m₁).trans (by
    exact_mod_cast (le_max_left _ _).trans (le_max_right _ _))
  have hN₂ : m₂ ≤ (N : ℤ) := (Int.self_le_toNat m₂).trans (by
    exact_mod_cast ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _))
  have hN₃ : m₃ ≤ (N : ℤ) := (Int.self_le_toNat m₃).trans (by
    exact_mod_cast ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _))
  obtain ⟨hgenx, himmx⟩ := hm₁ N hN₁
  obtain ⟨hgenT, himmT⟩ := hm₂ N hN₂
  obtain ⟨q, b', hb', himm'⟩ := hm₃ N hN₃
  have hamp : IsAmple X (tensorPowModule X L (N : ℤ)) :=
    Stacks.AmplePositivePower.isAmple_tensorPowModule_of_isAmple L N hN1 hL
  have hfin : Module.finrank k (subschemeSections k p Ix (L := L) (N : ℤ)) ≤ 1 := by
    have hsupp2 : (Ix.support : Set X) = {x, x} := by
      rw [Set.pair_eq_singleton]
      exact hsuppx
    rw [finrank_subschemeSections_eq_finrank_globalSections_of_coe_support_eq_pair k p Ix hx hx
      hsupp2]
    have : IsFinite (Ix.subschemeι ≫ p) :=
      isFinite_subschemeι_comp_of_coe_support_eq_pair k p Ix hx hx hsupp2
    have : IsReduced Ix.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
    have : Subsingleton Ix.subscheme := ⟨fun a b => Ix.subschemeι.isClosedEmbedding.injective
      ((hIx _ (subschemeι_mem_support Ix a)).trans (hIx _ (subschemeι_mem_support Ix b)).symm)⟩
    have : Finite Ix.subscheme := Finite.of_subsingleton
    refine (finrank_globalSections_le_natCard_of_isReduced k (Ix.subschemeι ≫ p)).trans ?_
    exact Finite.card_le_one_iff_subsingleton.mpr inferInstance
  obtain ⟨v, hB', hY', hcut⟩ := exists_cutInvariant p (N : ℤ) Ix x hx hIx hgenx
    (fun N b => (himmx N b).1) himm' hfin B Y hxB hxY d hB hY (d - 1) le_rfl
  set s : Fin (d - 1) → Γ(tensorPowModule X L (N : ℤ), ⊤) := fun i => vsec p (N : ℤ) (v i)
    with hsdef
  set C := partialIdeal (tensorPowModule X L (N : ℤ)) s (d - 1) with hCdef
  have hCB : ∀ z ∈ C.support, z ∉ B.support := fun z hzC hzB => by
    have := hB' z (by rw [Scheme.IdealSheafData.support_sup]; exact ⟨hzB, hzC⟩)
    have := hnn z
    omega
  have hZC : ∀ m (hm : m < d - 1), ∀ z ∈ C.support,
      z ∈ (zeroScheme X (tensorPowModule X L (N : ℤ)) (s ⟨m, hm⟩)).support :=
    fun m hm z hz => Scheme.IdealSheafData.support_antitone
      (zeroScheme_le_partialIdeal _ s (d - 1) ⟨m, hm⟩ hm) hz
  have hxC : x ∈ C.support := by
    have hle : C ≤ Ix := by
      rw [hCdef]
      unfold partialIdeal
      exact iSup₂_le fun j _ => zeroScheme_vsec_le p Ix (N : ℤ) (v j)
    exact Scheme.IdealSheafData.support_antitone hle hxIx
  have h2 : ∀ z ∈ C.support, ∀ m ≤ d - 1,
      SubschemeSmoothAt p (partialIdeal (tensorPowModule X L (N : ℤ)) s m) (d - m) z := by
    intro z hz m hm
    induction m with
    | zero =>
      rw [partialIdeal_zero, Nat.sub_zero]
      by_contra hns
      refine hCB z hz ((hmemB z).2 (Or.inl ((mem_notSmoothLocus_iff p _ d).2 ⟨?_, hns⟩)))
      rw [Scheme.IdealSheafData.support_bot]
      trivial
    | succ m ih =>
      have hm' : m < d - 1 := by omega
      have h := ih (by omega)
      rw [show d - m = d - m - 1 + 1 by omega] at h
      have hc := (hcut ⟨m, hm'⟩ hm').1 z h (hZC m hm' z hz)
      rw [partialIdeal_succ _ s m hm', show d - (m + 1) = d - m - 1 by omega]
      exact hc
  have h3 : ∀ z ∈ C.support, z ∉ W → ∀ m ≤ d - 1,
      SubschemeSmoothAt p (Y ⊔ partialIdeal (tensorPowModule X L (N : ℤ)) s m) (d - 1 - m) z := by
    intro z hz hzW m hm
    induction m with
    | zero =>
      rw [partialIdeal_zero, sup_bot_eq, Nat.sub_zero]
      by_contra hns
      exact hCB z hz ((hmemB z).2 (Or.inr ((mem_notSmoothLocus_iff p Y (d - 1)).2
        ⟨hmemY z hzW, hns⟩)))
    | succ m ih =>
      have hm' : m < d - 1 := by omega
      have h := ih (by omega)
      rw [show d - 1 - m = d - m - 2 + 1 by omega] at h
      have hc := (hcut ⟨m, hm'⟩ hm').2 z h (hZC m hm' z hz)
      rw [partialIdeal_succ _ s m hm', ← sup_assoc, show d - 1 - (m + 1) = d - m - 2 by omega]
      exact hc
  have hCsm : ∀ z ∈ C.support, SubschemeSmoothAt p C (0 + 1) z := fun z hz => by
    have := h2 z hz (d - 1) le_rfl
    rwa [show d - (d - 1) = 0 + 1 by omega] at this
  obtain ⟨w, hw1, hw2, hw3⟩ := ((exists_cutGood p (N : ℤ) (⊤ : X.IdealSheafData) x hx
      (fun y hy => absurd hy (hnot y)) hgenT (fun N b => (himmT N b).1) himm' C 0
      (fun h => absurd h (hnot x))).and
    (((GeneralIn.of_notMem _ (Stacks.Chow.BertiniChain.vanishingAtSubmodule_ne_top k p ⊤ L
      (N : ℤ) hgenT (hnot x))).mono fun w hw =>
        notMem_support_of_notMem_vanishingAtSubmodule p ⊤ (N : ℤ) hw).and
    (generalIn_notMem_support_genericPoints p ⊤ (N : ℤ) hgenT (Y ⊔ C)))).exists
  have h4 : ∀ z ∈ C.support,
      z ∈ (zeroScheme X (tensorPowModule X L (N : ℤ)) (vsec p (N : ℤ) w)).support →
      z ∈ W ∧ SubschemeSmoothAt p
        (C ⊔ zeroScheme X (tensorPowModule X L (N : ℤ)) (vsec p (N : ℤ) w)) 0 z := by
    intro z hz hzw
    refine ⟨?_, hw1 z (hCsm z hz) hzw⟩
    by_contra hzW
    have hmem : z ∈ (Y ⊔ C).support := by
      rw [Scheme.IdealSheafData.support_sup]
      exact ⟨hmemY z hzW, hz⟩
    have := relativeDimension_le_sub_one_of_mem_zeroScheme p (Y ⊔ C) 0
      (fun y hy => by have := hY' y hy; have := hnn y; omega) _
      (fun η hη => hw3 η hη (hnot _)) z hmem hzw
    have := hnn z
    omega
  obtain ⟨e, heC, hew⟩ := exists_mem_support_zeroScheme_of_subschemeSmoothAt k p
    (tensorPowModule X L (N : ℤ)) hamp (vsec p (N : ℤ) w) C 0 (hCsm x hxC)
  exact ⟨tensorPowModule X L (N : ℤ), inferInstance, s, vsec p (N : ℤ) w, hxC, hw2, h2, h3, h4,
    e, heC, hew⟩

end AlgebraicGeometry.GoodNeighbourhood

end
