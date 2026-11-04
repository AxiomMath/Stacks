module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.ComponentRestriction
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.ExtremallyDisconnectedComponents
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.FaithfullyFlatExtension
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.LocalRings
public import StacksFrontier.AlgebraicGeometry.ProEtale.LocalIso.Flatness
public import StacksFrontier.AlgebraicGeometry.ProEtale.LocalIso.Permanence
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.AlgebraicResidueExtensionWLocal
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.ClopenRefinement
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.IdentifiesLocalRingsIso
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.ProfiniteSpectrumLocalRings
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationColimitIndZariski
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationLimitClosedPoints
public import StacksFrontier.Topology.ExtremallyDisconnected.Characterization
public import StacksFrontier.Topology.ExtremallyDisconnected.Cover
public import StacksFrontier.Topology.Profinite.Characterization
public import StacksFrontier.Topology.Spectral.ComponentSpace
public import StacksCore.Tactic.StacksAttribute

/-!
# W-local rings and the retraction property

For a commutative ring `A`, the retraction property for faithfully flat algebras that identify
local rings, the retraction property for faithfully flat ind-Zariski algebras, and the pair of
conditions "`Spec A` is w-local and `π₀(Spec A)` is extremally disconnected" are all equivalent.

## Main results

* `AlgebraicGeometry.ProEtale.wLocal_extremallyDisconnected_tfae`: the three equivalent
  conditions.
* `AlgebraicGeometry.ProEtale.nonempty_algHom_of_wLocal_extremallyDisconnected`: the retraction
  itself, from the third condition, for every faithfully flat algebra identifying local rings.
* `AlgebraicGeometry.ProEtale.closedPointsHomeomorphConnectedComponents`: in a w-local space the
  closed points are homeomorphic to the space of connected components.
* `AlgebraicGeometry.ProEtale.exists_continuousSection_of_extremallyDisconnected`: a continuous
  surjection onto an extremally disconnected compact Hausdorff space from a compact Hausdorff space
  in another universe has a continuous section.

## Implementation notes

The equivalences are proved as the cycle (1) ⟹ (2) ⟹ (3) ⟹ (1), with (3) ⟹ (1)
(`nonempty_algHom_of_wLocal_extremallyDisconnected`) proved for every faithfully flat algebra that
identifies local rings, so Tag 097G is not used.

The target algebras of the first two conditions live in `Type (max u v)`, so their universe is at
least that of `A`; the index universe of the ind-Zariski presentations is the same. The
intermediate spaces of the third arrow are lifted into that universe where Tag 097D needs them.

## References

* [Stacks Project, Tag 09AZ](https://stacks.math.columbia.edu/tag/09AZ)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

universe u v

/-- In a w-local space, sending a closed point to its connected component is a homeomorphism from
the closed points onto the space of connected components. -/
def closedPointsHomeomorphConnectedComponents (X : Type*) [TopologicalSpace X] [WLocalSpace X] :
    closedPoints X ≃ₜ ConnectedComponents X := by
  have hunique (x : X) : ∃! x₀ : closedPoints X, Specializes x x₀.1 := by
    obtain ⟨c, hc, huniq⟩ := WLocalSpace.existsUnique_closedPoint_specializes x
    exact ⟨⟨c, hc.1⟩, hc.2, fun c' hc' => Subtype.ext (huniq c'.1 ⟨c'.2, hc'⟩)⟩
  have hbij := closedPoints_to_connectedComponents_bijective_of_unique_specialization
    (WLocalSpace.isClosed_closedPoints (X := X)) hunique
  have : CompactSpace (closedPoints X) :=
    isCompact_iff_compactSpace.mp (WLocalSpace.isClosed_closedPoints (X := X)).isCompact
  have : T2Space (ConnectedComponents X) := (connectedComponents_isProfinite X).1
  exact (isHomeomorph_iff_continuous_bijective.mpr
    ⟨ConnectedComponents.continuous_coe.comp continuous_subtype_val, hbij⟩).homeomorph

/-- A continuous surjection onto an extremally disconnected quasi-compact Hausdorff space from a
quasi-compact Hausdorff space in another universe has a continuous section. This is Tag 08YN with
its two spaces in independent universes. -/
theorem exists_continuousSection_of_extremallyDisconnected {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space X]
    [ExtremallyDisconnected X] [CompactSpace Y] [T2Space Y] (f : Y → X) (hf : Continuous f)
    (hfsurj : Function.Surjective f) : ∃ s : X → Y, Continuous s ∧ f ∘ s = id := by
  let eX : ULift.{max u v} X ≃ₜ X := Homeomorph.ulift
  let eY : ULift.{u} Y ≃ₜ Y := Homeomorph.ulift
  have : CompactSpace (ULift.{max u v} X) := eX.symm.compactSpace
  have : ExtremallyDisconnected (ULift.{max u v} X) := extremallyDisconnected_of_homeo eX.symm
  have : CompactSpace (ULift.{u} Y) := eY.symm.compactSpace
  have hiff : ExtremallyDisconnected (ULift.{max u v} X) ↔
      HasContinuousSectionFromCompactT2 (ULift.{max u v} X) :=
    (extremallyDisconnected_tfae (ULift.{max u v} X)).out 1 2
  obtain ⟨s, hscont, hs⟩ := hiff.mp inferInstance (fun y => eX.symm (f (eY y)))
    (eX.symm.continuous.comp (hf.comp eY.continuous))
    (fun x => ((hfsurj (eX x)).elim fun y hy => ⟨eY.symm y, by simp [hy]⟩))
  refine ⟨fun x => eY (s (eX.symm x)), eY.continuous.comp (hscont.comp eX.symm.continuous),
    funext fun x => ?_⟩
  simpa [Function.comp_def] using congrArg eX (congrFun hs (eX.symm x))

/-- If `Spec A` is w-local and `π₀(Spec A)` is extremally disconnected, then every faithfully flat
`A`-algebra identifying local rings admits a retraction. -/
theorem nonempty_algHom_of_wLocal_extremallyDisconnected (A : Type u) [CommRing A]
    [WLocalSpace (PrimeSpectrum A)]
    (hED : ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum A)))
    (B : Type (max u v)) [CommRing B] [Algebra A B] (hff : Module.FaithfullyFlat A B)
    (hlocalAB : Algebra.IdentifiesLocalRings A B) : Nonempty (B →ₐ[A] A) := by
  classical
  have hffAB : (algebraMap A B).FaithfullyFlat := RingHom.faithfullyFlat_algebraMap_iff.mpr hff
  obtain ⟨I, hzero⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp
    (WLocalSpace.isClosed_closedPoints (X := PrimeSpectrum A))
  obtain ⟨C, hC, algBC, hIndBC, hquotBij, hW_C, hWMapC, hclosedC⟩ :=
    exists_isIndZariski_wLocal_of_isAlgebraic_residueField (algebraMap A B) I hzero.symm
      (fun q _ => isAlgebraic_residueField_of_identifiesLocalRings hlocalAB q)
  let : CommRing C := hC
  let : Algebra B C := algBC
  let : Algebra A C := ((algebraMap B C).comp (algebraMap A B)).toAlgebra
  let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
  let : WLocalSpace (PrimeSpectrum C) := hW_C
  have hlocalAC : Algebra.IdentifiesLocalRings A C :=
    identifiesLocalRings_comp A B C hlocalAB (identifiesLocalRings_of_isIndZariski B C hIndBC)
  have : T2Space (ConnectedComponents (PrimeSpectrum A)) :=
    (connectedComponents_isProfinite (PrimeSpectrum A)).1
  have : T2Space (ConnectedComponents (PrimeSpectrum C)) :=
    (connectedComponents_isProfinite (PrimeSpectrum C)).1
  let eA := closedPointsHomeomorphConnectedComponents (PrimeSpectrum A)
  let eC := closedPointsHomeomorphConnectedComponents (PrimeSpectrum C)
  let fCC : ConnectedComponents (PrimeSpectrum C) → ConnectedComponents (PrimeSpectrum A) :=
    (PrimeSpectrum.continuous_comap (algebraMap A C)).connectedComponentsMap
  have hclosedLift : ∀ a : closedPoints (PrimeSpectrum A),
      ∃ c : closedPoints (PrimeSpectrum C), PrimeSpectrum.comap (algebraMap A C) c.1 = a.1 := by
    intro a
    obtain ⟨qB, hqBspec⟩ :=
      (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp hffAB).2 a.1
    have hIa : I ≤ a.1.asIdeal :=
      (PrimeSpectrum.mem_zeroLocus a.1 (I : Set A)).mp (by rw [← hzero]; exact a.2)
    have hqBcon : qB.asIdeal.comap (algebraMap A B) = a.1.asIdeal :=
      congrArg PrimeSpectrum.asIdeal hqBspec
    have hJq : Ideal.map (algebraMap A B) I ≤ qB.asIdeal := by
      rwa [Ideal.map_le_iff_le_comap, hqBcon]
    let J : Ideal B := Ideal.map (algebraMap A B) I
    let K : Ideal C := Ideal.map (algebraMap B C) J
    let qbarB : Ideal (B ⧸ J) := Ideal.map (Ideal.Quotient.mk J) qB.asIdeal
    have : qbarB.IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
    let e : (B ⧸ J) ≃+* (C ⧸ K) :=
      RingEquiv.ofBijective (algebraMap (B ⧸ J) (C ⧸ K)) hquotBij
    let qbarC : Ideal (C ⧸ K) := qbarB.comap e.symm.toRingHom
    have : qbarC.IsPrime := Ideal.comap_isPrime e.symm.toRingHom qbarB
    let qC : Ideal C := qbarC.comap (Ideal.Quotient.mk K)
    have : qC.IsPrime := Ideal.comap_isPrime (Ideal.Quotient.mk K) qbarC
    have hqbarBcomap : qbarB.comap (Ideal.Quotient.mk J) = qB.asIdeal := by
      rw [show qbarB = Ideal.map (Ideal.Quotient.mk J) qB.asIdeal from rfl,
        Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
        show Ideal.comap (Ideal.Quotient.mk J) ⊥ = J from Ideal.mk_ker]
      exact sup_eq_left.mpr hJq
    have hqbarCcomap : qbarC.comap (algebraMap (B ⧸ J) (C ⧸ K)) = qbarB := by
      rw [show qbarC = qbarB.comap e.symm.toRingHom from rfl, Ideal.comap_comap,
        show e.symm.toRingHom.comp (algebraMap (B ⧸ J) (C ⧸ K)) = RingHom.id (B ⧸ J) from
          RingHom.ext fun x => e.symm_apply_apply x]
      rfl
    have hquotFactor : (Ideal.Quotient.mk K).comp (algebraMap A C) =
        (algebraMap (B ⧸ J) (C ⧸ K)).comp
          ((Ideal.Quotient.mk J).comp (algebraMap A B)) :=
      RingHom.ext fun _ => rfl
    have hcontract : qC.comap (algebraMap A C) = a.1.asIdeal := by
      rw [show qC = qbarC.comap (Ideal.Quotient.mk K) from rfl, Ideal.comap_comap, hquotFactor,
        ← Ideal.comap_comap, hqbarCcomap, ← Ideal.comap_comap, hqbarBcomap, hqBcon]
    have hcspec : PrimeSpectrum.comap (algebraMap A C) ⟨qC, ‹qC.IsPrime›⟩ = a.1 :=
      PrimeSpectrum.ext hcontract
    exact ⟨⟨⟨qC, ‹qC.IsPrime›⟩, by rw [hclosedC]; exact Set.mem_preimage.mpr (hcspec ▸ a.2)⟩,
      hcspec⟩
  have hfCCsurj : Function.Surjective fCC := by
    intro x
    obtain ⟨a, ha⟩ := eA.surjective x
    obtain ⟨c, hc⟩ := hclosedLift a
    exact ⟨eC c, by
      show ConnectedComponents.mk (PrimeSpectrum.comap (algebraMap A C) c.1) = x
      rw [hc]; exact ha⟩
  obtain ⟨s, hscont, hs⟩ := exists_continuousSection_of_extremallyDisconnected fCC
    (PrimeSpectrum.continuous_comap (algebraMap A C)).connectedComponentsMap_continuous hfCCsurj
  obtain ⟨D, hD, algCD, hIndCD, hCDsurj, hCDembed, hDRange⟩ :=
    exists_surjective_indZariski_range_comap_eq_preimage_components C (Set.range s)
      (isCompact_range hscont).isClosed
  let : CommRing D := hD
  let : Algebra C D := algCD
  let : Algebra A D := ((algebraMap C D).comp (algebraMap A C)).toAlgebra
  let : IsScalarTower A C D := IsScalarTower.of_algebraMap_eq' rfl
  have hRclosed : IsClosed (Set.range (PrimeSpectrum.comap (algebraMap C D))) := by
    rw [hDRange]
    exact (isCompact_range hscont).isClosed.preimage ConnectedComponents.continuous_coe
  have : WLocalSpace (Set.range (PrimeSpectrum.comap (algebraMap C D))) :=
    wLocalSpace_of_isClosed hRclosed
  have : WLocalSpace (PrimeSpectrum D) := wLocalSpace_of_homeomorph hCDembed.toHomeomorph
  have hlocalAD : Algebra.IdentifiesLocalRings A D :=
    identifiesLocalRings_comp A C D hlocalAC (identifiesLocalRings_of_isIndZariski C D hIndCD)
  have hCclosedOfD (q : PrimeSpectrum D) (hq : q ∈ closedPoints (PrimeSpectrum D)) :
      PrimeSpectrum.comap (algebraMap C D) q ∈ closedPoints (PrimeSpectrum C) := by
    have : q.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mp hq
    exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal
      (PrimeSpectrum.comap (algebraMap C D) q)).mpr
      (Ideal.comap_isMaximal_of_surjective (algebraMap C D) hCDsurj)
  have hWMapAD : IsWLocalMap (PrimeSpectrum.comap (algebraMap A D)) := by
    refine ⟨PrimeSpectrum.isSpectralMap_comap (algebraMap A D), fun q hq => ?_⟩
    have hspec : PrimeSpectrum.comap (algebraMap A D) q =
        PrimeSpectrum.comap (algebraMap A C) (PrimeSpectrum.comap (algebraMap C D) q) := rfl
    show IsClosed ({PrimeSpectrum.comap (algebraMap A D) q} : Set (PrimeSpectrum A))
    rw [hspec]
    exact hWMapC.closedPoints_subset_preimage_closedPoints (hCclosedOfD q hq)
  let eD := closedPointsHomeomorphConnectedComponents (PrimeSpectrum D)
  let F : closedPoints (PrimeSpectrum D) → closedPoints (PrimeSpectrum A) := fun q =>
    ⟨PrimeSpectrum.comap (algebraMap A D) q.1,
      hWMapAD.closedPoints_subset_preimage_closedPoints q.2⟩
  let cOf : closedPoints (PrimeSpectrum D) → closedPoints (PrimeSpectrum C) := fun q =>
    ⟨PrimeSpectrum.comap (algebraMap C D) q.1, hCclosedOfD q.1 q.2⟩
  have hFformula (q : closedPoints (PrimeSpectrum D)) : eA (F q) = fCC (eC (cOf q)) := by
    show ConnectedComponents.mk (PrimeSpectrum.comap (algebraMap A D) q.1) =
      (PrimeSpectrum.continuous_comap (algebraMap A C)).connectedComponentsMap
        (ConnectedComponents.mk (PrimeSpectrum.comap (algebraMap C D) q.1))
    rw [Continuous.connectedComponentsMap_mk]
    rfl
  have hcomponentInT (d : closedPoints (PrimeSpectrum D)) : eC (cOf d) ∈ Set.range s := by
    have hr : PrimeSpectrum.comap (algebraMap C D) d.1 ∈
        Set.range (PrimeSpectrum.comap (algebraMap C D)) := ⟨d.1, rfl⟩
    rwa [hDRange] at hr
  have hFsurj : Function.Surjective F := by
    intro a
    let c : closedPoints (PrimeSpectrum C) := eC.symm (s (eA a))
    have hcR : c.1 ∈ Set.range (PrimeSpectrum.comap (algebraMap C D)) := by
      rw [hDRange]
      show eC c ∈ Set.range s
      rw [eC.apply_symm_apply]
      exact ⟨eA a, rfl⟩
    let d : PrimeSpectrum D := hCDembed.toHomeomorph.symm ⟨c.1, hcR⟩
    have hd : PrimeSpectrum.comap (algebraMap C D) d = c.1 :=
      congrArg Subtype.val (hCDembed.toHomeomorph.apply_symm_apply ⟨c.1, hcR⟩)
    have hdclosed : d ∈ closedPoints (PrimeSpectrum D) := by
      have hpre := c.2.preimage (PrimeSpectrum.continuous_comap (algebraMap C D))
      show IsClosed ({d} : Set (PrimeSpectrum D))
      convert hpre using 1
      refine Set.eq_of_subset_of_subset (fun z hz => ?_) (fun z hz => ?_)
      · rw [Set.mem_singleton_iff] at hz
        exact hz ▸ hd
      · exact Set.mem_singleton_iff.mpr (hCDembed.injective (hz.trans hd.symm))
    refine ⟨⟨d, hdclosed⟩, eA.injective ?_⟩
    have hcOf : cOf ⟨d, hdclosed⟩ = c := Subtype.ext hd
    calc eA (F ⟨d, hdclosed⟩) = fCC (eC (cOf ⟨d, hdclosed⟩)) := hFformula ⟨d, hdclosed⟩
      _ = fCC (eC c) := congrArg (fun z => fCC (eC z)) hcOf
      _ = fCC (s (eA a)) := congrArg fCC (eC.apply_symm_apply _)
      _ = eA a := congrFun hs (eA a)
  have hFinj : Function.Injective F := by
    intro d₁ d₂ h12
    obtain ⟨x₁, hx₁⟩ := hcomponentInT d₁
    obtain ⟨x₂, hx₂⟩ := hcomponentInT d₂
    have hfc : fCC (eC (cOf d₁)) = fCC (eC (cOf d₂)) :=
      (hFformula d₁).symm.trans ((congrArg eA h12).trans (hFformula d₂))
    have hxEq : x₁ = x₂ :=
      calc x₁ = fCC (s x₁) := (congrFun hs x₁).symm
        _ = fCC (eC (cOf d₁)) := congrArg fCC hx₁
        _ = fCC (eC (cOf d₂)) := hfc
        _ = fCC (s x₂) := congrArg fCC hx₂.symm
        _ = x₂ := congrFun hs x₂
    have hCpts : cOf d₁ = cOf d₂ := eC.injective (by rw [← hx₁, ← hx₂, hxEq])
    exact Subtype.ext (hCDembed.injective (congrArg Subtype.val hCpts))
  have hcomponents : Function.Bijective
      (PrimeSpectrum.continuous_comap (algebraMap A D)).connectedComponentsMap := by
    have heq : (PrimeSpectrum.continuous_comap (algebraMap A D)).connectedComponentsMap =
        fun x => eA (F (eD.symm x)) := by
      refine funext fun x => ?_
      obtain ⟨q, rfl⟩ := eD.surjective x
      rw [eD.symm_apply_apply]
      rfl
    rw [heq]
    exact Function.Bijective.comp eA.bijective
      (Function.Bijective.comp (⟨hFinj, hFsurj⟩ : Function.Bijective F) eD.symm.bijective)
  let e : A ≃+* D := RingEquiv.ofBijective (algebraMap A D)
    (bijective_of_wLocalMap_identifiesLocalRings hlocalAD hWMapAD hcomponents)
  exact ⟨({ toRingHom := e.symm.toRingHom
            commutes' := fun a => by
              rw [show algebraMap A A a = a from rfl,
                show algebraMap A D a = e a from rfl]
              exact e.symm_apply_apply a } : D →ₐ[A] A).comp
    ({ toRingHom := (algebraMap C D).comp (algebraMap B C)
       commutes' := fun a => rfl } : B →ₐ[A] D)⟩

/-- For a commutative ring `A` the following are equivalent: every faithfully
flat `A`-algebra identifying local rings admits a retraction; every faithfully flat ind-Zariski
`A`-algebra admits a retraction; `Spec A` is w-local and `π₀(Spec A)` is extremally
disconnected. -/
@[stacks 09AZ]
theorem wLocal_extremallyDisconnected_tfae (A : Type u) [CommRing A] :
    List.TFAE
      [∀ (B : Type (max u v)) [CommRing B] [Algebra A B],
          Module.FaithfullyFlat A B → Algebra.IdentifiesLocalRings A B → Nonempty (B →ₐ[A] A),
        ∀ (B : Type (max u v)) [CommRing B] [Algebra A B],
          Module.FaithfullyFlat A B →
            IsIndZariski.{u, max u v, max u v} A B → Nonempty (B →ₐ[A] A),
        WLocalSpace (PrimeSpectrum A) ∧
          ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum A))] := by
  tfae_have h12 : 1 → 2 := fun h B _ _ hff hInd =>
    h B hff (identifiesLocalRings_of_isIndZariski A B hInd)
  tfae_have h23 : 2 → 3 := fun h =>
    ⟨wLocalSpace_of_indZariski_faithfullyFlat_retracts A h,
      extremallyDisconnected_of_indZariski_faithfullyFlat_retracts A h⟩
  tfae_have h31 : 3 → 1 := by
    intro h B _ _ hff hlocal
    have : WLocalSpace (PrimeSpectrum A) := h.1
    exact nonempty_algHom_of_wLocal_extremallyDisconnected A h.2 B hff hlocal
  tfae_finish

end AlgebraicGeometry.ProEtale

end
