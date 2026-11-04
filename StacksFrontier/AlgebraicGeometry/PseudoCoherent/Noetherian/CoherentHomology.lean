module

public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Basic
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.Noetherian.BoundedAbove
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.Noetherian.CoherentModule
public import StacksCore.Tactic.StacksAttribute

/-!
# Pseudo-coherence on a Noetherian scheme

Let `X` be a Noetherian scheme and let `E` be an object of `D_QCoh(𝒪_X)`. For an integer `m`,
pseudo-coherence of `E` from degree `m` is equivalent to the conjunction of coherence of `Hⁱ(E)`
for `i ≥ m` and vanishing of `Hⁱ(E)` for `i ≫ 0`. Consequently the pseudo-coherent objects of
`D_QCoh(𝒪_X)` are exactly those of `D⁻_Coh(𝒪_X)`.

Both directions are local. From pseudo-coherence,
the cohomology of a local strictly perfect approximation is coherent and surjects onto that of
`E`, so `Hⁱ(E)` is a quasi-coherent quotient of a coherent module and hence coherent
([Stacks, Tag 01Y1]); the bound above comes from the finitely many nonzero terms of the
approximation and quasi-compactness. Conversely a coherent module is pseudo-coherent in every
degree, by the syzygy induction of
`AlgebraicGeometry.isPseudoCoherentFrom_singleFunctor_zero_of_isCoherent`, and an object which is
bounded above and whose cohomology sheaves are pseudo-coherent in the shifted degrees is
pseudo-coherent, by [Stacks, Tag 09V8].

## Main results

* `AlgebraicGeometry.isCoherent_homology_of_isPseudoCoherentFrom`: the cohomology of an
  `m`-pseudo-coherent object with quasi-coherent cohomology on a locally Noetherian scheme is
  coherent in every degree at least `m`.
* `AlgebraicGeometry.isPseudoCoherentFrom_iff_coherent_homology`: the equivalence in degree `m`.
* `AlgebraicGeometry.isPseudoCoherent_iff_boundedAbove_coherent_homology`: the identification of
  the pseudo-coherent objects of `D_QCoh(𝒪_X)` with `D⁻_Coh(𝒪_X)`.

## Implementation notes

`D_QCoh(𝒪_X)` is the full subcategory of `D(𝒪_X)` cut out by `DerivedCategoryB.derivedCategoryB`
at the quasi-coherence property, that is, the objects all of whose cohomology sheaves are
quasi-coherent; cohomology and pseudo-coherence are read on the underlying object of `D(𝒪_X)`.
`DerivedCategoryB.IsBoundedAbove` is the vanishing of the cohomology in all sufficiently large
degrees, so the right-hand side of the second statement is, written out,
`DerivedCategoryB.derivedCategoryBMinus` at the coherence property, which is `D⁻_Coh(𝒪_X)`.

## References

* [Stacks Project, Tag 08E8](https://stacks.math.columbia.edu/tag/08E8)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
* [Stacks Project, Tag 09V8](https://stacks.math.columbia.edu/tag/09V8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect TopologicalSpace

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

/-- **The cohomology of an `m`-pseudo-coherent object with quasi-coherent cohomology on a
locally Noetherian scheme is coherent in every degree at least `m`.**

Coherence is local, and over an open set carrying a strictly perfect approximation `𝒫 ⟶ 𝒦|_U` of
a complex `𝒦` representing the object the map on degree-`i` cohomology is an epimorphism for
`i ≥ m`; its source is coherent because `𝒫` is strictly perfect, and its target is
quasi-coherent, so [Stacks, Tag 01Y1] applies. -/
public theorem isCoherent_homology_of_isPseudoCoherentFrom (X : Scheme.{u})
    [IsLocallyNoetherian X] (E : DerivedCategory X.Modules) (m : ℤ)
    (hqc : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent)
    (hE : RingedSpace.IsPseudoCoherentFrom (X := X.toRingedSpace) E m)
    (i : ℤ) (hi : m ≤ i) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsCoherent := by
  classical
  obtain ⟨K, hK, ⟨eK⟩⟩ := hE
  have eh : K.homology i ≅ (DerivedCategory.homologyFunctor X.Modules i).obj E :=
    ((DerivedCategory.homologyFunctorFactors (OXMod.{u, u} X.toRingedSpace) i).app K).symm ≪≫
      (DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).mapIso eK
  have hqcK : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (K.homology i) :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso eh.symm (hqc i)
  have hlocal : ∀ y : X.toRingedSpace.carrier, ∃ U : Opens X.toRingedSpace.carrier, y ∈ U ∧
      Stacks.SheafOfModules.IsCoherent
        ((RingedSpace.restrictModules X.toRingedSpace U).obj (K.homology i)) := by
    intro y
    obtain ⟨U, hyU, P, hP, α, hgt, hepi⟩ := hK y
    refine ⟨U, hyU, ?_⟩
    have hNU : IsLocallyNoetherian (Scheme.Opens.toScheme (X := X) U) :=
      isLocallyNoetherian_of_isOpenImmersion (Scheme.Opens.ι (X := X) U)
    have hlim : PreservesFiniteLimits (RingedSpace.restrictModules X.toRingedSpace U) :=
      RingedSpace.restrictModules_preservesFiniteLimits X.toRingedSpace U
    have hcolim : PreservesFiniteColimits (RingedSpace.restrictModules X.toRingedSpace U) :=
      RingedSpace.restrictModules_preservesFiniteColimits X.toRingedSpace U
    have e := Stacks.AlgebraicGeometry.PerfectCohomology.mapHomologyIso
      (RingedSpace.restrictModules X.toRingedSpace U) K i
    have := hqcK
    have hqcRC : SheafOfModules.IsQuasicoherent
        (R := (Scheme.Opens.toScheme (X := X) U).ringCatSheaf)
        ((RingedSpace.restrictComplex K U).homology i) :=
      (SheafOfModules.isQuasicoherent
          (Scheme.Opens.toScheme (X := X) U).ringCatSheaf).prop_of_iso e.symm
        (((SheafOfModules.isQuasicoherent
          (Scheme.Opens.toScheme (X := X) U).ringCatSheaf).prop_of_iso
          ((Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict X U).app
            (K.homology i)).symm
          (Scheme.Modules.isQuasicoherent_restrictFunctor (Scheme.Opens.ι (X := X) U)
            (K.homology i))))
    have := hqcRC
    have hPc : Stacks.SheafOfModules.IsCoherent (P.homology i) :=
      Stacks.AlgebraicGeometry.PerfectCohomology.isCoherent_homology_of_isStrictlyPerfect
        (Scheme.Opens.toScheme (X := X) U) P hP i
    have hepi' : Epi (HomologicalComplex.homologyMap α i) := by
      rcases hi.eq_or_lt with rfl | hlt
      · exact hepi
      · have := hgt i hlt
        infer_instance
    have hGc := @Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_epi
      (Scheme.Opens.toScheme (X := X) U) hNU (P.homology i)
      ((RingedSpace.restrictComplex K U).homology i) hPc.rootIsCoherent hqcRC
      (HomologicalComplex.homologyMap α i) hepi'
    exact Stacks.AlgebraicGeometry.PerfectCohomology.isCoherentStacks_of_iso e
      hGc.stacksIsCoherent
  choose U hyU hcU using hlocal
  have hKc : (K.homology i).IsCoherent := by
    refine Modules.isCoherent_of_restrict (K.homology i) U ?_ fun y => ?_
    · refine eq_top_iff.mpr fun y _ => ?_
      exact Opens.mem_iSup.mpr ⟨y, hyU y⟩
    · exact (Stacks.AlgebraicGeometry.PerfectCohomology.isCoherentStacks_of_iso
        ((Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict X
          (U y)).app (K.homology i)) (hcU y)).rootIsCoherent
  exact (Stacks.AlgebraicGeometry.PerfectCohomology.isCoherentStacks_of_iso eh
    hKc.stacksIsCoherent).rootIsCoherent

/-- **Stacks Project, Tag 08E8.** Let `X` be a Noetherian scheme, let `E` be an object of
`D_QCoh(𝒪_X)` and let `m` be an integer. Then `E` is `m`-pseudo-coherent if and only if `Hⁱ(E)`
is coherent for every `i ≥ m` and vanishes for `i ≫ 0`. -/
@[stacks 08E8 "equivalence in degree m", sga "6 I 3.5" "b), Noetherian scheme"]
public theorem isPseudoCoherentFrom_iff_coherent_homology (X : Scheme.{u}) [IsNoetherian X]
    (E : (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).FullSubcategory)
    (m : ℤ) :
    RingedSpace.IsPseudoCoherentFrom (X := X.toRingedSpace) E.1 m ↔
      ((∀ i : ℤ, m ≤ i →
          ((DerivedCategory.homologyFunctor X.Modules i).obj E.1).IsCoherent) ∧
        DerivedCategoryB.IsBoundedAbove E.1) := by
  refine ⟨fun hE => ⟨fun i hi =>
    isCoherent_homology_of_isPseudoCoherentFrom X E.1 m E.property hE i hi,
      isBoundedAbove_of_isPseudoCoherentFrom X E.1 m hE⟩, ?_⟩
  rintro ⟨hcoh, b, hb⟩
  exact RingedSpace.isPseudoCoherentFrom_of_isLE_homology (X := X.toRingedSpace) E.1 m b
    ((DerivedCategory.isLE_iff E.1 b).mpr fun j hj => hb j hj) fun i hi =>
      isPseudoCoherentFrom_singleFunctor_zero_of_isCoherent X _
        (hcoh i hi).stacksIsCoherent (m - i)

/-- **Stacks Project, Tag 08E8, the final statement.** On a Noetherian scheme an object of
`D_QCoh(𝒪_X)` is pseudo-coherent if and only if it is bounded above and all of its cohomology
sheaves are coherent, that is, if and only if it is an object of `D⁻_Coh(𝒪_X)`. -/
@[stacks 08E8 "identification with D⁻_Coh", sga "6 I 3.5" "b) last claim, Noeth X"]
public theorem isPseudoCoherent_iff_boundedAbove_coherent_homology (X : Scheme.{u})
    [IsNoetherian X]
    (E : (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).FullSubcategory) :
    RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E.1 ↔
      (DerivedCategoryB.IsBoundedAbove E.1 ∧
        ∀ i : ℤ,
          ((DerivedCategory.homologyFunctor X.Modules i).obj E.1).IsCoherent) := by
  refine ⟨fun h => ⟨((isPseudoCoherentFrom_iff_coherent_homology X E 0).1
    (h.isPseudoCoherentFrom 0)).2, fun i => ((isPseudoCoherentFrom_iff_coherent_homology X E i).1
      (h.isPseudoCoherentFrom i)).1 i le_rfl⟩, ?_⟩
  rintro ⟨hb, hcoh⟩
  obtain ⟨K, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (F := DerivedCategory.Q (C := OXMod.{u, u} X.toRingedSpace)) E.1
  exact ⟨K, fun m => RingedSpace.isPseudoCoherentComplexFrom_of_iso E.1 m
    ((isPseudoCoherentFrom_iff_coherent_homology X E m).2 ⟨fun i _ => hcoh i, hb⟩) K e, ⟨e⟩⟩

end AlgebraicGeometry

end
