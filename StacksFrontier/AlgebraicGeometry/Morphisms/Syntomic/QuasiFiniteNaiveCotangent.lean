module

public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermPerfect
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.NaiveCotangent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreEulerCharacteristicAffine
public import StacksFrontier.RingTheory.Syntomic.ConormalRank
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The naive cotangent complex of a locally quasi-finite syntomic morphism

The naive cotangent complex `NL_{Y/X}` of a locally quasi-finite syntomic morphism of schemes
`f : Y ⟶ X` has rank zero, in the sense of
`AlgebraicGeometry.DeterminantTwoTerm.IsRankZeroScheme`. Conversely, a flat morphism locally of
finite presentation whose naive cotangent complex is perfect of rank zero with Tor amplitude in
`[-1, 0]` is locally quasi-finite and syntomic. With the conditions on presentations and fibres
this gives all seven equivalent characterisations of Stacks 0BWE.

## Main results

* `AlgebraicGeometry.isRankZeroScheme_naiveCotangentComplex_of_locallyQuasiFinite_syntomic`: the
  naive cotangent complex of a locally quasi-finite syntomic morphism has rank zero.
* `AlgebraicGeometry.locallyQuasiFinite_of_syntomic_of_isRankZeroScheme`: a syntomic morphism
  whose naive cotangent complex has rank zero is locally quasi-finite.
* `AlgebraicGeometry.locallyQuasiFinite_syntomic_tfae_naiveCotangentComplex`: the equivalence of
  the seven conditions of Stacks 0BWE.

## References

* [Stacks Project, Tag 0BWE](https://stacks.math.columbia.edu/tag/0BWE)
* [Stacks Project, Tag 0FKY](https://stacks.math.columbia.edu/tag/0FKY)
* [Stacks Project, Lemma 37.62.17 (0FK3)](https://stacks.math.columbia.edu/tag/0FK3)
* [Stacks Project, Lemma 36.3.5 (0D0I)](https://stacks.math.columbia.edu/tag/0D0I)
* [Stacks Project, Tag 00SY](https://stacks.math.columbia.edu/tag/00SY)
* [Stacks Project, Tag 00SV](https://stacks.math.columbia.edu/tag/00SV)
* [Stacks Project, Tag 0BDJ](https://stacks.math.columbia.edu/tag/0BDJ)
* [Stacks Project, Section 15.87 (Tag 0FJI)](https://stacks.math.columbia.edu/tag/0FJI)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-- Every point of the source lies in an affine open mapping into an affine open of the target. -/
private theorem exists_isAffineOpen_le_preimage {Y X : Scheme.{u}} (f : Y ⟶ X) (y : Y) :
    ∃ (U : X.Opens) (V : Y.Opens), IsAffineOpen U ∧ IsAffineOpen V ∧ y ∈ V ∧ V ≤ f ⁻¹ᵁ U := by
  obtain ⟨U, hU, hyU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := f.base y) (U := ⊤) (by simp)
  obtain ⟨V, hV, hyV, hVU⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := f ⁻¹ᵁ U) hyU
  exact ⟨U, V, hU, hV, hyV, hVU⟩

/-- A syntomic morphism has a perfect naive cotangent complex with Tor amplitude in `[-1, 0]`. -/
private theorem isPerfect_and_hasTorAmplitude_naiveCotangentComplex_of_syntomic
    {Y X : Scheme.{u}} {f : Y ⟶ X} (hf : Syntomic f) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace)
        (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) ∧
      Stacks.Cohomology.TorAmplitude.HasTorAmplitude Y.toRingedSpace
        (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0 :=
  isPerfect_and_hasTorAmplitude_naiveCotangentComplex f
    (isLocalCompleteIntersectionMorphism_of_syntomic hf)

/-- **The naive cotangent complex of a locally quasi-finite syntomic morphism has rank zero.** -/
theorem isRankZeroScheme_naiveCotangentComplex_of_locallyQuasiFinite_syntomic
    {Y X : Scheme.{u}} {f : Y ⟶ X} [LocallyQuasiFinite f] (hf : Syntomic f) :
    DeterminantTwoTerm.IsRankZeroScheme
      (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) := by
  intro y
  obtain ⟨U, V, hU, hV, hyV, hVU⟩ := exists_isAffineOpen_le_preimage f y
  let := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
  have : Algebra.Syntomic Γ(X, U) Γ(Y, V) :=
    (HasRingHomProperty.iff_appLE (P := @Syntomic) (Q := RingHom.Syntomic)).mp hf ⟨U, hU⟩
      ⟨V, hV⟩ hVU
  have : Algebra.QuasiFinite Γ(X, U) Γ(Y, V) :=
    HasRingHomProperty.appLE (@LocallyQuasiFinite) f ‹_› ⟨U, hU⟩ ⟨V, hV⟩ hVU
  obtain ⟨P, hP⟩ := Algebra.isRankZero_naiveCotangentObject_of_quasiFinite_syntomic
    (A := Γ(X, U)) (B := Γ(Y, V))
  let e := NaiveCotangentLocalCompleteIntersection.sectionsNaiveCotangentComplexIso f hVU
  refine ⟨V, hV, hyV, _, ⟨{ P with iso := e ≪≫ P.iso }, hP⟩,
    ⟨NaiveCotangentLocalCompleteIntersection.naiveCotangentComplexRestrictIso f hVU hU hV⟩⟩

/-! ### Rank zero forces quasi-finiteness -/

/-- The naive cotangent complex of a syntomic morphism is pseudo-coherent. -/
theorem isPseudoCoherent_naiveCotangentComplex_of_syntomic {Y X : Scheme.{u}} {f : Y ⟶ X}
    (hf : Syntomic f) :
    RingedSpace.IsPseudoCoherent (X := Y.toRingedSpace)
      (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) :=
  (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent'
    (X := Y.toRingedSpace) _).1
    (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect (X := Y.toRingedSpace) _
      (isPerfect_and_hasTorAmplitude_naiveCotangentComplex_of_syntomic hf).1)

/-- **A syntomic morphism whose naive cotangent complex has rank zero is locally quasi-finite.** -/
theorem locallyQuasiFinite_of_syntomic_of_isRankZeroScheme {Y X : Scheme.{u}} {f : Y ⟶ X}
    (hf : Syntomic f)
    (h0 : DeterminantTwoTerm.IsRankZeroScheme
      (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f))) :
    LocallyQuasiFinite f := by
  have hpc := isPseudoCoherent_naiveCotangentComplex_of_syntomic hf
  refine (HasRingHomProperty.iff_exists_appLE (P := @LocallyQuasiFinite)
    (Q := RingHom.QuasiFinite)
    (RingHom.QuasiFinite.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.QuasiFinite.holdsForLocalizationAway).left).2 fun y => ?_
  obtain ⟨V₀, hyV₀, U, hVU, hsyn⟩ := hf y
  let _ : Algebra Γ(X, U.1) Γ(Y, V₀.1) := (f.appLE U.1 V₀.1 hVU).hom.toAlgebra
  have : Algebra.Syntomic Γ(X, U.1) Γ(Y, V₀.1) := hsyn
  obtain ⟨r, hr, hrgci⟩ := Algebra.Syntomic.exists_notMem_isRelativeGlobalCompleteIntersection
    (R := Γ(X, U.1)) (V₀.2.primeIdealOf ⟨y, hyV₀⟩).asIdeal
  have hyr : y ∈ Y.basicOpen r := by
    have h1 : V₀.2.primeIdealOf ⟨y, hyV₀⟩ ∈ V₀.2.fromSpec ⁻¹ᵁ Y.basicOpen r := by
      rw [V₀.2.fromSpec_preimage_basicOpen r]
      exact (PrimeSpectrum.mem_basicOpen r _).mpr hr
    have h2 : V₀.2.fromSpec (V₀.2.primeIdealOf ⟨y, hyV₀⟩) ∈ Y.basicOpen r := h1
    rwa [V₀.2.fromSpec_primeIdealOf ⟨y, hyV₀⟩] at h2
  have hle : Y.basicOpen r ≤ f ⁻¹ᵁ U.1 := (Y.basicOpen_le r).trans hVU
  have hW : IsAffineOpen (Y.basicOpen r) := V₀.2.basicOpen r
  let _ : Algebra Γ(X, U.1) Γ(Y, Y.basicOpen r) :=
    (f.appLE U.1 (Y.basicOpen r) hle).hom.toAlgebra
  have := V₀.2.isLocalization_basicOpen r
  have : IsScalarTower Γ(X, U.1) Γ(Y, V₀.1) Γ(Y, Y.basicOpen r) :=
    .of_algebraMap_eq fun x => by
      simp only [RingHom.algebraMap_toAlgebra, ← ConcreteCategory.comp_apply,
        Scheme.Hom.appLE_map]
  have hrgci' : Algebra.IsRelativeGlobalCompleteIntersection Γ(X, U.1) Γ(Y, Y.basicOpen r) :=
    .of_algEquiv ((IsLocalization.algEquiv (Submonoid.powers r) (Localization.Away r)
      Γ(Y, Y.basicOpen r)).restrictScalars Γ(X, U.1))
  obtain ⟨n, c, Q, hQ⟩ := hrgci'.out
  obtain ⟨b, -⟩ := Q.exists_basis_cotangent_relation
  have : Module.Finite Γ(Y, Y.basicOpen r) Q.toExtension.Cotangent := Module.Finite.of_basis b
  have : Module.Projective Γ(Y, Y.basicOpen r) Q.toExtension.Cotangent :=
    Module.Projective.of_basis b
  obtain ⟨T, hT⟩ := Q.toGenerators.exists_twoTermPresentation_naiveCotangentObject
  have hW' := DerivedFibreBetti.chiDerivedFibre_eq_of_derivedRestrict_iso (X := Y)
    (Scheme.naiveCotangentComplex f) hpc hW T.complex (-1) 0 T.strictlyGE T.strictlyLE
    T.finite T.projective
    (NaiveCotangentLocalCompleteIntersection.naiveCotangentComplexRestrictIso f hle U.2 hW ≪≫
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (Stacks.Cohomology.TransportAlongIso.ringedSpaceIsoOfSchemeIso hW.isoSpec).hom).mapIso
        ((tilde.functor Γ(Y, Y.basicOpen r)).mapDerivedCategory.mapIso
          (NaiveCotangentLocalCompleteIntersection.sectionsNaiveCotangentComplexIso f hle ≪≫
            T.iso)))
    y hyr
  have h₁ := DerivedFibreBetti.chiDerivedFibre_eq_zero_of_isRankZeroScheme (X := Y)
    (Scheme.naiveCotangentComplex f) hpc h0 y
  rw [DerivedFibreBetti.finsum_negOnePow_rankAtStalk_of_twoTerm _ T.strictlyGE T.strictlyLE]
    at hW'
  obtain ⟨hc, hn⟩ := hT (hW.primeIdealOf ⟨y, hyr⟩)
  have : Nontrivial Γ(Y, Y.basicOpen r) := (hW.primeIdealOf ⟨y, hyr⟩).nontrivial
  have hc' : Module.rankAtStalk Q.toExtension.Cotangent (hW.primeIdealOf ⟨y, hyr⟩) = c := by
    simp [Module.finrank_eq_card_basis b]
  have hnc : c = n := by rw [h₁, hn, hc, hc'] at hW'; lia
  subst hnc
  exact ⟨U, ⟨Y.basicOpen r, hW⟩, hyr, hle, Algebra.QuasiFinite.of_square_presentation hQ rfl⟩

/-! ### Parts (6) and (7) of Stacks 0BWE -/

/-- **A flat morphism locally of finite presentation whose naive cotangent complex has Tor
amplitude in `[-1, 0]` is syntomic.** -/
theorem syntomic_of_flat_of_hasTorAmplitude_naiveCotangentComplex {Y X : Scheme.{u}}
    {f : Y ⟶ X} [Flat f] [LocallyOfFinitePresentation f]
    (hamp : Stacks.Cohomology.TorAmplitude.HasTorAmplitude Y.toRingedSpace
      (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0) :
    Syntomic f := by
  intro y
  obtain ⟨U, V, hU, hV, hyV, hVU⟩ := exists_isAffineOpen_le_preimage f y
  exact ⟨⟨V, hV⟩, hyV, ⟨U, hU⟩, hVU,
    NaiveCotangentLocalCompleteIntersection.syntomic_appLE_of_hasTorAmplitude f hVU hU hV hamp⟩

/-- A locally quasi-finite syntomic morphism of schemes is locally quasi-finite, flat and locally
of finite presentation, and its naive cotangent complex `NL_{Y/X}` has Tor amplitude in
`[-1, 0]`. -/
@[stacks 0BWE "the implication (1) ⟹ (6)"]
theorem locallyQuasiFinite_flat_lfp_and_hasTorAmplitude_of_locallyQuasiFinite_syntomic
    {Y X : Scheme.{u}} {f : Y ⟶ X} (h : LocallyQuasiFinite f ∧ Syntomic f) :
    ((LocallyQuasiFinite f ∧ Flat f) ∧ LocallyOfFinitePresentation f) ∧
      Stacks.Cohomology.TorAmplitude.HasTorAmplitude Y.toRingedSpace
        (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0 :=
  ⟨⟨⟨h.1, flat h.2⟩, locallyOfFinitePresentation h.2⟩,
    (isPerfect_and_hasTorAmplitude_naiveCotangentComplex_of_syntomic h.2).2⟩

/-- A locally quasi-finite flat morphism of schemes which is locally of finite presentation and
whose naive cotangent complex has Tor amplitude in `[-1, 0]` is syntomic. -/
@[stacks 0BWE "the implication (6) ⟹ (1)"]
theorem locallyQuasiFinite_syntomic_of_flat_lfp_of_hasTorAmplitude {Y X : Scheme.{u}}
    {f : Y ⟶ X}
    (h : ((LocallyQuasiFinite f ∧ Flat f) ∧ LocallyOfFinitePresentation f) ∧
      Stacks.Cohomology.TorAmplitude.HasTorAmplitude Y.toRingedSpace
        (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0) :
    LocallyQuasiFinite f ∧ Syntomic f :=
  have : Flat f := h.1.1.2
  have : LocallyOfFinitePresentation f := h.1.2
  ⟨h.1.1.1, syntomic_of_flat_of_hasTorAmplitude_naiveCotangentComplex h.2⟩

/-- A locally quasi-finite syntomic morphism of schemes is flat and locally of finite
presentation, and its naive cotangent complex `NL_{Y/X}` is a perfect object of `D(𝒪_Y)` of rank
zero with Tor amplitude in `[-1, 0]`. -/
@[stacks 0BWE "the implication (1) ⟹ (7)", sga "6 0 4.3" "special case", sga "6 VIII 2.4" "partial"]
theorem flat_lfp_and_isPerfect_and_hasTorAmplitude_of_locallyQuasiFinite_syntomic
    {Y X : Scheme.{u}} {f : Y ⟶ X} (h : LocallyQuasiFinite f ∧ Syntomic f) :
    (Flat f ∧ LocallyOfFinitePresentation f) ∧
      (Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace)
          (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) ∧
        DeterminantTwoTerm.IsRankZeroScheme
          (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) ∧
        Stacks.Cohomology.TorAmplitude.HasTorAmplitude Y.toRingedSpace
          (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0) := by
  have := h.1
  obtain ⟨hperf, hamp⟩ := isPerfect_and_hasTorAmplitude_naiveCotangentComplex_of_syntomic h.2
  exact ⟨⟨flat h.2, locallyOfFinitePresentation h.2⟩, hperf,
    isRankZeroScheme_naiveCotangentComplex_of_locallyQuasiFinite_syntomic h.2, hamp⟩

/-- A flat morphism of schemes which is locally of finite presentation and whose naive cotangent
complex `NL_{Y/X}` is a perfect object of `D(𝒪_Y)` of rank zero with Tor amplitude in `[-1, 0]`
is locally quasi-finite and syntomic. -/
@[stacks 0BWE "the implication (7) ⟹ (1)"]
theorem locallyQuasiFinite_syntomic_of_flat_lfp_of_isPerfect_of_isRankZeroScheme
    {Y X : Scheme.{u}} {f : Y ⟶ X}
    (h : (Flat f ∧ LocallyOfFinitePresentation f) ∧
      (Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace)
          (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) ∧
        DeterminantTwoTerm.IsRankZeroScheme
          (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) ∧
        Stacks.Cohomology.TorAmplitude.HasTorAmplitude Y.toRingedSpace
          (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0)) :
    LocallyQuasiFinite f ∧ Syntomic f :=
  have : Flat f := h.1.1
  have : LocallyOfFinitePresentation f := h.1.2
  have hf : Syntomic f := syntomic_of_flat_of_hasTorAmplitude_naiveCotangentComplex h.2.2.2
  ⟨locallyQuasiFinite_of_syntomic_of_isRankZeroScheme hf h.2.2.1, hf⟩

/-- For a morphism of schemes `f : Y ⟶ X` the following are equivalent:

1. `f` is locally quasi-finite and syntomic;
2. `f` is locally quasi-finite, flat, and a local complete intersection morphism;
3. `f` is locally quasi-finite, flat, locally of finite presentation, and all the fibres of `f`
   are local complete intersections over the residue fields of their base points;
4. `f` is locally quasi-finite and, around every point of its source, there are affine opens
   `y ∈ V = Spec(B) ⊆ Y` and `U = Spec(A) ⊆ X` with `f(V) ⊆ U`, an integer `n` and
   `h, f_1, …, f_n ∈ A[x_1, …, x_n]` with `B = A[x_1, …, x_n, 1/h]/(f_1, …, f_n)`;
5. around every point of the source there are such affine opens with `A → B` a relative global
   complete intersection of the form `B = A[x_1, …, x_n]/(f_1, …, f_n)`;
6. `f` is locally quasi-finite, flat, locally of finite presentation, and `NL_{Y/X}` has Tor
   amplitude in `[-1, 0]`;
7. `f` is flat and locally of finite presentation, and `NL_{Y/X}` is a perfect object of
   `D(𝒪_Y)` of rank zero with Tor amplitude in `[-1, 0]`. -/
@[stacks 0BWE]
theorem locallyQuasiFinite_syntomic_tfae_naiveCotangentComplex {Y X : Scheme.{u}}
    (f : Y ⟶ X) :
    List.TFAE [
      LocallyQuasiFinite f ∧ Syntomic f,
      (LocallyQuasiFinite f ∧ Flat f) ∧ IsLocalCompleteIntersectionMorphism f,
      ((LocallyQuasiFinite f ∧ Flat f) ∧ LocallyOfFinitePresentation f) ∧
        ∀ x : X, IsLocalCompleteIntersectionOverField (f.fiberToSpecResidueField x),
      LocallyQuasiFinite f ∧ HasLocalSquarePresentation f,
      HasLocalSquareRelativeGlobalCompleteIntersection f,
      ((LocallyQuasiFinite f ∧ Flat f) ∧ LocallyOfFinitePresentation f) ∧
        Stacks.Cohomology.TorAmplitude.HasTorAmplitude Y.toRingedSpace
          (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0,
      (Flat f ∧ LocallyOfFinitePresentation f) ∧
        (Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace)
            (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) ∧
          DeterminantTwoTerm.IsRankZeroScheme
            (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) ∧
          Stacks.Cohomology.TorAmplitude.HasTorAmplitude Y.toRingedSpace
            (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0)] := by
  have h15 := locallyQuasiFinite_syntomic_tfae f
  tfae_have 1 ↔ 2 := h15.out 1 2
  tfae_have 1 ↔ 3 := h15.out 1 3
  tfae_have 1 ↔ 4 := h15.out 1 4
  tfae_have 1 ↔ 5 := h15.out 1 5
  tfae_have 1 → 6 := locallyQuasiFinite_flat_lfp_and_hasTorAmplitude_of_locallyQuasiFinite_syntomic
  tfae_have 6 → 1 := locallyQuasiFinite_syntomic_of_flat_lfp_of_hasTorAmplitude
  tfae_have 1 → 7 := flat_lfp_and_isPerfect_and_hasTorAmplitude_of_locallyQuasiFinite_syntomic
  tfae_have 7 → 1 := locallyQuasiFinite_syntomic_of_flat_lfp_of_isPerfect_of_isRankZeroScheme
  tfae_finish

end AlgebraicGeometry

end
