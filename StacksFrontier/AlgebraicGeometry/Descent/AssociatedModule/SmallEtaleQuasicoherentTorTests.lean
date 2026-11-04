module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleTorAmplitudeComparison
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.ZariskiRingedSiteOfARingedSpace
public import StacksFrontier.AlgebraicGeometry.Perfect.TorAmplitudeQuasiCoherentTestsGlobal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.DerivedPullbackReflection
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.DerivedPullbackReflectionSingleTest
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.FiniteTorDimensionOfAPerfectObject

/-!
# Quasi-coherent Tor tests on the small étale site of a quasi-separated scheme

Let `S` be a quasi-separated scheme and `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` the comparison morphism
of Stacks 08H7, read on the `Type u`-presented model of the small étale ringed topos
(`AlgebraicGeometry.SmallEtale.toZariskiSmallModelHom`).  For `E` an object of `D_QCoh(𝒪_S)`,
the object `Lε^*E` has Tor amplitude in `[a, b]` as soon as
`Hⁱ(Lε^*E ⊗^L (ε^*𝓕)[0]) = 0` for `i ∉ [a, b]` and every *quasi-coherent* `𝒪_S`-module `𝓕`.

This is the representable case of Stacks 08IL, in the form its proof uses — the second paragraph
of the source's proof, after `E` has been written as `ε^*E₀` by Stacks 071Q: the test modules
`ε^*𝓕₀` are quasi-coherent, the vanishing for `ε^*𝓕₀` gives the vanishing for `𝓕₀` because `ε`
is flat and `ε^*` detects the zero sheaf (Stacks 08H8), the scheme case Stacks 08EA then gives Tor
amplitude of `E₀`, and Stacks 08HF carries it back to `ε^*E₀`.

## Main results

* `Stacks.Cohomology.TorAmplitude.isZero_homology_derivedTensorProduct_iff`: one Tor test on a
  ringed space reads the same against an arbitrary derived tensor product datum on its site of
  opens as against `Stacks.Cohomology.TorAmplitude.derTensor`.
* `Stacks.Cohomology.TorAmplitude.hasTorAmplitudeOnQuasicoherent_iff_derivedTensorProduct`: so
  condition (2) of Stacks 08EA may be read against an arbitrary datum.
* `AlgebraicGeometry.SmallEtale.hasTorAmplitude_derivedPullback_of_quasicoherent_tests`: **the
  representable case of Stacks 08IL**, on the model.

## Implementation notes

The derived tensor product data on the small Zariski site and on the model are arbitrary, as in
Stacks 08HF; the one on the Zariski site is internal to the proof and is the canonical one of
Stacks 06YU (`Stacks.SheafOfModules.canonicalDerivedTensorProduct`).

The derived categories carry `CategoryTheory.HasDerivedCategory.standard`, the instance at which
Stacks 08HF and Stacks 08EA are stated.

## References

* [Stacks Project, Lemma 75.13.8 (Tag 08IL)](https://stacks.math.columbia.edu/tag/08IL)
* [Stacks Project, Lemma 36.10.6 (Tag 08EA)](https://stacks.math.columbia.edu/tag/08EA)
* [Stacks Project, Tag 08HF](https://stacks.math.columbia.edu/tag/08HF)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect

universe u d

namespace Stacks.Cohomology.TorAmplitude

section Bridge

variable (X : RingedSpace.{u, u}) [HasDerivedCategory.{d} (OXMod.{u, u} X)]

attribute [local instance] hasDerivedCategoryModules
attribute [local instance]
  Stacks.Cohomology.PerfectComplexes.hasDerivedCategoryRingedSiteModules

/-- **One Tor test on a ringed space is independent of the derived tensor product datum.**  The
`i`-th cohomology sheaf of `E ⊗^L F[0]` vanishes for a derived tensor product datum `T` of
Stacks 06YU on the site of opens of `X` exactly when it vanishes for
`Stacks.Cohomology.TorAmplitude.derTensor`: a K-flat representative of `E` computes both, by the
left K-flat comparison fields of the two data. -/
theorem isZero_homology_derivedTensorProduct_iff
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{u, u, u, d}
      (AlgebraicGeometry.RingedSpace.ringedSite X))
    (E : DerivedCategory (OXMod.{u, u} X)) (F : OXMod.{u, u} X) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj
        ((T.tensor.obj E).obj ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F))) ↔
      IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj
        (((derTensor X).tensor.obj E).obj
          ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F))) := by
  obtain ⟨K, hK, ⟨eK⟩⟩ :=
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.exists_kFlat_representative (X := X) E
  have e1 : (T.tensor.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj
        ((HomologicalComplex.single (OXMod.{u, u} X) (ComplexShape.up ℤ) 0).obj F)) ≅
      ((derTensor X).tensor.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj
        ((HomologicalComplex.single (OXMod.{u, u} X) (ComplexShape.up ℤ) 0).obj F)) :=
    T.comparisonLeft K _ hK ≪≫ ((derTensor X).comparisonLeft K _ hK).symm
  have key : (T.tensor.obj E).obj ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F) ≅
      ((derTensor X).tensor.obj E).obj
        ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F) :=
    ((T.tensor.mapIso eK.symm).app _) ≪≫ e1 ≪≫ ((derTensor X).tensor.mapIso eK).app _
  exact Iso.isZero_iff ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).mapIso key)

/-- **Condition (2) of Stacks 08EA is independent of the derived tensor product datum**: it holds
for `Stacks.Cohomology.TorAmplitude.derTensor` exactly when it holds for an arbitrary datum `T`
of Stacks 06YU on the site of opens, test module by test module
(`Stacks.Cohomology.TorAmplitude.isZero_homology_derivedTensorProduct_iff`). -/
theorem hasTorAmplitudeOnQuasicoherent_iff_derivedTensorProduct
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{u, u, u, d}
      (AlgebraicGeometry.RingedSpace.ringedSite X))
    (E : DerivedCategory (OXMod.{u, u} X)) (a b : ℤ) :
    (∀ F : OXMod.{u, u} X, F.IsQuasicoherent → ∀ i : ℤ, i ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj
        ((T.tensor.obj E).obj ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F)))) ↔
      HasTorAmplitudeOnQuasicoherent X E a b :=
  ⟨fun h F hF i hi => (isZero_homology_derivedTensorProduct_iff X T E F i).1 (h F hF i hi),
    fun h F hF i hi => (isZero_homology_derivedTensorProduct_iff X T E F i).2 (h F hF i hi)⟩

end Bridge

end Stacks.Cohomology.TorAmplitude

namespace AlgebraicGeometry.SmallEtale

open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.SheafOfModules Stacks.SheafOfModules.DerivedTensorProduct

attribute [local instance 20000] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The representable case of Stacks 08IL**, on the `Type u`-presented model of the small étale
ringed topos.  Let `S` be a quasi-separated scheme and `E` an object of `D_QCoh(𝒪_S)`.  If
`Hⁱ(Lε^*E ⊗^L (ε^*𝓕)[0]) = 0` for every quasi-coherent `𝒪_S`-module `𝓕` and every `i ∉ [a, b]`,
then `Lε^*E` has Tor amplitude in `[a, b]`, for an arbitrary derived tensor product datum `T'`
on the model.

The vanishing for `ε^*𝓕` gives the vanishing of `Hⁱ(E ⊗^L 𝓕[0])` because `ε` is flat and `ε^*`
detects the zero sheaf (Stacks 08H8,
`Stacks.SheafOfModules.DerivedTensorProduct.isZero_homology_tensor_single_of_derivedPullback`);
the scheme case Stacks 08EA then gives Tor amplitude of `E` in `[a, b]`, and Stacks 08HF carries
it to `Lε^*E`. -/
theorem hasTorAmplitude_derivedPullback_of_quasicoherent_tests [QuasiSeparatedSpace S]
    (T' : DerivedTensorProduct (smallModelRingedTopos B S hS).toRingedSite)
    (E : RingedSite.DerivedModules S.zariskiRingedTopos.toRingedSite) (a b : ℤ)
    (hqc : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (RingedSite.Modules S.zariskiRingedTopos.toRingedSite) n).obj E).IsQuasicoherent)
    (h : ∀ F : RingedSite.Modules S.zariskiRingedTopos.toRingedSite, F.IsQuasicoherent →
      ∀ i : ℤ, i ∉ Set.Icc a b →
        IsZero ((DerivedCategory.homologyFunctor
            (RingedSite.Modules (smallModelRingedTopos B S hS).toRingedSite) i).obj
          ((T'.tensor.obj ((derivedPullback (toZariskiSmallModelHom B S hS)).obj E)).obj
            ((DerivedCategory.singleFunctor
                (RingedSite.Modules (smallModelRingedTopos B S hS).toRingedSite) 0).obj
              ((toZariskiSmallModelHom B S hS).pullbackTopos.obj F))))) :
    HasTorAmplitude T' ((derivedPullback (toZariskiSmallModelHom B S hS)).obj E) a b := by
  let T : DerivedTensorProduct S.zariskiRingedTopos.toRingedSite :=
    canonicalDerivedTensorProduct S.zariskiRingedTopos.toRingedSite
  have h₀ : ∀ F : RingedSite.Modules S.zariskiRingedTopos.toRingedSite, F.IsQuasicoherent →
      ∀ i : ℤ, i ∉ Set.Icc a b →
        IsZero ((DerivedCategory.homologyFunctor
            (RingedSite.Modules S.zariskiRingedTopos.toRingedSite) i).obj
          ((T.tensor.obj E).obj
            ((DerivedCategory.singleFunctor
              (RingedSite.Modules S.zariskiRingedTopos.toRingedSite) 0).obj F))) :=
    fun F hF i hi => isZero_homology_tensor_single_of_derivedPullback
      (toZariskiSmallModelHom B S hS) (isMorphismOfSites_toZariskiSmallModelHom_u B S hS)
      (isZero_of_isZero_pullbackTopos_toZariskiSmallModelHom B S hS) T T' E F i (h F hF i hi)
  have h₁ : Stacks.Cohomology.TorAmplitude.HasTorAmplitudeOnQuasicoherent S.toRingedSpace E a b :=
    (Stacks.Cohomology.TorAmplitude.hasTorAmplitudeOnQuasicoherent_iff_derivedTensorProduct
      S.toRingedSpace T E a b).1 h₀
  have h₂ : Stacks.Cohomology.TorAmplitude.HasTorAmplitude S.toRingedSpace E a b :=
    hasTorAmplitude_of_hasTorAmplitudeOnQuasicoherent E a b hqc h₁
  exact (hasTorAmplitude_derivedPullback_of_hasTorAmplitude B S hS T T' E a b).2
    ((Stacks.Cohomology.TorAmplitude.hasTorAmplitude_iff_derivedTensorProduct
      S.toRingedSpace T E a b).2 h₂)

end AlgebraicGeometry.SmallEtale

end
