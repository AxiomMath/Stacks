module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.MayerVietorisTorDimension
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# The Tor-dimension half of perfectness of a direct image, over an arbitrary base

Let `f : X ⟶ S` be a perfect, quasi-compact and quasi-separated morphism of schemes and let `E`
be a perfect object of `D(𝒪_X)`. Then `Rf_*E` has locally finite Tor dimension on `S`.

No Noetherian hypothesis is made, and none is needed: the Mayer--Vietoris induction of
`AlgebraicGeometry.hasFiniteTorDimension_schemeDerivedPushforward_of_isAffine_target` runs over
any affine open `V ⊆ S`, whose preimage is quasi-compact and quasi-separated because `f` is; and a
perfect object has quasi-coherent cohomology (Tag 08E5, via pseudo-coherence) and finite Tor
dimension on a quasi-compact scheme.

By Tag 08CQ, perfectness of `Rf_*E` is therefore equivalent to its pseudo-coherence, which is
what `isPerfect_derivedPushforward_of_isPseudoCoherent` records.

## Main results

* `locallyHasFiniteTorDimension_derivedPushforward_of_isPerfect`: `Rf_*E` has locally finite Tor
  dimension.
* `isPerfect_derivedPushforward_of_isPseudoCoherent`: `Rf_*E` is perfect as soon as it is
  pseudo-coherent.

## References

* [Stacks Project, Tag 0B6G](https://stacks.math.columbia.edu/tag/0B6G)
* [Stacks Project, Tag 08CQ](https://stacks.math.columbia.edu/tag/08CQ)
* [Stacks Project, Tag 08EV](https://stacks.math.columbia.edu/tag/08EV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.PerfectProperDirectImage

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.Perfect f] [QuasiCompact f]
  [QuasiSeparated f]

/-- **The direct image of a perfect object along a perfect quasi-compact quasi-separated morphism
has locally finite Tor dimension**, over an arbitrary base. -/
@[sga "6 0 3.1" "partial"]
theorem locallyHasFiniteTorDimension_derivedPushforward_of_isPerfect
    (E : DerivedCategory X.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E) :
    Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension S.toRingedSpace
      ((derivedPushforwardModules f).obj E) := by
  refine locallyHasFiniteTorDimension_derivedPushforward_of_forall_affineOpen f E fun V => ?_
  have : IsAffine (V : S.Opens).toScheme := V.2
  have : AlgebraicGeometry.Perfect (f ∣_ (V : S.Opens)) :=
    IsZariskiLocalAtTarget.restrict (P := @AlgebraicGeometry.Perfect) inferInstance _
  have : CompactSpace (f ⁻¹ᵁ (V : S.Opens)).toScheme :=
    QuasiCompact.compactSpace_of_compactSpace (f ∣_ (V : S.Opens))
  have : QuasiSeparatedSpace (f ⁻¹ᵁ (V : S.Opens)).toScheme :=
    quasiSeparatedSpace_of_quasiSeparated (f ∣_ (V : S.Opens))
  have hqcE : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent :=
    PerfectApproximation.isQuasicoherent_homology_of_isPerfect X E hE
  have hTor : Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension
      (f ⁻¹ᵁ (V : S.Opens)).toScheme.toRingedSpace
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ (V : S.Opens)).ι).mapDerivedCategory.obj E) :=
    (AffineRelativeTorAmplitude.locallyHasFiniteTorDimension_iff_hasFiniteTorDimension
      (X := (f ⁻¹ᵁ (V : S.Opens)).toScheme.toRingedSpace) _).1
      (Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_of_isPerfect
        (X := (f ⁻¹ᵁ (V : S.Opens)).toScheme.toRingedSpace) _
        (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
          (X := (f ⁻¹ᵁ (V : S.Opens)).toScheme.toRingedSpace)
          ((Scheme.Modules.derivedRestrictIsoDerivedPullback (f ⁻¹ᵁ (V : S.Opens)).ι).app E).symm
          (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
            (f ⁻¹ᵁ (V : S.Opens)).ι.toLRSHom.toShHom E hE)))
  exact hasFiniteTorDimension_schemeDerivedPushforward_of_isAffine_target
    (f ∣_ (V : S.Opens)) _
    (isQuasicoherent_homology_restrictFunctor_mapDerivedCategory (f ⁻¹ᵁ (V : S.Opens)).ι hqcE)
    hTor

/-- **The direct image of a perfect object along a perfect quasi-compact quasi-separated morphism
is perfect as soon as it is pseudo-coherent**. -/
theorem isPerfect_derivedPushforward_of_isPseudoCoherent (E : DerivedCategory X.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (hpc : AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := S.toRingedSpace)
      ((derivedPushforwardModules f).obj E)) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.toRingedSpace)
      ((derivedPushforwardModules f).obj E) :=
  Stacks.Cohomology.TorAmplitude.isPerfect_of_isPseudoCoherent_of_locallyHasFiniteTorDimension
    (X := S.toRingedSpace) ((derivedPushforwardModules f).obj E)
    ((Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent'
        (X := S.toRingedSpace) ((derivedPushforwardModules f).obj E)).2 hpc)
    (locallyHasFiniteTorDimension_derivedPushforward_of_isPerfect f E hE)

end Stacks.AlgebraicGeometry.PerfectProperDirectImage

end
