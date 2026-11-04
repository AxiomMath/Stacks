module

public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.DerivedCharacterization
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlatAndDerivedPullback.ResolvingDatum
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional
import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.DerivedPullback

/-!
# Pseudo-coherence under derived pullback: reduction to the complex level

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `E` be an object of
`D(𝒪_Y)` which is `m`-pseudo-coherent. Tag 09U7 asserts that `Lf^*E` is `m`-pseudo-coherent.

This file carries out the derived-category half of that statement and nothing else: it replaces
`E` by a K-flat complex `P` representing it, which makes `Lf^*E` the class of the *degreewise*
pullback `f^*P`, and so reduces Tag 09U7 to the assertion that degreewise pullback preserves
`m`-pseudo-coherence of a K-flat complex. The surviving assertion mentions no derived functor.

## Main results

* `isPseudoCoherentFrom_derivedPullback_of_complexLevel`: Tag 09U7, granted that
  degreewise pullback preserves `m`-pseudo-coherence of complexes which are K-flat.

## Implementation notes

The derived pullback is `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback`, which
exists as soon as degreewise pullback has a resolving datum; the K-flat complexes are one, and
the instance
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.hasLeftDerivedFunctor_pullbackOnHomotopy`
provides it with no hypothesis. On a K-flat complex `P`, `Lf^*` of the class of `P` is the class
of `f^*P` by `Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat`.

The K-flat representative comes from Tag 06YS and the transfer of `m`-pseudo-coherence from the
original representative to it is Tag 08CC part (2), which says that the condition depends only
on the object of the derived category.

## References

* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Tag 08CC](https://stacks.math.columbia.edu/tag/08CC)
* [Stacks Project, Tag 09U7](https://stacks.math.columbia.edu/tag/09U7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect RingedSpaceModuleAdjunction

namespace AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

universe u

attribute [local instance] HasDerivedCategory.standard

/-- **Tag 09U7, reduced to the complex level.**  If degreewise pullback along `f` preserves
`m`-pseudo-coherence of K-flat complexes, then the derived pullback of an `m`-pseudo-coherent
object of `D(𝒪_Y)` is `m`-pseudo-coherent.

Represent the given object by a K-flat complex `P`, using the K-flat resolutions of Tag 06YS
and the independence of `m`-pseudo-coherence from the representative (Tag 08CC part (2)). Since
`P` is K-flat, the comparison of `Lf^*` with degreewise pullback is invertible at `P`, so
`Lf^*E` is the class of `f^*P`, and `f^*P` is `m`-pseudo-coherent by hypothesis. -/
theorem isPseudoCoherentFrom_derivedPullback_of_complexLevel
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (E : DerivedCategory (OXMod.{u} Y)) (m : ℤ)
    (hE : AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherentFrom (X := Y) E m)
    (hcomplex : ∀ P : CochainComplex (Modules Y) ℤ, KFlat Y P →
      AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherentComplexFrom (X := Y) P m →
      AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherentComplexFrom (X := X)
        (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) m) :
    AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherentFrom (X := X)
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj E) m := by
  obtain ⟨K, hK, ⟨eKE⟩⟩ := hE
  obtain ⟨P, p, hPkflat, _, hp, _⟩ := exists_kFlatResolution Y K
  have : IsIso (DerivedCategory.Q.map p) :=
    Localization.inverts DerivedCategory.Q
      (HomologicalComplex.quasiIso (OXMod.{u} Y) (ComplexShape.up ℤ)) p
      ((HomologicalComplex.mem_quasiIso_iff p).2 hp)
  let ePK : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj K :=
    asIso (DerivedCategory.Q.map p)
  have efinal : DerivedCategory.Q.obj
      (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj E :=
    (Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat f P hPkflat).symm ≪≫
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).mapIso (ePK ≪≫ eKE)
  exact ⟨_, hcomplex P hPkflat
    (Stacks.PseudoCoherence.DerivedCharacterization.isPseudoCoherentComplexFrom_of_iso
      (DerivedCategory.Q.obj K) m ⟨K, hK, ⟨Iso.refl _⟩⟩ P ePK), ⟨efinal⟩⟩

end AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

end
