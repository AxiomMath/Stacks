module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardClosedImmersion
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TransportAlongIso
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.ExactAlongAnIsomorphism

/-!
# Pseudo-coherence travels along restriction to an isomorphic scheme

Let `g : A ⟶ B` be an isomorphism of schemes. Restriction of sheaves of modules along `g`
(Mathlib's `AlgebraicGeometry.Scheme.Modules.restrictFunctor`) is exact, so it induces a functor
`D(𝒪_B) ⥤ D(𝒪_A)`, and that functor preserves sheaf-level pseudo-coherence in the sense of
[Stacks, Tag 08CB].

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.mapDerivedCategoryRestrictFunctorIsoPullback`: the functor
  induced on derived categories by restriction along an open immersion is the one induced by
  degreewise inverse image, `D(f|) ≅ D(f^*)`.
* `AlgebraicGeometry.Scheme.Modules.derivedPullbackObjIsoRestrictFunctor`: for an isomorphism
  `g`, the derived pullback `Lg^*E` is the restriction `D(g|)E`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.pullback_preservesFiniteLimits`: degreewise inverse image
  along an open immersion of schemes is left exact.
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_restrictFunctor_mapDerivedCategory_of_isIso`:
  pseudo-coherence of a derived object transports along restriction to an isomorphic scheme.

## References

* [Stacks Project, Definition 36.60.1 (Tag 08CB)](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Lemma 20.46.13 (Tag 09U7)](https://stacks.math.columbia.edu/tag/09U7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme.Modules

/-- Degreewise inverse image of sheaves of modules along an open immersion of schemes preserves
finite limits. -/
public instance pullback_preservesFiniteLimits {A B : Scheme.{u}} (g : A ⟶ B)
    [IsOpenImmersion g] : PreservesFiniteLimits (pullback g) :=
  preservesFiniteLimits_of_natIso (restrictFunctorIsoPullback g)

/-- Restriction along an open immersion and degreewise inverse image induce isomorphic functors on
derived categories, `D(f|) ≅ D(f^*)`. -/
def mapDerivedCategoryRestrictFunctorIsoPullback {A B : Scheme.{u}} (g : A ⟶ B)
    [IsOpenImmersion g] :
    (restrictFunctor g).mapDerivedCategory ≅ (pullback g).mapDerivedCategory :=
  Functor.mapDerivedCategoryCongr (restrictFunctorIsoPullback g)

/-- For an isomorphism of schemes `g : A ⟶ B` and an object `E` of `D(𝒪_B)`, the derived pullback
of `E` is its restriction: `Lg^*E ≅ D(g|)E`. -/
def derivedPullbackObjIsoRestrictFunctor {A B : Scheme.{u}} (g : A ⟶ B) [IsIso g]
    (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u} B.toRingedSpace)) :
    (derivedPullback g.toLRSHom.toShHom).obj E ≅ (restrictFunctor g).mapDerivedCategory.obj E :=
  (Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackIsoMapDerivedCategoryOfIsIso
      g.toLRSHom.toShHom).app E ≪≫
    ((mapDerivedCategoryRestrictFunctorIsoPullback g).app E).symm

/-- If `E` is a pseudo-coherent object of `D(𝒪_B)` in the sheaf-level sense and `g : A ⟶ B` is an
isomorphism of schemes, then the restriction of `E` along `g` is a pseudo-coherent object of
`D(𝒪_A)`. -/
theorem isPseudoCoherent_restrictFunctor_mapDerivedCategory_of_isIso {A B : Scheme.{u}}
    (g : A ⟶ B) [IsIso g]
    (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u} B.toRingedSpace))
    (hE : RingedSpace.IsPseudoCoherent (X := B.toRingedSpace) E) :
    RingedSpace.IsPseudoCoherent (X := A.toRingedSpace)
      ((restrictFunctor g).mapDerivedCategory.obj E) :=
  (Scheme.Hom.isPseudoCoherent_derivedPullback g E hE).of_iso
    (derivedPullbackObjIsoRestrictFunctor g E)

end AlgebraicGeometry.Scheme.Modules

end
