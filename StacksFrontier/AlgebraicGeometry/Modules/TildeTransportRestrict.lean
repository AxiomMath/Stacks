module

public import StacksFrontier.AlgebraicGeometry.PushforwardRegularity.OpenBaseChange
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeOpenImmersion
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.AffineFiniteProjective
public import StacksFrontier.Topology.Sheaves.Cohomology.TransportAlongAnIsomorphism

/-!
# Direct image along an isomorphism of schemes is restriction along its inverse

Let `e : W ≅ Z` be an isomorphism of schemes.  Module sheaves on `W` can be carried to `Z` in
two ways, and the library states its results in both: as the direct image
`AlgebraicGeometry.RingedSpace.PseudoCoherence.directImage` along the morphism of ringed spaces
underlying `e.hom`, which is how `Stacks.AffineTilde.transportTildeComplex` and with it the
strict-perfection transport of [Stacks, Tag 08CB] are phrased; and as Mathlib's restriction
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` along the open immersion `e.inv`, which is
how the comparison of décalages on an affine scheme, [Stacks, Tag 0GTV], and the `represents`
field of an affine chart of Situation 0F8S are phrased.  This file identifies the two.

## Main definitions

* `AlgebraicGeometry.RingedSpace.PseudoCoherence.moduleEquivFunctorIsoRestrictFunctor`:
  **the direct image along `e` is the restriction along `e.inv`.**
* `Stacks.AffineTilde.transportTildeComplexIsoRestrict`: the complex of `𝒪_Z`-modules obtained
  by sheafifying a complex of `R`-modules on `Spec R` and transporting it along an isomorphism
  `e : Spec R ≅ Z` is the degreewise restriction of `\widetilde{E^•}` along `e.inv`.

## Implementation notes

Both functors are a `SheafOfModules.pushforward`, but along comparison maps of ring sheaves
built over different functors on opens — the image functor of the open immersion `e.inv` on one
side, `TopologicalSpace.Opens.map` of the base map of `e.hom` on the other — so they are not
identified by any congruence lemma for `SheafOfModules.pushforward`.  What identifies them is
that both are left adjoint to the same functor: `AlgebraicGeometry.Scheme.Modules.pushforward`
of a morphism of schemes is by definition the direct image along the underlying morphism of
ringed spaces, so the direct image along `e.hom` is `Scheme.Modules.pushforward e.hom`, and
`Stacks.AlgebraicGeometry.OpenBaseChange.restrictFunctorIsoPushforwardInv` already identifies
that with restriction along `e.inv` by uniqueness of left adjoints.

## References

* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Tag 0GTV](https://stacks.math.columbia.edu/tag/0GTV)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry StrictlyPerfect TopologicalSpace
open Stacks.Cohomology.TransportAlongIso (ringedSpaceIsoOfSchemeIso)

universe u

namespace AlgebraicGeometry.RingedSpace.PseudoCoherence

/-- **The direct image of module sheaves along an isomorphism of schemes is the restriction
along its inverse.**  For `e : W ≅ Z` the equivalence
`AlgebraicGeometry.RingedSpace.PseudoCoherence.moduleEquivOfIso` attached to the underlying
isomorphism of ringed spaces has underlying functor the direct image along `e.hom`, which is
`AlgebraicGeometry.Scheme.Modules.pushforward e.hom`; that functor is left adjoint to the
direct image along `e.inv`, as is restriction along `e.inv`, so the two agree. -/
def moduleEquivFunctorIsoRestrictFunctor {W Z : Scheme.{u}} (e : W ≅ Z) :
    (moduleEquivOfIso (ringedSpaceIsoOfSchemeIso e)).functor ≅
      Scheme.Modules.restrictFunctor e.inv :=
  (Stacks.AlgebraicGeometry.OpenBaseChange.restrictFunctorIsoPushforwardInv e.symm).symm

end AlgebraicGeometry.RingedSpace.PseudoCoherence

namespace Stacks.AffineTilde

variable (R : CommRingCat.{u})

/-- **The complex of `𝒪_Z`-modules attached to a complex of `R`-modules along an isomorphism
`e : Spec R ≅ Z` is the degreewise restriction of `\widetilde{E^•}` along `e.inv`.**

`Stacks.AffineTilde.transportTildeComplex` sheafifies `E^•` on `Spec R` and takes the direct
image along the morphism of ringed spaces underlying `e.hom`; that direct image is restriction
along `e.inv` by
`AlgebraicGeometry.RingedSpace.PseudoCoherence.moduleEquivFunctorIsoRestrictFunctor`, so the
isomorphism is that one read at `\widetilde{E^n}` in each degree, its commutation with the
differentials being the naturality of the comparison. -/
def transportTildeComplexIsoRestrict {Z : Scheme.{u}} (e : Spec R ≅ Z)
    (E : CochainComplex (ModuleCat.{u} R) ℤ) :
    transportTildeComplex (ringedSpaceIsoOfSchemeIso e) E ≅
      ((AlgebraicGeometry.tilde.functor R ⋙
        Scheme.Modules.restrictFunctor e.inv).mapHomologicalComplex (ComplexShape.up ℤ)).obj E :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (AlgebraicGeometry.RingedSpace.PseudoCoherence.moduleEquivFunctorIsoRestrictFunctor
      e).app ((AlgebraicGeometry.tilde.functor R).obj (E.X n)))
    fun _ _ _ =>
      ((AlgebraicGeometry.RingedSpace.PseudoCoherence.moduleEquivFunctorIsoRestrictFunctor
        e).hom.naturality _).symm

end Stacks.AffineTilde

end
