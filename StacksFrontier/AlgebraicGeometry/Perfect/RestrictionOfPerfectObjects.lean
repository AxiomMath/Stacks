module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictFunctorAlongIso
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictPseudoCoherentPullback
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictTarget
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.BasicProperties
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback
import StacksCore.Tactic.StacksAttribute

/-!
# Perfectness travels along restriction to an open subspace

[Stacks, Tag 09UA] says the derived pullback of a perfect object is perfect, with no hypothesis
on the morphism. Restriction of modules to an open subspace of a ringed space, and restriction
along an isomorphism of schemes, are two functors that *are* derived pullbacks after an
identification which is already available in this development — the identifications
`AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoDerivedPullback` and
`AlgebraicGeometry.Scheme.Modules.derivedPullbackObjIsoRestrictFunctor` made for the
pseudo-coherent case. This file reads [Stacks, Tag 09UA] across them, which is what a local
argument about a perfect object on a scheme needs in order to pass to an affine open.

## Main results

* `AlgebraicGeometry.RingedSpace.isPerfect_derivedRestrictModules`: the derived restriction of a
  perfect object to an open subspace is perfect.
* `AlgebraicGeometry.Scheme.Modules.isPerfect_restrictFunctor_mapDerivedCategory`: the same for
  an open subscheme `U` of a scheme, in the `restrictFunctor U.ι` spelling.
* `AlgebraicGeometry.Scheme.Modules.isPerfect_restrictFunctor_mapDerivedCategory_of_isIso`:
  perfectness transports along restriction to an isomorphic scheme.

## Implementation notes

The three statements are the perfect-object companions of
`AlgebraicGeometry.RingedSpace.isPseudoCoherent_derivedPullback` and
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_restrictFunctor_mapDerivedCategory_of_isIso`,
and are proved by the same composition: the derived-pullback preservation statement, which has
no hypothesis, followed by the identification of the derived pullback with the restriction. No
new mathematics is introduced; what is paid here is the crossing between the two spellings
`Stacks.StrictlyPerfect.OXMod X.toRingedSpace` and `AlgebraicGeometry.Scheme.Modules X` of the
category of `𝒪_X`-modules, which happens inside the `Iso.trans` and in the unification of the
statement with the term, both at default transparency.

Everything is stated at `CategoryTheory.HasDerivedCategory.standard`, as the identifications are;
the local instance carries priority `10000` because the import closure supplies a global instance
of the same class.

## References

* [Stacks Project, Lemma 20.46.14 (Tag 09UA)](https://stacks.math.columbia.edu/tag/09UA)
* [Stacks Project, Definition 20.49.1 (Tag 08CM)](https://stacks.math.columbia.edu/tag/08CM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-- **The derived restriction of a perfect object to an open subspace is perfect.** The
perfect-object companion of
`AlgebraicGeometry.RingedSpace.isPseudoCoherent_derivedPullback`: restriction to `W` is the
derived pullback along the inclusion of `W`, and the derived pullback of a perfect object is
perfect by [Stacks, Tag 09UA]. -/
public theorem isPerfect_derivedRestrictModules (X : RingedSpace.{u, u}) (W : Opens X.carrier)
    (E : DerivedCategory (OXMod.{u, u} X)) (hE : IsPerfect (X := X) E) :
    IsPerfect (X := X.restrict W.isOpenEmbedding) ((derivedRestrictModules X W).obj E) :=
  IsPerfect.of_iso (X := X.restrict W.isOpenEmbedding)
    (KFlatDerivedPullback.isPerfect_derivedPullback (X.ofRestrict W.isOpenEmbedding) E hE)
    ((derivedRestrictModulesIsoDerivedPullback X W).app E).symm

end AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- **The restriction of a perfect object to an open subscheme is perfect**, in the
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` spelling that the local arguments on a scheme
use. -/
public theorem isPerfect_restrictFunctor_mapDerivedCategory (Z : Scheme.{u}) (U : Z.Opens)
    (E : DerivedCategory (OXMod.{u, u} Z.toRingedSpace))
    (hE : RingedSpace.IsPerfect (X := Z.toRingedSpace) E) :
    RingedSpace.IsPerfect (X := U.toScheme.toRingedSpace)
      ((restrictFunctor U.ι).mapDerivedCategory.obj E) :=
  (RingedSpace.isPerfect_derivedRestrictModules Z.toRingedSpace U E hE).of_iso
    ((RingedSpace.derivedRestrictModulesIsoRestrictFunctor Z U).app E)

/-- **Perfectness travels along restriction to an isomorphic scheme.** The perfect-object
companion of
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_restrictFunctor_mapDerivedCategory_of_isIso`:
perfectness of the derived pullback `Lg^*E` is [Stacks, Tag 09UA] and needs no hypothesis on
`g`, and invertibility enters only through
`AlgebraicGeometry.Scheme.Modules.derivedPullbackObjIsoRestrictFunctor`. -/
public theorem isPerfect_restrictFunctor_mapDerivedCategory_of_isIso {A B : Scheme.{u}}
    (g : A ⟶ B) [IsIso g] (E : DerivedCategory (OXMod.{u, u} B.toRingedSpace))
    (hE : RingedSpace.IsPerfect (X := B.toRingedSpace) E) :
    RingedSpace.IsPerfect (X := A.toRingedSpace)
      ((restrictFunctor g).mapDerivedCategory.obj E) :=
  RingedSpace.IsPerfect.of_iso (X := A.toRingedSpace)
    (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback g.toLRSHom.toShHom E hE)
    (derivedPullbackObjIsoRestrictFunctor g E)

end AlgebraicGeometry.Scheme.Modules

end
