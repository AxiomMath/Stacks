module

public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.Pushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
import StacksCore.Tactic.StacksAttribute

/-!
# Derived direct image and restriction to an open of the base, for schemes

Let `f : X ⟶ S` be a morphism of schemes and let `U ⊆ S` be an open. [Stacks, Tag 08FE] identifies
the restriction to `U` of `Rf_*E` with the derived direct image along `f|_{f^{-1}U} : f^{-1}U ⟶ U`
of the restriction of `E` to `f^{-1}U`, the square
```
f⁻¹U --f|--> U
  |          |
  ι          ι
  v          v
  X ---f---> S
```
being Cartesian with open immersions on the vertical sides. This file states that identification
for schemes, at `AlgebraicGeometry.schemeDerivedPushforward`, for an arbitrary object of `D(𝒪_X)`.

## Main results

* `AlgebraicGeometry.schemeDerivedPushforwardRestrictOpenIso`: **[Stacks, Tag 08FE] for schemes**,
  for a Cartesian square with open immersions on the vertical sides, with
  `AlgebraicGeometry.Scheme.Modules.restrictFunctor` on both restriction edges — the spelling in
  which the restriction of a complex to an open subscheme is usually met.
* `AlgebraicGeometry.schemeDerivedPushforwardRestrictOpensIso`: the same at the square of
  `AlgebraicGeometry.isPullback_morphismRestrict`, so that the two restriction edges are the
  inclusions of `U` and of `f ⁻¹ᵁ U` and no square has to be supplied.

## Implementation notes

The content is exactly `Stacks.Cohomology.derivedPushforwardRestrictIso`, instantiated at the
square pushed to ringed spaces. The four right-derived-functor witnesses are supplied explicitly:
they are phrased in the scheme spelling of the categories of modules, which instance search does
not unify with the ringed-space spelling [Stacks, Tag 08FE] is stated in. The two restriction
edges are instantiated at `CategoryTheory.Functor.mapDerivedCategory` of the degreewise pullback
along the two open immersions, which is exact, so no derived functor appears on those edges.

`IsOpenImmersion g'` is not an instance binder: it is a consequence of the square and of
`IsOpenImmersion g`, so it is bound in the statement by `letI` rather than assumed. That is what
keeps `(Scheme.Modules.restrictFunctor g').mapDerivedCategory`, whose exactness instances need it,
writable in the conclusion.

This is the generalisation to an arbitrary object of `D(𝒪_X)` of the construction inside
`AlgebraicGeometry.ProperFlatRankOpen.openImmersionBaseChangeDerivedPushforward`, where it is used
at a module placed in degree zero and packaged together with hypotheses of properness, finite
presentation and flatness that the identification does not use.

## References

* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.SchemeCohomology (hom)
open Stacks.Cohomology.PerfectComplexTriangles (mapDerivedCategoryIsoOfNatIso)

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-- **[Stacks, Tag 08FE] for schemes.** For a Cartesian square of schemes
```
X' --f'--> T
|          |
g'         g
v          v
X ---f---> S
```
whose vertical sides are open immersions, the restriction to `T` of `Rf_*E` is the derived direct
image along `f'` of the restriction of `E` to `X'`.

Restriction along an open immersion is exact, so both restriction edges are the functors induced
on derived categories and carry no derivation. -/
@[stacks 08FE "for schemes, at the derived direct image of Tag 079W, with restriction to an \
open subscheme on the restriction edges"]
def schemeDerivedPushforwardRestrictOpenIso {X S X' T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [IsOpenImmersion g] (f' : X' ⟶ T) (g' : X' ⟶ X) (hsq : IsPullback g' f' f g)
    (E : DerivedCategory X.Modules) :
    letI : IsOpenImmersion g' := MorphismProperty.of_isPullback hsq.flip inferInstance
    (Scheme.Modules.restrictFunctor g).mapDerivedCategory.obj
        ((schemeDerivedPushforward f).obj E) ≅
      (schemeDerivedPushforward f').obj
        ((Scheme.Modules.restrictFunctor g').mapDerivedCategory.obj E) := by
  letI hg' : IsOpenImmersion g' := MorphismProperty.of_isPullback hsq.flip inferInstance
  have hli : PreservesFiniteLimits (Scheme.Modules.pullback g') :=
    pullback_preservesFiniteLimits_of_isOpenImmersion g'
  have hlj : PreservesFiniteLimits (Scheme.Modules.pullback g) :=
    pullback_preservesFiniteLimits_of_isOpenImmersion g
  have hiR : (Scheme.Modules.pullback g').mapDerivedCategory.IsRightDerivedFunctor
      (Scheme.Modules.pullback g').mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts _ _
      (Scheme.Modules.pullback g').mapDerivedCategoryFactorsh
  have hjR : (Scheme.Modules.pullback g).mapDerivedCategory.IsRightDerivedFunctor
      (Scheme.Modules.pullback g).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso S.Modules (ComplexShape.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts _ _
      (Scheme.Modules.pullback g).mapDerivedCategoryFactorsh
  have hfR : (schemeDerivedPushforward f).IsRightDerivedFunctor (schemeDerivedPushforwardUnit f)
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) := inferInstance
  have hf'R : (schemeDerivedPushforward f').IsRightDerivedFunctor (schemeDerivedPushforwardUnit f')
      (HomotopyCategory.quasiIso X'.Modules (ComplexShape.up ℤ)) := inferInstance
  let e : schemeDerivedPushforward f ⋙ (Scheme.Modules.pullback g).mapDerivedCategory ≅
      (Scheme.Modules.pullback g').mapDerivedCategory ⋙ schemeDerivedPushforward f' :=
    @Stacks.Cohomology.derivedPushforwardRestrictIso _ _ _ _
      (hom f) (hom g') (hom g) (hom f') _ _
      (isPullback_toShHom g' f' f g hsq) _ _ _ _
      (schemeDerivedPushforward f) (schemeDerivedPushforward f')
      (Scheme.Modules.pullback g').mapDerivedCategory
      (Scheme.Modules.pullback g).mapDerivedCategory
      (schemeDerivedPushforwardUnit f) (schemeDerivedPushforwardUnit f')
      (Scheme.Modules.pullback g').mapDerivedCategoryFactorsh.inv
      (Scheme.Modules.pullback g).mapDerivedCategoryFactorsh.inv
      hfR hf'R hiR hjR
  exact (mapDerivedCategoryIsoOfNatIso (Scheme.Modules.restrictFunctor g)
        (Scheme.Modules.pullback g) (Scheme.Modules.restrictFunctorIsoPullback g)).app _ ≪≫
    e.app E ≪≫
    (schemeDerivedPushforward f').mapIso
      ((mapDerivedCategoryIsoOfNatIso (Scheme.Modules.restrictFunctor g')
        (Scheme.Modules.pullback g') (Scheme.Modules.restrictFunctorIsoPullback g')).app E).symm

/-- **[Stacks, Tag 08FE] for schemes, at an open of the base.** The restriction to an open
`U ⊆ S` of `Rf_*E` is the derived direct image along `f ∣_ U : f ⁻¹ᵁ U ⟶ U` of the restriction of
`E` to `f ⁻¹ᵁ U`.

This is `AlgebraicGeometry.schemeDerivedPushforwardRestrictOpenIso` at the Cartesian square of
`AlgebraicGeometry.isPullback_morphismRestrict`. -/
@[stacks 08FE "for schemes, at the restriction of f to the preimage of an open of the base"]
def schemeDerivedPushforwardRestrictOpensIso {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens)
    (E : DerivedCategory X.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj
        ((schemeDerivedPushforward f).obj E) ≅
      (schemeDerivedPushforward (f ∣_ U)).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).mapDerivedCategory.obj E) :=
  schemeDerivedPushforwardRestrictOpenIso f U.ι (f ∣_ U) (f ⁻¹ᵁ U).ι
    (isPullback_morphismRestrict f U).flip E

end AlgebraicGeometry

end
