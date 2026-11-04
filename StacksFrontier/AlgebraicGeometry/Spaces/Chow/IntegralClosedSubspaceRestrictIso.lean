module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalDivisorCycleIsoTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedSubspaceComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp

/-!
# Restricting a module twice along a chain of integral closed subspaces

In Situation 0EDT let `X/B` be good, let `W ⊆ X` be an integral closed subspace and let
`V ⊆ W` be an integral closed subspace of `W`, with image `V' ⊆ X`
(`AlgebraicGeometry.Space.IntegralClosedSubspace.pushforward`).  For an `𝒪_X`-module `𝒩` the two
restrictions

`(𝒩|_W)|_V`   and   `(𝒩|_{V'})` pulled back along `V ≅ V'`

are isomorphic.  Both are the inverse image of `𝒩` along a morphism `V ⟶ X`, and the two
morphisms are *equal*: the inclusion of `V` in `W` followed by that of `W` in `X` is the
identification `V ≅ V'` of
`AlgebraicGeometry.Space.IntegralClosedSubspace.pushforwardIso` followed by the inclusion of
`V'` in `X`, which is
`AlgebraicGeometry.Space.IntegralClosedSubspace.pushforwardIso_hom_comp_ι`.  So the isomorphism
is the comparison of Stacks 03LU for the inverse image of a composite
(`AlgebraicGeometry.Space.modulePullbackCompIso`) on each side, with the transport along that
equality of morphisms in between.

This is the comparison that a three-level argument about divisors needs: the Weil divisor of
Stacks 0EQE of a section of `(𝒩|_W)|_V` on `V` and the one of a section of `𝒩|_{V'}` on `V'` are
cycles for two different modules on two different — though isomorphic — spaces, and this
isomorphism is what lets `AlgebraicGeometry.Space.canonicalDivisorCycleAt_sectionsMap_iso` and
`AlgebraicGeometry.Space.canonicalDivisorCycleAt_pushforwardOfIso` be applied in turn.

## Main definitions

* `AlgebraicGeometry.Space.integralClosedSubspaceRestrictPushforwardIso`: the isomorphism
  `(𝒩|_W)|_V ≅ (V ≅ V')^*(𝒩|_{V'})`.

## Main results

* `AlgebraicGeometry.Space.closedSubspaceHom_comp_eq_pushforwardIso_hom_comp`: the two morphisms
  `V ⟶ X` agree.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (V : IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor)

/-- The identification `V ≅ V'` of an integral closed subspace of `W ⊆ X` with its image in `X`,
read as an isomorphism of objects of `AlgebraicGeometry.Space.AlgebraicSpaces`, which is the form
in which a module is pulled back along it. -/
abbrev integralClosedSubspacePushforwardSpaceIso :
    (⟨V.subspace.toFunctor, V.isClosedSubspace.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ≅
      ⟨(integralClosedSubspaceImage D sX hX W V).subspace.toFunctor,
        (integralClosedSubspaceImage D sX hX W V).isClosedSubspace.1⟩ :=
  algebraicSpacesIsoOfIso D.site D.base D.base_mem _ _
    (IntegralClosedSubspace.pushforwardIso D.site D.base D.base_mem hX.1 W.isClosedSubspace.1
      (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2 V)

/-- **The two morphisms `V ⟶ X` agree.**  Including an integral closed subspace `V` of `W ⊆ X`
into `W` and then `W` into `X` is the same as identifying `V` with its image `V' ⊆ X` and
including `V'` into `X`.

This is `AlgebraicGeometry.Space.IntegralClosedSubspace.pushforwardIso_hom_comp_ι` read in
`AlgebraicGeometry.Space.AlgebraicSpaces`, where a morphism is determined by the underlying
morphism of functors. -/
theorem closedSubspaceHom_comp_eq_pushforwardIso_hom_comp :
    closedSubspaceHom D.site D.base D.base_mem W.isClosedSubspace.1 V.subspace
          V.isClosedSubspace ≫
        closedSubspaceHom D.site D.base D.base_mem hX.1 W.subspace W.isClosedSubspace =
      (integralClosedSubspacePushforwardSpaceIso D sX hX W V).hom ≫
        closedSubspaceHom D.site D.base D.base_mem hX.1
          (integralClosedSubspaceImage D sX hX W V).subspace
          (integralClosedSubspaceImage D sX hX W V).isClosedSubspace :=
  ObjectProperty.hom_ext _
    (IntegralClosedSubspace.pushforwardIso_hom_comp_ι D.site D.base D.base_mem hX.1
      W.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2 V).symm

/-- **`(𝒩|_W)|_V ≅ (V ≅ V')^*(𝒩|_{V'})`.**  Restricting an `𝒪_X`-module to an integral closed
subspace `W ⊆ X` and then to an integral closed subspace `V ⊆ W` gives the same module, up to
the identification of `V` with its image `V' ⊆ X`, as restricting it to `V'`.

Both sides are the inverse image of `𝒩` along a morphism `V ⟶ X`, the composite comparisons
being `AlgebraicGeometry.Space.modulePullbackCompIso` (Stacks 03LU), and the two morphisms agree
by `AlgebraicGeometry.Space.closedSubspaceHom_comp_eq_pushforwardIso_hom_comp`. -/
def integralClosedSubspaceRestrictPushforwardIso
    (N : Modules.{u, u} D.site D.base D.base_mem X hX.1) :
    integralClosedSubspaceRestrict D (W.subspace.ι ≫ sX)
          (isGood_integralClosedSubspace D sX hX W)
          (integralClosedSubspaceRestrict D sX hX N W) V ≅
      (modulePullback D.site D.base D.base_mem
          (integralClosedSubspacePushforwardSpaceIso D sX hX W V).hom).obj
        (integralClosedSubspaceRestrict D sX hX N (integralClosedSubspaceImage D sX hX W V)) :=
  (modulePullbackCompIso D.site D.base D.base_mem
      (closedSubspaceHom D.site D.base D.base_mem W.isClosedSubspace.1 V.subspace
        V.isClosedSubspace)
      (closedSubspaceHom D.site D.base D.base_mem hX.1 W.subspace W.isClosedSubspace)).app N ≪≫
    (closedSubspaceHom_comp_eq_pushforwardIso_hom_comp D sX hX W V ▸
      ((modulePullbackCompIso D.site D.base D.base_mem
        (integralClosedSubspacePushforwardSpaceIso D sX hX W V).hom
        (closedSubspaceHom D.site D.base D.base_mem hX.1
          (integralClosedSubspaceImage D sX hX W V).subspace
          (integralClosedSubspaceImage D sX hX W V).isClosedSubspace)).app N).symm)

end AlgebraicGeometry.Space

end
