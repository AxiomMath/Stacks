module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Closure under colimits of one shape from coproducts and cokernels

A colimit of a diagram of shape `J` is a coequalizer of two maps between two coproducts of the
objects of the diagram, one indexed by the objects of `J` and one by its arrows, and in a
preadditive category a coequalizer is a cokernel of a difference.  So a property of objects is
closed under colimits of shape `J` as soon as it is closed under isomorphisms, under cokernels
and under those two coproducts.

The finite case — all finite shapes at once, from finite coproducts — is
`CategoryTheory.ObjectProperty.IsClosedUnderFiniteColimits.mk'` in
`StacksDraft.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerreSets`, submodule
`FiniteLimitsFromProductsAndEqualizers`.  Here the shape is one fixed small category and only
the two coproducts it needs are required, so no `CategoryTheory.Limits.HasCoproducts` of a whole
size is assumed.

## Main results

* `CategoryTheory.ObjectProperty.IsClosedUnderColimitsOfShape.walkingParallelPair_of_cokernels`:
  in a preadditive category with cokernels, closure under cokernels gives closure under
  coequalizers.
* `CategoryTheory.ObjectProperty.IsClosedUnderColimitsOfShape.of_coproducts_and_cokernels`:
  closure under colimits of shape `J` from closure under cokernels and under coproducts indexed
  by the objects and by the arrows of `J`.

## Implementation notes

The reduction to coequalizers is Mathlib's
`CategoryTheory.Limits.hasColimit_of_coequalizer_and_coproduct` and
`CategoryTheory.Limits.preservesColimit_of_preservesCoequalizers_and_coproduct`, applied to the
full subcategory cut out by the property and to its inclusion;  the conclusion is then
`CategoryTheory.ObjectProperty.isClosedUnderColimitsOfShape_of_preservesColimitsOfShape_ι`.
Both Mathlib inputs are stated for a shape which is a small category, which is why `J` is one
here.

Closure under coequalizers is deduced rather than assumed, because the property of objects it is
applied to is `SheafOfModules.isQuasicoherentOnSite`, whose closure properties are formulated for
cokernels.  A coequalizer of `f` and `g` is a cokernel of `f - g`
(`CategoryTheory.Preadditive.isColimitCoforkOfCokernelCofork`), and a diagram indexed by
`CategoryTheory.Limits.WalkingParallelPair` is isomorphic to the parallel pair of its two
nonidentity arrows, so nothing but preadditivity is needed.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)

/-- In a preadditive category with cokernels, a property of objects closed under isomorphisms and
under cokernels is closed under coequalizers. -/
lemma IsClosedUnderColimitsOfShape.walkingParallelPair_of_cokernels [Preadditive C]
    [HasCokernels C] [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderCokernels] :
    P.IsClosedUnderColimitsOfShape WalkingParallelPair := by
  refine IsClosedUnderColimitsOfShape.mk' ?_
  rintro _ ⟨F, hF⟩
  have h := (IsColimit.precomposeHomEquiv (diagramIsoParallelPair F) _).symm
    (Preadditive.isColimitCoforkOfCokernelCofork
      (cokernelIsCokernel (F.map WalkingParallelPairHom.left -
        F.map WalkingParallelPairHom.right)))
  exact P.prop_of_iso
    (IsColimit.coconePointUniqueUpToIso (colimit.isColimit F) h).symm
    (P.prop_cokernel _ (hF WalkingParallelPair.zero) (hF WalkingParallelPair.one))

/-- A property of objects of a preadditive category with cokernels which is closed under
isomorphisms, under cokernels, and under coproducts indexed by the objects and by the arrows of a
small category `J`, is closed under colimits of shape `J`. -/
lemma IsClosedUnderColimitsOfShape.of_coproducts_and_cokernels [Preadditive C] [HasCokernels C]
    (J : Type w) [SmallCategory J] [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderCokernels]
    [HasColimitsOfShape (Discrete.{w} J) C]
    [HasColimitsOfShape (Discrete.{w} (Σ p : J × J, p.1 ⟶ p.2)) C]
    [P.IsClosedUnderColimitsOfShape (Discrete.{w} J)]
    [P.IsClosedUnderColimitsOfShape (Discrete.{w} (Σ p : J × J, p.1 ⟶ p.2))] :
    P.IsClosedUnderColimitsOfShape J := by
  have : HasCoequalizers C := Preadditive.hasCoequalizers_of_hasCokernels
  have : P.IsClosedUnderColimitsOfShape WalkingParallelPair :=
    IsClosedUnderColimitsOfShape.walkingParallelPair_of_cokernels P
  have : HasColimitsOfShape J P.FullSubcategory :=
    { has_colimit := fun F ↦ hasColimit_of_coequalizer_and_coproduct F }
  have : PreservesColimitsOfShape J P.ι :=
    preservesColimit_of_preservesCoequalizers_and_coproduct P.ι
  exact P.isClosedUnderColimitsOfShape_of_preservesColimitsOfShape_ι J

end CategoryTheory.ObjectProperty

end
