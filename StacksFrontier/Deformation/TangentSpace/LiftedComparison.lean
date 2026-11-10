module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Module.ULift
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import StacksFrontier.Deformation.PredeformationTangent.TangentVectorSpace

/-!
# Comparing the two models of the tangent space of a predeformation category

The tangent space of a predeformation category `𝓖` over `𝒞_Λ` appears in this development in
two shapes, differing only in which rank-one `k`-module is used to build the dual numbers:

* `Deformation.artinianTangentSpace Λ k F`, the *unlifted* model, which evaluates `F` on the
  square-zero extension of `k` by `FGModuleCat.of k k`;
* `Deformation.tangentSpaceArtinian Λ k F`, the *lifted* model, which evaluates `F` on the
  square-zero extension of `k` by `FGModuleCat.of k (ULift k)` and so is available in a
  carrier universe larger than that of `k`.

Both carry the canonical `k`-vector-space structure of Stacks 06IH, and — this is the point
that makes a comparison possible at all — they carry it for the *same reason*: the linear
lift `Deformation.associatedTangentSpaceModuleStructureUnlifted` of the set-valued functor
`V ↦ 𝓖(k[V])` is by definition the universe specialization
`Deformation.associatedTangentSpaceModuleStructure.{u, w, w}` of the lift used for the lifted
model. So there is a single `k`-linear, additive, module-valued functor `L` on finitely
generated `k`-modules underlying both, the two tangent spaces are the carriers of `L` at
`FGModuleCat.of k (ULift k)` and at `FGModuleCat.of k k` respectively, and those two
`k`-modules are isomorphic in `FGModuleCat k` because `ULift.moduleEquiv` is a `k`-linear
equivalence `ULift k ≃ₗ[k] k`. Applying `L` to that isomorphism gives the comparison, and it
is linear for the canonical structures rather than merely bijective.

This matters because the two models are produced and consumed at opposite ends of the
Schlessinger theory. The finiteness criterion
`Deformation.finiteDimensional_artinianTangentSpace_of_natural_injection` concludes about
`Deformation.artinianTangentSpace`; whereas the hull theorem
`Deformation.exists_hull_isomorphismClasses` (Stacks 06IZ) requires a `FiniteDimensional`
*instance* for `Deformation.tangentSpaceArtinian`, and so does the finiteness hypothesis of
`Deformation.Examples.ProjectiveGradedAlgebra.exists_hull_isomorphismClasses_gradedAlgebra`,
whose module docstring names that criterion as the thing it has to be fed into. This file is
the link between them.

## Main definitions

* `Deformation.fgModuleCatULiftSelfIso`: the isomorphism
  `FGModuleCat.of k (ULift k) ≅ FGModuleCat.of k k` of rank-one modules.
* `Deformation.tangentSpaceArtinianLinearEquivUnlifted`: the `k`-linear comparison of the two
  models of the tangent space, for their canonical structures of Stacks 06IH.

## Main results

* `Deformation.finiteDimensional_tangentSpaceArtinian_of_artinianTangentSpace`: a tangent
  space that is finite-dimensional in the unlifted model is finite-dimensional in the lifted
  model.

## Implementation notes

As in Stacks 06IJ the (S2) and predeformation hypotheses appear as `Fact` instances, because
that is how Stacks 06IH exposes the vector-space structure to instance search. The main
theorem therefore states both its hypothesis and its conclusion under a `letI` prefix
supplying those two instances, matching
`Deformation.finiteDimensional_artinianTangentSpace_of_natural_injection`; a caller that has
already installed the instances with `haveI` can use it directly.

`StacksFrontier.Deformation.TangentSpace.BijectiveDifferential` compares the two models for an
arbitrary set-valued functor, as a bare `Equiv` obtained by applying the functor to an
isomorphism of dual-number objects. That comparison says nothing about the vector-space
structures, which are not defined from the value at one object but from the whole functor
`V ↦ 𝓖(k[V])`; the present comparison is linear precisely because it is the image under the
common linear lift of an isomorphism of rank-one modules.

## References

* [Stacks Project, Tag 06IH](https://stacks.math.columbia.edu/tag/06IH)
* [Stacks Project, Tag 06IZ](https://stacks.math.columbia.edu/tag/06IZ)
-/

@[expose] public section

open CategoryTheory

namespace Deformation

universe u w u₁ v₁

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The rank-one module `ULift k` used by the lifted tangent-space model is isomorphic, in the
category of finitely generated `k`-modules, to the rank-one module `k` used by the unlifted
one. It is the image of the `k`-linear equivalence `ULift.moduleEquiv`. -/
noncomputable def fgModuleCatULiftSelfIso :
    FGModuleCat.of k (ULift.{w} k) ≅ FGModuleCat.of k k :=
  (ULift.moduleEquiv (R := k) (M := k) : ULift.{w} k ≃ₗ[k] k).toFGModuleCatIso

/-- The `k`-linear comparison of the two models of the tangent space of a predeformation
category whose functor of isomorphism classes satisfies Schlessinger's condition (S2), for
their canonical vector-space structures of Stacks 06IH.

Both structures are transported from the same linear lift `L` of the set-valued functor
`V ↦ 𝓖(k[V])`: the unlifted one from the carrier of `L` at `FGModuleCat.of k k` and the
lifted one from its carrier at `FGModuleCat.of k (ULift k)`. The comparison is the image under
`L` of `Deformation.fgModuleCatULiftSelfIso`, conjugated by those two transports. -/
noncomputable def tangentSpaceArtinianLinearEquivUnlifted
    (𝓖 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓖 : IsPredeformationCategory 𝓖.p)
    (hS2 : SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓖 h𝓖.cofibered)))
    [Fact (IsPredeformationCategory 𝓖.p)]
    [Fact (SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓖 h𝓖.cofibered)))] :
    tangentSpaceArtinian.{u, w, w} Λ k (isomorphismClasses 𝓖 h𝓖.cofibered) ≃ₗ[k]
      artinianTangentSpace Λ k (isomorphismClasses 𝓖 h𝓖.cofibered) :=
  ((associatedTangentSpaceCarrierLinearEquiv.{u, w, w} 𝓖 h𝓖 hS2).symm.trans
      (((associatedTangentSpaceModuleStructure.{u, w, w} 𝓖 h𝓖 hS2).functor.mapIso
        fgModuleCatULiftSelfIso).toLinearEquiv)).trans
    (associatedTangentSpaceCarrierLinearEquivUnlifted 𝓖 h𝓖 hS2)

/-- If the tangent space of a predeformation category satisfying Schlessinger's condition (S2)
is finite-dimensional in the unlifted model `Deformation.artinianTangentSpace`, then it is
finite-dimensional in the lifted model `Deformation.tangentSpaceArtinian`.

This converts the output of
`Deformation.finiteDimensional_artinianTangentSpace_of_natural_injection` into the instance
required by the hull theorem `Deformation.exists_hull_isomorphismClasses` of Stacks 06IZ. -/
theorem finiteDimensional_tangentSpaceArtinian_of_artinianTangentSpace
    (𝓖 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓖 : IsPredeformationCategory 𝓖.p)
    (hS2 : SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓖 h𝓖.cofibered)))
    (h : letI : Fact (IsPredeformationCategory 𝓖.p) := ⟨h𝓖⟩
         letI : Fact (SchlessingerConditionS2
           (Functor.Elements.π (isomorphismClasses 𝓖 h𝓖.cofibered))) := ⟨hS2⟩
         FiniteDimensional k (artinianTangentSpace Λ k (isomorphismClasses 𝓖 h𝓖.cofibered))) :
    letI : Fact (IsPredeformationCategory 𝓖.p) := ⟨h𝓖⟩
    letI : Fact (SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓖 h𝓖.cofibered))) := ⟨hS2⟩
    FiniteDimensional k
      (tangentSpaceArtinian.{u, w, w} Λ k (isomorphismClasses 𝓖 h𝓖.cofibered)) := by
  let : Fact (IsPredeformationCategory 𝓖.p) := ⟨h𝓖⟩
  let : Fact (SchlessingerConditionS2
    (Functor.Elements.π (isomorphismClasses 𝓖 h𝓖.cofibered))) := ⟨hS2⟩
  let : FiniteDimensional k
    (artinianTangentSpace Λ k (isomorphismClasses 𝓖 h𝓖.cofibered)) := h
  exact (tangentSpaceArtinianLinearEquivUnlifted 𝓖 h𝓖 hS2).symm.finiteDimensional

end Deformation

end
