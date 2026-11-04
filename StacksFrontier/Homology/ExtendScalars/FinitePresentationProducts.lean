module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import StacksFrontier.RingTheory.TensorProduct.TensorPi

/-!
# Extension of scalars along a finitely presented ring map preserves arbitrary products

Let `f : R →+* S` be a homomorphism of commutative rings making `S` a **finitely presented**
`R`-module. This file proves that `ModuleCat.extendScalars f`, that is `S ⊗[R] -`, preserves
products indexed by an *arbitrary* type.

Without a hypothesis on `S` this is false, and only *finite* products are preserved — which is
all that additivity gives. The finitely presented case is [Stacks, Tag 059K], formalized in this
library as `TensorProduct.piRightOfFinitePresentation`; what is added here is the passage
from that linear equivalence to the categorical statement, which is the form a Čech argument
over a possibly infinite covering consumes.

This is the categorical half of the algebraic input of [Stacks, Tag 0CKW]: the Čech complex of
a covering by *all* the affine opens of a scheme has an infinite product in each degree, and it
is exactly the finite presentation of `S` over `R` that lets base change be carried through it.

## Main definitions

* `ModuleCat.extendScalarsProductIso`: the comparison `S ⊗[R] (∏ Mⱼ) ≅ ∏ (S ⊗[R] Mⱼ)`, written
  at the explicit product cone `ModuleCat.HasLimit.productLimitCone`.

## Main results

* `ModuleCat.extendScalarsProductIso_comp_π`: the comparison is the one determined by the
  projections.
* `ModuleCat.preservesLimit_discrete_extendScalars`: `extendScalars f` preserves the limit of a
  discrete diagram.
* `ModuleCat.preservesLimitsOfShape_discrete_extendScalars`: hence products of every shape.

## Implementation notes

The finite presentation hypothesis is stated as
`letI := f.toAlgebra; Module.FinitePresentation R S` rather than through an `Algebra R S`
instance, because the consumer obtains it in exactly that shape from
`Stacks.Tag0CKW.flat_and_finitePresentation_of_isFiniteLocallyFree`.

Both the source and the target of `extendScalarsProductIso` are spelled as the point of
`ModuleCat.HasLimit.productLimitCone`, not as `ModuleCat.of R (∀ j, Mⱼ)`. The two are
definitionally equal, but `CategoryTheory.Limits.limit.cone` cannot be unfolded in this module —
`CategoryTheory.Limits.getLimitCone` is not exposed — so the cone spelling is the one in which
the components of `CategoryTheory.Limits.piComparison` can be rewritten.

## References

* [Stacks Project, Tag 059K](https://stacks.math.columbia.edu/tag/059K)
* [Stacks Project, Tag 0CKW](https://stacks.math.columbia.edu/tag/0CKW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- **Tensoring with a finitely presented module commutes with arbitrary products**, as a
comparison of the explicit product cones of `ModuleCat`. This is
`TensorProduct.piRightOfFinitePresentation`, [Stacks, Tag 059K], read in `ModuleCat`. -/
def extendScalarsProductIso (hfp : letI := f.toAlgebra; Module.FinitePresentation R S)
    {J : Type u} (M : J → ModuleCat.{u} R) :
    (extendScalars.{u, u, u} f).obj (ModuleCat.HasLimit.productLimitCone M).cone.pt ≅
      (ModuleCat.HasLimit.productLimitCone
        (fun j => (extendScalars.{u, u, u} f).obj (M j))).cone.pt :=
  letI := f.toAlgebra
  letI : Module.FinitePresentation R S := hfp
  (TensorProduct.piRightOfFinitePresentation R S S (fun j => (M j : Type u))).toModuleIso

/-- The comparison of products is the map determined by the projections: it is the canonical
comparison, not an unspecified isomorphism. -/
theorem extendScalarsProductIso_comp_π
    (hfp : letI := f.toAlgebra; Module.FinitePresentation R S)
    {J : Type u} (M : J → ModuleCat.{u} R) (j : J) :
    (extendScalarsProductIso f hfp M).hom ≫ (ModuleCat.HasLimit.productLimitCone
        (fun j => (extendScalars.{u, u, u} f).obj (M j))).cone.π.app (Discrete.mk j) =
      (extendScalars.{u, u, u} f).map
        ((ModuleCat.HasLimit.productLimitCone M).cone.π.app (Discrete.mk j)) := by
  let := f.toAlgebra
  let : Module.FinitePresentation R S := hfp
  ext m
  rfl

/-- **Extension of scalars along a ring map with finitely presented target preserves the limit
of a discrete diagram**, with no finiteness hypothesis on the index type. -/
theorem preservesLimit_discrete_extendScalars
    (hfp : letI := f.toAlgebra; Module.FinitePresentation R S)
    {J : Type u} (M : J → ModuleCat.{u} R) :
    PreservesLimit (Discrete.functor M) (extendScalars.{u, u, u} f) := by
  have hd' : ∀ j : J,
      (IsLimit.conePointUniqueUpToIso
          (limit.isLimit (Discrete.functor fun b => (extendScalars.{u, u, u} f).obj (M b)))
          (ModuleCat.HasLimit.productLimitCone
            (fun j => (extendScalars.{u, u, u} f).obj (M j))).isLimit).inv ≫
        Pi.π (fun b => (extendScalars.{u, u, u} f).obj (M b)) j =
      (ModuleCat.HasLimit.productLimitCone
        (fun j => (extendScalars.{u, u, u} f).obj (M j))).cone.π.app (Discrete.mk j) :=
    fun j => IsLimit.conePointUniqueUpToIso_inv_comp
      (limit.isLimit (Discrete.functor fun b => (extendScalars.{u, u, u} f).obj (M b)))
      (ModuleCat.HasLimit.productLimitCone
        (fun j => (extendScalars.{u, u, u} f).obj (M j))).isLimit (Discrete.mk j)
  have hd : ∀ j : J,
      (IsLimit.conePointUniqueUpToIso (limit.isLimit (Discrete.functor M))
          (ModuleCat.HasLimit.productLimitCone M).isLimit).hom ≫
        (ModuleCat.HasLimit.productLimitCone M).cone.π.app (Discrete.mk j) = Pi.π M j :=
    fun j => IsLimit.conePointUniqueUpToIso_hom_comp
      (limit.isLimit (Discrete.functor M))
      (ModuleCat.HasLimit.productLimitCone M).isLimit (Discrete.mk j)
  have key : piComparison (extendScalars.{u, u, u} f) M =
      (extendScalars.{u, u, u} f).map (IsLimit.conePointUniqueUpToIso
          (limit.isLimit (Discrete.functor M))
          (ModuleCat.HasLimit.productLimitCone M).isLimit).hom ≫
        (extendScalarsProductIso f hfp M).hom ≫
          (IsLimit.conePointUniqueUpToIso
            (limit.isLimit (Discrete.functor fun b => (extendScalars.{u, u, u} f).obj (M b)))
            (ModuleCat.HasLimit.productLimitCone
              (fun j => (extendScalars.{u, u, u} f).obj (M j))).isLimit).inv := by
    refine limit.hom_ext fun j => ?_
    obtain ⟨j⟩ := j
    rw [piComparison_comp_π, Category.assoc, Category.assoc,
      show _ = _ from hd' j, extendScalarsProductIso_comp_π f hfp M j, ← Functor.map_comp, hd j]
  have : IsIso (piComparison (extendScalars.{u, u, u} f) M) := by
    rw [key]; infer_instance
  exact PreservesProduct.of_iso_comparison _ M

/-- **Extension of scalars along a ring map with finitely presented target preserves products of
every shape.** Every diagram out of a discrete category is isomorphic to one of the form
`CategoryTheory.Discrete.functor`, so this is `preservesLimit_discrete_extendScalars`
transported along `CategoryTheory.Discrete.natIsoFunctor`. -/
theorem preservesLimitsOfShape_discrete_extendScalars
    (hfp : letI := f.toAlgebra; Module.FinitePresentation R S) (J : Type u) :
    PreservesLimitsOfShape (Discrete J) (extendScalars.{u, u, u} f) :=
  ⟨fun {K} =>
    have := preservesLimit_discrete_extendScalars f hfp (K.obj ∘ Discrete.mk)
    preservesLimit_of_iso_diagram _ (Discrete.natIsoFunctor (F := K)).symm⟩

end ModuleCat

end
