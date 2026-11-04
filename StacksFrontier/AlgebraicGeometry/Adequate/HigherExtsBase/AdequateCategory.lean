module

public import Mathlib.CategoryTheory.Abelian.Subcategory
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Cokernels
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Kernels

/-!
# The abelian category of adequate functors

The adequate module-valued functors on the commutative `A`-algebras form a strictly full
subcategory `AdequateFunctor.adequate A` of all module-valued functors which contains the zero
functor and is closed under kernels and cokernels. This file records those closure properties as
instances, so that the full subcategory inherits the kernels, the cokernels and the normal
mono/epi structure of the ambient category, and so that the inclusion functor preserves
monomorphisms.

## Main definitions

* `AdequateFunctor.adequate` — adequacy as a property of module-valued functors, cutting out the
  full subcategory `(AdequateFunctor.adequate A).FullSubcategory` of adequate functors.

## Main results

* `AdequateFunctor.adequate` contains zero and is closed under isomorphisms, kernels and
  cokernels, hence the full subcategory it cuts out has kernels and cokernels and is a
  normal mono and normal epi category.
* `AdequateFunctor.preservesMonomorphisms_ι_adequate` — the inclusion of the adequate functors
  into all module-valued functors preserves monomorphisms, so a monomorphism of adequate functors
  is already a monomorphism of module-valued functors.

## Implementation notes

The closure properties are the ones already available for the full domain of algebras: the zero
functor is the extension of the zero module, kernels are [Stacks, Tag 06V3] and cokernels are
[Stacks, Tag 06V2]. Closure under extensions, which would make `adequate` a weak Serre class and
the inclusion exact, is not asserted here.

## References

* [Stacks Project, Tag 06V2](https://stacks.math.columbia.edu/tag/06V2)
* [Stacks Project, Tag 06V3](https://stacks.math.columbia.edu/tag/06V3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u v w

namespace AdequateFunctor

variable (A : Type u) [CommRing A]

/-- Adequacy, as a property of the module-valued functors on all commutative `A`-algebras. -/
public abbrev adequate : ObjectProperty (ModuleValuedFunctor.{w, v} A) :=
  fun F ↦ IsAdequate (𝟭 _) F

/-- Adequacy is invariant under isomorphism of module-valued functors. -/
public instance adequate_isClosedUnderIsomorphisms :
    (adequate.{u, v, w} A).IsClosedUnderIsomorphisms where
  of_iso e hF := IsAdequate.of_iso hF e.symm

/-- The zero functor is adequate: it is the kernel of the identity of the zero module. -/
public instance adequate_containsZero : (adequate.{u, v, w} A).ContainsZero where
  exists_zero := by
    refine ⟨0, isZero_zero _, ?_⟩
    let M : ModuleCat.{max u v w} A := 0
    refine ⟨M, M, 𝟙 M, ⟨IsZero.iso (Functor.map_isZero _ (isZero_zero _)) ?_⟩⟩
    have : Mono ((moduleExtensionFunctor.{max u v w, v} A).map (𝟙 M)) :=
      (moduleExtensionFunctor.{max u v w, v} A).map_id M ▸ inferInstance
    exact isZero_kernel_of_mono _

/-- The kernel of a morphism of adequate functors is adequate. -/
public instance adequate_isClosedUnderKernels :
    (adequate.{u, v, w} A).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨φ, k, hk, hF, hG⟩
    exact IsAdequate.of_iso (isAdequate_kernel φ hF hG)
      (IsLimit.conePointUniqueUpToIso hk (limit.isLimit (parallelPair φ 0)))

/-- The cokernel of a morphism of adequate functors is adequate. -/
public instance adequate_isClosedUnderCokernels :
    (adequate.{u, v, w} A).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨φ, k, hk, hF, hG⟩
    exact IsAdequate.of_iso (isAdequate_cokernel φ hF hG)
      (IsColimit.coconePointUniqueUpToIso hk (colimit.isColimit (parallelPair φ 0)))

/-- The inclusion of the adequate functors into all module-valued functors preserves
monomorphisms, because the adequate functors contain zero and are closed under kernels. -/
public instance preservesMonomorphisms_ι_adequate :
    (adequate.{u, v, w} A).ι.PreservesMonomorphisms :=
  ObjectProperty.preservesMonomorphisms_ι_of_isNormalEpiCategory _

end AdequateFunctor

end
