module

public import StacksFrontier.AlgebraicGeometry.RelativeSpec.AlgebraHomComparison
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.RelativeSpecClosedImmersion.Basic

/-!
# The two morphisms of relative spectra attached to a morphism of algebras agree

Let `S` be a scheme and `ψ : 𝓐 ⟶ 𝓑` a morphism of quasi-coherent sheaves of commutative
`𝒪_S`-algebras. The induced morphism of relative spectra `Spec_S(𝓑) ⟶ Spec_S(𝓐)` over `S` has
two constructions in this library: one through the representability of the relative spectrum
functor ([Stacks, Tag 01LV]), specified by its universal element, and one through the
anti-equivalence between schemes affine over `S` and quasi-coherent `𝒪_S`-algebras
([Stacks, Tag 01S8]), specified by the map it induces on pushed-forward structure sheaves. This
file proves that they are the same morphism, and deduces that the first is a closed immersion
when `ψ` is locally surjective, because the second is.

## Main results

* `Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraHom_eq`: the morphism of relative spectra
  defined by the universal element is the one defined by the map on pushed-forward structure
  sheaves.
* `Stacks.RelativeSpec.isClosedImmersion_relativeSpectrumMapOfAlgebraHom_of_isLocallySurjective`:
  **the relative spectrum of a locally surjective morphism of quasi-coherent algebra sheaves is
  a closed immersion**, for the morphism defined by the universal element.

## Implementation notes

The comparison is the uniqueness half of the representing bijection: a morphism into the
relative spectrum is determined by the structure morphism of its source together with its
universal algebra map (`Stacks.RelativeSpec.pullback_universalRelativeSpecPair_eq`). The algebra
map of the second construction over an affine open is read off from its map on pushed-forward
structure sheaves, and the universal algebra map is the inverse of the identification of
[Stacks, Tag 01LX] part (3), so the two composites cancel.

## References

* [Stacks Project, Tag 01LV](https://stacks.math.columbia.edu/tag/01LV)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01S8](https://stacks.math.columbia.edu/tag/01S8)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.RelativeSpec

variable (s : RelativeSpecSituation.{u}) (B : AlgebraSheaf s.base) (hB : B.IsQuasicoherent)
  (ψ : s.algebra ⟶ B)

/-- **The two constructions of the morphism of relative spectra induced by a morphism of
algebras agree**: the morphism specified by its universal element under the representing
bijection of [Stacks, Tag 01LV] is the morphism over the base specified by its map on
pushed-forward structure sheaves. -/
theorem relativeSpectrumMapOfAlgebraHom_eq :
    haveI := hB
    relativeSpectrumMapOfAlgebraHom s B hB ψ =
      (relativeSpecMapOfAlgebraHom s.algebra B ψ).left := by
  have := hB
  refine (relativeSpecRepresentableBy s).homEquiv.injective
    ((relativeSpectrumMapOfAlgebraHom_homEquiv s B hB ψ).trans ?_)
  refine (pullback_universalRelativeSpecPair_eq _ _
    (Over.w (relativeSpecMapOfAlgebraHom s.algebra B ψ)) fun U h => ?_).symm
  have key := pushforwardAlgebraMap_app (relativeSpecMapOfAlgebraHom s.algebra B ψ) U.1 h
  rw [pushforwardAlgebraMap_relativeSpecMapOfAlgebraHom] at key
  have hA : (universalAlgebraMap s).right.app (op U.1) ≫
      (pushforwardAlgebraIso s.algebra).hom.right.hom.app (op U.1) = 𝟙 _ :=
    congrArg (fun f : s.algebra ⟶ s.algebra => f.right.hom.app (op U.1))
      (pushforwardAlgebraIso s.algebra).inv_hom_id
  refine (congrArg ((universalAlgebraMap s).right.app (op U.1) ≫ ·) key.symm).trans ?_
  change (universalAlgebraMap s).right.app (op U.1) ≫
      (pushforwardAlgebraIso s.algebra).hom.right.hom.app (op U.1) ≫
        ψ.right.hom.app (op U.1) ≫ (pushforwardAlgebraIso B).inv.right.hom.app (op U.1) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ ψ.right.hom.app (op U.1) ≫
      (pushforwardAlgebraIso B).inv.right.hom.app (op U.1)) hA).trans (Category.id_comp _))

end Stacks.RelativeSpec

end
