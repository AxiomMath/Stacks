module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.NeighbourhoodHoms

/-!
# The comparison of Stacks 0EIV rests on a single isomorphism

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, put `U = Spec(A) ∖ V(𝔞)` and let `𝒢`, `ℱ` be
coherent modules on `U`. The canonical map

`colim_{V ∈ 𝒱} Hom_V(𝒢|_V, ℱ|_V) ⟶ Hom_{Coh(U, I𝒪_U)}(𝒢^∧, ℱ^∧)`

of Stacks 0EIV is `Stacks.Algebraization.NeighbourhoodHoms.nbhdHomComparison`, a composite of
five maps. Four of them are isomorphisms by construction — two commutations of global sections
with an inverse limit, a shift of the ideal-power tower, and the identification of Stacks 0882.
The fifth is the comparison map of Stacks 0EG2 for the internal hom `SheafHom(𝒢, ℱ)`.

So the whole of Stacks 0EIV, and of Stacks 0EKU above it, reduces to that one comparison being
an isomorphism, and so does the conclusion of Stacks 0EKV for a pair of modules defined on `U`
itself. Stacks 0EKV in full is about an object of `colim_𝒱 Coh(𝒪_V)` defined on an arbitrary
`V ∈ 𝒱`, where this map is not defined; it is proved through Stacks 0EK2 and registered on
`Stacks.Algebraization.completionFullyFaithfulComplete_principal`.

This file isolates that reduction, so that a consumer which
establishes the comparison for `SheafHom(𝒢, ℱ)` by some route other than Stacks 0EG2 does not
have to carry the hypotheses of Stacks 0EG2 along with it.

## Main results

* `Stacks.Algebraization.NeighbourhoodHoms.nbhdHomComparison_bijective_of_isIso` — the map of
  Stacks 0EIV is bijective as soon as the comparison map of Stacks 0EG2 for the internal hom is
  an isomorphism.

## References

* [Stacks Project, Tag 0EIV](https://stacks.math.columbia.edu/tag/0EIV)
* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
* [Stacks Project, Tag 0882](https://stacks.math.columbia.edu/tag/0882)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization.NeighbourhoodHoms

open Stacks.Algebraization Stacks.LocalCohomology

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I a : Ideal A)
  (G F : AlgebraicGeometry.SheafOfModules.CoherentModules
    (complementZeroLocus A a : Scheme).ringCatSheaf)

/-- **The map of Stacks 0EIV is bijective as soon as the comparison of Stacks 0EG2 is an
isomorphism for the internal hom.** The map of Stacks 0EIV is the composite of the comparison
of Stacks 0EG2 for `SheafHom(𝒢, ℱ)` with four isomorphisms: the commutation of global sections
with the limit of the ideal-power tower, the shift of that tower, the commutation of global
sections with the limit of the completion, and the identification of Stacks 0882 of that limit
with the morphisms of the completions. -/
theorem nbhdHomComparison_bijective_of_isIso
    (hiso : IsIso (comparisonMap A I a (internalHomNear A a G F).obj)) :
    Function.Bijective (nbhdHomComparison A I a G F) := by
  have b1 : Function.Bijective
      (ConcreteCategory.hom (comparisonMap A I a (internalHomNear A a G F).obj)) :=
    (ConcreteCategory.isIso_iff_bijective _).1 hiso
  have b2 : Function.Bijective (ConcreteCategory.hom (sectionsAbLimitIso
      (adicQuotientSystem (idealSheafNearVanishing A I a)
        (internalHomNear A a G F).obj)).inv) :=
    ConcreteCategory.bijective_of_isIso _
  have b3 : Function.Bijective (ConcreteCategory.hom
      ((sectionsAb (complementZeroLocus A a : Scheme)).map
        (adicCompletionLimitIso (idealSheafNearVanishing A I a)
          (internalHomNear A a G F)).hom)) :=
    ConcreteCategory.bijective_of_isIso _
  have b4 : Function.Bijective (ConcreteCategory.hom
      (globalSectionsLimitIso (idealSheafNearVanishing A I a)
        (internalHomNear A a G F)).hom) :=
    (ConcreteCategory.isIso_iff_bijective _).1 (Iso.isIso_hom _)
  exact (completionInternalHomEquiv (complementZeroLocus A a : Scheme)
    (idealSheafNearVanishing A I a) G F).bijective.comp (b4.comp (b3.comp (b2.comp b1)))

end Stacks.Algebraization.NeighbourhoodHoms

end
