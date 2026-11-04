module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.RelativeSpecCriterion

/-!
# The relative spectrum of an isomorphism of quasi-coherent algebras

`AlgebraicGeometry.relativeSpecMapOfAlgebraHom` is the morphism `Spec_S(B) ⟶ Spec_S(A)` over `S`
induced by a morphism `φ : A ⟶ B` of quasi-coherent `𝒪_S`-algebras.  This file records that an
isomorphism of algebras induces an isomorphism of relative spectra.

## Main results

* `AlgebraicGeometry.isIso_relativeSpecMapOfAlgebraHom`: the morphism of relative spectra attached
  to an isomorphism of quasi-coherent algebras is an isomorphism.
-/

@[expose] public section

open CategoryTheory
open Stacks.AffineAlgebraEquivalence
open Stacks.RelativeSpec (AlgebraSheaf)

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} (A B : AlgebraSheaf S) [AlgebraSheaf.IsQuasicoherent A]
  [AlgebraSheaf.IsQuasicoherent B] (φ : A ⟶ B)

/-- **The morphism of relative spectra induced by an isomorphism of quasi-coherent algebras is
an isomorphism.**

Its inverse is the morphism induced by the inverse algebra map: the two composites induce the
identity on pushed-forward structure sheaves by
`AlgebraicGeometry.pushforwardAlgebraMap_relativeSpecMapOfAlgebraHom`, and a morphism over `S`
into a scheme affine over `S` is determined by the map it induces there
(`Stacks.AffineAlgebraEquivalence.eq_of_pushforwardAlgebraMap_eq`). -/
instance isIso_relativeSpecMapOfAlgebraHom [IsIso φ] :
    IsIso (relativeSpecMapOfAlgebraHom A B φ) := by
  refine ⟨relativeSpecMapOfAlgebraHom B A (inv φ), ?_, ?_⟩
  · refine eq_of_pushforwardAlgebraMap_eq ?_
    rw [pushforwardAlgebraMap_comp, pushforwardAlgebraMap_id,
      pushforwardAlgebraMap_relativeSpecMapOfAlgebraHom,
      pushforwardAlgebraMap_relativeSpecMapOfAlgebraHom]
    simp
  · refine eq_of_pushforwardAlgebraMap_eq ?_
    rw [pushforwardAlgebraMap_comp, pushforwardAlgebraMap_id,
      pushforwardAlgebraMap_relativeSpecMapOfAlgebraHom,
      pushforwardAlgebraMap_relativeSpecMapOfAlgebraHom]
    simp

end AlgebraicGeometry
