module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesGraph

/-!
# Fullness in clause (1) of Stacks 0AF4 from the graph argument of Stacks 0AF6

In a formal glueing situation `(f : Y ⟶ X, Z, U = X \ Z, V = Y \ f⁻¹(Z))`, clause (1) of
Stacks 0AF4 asserts that the restriction functor of Stacks 0AF3 is an equivalence from the
algebraic spaces affine over `X` onto the glueing triples with affine legs. This module proves
that the *fullness* half of that clause needs no input specific to affine morphisms: an affine
morphism is separated, and for a separated target the graph argument of Stacks 0AF6 produces a
preimage of every morphism of glueing triples, granted only that a morphism of glueing data into
the restriction of a space over `X` whose two legs are closed immersions comes from a space over
that space.

So clause (1) — and with it clauses (2) and (3), by the reductions of
`StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesEquivalence` — is reduced here
to two essential-surjectivity statements, both about *constructing* spaces: essential
surjectivity of clause (1) itself, and the closed-immersion construction in the slice over a
space over `X` that the graph argument consumes.

## Main definitions

* `AlgebraicGeometry.Space.FormalGlueingSituation.ClosedSliceRealization`: the slice
  construction, as a named statement — the hypothesis of
  `AlgebraicGeometry.Space.FormalGlueingSituation.exists_map_eq_of_essSurj_closedImmersion`.

## Main results

* `AlgebraicGeometry.Space.FormalGlueingSituation.full_affineGlueingFunctor_of_realization`:
  fullness of clause (1) from the slice construction.
* `FormalGlueingSituation.isEquivalence_affineGlueingFunctor_of_realization` and its companions
  for clauses (2) and (3): the three clauses from essential surjectivity of clause (1) together
  with the slice construction.

## Implementation notes

Both inputs are parts of what the tag asserts (the slice construction is clause (2) read over a
base change of the situation), so these are reduction lemmas. Stacks 0AF4 is registered on
`AlgebraicGeometry.Space.FormalGlueingSituation.affineGlueingFunctor_isEquivalence`,
`closedGlueingFunctor_isEquivalence` and `finiteGlueingFunctor_isEquivalence`
(`StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesRestrictedEquivalences`).

## References

* [Stacks Project, Tag 0AF4](https://stacks.math.columbia.edu/tag/0AF4)
* [Stacks Project, Tag 0AF6](https://stacks.math.columbia.edu/tag/0AF6)
* [Stacks Project, Tag 03KO](https://stacks.math.columbia.edu/tag/03KO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.FormalGlueingSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The closed-immersion construction in the slice over a space over `X`: a morphism `ψ` of
glueing data into the restriction of a space `Qq` over `X`, whose two legs are closed
immersions, is the restriction of a morphism `k : T ⟶ Qq` of spaces over `X`, up to an
isomorphism of glueing data. This is clause (2) of Stacks 0AF4 for the base change of the
situation along `Qq ⟶ X`, read in the slice over the restriction of `Qq`. -/
def ClosedSliceRealization (D : FormalGlueingSituation B S hS) : Prop :=
  ∀ (Qq : spacesOverX D) (G : glueingData D) (ψ : G ⟶ (formalGlueingFunctor D).1.obj Qq),
    IsClosedImmersion B S hS ψ.hom.left.left →
    IsClosedImmersion B S hS ψ.hom.right.left →
    ∃ (T : spacesOverX D) (k : T ⟶ Qq) (θ : (formalGlueingFunctor D).1.obj T ≅ G),
      θ.hom ≫ ψ = (formalGlueingFunctor D).1.map k

/-- **Fullness in clause (1) of Stacks 0AF4.** A space affine over `X` is separated over `X`,
so the graph argument of Stacks 0AF6
(`AlgebraicGeometry.Space.FormalGlueingSituation.exists_map_eq_of_essSurj_closedImmersion`)
lifts every morphism between the glueing triples of two spaces affine over `X` to a morphism
over `X`, granted the slice construction. -/
theorem full_affineGlueingFunctor_of_realization (D : FormalGlueingSituation B S hS)
    (h : ClosedSliceRealization D) : (affineGlueingFunctor D).Full := by
  constructor
  intro T₁ T₂ φ
  have hsep : IsSeparated B S hS T₂.obj.obj.hom :=
    isSeparated_of_isAffineHom B S hS _ T₂.obj.property D.algebraicSpace_X T₂.property
  obtain ⟨a, ha⟩ := exists_map_eq_of_essSurj_closedImmersion D (X₁ := T₁.obj) (X₂ := T₂.obj)
    hsep h φ.hom
  exact ⟨ObjectProperty.homMk a, ObjectProperty.hom_ext _ ha⟩

/-- **Clause (1) of Stacks 0AF4 from the two constructions.** The restriction of the functor of
Stacks 0AF3 to the spaces affine over `X` is faithful unconditionally, full by the graph
argument granted the slice construction, and essentially surjective by hypothesis. -/
theorem isEquivalence_affineGlueingFunctor_of_realization (D : FormalGlueingSituation B S hS)
    (hes : (affineGlueingFunctor D).EssSurj) (h : ClosedSliceRealization D) :
    (affineGlueingFunctor D).IsEquivalence where
  faithful := faithful_affineGlueingFunctor D
  full := full_affineGlueingFunctor_of_realization D h
  essSurj := hes

/-- **Clause (2) of Stacks 0AF4 from the two constructions**, through clause (1). -/
theorem isEquivalence_closedGlueingFunctor_of_realization (D : FormalGlueingSituation B S hS)
    (hes : (affineGlueingFunctor D).EssSurj) (h : ClosedSliceRealization D) :
    (closedGlueingFunctor D).IsEquivalence :=
  isEquivalence_closedGlueingFunctor D (isEquivalence_affineGlueingFunctor_of_realization D hes h)

/-- **Clause (3) of Stacks 0AF4 from the two constructions**, through clause (1). -/
theorem isEquivalence_finiteGlueingFunctor_of_realization (D : FormalGlueingSituation B S hS)
    (hes : (affineGlueingFunctor D).EssSurj) (h : ClosedSliceRealization D) :
    (finiteGlueingFunctor D).IsEquivalence :=
  isEquivalence_finiteGlueingFunctor D (isEquivalence_affineGlueingFunctor_of_realization D hes h)

end AlgebraicGeometry.Space.FormalGlueingSituation

end
