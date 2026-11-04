module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Blowup.NormalizedBlowUp
public import StacksFrontier.AlgebraicGeometry.Properties.Regular

/-!
# Resolutions by normalized blowups

A *resolution by normalized blowups* of a scheme `Y` starts at the normalization of `Y`,
continues through finitely many normalized blowups at closed points, and ends in a regular
scheme. Every scheme in the sequence is proper over `Y`.

## Main definitions

* `AlgebraicGeometry.NormalizedBlowUpChain` records the normalization and the successive
  normalized blowups, together with their morphisms to `Y` and the properness of each.
* `AlgebraicGeometry.HasResolutionByNormalizedBlowUps` asserts that such a chain ends in a
  regular scheme.

## Main results

There are no results in this file; both declarations are definitions.

## Implementation notes

The inductive chain is what expresses finiteness of the sequence: its initial morphism is the
canonical normalization `AlgebraicGeometry.Scheme.normalization`, and each later morphism is the
canonical normalized blowup `Stacks.Blowup.normalizedBlowUp` at a closed point, composed with
the preceding morphism to the base. The finiteness witnesses for irreducible components of
quasi-compact opens are what make those two canonical constructions available, and they hold on
the two-dimensional Noetherian integral schemes of the source. The predicate is stated for any
scheme for which the constructions exist, so that clients need not carry dimension or
Noetherian hypotheses in order to use it.

## References

* [Stacks Project, Tag 0BGL](https://stacks.math.columbia.edu/tag/0BGL)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0BGL.** A finite sequence starting at the normalization of `Y` and
continuing through normalized blowups at closed points. The indexed morphism is the composite
map from the current scheme down to `Y`, and properness is required at every stage. -/
inductive NormalizedBlowUpChain (Y : Scheme.{u})
    (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite) :
    (X : Scheme.{u}) → (X ⟶ Y) → Prop where
  | normalization (hproper : IsProper (Scheme.normalization Y hY)) :
      NormalizedBlowUpChain Y hY (Scheme.normalizationScheme Y hY) (Scheme.normalization Y hY)
  | blowUp {X : Scheme.{u}} {f : X ⟶ Y} (previous : NormalizedBlowUpChain Y hY X f)
      (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
      (x : X) (hx : IsClosed ({x} : Set X))
      (hproper : IsProper (Stacks.Blowup.normalizedBlowUp X hX x hx ≫ f)) :
      NormalizedBlowUpChain Y hY (Stacks.Blowup.normalizedBlowUpScheme X hX x hx)
        (Stacks.Blowup.normalizedBlowUp X hX x hx ≫ f)

/-- **Stacks Project, Tag 0BGL.** A scheme admits a *resolution of singularities by normalized
blowups* if its normalization can be followed by finitely many normalized blowups at closed
points, all proper over the scheme, so as to obtain a regular scheme. -/
@[stacks 0BGL]
abbrev HasResolutionByNormalizedBlowUps (Y : Scheme.{u}) : Prop :=
  ∃ hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite,
    ∃ (X : Scheme.{u}) (f : X ⟶ Y), NormalizedBlowUpChain Y hY X f ∧ IsRegular X

end AlgebraicGeometry

end
