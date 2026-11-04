module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.Modification
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Stability
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.FiniteType
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.IntegralClosureBaseChange
public import StacksFrontier.AlgebraicGeometry.NormalizationBirational.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksCore.Tactic.StacksAttribute

/-!
# Normalizing a modification of the spectrum of a Nagata domain

Let `A` be a Nagata domain and let `f : X ⟶ Spec(A)` be a modification. The normalization
`ν : X^ν ⟶ X` is then finite, so `ν ≫ f` is again a modification, and `X^ν` is normal. Thus every
modification of `Spec(A)` is dominated by a *normal* modification with the same source up to
normalization.

## Main results

* `AlgebraicGeometry.isModification_normalization_comp`: the normalization of a modification of
  the spectrum of a Nagata domain is again a modification.

## Implementation notes

This is the step "since `A` is Nagata, we can replace `X` by its normalization, after which
`X ⟶ Spec(A)` is a normal modification" in the source's proof of clause (1) of
[Stacks, Tag 0BG7], stated for an arbitrary modification of the spectrum of a Nagata domain
rather than for an admissible blowup, since nothing in the argument uses the blowup.

Normality of the source needs no separate statement: it is
`AlgebraicGeometry.Scheme.isNormal_normalizationScheme`, which asks only that the quasi-compact
opens of `X` have finitely many irreducible components — the same hypothesis that forms the
normalization morphism.

The three ingredients are: the normalization morphism is birational
([Stacks, Tag 0BXC]) and birationality composes; the normalization morphism of a Nagata scheme
is finite ([Stacks, Tag 035S]), hence proper, and properness composes; and the normalization of
an integral scheme is integral ([Stacks, Tag 035Q], integral case). That `X` is a Nagata scheme
follows from `A` being a Nagata ring, because a modification is of finite type.

## References

* [Stacks Project, Tag 0BG7](https://stacks.math.columbia.edu/tag/0BG7)
* [Stacks Project, Tag 035S](https://stacks.math.columbia.edu/tag/035S)
* [Stacks Project, Tag 035Q](https://stacks.math.columbia.edu/tag/035Q)
* [Stacks Project, Tag 0BXC](https://stacks.math.columbia.edu/tag/0BXC)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **The normalization of a modification of the spectrum of a Nagata domain is a
modification.** For a Nagata domain `A` and a modification `f : X ⟶ Spec(A)`, the composite of
the normalization morphism `X^ν ⟶ X` with `f` is again a modification of `Spec(A)`. -/
public theorem isModification_normalization_comp (A : Type u) [CommRing A] [IsDomain A]
    (hNagata : IsNagataRing A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (hf : IsModification f)
    (hfin : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    IsModification (X.normalization hfin ≫ f) := by
  have hXint : IsIntegral X := hf.source_isIntegral
  have hproper : IsProper f := hf.isProper
  have hNagataX : IsNagataScheme X :=
    isNagataScheme_of_locallyOfFiniteType f (isNagataScheme_spec_of_isNagataRing A hNagata)
  have hfinite : IsFinite (X.normalization hfin) := Scheme.isFinite_normalization hNagataX hfin
  exact ⟨(Scheme.isBirational_normalization X hfin).comp hf.isBirational,
    inferInstance, inferInstance⟩

end AlgebraicGeometry

end
