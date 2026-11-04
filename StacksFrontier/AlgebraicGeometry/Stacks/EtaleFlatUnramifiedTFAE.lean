module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordFibreProductEtaleCover
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleFlatUnramifiedCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.UnramifiedDiagonalEtale

/-!
# Étale = locally of finite presentation, flat and unramified, for algebraic stacks (Stacks 0CJ1)

For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` the following are equivalent:

1. `f` is étale (**Stacks 0CIL**);
2. `f` is locally of finite presentation (**Stacks 06Q2**, part (1)), flat (**Stacks 06PW**) and
   unramified (**Stacks 0CIT**);
3. `f` is locally of finite presentation, flat, and its relative diagonal is étale.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isEtale_tfae`: **Stacks 0CJ1**, all three conditions,
  with no hypothesis beyond the 1-morphism `f`.

## Implementation notes

The proof follows Stacks. The equivalence of (2) and (3) is **Stacks 0CJ0** (unramified is locally
of finite type with étale diagonal), local finite type coming from local finite presentation by
**Stacks 06Q5**
(`Stack.AlgebraicStacks.isUnramified_iff_isLocallyOfFiniteType_isEtale_relativeDiagonal`).
The implication (2) ⇒ (1) is
`Stack.AlgebraicStacks.isEtale_of_isLocallyOfFinitePresentation_of_isFlat_of_isUnramified`,
which needs nothing further. For (1) ⇒ (2), an étale `f` is Deligne–Mumford, so **Stacks 0CIA**
provides a diagram `U ⟶ V` over `f` with `V ⟶ 𝒴` smooth surjective and `U ⟶ 𝒳 ×_𝒴 V` surjective
étale (`AlgebraicGeometry.Stack.hasSurjectiveEtaleSmoothDiagram_of_isDM_of_forward` at the
structure theorem of **Stacks 06N3**,
`AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM`), and
`Stack.AlgebraicStacks.isLocallyOfFinitePresentation_isFlat_isUnramified_of_isEtale`
reads local finite presentation and flatness off its top morphism (**Stacks 0468**, **0467**).

## References

* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 0CIA](https://stacks.math.columbia.edu/tag/0CIA)
* [Stacks Project, Tag 0CJ0](https://stacks.math.columbia.edu/tag/0CJ0)
* [Stacks Project, Tag 0CJ1](https://stacks.math.columbia.edu/tag/0CJ1)
* [Stacks Project, Tag 06Q5](https://stacks.math.columbia.edu/tag/06Q5)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CJ1.** For a 1-morphism `f` of algebraic stacks over `S` the following are
equivalent: `f` is étale; `f` is locally of finite presentation, flat and unramified; `f` is
locally of finite presentation, flat and has étale relative diagonal.

(2) ⇔ (3) is Stacks 0CJ0 together with Stacks 06Q5; (2) ⇒ (1) is Stacks 06LU on the top morphism
of an étale-smooth diagram; (1) ⇒ (2) uses the diagram Stacks 0CIA provides for the
Deligne–Mumford 1-morphism `f`. -/
@[stacks 0CJ1]
theorem isEtale_tfae {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    List.TFAE
      [Stack.IsEtale B S hS f,
        IsLocallyOfFinitePresentation B S hS f ∧ IsFlat B S hS f ∧ Stack.IsUnramified B S hS f,
        IsLocallyOfFinitePresentation B S hS f ∧ IsFlat B S hS f ∧
          Stack.IsEtale B S hS (relativeDiagonal B S hS f)] := by
  tfae_have 1 → 2 := fun hf =>
    isLocallyOfFinitePresentation_isFlat_isUnramified_of_isEtale B S hS f
      (Stack.hasSurjectiveEtaleSmoothDiagram_of_isDM_of_forward B S hS
        (Stack.existsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS B.contains_terminal) f hf.1)
      hf
  tfae_have 2 → 1 := fun ⟨hlfp, hflat, hunr⟩ =>
    isEtale_of_isLocallyOfFinitePresentation_of_isFlat_of_isUnramified B S hS f hlfp hflat hunr
  tfae_have 2 ↔ 3 :=
    and_congr_right fun hlfp => and_congr_right fun _ =>
      (isUnramified_iff_isLocallyOfFiniteType_isEtale_relativeDiagonal B S hS f).trans
        (and_iff_right (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hlfp))
  tfae_finish

end AlgebraicGeometry.Stack.AlgebraicStacks

end
