module

public import StacksFrontier.AlgebraicGeometry.GrassmannianScheme.Projective

/-!
# The Grassmannian is proper

The Grassmannian `G(k, n)_S` is proper over `S`, for every scheme `S`; in particular the
Grassmannian `G(k, n)` over the integers is proper over `Spec ℤ`, or over any terminal scheme.

## Main results

* `AlgebraicGeometry.Grassmannian.isProper_schemeOver`: `G(k, n)_S ⟶ S` is proper.
* `AlgebraicGeometry.Grassmannian.isProper_of_isTerminal`: every morphism from `G(k, n)` to a
  terminal scheme, such as `Spec ℤ`, is proper.

## Implementation notes

The Plücker morphism embeds `G(k, n)_S` as a closed subscheme of a projective space over `S`
(`AlgebraicGeometry.Grassmannian.isProjectiveMorphism_schemeOver`), and an H-projective
morphism is proper (`AlgebraicGeometry.isProper_of_isProjectiveMorphism`). Over a terminal
scheme `T` the structure morphism of `G(k, n)_T` is identified with the given morphism
`G(k, n) ⟶ T` through the second projection, which is an isomorphism. As for the Grassmannian
itself, no bound on `k` and `n` is needed.

## References

* [Stacks Project, Tag 089U](https://stacks.math.columbia.edu/tag/089U)
* [Stacks Project, Tag 089T](https://stacks.math.columbia.edu/tag/089T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Grassmannian

variable (k n : ℕ)

/-- **The Grassmannian `G(k, n)_S` is proper over `S`.** -/
theorem isProper_schemeOver (S : Scheme.{u}) : IsProper (schemeOver.over k n S).hom :=
  isProper_of_isProjectiveMorphism _ (isProjectiveMorphism_schemeOver k n S)

/-- **The Grassmannian `G(k, n)` over the integers is proper over any terminal scheme**, for
instance over `Spec ℤ`. -/
theorem isProper_of_isTerminal {T : Scheme.{u}} (hT : IsTerminal T)
    (f : scheme.{u} k n ⟶ T) : IsProper f := by
  have hS := isProper_schemeOver k n T
  have : IsIso (terminal.from T) := isIso_of_isTerminal hT terminalIsTerminal _
  have hf : f = inv (schemeOver.toIntegral k n T) ≫ (schemeOver.over k n T).hom :=
    hT.hom_ext _ _
  rw [hf]
  infer_instance

/-- The Grassmannian `G(k, n)` over the integers is proper over the terminal scheme. -/
instance isProper_terminalFrom : IsProper (terminal.from (scheme.{u} k n)) :=
  isProper_of_isTerminal k n terminalIsTerminal _

end AlgebraicGeometry.Grassmannian

end
