module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjectiveDiagonal

/-!
# A surjective 1-morphism with a retraction is a homeomorphism on points

Let `s : 𝒳 ⟶ 𝒵` be a 1-morphism of algebraic stacks over `S` which is surjective and which
admits a retraction, that is a 1-morphism `r : 𝒵 ⟶ 𝒳` with `s ≫ r = 𝟙 𝒳`. Then `|s|` is a
homeomorphism, with inverse `|r|`: it is injective because `|r|` undoes it, surjective by
hypothesis, and its inverse `|r|` is continuous by **Stacks 04XL**. In particular `s` is closed
and open in the sense of **Stacks 0513**, part (1).

This is the exact strength of the step "since the composition of `Δ` with the projection
`𝒳 ×_𝒴 𝒳 ⟶ 𝒳` is the identity, we see that `Δ` is universally closed" in the published proof of
**Stacks 0CPQ**. A retraction gives closedness of `s` itself, and nothing more: universal
closedness is closedness of *every* base change (**Stacks 0512**,
`AlgebraicGeometry.Stack.representable_universallyClosed_iff_closedMap_baseChange`), and a
retraction of `s` is not a retraction of the base change of `s` along a 1-morphism to `𝒵`.
For the relative diagonal the two differ: closedness is
`AlgebraicGeometry.Stack.AlgebraicStacks.isClosed_relativeDiagonal_of_universallyInjective`
below, proved from universal injectivity alone, while universal closedness of `Δ_f` is the
hypothesis `hdiagUC` of
`AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_of_isSeparated_comp_of_universallyInjective`
in `StacksFrontier/AlgebraicGeometry/Stacks/SeparationUniversallyInjectiveCover.lean`.

What repairs the step for algebraic spaces is that the relative diagonal is a monomorphism
there. For a 1-morphism of algebraic stacks that holds when the 1-morphism is representable by
algebraic spaces — part (3) of **Stacks 04YQ**,
`AlgebraicGeometry.Stack.mono_relativeDiagonal_of_isRepresentableByAlgebraicSpaces` — which by
**Stacks 04Y5** is faithfulness, and faithfulness is not among the hypotheses of Stacks 0CPQ.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isHomeomorph_pointsMap_of_isSurjective_of_retraction`:
  a surjective 1-morphism with a retraction is a homeomorphism on the points of Stacks 04XL.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isClosed_of_isSurjective_of_retraction`: such a
  1-morphism is closed in the sense of Stacks 0513, part (1).
* `AlgebraicGeometry.Stack.AlgebraicStacks.isClosed_relativeDiagonal_of_universallyInjective`:
  the relative diagonal of a universally injective 1-morphism of algebraic stacks is closed.

## References

* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 04Y5](https://stacks.math.columbia.edu/tag/04Y5)
* [Stacks Project, Tag 04YQ](https://stacks.math.columbia.edu/tag/04YQ)
* [Stacks Project, Tag 0512](https://stacks.math.columbia.edu/tag/0512)
* [Stacks Project, Tag 0513](https://stacks.math.columbia.edu/tag/0513)
* [Stacks Project, Tag 0CPN](https://stacks.math.columbia.edu/tag/0CPN)
* [Stacks Project, Tag 0CPQ](https://stacks.math.columbia.edu/tag/0CPQ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- The map on points of a retraction undoes the map on points of the 1-morphism it retracts. -/
theorem leftInverse_pointsMap_of_comp_eq_id (s : 𝒳 ⟶ 𝒵) (r : 𝒵 ⟶ 𝒳) (hsr : s ≫ r = 𝟙 𝒳) :
    Function.LeftInverse (pointsMap B S hS r) (pointsMap B S hS s) := by
  have h : pointsMap B S hS (s ≫ r) = pointsMap B S hS (𝟙 𝒳) := by rw [hsr]
  rw [pointsMap_comp, pointsMap_id] at h
  exact congrFun h

/-- The image of a set under a surjective 1-morphism with a retraction is the preimage of that
set under the retraction. -/
theorem image_pointsMap_eq_preimage (s : 𝒳 ⟶ 𝒵) (r : 𝒵 ⟶ 𝒳) (hsr : s ≫ r = 𝟙 𝒳)
    (hs : Stack.IsSurjective B S hS s) (C : Set (points B S hS 𝒳)) :
    pointsMap B S hS s '' C = pointsMap B S hS r ⁻¹' C := by
  have hli := leftInverse_pointsMap_of_comp_eq_id B S hS s r hsr
  ext z
  refine ⟨?_, fun hz => ?_⟩
  · rintro ⟨x, hx, rfl⟩
    rwa [Set.mem_preimage, hli x]
  · obtain ⟨x, rfl⟩ := hs z
    rw [Set.mem_preimage, hli x] at hz
    exact ⟨x, hz, rfl⟩

/-- **A surjective 1-morphism of algebraic stacks over `S` which admits a retraction is a
homeomorphism on points.** The map on points of the retraction undoes it, so it is injective;
it is surjective by hypothesis; and both it and its inverse are continuous by Stacks 04XL. -/
theorem isHomeomorph_pointsMap_of_isSurjective_of_retraction (s : 𝒳 ⟶ 𝒵) (r : 𝒵 ⟶ 𝒳)
    (hsr : s ≫ r = 𝟙 𝒳) (hs : Stack.IsSurjective B S hS s) :
    @IsHomeomorph _ _ (Stack.pointTopology B S hS 𝒳.val) (Stack.pointTopology B S hS 𝒵.val)
      (pointsMap B S hS s) := by
  let _ := Stack.pointTopology B S hS 𝒳.val
  let _ := Stack.pointTopology B S hS 𝒵.val
  refine ⟨Stack.continuous_pointsMap B S hS 𝒳.val 𝒵.val s.hom.hom, fun U hU => ?_,
    (leftInverse_pointsMap_of_comp_eq_id B S hS s r hsr).injective, hs⟩
  rw [image_pointsMap_eq_preimage B S hS s r hsr hs]
  exact hU.preimage (Stack.continuous_pointsMap B S hS 𝒵.val 𝒳.val r.hom.hom)

/-- **A surjective 1-morphism of algebraic stacks over `S` which admits a retraction is
closed**, in the sense of Stacks 0513 part (1): it is a homeomorphism on points.

It is *not* universally closed on that account: the retraction is lost on base change, and
universal closedness asks for closedness of every base change. -/
theorem isClosed_of_isSurjective_of_retraction (s : 𝒳 ⟶ 𝒵) (r : 𝒵 ⟶ 𝒳) (hsr : s ≫ r = 𝟙 𝒳)
    (hs : Stack.IsSurjective B S hS s) :
    IsClosed B S hS s := by
  let _ := Stack.pointTopology B S hS 𝒳.val
  let _ := Stack.pointTopology B S hS 𝒵.val
  exact (isHomeomorph_pointsMap_of_isSurjective_of_retraction B S hS s r hsr hs).isClosedMap

/-- **The relative diagonal of a universally injective 1-morphism of algebraic stacks is
closed.** It is surjective by **Stacks 0CPN**, and the first projection of `𝒳 ×_𝒴 𝒳` retracts
it, so `AlgebraicGeometry.Stack.AlgebraicStacks.isClosed_of_isSurjective_of_retraction`
applies.

This is the step the published proof of **Stacks 0CPQ** takes; what it yields is closedness of
`Δ_f`, not universal closedness. -/
theorem isClosed_relativeDiagonal_of_universallyInjective (f : 𝒳 ⟶ 𝒴)
    (hf : Stack.UniversallyInjective B S hS f) :
    IsClosed B S hS (relativeDiagonal B S hS f) :=
  isClosed_of_isSurjective_of_retraction B S hS (relativeDiagonal B S hS f)
    (twoFibreProductSquare B S hS f f).fst (relativeDiagonal_comp_fst B S hS f)
    (Stack.isSurjective_relativeDiagonal_of_universallyInjective B S hS f hf)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
