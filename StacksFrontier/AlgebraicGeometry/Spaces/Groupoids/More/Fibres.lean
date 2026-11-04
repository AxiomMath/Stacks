module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.Diagrams

/-!
# Comparing the source fibres of a groupoid in algebraic spaces

Let `G` be a groupoid in algebraic spaces and let `r, r'` be two arrows over a test algebraic
space `X` with the same target. Then the fibre of the source morphism over the source of `r`
and the fibre over the source of `r'` are isomorphic over `X`: composing with the arrow
`r' ∘ r⁻¹` carries one to the other.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.sourceFibersIsoOfTargetEq`: **Stacks 0452**.

## Implementation notes

The test object is an arbitrary algebraic space, not only the spectrum of a field, and the
isomorphism is produced in the slice over it, so the statement records that the two fibres
agree *over* the test object and not merely as absolute algebraic spaces.

The arrow `q = r' ∘ r⁻¹` is extracted from the cartesian square
`Space.isPullback_fst_comp` of Stacks 04P9: `r` and `r'` have the same
target, so they are the first entry and the composite of a unique composable pair over `X`,
and `q` is its second entry. The two fibres are then both identified with the fibre product of
`X` with the space of composable pairs over the arrow space, pasting that fibre product with
the defining fibre-product square in one case and with the Stacks 043Z square
`AlgebraicGeometry.Space.isPullback_comp_source` in the other.

## References

* [Stacks Project, Tag 043Z](https://stacks.math.columbia.edu/tag/043Z)
* [Stacks Project, Tag 04P9](https://stacks.math.columbia.edu/tag/04P9)
* [Stacks Project, Tag 0452](https://stacks.math.columbia.edu/tag/0452)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

/-- **Stacks 0452.** Two arrows of a groupoid in algebraic spaces over a test algebraic space
`X` with the same target have isomorphic source fibres over `X`. -/
@[stacks 0452]
theorem sourceFibersIsoOfTargetEq (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS) (G : GroupoidInAlgebraicSpaces C S hS B)
    (X : AlgebraicSpaces C S hS) (r r' : X ⟶ G.arrows)
    (h : r ≫ G.target = r' ≫ G.target) :
    Nonempty
      ((Over.mk
          (ObjectProperty.homMk (pullback.fst (r ≫ G.source).hom G.source.hom) :
            AlgebraicSpaces.fiberProduct C S hS (r ≫ G.source) G.source ⟶ X) :
          Over X) ≅
       (Over.mk
          (ObjectProperty.homMk (pullback.fst (r' ≫ G.source).hom G.source.hom) :
            AlgebraicSpaces.fiberProduct C S hS (r' ≫ G.source) G.source ⟶ X) :
          Over X)) := by
  let P := AlgebraicSpaces.fiberProduct C S hS G.source G.target
  let p₀ : P ⟶ G.arrows := ObjectProperty.homMk (pullback.fst G.source.hom G.target.hom)
  let p₁ : P ⟶ G.arrows := ObjectProperty.homMk (pullback.snd G.source.hom G.target.hom)
  let hP := AlgebraicSpaces.isPullback_fiberProduct C S hS G.source G.target
  let ξ : X ⟶ P := (Space.isPullback_fst_comp G).lift r r' h
  have hξ₀ : ξ ≫ p₀ = r := by simp [ξ, p₀, P]
  have hξc : ξ ≫ G.comp = r' := by simp [ξ]
  let q : X ⟶ G.arrows := ξ ≫ p₁
  have hcomposable : r ≫ G.source = q ≫ G.target := by
    simpa [p₀, p₁, q, ← Category.assoc, hξ₀] using congrArg (fun f => ξ ≫ f) hP.w
  have hsource : q ≫ G.source = r' ≫ G.source := by
    simpa [p₁, q, ← Category.assoc, hξc] using
      (congrArg (fun f => ξ ≫ f) (Space.isPullback_comp_source G).w).symm
  let Q := AlgebraicSpaces.fiberProduct C S hS q p₁
  let q₀ : Q ⟶ X := ObjectProperty.homMk (pullback.fst q.hom p₁.hom)
  let q₁ : Q ⟶ P := ObjectProperty.homMk (pullback.snd q.hom p₁.hom)
  let hQ := AlgebraicSpaces.isPullback_fiberProduct C S hS q p₁
  have hpSquares : IsPullback p₀ p₁ G.source G.target := by simpa [P, p₀, p₁] using hP
  have key : ∀ (t : P ⟶ G.arrows) (m : G.arrows ⟶ G.objects) (a : X ⟶ G.arrows),
      IsPullback t p₁ G.source m → a ≫ G.source = q ≫ m →
        Nonempty ((Over.mk (ObjectProperty.homMk (pullback.fst (a ≫ G.source).hom G.source.hom) :
            AlgebraicSpaces.fiberProduct C S hS (a ≫ G.source) G.source ⟶ X) : Over X) ≅
          Over.mk q₀) := fun t m a hT ha => by
    have hC : IsPullback q₀ (q₁ ≫ t) (a ≫ G.source) G.source := by
      rw [ha]
      simpa [q₀, q₁, Q, q, Category.assoc] using IsPullback.paste_vert hQ hT.flip
    exact ⟨Over.isoMk (hC.isoIsPullback _ _
      (AlgebraicSpaces.isPullback_fiberProduct C S hS (a ≫ G.source) G.source)).symm
      (by simp [q₀])⟩
  obtain ⟨e₀⟩ := key p₀ G.target r hpSquares hcomposable
  obtain ⟨e₁⟩ := key G.comp G.source r' (by simpa [p₁] using Space.isPullback_comp_source G)
    hsource.symm
  exact ⟨e₀ ≪≫ e₁.symm⟩

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
