module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces

/-!
# The groupoid of sections of a groupoid in algebraic spaces

A *section* of a groupoid in algebraic spaces is a section `δ` of its source morphism: it
picks out, over every test scheme and functorially, an arrow emanating from each object. Two
sections compose: at an object `u` one follows `δ₂` to an arrow out of `u`, and then `δ₁` at
the target of that arrow, and composes the two arrows in the groupoid. In formulas this is
`δ₁ ∘ δ₂ = c(δ₁ ∘ t ∘ δ₂, δ₂)`, which is again a section of the source.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Section`: a section of the source morphism.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.sectionCompHom`: the morphism of algebraic
  spaces given by the composition formula.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.sectionComp`: composition of two sections.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.sectionCompHom_source`: the composition formula
  again satisfies the section condition, which is what makes `sectionComp` well defined.

## Implementation notes

The composition formula is built with the universal property of the chosen fibre product
`AlgebraicGeometry.AlgebraicSpaces.fiberProduct` of the source and the target morphisms, which
is the domain of the composition morphism carried by the structure. That the formula lands in
the sections is a pointwise statement: after evaluation at a test scheme, the formula produces
a composable pair whose composite has, by
`Deformation.PointwiseGroupoid.source_comp`, the source of its second entry, and the second
entry is `δ₂` applied to the object, whose source is the object again.

## References

* [Stacks Project, Tag 0CKC](https://stacks.math.columbia.edu/tag/0CKC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)

/-- A section of a groupoid in algebraic spaces: a morphism from the object space to the arrow
space which is a section of the source morphism, so that it assigns to every object an arrow
emanating from it. -/
abbrev Section := {δ : G.objects ⟶ G.arrows // δ ≫ G.source = 𝟙 G.objects}

/-- The morphism from the object space to the arrow space given by the groupoid composition
formula `c(δ₁ ∘ t ∘ δ₂, δ₂)` applied to two sections. -/
noncomputable def sectionCompHom (δ₁ δ₂ : Section G) : G.objects ⟶ G.arrows :=
  (ObjectProperty.homMk
    (pullback.lift (δ₂.1.hom ≫ G.target.hom ≫ δ₁.1.hom) δ₂.1.hom
      (by
        have h : δ₁.1.hom ≫ G.source.hom = 𝟙 G.objects.obj :=
          congrArg (fun f => f.hom) δ₁.2
        simp [Category.assoc, h])) :
      G.objects ⟶ AlgebraicSpaces.fiberProduct C S hS G.source G.target) ≫ G.comp

/-- The groupoid composition formula applied to two sections is again a section of the source
morphism. -/
@[stacks 0CKC "well-definedness of composition"]
theorem sectionCompHom_source (δ₁ δ₂ : Section G) :
    sectionCompHom G δ₁ δ₂ ≫ G.source = 𝟙 G.objects := by
  apply ObjectProperty.hom_ext
  ext T x
  have hsection : ∀ (δ : Section G) (T : (BigFppfOver C S hS)ᵒᵖ) (y : G.objects.obj.obj T),
      G.source.hom.app T (δ.1.hom.app T y) = y := fun δ T y =>
    congrArg (fun f => f.app T y) (congrArg (fun f => f.hom) δ.2)
  let q : G.objects.obj ⟶
      Deformation.composableArrows G.objects.obj G.arrows.obj G.source.hom G.target.hom :=
    { app := fun T => ↾ fun x => ⟨
        (δ₁.1.hom.app T (G.target.hom.app T (δ₂.1.hom.app T x)), δ₂.1.hom.app T x),
        by rw [hsection]⟩
      naturality := by
        intro X Y f
        ext x
        simp [Deformation.composableArrows] }
  have hpair : ∀ w, pullback.lift (δ₂.1.hom ≫ G.target.hom ≫ δ₁.1.hom) δ₂.1.hom w =
      q ≫ composableToPullback G.source.hom G.target.hom := by
    intro w
    apply pullback.hom_ext
    · simp only [pullback.lift_fst, Category.assoc, composableToPullback]
      ext T x
      rfl
    · simp only [pullback.lift_snd, Category.assoc, composableToPullback]
      ext T x
      rfl
  have happ : (sectionCompHom G δ₁ δ₂).hom.app T x =
      (composableToPullback G.source.hom G.target.hom ≫ G.comp.hom).app T (q.app T x) :=
    congrArg (fun f => G.comp.hom.app T (f.app T x)) (hpair _)
  change G.source.hom.app T ((sectionCompHom G δ₁ δ₂).hom.app T x) = x
  rw [happ]
  have hc := (Classical.choice (G.pointwiseGroupoid T)).source_comp
    (δ₁.1.hom.app T (G.target.hom.app T (δ₂.1.hom.app T x))) (δ₂.1.hom.app T x)
    (q.app T x).property
  change G.source.hom.app T
      ((composableToPullback G.source.hom G.target.hom ≫ G.comp.hom).app T
        (q.app T x)) = G.source.hom.app T (δ₂.1.hom.app T x) at hc
  rw [hc, hsection]

/-- Composition of sections of a groupoid in algebraic spaces: `δ₁ ∘ δ₂ = c(δ₁ ∘ t ∘ δ₂, δ₂)`,
which is again a section by `sectionCompHom_source`. -/
@[stacks 0CKC "composition formula"]
noncomputable def sectionComp (δ₁ δ₂ : Section G) : Section G :=
  ⟨sectionCompHom G δ₁ δ₂, sectionCompHom_source G δ₁ δ₂⟩

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
