module

public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.BaseChangeQuotientStackDiagram
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsOfPullback

/-!
# The evaluated functors of a base-change morphism of groupoids are faithful

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `X` and let
`g : X' ⟶ X` be a morphism of algebraic spaces. The base change of Stacks 0DTA has
`U' = X' ×_X U` and `R' = X' ×_X R`, and its projection to `G` is **not** a monomorphism on
arrow spaces. It is nevertheless injective on the arrows of each evaluated groupoid, because an
arrow of the evaluated groupoid of the base change has a prescribed source, and the `X'`-component
of a `T`-point of `R'` is the `X'`-component of its source.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.evaluation_faithful_of_source_injective`: the
  evaluated functors of a morphism of groupoids in algebraic spaces are faithful as soon as the
  map on arrow spaces is injective on `T`-points with a prescribed source.
* `AlgebraicGeometry.Space.baseChange_arrows_injective`: for the base change of Stacks 0DTA, a
  `T`-point of the arrow space is determined by its image in the arrow space of the original
  groupoid together with the source of its image in the object space.
* `AlgebraicGeometry.Stack.evaluation_faithful_invariantBaseChangeGroupoidHom`: the evaluated
  functors of the morphism of groupoids of the Stacks 0DTG diagram are faithful.

## Implementation notes

The injectivity statement is the joint injectivity of the two projections of the cartesian square
on arrow spaces recorded by `AlgebraicGeometry.Space.BaseChange`
(`AlgebraicGeometry.Space.section_eq_of_isPullback`, Stacks 02X2 on sections), combined with the
groupoid axiom `source_over`, which says that the structure morphism of the arrow space to the
base is the source map followed by the structure morphism of the object space. Two `T`-points of
`R'` with the same source therefore have the same `X'`-component, and the cartesian square then
identifies them as soon as their images in `R` agree.

Faithfulness of the evaluated functor is read off
`Deformation.GroupoidInFunctors.evaluationArrowEquiv`, whose subtype condition supplies the
equality of the sources, and `Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow`, which
says that the arrow underlying the image of an arrow is the image of the arrow underlying it.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 048G](https://stacks.math.columbia.edu/tag/048G)
* [Stacks Project, Tag 0DTA](https://stacks.math.columbia.edu/tag/0DTA)
* [Stacks Project, Tag 0DTG](https://stacks.math.columbia.edu/tag/0DTG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

namespace GroupoidInAlgebraicSpaces

/-- **The evaluated functors of a morphism of groupoids in algebraic spaces are faithful once its
map on arrow spaces is injective on `T`-points with a prescribed source.** An arrow of an
evaluated groupoid is a `T`-point of the arrow space with prescribed source and target, so two
parallel arrows have equal sources; if their images in the arrow space of the target agree, the
hypothesis identifies them. -/
theorem evaluation_faithful_of_source_injective {B : AlgebraicSpaces C S hS}
    {G H : GroupoidInAlgebraicSpaces C S hS B} (φ : GroupoidInAlgebraicSpaces.Hom G H)
    (hinj : ∀ (T : (BigFppfOver C S hS)ᵒᵖ) (a b : G.arrows.obj.obj T),
      φ.toGroupoidHom.mapArrows.app T a = φ.toGroupoidHom.mapArrows.app T b →
      G.source.hom.app T a = G.source.hom.app T b → a = b)
    (T : (BigFppfOver C S hS)ᵒᵖ) :
    (φ.toGroupoidHom.evaluation T).Faithful := by
  constructor
  intro x y m n hmn
  refine (G.toGroupoidInFunctors.evaluationArrowEquiv T x y).injective (Subtype.ext ?_)
  have hm := congrArg
    (fun k : (φ.toGroupoidHom.evaluation T).obj x ⟶ (φ.toGroupoidHom.evaluation T).obj y =>
      (H.toGroupoidInFunctors.evaluationArrowEquiv T _ _ k).1) hmn
  rw [Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow,
    Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow] at hm
  exact hinj T _ _ hm
    (((G.toGroupoidInFunctors.evaluationArrowEquiv T x y m).2.1).trans
      ((G.toGroupoidInFunctors.evaluationArrowEquiv T x y n).2.1).symm)

end GroupoidInAlgebraicSpaces

namespace Space

/-- **A `T`-point of the arrow space of a base change is determined by its image in the original
arrow space together with its source.** The square on arrow spaces is cartesian, so a `T`-point
of `R'` is determined by its image in `R` and its `X'`-component; and the `X'`-component is the
`X'`-component of its source, by the groupoid axiom `source_over`. -/
theorem baseChange_arrows_injective {X X' : AlgebraicSpaces C S hS}
    (H : GroupoidInAlgebraicSpaces C S hS X) (g : X' ⟶ X)
    (T : BigFppfOver C S hS) (a b : (Space.baseChange H g).groupoid.arrows.obj.obj (op T))
    (harr : (Space.baseChange H g).projection.mapArrows.app (op T) a =
      (Space.baseChange H g).projection.mapArrows.app (op T) b)
    (hsrc : (Space.baseChange H g).groupoid.source.hom.app (op T) a =
      (Space.baseChange H g).groupoid.source.hom.app (op T) b) :
    a = b := by
  have hover : ∀ c : (Space.baseChange H g).groupoid.arrows.obj.obj (op T),
      (Space.baseChange H g).groupoid.arrowsToBase.hom.app (op T) c
        = (Space.baseChange H g).groupoid.objectsToBase.hom.app (op T)
            ((Space.baseChange H g).groupoid.source.hom.app (op T) c) := fun c => by
    simpa using (congrArg
      (fun k : (Space.baseChange H g).groupoid.arrows ⟶ X' => k.hom.app (op T) c)
      (Space.baseChange H g).groupoid.source_over).symm
  exact Space.section_eq_of_isPullback C S hS (Space.baseChange H g).arrows_isPullback a b
    harr (by rw [hover a, hover b, hsrc])

end Space

namespace Stack

variable {B : AlgebraicSpaces C S hS}

/-- **The evaluated functors of the morphism of groupoids of the Stacks 0DTG diagram are
faithful.** -/
theorem evaluation_faithful_invariantBaseChangeGroupoidHom
    (G : GroupoidInAlgebraicSpaces C S hS B) {X X' : AlgebraicSpaces C S hS}
    (XtoB : X ⟶ B) (X'toB : X' ⟶ B) (g : X' ⟶ X) (hg : g ≫ XtoB = X'toB)
    (φ : G.objects ⟶ X) (hφB : φ ≫ XtoB = G.objectsToBase)
    (hφ : Space.IsInvariant (Space.groupoidPreRelation G) φ.hom)
    (T : (BigFppfOver C S hS)ᵒᵖ) :
    ((invariantBaseChangeGroupoidHom (G := G) (XtoB := XtoB) (X'toB := X'toB)
      (g := g) (hg := hg) (φ := φ) (hφB := hφB) (hφ := hφ)).toGroupoidHom.evaluation T).Faithful :=
  GroupoidInAlgebraicSpaces.evaluation_faithful_of_source_injective
    (invariantBaseChangeGroupoidHom (G := G) (XtoB := XtoB) (X'toB := X'toB)
      (g := g) (hg := hg) (φ := φ) (hφB := hφB) (hφ := hφ))
    (fun T => Space.baseChange_arrows_injective (invariantTargetGroupoid G XtoB φ hφB hφ) g
      T.unop) T

end Stack

end AlgebraicGeometry

end
