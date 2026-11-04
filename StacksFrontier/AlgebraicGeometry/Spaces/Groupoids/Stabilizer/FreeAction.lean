module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FreeAction
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.Action

/-!
# The stabilizer acts freely on the arrow space (Stacks 06QJ)

Let `G` be a groupoid in algebraic spaces over `B`, with object space `U` and arrow space `R`,
and let `S ⟶ U` be its stabilizer group algebraic space (**Stacks 0448**). **Stacks 0449** makes
`S` act on `R`, read over `U` through the target morphism, by groupoid composition
`(g, r) ↦ c(g, r)`. This file proves that this action is *free* in the sense of **Stacks 06P8**:
on the points of every scheme over `U` it cancels on both sides.

Freeness of exactly this action is the step of the proof of **Stacks 06QJ**, the implication
(2) `⟹` (1), that licenses forming the quotient `R/S` by **Stacks 06PH**.

## Main results

All of these live in the namespace `AlgebraicGeometry.GroupoidInAlgebraicSpaces`.

* `stabilizerSMul_left`: the action of the stabilizer on a generalized point of the arrow
  space, read on underlying arrows, is groupoid composition. This is `stabilizerAction`'s own
  characterization transported to the `•` notation of `CategoryTheory.Hom.instSMul`.
* `eq_of_groupoidCompose_right` and `eq_of_groupoidCompose_left`: composition of generalized
  arrows cancels on either side.
* `isFreeAction_stabilizer`: the action of **Stacks 0449** is free.

## Implementation notes

The two cancellation statements are proved for generalized arrows rather than for points of a
test object: a composable pair of morphisms into the arrow space has an inverse by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.groupoidInverse`, and the two cancellations are
then the two associativity-and-inverse computations, with the identity arrow produced in the
form `identityAfterTarget` on one side and `identityAfterSource` on the other — the two agree
precisely because the pair is composable, which is what each proof's `hid` records.

`AlgebraicGeometry.Space.IsFreeAction` quantifies over the points of the objects `Over.mk b` of
the slice over the object space presheaf whose source is representable, so the cancellation is
needed only there; it is proved for an arbitrary object of the slice, since nothing in the
argument sees the test object. The passage from an equality of generalized arrows back to an
equality of generalized points of the stabilizer is
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizer_hom_ext`, and the one for the arrow
space over the object space is `CategoryTheory.Over.OverMorphism.ext`, both ends of a
generalized point of either being determined by the underlying arrow.

## References

* [Stacks Project, Tag 0447](https://stacks.math.columbia.edu/tag/0447)
* [Stacks Project, Tag 0448](https://stacks.math.columbia.edu/tag/0448)
* [Stacks Project, Tag 0449](https://stacks.math.columbia.edu/tag/0449)
* [Stacks Project, Tag 06P8](https://stacks.math.columbia.edu/tag/06P8)
* [Stacks Project, Tag 06PH](https://stacks.math.columbia.edu/tag/06PH)
* [Stacks Project, Tag 06QJ](https://stacks.math.columbia.edu/tag/06QJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory MonoidalCategory MonObj

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- The action of **Stacks 0449** of the stabilizer on the arrow space over the object space,
read on underlying arrows: it is groupoid composition. -/
theorem stabilizerSMul_left (G : GroupoidInAlgebraicSpaces C S hS B) {T : Over G.objects.obj}
    (g : T ⟶ stabilizer G) (r : T ⟶ arrowsOverTarget G) :
    (g • r).left = groupoidCompose G (stabilizerArrowHom G g) r.left
      (stabilizerArrowHom_arrowOverTarget_composable G g r) := by
  obtain ⟨w, hw⟩ := (stabilizerAction G).2 T g r
  show (lift g r ≫ γ[stabilizer G, arrowsOverTarget G]).left = _
  rw [hw]
  rfl

/-- **Composition of generalized arrows cancels on the right.** Two generalized arrows of a
groupoid in algebraic spaces which are composable before a third one and whose composites with
it agree are equal: compose with the inverse of the third. -/
theorem eq_of_groupoidCompose_right (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} {x y r : T ⟶ G.arrows.obj}
    (wx : x ≫ G.source.hom = r ≫ G.target.hom)
    (wy : y ≫ G.source.hom = r ≫ G.target.hom)
    (h : groupoidCompose G x r wx = groupoidCompose G y r wy) : x = y := by
  have wri : r ≫ G.source.hom = (r ≫ groupoidInverse G) ≫ G.target.hom := by
    rw [Category.assoc, groupoidInverse_target]
  have wL : ∀ (z : T ⟶ G.arrows.obj) (wz : z ≫ G.source.hom = r ≫ G.target.hom),
      groupoidCompose G z r wz ≫ G.source.hom = (r ≫ groupoidInverse G) ≫ G.target.hom := by
    intro z wz
    rwa [groupoidCompose_source]
  have key : ∀ (z : T ⟶ G.arrows.obj) (wz : z ≫ G.source.hom = r ≫ G.target.hom),
      groupoidCompose G (groupoidCompose G z r wz) (r ≫ groupoidInverse G) (wL z wz) = z := by
    intro z wz
    have wR : z ≫ G.source.hom =
        groupoidCompose G r (r ≫ groupoidInverse G) wri ≫ G.target.hom := by
      rwa [groupoidCompose_target]
    have hid : identityAfterTarget G r = identityAfterSource G z := by
      show r ≫ G.target.hom ≫ (identityArrow G).hom =
        z ≫ G.source.hom ≫ (identityArrow G).hom
      rw [← Category.assoc, ← Category.assoc, ← wz]
    calc groupoidCompose G (groupoidCompose G z r wz) (r ≫ groupoidInverse G) (wL z wz)
        = groupoidCompose G z (groupoidCompose G r (r ≫ groupoidInverse G) wri) wR :=
          groupoidCompose_assoc G z r (r ≫ groupoidInverse G) wz wri (wL z wz) wR
      _ = groupoidCompose G z (identityAfterSource G z)
            (identityAfterSource_composable G z) :=
          groupoidCompose_congr G _ _ rfl ((groupoidCompose_inverseLeft G r).trans hid)
      _ = z := groupoidCompose_rightIdentity G z
  calc x = groupoidCompose G (groupoidCompose G x r wx) (r ≫ groupoidInverse G) (wL x wx) :=
        (key x wx).symm
    _ = groupoidCompose G (groupoidCompose G y r wy) (r ≫ groupoidInverse G) (wL y wy) :=
        groupoidCompose_congr G _ _ h rfl
    _ = y := key y wy

/-- **Composition of generalized arrows cancels on the left.** Two generalized arrows of a
groupoid in algebraic spaces before which a third one is composable and whose composites with it
agree are equal: compose with the inverse of the third. -/
theorem eq_of_groupoidCompose_left (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} {x r₁ r₂ : T ⟶ G.arrows.obj}
    (w₁ : x ≫ G.source.hom = r₁ ≫ G.target.hom)
    (w₂ : x ≫ G.source.hom = r₂ ≫ G.target.hom)
    (h : groupoidCompose G x r₁ w₁ = groupoidCompose G x r₂ w₂) : r₁ = r₂ := by
  have wxi : (x ≫ groupoidInverse G) ≫ G.source.hom = x ≫ G.target.hom := by
    rw [Category.assoc, groupoidInverse_source]
  have wR : ∀ (z : T ⟶ G.arrows.obj) (wz : x ≫ G.source.hom = z ≫ G.target.hom),
      (x ≫ groupoidInverse G) ≫ G.source.hom = groupoidCompose G x z wz ≫ G.target.hom := by
    intro z wz
    rwa [groupoidCompose_target]
  have key : ∀ (z : T ⟶ G.arrows.obj) (wz : x ≫ G.source.hom = z ≫ G.target.hom),
      groupoidCompose G (x ≫ groupoidInverse G) (groupoidCompose G x z wz) (wR z wz) = z := by
    intro z wz
    have wL : groupoidCompose G (x ≫ groupoidInverse G) x wxi ≫ G.source.hom =
        z ≫ G.target.hom := by
      rwa [groupoidCompose_source]
    have hid : identityAfterSource G x = identityAfterTarget G z := by
      show x ≫ G.source.hom ≫ (identityArrow G).hom =
        z ≫ G.target.hom ≫ (identityArrow G).hom
      rw [← Category.assoc, ← Category.assoc, wz]
    calc groupoidCompose G (x ≫ groupoidInverse G) (groupoidCompose G x z wz) (wR z wz)
        = groupoidCompose G (groupoidCompose G (x ≫ groupoidInverse G) x wxi) z wL :=
          (groupoidCompose_assoc G (x ≫ groupoidInverse G) x z wxi wz wL (wR z wz)).symm
      _ = groupoidCompose G (identityAfterTarget G z) z
            (identityAfterTarget_composable G z) :=
          groupoidCompose_congr G _ _ ((groupoidCompose_inverseRight G x).trans hid) rfl
      _ = z := groupoidCompose_leftIdentity G z
  calc r₁ = groupoidCompose G (x ≫ groupoidInverse G) (groupoidCompose G x r₁ w₁) (wR r₁ w₁) :=
        (key r₁ w₁).symm
    _ = groupoidCompose G (x ≫ groupoidInverse G) (groupoidCompose G x r₂ w₂) (wR r₂ w₂) :=
        groupoidCompose_congr G _ _ rfl h
    _ = r₂ := key r₂ w₂

/-- **Stacks 06QJ, the freeness step of the implication (2) `⟹` (1).** The action of
**Stacks 0449** of the stabilizer group algebraic space of a groupoid in algebraic spaces on its
arrow space, read over the object space through the target morphism, is free in the sense of
**Stacks 06P8**.

On generalized points the action is groupoid composition, so both cancellations are cancellation
of a composable pair of generalized arrows. -/
theorem isFreeAction_stabilizer (G : GroupoidInAlgebraicSpaces C S hS B) :
    Space.IsFreeAction C S hS G.objects.obj (stabilizer G) (arrowsOverTarget G) := by
  intro T b
  have hleft : ∀ (g : (Over.mk b : Over G.objects.obj) ⟶ stabilizer G)
      (r r' : (Over.mk b : Over G.objects.obj) ⟶ arrowsOverTarget G),
      g • r = g • r' → r = r' := by
    intro g r r' h
    refine Over.OverMorphism.ext (eq_of_groupoidCompose_left G
      (stabilizerArrowHom_arrowOverTarget_composable G g r)
      (stabilizerArrowHom_arrowOverTarget_composable G g r') ?_)
    rw [← stabilizerSMul_left G g r, ← stabilizerSMul_left G g r', h]
  have hright : ∀ (g g' : (Over.mk b : Over G.objects.obj) ⟶ stabilizer G)
      (r : (Over.mk b : Over G.objects.obj) ⟶ arrowsOverTarget G),
      g • r = g' • r → g = g' := by
    intro g g' r h
    refine stabilizer_hom_ext G g g' (eq_of_groupoidCompose_right G
      (stabilizerArrowHom_arrowOverTarget_composable G g r)
      (stabilizerArrowHom_arrowOverTarget_composable G g' r) ?_)
    rw [← stabilizerSMul_left G g r, ← stabilizerSMul_left G g' r, h]
  exact { toIsLeftCancelSMul := ⟨hleft⟩, right_cancel' := hright }

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
