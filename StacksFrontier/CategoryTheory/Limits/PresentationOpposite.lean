module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Presentation

/-!
# The legs of a colimit presentation, and colimit presentations in the opposite category

A `CategoryTheory.Limits.ColimitPresentation J X` exhibits `X` as the colimit of a diagram
indexed by `J`, and dually a `CategoryTheory.Limits.LimitPresentation J X` exhibits `X` as a
limit.  Two small facts about them are recorded here.

The first is the named leg `CategoryTheory.Limits.ColimitPresentation.leg`.  The structure field
`CategoryTheory.Limits.ColimitPresentation.ι` is a natural transformation into
`(CategoryTheory.Functor.const J).obj X`, so its component at `j` has codomain
`((CategoryTheory.Functor.const J).obj X).obj j` rather than `X`.  The two are definitionally
equal, but the unreduced form propagates into the implicit arguments of every projection and
composition built from a leg, and that is what makes downstream statements about the legs fail
to typecheck at ordinary transparency.  `CategoryTheory.Limits.ColimitPresentation.leg` performs
the reduction once, in its own type ascription, so that `X` is what later statements see.

The second is the direction of the limit/colimit duality that turns an ind-presentation of an
object into a pro-presentation of its image under a contravariant functor: a colimit
presentation of `X` over `J` is a limit presentation of `Opposite.op X` over `Jᵒᵖ`.

## Main definitions

* `CategoryTheory.Limits.ColimitPresentation.leg`
* `CategoryTheory.Limits.ColimitPresentation.op`

## Main results

* `CategoryTheory.Limits.ColimitPresentation.diag_map_comp_leg` and
  `CategoryTheory.Limits.ColimitPresentation.right_diag_map_comp_leg`: naturality of the legs,
  the latter in an under category and after forgetting the structure morphism.

## Implementation notes

For `CategoryTheory.Limits.ColimitPresentation.op`, Mathlib's
`CategoryTheory.Limits.Cocone.op` and `CategoryTheory.Limits.IsColimit.op` do the work; the only
content is that the cone they produce is already in the shape that
`CategoryTheory.Limits.LimitPresentation` asks for, so no transport along an isomorphism of
cones is needed.
-/

@[expose] public section

namespace CategoryTheory.Limits

universe t w v u

variable {C : Type u} [Category.{v} C] {J : Type w} [Category.{t} J] {X : C}

/-- The `j`-th leg of a colimit presentation, as a morphism with codomain `X`.  This is
`CategoryTheory.Limits.ColimitPresentation.ι` evaluated at `j`, whose codomain
`((CategoryTheory.Functor.const J).obj X).obj j` is reduced to `X` here once and for all. -/
def ColimitPresentation.leg (pres : ColimitPresentation J X) (j : J) : pres.diag.obj j ⟶ X :=
  pres.ι.app j

/-- The legs of a colimit presentation are compatible with the transition maps of its diagram:
`pres.diag.map f ≫ pres.leg j = pres.leg i` for `f : i ⟶ j`. -/
lemma ColimitPresentation.diag_map_comp_leg (pres : ColimitPresentation J X) {i j : J}
    (f : i ⟶ j) : pres.diag.map f ≫ pres.leg j = pres.leg i :=
  pres.w f

/-- The underlying morphisms of the legs of a colimit presentation in an under category compose
with the underlying morphisms of the diagram in the expected way. -/
lemma ColimitPresentation.right_diag_map_comp_leg {A : C} {Y : Under A}
    (pres : ColimitPresentation J Y) {i j : J} (f : i ⟶ j) :
    (pres.diag.map f).right ≫ (pres.leg j).right = (pres.leg i).right := by
  rw [← Under.comp_right, pres.diag_map_comp_leg]

/-- A colimit presentation of `X` over `J` is a limit presentation of `Opposite.op X`
over `Jᵒᵖ`. -/
def ColimitPresentation.op (pres : ColimitPresentation J X) :
    LimitPresentation Jᵒᵖ (Opposite.op X) where
  diag := pres.diag.op
  π := NatTrans.op pres.ι
  isLimit := pres.isColimit.op

/-- The diagram of `pres.op` is the opposite of the diagram of `pres`. -/
@[simp]
lemma ColimitPresentation.op_diag (pres : ColimitPresentation J X) :
    pres.op.diag = pres.diag.op :=
  rfl

/-- The component of the cone of `pres.op` at `j` is the opposite of the leg of `pres` at
`j.unop`. -/
@[simp]
lemma ColimitPresentation.op_π_app (pres : ColimitPresentation J X) (j : Jᵒᵖ) :
    pres.op.π.app j = (pres.leg j.unop).op :=
  rfl

end CategoryTheory.Limits

end
