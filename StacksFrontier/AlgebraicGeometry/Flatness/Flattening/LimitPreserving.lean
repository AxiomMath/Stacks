module

public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.CategoryTheory.Limits.Over
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Limit-preserving presheaves on the big fppf site

A presheaf of sets is locally of finite presentation when it sends cofiltered inverse limits
of affine schemes to filtered colimits of sets. A transformation of presheaves has this
property relatively when, for every section of the target, the presheaf of its lifts is
itself limit preserving.

## Main definitions

* `AlgebraicGeometry.LimitPreserving` is local finite presentation for a presheaf.
* `AlgebraicGeometry.sectionFiber` is the presheaf of lifts of a section of the target.
* `AlgebraicGeometry.RelativelyLimitPreserving` is relative local finite presentation.

## Implementation notes

The functor to schemes is an explicit argument, so that the same limit-preservation notion
applies both to a big fppf slice and to the further slice on which a section fibre lives.
The fibre is a subtype of sections, with restriction induced by the source presheaf; clients
can therefore apply the first definition directly to each fibre, with no comparison lemma.
Each tested scheme-limit cone is sent to a colimit cocone, and the underlying-scheme functor
is not assumed to reflect limits in the chosen size-bounded site. The object universe of the
indexing category includes its morphism universe, so passage to a cofiltered slice keeps the
same indexing size.

## References

* [Stacks Project, Tag 049J](https://stacks.math.columbia.edu/tag/049J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w w' z

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 049J.** A presheaf of sets preserves inverse limits of affine
schemes as filtered colimits of sets, relative to its underlying-scheme functor. -/
@[stacks 049J "part (1)", sga "3 XI 3.2" "definition of (*)"]
abbrev LimitPreserving {C : Type z} [Category C]
    (toScheme : C ⥤ Scheme.{u}) (F : Cᵒᵖ ⥤ Type v) : Prop :=
  ∀ (I : Type (max w w')) [Category.{w'} I] [IsCofiltered I] (D : I ⥤ C) (c : Cone D),
    IsLimit (toScheme.mapCone c) → (∀ i, IsAffine (toScheme.obj (D.obj i))) →
      IsAffine (toScheme.obj c.pt) → Nonempty (IsColimit (F.mapCocone c.op))

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The presheaf of lifts through `a` of a section `y` over `X`, on schemes over `X`. -/
@[implicit_reducible]
def sectionFiber
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}
    (a : F ⟶ G) (X : BigFppfOver B S hS)
    (y : G.obj (Opposite.op X)) : (Over X)ᵒᵖ ⥤ Type v where
  obj Y := {x : F.obj (Opposite.op Y.unop.left) //
    a.app (Opposite.op Y.unop.left) x = G.map Y.unop.hom.op y}
  map {Y Z} f := TypeCat.ofHom (fun x => ⟨F.map f.unop.left.op x.1, by
    change (F.map f.unop.left.op ≫ a.app (Opposite.op Z.unop.left)) x.1 = _
    rw [a.naturality f.unop.left.op]
    change G.map f.unop.left.op (a.app (Opposite.op Y.unop.left) x.1) = _
    rw [x.2]
    change (G.map Y.unop.hom.op ≫ G.map f.unop.left.op) y = _
    rw [← G.map_comp, ← op_comp, f.unop.w]⟩)
  map_id _ := by ext x; simp
  map_comp _ _ := by ext x; simp

/-- **Stacks Project, Tag 049J.** A transformation is relatively limit preserving when the
presheaf of lifts of every target section is limit preserving over that section's base. -/
@[stacks 049J "part (2)"]
abbrev RelativelyLimitPreserving
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}
    (a : F ⟶ G) : Prop :=
  ∀ (X : BigFppfOver B S hS) (y : G.obj (Opposite.op X)),
    LimitPreserving.{u, v, w, w', u + 1, u}
      (Over.forget X ⋙ BigFppfOver.toScheme B S hS)
      (sectionFiber B S hS a X y)

end AlgebraicGeometry
