module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreserving

/-!
# The fibre of a transformation over a section as a fibre product of presheaves

Let `F, G` be presheaves of sets on the big fppf site over a scheme `S`, let `a : F ⟶ G` be a
transformation, let `X` be an object of that site and let `y` be a section of `G` over `X`. The
presheaf `AlgebraicGeometry.sectionFiber` of lifts of `y` through `a` is a presheaf on the big
fppf site over `X`, namely

```text
  F_y(X' → X)  =  { x ∈ F(X') | a(x) = y|_{X'} } .
```

This file identifies it there: writing `j : (Sch/X)_fppf ⥤ (Sch/S)_fppf` for the localization
functor and `j^{-1}` for restriction along it, the square

```text
  F_y  --------ι------->  j^{-1}F
   |                         |
   v                         v  j^{-1}a
   *   ---- y|_(-) ----->  j^{-1}G
```

is cartesian, so that `F_y = j^{-1}F ×_{j^{-1}G} *`, where `*` is the final presheaf on the big
fppf site over `X` and the bottom edge is the point of `j^{-1}G` named by `y`.

## Main definitions

* `AlgebraicGeometry.sectionFiberι`: the inclusion of the fibre into `j^{-1}F`.
* `AlgebraicGeometry.sectionFiberToFinal`: the structural morphism of the fibre to the final
  presheaf.
* `AlgebraicGeometry.pointOfSection`: the point of `j^{-1}G` named by `y`, the family of
  restrictions of `y` along the structure morphisms of the objects of `(Sch/X)_fppf`.

## Main results

* `AlgebraicGeometry.isPullback_sectionFiberι`: the square above is cartesian.

## Implementation notes

The final presheaf is realized as the constant presheaf with value `PUnit`; it is terminal by
`CategoryTheory.Functor.isTerminalConst` together with
`CategoryTheory.Limits.Types.isTerminalPUnit`. Taking this model rather than the representable
presheaf of the terminal object `X → X` of `(Sch/X)_fppf` keeps the universe of the values of the
presheaves independent of the universe of the morphisms of the site, which is what the
surrounding development uses: a section of the constant presheaf carries no information, whereas
a morphism to `X` over `X` lives in the morphism universe of the site.

Since fibre products of presheaves are computed sectionwise, the square is cartesian as soon as
it is so over every object of `(Sch/X)_fppf`, which is
`CategoryTheory.IsPullback.of_forall_isPullback_app`. Over an object `X' → X` all three clauses of
`CategoryTheory.Limits.Types.isPullback_iff` are immediate from the definition of the fibre:
commutativity and joint surjectivity are its defining equation, and joint injectivity is
`Subtype.ext`, the component in the final factor carrying no information.

## References

* [Stacks Project, Tag 049J](https://stacks.math.columbia.edu/tag/049J)
* [Stacks Project, Tag 049K](https://stacks.math.columbia.edu/tag/049K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The point of `j^{-1}G` named by a section `y` of `G` over `X`**, where `j^{-1}` is
restriction along the localization functor `j : (Sch/X)_fppf ⥤ (Sch/S)_fppf`: over an object
`X' → X` it is the restriction `y|_{X'}` of `y` along the structure morphism of `X'`. Its source
is the final presheaf, so it carries no information beyond that family of sections. -/
def pointOfSection (G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v) (X : BigFppfOver B S hS)
    (y : G.obj (op X)) :
    (Functor.const (Over X)ᵒᵖ).obj PUnit.{v + 1} ⟶ (Over.forget X).op ⋙ G where
  app W := ↾fun _ => G.map (unop W).hom.op y
  naturality W W' g := by
    ext _
    change G.map (unop W').hom.op y = G.map (unop g).left.op (G.map (unop W).hom.op y)
    rw [← G.map_comp_apply, ← op_comp, Over.w (unop g)]

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v} (a : F ⟶ G) (X : BigFppfOver B S hS)
  (y : G.obj (op X))

/-- The inclusion of the presheaf of lifts of `y` through `a` into the restriction of `F` to the
big fppf site over `X`: it forgets that a lift lifts `y`. -/
def sectionFiberι : sectionFiber B S hS a X y ⟶ (Over.forget X).op ⋙ F where
  app _ := ↾fun x => x.1
  naturality _ _ _ := rfl

/-- The structural morphism of the presheaf of lifts of `y` through `a` to the final presheaf on
the big fppf site over `X`. It is the unique such morphism. -/
def sectionFiberToFinal :
    sectionFiber B S hS a X y ⟶ (Functor.const (Over X)ᵒᵖ).obj PUnit.{v + 1} where
  app _ := ↾fun _ => PUnit.unit
  naturality _ _ _ := rfl

/-- **Stacks Project, Tag 049K.** The presheaf of lifts of a section `y` of `G` over `X` through
a transformation `a : F ⟶ G` of presheaves of sets on the big fppf site over `S` is the fibre
product

```text
  F_y = F|_{(Sch/X)_fppf} ×_{G|_{(Sch/X)_fppf}} *
```

of presheaves on the big fppf site over `X`, where `*` is the final presheaf and the morphism
`* ⟶ G|_{(Sch/X)_fppf}` is the point named by `y`. That is, the inclusion of the fibre into the
restriction of `F` along the localization functor and its structural morphism to the final
presheaf exhibit it as the fibre product of the restriction of `a` and of that point. -/
@[stacks 049K]
theorem isPullback_sectionFiberι :
    IsPullback (sectionFiberι B S hS a X y) (sectionFiberToFinal B S hS a X y)
      (Functor.whiskerLeft (Over.forget X).op a) (pointOfSection B S hS G X y) := by
  apply IsPullback.of_forall_isPullback_app
  intro W
  rw [Limits.Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext x
    exact x.2
  · rintro x x' ⟨h, -⟩
    exact Subtype.ext h
  · intro x _ hx
    exact ⟨⟨x, hx⟩, rfl, Subsingleton.elim (α := PUnit.{v + 1}) _ _⟩

end AlgebraicGeometry

end
