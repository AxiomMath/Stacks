module

public import StacksFrontier.AlgebraicGeometry.Duality.GlueingDualizingComplexes
public import StacksFrontier.AlgebraicGeometry.Duality.StandardModelMonoidalClosed
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekDuality
public import StacksFrontier.CategoryTheory.Monoidal.DualConjugatePseudofunctor

/-!
# `f_new^!` at the standard model of the derived category

`Stacks.Duality.fNewShriek` is the formula `f_new^! = D_X ∘ Lf^* ∘ D_Y` of [Stacks, Tag 0AUE]
part (5), over a closed monoidal structure on `D(𝒪_X)` given as an instance argument. At the
standard model `Std X` of `D(𝒪_X)`, where the derived internal hom `R𝓗om` of [Stacks, Tag 08DH]
and the derived pullback `Lf^*` are defined, `D(𝒪_X)` is closed symmetric monoidal
(`Stacks.Duality.TwistedInverseImageDuality.stdMonoidalClosed`). This file states the formula
there, with `D_X = CategoryTheory.MonoidalClosed.dualInto ω`.

## Main definitions

* `Stacks.Duality.fNewShriekStd` — `f_new^! = D_X ∘ Lf^* ∘ D_Y` at the standard model.
* `Stacks.Duality.relativeDualIsoSheafHom` — `D_X` is `(sheafHom X).flip.obj ω`, the duality
  functor of [Stacks, Tag 0AU2].
* `Stacks.Duality.dualIntoMapIso` — an isomorphism of the chosen complexes induces one of the
  duality functors, in any closed monoidal category.

## References

* [Stacks Project, Tag 0AUE](https://stacks.math.columbia.edu/tag/0AUE)
* [Stacks Project, Tag 0AU2](https://stacks.math.columbia.edu/tag/0AU2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed Opposite

universe v v' v₁ v₂ u u₁ u₂

namespace Stacks.Duality

open Stacks.Duality.TwistedInverseImageDuality (Std sheafHom pull stdMonoidal stdSymmetric
  stdMonoidalClosed)

section Functors

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] stdMonoidal stdSymmetric stdMonoidalClosed

variable {X Y : Scheme.{u}}

/-- **`Stacks.Duality.fNewShriek` at the standard model.** For a morphism
`f : X ⟶ Y` of schemes of finite type over the base, and chosen complexes `ω_X^•` and `ω_Y^•`,

`f_new^! M = D_X(Lf^* D_Y(M))`.

No compactification and no `f^!` enter: the right hand side is `R𝓗om_{𝒪_X}(-, ω_X^•)` applied
to the derived pullback of `R𝓗om_{𝒪_Y}(M, ω_Y^•)`. -/
abbrev fNewShriekStd (f : X ⟶ Y) (ωX : Std X) (ωY : Std Y) :
    Std Y ⥤ Std X :=
  dualConj (dualInto ωX) (dualInto ωY) (pull f)

/-- `D_X` is `R𝓗om(-, ω)`, the contravariant variable acting through `sheafHom X`: the two agree
on objects by definition and on morphisms by
`Stacks.Duality.TwistedInverseImageDuality.pre_app_std`. -/
def relativeDualIsoSheafHom (ω : Std X) : dualInto ω ≅ (sheafHom X).flip.obj ω :=
  NatIso.ofComponents (fun K => Iso.refl (((sheafHom X).obj K).obj ω))
    (fun {K L} g => (Category.comp_id _).trans
      ((TwistedInverseImageDuality.pre_app_std X g.unop ω).trans (Category.id_comp _).symm))

/-- On objects, `f_new^! M = R𝓗om(Lf^* R𝓗om(M, ω_Y^•), ω_X^•)`. -/
@[simp]
theorem fNewShriekStd_obj (f : X ⟶ Y) (ωX : Std X)
    (ωY : Std Y) (M : Std Y) :
    (fNewShriekStd f ωX ωY).obj M =
      (ihom ((pull f).obj ((ihom M).obj ωY))).obj ωX :=
  rfl

end Functors

section Twist

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [MonoidalClosed C]

/-- An isomorphism of the chosen complexes induces one of the duality functors
`CategoryTheory.MonoidalClosed.dualInto`. -/
def dualIntoMapIso {ω ω' : C} (e : ω ≅ ω') :
    dualInto ω ≅ dualInto ω' :=
  MonoidalClosed.internalHom.flip.mapIso e

end Twist

end Stacks.Duality

end
