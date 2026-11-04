module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerived.CechIsTheDerivedFunctor

/-!
# Additivity of evaluation on formal coproducts

Let `C` be a category and let `A` be a preadditive category with arbitrary products. Mathlib's
`CategoryTheory.Limits.FormalCoproduct.evalOp C A` extends a presheaf `P : Cᵒᵖ ⥤ A` to a presheaf
on the category `FormalCoproduct.{w} C` of formal coproducts — the Stacks Project's category
`SR(C)` of semi-representable objects — by `X ↦ ∏ i, P(X.obj i)`. This file proves that this
extension is an additive functor, and propagates additivity to the two functors built from it in
`Mathlib.CategoryTheory.Sites.SheafCohomology.Cech`: the cosimplicial object and the cochain
complex obtained by evaluating a presheaf on a simplicial semi-representable object.

## Main results

* `CategoryTheory.Limits.Pi.map_add`: `Pi.map` is additive in the family of component morphisms.
* `CategoryTheory.Limits.FormalCoproduct.evalOp_additive`: `evalOp C A` is additive.
* `CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor_additive` and
  `CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor_additive`: the Čech-style
  functors `(Cᵒᵖ ⥤ A) ⥤ CosimplicialObject A` and `(Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ` attached to a
  simplicial object of `FormalCoproduct.{w} C` are additive.

## Implementation notes

Additivity of `evalOp` is proved through the auxiliary `Pi.map_add` rather than in place, and
that is load-bearing. `Functor.Additive.map_add` for `evalOp` is an equality of natural
transformations; after `ext X : 2` the two sides are morphisms whose source is spelled
`((evalOp C A).obj P).obj X` on one side, while `Limits.Pi.hom_ext` forces the spelling
`∏ᶜ fun i ↦ P.obj (op ((unop X).obj i))`. The two are definitionally equal but not
syntactically so, and once a goal mixes them it is no longer type-correct at `implicit`
transparency: `Pi.map_π` and `Preadditive.add_comp` then both report that they cannot find
their pattern while printing exactly that pattern. Stating `Pi.map_add` separately keeps every
object in the product spelling throughout its proof, and the instance discharges its goal by
`exact`, which only needs definitional equality.

The two propagation instances are not automatic: `cosimplicialObjectFunctor` and
`cochainComplexFunctor` are semireducible definitions, so instance search does not unfold them
to the composites they are defined as, and a consumer writing either name needs an instance
headed by that name. `cochainComplexFunctor` is a composite with
`AlgebraicTopology.alternatingCofaceMapComplex A`, whose additivity is *not* in Mathlib (only
the `alternatingFaceMapComplex` variant is) but is proved in this repository as
`Stacks.Cohomology.CechDerived.alternatingCofaceMapComplex_additive`; that is the reason this
file imports `StacksDraft.Ch20.Sec13.Tag01EN`.
-/

@[expose] public section

universe w v₁ u₁ v u

open Opposite

namespace CategoryTheory.Limits

/-- `Pi.map` is additive in the family of component morphisms: the product of a pointwise sum of
two families of morphisms is the sum of the two products. -/
theorem Pi.map_add {A : Type u₁} [Category.{v₁} A] [Preadditive A] {β : Type w} {f g : β → A}
    [HasProduct f] [HasProduct g] (p q : ∀ b, f b ⟶ g b) :
    Limits.Pi.map (fun b ↦ p b + q b) = Limits.Pi.map p + Limits.Pi.map q := by
  ext b
  simp [Preadditive.add_comp]

variable {C : Type u} [Category.{v} C] (A : Type u₁) [Category.{v₁} A]
  [Preadditive A] [HasProducts.{w} A]

/-- Extension of presheaves to formal coproducts is additive: it acts on a morphism of presheaves
by taking the product of its components, and `Pi.map` is additive. -/
instance FormalCoproduct.evalOp_additive : (FormalCoproduct.evalOp.{w} C A).Additive where
  map_add := by
    intro P Q α β
    ext X : 2
    exact Limits.Pi.map_add
      (f := fun i : (unop X).I ↦ P.obj (op ((unop X).obj i)))
      (g := fun i : (unop X).I ↦ Q.obj (op ((unop X).obj i)))
      (fun i ↦ α.app _) (fun i ↦ β.app _)

variable (E : SimplicialObject (FormalCoproduct.{w} C))

/-- Evaluating a presheaf degreewise on a simplicial semi-representable object is additive in the
presheaf. -/
instance FormalCoproduct.cosimplicialObjectFunctor_additive :
    (FormalCoproduct.cosimplicialObjectFunctor (A := A) E).Additive :=
  inferInstanceAs (Functor.Additive (FormalCoproduct.evalOp.{w} C A ⋙
    (Functor.whiskeringLeft _ _ _).obj E.rightOp))

/-- The Čech-style cochain complex of a simplicial semi-representable object is additive in the
coefficient presheaf. -/
instance FormalCoproduct.cochainComplexFunctor_additive :
    (FormalCoproduct.cochainComplexFunctor (A := A) E).Additive :=
  inferInstanceAs (Functor.Additive (FormalCoproduct.cosimplicialObjectFunctor (A := A) E ⋙
    AlgebraicTopology.alternatingCofaceMapComplex A))

end CategoryTheory.Limits

end
