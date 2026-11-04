module

public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import StacksFrontier.CategoryTheory.Limits.FormalCoproductAdditive

/-!
# Linearity of evaluation on formal coproducts

Let `R` be a semiring, let `C` be a category and let `A` be an `R`-linear preadditive category
with arbitrary products. `Mathlib`'s `CategoryTheory.Limits.FormalCoproduct.evalOp C A` extends a
presheaf `P : Cᵒᵖ ⥤ A` to a presheaf on the category `FormalCoproduct.{w} C` of formal
coproducts by `X ↦ ∏ i, P(X.obj i)`. This file proves that this extension is an `R`-linear
functor, and propagates linearity to the two functors built from it in
`Mathlib.CategoryTheory.Sites.SheafCohomology.Cech`: the cosimplicial object and the cochain
complex obtained by evaluating a presheaf on a simplicial semi-representable object.

## Main results

* `CategoryTheory.Limits.Pi.map_smul`: `Pi.map` commutes with multiplying the family of component
  morphisms by a scalar.
* `CategoryTheory.Limits.FormalCoproduct.evalOp_linear`: `evalOp C A` is `R`-linear.
* `CategoryTheory.Functor.whiskeringLeft_obj_linear`: precomposition with a fixed functor is
  `R`-linear.
* `AlgebraicTopology.alternatingCofaceMapComplex_linear`: the alternating coface
  map complex of a cosimplicial object is an `R`-linear functor of that object.
* `CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor_linear` and
  `CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor_linear`: the Čech-style functors
  `(Cᵒᵖ ⥤ A) ⥤ CosimplicialObject A` and `(Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ` attached to a
  simplicial object of `FormalCoproduct.{w} C` are `R`-linear.

## Implementation notes

The proofs follow `StacksFrontier.CategoryTheory.Limits.FormalCoproductAdditive` step for step, the
scalar action replacing the addition. In particular linearity of `evalOp` goes through the
auxiliary `Pi.map_smul`, which keeps every object in the product spelling
`∏ᶜ fun i ↦ P.obj (op ((unop X).obj i))` throughout its proof; a goal that mixes that spelling
with `((evalOp C A).obj P).obj X` is no longer type-correct at `implicit` transparency, and
`Pi.map_π` then fails to find a pattern it is printing.

The three propagation instances are not automatic: `alternatingCofaceMapComplex`,
`cosimplicialObjectFunctor` and `cochainComplexFunctor` are semireducible definitions, so
instance search does not unfold them to the composites or the degreewise descriptions they are
defined as, and a consumer writing either name needs an instance headed by that name.
-/

@[expose] public section

universe w v₁ u₁ v u

open Opposite

namespace CategoryTheory

/-- **Precomposition with a fixed functor is `R`-linear.** A scalar acts on a natural
transformation componentwise, and precomposition only reindexes the components. -/
instance Functor.whiskeringLeft_obj_linear {R : Type*} [Semiring R] {D D' A : Type*}
    [Category* D] [Category* D'] [Category* A] [Preadditive A]
    [_root_.CategoryTheory.Linear R A] (G : D ⥤ D') :
    Functor.Linear R ((Functor.whiskeringLeft D D' A).obj G) where
  map_smul _ _ := NatTrans.ext (funext fun _ ↦ rfl)

end CategoryTheory

namespace AlgebraicTopology

open CategoryTheory

/-- **The alternating coface map complex is an `R`-linear functor of the cosimplicial object.**
A scalar acts degreewise on both sides, and the complex is formed degreewise. -/
instance alternatingCofaceMapComplex_linear {R : Type*} [Semiring R] (A : Type u₁)
    [Category.{v₁} A] [Preadditive A] [Linear R A] :
    Functor.Linear R (alternatingCofaceMapComplex A) where
  map_smul _ _ := HomologicalComplex.hom_ext _ _ (fun _ ↦ rfl)

end AlgebraicTopology

namespace CategoryTheory.Limits

/-- `Pi.map` commutes with multiplying the family of component morphisms by a scalar: the
product of a family scaled pointwise is the scalar multiple of the product. -/
theorem Pi.map_smul {R : Type*} [Semiring R] {A : Type u₁} [Category.{v₁} A] [Preadditive A]
    [Linear R A] {β : Type w} {f g : β → A} [HasProduct f] [HasProduct g] (a : R)
    (p : ∀ b, f b ⟶ g b) :
    Limits.Pi.map (fun b ↦ a • p b) = a • Limits.Pi.map p := by
  refine Limits.Pi.hom_ext _ _ (fun b ↦ ?_)
  rw [Limits.Pi.map_π, Linear.smul_comp, Limits.Pi.map_π, Linear.comp_smul]

variable {R : Type*} [Semiring R] {C : Type u} [Category.{v} C] (A : Type u₁) [Category.{v₁} A]
  [Preadditive A] [Linear R A] [HasProducts.{w} A]

/-- **Extension of presheaves to formal coproducts is `R`-linear**: it acts on a morphism of
presheaves by taking the product of its components, and `Pi.map` commutes with scalars. -/
instance FormalCoproduct.evalOp_linear :
    Functor.Linear R (FormalCoproduct.evalOp.{w} C A) where
  map_smul := by
    intro P Q α a
    ext X : 2
    exact Limits.Pi.map_smul
      (f := fun i : (unop X).I ↦ P.obj (op ((unop X).obj i)))
      (g := fun i : (unop X).I ↦ Q.obj (op ((unop X).obj i)))
      a (fun i ↦ α.app _)

variable (E : SimplicialObject (FormalCoproduct.{w} C))

/-- Evaluating a presheaf degreewise on a simplicial semi-representable object is `R`-linear in
the presheaf. -/
instance FormalCoproduct.cosimplicialObjectFunctor_linear :
    Functor.Linear R (FormalCoproduct.cosimplicialObjectFunctor (A := A) E) :=
  inferInstanceAs (Functor.Linear R (FormalCoproduct.evalOp.{w} C A ⋙
    (Functor.whiskeringLeft _ _ _).obj E.rightOp))

/-- **The Čech-style cochain complex of a simplicial semi-representable object is `R`-linear in
the coefficient presheaf.** -/
instance FormalCoproduct.cochainComplexFunctor_linear :
    Functor.Linear R (FormalCoproduct.cochainComplexFunctor (A := A) E) :=
  inferInstanceAs (Functor.Linear R (FormalCoproduct.cosimplicialObjectFunctor (A := A) E ⋙
    AlgebraicTopology.alternatingCofaceMapComplex A))

end CategoryTheory.Limits

end
