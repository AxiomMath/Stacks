module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackGradedAlgebra
public import StacksFrontier.AlgebraicGeometry.Constructions.SymmetricAlgebraSheafFunctorial

/-!
# The unit of a degreewise comparison, and the algebra sheaf of an isomorphism

`Stacks.RelativeSpec.gradedAlgebraSheafMap` turns a *unital* homomorphism of sheaves of graded
algebras with commutative homogeneous multiplication into a morphism of the algebra sheaves of
[Stacks, Tag 01LM]. Two steps separate it from a comparison produced by a recognition theorem,
and this file supplies both.

## The unit

The category structure on `SheafOfModules.GradedAlgebra` is carried by
`SheafOfModules.GradedAlgebra.Hom`, which has an `app` and a `map_mul` and **no** `map_one`; a
`SheafOfModules.GradedAlgebra.UnitalHom` is the subclass that preserves the distinguished unit.
A comparison assembled degreewise is therefore a `Hom`, and its unit preservation is a separate
statement — which in practice arrives in the *global* form

`SheafOfModules.GradedAlgebra.oneHom A ≫ f.app 0 = SheafOfModules.GradedAlgebra.oneHom B`,

an equation between morphisms out of the monoidal unit, whereas
`SheafOfModules.GradedAlgebra.UnitalHom.ofHom` asks for
`SheafOfModules.sectionsMap (f.app 0) A.one = B.one`, an equation between global sections of the
degree-zero pieces. `sectionsMap_one_of_oneHom_comp` is the conversion: the unit morphism
corresponds to the unit under `SheafOfModules.unitHomEquiv`
(`SheafOfModules.GradedAlgebra.unitHomEquiv_oneHom`) and that bijection carries composition to
`SheafOfModules.sectionsMap` (`SheafOfModules.unitHomEquiv_comp_apply`), so the two forms are the
same equation read through one bijection and nothing else is involved.

## The isomorphism

`Stacks.RelativeSpec.gradedAlgebraSheafMap` has no `Iso` form, only the two functoriality laws
`Stacks.RelativeSpec.gradedAlgebraSheafMap_id` and `…_comp`. With
`SheafOfModules.GradedAlgebra.UnitalHom.inverse` — the degreewise inverse of a homomorphism
invertible in every degree, which is again multiplicative and unital — and its two laws
`…UnitalHom.comp_inverse` and `…inverse_comp`, the `Iso` is those four statements assembled and
carries no further hypothesis.

## Main results

* `SheafOfModules.GradedAlgebra.sectionsMap_one_of_oneHom_comp`: **the global form of unit
  preservation implies the global-sections form** that
  `SheafOfModules.GradedAlgebra.UnitalHom.ofHom` consumes.
* `SheafOfModules.GradedAlgebra.UnitalHom.ofOneHomComp`: **a homomorphism of sheaves of graded
  algebras commuting with the unit morphisms is a unital homomorphism.**
* `Stacks.RelativeSpec.gradedAlgebraSheafIso`: **a unital homomorphism of sheaves of graded
  algebras which is an isomorphism in every degree induces an isomorphism of their algebra
  sheaves.**

## References

* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory.Sheaf

universe w v u

namespace SheafOfModules.GradedAlgebra

/-! ### The unit, from the global form to the global-sections form -/

section Unit

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable {A B : GradedAlgebra.{w, w} (toRingCat J Osharp)}

/-- **Unit preservation in its global form implies unit preservation in the global-sections
form.** The unit morphism `SheafOfModules.GradedAlgebra.oneHom` is the unit read through the
bijection `SheafOfModules.unitHomEquiv` between morphisms out of the monoidal unit and global
sections, and that bijection carries postcomposition to `SheafOfModules.sectionsMap`; so the
equation of morphisms and the equation of global sections are the same statement. -/
theorem sectionsMap_one_of_oneHom_comp (f : Hom A B)
    (h : oneHom A ≫ f.app 0 = oneHom B) :
    SheafOfModules.sectionsMap (f.app 0) A.one = B.one :=
  (congrArg (SheafOfModules.sectionsMap (f.app 0)) (unitHomEquiv_oneHom A).symm).trans
    ((SheafOfModules.unitHomEquiv_comp_apply (oneHom A) (f.app 0)).symm.trans
      ((congrArg (B.piece 0).unitHomEquiv h).trans (unitHomEquiv_oneHom B)))

/-- **A homomorphism of sheaves of graded algebras commuting with the unit morphisms is a unital
homomorphism.** It is `SheafOfModules.GradedAlgebra.UnitalHom.ofHom` applied with
`sectionsMap_one_of_oneHom_comp`. -/
def UnitalHom.ofOneHomComp (f : Hom A B) (h : oneHom A ≫ f.app 0 = oneHom B) :
    UnitalHom A B :=
  UnitalHom.ofHom f (sectionsMap_one_of_oneHom_comp f h)

/-- In each degree, `UnitalHom.ofOneHomComp f h` is the component of `f`. -/
@[simp] theorem UnitalHom.ofOneHomComp_app (f : Hom A B)
    (h : oneHom A ≫ f.app 0 = oneHom B) (n : ℤ) :
    (UnitalHom.ofOneHomComp f h).app n = f.app n :=
  rfl

/-- The underlying homomorphism of `UnitalHom.ofOneHomComp f h` is `f`. -/
@[simp] theorem UnitalHom.toHom_ofOneHomComp (f : Hom A B)
    (h : oneHom A ≫ f.app 0 = oneHom B) :
    (UnitalHom.ofOneHomComp f h).toHom = f :=
  rfl

end Unit

end SheafOfModules.GradedAlgebra

/-! ### The algebra sheaf of a degreewise invertible unital homomorphism -/

namespace Stacks.RelativeSpec

open _root_.AlgebraicGeometry

variable (X : Scheme.{u}) {A B : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}
  (hcA : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (A.piece i).val.obj W)
    (b : (A.piece j).val.obj W), HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
  (hcB : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (B.piece i).val.obj W)
    (b : (B.piece j).val.obj W), HEq ((B.mul i j).app W a b) ((B.mul j i).app W b a))

/-- **A unital homomorphism of sheaves of graded algebras which is an isomorphism in every degree
induces an isomorphism of their algebra sheaves.**

This is the `Iso` form of `Stacks.RelativeSpec.gradedAlgebraSheafMap`. The inverse is the algebra
sheaf of the degreewise inverse `SheafOfModules.GradedAlgebra.UnitalHom.inverse`, and the two
identities are `…UnitalHom.comp_inverse` and `…inverse_comp` carried through
`Stacks.RelativeSpec.gradedAlgebraSheafMap_comp` and `…_id`. -/
def gradedAlgebraSheafIso (f : SheafOfModules.GradedAlgebra.UnitalHom A B)
    [∀ n, IsIso (f.app n)] :
    gradedAlgebraSheaf X A hcA ≅ gradedAlgebraSheaf X B hcB where
  hom := gradedAlgebraSheafMap X f hcA hcB
  inv := gradedAlgebraSheafMap X f.inverse hcB hcA
  hom_inv_id := by
    rw [← gradedAlgebraSheafMap_comp X A B A hcA hcB hcA f f.inverse,
      SheafOfModules.GradedAlgebra.UnitalHom.comp_inverse, gradedAlgebraSheafMap_id]
  inv_hom_id := by
    rw [← gradedAlgebraSheafMap_comp X B A B hcB hcA hcB f.inverse f,
      SheafOfModules.GradedAlgebra.UnitalHom.inverse_comp, gradedAlgebraSheafMap_id]

/-- The forward morphism of `gradedAlgebraSheafIso` is `gradedAlgebraSheafMap` of `f`. -/
@[simp] theorem gradedAlgebraSheafIso_hom (f : SheafOfModules.GradedAlgebra.UnitalHom A B)
    [∀ n, IsIso (f.app n)] :
    (gradedAlgebraSheafIso X hcA hcB f).hom = gradedAlgebraSheafMap X f hcA hcB :=
  rfl

/-- The inverse morphism of `gradedAlgebraSheafIso` is `gradedAlgebraSheafMap` of the degreewise
inverse `f.inverse`. -/
@[simp] theorem gradedAlgebraSheafIso_inv (f : SheafOfModules.GradedAlgebra.UnitalHom A B)
    [∀ n, IsIso (f.app n)] :
    (gradedAlgebraSheafIso X hcA hcB f).inv = gradedAlgebraSheafMap X f.inverse hcB hcA :=
  rfl

end Stacks.RelativeSpec

end
