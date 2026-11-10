module

public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeIdentity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedCategory
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedHomotopyCategoryTriangulated
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomFilteredColimit
public import StacksCore.Tactic.StacksAttribute

/-!
# The derived morphism attached to a relative de Rham cohomology class

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space `X`, let
`Ω^• = Ω^•_{𝒪_X/A}` be the relative de Rham complex and let `ξ ∈ H^n_{dR}` be a relative de Rham
cohomology class. Reading `Ω^•` as a sheaf of differential graded `A`-algebras and as the regular
right differential graded module over itself, there is a morphism

`ξ' : Ω^• ⟶ Ω^•[n]`

in `D(A)` which lifts to a morphism `Ω^• ⟶ Ω^•[n]` of the derived category of right differential
graded `Ω^•`-modules and whose value at the unit is `ξ`, and these two properties determine it.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.deRhamDerivedObject`: the relative de Rham complex as an
  object of `D(A)`.
* `AlgebraicGeometry.SheafOfModules.deRhamRegularModule`: the relative de Rham complex as the
  regular right differential graded module over the de Rham differential graded algebra.
* `AlgebraicGeometry.SheafOfModules.deRhamDerivedRegular` and
  `AlgebraicGeometry.SheafOfModules.deRhamDerivedRegularShift`: that module and its `n`-fold
  translate, as objects of the derived category of right differential graded modules.
* `AlgebraicGeometry.SheafOfModules.DeRhamDerivedModuleCorrespondence`: **the parameter**, the
  identification of `H^n_{dR}` with morphisms `Ω^• ⟶ Ω^•[n]` in the derived category of right
  differential graded modules, together with the forgetful map to `D(A)` and the evaluation at
  the unit.
* `AlgebraicGeometry.SheafOfModules.deRhamClassDerivedMorphism`: **the morphism `ξ'` attached to
  a relative de Rham cohomology class `ξ`.**

## Main results

* `AlgebraicGeometry.SheafOfModules.exists_lift_deRhamClassDerivedMorphism` and
  `AlgebraicGeometry.SheafOfModules.evalOne_deRhamClassDerivedMorphism`: `ξ'` lifts to a morphism
  of the derived category of right differential graded modules, and `ξ'(1) = ξ`.
* `AlgebraicGeometry.SheafOfModules.eq_deRhamClassDerivedMorphism`: **those two properties
  characterize `ξ'` uniquely.**
* `AlgebraicGeometry.SheafOfModules.deRhamClassDerivedMorphism_injective`: distinct classes give
  distinct morphisms.

## Implementation notes

The one parameter of this file is
`AlgebraicGeometry.SheafOfModules.DeRhamDerivedModuleCorrespondence`. It carries the input of
Differential Graded Sheaves, Section 0FU3 that the library does not have: the identification
`H^n(C, M) = Hom_{D(A, d)}(A, M[n])` of Tag 0FTX, taken for `M` the regular module, the map
induced on morphisms by forgetting the right differential graded module structure, and the
evaluation at the unit, which reads a morphism `Ω^• ⟶ Ω^•[n]` of `D(A)` as a class in
`H^0(X, Ω^•[n]) = H^n_{dR}`. Only the compatibility of the three — that evaluation at the unit
inverts the identification of Tag 0FTX — is assumed; the existence and the uniqueness of `ξ'` are
deduced from it, so neither is taken as a hypothesis.

Both the source and the target of `ξ'` are the relative de Rham complex, extended by zero to
negative degrees, which is why the forgetful map of the parameter has the type it has: the
complex underlying the regular right differential graded module is
`AlgebraicGeometry.SheafOfModules.deRhamComplexInt` on the nose
(`AlgebraicGeometry.SheafOfModules.deRhamRegularModule_complex`).

The translation functors of the homotopy category of right differential graded modules are
available for a sheaf of differential graded algebras on a ringed *site*, so the ringed space `X`
with the base sheaf `A` as its structure sheaf is read as one through
`Stacks.SheafOfModules.opensRingedSite`; this is
`AlgebraicGeometry.SheafOfModules.deRhamHomotopyHasShift`.

Everything is stated for an arbitrary package `B` of the three algebras of Stacks Section 17.21 on
the sheaf of relative differentials of `φ` and an arbitrary de Rham differential `D` on it, as the
rest of the development is.

## References

* [Stacks Project, Tag 0FU7](https://stacks.math.columbia.edu/tag/0FU7)
* [Stacks Project, Tag 0FU6](https://stacks.math.columbia.edu/tag/0FU6)
* [Stacks Project, Tag 0FU3](https://stacks.math.columbia.edu/tag/0FU3)
* [Stacks Project, Tag 0FTX](https://stacks.math.columbia.edu/tag/0FTX)
* [Stacks Project, Tag 0FT5](https://stacks.math.columbia.edu/tag/0FT5)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open _root_.SheafOfModules.DifferentialGradedModule (regularModule derivedCategory
  toDerivedCategory)

universe u

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-! ### The relative de Rham complex as an object of two derived categories -/

/-- The relative de Rham complex, extended by zero to negative degrees, as an object of the
derived category of sheaves of `A`-modules. -/
noncomputable abbrev deRhamDerivedObject :
    DerivedCategory (_root_.SheafOfModules.{u} (underlyingRingSheaf A)) :=
  DerivedCategory.Q.obj (deRhamComplexInt B D)

/-- The relative de Rham complex as the regular right differential graded module over the de Rham
differential graded algebra of Tag 0FU6. -/
noncomputable abbrev deRhamRegularModule :
    _root_.SheafOfModules.DifferentialGradedModule.{u, u, u}
      (deRhamDifferentialGradedAlgebra B D) :=
  regularModule (deRhamDifferentialGradedAlgebra B D)

/-- The complex underlying the regular right differential graded module is the relative de Rham
complex, extended by zero to negative degrees. -/
theorem deRhamRegularModule_complex :
    (deRhamRegularModule B D).complex = deRhamComplexInt B D := rfl

/-- The translation functors of the homotopy category of right differential graded modules over
the relative de Rham complex, read on the site of open subsets of `X` with the base ring sheaf as
its structure sheaf. -/
noncomputable instance deRhamHomotopyHasShift :
    HasShift (_root_.SheafOfModules.DifferentialGradedModule.HomotopyCategory.{u, u, u}
      (deRhamDifferentialGradedAlgebra B D)) ℤ :=
  _root_.SheafOfModules.DifferentialGradedModule.HomotopyCategory.instHasShift
    (X := Stacks.SheafOfModules.opensRingedSite A) (deRhamDifferentialGradedAlgebra B D)

/-- The relative de Rham complex as an object of the derived category of right differential graded
modules over itself. -/
noncomputable abbrev deRhamDerivedRegular :
    derivedCategory.{u, u, u} (deRhamDifferentialGradedAlgebra B D) :=
  (toDerivedCategory _).obj
    ((_root_.SheafOfModules.DifferentialGradedModule.HomotopyCategory.quotient _).obj
      (deRhamRegularModule B D))

/-- The `n`-fold translate `Ω^•[n]` of the relative de Rham complex, as an object of the derived
category of right differential graded modules over itself. -/
noncomputable abbrev deRhamDerivedRegularShift (n : ℤ) :
    derivedCategory.{u, u, u} (deRhamDifferentialGradedAlgebra B D) :=
  (toDerivedCategory _).obj
    (((_root_.SheafOfModules.DifferentialGradedModule.HomotopyCategory.quotient _).obj
      (deRhamRegularModule B D))⟦n⟧)

/-! ### The identification of de Rham classes with derived differential graded module maps -/

/-- **The identification of Differential Graded Sheaves, Section 0FU3 for the relative de Rham
complex.**

A term of this structure provides, in every degree `n`, the map induced on morphisms by forgetting
the right differential graded module structure, the identification

`H^n_{dR} ≃ Hom_{D(Ω^•, d)}(Ω^•, Ω^•[n])`

which Tag 0FTX gives for the regular module, and the evaluation at the unit, which reads a
morphism `Ω^• ⟶ Ω^•[n]` of `D(A)` as a class in `H^0(X, Ω^•[n]) = H^n_{dR}`, together with the one
compatibility between them: evaluation at the unit inverts the identification of Tag 0FTX.

This is the one parameter of this file: Section 0FU3 and Tag 0FTX are not in the library, and no
second construction of them is given here. The existence and the uniqueness of the morphism
attached to a class are *deduced* from the compatibility and are not fields. -/
structure DeRhamDerivedModuleCorrespondence where
  /-- Forgetting the right differential graded module structure, on morphisms. -/
  forget (n : ℤ) :
    (deRhamDerivedRegular B D ⟶ deRhamDerivedRegularShift B D n) →
      (deRhamDerivedObject B D ⟶ (deRhamDerivedObject B D)⟦n⟧)
  /-- Tag 0FTX for the regular module: a de Rham class of degree `n` is a morphism
  `Ω^• ⟶ Ω^•[n]` in the derived category of right differential graded modules. -/
  classEquiv (n : ℤ) :
    deRhamCohomology B D n ≃ (deRhamDerivedRegular B D ⟶ deRhamDerivedRegularShift B D n)
  /-- Evaluation at the unit, through `H^0(X, Ω^•[n]) = H^n_{dR}`. -/
  evalOne (n : ℤ) :
    (deRhamDerivedObject B D ⟶ (deRhamDerivedObject B D)⟦n⟧) → deRhamCohomology B D n
  /-- The normalization of Section 0FU3: evaluation at the unit inverts the identification of
  Tag 0FTX. -/
  evalOne_forget_classEquiv (n : ℤ) (ξ : deRhamCohomology B D n) :
    evalOne n (forget n (classEquiv n ξ)) = ξ

variable (c : DeRhamDerivedModuleCorrespondence B D)

/-! ### The morphism attached to a de Rham class -/

/-- **Stacks Project, Tag 0FU7.** The morphism

`ξ' : Ω^•_{X/S} ⟶ Ω^•_{X/S}[n]`

in `D(f^{-1}𝒪_S)` attached to a relative de Rham cohomology class `ξ ∈ H^n_{dR}(X/S)`: the
morphism of right differential graded `Ω^•_{X/S}`-modules which Tag 0FTX attaches to `ξ`, with its
module structure forgotten. -/
@[stacks 0FU7 "the morphism of D(f^{-1}O_S) attached to a de Rham class; the discussion of
Differential Graded Sheaves Section 0FU3 is carried as the explicit named hypothesis
DeRhamDerivedModuleCorrespondence, whose fields are the identification of Tag 0FTX for the regular
module, the forgetful map on morphisms and the evaluation at the unit"]
noncomputable def deRhamClassDerivedMorphism (n : ℤ) (ξ : deRhamCohomology B D n) :
    deRhamDerivedObject B D ⟶ (deRhamDerivedObject B D)⟦n⟧ :=
  c.forget n (c.classEquiv n ξ)

/-- **Stacks Project, Tag 0FU7, property (1).** The morphism attached to a relative de Rham class
lifts to a morphism in the derived category of right differential graded `Ω^•_{X/S}`-modules. -/
@[stacks 0FU7 "property (1): the morphism lifts to the derived category of right differential
graded modules; Section 0FU3 is carried as the hypothesis DeRhamDerivedModuleCorrespondence"]
theorem exists_lift_deRhamClassDerivedMorphism (n : ℤ) (ξ : deRhamCohomology B D n) :
    ∃ g : deRhamDerivedRegular B D ⟶ deRhamDerivedRegularShift B D n,
      c.forget n g = deRhamClassDerivedMorphism B D c n ξ :=
  ⟨c.classEquiv n ξ, rfl⟩

/-- **Stacks Project, Tag 0FU7, property (2).** The value at the unit of the morphism attached to
a relative de Rham class `ξ` is `ξ` itself: `ξ'(1) = ξ` in
`H^0(X, Ω^•_{X/S}[n]) = H^n_{dR}(X/S)`. -/
@[stacks 0FU7 "property (2): the value of the morphism at the unit is the class it came from;
Section 0FU3 is carried as the hypothesis DeRhamDerivedModuleCorrespondence"]
theorem evalOne_deRhamClassDerivedMorphism (n : ℤ) (ξ : deRhamCohomology B D n) :
    c.evalOne n (deRhamClassDerivedMorphism B D c n ξ) = ξ :=
  c.evalOne_forget_classEquiv n ξ

/-- **Stacks Project, Tag 0FU7.** A morphism `Ω^•_{X/S} ⟶ Ω^•_{X/S}[n]` of `D(f^{-1}𝒪_S)` which
lifts to the derived category of right differential graded `Ω^•_{X/S}`-modules and whose value at
the unit is `ξ` is the morphism attached to `ξ`. -/
@[stacks 0FU7 "uniqueness: properties (1) and (2) determine the morphism; Section 0FU3 is carried
as the hypothesis DeRhamDerivedModuleCorrespondence"]
theorem eq_deRhamClassDerivedMorphism (n : ℤ) (ξ : deRhamCohomology B D n)
    {f : deRhamDerivedObject B D ⟶ (deRhamDerivedObject B D)⟦n⟧}
    (hlift : ∃ g : deRhamDerivedRegular B D ⟶ deRhamDerivedRegularShift B D n, c.forget n g = f)
    (hev : c.evalOne n f = ξ) :
    f = deRhamClassDerivedMorphism B D c n ξ := by
  obtain ⟨g, rfl⟩ := hlift
  have key := c.evalOne_forget_classEquiv n ((c.classEquiv n).symm g)
  rw [Equiv.apply_symm_apply, hev] at key
  change c.forget n g = c.forget n (c.classEquiv n ξ)
  exact congrArg (c.forget n) ((Equiv.symm_apply_eq _).1 key.symm)

/-- Distinct relative de Rham cohomology classes of degree `n` give distinct morphisms
`Ω^•_{X/S} ⟶ Ω^•_{X/S}[n]`. -/
theorem deRhamClassDerivedMorphism_injective (n : ℤ) :
    Function.Injective (deRhamClassDerivedMorphism B D c n) := by
  intro ξ η h
  have key := evalOne_deRhamClassDerivedMorphism B D c n ξ
  rw [h, evalOne_deRhamClassDerivedMorphism] at key
  exact key.symm

end AlgebraicGeometry.SheafOfModules

end
