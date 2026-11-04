module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAlgebraConstruction

/-!
# Recognising a sheaf of graded algebras as the sheafification of a sectionwise one

Let `(C, J)` be a site, `α : R₀ ⟶ R.obj` a locally bijective morphism from a presheaf of rings
to (the presheaf underlying) a sheaf of rings, `A` a graded algebra of presheaves of
`R₀`-modules and `B` a sheaf of graded `R`-algebras. `Stacks.GradedAlgebra.existsUnique_desc`
already turns a degreewise morphism `g n : A^n ⟶ B^n` which is multiplicative on homogeneous
local sections and carries the unit to the unit into a unital homomorphism

`A^♯ ⟶ B`

out of the sheafification `Stacks.GradedAlgebra.sheafify`. This file adds the recognition
statement: **if each `g n` is locally bijective, that homomorphism is an isomorphism in every
degree**, so `B` *is* the sheafification of `A` as a sheaf of graded algebras and not merely
degreewise. Consequently a universal property of `A^♯` — being the tensor, the exterior or the
symmetric algebra of a sheaf of modules — transports to `B`.

The intended use is a sheaf of graded algebras which is *not presented* as a sheafification but
which receives a locally bijective multiplicative unit from a sectionwise algebra: the
restriction of a sheafified sectionwise algebra to a slice site is the leading example, the
restricted sheafification unit being locally bijective by
`Stacks.SheafOfModules.SliceSheafification.isLocallyInjective_overToSheafify` and its surjective
companion, and multiplicative because the restricted algebra's multiplication on the sections
over an object of the slice site is the original multiplication on the sections over its
underlying object.

## Main definitions

* `Stacks.GradedAlgebra.descUnitalHom`: the unital homomorphism `A^♯ ⟶ B` extending a
  multiplicative unital degreewise morphism, named rather than extracted from the
  `ExistsUnique` at each use.

## Main results

* `Stacks.GradedAlgebra.descUnitalHom_app`: its degree-`n` component is
  `Stacks.GradedAlgebra.descApp`, the adjoint transpose of `g n`.
* `Stacks.GradedAlgebra.isIso_descApp` and `Stacks.GradedAlgebra.isIso_descUnitalHom_app`:
  **the components are isomorphisms as soon as `g` is degreewise locally bijective.**
* `Stacks.GradedAlgebra.isUniversal_of_locallyBijective`: **a universal property of the
  sheafified sectionwise algebra transports to `B`.**

## Implementation notes

The invertibility is not a statement about graded algebras at all: it is
`Stacks.SheafOfModules.SliceSheafification.isIso_sheafificationHomEquiv_symm`, that a locally
bijective morphism from a presheaf of modules into a sheaf exhibits the sheaf as the
sheafification, applied in each degree. What the graded layer contributes is that the adjoint
transposes assemble into a *unital homomorphism*, which is
`Stacks.GradedAlgebra.existsUnique_desc`, and that is also why the uniqueness clause of that
statement is used here: it identifies the components of the homomorphism it produces with
`Stacks.GradedAlgebra.descApp`, which is the morphism whose invertibility is available.

`Stacks.GradedAlgebra.isUniversal_of_locallyBijective` is stated with the generator of the
conclusion written out as `A.sheafifyGen α gen ≫ (A.descUnitalHom α g hmul hone).app 1` rather
than as a hypothesis, exactly as in
`SheafOfModules.GradedAlgebra.IsUniversal.ofDegreewiseIso`: the property `Pr` of generators is
quantified over the algebra, so the generator of `B` that the transported universal property is
about is determined by the homomorphism and cannot be chosen.

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite PresheafOfModules

universe v u t a

namespace Stacks.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{t}} {R : Sheaf J RingCat.{t}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{a}] [HasWeakSheafify J AddCommGrpCat.{a}]
  {P : ℤ → PresheafOfModules.{a} R₀} (A : GradedAlgebra P)
  {B : SheafOfModules.GradedAlgebra.{t, a} R}
  (g : ∀ n : ℤ, P n ⟶ (SheafOfModules.forget R ⋙ restrictScalars α).obj (B.piece n))

/-- **A degreewise locally bijective morphism into a sheaf of graded algebras has invertible
adjoint transposes.** This is the recognition statement of this file in the form in which it is
proved: a locally bijective morphism from a presheaf of modules into a sheaf exhibits the sheaf
as the sheafification of the presheaf, in each degree separately. -/
theorem isIso_descApp
    (hinj : ∀ n : ℤ, Presheaf.IsLocallyInjective J ((toPresheaf R₀).map (g n)))
    (hsurj : ∀ n : ℤ, Presheaf.IsLocallySurjective J ((toPresheaf R₀).map (g n))) (n : ℤ) :
    IsIso (A.descApp α g n) := by
  have he : (PresheafOfModules.sheafificationAdjunction α).homEquiv (P n) (B.piece n) =
      PresheafOfModules.sheafificationHomEquiv α :=
    Equiv.ext fun f => PresheafOfModules.sheafificationAdjunction_homEquiv_apply α f
  have hd : A.descApp α g n =
      ((PresheafOfModules.sheafificationAdjunction α).homEquiv (P n) (B.piece n)).symm (g n) :=
    rfl
  rw [hd, he]
  exact Stacks.SheafOfModules.SliceSheafification.isIso_sheafificationHomEquiv_symm α (g n)
    (hinj n) (hsurj n)

variable
  (hmul : ∀ (i j : ℤ) (X : Cᵒᵖ) (x : (P i).obj X) (y : (P j).obj X),
    PresheafOfModules.Hom.app (g (i + j)) X ((A.mul i j).app X x y) =
      (B.mul i j).app X (PresheafOfModules.Hom.app (g i) X x) (PresheafOfModules.Hom.app (g j) X y))
  (hone : ∀ X : Cᵒᵖ, PresheafOfModules.Hom.app (g 0) X (A.one.eval X) = B.one.eval X)

include hmul hone

/-- **The unital homomorphism out of the sheafification determined by a multiplicative unital
degreewise morphism**, named: it is the homomorphism whose existence and uniqueness is
`Stacks.GradedAlgebra.existsUnique_desc`. -/
def descUnitalHom : SheafOfModules.GradedAlgebra.UnitalHom (A.sheafify α) B :=
  (A.existsUnique_desc α g hmul hone).choose

/-- `Stacks.GradedAlgebra.descUnitalHom` extends the given degreewise morphism: on the
unit-image of a homogeneous local section it is that morphism. -/
theorem descUnitalHom_unit (n : ℤ) (X : Cᵒᵖ) (s : (P n).obj X) :
    ((A.descUnitalHom α g hmul hone).app n).val.app X
        (PresheafOfModules.Hom.app (sheafifyUnit α (P n)) X s) =
      PresheafOfModules.Hom.app (g n) X s :=
  (A.existsUnique_desc α g hmul hone).choose_spec.1 n X s

/-- The degree-`n` component of `Stacks.GradedAlgebra.descUnitalHom` is the adjoint transpose
`Stacks.GradedAlgebra.descApp` of `g n`: both agree on unit-images, and a morphism out of a
sheafification is determined by its values there. -/
theorem descUnitalHom_app (n : ℤ) :
    (A.descUnitalHom α g hmul hone).app n = A.descApp α g n :=
  PresheafOfModules.sheafification_hom_ext_apply α fun X s =>
    (A.descUnitalHom_unit α g hmul hone n X s).trans (A.descApp_unit α g n X s).symm

/-- **The homomorphism out of the sheafification is an isomorphism in every degree as soon as
the given degreewise morphism is locally bijective**: so `B`, with the multiplication and the
unit it carries, *is* the sheafification of the sectionwise graded algebra `A`. -/
theorem isIso_descUnitalHom_app
    (hinj : ∀ n : ℤ, Presheaf.IsLocallyInjective J ((toPresheaf R₀).map (g n)))
    (hsurj : ∀ n : ℤ, Presheaf.IsLocallySurjective J ((toPresheaf R₀).map (g n))) (n : ℤ) :
    IsIso ((A.descUnitalHom α g hmul hone).app n) := by
  rw [A.descUnitalHom_app α g hmul hone n]
  exact A.isIso_descApp α g hinj hsurj n

/-- **A universal property of the sheafified sectionwise graded algebra transports along a
degreewise locally bijective multiplicative unital morphism.** If `A^♯` with the sheafified
degree-one generator is universal for a property `Pr` of degree-one generators — for
`Pr = SquareZero` this is `Stacks.GradedAlgebra.isExteriorAlgebra_sheafify` — and `g` is
multiplicative, unital and degreewise locally bijective, then `B` with the transported
generator is universal for `Pr` as soon as that generator has `Pr`. -/
theorem isUniversal_of_locallyBijective
    (hinj : ∀ n : ℤ, Presheaf.IsLocallyInjective J ((toPresheaf R₀).map (g n)))
    (hsurj : ∀ n : ℤ, Presheaf.IsLocallySurjective J ((toPresheaf R₀).map (g n)))
    {F : PresheafOfModules.{a} R₀} (gen : F ⟶ P 1)
    {Pr : ∀ D : SheafOfModules.GradedAlgebra.{t, a} R,
      ((sheafification α).obj F ⟶ D.piece 1) → Prop}
    (hA : SheafOfModules.GradedAlgebra.IsUniversal Pr (A.sheafify α) (A.sheafifyGen α gen))
    (hPr : Pr B (A.sheafifyGen α gen ≫ (A.descUnitalHom α g hmul hone).app 1)) :
    SheafOfModules.GradedAlgebra.IsUniversal Pr B
      (A.sheafifyGen α gen ≫ (A.descUnitalHom α g hmul hone).app 1) :=
  have : ∀ n : ℤ, IsIso ((A.descUnitalHom α g hmul hone).app n) :=
    fun n => A.isIso_descUnitalHom_app α g hmul hone hinj hsurj n
  hA.ofDegreewiseIso (A.descUnitalHom α g hmul hone) hPr

end Stacks.GradedAlgebra

end
