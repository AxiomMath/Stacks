module

public import StacksFrontier.Deformation.ToposThickening.DerivedReductionData
public import StacksFrontier.Deformation.ToposThickening.ExtensionRestrictTensor

/-!
# Derived base change, read over `O`, is the derived tensor product with `O₀`

Let `f : O ⟶ O₀` be a morphism of sheaves of commutative rings on a site. Derived base change
along `f`, followed by derived restriction of scalars, and the derived tensor product with `O₀`
read as a sheaf of `O`-modules are both total left derived functors, along the localization of
the homotopy category, of *the same* functor on complexes: that is the content of
`Deformation.ComplexLift.restrictExtensionIsoTensorRight` at the level of complexes. Uniqueness
of left derived functors therefore identifies them, and this file performs that identification.

This is the first of the two comparisons a
`Deformation.ComplexLift.DerivedReduction` needs — the identification of the third vertex
`restriction (K ⊗^L_O O₀)` of the reduction triangle with `K ⊗^L_O O₀` formed in `D(O)`.

## Main definitions

* `Deformation.ComplexLift.restrictionCompHomotopyIso`: the isomorphism, on the homotopy
  category, of the two functors being derived.
* `Deformation.ComplexLift.derivedRestrictExtensionIso`: **the comparison**
  `(- ⊗^L_O O₀)|_O ≅ - ⊗^L_O O₀|_O`, for the derived base change constructed by Stacks 0794.
* `Deformation.ComplexLift.derivedRestrictExtensionIsoOf`: the same for an arbitrary derived
  base change along `f`, which is the form a `Deformation.ComplexLift.DerivedReduction` consumes.

## Main results

* `Deformation.ComplexLift.isLeftDerivedFunctor_of_targetIso`: a left derived functor stays one
  when its comparison is composed with an isomorphism of the functor being derived.

## Implementation notes

**Where the work is.** Both sides are left derived functors along `Qh`, by
`Deformation.ComplexLift.isLeftDerivedFunctor_comp_derivedExtensionOfScalars` — absoluteness of
derived base change — and by
`Deformation.ComplexLift.isLeftDerivedFunctor_derivedTensorRightCounitHomotopy`. What they derive
is stated in two different shapes, `extensionOfScalarsHomotopy f ⋙ restrictionOnDerived f` and
`tensorRightHomotopy (restrictUnitOf f)`, and the only real step is an isomorphism between them.

**Why it is built after precomposing with the homotopy quotient.** The composite
`(F ⋙ G).mapHomotopyCategory` is *not* the composite of the two
`mapHomotopyCategory`s — `rfl` fails — whereas for
`CategoryTheory.Functor.mapHomologicalComplex` it is, on the nose. So the isomorphism is built on
cochain complexes, where the two sides are the degreewise functors of
`Deformation.ComplexLift.restrictExtensionIsoTensorRight` followed by the localization, and then
pushed back up to the homotopy category by `CategoryTheory.Quotient.natIsoLift`: the homotopy
category is a quotient, so a natural isomorphism of functors out of it is exactly one of their
precomposites with the quotient functor. The two precomposites are already in the tree, as
`Deformation.ComplexLift.quotientCompExtensionOfScalarsIso` and
`Deformation.ComplexLift.quotientCompTensorRightIso`.

**The universes.** Nothing here narrows them: the module universe `u` stays independent of the
two site universes `u'` and `v'`, and the two derived-category hom universes `d` and `d₀` stay
independent of all three, exactly as in
`Deformation.ComplexLift.DerivedExtensionOfScalars`.

## References

* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 0DIY](https://stacks.math.columbia.edu/tag/0DIY)
-/

@[expose] public noncomputable section

open CategoryTheory

universe d d₀ v' u u'

namespace Deformation.ComplexLift

/-! ### A left derived functor is one along any isomorphism of what it derives -/

/-- **A left derived functor stays one when the functor it derives is replaced by an isomorphic
one**, the comparison being composed with the isomorphism. This is
`CategoryTheory.Functor.isRightKanExtension_iff_of_iso₂` at the identity isomorphism of the
derived functor itself. -/
theorem isLeftDerivedFunctor_of_targetIso {A B H : Type*} [Category A] [Category B] [Category H]
    {LF : B ⥤ H} {F F' : A ⥤ H} {L : A ⥤ B} (α : L ⋙ LF ⟶ F) (e : F ≅ F')
    (W : MorphismProperty A) [L.IsLocalization W] [LF.IsLeftDerivedFunctor α W] :
    LF.IsLeftDerivedFunctor (α ≫ e.hom) W := by
  rw [Functor.isLeftDerivedFunctor_iff_isRightKanExtension]
  rw [← Functor.isRightKanExtension_iff_of_iso₂ α (α ≫ e.hom) e (Iso.refl LF)
    (by simp)]
  exact (Functor.isLeftDerivedFunctor_iff_isRightKanExtension LF α W).1 inferInstance

/-! ### The isomorphism of the two functors being derived -/

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O O₀ : Sheaf J CommRingCat.{u}} (f : O ⟶ O₀)
variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
variable [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]

/-- Degreewise extension of scalars followed by degreewise restriction of scalars is the
degreewise tensor product with `O₀`: the degreewise functor of
`Deformation.ComplexLift.restrictExtensionIsoTensorRight`.

The composite of two `CategoryTheory.Functor.mapHomologicalComplex`es is the
`mapHomologicalComplex` of the composite, on the nose, which is why this is a plain
`CategoryTheory.NatIso` and not a transport. -/
def restrictExtensionComplexIso :
    (extensionOfScalars f ⋙
        SheafOfModules.restrictScalars (ringSheafMapOf J f)).mapHomologicalComplex
          (ComplexShape.up ℤ) ≅
      (tensorRight O (restrictUnitOf f)).mapHomologicalComplex (ComplexShape.up ℤ) where
  hom := NatTrans.mapHomologicalComplex (restrictExtensionIsoTensorRight f).hom
    (ComplexShape.up ℤ)
  inv := NatTrans.mapHomologicalComplex (restrictExtensionIsoTensorRight f).inv
    (ComplexShape.up ℤ)
  hom_inv_id := by
    rw [← NatTrans.mapHomologicalComplex_comp, Iso.hom_inv_id,
      NatTrans.mapHomologicalComplex_id]
  inv_hom_id := by
    rw [← NatTrans.mapHomologicalComplex_comp, Iso.inv_hom_id,
      NatTrans.mapHomologicalComplex_id]

/-- The isomorphism of the two functors being derived, read after precomposition with the
homotopy quotient — the shape in which it is built, on cochain complexes. -/
def quotientCompRestrictionIso :
    HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ) ⋙
        (extensionOfScalarsHomotopy.{d₀} f ⋙ restrictionOnDerived.{d, d₀} f) ≅
      HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
        (ComplexShape.up ℤ) ⋙
        tensorRightHomotopy.{d} (restrictUnitOf f) :=
  Functor.isoWhiskerRight (quotientCompExtensionOfScalarsIso.{d₀} f)
      (restrictionOnDerived.{d, d₀} f) ≪≫
    Functor.isoWhiskerLeft (extensionOfScalarsCochainComplex J f)
      ((SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).mapDerivedCategoryFactors) ≪≫
    Functor.isoWhiskerRight (restrictExtensionComplexIso f) DerivedCategory.Q ≪≫
    (quotientCompTensorRightIso.{d} (restrictUnitOf f)).symm

/-- **The two functors being derived are isomorphic.** Derived base change followed by derived
restriction of scalars derives degreewise extension of scalars followed by degreewise
restriction of scalars, and the derived tensor product with `O₀|_O` derives the degreewise
tensor product with it; those two degreewise functors are identified by
`Deformation.ComplexLift.restrictExtensionIsoTensorRight`.

The homotopy category is a quotient of the category of cochain complexes, so this is
`Deformation.ComplexLift.quotientCompRestrictionIso` lifted along the quotient functor. -/
def restrictionCompHomotopyIso :
    extensionOfScalarsHomotopy.{d₀} f ⋙ restrictionOnDerived.{d, d₀} f ≅
      tensorRightHomotopy.{d} (restrictUnitOf f) :=
  Quotient.natIsoLift _ (quotientCompRestrictionIso.{d, d₀} f)

/-! ### The comparison -/

/-- **Derived base change read over `O` is the derived tensor product with `O₀`.** The
isomorphism of functors `D(O) ⥤ D(O)`

`(- ⊗^L_O O₀)|_O ≅ - ⊗^L_O O₀|_O`

for the derived base change constructed by Stacks 0794. Both sides are total left derived
functors, along `Qh`, of functors identified by
`Deformation.ComplexLift.restrictionCompHomotopyIso`, so this is uniqueness of left derived
functors. -/
def restrictExtensionCounitHomotopy :
    DerivedCategory.Qh ⋙
        (derivedExtensionOfScalars.{d, d₀} f ⋙ restrictionOnDerived.{d, d₀} f) ⟶
      tensorRightHomotopy.{d} (restrictUnitOf f) :=
  ((Functor.associator DerivedCategory.Qh (derivedExtensionOfScalars.{d, d₀} f)
        (restrictionOnDerived.{d, d₀} f)).inv ≫
      Functor.whiskerRight (derivedExtensionOfScalarsCounitHomotopy f)
        (restrictionOnDerived.{d, d₀} f)) ≫
    (restrictionCompHomotopyIso.{d, d₀} f).hom

/-- Derived base change followed by derived restriction of scalars is the total left derived
functor of the degreewise tensor product with `O₀|_O`: absoluteness of derived base change,
read through `Deformation.ComplexLift.restrictionCompHomotopyIso`. -/
instance isLeftDerivedFunctor_restrictExtensionCounitHomotopy :
    (derivedExtensionOfScalars.{d, d₀} f ⋙
        restrictionOnDerived.{d, d₀} f).IsLeftDerivedFunctor
      (restrictExtensionCounitHomotopy.{d, d₀} f)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
        (ComplexShape.up ℤ)) :=
  haveI := isLeftDerivedFunctor_comp_derivedExtensionOfScalars.{d, d₀} f
    (restrictionOnDerived.{d, d₀} f)
  isLeftDerivedFunctor_of_targetIso
    ((Functor.associator DerivedCategory.Qh (derivedExtensionOfScalars.{d, d₀} f)
        (restrictionOnDerived.{d, d₀} f)).inv ≫
      Functor.whiskerRight (derivedExtensionOfScalarsCounitHomotopy f)
        (restrictionOnDerived.{d, d₀} f))
    (restrictionCompHomotopyIso.{d, d₀} f)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ))

/-- **Derived base change read over `O` is the derived tensor product with `O₀`.** -/
def derivedRestrictExtensionIso :
    derivedExtensionOfScalars.{d, d₀} f ⋙ restrictionOnDerived.{d, d₀} f ≅
      derivedTensorRight.{d} (restrictUnitOf f) :=
  Functor.leftDerivedUnique _ _ (restrictExtensionCounitHomotopy.{d, d₀} f)
    (derivedTensorRightCounitHomotopy.{d} (restrictUnitOf f))
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ))

/-- **The same comparison for an arbitrary derived base change along `f`.** Any two derived base
changes along `f` are canonically isomorphic, so the identification above transports to the one
chosen in the statements of Tags 0DIY and 0DIZ. -/
def derivedRestrictExtensionIsoOf (T : DerivedExtensionOfScalars.{d, d₀} f) :
    T.baseChange ⋙ restrictionOnDerived.{d, d₀} f ≅
      derivedTensorRight.{d} (restrictUnitOf f) :=
  Functor.isoWhiskerRight
      (DerivedExtensionOfScalars.baseChangeIso T (derivedExtensionOfScalarsData.{d, d₀} f))
      (restrictionOnDerived.{d, d₀} f) ≪≫
    derivedRestrictExtensionIso.{d, d₀} f

end Deformation.ComplexLift

end
