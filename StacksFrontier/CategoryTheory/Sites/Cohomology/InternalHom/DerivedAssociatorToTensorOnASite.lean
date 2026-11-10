module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.AssociatorOnKFlatComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.LeftKFlatResolutions
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseatConstraints
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DualityDescentDiagrams
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.InvertibleDerivedSheafHomCounitOnASite

/-!
# The associativity constraint of `D(O)` against the canonical map to the total tensor complex

Let `(C, O)` be a ringed site and let `A`, `B`, `D` be complexes of `O`-modules.  Write
`t_{A,B} : QA ⊗^𝐋_O QB ⟶ Q(Tot(A ⊗_O B))` for the canonical map of [Stacks, Tag 06YU] from the
derived tensor product to the total tensor complex.  Then

`(t_{A,B} ▷ QD) ≫ t_{A ⊗ B, D} ≫ Q(α_{A,B,D}) = α_{QA,QB,QD} ≫ (QA ◁ t_{B,D}) ≫ t_{A, B ⊗ D}`,

with no flatness hypothesis on `A`, `B` or `D`: the associativity constraint of the monoidal
structure of [Stacks, Tag 0FPT] on `D(O)` is carried by `t` to the associator of total tensor
complexes.

`Stacks.SheafOfModules.derivedAssociator_toTensor` is this statement for a ringed *space*; the
slice site `C/U` of a ringed site is not a ringed space, and the composition law (C) of the
derived-duality cluster -- `AlgebraicGeometry.RingedSite.compositionApplicationLaw` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionApplicationLawOnASite` --
needs it over an arbitrary ringed site.  This file states it there, with the same proof.

## The monoidal structure the statement is read at

`AlgebraicGeometry.RingedSite.derivedTensorMonoidal`, the structure of [Stacks, Tag 0FPT]
re-seated onto `Stacks.SheafOfModules.derivedTensorProductFunctor` by
`Stacks.SheafOfModules.DerivedMonoidal.reseatedDerivedMonoidal`.  Its associator is therefore
`Stacks.SheafOfModules.DerivedTensorProduct.associator` at the canonical datum of
[Stacks, Tag 06YU], on the nose, which is what lets the statement mention the associator and the
canonical map `t` at once: `t` is a morphism out of a bifunctor application, and a goal carrying
both `QA ⊗ QB` and that application is not type-correct at the `implicit` transparency level.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedTensorReseatDatum`: the canonical derived tensor product of
  [Stacks, Tag 06YU] on `D(O)`, read as a derived tensor product over the structure sheaf -- the
  spelling the re-seating isomorphism is stated for, and the one
  `AlgebraicGeometry.RingedSite.derivedTensorMonoidal` is seated on.
* `AlgebraicGeometry.RingedSite.derivedAssociatorHom`,
  `AlgebraicGeometry.RingedSite.derivedWhiskerRight`,
  `AlgebraicGeometry.RingedSite.derivedWhiskerLeft`: the associativity constraint and the two
  whiskerings of that structure, ascribed at the bifunctor spelling of their sources.
* `AlgebraicGeometry.RingedSite.derivedTensorComparisonHom`,
  `AlgebraicGeometry.RingedSite.derivedToTensorHom`: the K-flat comparison and the canonical map
  of [Stacks, Tag 06YU], ascribed at the same spelling.

## Main results

* `AlgebraicGeometry.RingedSite.derivedAssociator_comparison`: the associativity constraint of
  `D(O)` is the associator of total tensor complexes, read through the K-flat comparison on
  K-flat complexes.  This is
  `Stacks.SheafOfModules.DerivedMonoidal.kFlatTensorComparison_associator`, which is already
  stated for an arbitrary prescribed derived tensor product, with the comparison in the pinned
  spelling.
* `AlgebraicGeometry.RingedSite.derivedAssociator_toTensor`: **the identity displayed above**,
  for arbitrary complexes, by descent along K-flat resolutions.

## Nothing here is tagged

[Stacks, Tag 0FPT] is carried by
`Stacks.SheafOfModules.DerivedMonoidal.symmetricMonoidalDerivedTensor` and [Stacks, Tag 06YU] by
the derived tensor product and its comparisons.  A compatibility of the two at a prescribed
bifunctor is not a further part of either, which is the reason
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/AssociatorOnKFlatComplexes.lean`
carries no attribute either.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
  Opposite
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.Cohomology.DualityDescent

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
attribute [local instance 10000] CochainComplex.symmetricCategory
  SheafOfModules.monoidalCategorySheafTensor

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)]

/-- The monoidal structure on `Comp(Mod(O))`, as a top-priority local instance.  The default
search for it has to sift every monoidal instance this file's imports put on the K-flat
subcategories, which costs more than the statements below can afford; naming it answers the
query in one step.  This is the device
`StacksFrontier/CategoryTheory/Sites/Cohomology/Monoidal/DerivedTensorReseatConstraints.lean` uses
for the same query, and for the same reason. -/
local instance (priority := 100000) monoidalCategoryStructComplexesSite :
    MonoidalCategoryStruct
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :=
  inferInstance

/-! ### Pinned spellings -/

/-- **The canonical derived tensor product of [Stacks, Tag 06YU], read as a derived tensor
product over the structure sheaf of the site.**  The two packagings of the datum differ only in
which of two equal abbreviations spells K-flatness; this is the spelling the re-seating
isomorphism `Stacks.SheafOfModules.DerivedMonoidal.derivedTensorMonoidalIso` is stated for, and
it is the datum `AlgebraicGeometry.RingedSite.derivedTensorMonoidal` is seated on. -/
def derivedTensorReseatDatum : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.O :=
  Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)

/-- **The associativity constraint of `AlgebraicGeometry.RingedSite.derivedTensorMonoidal`**,
ascribed at the bifunctor spelling of its source and target.  Pinned so that the statements
below can mention it beside the canonical map `t` of [Stacks, Tag 06YU], whose source is a
bifunctor application: a goal carrying both `A ⊗ B` and that application is not type-correct at
the `implicit` transparency level. -/
def derivedAssociatorHom
    (A B D : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).obj B)).obj D ⟶
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).obj
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj B).obj D) :=
  ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).associator A B D).hom

/-- **Right whiskering for `AlgebraicGeometry.RingedSite.derivedTensorMonoidal`**: the action of
the derived tensor bifunctor in its first variable, which is `▷` of that structure by
construction (`CategoryTheory.MonoidalCategory.reseatStruct`). -/
def derivedWhiskerRight
    {A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (f : A ⟶ B)
    (D : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).obj D ⟶
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj B).obj D :=
  ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map f).app D

/-- **Left whiskering for `AlgebraicGeometry.RingedSite.derivedTensorMonoidal`**: the action of
the derived tensor bifunctor in its second variable, which is `◁` of that structure. -/
def derivedWhiskerLeft
    (A : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {B D : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (g : B ⟶ D) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).obj B ⟶
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).obj D :=
  ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).map g

section Monoidal

attribute [local instance] derivedTensorMonoidal

/-- `AlgebraicGeometry.RingedSite.derivedAssociatorHom` *is* the associator of
`AlgebraicGeometry.RingedSite.derivedTensorMonoidal`. -/
theorem derivedAssociatorHom_eq
    (A B D : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedAssociatorHom X A B D = (α_ A B D).hom :=
  rfl

/-- `AlgebraicGeometry.RingedSite.derivedWhiskerRight` *is* the right whiskering of
`AlgebraicGeometry.RingedSite.derivedTensorMonoidal`. -/
theorem derivedWhiskerRight_eq
    {A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (f : A ⟶ B)
    (D : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedWhiskerRight X f D = f ▷ D :=
  rfl

/-- `AlgebraicGeometry.RingedSite.derivedWhiskerLeft` *is* the left whiskering of
`AlgebraicGeometry.RingedSite.derivedTensorMonoidal`. -/
theorem derivedWhiskerLeft_eq
    (A : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {B D : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (g : B ⟶ D) :
    derivedWhiskerLeft X A g = A ◁ g :=
  rfl

/-- **The associativity constraint of `D(O)` is natural in all three variables**, in the pinned
spelling.  This is `CategoryTheory.MonoidalCategory.associator_naturality`, read with the two
whiskerings written as the actions of the derived tensor bifunctor -- which is what they are, by
`rfl`, for a re-seated monoidal structure. -/
theorem derivedAssociatorHom_naturality
    {A A' B B' D D' :
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (a : A' ⟶ A) (b : B' ⟶ B) (d : D' ⟶ D) :
    derivedWhiskerRight X (derivedWhiskerRight X a B' ≫ derivedWhiskerLeft X A b) D' ≫
        derivedWhiskerLeft X _ d ≫ derivedAssociatorHom X A B D =
      derivedAssociatorHom X A' B' D' ≫ derivedWhiskerRight X a _ ≫
        derivedWhiskerLeft X A (derivedWhiskerRight X b D' ≫ derivedWhiskerLeft X B d) := by
  have h := associator_naturality a b d
  rw [tensorHom_def, tensorHom_def, tensorHom_def, tensorHom_def, Category.assoc] at h
  exact h

end Monoidal

/-! ### The K-flat comparison and the canonical map -/

/-- **The K-flat comparison of [Stacks, Tag 06YU]**, ascribed at the bifunctor spelling of its
source and at the `⊗` spelling of its target.  Pinned, so that the associativity clause below
can mention it four times beside the associativity constraint without re-elaborating the
comparison each time -- the device
`StacksFrontier/CategoryTheory/Sites/Cohomology/Monoidal/DerivedTensorReseatConstraints.lean` uses
for the same query. -/
def derivedTensorComparisonHom
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.KFlat X.O A)
    (hB : Stacks.SheafOfModules.KFlat X.O B) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          (DerivedCategory.Q.obj A)).obj (DerivedCategory.Q.obj B) ⟶
      DerivedCategory.Q.obj
        ((A ⊗ B :
          CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)) :=
  ((derivedTensorReseatDatum X).comparison A B hA hB).hom

/-- **The re-seating isomorphism carries the pinned K-flat comparison to the tensorator of the
K-flat localization**, which is what makes the constraints of
`AlgebraicGeometry.RingedSite.derivedTensorMonoidal` computable.  This is
`Stacks.SheafOfModules.DerivedMonoidal.reseatIso_comp_comparison` at the prescribed datum
`AlgebraicGeometry.RingedSite.derivedTensorReseatDatum`, with the re-seating isomorphism written
at the name `Stacks.SheafOfModules.DerivedMonoidal.derivedTensorMonoidalIso` that
`AlgebraicGeometry.RingedSite.derivedTensorMonoidal` is defined at.

It is a separate declaration, and that is not decoration: the existing clause is stated at the
*composite* `derivedTensorBifunctorIso ≪≫ derivedBifunctorTensorIso`, and recognising that
composite as `derivedTensorMonoidalIso` costs a definitional unfolding which, done four times
inside the associativity clause below, exhausts that declaration's heartbeat budget.  Done once
here it is free. -/
theorem reseatIso_comp_derivedTensorComparisonHom
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.KFlat X.O A)
    (hB : Stacks.SheafOfModules.KFlat X.O B) :
    letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O
    (reseatIso (Stacks.SheafOfModules.DerivedMonoidal.derivedTensorMonoidalIso X.O
            (derivedTensorReseatDatum X))
          (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)).hom ≫
        derivedTensorComparisonHom X A B hA hB =
      (CochainComplex.KFlatMonoidal.derivedTensorIso
        (Stacks.SheafOfModules.DerivedMonoidal.Mod X.O)
        (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution X.O) hA hB).hom :=
  Stacks.SheafOfModules.DerivedMonoidal.reseatIso_comp_comparison X.O
    (derivedTensorReseatDatum X) A B hA hB

/-- **The associativity clause of [Stacks, Tag 0FPT] at the re-seating onto the canonical
derived tensor product of [Stacks, Tag 06YU]**, as a proposition.  The statement is a `def`
rather than being inlined in the theorem below for the reason
`Stacks.SheafOfModules.DerivedMonoidal.CanonicalComparisonAssociator` gives for its own: at a
concrete monoidal category, elaborating this equation and then the proof term in one declaration
costs more than the heartbeat budget allows. -/
def DerivedAssociatorComparison
    (A B D : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.KFlat X.O A)
    (hB : Stacks.SheafOfModules.KFlat X.O B)
    (hD : Stacks.SheafOfModules.KFlat X.O D) : Prop :=
  derivedWhiskerRight X (derivedTensorComparisonHom X A B hA hB) (DerivedCategory.Q.obj D) ≫
      derivedTensorComparisonHom X (A ⊗ B) D
          (Stacks.SheafOfModules.DerivedMonoidal.kFlat_tensor_complexes X.O hA hB) hD ≫
        Stacks.SheafOfModules.DerivedMonoidal.complexAssociatorHom X.O A B D =
    derivedAssociatorHom X (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)
          (DerivedCategory.Q.obj D) ≫
      derivedWhiskerLeft X (DerivedCategory.Q.obj A) (derivedTensorComparisonHom X B D hB hD) ≫
        derivedTensorComparisonHom X A (B ⊗ D) hA
          (Stacks.SheafOfModules.DerivedMonoidal.kFlat_tensor_complexes X.O hB hD)

/-- **The associativity constraint of `D(O)` is the associator of total tensor complexes**,
carried across by the K-flat comparison of [Stacks, Tag 06YU]: on the classes of K-flat
complexes `A`, `B`, `D`,

`(cmp A B) ▷ QD ≫ (cmp (A ⊗ B) D) ≫ Q(α_ A B D).hom =`
`  α_{QA,QB,QD} ≫ (QA ◁ (cmp B D)) ≫ (cmp A (B ⊗ D))`,

the equation spelled out in `AlgebraicGeometry.RingedSite.DerivedAssociatorComparison`.

This is a single application of
`CategoryTheory.MonoidalCategory.reseat_associator_comp_of_eq` to
`CochainComplex.KFlatMonoidal.associator_derivedTensorIso`, with the four comparisons read
through the re-seating isomorphism by `reseatIso_comp_derivedTensorComparisonHom`.  The
ringed-space form is `Stacks.SheafOfModules.derivedAssociator_comparison`. -/
theorem derivedAssociator_comparison
    (A B D : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.KFlat X.O A)
    (hB : Stacks.SheafOfModules.KFlat X.O B)
    (hD : Stacks.SheafOfModules.KFlat X.O D) :
    DerivedAssociatorComparison X A B D hA hB hD :=
  let := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O
  reseat_associator_comp_of_eq
    (Stacks.SheafOfModules.DerivedMonoidal.derivedTensorMonoidalIso X.O
      (derivedTensorReseatDatum X))
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso X.O)
    (Stacks.SheafOfModules.DerivedMonoidal.complexAssociatorHom X.O A B D)
    (reseatIso_comp_derivedTensorComparisonHom X A B hA hB)
    (reseatIso_comp_derivedTensorComparisonHom X B D hB hD)
    (reseatIso_comp_derivedTensorComparisonHom X (A ⊗ B) D
      (Stacks.SheafOfModules.DerivedMonoidal.kFlat_tensor_complexes X.O hA hB) hD)
    (reseatIso_comp_derivedTensorComparisonHom X A (B ⊗ D) hA
      (Stacks.SheafOfModules.DerivedMonoidal.kFlat_tensor_complexes X.O hB hD))
    (CochainComplex.KFlatMonoidal.associator_derivedTensorIso
      (Stacks.SheafOfModules.DerivedMonoidal.Mod X.O)
      (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution X.O) hA hB hD)

/-- **The canonical map of [Stacks, Tag 06YU]** from the derived tensor product to the total
tensor complex, at the `⊗` spelling of its target. -/
def derivedToTensorHom
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          (DerivedCategory.Q.obj A)).obj (DerivedCategory.Q.obj B) ⟶
      DerivedCategory.Q.obj
        ((A ⊗ B :
          CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)) :=
  (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).toTensor A B

/-- On two K-flat complexes the canonical map is the K-flat comparison. -/
theorem derivedToTensorHom_eq_comparisonHom
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.KFlat X.O A)
    (hB : Stacks.SheafOfModules.KFlat X.O B) :
    derivedToTensorHom X A B = derivedTensorComparisonHom X A B hA hB := by
  rw [derivedToTensorHom, derivedTensorComparisonHom,
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).toTensor_eq_comparisonRight A B hB,
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight_eq_comparison
      A B hA hB]
  rfl

/-- The canonical map is natural in both complexes. -/
theorem derivedToTensorHom_naturality
    {A A' B B' :
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : A ⟶ A') (g : B ⟶ B') :
    derivedWhiskerRight X (DerivedCategory.Q.map f) (DerivedCategory.Q.obj B) ≫
        derivedWhiskerLeft X (DerivedCategory.Q.obj A') (DerivedCategory.Q.map g) ≫
        derivedToTensorHom X A' B' =
      derivedToTensorHom X A B ≫ DerivedCategory.Q.map (f ⊗ₘ g) :=
  (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).toTensor_naturality f g

omit [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
  HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)] in
/-- The associator of total tensor complexes is natural in all three complexes. -/
theorem complexAssociatorHom_naturality
    {A A' B B' D D' :
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (a : A' ⟶ A) (b : B' ⟶ B) (d : D' ⟶ D) :
    DerivedCategory.Q.map ((a ⊗ₘ b) ⊗ₘ d) ≫
        Stacks.SheafOfModules.DerivedMonoidal.complexAssociatorHom X.O A B D =
      Stacks.SheafOfModules.DerivedMonoidal.complexAssociatorHom X.O A' B' D' ≫
        DerivedCategory.Q.map (a ⊗ₘ (b ⊗ₘ d)) := by
  rw [Stacks.SheafOfModules.DerivedMonoidal.complexAssociatorHom_eq,
    Stacks.SheafOfModules.DerivedMonoidal.complexAssociatorHom_eq,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    associator_naturality a b d]

/-- `derivedAssociator_comparison` with the K-flat comparisons written as the canonical map
`AlgebraicGeometry.RingedSite.derivedToTensorHom`. -/
theorem derivedAssociator_toTensor_of_kFlat
    (A B D : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.KFlat X.O A)
    (hB : Stacks.SheafOfModules.KFlat X.O B)
    (hD : Stacks.SheafOfModules.KFlat X.O D) :
    derivedWhiskerRight X (derivedToTensorHom X A B) (DerivedCategory.Q.obj D) ≫
        derivedToTensorHom X (A ⊗ B) D ≫
          Stacks.SheafOfModules.DerivedMonoidal.complexAssociatorHom X.O A B D =
      derivedAssociatorHom X (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)
          (DerivedCategory.Q.obj D) ≫
        derivedWhiskerLeft X (DerivedCategory.Q.obj A) (derivedToTensorHom X B D) ≫
          derivedToTensorHom X A (B ⊗ D) := by
  rw [derivedToTensorHom_eq_comparisonHom X A B hA hB,
    derivedToTensorHom_eq_comparisonHom X B D hB hD,
    derivedToTensorHom_eq_comparisonHom X (A ⊗ B) D
      (Stacks.SheafOfModules.DerivedMonoidal.kFlat_tensor_complexes X.O hA hB) hD,
    derivedToTensorHom_eq_comparisonHom X A (B ⊗ D) hA
      (Stacks.SheafOfModules.DerivedMonoidal.kFlat_tensor_complexes X.O hB hD)]
  exact derivedAssociator_comparison X A B D hA hB hD

/-- **The associativity constraint of `D(O)` is the associator of total tensor complexes**,
carried across by the canonical map `t` of [Stacks, Tag 06YU]: for arbitrary complexes `A`, `B`,
`D` of `O`-modules,

`(t_{A,B} ▷ QD) ≫ t_{A ⊗ B, D} ≫ Q(α_{A,B,D}) = α_{QA,QB,QD} ≫ (QA ◁ t_{B,D}) ≫ t_{A, B ⊗ D}`.

This is `derivedAssociator_comparison` at K-flat resolutions of `A`, `B` and `D`, carried back
along the resolutions by the naturality of `t` and of both associators, which is
`Stacks.Cohomology.DualityDescent.assoc_descent`.  The ringed-space form is
`Stacks.SheafOfModules.derivedAssociator_toTensor`. -/
theorem derivedAssociator_toTensor
    (A B D : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    derivedWhiskerRight X (derivedToTensorHom X A B) (DerivedCategory.Q.obj D) ≫
        derivedToTensorHom X (A ⊗ B) D ≫
          Stacks.SheafOfModules.DerivedMonoidal.complexAssociatorHom X.O A B D =
      derivedAssociatorHom X (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)
          (DerivedCategory.Q.obj D) ≫
        derivedWhiskerLeft X (DerivedCategory.Q.obj A) (derivedToTensorHom X B D) ≫
          derivedToTensorHom X A (B ⊗ D) := by
  obtain ⟨A', a, hA', _⟩ := Stacks.DerivedTensor.RingedSite.exists_kFlat_quasiIso X.O A
  obtain ⟨B', b, hB', _⟩ := Stacks.DerivedTensor.RingedSite.exists_kFlat_quasiIso X.O B
  obtain ⟨D', d, hD', _⟩ := Stacks.DerivedTensor.RingedSite.exists_kFlat_quasiIso X.O D
  exact assoc_descent (Stacks.SheafOfModules.derivedTensorProductFunctor X)
    (DerivedCategory.Q.map a) (DerivedCategory.Q.map b) (DerivedCategory.Q.map d)
    (derivedToTensorHom X A B) (derivedToTensorHom X A' B')
    (DerivedCategory.Q.map (a ⊗ₘ b)) (derivedToTensorHom_naturality X a b)
    (derivedToTensorHom X B D) (derivedToTensorHom X B' D')
    (DerivedCategory.Q.map (b ⊗ₘ d)) (derivedToTensorHom_naturality X b d)
    (derivedToTensorHom X (A ⊗ B) D) (derivedToTensorHom X (A' ⊗ B') D')
    (DerivedCategory.Q.map ((a ⊗ₘ b) ⊗ₘ d)) (derivedToTensorHom_naturality X (a ⊗ₘ b) d)
    (derivedToTensorHom X A (B ⊗ D)) (derivedToTensorHom X A' (B' ⊗ D'))
    (DerivedCategory.Q.map (a ⊗ₘ (b ⊗ₘ d))) (derivedToTensorHom_naturality X a (b ⊗ₘ d))
    (Stacks.SheafOfModules.DerivedMonoidal.complexAssociatorHom X.O A B D)
    (Stacks.SheafOfModules.DerivedMonoidal.complexAssociatorHom X.O A' B' D')
    (complexAssociatorHom_naturality X a b d)
    (derivedAssociatorHom X _ _ _) (derivedAssociatorHom X _ _ _)
    (derivedAssociatorHom_naturality X _ _ _)
    (derivedAssociator_toTensor_of_kFlat X A' B' D' hA' hB' hD')

end AlgebraicGeometry.RingedSite

end
