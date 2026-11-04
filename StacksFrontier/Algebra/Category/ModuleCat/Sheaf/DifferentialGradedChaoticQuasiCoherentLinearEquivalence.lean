module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedRestrictionTriangulated
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticQuasiCoherentQuasiIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConstantQuasiCoherent
public import StacksFrontier.CategoryTheory.Triangulated.LinearTriangulatedEquivalence

/-!
# `QC(A, d) ≃ QC(B, d)` as `R`-linear triangulated categories

Let `C` be a category with the chaotic topology, `R` a commutative ring and `φ : A ⟶ B` a
unit-preserving homomorphism of sheaves of differential graded algebras over the constant sheaf
of rings with value `R`. Restriction of scalars along `φ` does not change the underlying
sheaves, so it commutes with multiplication by every `r ∈ R`; it is therefore `R`-linear on the
modules, on the homotopy categories and, along the localization functors, on the derived
categories. When `φ` induces an isomorphism on cohomology sheaves, the equivalence
`QC(A, d) ≌ QC(B, d)` of Tag 0GZF has derived restriction of scalars as quasi-inverse, which
commutes with the translations, is triangulated and is `R`-linear; so the equivalence is an
equivalence of `R`-linear triangulated categories, the form in which Remark 0H1E uses it.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.Chaotic.constQCDerivedRestriction`: the functor
  `QC(B, d) ⥤ QC(A, d)` induced by derived restriction of scalars, over the constant sheaf of
  rings.
* `….Chaotic.qcDerivedRestrictionLinearTriangulatedEquivalence`:
  the equivalence `QC(B, d) ≌ QC(A, d)` given by derived restriction of scalars.

## Main results

* `SheafOfModules.DifferentialGradedModule.derivedRestriction_linear`: derived restriction of
  scalars is `R`-linear.
* `….Chaotic.qcDerivedExtensionLinearTriangulatedEquivalence`:
  **the equivalence `QC(A, d) ≌ QC(B, d)` of Tag 0GZF as an equivalence of `R`-linear
  triangulated categories.**

## References

* [Stacks Project, Lemma 24.34.2 (Tag 0GZF)](https://stacks.math.columbia.edu/tag/0GZF)
* [Stacks Project, Remark 24.35.5 (Tag 0H1E)](https://stacks.math.columbia.edu/tag/0H1E)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace SheafOfModules.DifferentialGradedModule

open Stacks.ChaoticSite

variable {C : Type u} [Category.{u} C] {R : Type u} [CommRing R]
  {A B : DifferentialGradedAlgebra.{u, u} (Stacks.PresheafOfModules.constRingSheaf (C := C) R)}
  (φ : A ⟶ B) (hφ : φ.PreservesOne)

/-- Restriction of scalars commutes with multiplication by `r ∈ R`. -/
theorem restriction_map_scalarEnd (r : R) (N : DifferentialGradedModule.{u, u, u} B) :
    (restriction.{u, u, u} φ hφ).map (scalarEnd r N) =
      scalarEnd r ((restriction.{u, u, u} φ hφ).obj N) :=
  rfl

/-- Restriction of scalars on right differential graded modules is `R`-linear. -/
instance restriction_linear : (restriction.{u, u, u} φ hφ).Linear R where
  map_smul f r := by
    rw [smul_eq_scalarEnd_comp, smul_eq_scalarEnd_comp, Functor.map_comp,
      restriction_map_scalarEnd]

/-- Restriction of scalars on the homotopy categories is `R`-linear. -/
instance homotopyRestriction_linear : (homotopyRestriction.{u, u, u} φ hφ).Linear R where
  map_smul f r := by
    obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient B).map_surjective f
    rw [← Functor.map_smul, homotopyRestriction_map_quotient_map,
      homotopyRestriction_map_quotient_map, Functor.map_smul, Functor.map_smul]
    rfl

/-- Restriction of scalars on the derived categories is the localization lift of restriction of
scalars on the homotopy categories followed by the localization functor of `D(A, d)`, over the
constant sheaf of rings. -/
instance const_derivedRestriction_lifting :
    Localization.Lifting (toDerivedCategory.{u, u, u} B) (quasiIsomorphisms.{u, u, u} B)
      (homotopyRestriction.{u, u, u} φ hφ ⋙ toDerivedCategory.{u, u, u} A)
      (derivedRestriction.{u, u, u} φ hφ) :=
  derivedRestriction_lifting (X := constRingedSite C R) φ hφ

/-- Restriction of scalars on the homotopy categories commutes with the translations, over the
constant sheaf of rings. -/
@[instance_reducible]
instance const_homotopyRestriction_commShift :
    (homotopyRestriction.{u, u, u} φ hφ).CommShift ℤ :=
  homotopyRestriction_commShift (X := constRingedSite C R) φ hφ

/-- Restriction of scalars on the derived categories commutes with the translations, over the
constant sheaf of rings. -/
@[instance_reducible]
instance const_derivedRestriction_commShift :
    (derivedRestriction.{u, u, u} φ hφ).CommShift ℤ :=
  derivedRestriction_commShift (X := constRingedSite C R) φ hφ

/-- Restriction of scalars on the derived categories is triangulated, over the constant sheaf of
rings. -/
instance const_derivedRestriction_isTriangulated :
    (derivedRestriction.{u, u, u} φ hφ).IsTriangulated :=
  derivedRestriction_isTriangulated (X := constRingedSite C R) φ hφ

/-- **Restriction of scalars on the derived categories is `R`-linear**, because it is the
localization lift of an `R`-linear functor. -/
instance derivedRestriction_linear : (derivedRestriction.{u, u, u} φ hφ).Linear R :=
  (Localization.functor_linear_iff (toDerivedCategory.{u, u, u} B)
    (quasiIsomorphisms.{u, u, u} B) R
    (homotopyRestriction.{u, u, u} φ hφ ⋙ toDerivedCategory.{u, u, u} A)
    (derivedRestriction.{u, u, u} φ hφ)).1 inferInstance

namespace Chaotic

variable (hqis : φ.IsQuasiIso)

/-- The functor `QC(B, d) ⥤ QC(A, d)` induced by derived restriction of scalars, over the constant
sheaf of rings: this is `qcDerivedRestriction`, with the categories read over the constant sheaf
of rings, so that their triangulated and `R`-linear structures are found by instance search. -/
def constQCDerivedRestriction : (QC B).FullSubcategory ⥤ (QC A).FullSubcategory :=
  ObjectProperty.lift (QC A) (QCι B ⋙ derivedRestriction.{u, u, u} φ hφ)
    fun X ↦ qc_derivedRestriction (O := Stacks.PresheafOfModules.constCommRingSheaf (C := C) R)
      φ hφ hqis X.property

/-- `constQCDerivedRestriction` is the functor induced by derived restriction of scalars. -/
theorem constQCDerivedRestriction_eq :
    constQCDerivedRestriction φ hφ hqis =
      qcDerivedRestriction (O := Stacks.PresheafOfModules.constCommRingSheaf (C := C) R)
        φ hφ hqis :=
  rfl

/-- The functor `QC(B, d) ⥤ QC(A, d)` induced by derived restriction of scalars commutes with
the translations. -/
@[instance_reducible]
instance constQCDerivedRestriction_commShift :
    (constQCDerivedRestriction φ hφ hqis).CommShift ℤ :=
  Functor.CommShift.ofComp ((QC A).liftCompιIso _ _) ℤ

/-- The functor `QC(B, d) ⥤ QC(A, d)` induced by derived restriction of scalars is
triangulated. -/
instance constQCDerivedRestriction_isTriangulated :
    (constQCDerivedRestriction φ hφ hqis).IsTriangulated :=
  haveI : NatTrans.CommShift (F₁ := constQCDerivedRestriction φ hφ hqis ⋙ QCι A)
      ((QC A).liftCompιIso (QCι B ⋙ derivedRestriction.{u, u, u} φ hφ)
        fun X ↦ qc_derivedRestriction (O := Stacks.PresheafOfModules.constCommRingSheaf (C := C) R)
          φ hφ hqis X.property).hom ℤ :=
    Functor.CommShift.ofComp_compatibility _ _
  (Functor.isTriangulated_iff_comp_right (F := constQCDerivedRestriction φ hφ hqis)
    ((QC A).liftCompιIso _ _)).2 inferInstance

/-- The functor `QC(B, d) ⥤ QC(A, d)` induced by derived restriction of scalars is
`R`-linear. -/
instance constQCDerivedRestriction_linear : (constQCDerivedRestriction φ hφ hqis).Linear R where
  map_smul f r := by
    ext
    exact (derivedRestriction.{u, u, u} φ hφ).map_smul r f.hom

/-- The equivalence `QC(B, d) ≌ QC(A, d)` given by derived restriction of scalars, the inverse of
the equivalence of Tag 0GZF, as an equivalence of `R`-linear triangulated categories. -/
def qcDerivedRestrictionLinearTriangulatedEquivalence :
    LinearTriangulatedEquivalence R (QC B).FullSubcategory (QC A).FullSubcategory where
  equivalence :=
    (qcDerivedExtensionEquivalence (O := Stacks.PresheafOfModules.constCommRingSheaf (C := C) R)
      φ hφ hqis).symm
  commShift := constQCDerivedRestriction_commShift φ hφ hqis
  isTriangulated := constQCDerivedRestriction_isTriangulated φ hφ hqis
  linear := constQCDerivedRestriction_linear φ hφ hqis

/-- The functor of `qcDerivedRestrictionLinearTriangulatedEquivalence` is the functor induced by
derived restriction of scalars. -/
theorem qcDerivedRestrictionLinearTriangulatedEquivalence_functor :
    (qcDerivedRestrictionLinearTriangulatedEquivalence φ hφ hqis).equivalence.functor =
      qcDerivedRestriction (O := Stacks.PresheafOfModules.constCommRingSheaf (C := C) R)
        φ hφ hqis :=
  rfl

/-- **The equivalence `QC(A, d) ≌ QC(B, d)` of Tag 0GZF, as an equivalence of `R`-linear
triangulated categories**: derived extension of scalars, with derived restriction of scalars as
quasi-inverse, the latter commuting with the translations, triangulated and `R`-linear. -/
def qcDerivedExtensionLinearTriangulatedEquivalence :
    LinearTriangulatedEquivalence R (QC A).FullSubcategory (QC B).FullSubcategory :=
  (qcDerivedRestrictionLinearTriangulatedEquivalence φ hφ hqis).symm

/-- The underlying equivalence of `qcDerivedExtensionLinearTriangulatedEquivalence` is the
equivalence of Tag 0GZF. -/
theorem qcDerivedExtensionLinearTriangulatedEquivalence_equivalence :
    (qcDerivedExtensionLinearTriangulatedEquivalence φ hφ hqis).equivalence =
      qcDerivedExtensionEquivalence (O := Stacks.PresheafOfModules.constCommRingSheaf (C := C) R)
        φ hφ hqis :=
  rfl

end Chaotic

end SheafOfModules.DifferentialGradedModule
