module

public import StacksFrontier.RingTheory.Dualizing.TrivialDuality
public import StacksFrontier.Algebra.Homology.DerivedCategory.EssentiallyConstant
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Homology.HomComplex.RHom
public import StacksFrontier.Homology.HomComplex.TensorHom
public import StacksFrontier.Homology.KInjective.ChangeOfRings
public import StacksCore.Tactic.StacksAttribute
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-!
# Derived Hom and restriction of scalars

For a homomorphism of commutative rings `f : A →+* B`, restriction of scalars identifies the
derived coextension `RHom(B, -) : D(A) ⥤ D(B)`, read in `D(A)`, with the `A`-valued derived
functor `RHom_A(B, -)`. This module sets up the two functors being compared, the comparison of
their derived units, and the resulting isomorphism.

## Main definitions

* `Dualizing.coextendScalarsToDerivedCategory` — coextension of scalars on the homotopy
  category, followed by localization.
* `Dualizing.homAlongToDerivedCategory` — the `A`-valued Hom functor, likewise.
* `Dualizing.homAlongRestrictScalarsIso` — the identity on underlying complexes of
  `A`-modules.
* `Dualizing.restrictedDerivedUnit` — the derived unit for restricted coextension.
* `Dualizing.coextendSingleUnit` — the induced map `Hom_A(B, M) → H^q(RHom(B, M[-q]))`.
* `Dualizing.HomologyExtComparison` — the specification of a natural, normalized Ext
  identification for a derived coextension functor.

## Main results

* `Dualizing.restrictScalars_mapDerivedCategory_isLeftAdjoint` — restriction of scalars on
  derived categories is a left adjoint, in any model.
* `Dualizing.derivedCoextendScalarsCompDerivedRestrictScalarsIso` — the natural isomorphism
  `RHom(B, -) ∘ restriction ≅ RHom_A(B, -)`, compatible with the right-derived-functor units.

## Implementation notes

Right-derived functors are specified by their universal properties, which allows arbitrary
models and independent universes for modules and derived morphisms. In particular this applies
to `Dualizing.derivedHom`; restriction is Mathlib's `Functor.mapDerivedCategory`. The
isomorphism carries its unit compatibility, hence agrees with the identity on `Hom_A(B, I)` for
K-injective complexes.

Both derived functors are constructed elsewhere and the comparison is stated with nothing
assumed in
`StacksFrontier/RingTheory/Dualizing/CoextendRestrictComparison/Constructed.lean`, as
`Dualizing.restrictDerivedHomIsoDerivedHomAlong` and
`Dualizing.derivedHomHomologyLinearEquivExt`.

## References

* [Stacks Project, Tag 0A71](https://stacks.math.columbia.edu/tag/0A71)
-/

@[expose] public section

open CategoryTheory

universe u v wA wB

namespace Dualizing

noncomputable section

variable {A B : Type u} [CommRing A] [CommRing B]
  [HasDerivedCategory.{wA} (ModuleCat.{max v u} A)]
  [HasDerivedCategory.{wB} (ModuleCat.{max v u} B)]

/-- Coextension of scalars on the homotopy category, followed by localization. -/
abbrev coextendScalarsToDerivedCategory (f : A →+* B) :
    HomotopyCategory (ModuleCat.{max v u} A) (.up ℤ) ⥤
      DerivedCategory (ModuleCat.{max v u} B) :=
  (ModuleCat.coextendScalars.{u, u, max v u} f).mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh

/-- The `A`-valued Hom functor on the homotopy category, followed by localization. -/
abbrev homAlongToDerivedCategory (f : A →+* B) :
    HomotopyCategory (ModuleCat.{max v u} A) (.up ℤ) ⥤
      DerivedCategory (ModuleCat.{max v u} A) :=
  (ModuleCat.coextendScalars.{u, u, max v u} f ⋙
      ModuleCat.restrictScalars f).mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh

/-- Module complexes admit K-injective resolutions, so derived coextension exists in any
chosen model of the derived categories. -/
instance coextendScalarsToDerivedCategory_hasPointwiseRightDerivedFunctor (f : A →+* B) :
    (coextendScalarsToDerivedCategory.{u, v, wB} f).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (.up ℤ)) := by
  have := ModuleCat.enoughInjectives A
  exact (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      max v u, wB, max v u, max (u + 1) (v + 1), max (u + 1) (v + 1),
      max (u + 1) (v + 1)}
    (coextendScalarsToDerivedCategory.{u, v, wB} f) (fun K ↦ by
      obtain ⟨I, g, hg, hI⟩ := CochainComplex.exists_quasiIso_isKInjective K
      exact ⟨I, g, hI, hg⟩)).1

/-- The identity on the underlying complexes of `A`-modules. -/
def homAlongRestrictScalarsIso (f : A →+* B) :
    homAlongToDerivedCategory f ≅ coextendScalarsToDerivedCategory f ⋙
      (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory :=
  Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (ModuleCat.coextendScalars f ⋙ ModuleCat.restrictScalars f))
        (.up ℤ)).symm DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (ModuleCat.restrictScalars f).mapDerivedCategoryFactorsh.symm ≪≫
    (Functor.associator _ _ _).symm

variable (f : A →+* B)
  (RF : DerivedCategory (ModuleCat.{max v u} A) ⥤
    DerivedCategory (ModuleCat.{max v u} B))
  (α : coextendScalarsToDerivedCategory f ⟶ DerivedCategory.Qh ⋙ RF)

/-- The derived unit for restricted coextension, induced by the identity on underlying Hom. -/
def restrictedDerivedUnit : homAlongToDerivedCategory f ⟶ DerivedCategory.Qh ⋙
    (RF ⋙ (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory) :=
  (homAlongRestrictScalarsIso f).hom ≫
    Functor.whiskerRight α (ModuleCat.restrictScalars f).mapDerivedCategory ≫
    (Functor.associator _ _ _).hom

/-- The derived unit induces `Hom_A(B, M) → H^q(RHom(B, M[-q]))`. -/
def coextendSingleUnit (M : ModuleCat.{max v u} A) (q : ℤ) :
    (ModuleCat.coextendScalars.{u, u, max v u} f).obj M ⟶
      (DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).obj
        (RF.obj ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) q).obj M)) := by
  let F := ModuleCat.coextendScalars.{u, u, max v u} f
  let S := (CochainComplex.singleFunctor (ModuleCat.{max v u} A) q).obj M
  let T := (HomotopyCategory.quotient _ _).obj S
  let e := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) q).app M
  exact (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) q (F.obj M)).inv ≫
    (HomologicalComplex.homologyFunctor _ _ q).map e.inv ≫
    (DerivedCategory.homologyFunctorFactors _ q).inv.app _ ≫
    (DerivedCategory.homologyFunctor _ q).map
      ((DerivedCategory.quotientCompQhIso _).inv.app _ ≫
        DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).inv.app S)) ≫
    (DerivedCategory.homologyFunctor _ q).map (α.app T) ≫
    (DerivedCategory.homologyFunctor _ q).map
      (RF.map ((DerivedCategory.quotientCompQhIso _).hom.app S))

/-- A natural Ext identification, normalized by the image of the identity of `B` under the
derived unit on `B[-q]`. -/
structure HomologyExtComparison where
  /-- The linear identification in each degree and at each derived object. -/
  linearEquiv (K : DerivedCategory (ModuleCat.{max v u} A)) (q : ℤ) :
    ((ModuleCat.restrictScalars f).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).obj (RF.obj K)) :
        Type (max v u)) ≃ₗ[A]
      DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
          ((ModuleCat.restrictScalars f).obj (ModuleCat.of B (ULift.{v} B)))) K q
  /-- Naturality in the derived argument. -/
  naturality {K L : DerivedCategory (ModuleCat.{max v u} A)} (g : K ⟶ L) (q : ℤ)
      (x : (DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).obj (RF.obj K)) :
    linearEquiv L q
        (((DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).map (RF.map g)) x) =
      linearEquiv K q x ≫ (shiftFunctor _ q).map g
  /-- Normalization on a morphism from the single-term complex `B[-q]`. -/
  unit_app (K : DerivedCategory (ModuleCat.{max v u} A)) (q : ℤ)
      (g : (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) q).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of B (ULift.{v} B))) ⟶ K) :
    linearEquiv K q
        (((DerivedCategory.homologyFunctor (ModuleCat.{max v u} B) q).map (RF.map g))
          ((coextendSingleUnit f RF α _ q)
            (((ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f).unit.app
              (ModuleCat.of B (ULift.{v} B))) (ULift.up 1)))) =
      (((DerivedCategory.singleFunctors (ModuleCat.{max v u} A)).shiftIso q 0 q
        (by simp)).inv.app _) ≫ (shiftFunctor _ q).map g

/-- Restriction of scalars on derived categories, for explicitly given models. -/
private abbrev restrictDerived {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (hA : HasDerivedCategory.{wA} (ModuleCat.{max v u} A))
    (hB : HasDerivedCategory.{wB} (ModuleCat.{max v u} B)) :
    @DerivedCategory (ModuleCat.{max v u} B) _ _ hB ⥤
      @DerivedCategory (ModuleCat.{max v u} A) _ _ hA :=
  letI := hA
  letI := hB
  (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory

/-- Restriction of scalars on derived categories factors through the homotopy categories. -/
private def restrictDerivedFactorsh {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (hA : HasDerivedCategory.{wA} (ModuleCat.{max v u} A))
    (hB : HasDerivedCategory.{wB} (ModuleCat.{max v u} B)) :
    (@DerivedCategory.Qh (ModuleCat.{max v u} B) _ _ hB) ⋙ restrictDerived f hA hB ≅
      (ModuleCat.restrictScalars.{max v u} f).mapHomotopyCategory (.up ℤ) ⋙
        @DerivedCategory.Qh (ModuleCat.{max v u} A) _ _ hA :=
  letI := hA
  letI := hB
  Functor.mapDerivedCategoryFactorsh (ModuleCat.restrictScalars.{max v u} f)

omit [HasDerivedCategory.{wA} (ModuleCat.{max v u} A)]
  [HasDerivedCategory.{wB} (ModuleCat.{max v u} B)] in
/-- Restriction of scalars read on derived categories is a left adjoint, in any model of the
derived categories: the statement transports from the standard model along the uniqueness of
localizations. -/
theorem restrictScalars_mapDerivedCategory_isLeftAdjoint
    [ha : HasDerivedCategory.{wA} (ModuleCat.{max v u} A)]
    [hb : HasDerivedCategory.{wB} (ModuleCat.{max v u} B)]
    (f : A →+* B) :
    (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory.IsLeftAdjoint := by
  let hAs := HasDerivedCategory.standard (ModuleCat.{max v u} A)
  let hBs := HasDerivedCategory.standard (ModuleCat.{max v u} B)
  let QAa := @DerivedCategory.Qh (ModuleCat.{max v u} A) _ _ ha
  let QBa := @DerivedCategory.Qh (ModuleCat.{max v u} B) _ _ hb
  let QAs := @DerivedCategory.Qh (ModuleCat.{max v u} A) _ _ hAs
  let QBs := @DerivedCategory.Qh (ModuleCat.{max v u} B) _ _ hBs
  let WA := HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (.up ℤ)
  let WB := HomotopyCategory.quasiIso (ModuleCat.{max v u} B) (.up ℤ)
  let eA := Localization.uniq QAs QAa WA
  let eB := Localization.uniq QBs QBa WB
  let F : @DerivedCategory (ModuleCat.{max v u} B) _ _ hb ⥤
      @DerivedCategory (ModuleCat.{max v u} A) _ _ ha :=
    eB.inverse ⋙ restrictDerived f hAs hBs ⋙ eA.functor
  have : F.IsLeftAdjoint := (eB.symm.toAdjunction.comp
    ((Classical.choice (restrictScalarsDerived_adj_derivedHom.{u, v} f)).comp
      eA.toAdjunction)).isLeftAdjoint
  have preIso : QBa ⋙ F ≅ QBa ⋙ restrictDerived f ha hb :=
    (Functor.associator QBa eB.inverse (restrictDerived f hAs hBs ⋙ eA.functor)).symm ≪≫
      Functor.isoWhiskerRight (Localization.compUniqFunctor QBs QBa WB).symm.compInverseIso _ ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (restrictDerivedFactorsh f hAs hBs) eA.functor ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Localization.compUniqFunctor QAs QAa WA) ≪≫
      (restrictDerivedFactorsh f ha hb).symm
  exact Functor.isLeftAdjoint_of_iso
    (Localization.liftNatIso QBa WB (QBa ⋙ F) (QBa ⋙ restrictDerived f ha hb) F
      (restrictDerived f ha hb) preIso)

/-- Restricting derived coextension gives `RHom_A(B, -)`, with the comparison uniquely
specified by its compatibility with the derived units.

Both derived functors enter as arbitrary right derived functors presented by their universal
properties, so the statement is independent of the models chosen for them. That data is
discharged by `Dualizing.AnyModel.derivedHom` with `Dualizing.AnyModel.derivedHomUnit` on the
left and by `Dualizing.derivedHomAlong` with `Dualizing.derivedHomAlongUnit` on the right,
giving the unconditional `Dualizing.restrictDerivedHomIsoDerivedHomAlong`. -/
@[stacks 0A71 "derived Hom after restriction, for arbitrary right derived functors RF of \
coextension of scalars and RH of Hom_A(B, -); the data RF, alpha, RH, beta is discharged by \
AnyModel.derivedHom with AnyModel.derivedHomUnit and derivedHomAlong with derivedHomAlongUnit, \
giving the unconditional restrictDerivedHomIsoDerivedHomAlong"]
def derivedCoextendScalarsCompDerivedRestrictScalarsIso
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (.up ℤ))]
    (RH : DerivedCategory (ModuleCat.{max v u} A) ⥤
      DerivedCategory (ModuleCat.{max v u} A))
    (β : homAlongToDerivedCategory f ⟶ DerivedCategory.Qh ⋙ RH)
    [RH.IsRightDerivedFunctor β (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (.up ℤ))] :
    { e : RF ⋙ (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory ≅ RH //
      restrictedDerivedUnit f RF α ≫ Functor.whiskerLeft DerivedCategory.Qh e.hom = β } := by
  letI : (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory.IsLeftAdjoint :=
    restrictScalars_mapDerivedCategory_isLeftAdjoint f
  let canon : coextendScalarsToDerivedCategory f ⋙
      (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory ⟶
      DerivedCategory.Qh ⋙
        (RF ⋙ (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory) :=
    Functor.whiskerRight α (ModuleCat.restrictScalars f).mapDerivedCategory ≫
      (Functor.associator _ _ _).hom
  have hcanon :
      (RF ⋙ (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory).IsRightDerivedFunctor
      canon (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (.up ℤ)) := by
    infer_instance
  letI : (RF ⋙ (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory).IsLeftKanExtension
      (restrictedDerivedUnit f RF α) := by
    apply (Functor.isLeftKanExtension_iff_of_iso₂
      (restrictedDerivedUnit f RF α) canon (homAlongRestrictScalarsIso f)
      (Iso.refl _) ?_).2 hcanon.isLeftKanExtension
    simp [restrictedDerivedUnit, canon]
  letI :
      (RF ⋙ (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory).IsRightDerivedFunctor
      (restrictedDerivedUnit f RF α)
      (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (.up ℤ)) :=
    ⟨by assumption⟩
  refine ⟨Functor.rightDerivedUnique
    (RF ⋙ (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory) RH
    (restrictedDerivedUnit f RF α) β
    (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (.up ℤ)), ?_⟩
  simp

end

section

attribute [local instance] HasDerivedCategory.standard

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The established derived Hom functor has the right-derived universal property for its
total-derived unit, so it can be used directly in both comparisons. -/
instance derivedHom_isRightDerivedFunctor (f : A →+* B) :
    (derivedHom.{u, v} f).IsRightDerivedFunctor
      ((coextendScalarsToDerivedCategory f).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (.up ℤ)))
      (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (.up ℤ)) := by
  dsimp [derivedHom]
  infer_instance

end

end Dualizing
