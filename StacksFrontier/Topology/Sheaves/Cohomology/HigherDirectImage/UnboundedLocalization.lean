module

public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationIsomorphisms
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredComplexSpectralSequence.HigherDirectImageSpectralSequence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.DerivedDirectImageAndRestriction
public import StacksFrontier.Algebra.Homology.HomotopyCategory.InducedCommShift
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZeroExact
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.RealizationShift
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The unbounded derived direct image commutes with restriction to an open

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces, `V ⊆ Y` open and `U = f⁻¹(V)`.
Stacks 01E5 is in the tree for higher direct images of sheaves and for bounded below complexes
(`StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationIsomorphisms`). This file
proves the statement for the **unbounded** derived direct image, the total right derived functor
of the direct image on the homotopy category of all complexes, in the form needed to restrict a
connecting morphism of the derived category to an open:

`(Rf_*K)|_V ≅ R(f|_U)_*(K|_U)`,

naturally in `K ∈ D(𝒪_X)`, compatibly with the shifts, and read on cohomology sheaves together
with the shift identifications `Hⁿ(L⟦s⟧) ≅ Hⁿ⁺ˢ(L)`. It is the ringed-space form of
[Stacks, Tag 0D6G], and the proof is the one of that tag: both sides are right derived functors of
`K ↦ (f_*K)|_V`, because restriction is exact and carries K-injective complexes to K-injective
complexes ([Stacks, Tag 08FI]).

## Main definitions

All in the namespace `Stacks.Cohomology.HigherDirectImage`.

* `totalDerivedPushforward f`: the unbounded derived direct image. For the de Rham complex of
  `X → Y → S` it is `Stacks.DeRhamSmooth.derivedRelativePushforward f g` at
  `relativeBase f g`, by `rfl`.
* `derivedModuleRestriction X U`: restriction to an open on derived categories.
* `derivedPushforwardRestrictIso f V`: **the comparison** `Rf_* ⋙ (-)|_V ≅ (-)|_U ⋙ R(f|_U)_*`.
* `derivedPushforwardHomologyRestrictIso f V n`: the comparison on `n`-th cohomology sheaves.

## Main results

* `isKInjective_moduleRestriction`: [Stacks, Tag 08FI] on a ringed space.
* `commShift_derivedPushforwardRestrictIso`: the comparison commutes with the shifts.
* `derivedPushforwardHomologyRestrictIso_shift`: the cohomology comparison is compatible with the
  shift identifications of cohomology, so it carries the cohomology of a morphism `K ⟶ K'⟦s⟧` of
  `D(𝒪_X)` to that of its restriction.
* `CategoryTheory.Functor.rightDerivedNatTrans_commShift`: a transformation of right derived
  functors induced by a transformation commuting with the shifts commutes with the shifts, when
  both units do (generic).

## References

* [Stacks Project, Tag 0D6G](https://stacks.math.columbia.edu/tag/0D6G)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction

universe u

namespace CategoryTheory.Functor

variable {C D H : Type*} [Category* C] [Category* D] [Category* H]
  (RF RF' : H ⥤ D) {F F' : C ⥤ D} {L : C ⥤ H}
  (α : F ⟶ L ⋙ RF) (α' : F' ⟶ L ⋙ RF') (W : MorphismProperty C) [L.IsLocalization W]
  [RF.IsRightDerivedFunctor α W]
  (A : Type*) [AddGroup A] [HasShift C A] [HasShift D A] [HasShift H A]
  [W.IsCompatibleWithShift A] [F.CommShift A] [F'.CommShift A] [L.CommShift A]
  [RF.CommShift A] [RF'.CommShift A] [NatTrans.CommShift α A] [NatTrans.CommShift α' A]

/-- **The transformation of right derived functors induced by a transformation commuting with the
shifts commutes with the shifts**, when both units do. -/
theorem rightDerivedNatTrans_commShift (τ : F ⟶ F') [NatTrans.CommShift τ A] :
    NatTrans.CommShift (rightDerivedNatTrans RF RF' α α' W τ) A where
  shift_comm a := by
    apply rightDerived_ext _ (IsRightDerivedFunctor.precomposeShiftNatTrans RF α a) W
    ext X
    have hα := NatTrans.shift_app_comm α a X
    have hα' := NatTrans.shift_app_comm α' a X
    have hτ := NatTrans.shift_app_comm τ a X
    simp only [Functor.comp_obj, Functor.commShiftIso_comp_hom_app] at hα hα'
    simp only [comp_obj, NatTrans.comp_app, IsRightDerivedFunctor.precomposeShiftNatTrans_app,
      whiskerLeft_app, whiskerRight_app, Category.assoc]
    have hσ := (rightDerivedNatTrans RF RF' α α' W τ).naturality ((L.commShiftIso a).hom.app X)
    have h₁ := rightDerivedNatTrans_app RF RF' α α' W τ X
    have h₂ := rightDerivedNatTrans_app RF RF' α α' W τ (X⟦a⟧)
    rw [← reassoc_of% hα, ← Functor.map_comp, h₁, Functor.map_comp, reassoc_of% hτ, hα']
    dsimp at hσ
    rw [reassoc_of% hσ, reassoc_of% h₂]

variable {D₁ D₂ D₃ D₄ B₂ B₄ : Type*} [Category* D₁] [Category* D₂] [Category* D₃] [Category* D₄]
  [Category* B₂] [Category* B₄] [HasShift D₁ ℤ] [HasShift D₂ ℤ] [HasShift D₃ ℤ] [HasShift D₄ ℤ]

omit [HasShift C A] [HasShift D A] [HasShift H A] in
/-- The shift compatibility of a comparison `G ∘ (R ⋙ jD) ≅ G ∘ (jD' ⋙ R')` of cohomological
functors, in the abstract: `R`, `jD`, `jD'`, `R'` commute with the shifts, `Φ : R ⋙ jD ≅ jD' ⋙ R'`
does too, and `μ` compares the shift sequences `G` and `G₂` through `jD` and `j` compatibly with
the shifts. -/
theorem shiftSequence_comparison_shift (R : D₁ ⥤ D₂) (jD : D₂ ⥤ D₄) (jD' : D₁ ⥤ D₃)
    (R' : D₃ ⥤ D₄) [R.CommShift ℤ] [jD.CommShift ℤ] [jD'.CommShift ℤ] [R'.CommShift ℤ]
    (Φ : R ⋙ jD ≅ jD' ⋙ R') [NatTrans.CommShift Φ.hom ℤ]
    (G : D₄ ⥤ B₄) [G.ShiftSequence ℤ] (G₂ : D₂ ⥤ B₂) [G₂.ShiftSequence ℤ] (j : B₂ ⥤ B₄)
    (μ : ∀ k : ℤ, jD ⋙ G.shift k ≅ G₂.shift k ⋙ j)
    (hμ : ∀ (Y : D₂) (s n n' : ℤ) (h : s + n = n'),
      (G.shift n).map ((jD.commShiftIso s).hom.app Y) ≫ (G.shiftIso s n n' h).hom.app (jD.obj Y) ≫
          (μ n').hom.app Y =
        (μ n).hom.app (Y⟦s⟧) ≫ j.map ((G₂.shiftIso s n n' h).hom.app Y))
    (M : D₁) (s n n' : ℤ) (h : s + n = n') :
    ((μ n).inv.app (R.obj (M⟦s⟧)) ≫ (G.shift n).map (Φ.hom.app (M⟦s⟧))) ≫
        (G.shift n).map (R'.map ((jD'.commShiftIso s).hom.app M) ≫
          (R'.commShiftIso s).hom.app (jD'.obj M)) ≫
        (G.shiftIso s n n' h).hom.app (R'.obj (jD'.obj M)) =
      j.map ((G₂.shift n).map ((R.commShiftIso s).hom.app M) ≫
          (G₂.shiftIso s n n' h).hom.app (R.obj M)) ≫
        ((μ n').inv.app (R.obj M) ≫ (G.shift n').map (Φ.hom.app M)) := by
  have hΦ : Φ.hom.app (M⟦s⟧) ≫ R'.map ((jD'.commShiftIso s).hom.app M) ≫
      (R'.commShiftIso s).hom.app (jD'.obj M) =
        jD.map ((R.commShiftIso s).hom.app M) ≫ (jD.commShiftIso s).hom.app (R.obj M) ≫
          (Φ.hom.app M)⟦s⟧' := by
    have := NatTrans.shift_app_comm Φ.hom s M
    simp only [Functor.comp_obj, Functor.commShiftIso_comp_hom_app, Category.assoc] at this
    exact this.symm
  have hsh := G.shiftIso_hom_naturality s n n' h (Φ.hom.app M)
  have hμn : (μ n).inv.app (R.obj (M⟦s⟧)) ≫
      (G.shift n).map (jD.map ((R.commShiftIso s).hom.app M)) =
      j.map ((G₂.shift n).map ((R.commShiftIso s).hom.app M)) ≫
        (μ n).inv.app ((R.obj M)⟦s⟧) :=
    ((μ n).inv.naturality ((R.commShiftIso s).hom.app M)).symm
  have hμs := congrArg (· ≫ (μ n').inv.app (R.obj M)) (hμ (R.obj M) s n n' h)
  simp only [Category.assoc, Iso.hom_inv_id_app] at hμs
  simp only [Functor.comp_obj, Category.assoc]
  rw [← Functor.map_comp_assoc, hΦ, Functor.map_comp, Functor.map_comp,
    Category.assoc, Category.assoc]
  dsimp only [Functor.comp_obj] at hsh
  rw [hsh, reassoc_of% hμn, reassoc_of% hμs, Iso.inv_hom_id_app_assoc, Functor.map_comp,
    Category.assoc]

end CategoryTheory.Functor

namespace Stacks.Cohomology.HigherDirectImage

attribute [local instance] HasDerivedCategory.standard

open Stacks.Cohomology.FilteredComplex (homotopyPushforward
  isIso_pushforwardUnit_app_of_isKInjective)

variable {X Y : RingedSpace.{u, u}}

/-- **The unbounded derived direct image** `Rf_* : D(𝒪_X) ⥤ D(𝒪_Y)` along a morphism of ringed
spaces: the total right derived functor of the direct image on the homotopy category. -/
noncomputable abbrev totalDerivedPushforward (f : X ⟶ Y) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) :=
  (homotopyPushforward f).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))

/-- The derived-functor unit of `totalDerivedPushforward`. -/
noncomputable abbrev totalDerivedPushforwardUnit (f : X ⟶ Y) :
    homotopyPushforward f ⟶ DerivedCategory.Qh ⋙ totalDerivedPushforward f :=
  (homotopyPushforward f).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))

/-- Restriction to an open subspace is left exact, being a right adjoint. -/
instance moduleRestriction_preservesFiniteLimits (X : RingedSpace.{u, u}) (U : Opens X) :
    PreservesFiniteLimits (moduleRestriction X U) := by
  have : (moduleRestriction X U).IsRightAdjoint := inferInstance
  infer_instance

/-- **Restriction to an open subspace on derived categories**, `D(𝒪_X) ⥤ D(𝒪_X|_U)`: the
functor induced by the exact functor `moduleRestriction`. -/
noncomputable abbrev derivedModuleRestriction (X : RingedSpace.{u, u}) (U : Opens X) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing (restrictToOpen X U))) :=
  (moduleRestriction X U).mapDerivedCategory

/-- **Stacks 08FI on a ringed space.** The restriction of a K-injective complex of sheaves of
modules to an open subspace is K-injective: restriction is right adjoint to the exact extension
by zero. -/
theorem isKInjective_moduleRestriction (X : RingedSpace.{u, u}) (U : Opens X)
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((moduleRestriction X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  @CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ _ _ _ _ _
    (moduleRestriction X U) (ExtensionByZeroModules.jShriek U (structureSheafRing X)) _
    (ExtensionByZeroModules.jShriek_additive U (structureSheafRing X))
    (ExtensionByZeroModules.jShriekAdjunction U (structureSheafRing X))
    (ExtensionByZeroModules.jShriek_preservesFiniteLimits U (structureSheafRing X))
    (@PreservesColimitsOfSize.preservesFiniteColimits _ _ _ _ _
      (ExtensionByZeroModules.jShriek_preservesColimitsOfSizeZero U (structureSheafRing X))) I _

section Comparison

variable (f : X ⟶ Y) (V : Opens Y)

/-- The unit exhibiting `Rf_* ⋙ (-)|_V` as a right derived functor of
`ℱ ↦ (f_*ℱ)|_V` on the homotopy category. -/
noncomputable def pushforwardRestrictUnit :
    (modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (moduleRestriction Y V).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (totalDerivedPushforward f ⋙ derivedModuleRestriction Y V) :=
  Functor.whiskerLeft ((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ))
      (moduleRestriction Y V).mapDerivedCategoryFactorsh.inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (totalDerivedPushforwardUnit f) (derivedModuleRestriction Y V) ≫
    (Functor.associator _ _ _).hom

/-- The unit exhibiting `(-)|_{f⁻¹V} ⋙ R(f|_{f⁻¹V})_*` as a right derived functor of
`ℱ ↦ (f|_{f⁻¹V})_*(ℱ|_{f⁻¹V})` on the homotopy category. -/
noncomputable def restrictPushforwardUnit :
    (moduleRestriction X (preimageOpen f V)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (modulePushforward (restrictedMorphism f V)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (derivedModuleRestriction X (preimageOpen f V) ⋙
        totalDerivedPushforward (restrictedMorphism f V)) :=
  Functor.whiskerLeft ((moduleRestriction X (preimageOpen f V)).mapHomotopyCategory
      (ComplexShape.up ℤ)) (totalDerivedPushforwardUnit (restrictedMorphism f V)) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (moduleRestriction X (preimageOpen f V)).mapDerivedCategoryFactorsh.inv
      (totalDerivedPushforward (restrictedMorphism f V)) ≫
    (Functor.associator _ _ _).hom

/-- `Rf_* ⋙ (-)|_V` is a right derived functor of `K ↦ (f_*K)|_V`. -/
instance isRightDerivedFunctor_pushforwardRestrictUnit :
    (totalDerivedPushforward f ⋙ derivedModuleRestriction Y V).IsRightDerivedFunctor
      (pushforwardRestrictUnit f V)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)) := by
  have e : pushforwardRestrictUnit f V =
      Functor.whiskerLeft ((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ))
        (moduleRestriction Y V).mapDerivedCategoryFactorsh.inv ≫
      Functor.whiskerRight (totalDerivedPushforwardUnit f) (derivedModuleRestriction Y V) := by
    ext K
    simp [pushforwardRestrictUnit]
  rw [e]
  exact Stacks.Cohomology.Localization.isRightDerivedFunctor_comp_of_kInjectives
    (modulePushforward f) (moduleRestriction Y V) (totalDerivedPushforward f)
    (derivedModuleRestriction Y V) (totalDerivedPushforwardUnit f)
    (moduleRestriction Y V).mapDerivedCategoryFactorsh.inv
    (fun I hI => isIso_pushforwardUnit_app_of_isKInjective f _ _ I hI)
    (fun _ _ => inferInstance)

/-- `(-)|_U ⋙ R(f|_U)_*` is a right derived functor of `K ↦ (f|_U)_*(K|_U)`. -/
instance isRightDerivedFunctor_restrictPushforwardUnit :
    (derivedModuleRestriction X (preimageOpen f V) ⋙
        totalDerivedPushforward (restrictedMorphism f V)).IsRightDerivedFunctor
      (restrictPushforwardUnit f V)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)) := by
  have e : restrictPushforwardUnit f V =
      Functor.whiskerLeft ((moduleRestriction X (preimageOpen f V)).mapHomotopyCategory
        (ComplexShape.up ℤ)) (totalDerivedPushforwardUnit (restrictedMorphism f V)) ≫
      Functor.whiskerRight (moduleRestriction X (preimageOpen f V)).mapDerivedCategoryFactorsh.inv
        (totalDerivedPushforward (restrictedMorphism f V)) := by
    ext K
    simp [restrictPushforwardUnit]
  rw [e]
  exact Stacks.Cohomology.Localization.isRightDerivedFunctor_comp_of_kInjectives
    (moduleRestriction X (preimageOpen f V)) (modulePushforward (restrictedMorphism f V))
    (derivedModuleRestriction X (preimageOpen f V))
    (totalDerivedPushforward (restrictedMorphism f V))
    (moduleRestriction X (preimageOpen f V)).mapDerivedCategoryFactorsh.inv
    (totalDerivedPushforwardUnit (restrictedMorphism f V))
    (fun _ _ => inferInstance)
    (fun I _ => isIso_pushforwardUnit_app_of_isKInjective (restrictedMorphism f V) _ _ _
      (isKInjective_moduleRestriction X (preimageOpen f V) I))

/-- The underived comparison `(f_*ℱ)|_V ≅ (f|_{f⁻¹V})_*(ℱ|_{f⁻¹V})` on the homotopy category,
followed by the localization functor. -/
noncomputable def pushforwardRestrictHomotopyIso :
    (modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (moduleRestriction Y V).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ≅
      (moduleRestriction X (preimageOpen f V)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (modulePushforward (restrictedMorphism f V)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
    ((Functor.mapHomotopyCategoryCompIso (Iso.refl (modulePushforward f ⋙ moduleRestriction Y V))
        (ComplexShape.up ℤ)) ≪≫
      (Functor.mapHomotopyCategoryCompIso (modulePushforwardRestrictIso f V)
        (ComplexShape.up ℤ)).symm) DerivedCategory.Qh ≪≫ Functor.associator _ _ _

/-- **The unbounded derived direct image commutes with restriction to an open** ([Stacks, Tag
0D6G] for a morphism of ringed spaces): for `f : X ⟶ Y` and an open `V ⊆ Y`,
`(Rf_*K)|_V ≅ R(f|_{f⁻¹V})_*(K|_{f⁻¹V})`, naturally in `K ∈ D(𝒪_X)`. -/
noncomputable def derivedPushforwardRestrictIso :
    totalDerivedPushforward f ⋙ derivedModuleRestriction Y V ≅
      derivedModuleRestriction X (preimageOpen f V) ⋙
        totalDerivedPushforward (restrictedMorphism f V) :=
  Functor.rightDerivedNatIso _ _ (pushforwardRestrictUnit f V) (restrictPushforwardUnit f V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    (pushforwardRestrictHomotopyIso f V)

/-- Shift compatibility of an auxiliary comparison. -/
instance commShift_pushforwardRestrictUnit :
    NatTrans.CommShift (pushforwardRestrictUnit f V) ℤ := by
  unfold pushforwardRestrictUnit
  infer_instance

/-- Shift compatibility of an auxiliary comparison. -/
instance commShift_restrictPushforwardUnit :
    NatTrans.CommShift (restrictPushforwardUnit f V) ℤ := by
  unfold restrictPushforwardUnit
  infer_instance

/-- Shift compatibility of an auxiliary comparison. -/
instance commShift_pushforwardRestrictHomotopyIso :
    NatTrans.CommShift (pushforwardRestrictHomotopyIso f V).hom ℤ := by
  have h1 : NatTrans.CommShift (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (modulePushforward f ⋙ moduleRestriction Y V)) (ComplexShape.up ℤ)).hom ℤ :=
    inferInstance
  have h2 : NatTrans.CommShift (Functor.mapHomotopyCategoryCompIso
      (modulePushforwardRestrictIso f V) (ComplexShape.up ℤ)).inv ℤ := inferInstance
  unfold pushforwardRestrictHomotopyIso
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.whiskerRight_comp]
  infer_instance

/-- The comparison `derivedPushforwardRestrictIso` commutes with the shifts. -/
instance commShift_derivedPushforwardRestrictIso :
    NatTrans.CommShift (derivedPushforwardRestrictIso f V).hom ℤ :=
  Functor.rightDerivedNatTrans_commShift _ _ (pushforwardRestrictUnit f V)
    (restrictPushforwardUnit f V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    ℤ (pushforwardRestrictHomotopyIso f V).hom

/-- **Higher direct images commute with restriction to an open**, at the level of cohomology
sheaves of the unbounded derived direct image: for `K ∈ D(𝒪_X)` and every `n`,
`(Hⁿ(Rf_*K))|_V ≅ Hⁿ(R(f|_{f⁻¹V})_*(K|_{f⁻¹V}))`, naturally in `K`. -/
@[sga "4 V 5.1" "Clause 3, special case"]
noncomputable def derivedPushforwardHomologyRestrictIso (n : ℤ) :
    totalDerivedPushforward f ⋙
        DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) n ⋙
          moduleRestriction Y V ≅
      derivedModuleRestriction X (preimageOpen f V) ⋙
        totalDerivedPushforward (restrictedMorphism f V) ⋙
          DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (structureSheafRing (restrictToOpen Y V))) n :=
  Functor.isoWhiskerLeft (totalDerivedPushforward f)
      ((moduleRestriction Y V).mapDerivedCategoryHomologyIso n).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (derivedPushforwardRestrictIso f V)
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing (restrictToOpen Y V))) n) ≪≫
    Functor.associator _ _ _

/-- **The cohomology comparison is compatible with the shift identifications**
`Hⁿ(L⟦s⟧) ≅ Hⁿ⁺ˢ(L)` on both sides, so that it carries the cohomology of a morphism
`K ⟶ K'⟦s⟧` of `D(𝒪_X)` — such as a connecting morphism — to the cohomology of its
restriction. -/
theorem derivedPushforwardHomologyRestrictIso_shift
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (s n n' : ℤ)
    (h : s + n = n') :
    (derivedPushforwardHomologyRestrictIso f V n).hom.app (M⟦s⟧) ≫
        (DerivedCategory.homologyFunctor _ n).map
          ((totalDerivedPushforward (restrictedMorphism f V)).map
            (((derivedModuleRestriction X (preimageOpen f V)).commShiftIso s).hom.app M) ≫
          ((totalDerivedPushforward (restrictedMorphism f V)).commShiftIso s).hom.app
            ((derivedModuleRestriction X (preimageOpen f V)).obj M)) ≫
        ((DerivedCategory.homologyFunctor _ 0).shiftIso s n n' h).hom.app
          ((totalDerivedPushforward (restrictedMorphism f V)).obj
            ((derivedModuleRestriction X (preimageOpen f V)).obj M)) =
      (moduleRestriction Y V).map
          ((DerivedCategory.homologyFunctor _ n).map
              (((totalDerivedPushforward f).commShiftIso s).hom.app M) ≫
            ((DerivedCategory.homologyFunctor _ 0).shiftIso s n n' h).hom.app
              ((totalDerivedPushforward f).obj M)) ≫
        (derivedPushforwardHomologyRestrictIso f V n').hom.app M := by
  have e₁ : ∀ k (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))),
      (derivedPushforwardHomologyRestrictIso f V k).hom.app L =
        ((moduleRestriction Y V).mapDerivedCategoryHomologyIso k).inv.app
            ((totalDerivedPushforward f).obj L) ≫
          (DerivedCategory.homologyFunctor _ k).map
            ((derivedPushforwardRestrictIso f V).hom.app L) := by
    intro k L
    simp [derivedPushforwardHomologyRestrictIso]
  rw [e₁, e₁]
  exact Functor.shiftSequence_comparison_shift (totalDerivedPushforward f)
    (derivedModuleRestriction Y V) (derivedModuleRestriction X (preimageOpen f V))
    (totalDerivedPushforward (restrictedMorphism f V)) (derivedPushforwardRestrictIso f V)
    (DerivedCategory.homologyFunctor _ 0) (DerivedCategory.homologyFunctor _ 0)
    (moduleRestriction Y V) (fun k => (moduleRestriction Y V).mapDerivedCategoryHomologyIso k)
    (fun Y' s n n' h => Stacks.Cohomology.RealizationShift.mapDerivedCategoryHomologyIso_shift
      (moduleRestriction Y V) Y' s n n' h) M s n n' h

end Comparison

end Stacks.Cohomology.HigherDirectImage
