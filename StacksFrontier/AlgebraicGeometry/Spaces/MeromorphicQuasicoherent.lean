module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleSheafifySections
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAlgebraColimits
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.CategoryTheory.Sites.Modules.MixedUniverseTensor
public import StacksFrontier.CategoryTheory.Sites.Modules.ModuleSheafLocalization
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# The sheaf of meromorphic functions is quasi-coherent and is computed on affine charts

Let `X` be an algebraic space over a scheme `S` satisfying the two standing hypotheses of
Stacks 0EN6:

* (a) every weakly associated point of `X` is a point of codimension `0`, and
* (b) every quasi-compact open of every étale scheme chart of `X` has finitely many irreducible
  components, the condition of Stacks 0BB1.

This file proves parts (1) and (2) of Stacks 0EN6: the sheaf of meromorphic functions `𝒦_X` of
Stacks 0EN3 is a quasi-coherent sheaf of `𝒪_X`-algebras, and over an affine object `U` of the
small étale site its ring of sections `𝒦_X(U)` is the total ring of fractions of `𝒪_X(U)`.

## Main results

* `Stacks.PresheafOfModules.isIso_restrictionBaseChange_algModule`: a presheaf of algebras which
  is sectionwise a localization is cartesian.
* `Stacks.PresheafOfModules.isIso_restrictionBaseChange_uliftSections`: raising the universe of
  the sections preserves cartesianness.
* `AlgebraicGeometry.Space.isSheaf_affineRegularLocalizationPresheaf`: the presheaf of sectionwise
  total fraction rings is a sheaf on the affine étale charts.
* `AlgebraicGeometry.Space.isQuasicoherent_meromorphicAlgebraSheaf`: `𝒦_X` is a quasi-coherent
  sheaf of `𝒪_X`-algebras.
* `AlgebraicGeometry.Space.isFractionRing_meromorphicFunctionSheaf_obj`: over an affine object
  `U` of the small étale site, `𝒦_X(U)` is the total ring of fractions of `𝒪_X(U)`.

## Implementation notes

The presheaf of sectionwise localizations has its sections in the universe of the schemes, one
below the universe of the affine étale site. Its sheaf condition is therefore obtained through
`PresheafOfModules.uliftSections` and `CommRingCat.uliftFunctor`;
`CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget` does not apply across that universe gap.

## References

* [Stacks Project, Tag 0EN6](https://stacks.math.columbia.edu/tag/0EN6)
* [Stacks Project, Tag 0EN3](https://stacks.math.columbia.edu/tag/0EN3)
* [Stacks Project, Tag 0EN4](https://stacks.math.columbia.edu/tag/0EN4)
* [Stacks Project, Tag 0BB1](https://stacks.math.columbia.edu/tag/0BB1)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open scoped nonZeroDivisors

universe t u v r

/-! ## The universe lift of commutative rings as a functor -/

namespace CommRingCat

/-- Raising the universe of the carrier of a commutative ring, as a functor. -/
def uliftFunctor : CommRingCat.{u} ⥤ CommRingCat.{max u t} where
  obj R := CommRingCat.of (ULift.{t} R)
  map f := CommRingCat.ofHom f.hom.ulift
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

/-- The universe lift of commutative rings is fully faithful. -/
def fullyFaithfulUliftFunctor : (uliftFunctor.{t, u}).FullyFaithful where
  preimage {_ _} f := CommRingCat.ofHom
    ((ULift.ringEquiv.toRingHom.comp f.hom).comp ULift.ringEquiv.symm.toRingHom)
  map_preimage {_ _} f := by ext x; rfl
  preimage_map {_ _} f := by ext x; rfl

/-- The universe lift of commutative rings is full. -/
instance : (uliftFunctor.{t, u}).Full := fullyFaithfulUliftFunctor.full
/-- The universe lift of commutative rings is faithful. -/
instance : (uliftFunctor.{t, u}).Faithful := fullyFaithfulUliftFunctor.faithful

end CommRingCat

namespace CategoryTheory.Presheaf

/-- A presheaf of commutative rings whose sections lie in a universe below that of the site is a
sheaf as soon as its underlying presheaf of types is one. -/
theorem isSheaf_of_isSheaf_forget_commRingCat {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (Q : Cᵒᵖ ⥤ CommRingCat.{r})
    (h : Presieve.IsSheaf J (Q ⋙ forget CommRingCat.{r})) : Presheaf.IsSheaf J Q := by
  refine Presheaf.isSheaf_of_isSheaf_comp J Q (CommRingCat.uliftFunctor.{max u v, r}) ?_
  rw [Presheaf.isSheaf_iff_isSheaf_comp J _ (forget CommRingCat.{max r u v})]
  refine (isSheaf_iff_isSheaf_of_type _ _).2 ?_
  have e : (Q ⋙ CommRingCat.uliftFunctor.{max u v, r}) ⋙ forget CommRingCat.{max r u v} ≅
      (Q ⋙ forget CommRingCat.{r}) ⋙ uliftFunctor.{max u v, r} :=
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  refine Presieve.isSheaf_iso J e.symm ?_
  rwa [Presieve.isSheaf_comp_uliftFunctor_iff]

end CategoryTheory.Presheaf

/-! ## The module underlying a presheaf of algebras, and its base change -/

namespace Stacks.PresheafOfModules

variable {C : Type u} [Category.{v} C] (R A : Cᵒᵖ ⥤ CommRingCat.{r}) (α : R ⟶ A)

/-- A presheaf of commutative `R`-algebras, read as a presheaf of `R`-modules. -/
noncomputable abbrev algModule :
    PresheafOfModules.{r} (R ⋙ forget₂ CommRingCat.{r} RingCat.{r}) :=
  (PresheafOfModules.restrictScalars
      (Functor.whiskerRight α (forget₂ CommRingCat.{r} RingCat.{r}))).obj
    (PresheafOfModules.unit (A ⋙ forget₂ CommRingCat.{r} RingCat.{r}))

/-- A presheaf of algebras which is sectionwise a localization is cartesian: if `A X` is the
localization of `R X` at `T` and `A Y` is the localization of `R Y` at the image of `T`, then
the base-change comparison `R Y ⊗_{R X} A X ⟶ A Y` is an isomorphism. -/
theorem isIso_restrictionBaseChange_algModule {X Y : Cᵒᵖ} (f : X ⟶ Y) (T : Submonoid (R.obj X))
    (h1 : letI := (α.app X).hom.toAlgebra; IsLocalization T (A.obj X))
    (h2 : letI : Algebra (R.obj X) (R.obj Y) := (R.map f).hom.toAlgebra
          letI := (α.app Y).hom.toAlgebra
          IsLocalization (Algebra.algebraMapSubmonoid (R.obj Y) T) (A.obj Y)) :
    IsIso (restrictionBaseChange (algModule R A α) f) := by
  let : Algebra (R.obj X) (R.obj Y) := (R.map f).hom.toAlgebra
  let : Algebra (R.obj X) (A.obj X) := (α.app X).hom.toAlgebra
  let : Algebra (R.obj Y) (A.obj Y) := (α.app Y).hom.toAlgebra
  have _ := h1
  have _ := h2
  set T' : Submonoid (R.obj Y) := Algebra.algebraMapSubmonoid (R.obj Y) T with hT'
  have hsrc : IsLocalization T' ((R.obj Y) ⊗[R.obj X] (A.obj X)) :=
    IsLocalization.tensor (R := R.obj X) (S := R.obj Y) (A := A.obj X) T
  set h₁ := Algebra.linearMap (R.obj Y) ((R.obj Y) ⊗[R.obj X] (A.obj X)) with hh1
  set e : ((R.obj Y) ⊗[R.obj X] (A.obj X)) →ₗ[R.obj Y] (A.obj Y) :=
    (restrictionBaseChange (algModule R A α) f).hom with he
  have hcomp : e ∘ₗ h₁ = Algebra.linearMap (R.obj Y) (A.obj Y) := by
    refine LinearMap.ext fun b => ?_
    have key := restrictionBaseChange_tmul (algModule R A α) f b (1 : A.obj X)
    refine key.trans ?_
    show (α.app Y).hom b * ((A.map f).hom (1 : A.obj X)) = _
    rw [map_one, mul_one]
    rfl
  have : IsLocalizedModule T' (e ∘ₗ h₁) := by rw [hcomp]; infer_instance
  have hE := IsLocalizedModule.linearEquiv_of_isLocalizedModule_comp T' h₁ e
  have hbij : Function.Bijective e := by
    rw [← hE]; exact (IsLocalizedModule.linearEquiv T' h₁ (e ∘ₗ h₁)).bijective
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hbij

end Stacks.PresheafOfModules

/-! ## Raising the universe of the sections of a cartesian presheaf -/

namespace Stacks.PresheafOfModules

universe m

/-- Raising the universe of the sections preserves being cartesian over a morphism. -/
theorem isIso_restrictionBaseChange_uliftSections
    {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{r}}
    (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))
    {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (h : IsIso (restrictionBaseChange.{u, v, r, m} M f)) :
    IsIso (restrictionBaseChange.{u, v, r, max t m} (M.uliftSections.{t}) f) := by
  have hb : Function.Bijective (restrictionBaseChange.{u, v, r, m} M f) := by
    have := h
    exact ConcreteCategory.bijective_of_isIso _
  let _ : Algebra (R.obj X) (R.obj Y) := (R.map f).hom.toAlgebra
  let d : ULift.{t} (M.obj Y) ≃ₗ[R.obj Y] (M.obj Y) := ULift.moduleEquiv
  let e : TensorProduct (R.obj X) (R.obj Y) (ULift.{t} (M.obj X)) ≃ₗ[R.obj Y]
      TensorProduct (R.obj X) (R.obj Y) (M.obj X) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (R.obj Y) (R.obj Y))
      ULift.moduleEquiv
  let L₁ : TensorProduct (R.obj X) (R.obj Y) (ULift.{t} (M.obj X)) →ₗ[R.obj Y] (M.obj Y) :=
    d.toLinearMap ∘ₗ (restrictionBaseChange.{u, v, r, max t m} (M.uliftSections.{t}) f).hom
  let L₂ : TensorProduct (R.obj X) (R.obj Y) (ULift.{t} (M.obj X)) →ₗ[R.obj Y] (M.obj Y) :=
    (restrictionBaseChange.{u, v, r, m} M f).hom ∘ₗ e.toLinearMap
  have key : L₁ = L₂ := by
    refine LinearMap.ext fun z => ?_
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul b x =>
      refine Eq.trans ?_ (restrictionBaseChange_tmul.{u, v, r, m} M f b (ULift.down x)).symm
      refine (congrArg d (restrictionBaseChange_tmul.{u, v, r, max t m}
        (M.uliftSections.{t}) f b x)).trans ?_
      exact (map_smul d b _).trans rfl
  have h₂ : Function.Bijective L₂ := hb.comp e.bijective
  rw [← key] at h₂
  have h₃ : Function.Bijective
      (restrictionBaseChange.{u, v, r, max t m} (M.uliftSections.{t}) f) := by
    have hd := d.symm.bijective.comp h₂
    have hfun : ((d.symm : _ → _) ∘ (L₁ : _ → _)) =
        ((restrictionBaseChange.{u, v, r, max t m} (M.uliftSections.{t}) f) : _ → _) := by
      funext z
      exact d.symm_apply_apply _
    rwa [hfun] at hd
  exact (ConcreteCategory.isIso_iff_bijective _).mpr h₃

end Stacks.PresheafOfModules

/-! ## The sheafified localization on sections -/

namespace AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf

variable {Y : RingedSite.{u, v, r}} (M : MultiplicativeSubpresheaf Y)
    [HasWeakSheafify Y.J CommRingCat.{r}]

/-- Over each object the canonical map `𝒪_Y ⟶ (S⁻¹𝒪_Y)^#` is the canonical map into the presheaf
of sectionwise localizations followed by the sheafification unit. -/
theorem toLocalizationSheaf_app (U : Y.Cᵒᵖ) :
    M.toLocalizationSheaf.hom.app U =
      M.toLocalizationPresheaf.app U ≫ (toSheafify Y.J M.localizationPresheaf).app U := by
  show (sheafificationIso Y.O).hom.hom.app U ≫
    ((presheafToSheaf Y.J CommRingCat.{r}).map M.toLocalizationPresheaf).hom.app U = _
  rw [show (sheafificationIso Y.O).hom.hom = toSheafify Y.J Y.O.obj by simp]
  show (toSheafify Y.J Y.O.obj ≫ sheafifyMap Y.J M.toLocalizationPresheaf).app U = _
  rw [← toSheafify_naturality]
  rfl

end AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf

namespace AlgebraicGeometry.Space

open Stacks.PresheafOfModules
open AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf
  (isLocalization_localizationPresheaf_toAlgebra toLocalizationSheaf_app)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-! ## The sheaf condition for the presheaf of sectionwise total fraction rings -/

/-- The presheaf of sectionwise localizations at the regular sections, restricted to the affine
étale charts. -/
noncomputable abbrev affineRegularLocalizationPresheaf :
    (AffineEtale B S hS X.1)ᵒᵖ ⥤ CommRingCat.{u} :=
  (AffineEtale.inclusion B S hS X.1).op ⋙ regularLocalizationPresheaf B S hS X

/-- The canonical morphism from the chart rings to the presheaf of sectionwise localizations. -/
noncomputable abbrev toAffineRegularLocalizationPresheaf :
    affineEtaleChartRings B S hS X.1 ⟶ affineRegularLocalizationPresheaf B S hS X :=
  (AffineEtale.inclusion B S hS X.1).op.whiskerLeft
    (regularSubpresheaf B S hS X).toLocalizationPresheaf

/-- The presheaf of sectionwise localizations on the affine charts, as a presheaf of modules over
the chart rings. -/
noncomputable abbrev affineRegularLocalizationModule :
    PresheafOfModules.{u}
      (affineEtaleChartRings B S hS X.1 ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  algModule _ _ (toAffineRegularLocalizationPresheaf B S hS X)

/-- Under hypotheses (a) and (b), the presheaf of sectionwise localizations at the regular
sections is cartesian on the affine étale charts. -/
theorem isIso_restrictionBaseChange_affineRegularLocalizationModule
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    {Z W : (AffineEtale B S hS X.1)ᵒᵖ} (f : Z ⟶ W) :
    IsIso (restrictionBaseChange (affineRegularLocalizationModule B S hS X) f) := by
  refine isIso_restrictionBaseChange_algModule _ _ _ f
    (regularSections B S hS X.1 (Z.unop.obj)) ?_ ?_
  · exact isLocalization_localizationPresheaf_toAlgebra (regularSubpresheaf B S hS X)
      (op Z.unop.obj)
  · let algV : Algebra ((structurePresheaf B S hS X.1).obj
          (op ((AffineEtale.inclusion B S hS X.1).obj W.unop)))
        ((affineRegularLocalizationPresheaf B S hS X).obj W) :=
      ((toAffineRegularLocalizationPresheaf B S hS X).app W).hom.toAlgebra
    have hlocV : IsLocalization
        (regularSections B S hS X.1 ((AffineEtale.inclusion B S hS X.1).obj W.unop))
        ((affineRegularLocalizationPresheaf B S hS X).obj W) :=
      isLocalization_localizationPresheaf_toAlgebra (regularSubpresheaf B S hS X)
        (op W.unop.obj)
    exact isLocalization_algebraMapSubmonoid_regularSections B S hS X hwa hfin
      ((AffineEtale.inclusion B S hS X.1).map f.unop) Z.unop.property W.unop.property
      ((affineRegularLocalizationPresheaf B S hS X).obj W)

/-- Under hypotheses (a) and (b), the presheaf `U ↦ 𝒮_X(U)⁻¹ 𝒪_X(U)` of sectionwise total
fraction rings is a sheaf on the affine étale charts. -/
theorem isSheaf_affineRegularLocalizationPresheaf
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1) :
    Presheaf.IsSheaf (AffineEtale.topology B S hS X.1)
      ((AffineEtale.inclusion B S hS X.1).op ⋙ regularLocalizationPresheaf B S hS X) := by
  have hcart : ∀ {Z W : (AffineEtale B S hS X.1)ᵒᵖ} (f : Z ⟶ W),
      IsIso (restrictionBaseChange.{u + 1, u, u, u + 1}
        ((affineRegularLocalizationModule B S hS X).uliftSections.{u + 1}) f) := fun f =>
    isIso_restrictionBaseChange_uliftSections.{u + 1, u + 1, u, u, u} _ f
      (isIso_restrictionBaseChange_affineRegularLocalizationModule B S hS X hwa hfin f)
  have hsheaf := isSheaf_of_cartesian_affineEtaleChart.{u, u} B S hS X.1
    ((affineRegularLocalizationModule B S hS X).uliftSections.{u + 1}) hcart
  rw [Presheaf.isSheaf_iff_isSheaf_comp (AffineEtale.topology B S hS X.1) _
    (CategoryTheory.forget AddCommGrpCat.{u + 1})] at hsheaf
  replace hsheaf := (isSheaf_iff_isSheaf_of_type _ _).1 hsheaf
  have e : ((affineRegularLocalizationModule B S hS X).uliftSections.{u + 1}).presheaf ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1} ≅
      (((AffineEtale.inclusion B S hS X.1).op ⋙ regularLocalizationPresheaf B S hS X) ⋙
        CategoryTheory.forget CommRingCat.{u}) ⋙ CategoryTheory.uliftFunctor.{u + 1, u} :=
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  exact Presheaf.isSheaf_of_isSheaf_forget_commRingCat _ _
    ((Presieve.isSheaf_comp_uliftFunctor_iff (J := AffineEtale.topology B S hS X.1)).mp
      (Presieve.isSheaf_iso _ e hsheaf))

/-! ## Meromorphic functions over an affine chart -/

/-- Over an affine chart the ring of meromorphic functions is the localization of the ring of
sections at the regular sections. -/
theorem isLocalization_regularSections_meromorphicFunctionSheaf_obj
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (U : SmallEtale B S hS X.1) (hU : IsAffine (smallEtaleScheme B S hS X.1 U)) :
    letI : Algebra ((structurePresheaf B S hS X.1).obj (op U))
        ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U)) :=
      ((toMeromorphicFunctionSheaf B S hS X.1 X.2).hom.app (op U)).hom.toAlgebra
    IsLocalization (regularSections B S hS X.1 U)
      ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U)) := by
  let algK : Algebra ((structurePresheaf B S hS X.1).obj (op U))
      ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U)) :=
    ((toMeromorphicFunctionSheaf B S hS X.1 X.2).hom.app (op U)).hom.toAlgebra
  have hiso : IsIso ((toSheafify (SmallEtale.topology B S hS X.1)
      (regularLocalizationPresheaf B S hS X)).app (op U)) :=
    isIso_toSheafify_app_of_isAffine B S hS X.1 X.2 _
      (isSheaf_affineRegularLocalizationPresheaf B S hS X hwa hfin) U hU
  let j := @asIso _ _ _ _ ((toSheafify (SmallEtale.topology B S hS X.1)
      (regularLocalizationPresheaf B S hS X)).app (op U)) hiso
  let jalg : Localization (regularSections B S hS X.1 U) ≃ₐ[
      (structurePresheaf B S hS X.1).obj (op U)]
      ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U)) :=
    { j.commRingCatIsoToRingEquiv with
      commutes' := fun r =>
        (congrArg (fun k : (structurePresheaf B S hS X.1).obj (op U) ⟶
            (meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U) => k.hom r)
          (toLocalizationSheaf_app (regularSubpresheaf B S hS X) (op U))).symm }
  exact (IsLocalization.isLocalization_iff_of_algEquiv (regularSections B S hS X.1 U) jalg).mp
    inferInstance

/-- For an affine object `U` of the small étale site of an algebraic
space `X` satisfying hypotheses (a) and (b), the ring `𝒦_X(U)` of meromorphic functions over `U`
is the total ring of fractions of `𝒪_X(U)`. -/
@[stacks 0EN6 "part (2): over an affine object of the small étale site the ring of meromorphic
functions is the total ring of fractions of the ring of sections"]
theorem isFractionRing_meromorphicFunctionSheaf_obj
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (U : SmallEtale B S hS X.1) (hU : IsAffine (smallEtaleScheme B S hS X.1 U)) :
    letI : Algebra ((structurePresheaf B S hS X.1).obj (op U))
        ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U)) :=
      ((toMeromorphicFunctionSheaf B S hS X.1 X.2).hom.app (op U)).hom.toAlgebra
    IsFractionRing ((structurePresheaf B S hS X.1).obj (op U))
      ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U)) := by
  have key := isLocalization_regularSections_meromorphicFunctionSheaf_obj B S hS X hwa hfin U hU
  rwa [regularSections_eq_nonZeroDivisors B S hS X.1 U hU] at key

/-! ## Quasi-coherence of the sheaf of meromorphic functions -/

/-- The sheaf of meromorphic functions `𝒦_X`, read as a sheaf of `𝒪_X`-algebras. -/
noncomputable abbrev meromorphicAlgebraSheaf : AlgebraSheaf.{u, u} B S hS X.1 X.2 :=
  AlgebraSheaf.ofHom (toMeromorphicFunctionSheaf B S hS X.1 X.2)

/-- Under hypotheses (a) and (b), the sheaf of meromorphic functions is cartesian on the affine
étale charts. -/
theorem isIso_restrictionBaseChange_meromorphic
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    {U V : SmallEtale B S hS X.1} (f : V ⟶ U)
    (hU : IsAffine (smallEtaleScheme B S hS X.1 U))
    (hV : IsAffine (smallEtaleScheme B S hS X.1 V)) :
    IsIso (restrictionBaseChange
      (algModule (structurePresheaf B S hS X.1)
        ((meromorphicFunctionSheaf B S hS X.1 X.2).obj)
        ((toMeromorphicFunctionSheaf B S hS X.1 X.2).hom)) f.op) := by
  refine isIso_restrictionBaseChange_algModule _ _ _ f.op
    (regularSections B S hS X.1 U) ?_ ?_
  · exact isLocalization_regularSections_meromorphicFunctionSheaf_obj B S hS X hwa hfin U hU
  · let algV : Algebra ((structurePresheaf B S hS X.1).obj (op V))
        ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op V)) :=
      ((toMeromorphicFunctionSheaf B S hS X.1 X.2).hom.app (op V)).hom.toAlgebra
    have hlocV : IsLocalization (regularSections B S hS X.1 V)
        ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op V)) :=
      isLocalization_regularSections_meromorphicFunctionSheaf_obj B S hS X hwa hfin V hV
    exact isLocalization_algebraMapSubmonoid_regularSections B S hS X hwa hfin f hU hV
      ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op V))

/-- For an algebraic space `X` satisfying hypotheses (a) and (b), the
sheaf of meromorphic functions `𝒦_X` is a quasi-coherent sheaf of `𝒪_X`-algebras. -/
@[stacks 0EN6 "part (1): the sheaf of meromorphic functions is a quasi-coherent sheaf of
algebras"]
theorem isQuasicoherent_meromorphicAlgebraSheaf
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1) :
    (meromorphicAlgebraSheaf B S hS X).IsQuasicoherent := by
  refine (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS X.1 X.2 _).mpr
    fun U V hU hV f => ?_
  exact (bijective_sectionsBaseChange_iff_isIso_restrictionBaseChange B S hS X.1 X.2 _ f).2
    (isIso_restrictionBaseChange_meromorphic B S hS X hwa hfin f hU hV)

end AlgebraicGeometry.Space

end
