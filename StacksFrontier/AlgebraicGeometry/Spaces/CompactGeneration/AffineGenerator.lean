module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDerivedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforward
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.Algebra.Homology.DerivedCategory.HomFromSingle
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedSerreInducedTStructure
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapChartwiseVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerre
public import StacksFrontier.Homology.DerivedCategory.IsZero
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectSums
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackSection
public import StacksFrontier.AlgebraicGeometry.Spaces.FreeModuleSections
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.HomologyDirectSums
public import StacksFrontier.CategoryTheory.Triangulated.LocalizingAdmissible
public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicRepresentableComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine

/-!
# The structure sheaf generates `D_QCoh` of an affine algebraic space

Let `X` be an algebraic space whose small étale site has a final object `T` with affine
underlying scheme, for instance an affine algebraic space. This file shows that the structure
sheaf `𝒪_X`, placed in degree zero, is a compact object of `D_QCoh(𝒪_X)` which generates it:

* morphisms `𝒪_X[0] ⟶ E⟦q⟧` are the global sections of `Hᵠ(E)`, for `E` in `D_QCoh(𝒪_X)`;
* an object of `D_QCoh(𝒪_X)` receiving no nonzero morphism from a shift of `𝒪_X[0]` is zero.

## Main results

* `AlgebraicGeometry.Space.homFromUnit_eq_zero_of_isLE`: a morphism `𝒪_X[0] ⟶ F` into an object
  of `D_QCoh(𝒪_X)` concentrated in degrees `≤ -1` vanishes. This is where the vanishing of the
  higher cohomology of quasi-coherent modules on the affine final object enters, through
  `AlgebraicGeometry.Space.isLE_rightDerived_sectionsFunctor_obj_of_isAffineChart`.
* `AlgebraicGeometry.Space.bijective_homFromUnitSections`: morphisms `𝒪_X[0] ⟶ E` are the
  sections of `H⁰(E)` over the final object, naturally in `E` (`homFromUnitSections_comp`).
* `AlgebraicGeometry.Space.isCompactObject_unitQuasicoherent` and
  `AlgebraicGeometry.Space.isWeakTriangulatedGenerator_unitQuasicoherent`: `𝒪_X[0]` is a compact
  object and a weak generator of `D_QCoh(𝒪_X)`.
* `AlgebraicGeometry.Space.isCompactObject_and_isWeakTriangulatedGenerator_unitQuasicoherent`:
  the same for an affine algebraic space.

## Implementation notes

The derived category is `HasDerivedCategory.standard`, the model in which
`AlgebraicGeometry.Space.QuasicoherentDerivedCategory` is formed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.FiniteTypeKernel (sectionsEquivOfTerminal)

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse
  Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory

variable {B S hS X hX}

/-- A morphism `𝒪_X ⟶ I⁰` killed by the differential factors through the differential
`I⁻¹ ⟶ I⁰`, as soon as the complex of sections of `I` over a final object of the site is exact
in degree zero. -/
theorem exists_comp_d_eq_of_exactAt (T : SmallEtale B S hS X) (hT : IsTerminal T)
    (I : CochainComplex (Modules.{u, u} B S hS X hX) ℤ)
    (hex : (((Stacks.Cohomology.SiteInverseLimits.sectionsFunctor
      (smallEtaleRingedSite B S hS X hX) T).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        I).ExactAt 0)
    (φ : structureModule ⟨X, hX⟩ ⟶ I.X 0) (hφ : φ ≫ I.d 0 1 = 0) :
    ∃ h : structureModule ⟨X, hX⟩ ⟶ I.X (-1), h ≫ I.d (-1) 0 = φ := by
  rw [HomologicalComplex.exactAt_iff' _ (-1) 0 1 (by simp) (by simp),
    ShortComplex.ab_exact_iff] at hex
  have hev : ∀ {M N : Modules.{u, u} B S hS X hX} (d : M ⟶ N) (s : M.sections),
      sectionsEquivOfTerminal N hT (SheafOfModules.sectionsMap d s) =
        (d.val.app (op T)).hom (sectionsEquivOfTerminal M hT s) := fun _ _ => rfl
  set x : ((I.X 0).val.obj (op T) : Type u) :=
    sectionsEquivOfTerminal (I.X 0) hT ((I.X 0).unitHomEquiv φ) with hx
  have hdx : ((I.d 0 1).val.app (op T)).hom x = 0 := by
    rw [hx, ← hev, ← SheafOfModules.unitHomEquiv_comp_apply, hφ]
    rfl
  obtain ⟨y, hy⟩ := hex x hdx
  refine ⟨(I.X (-1)).unitHomEquiv.symm ((sectionsEquivOfTerminal (I.X (-1)) hT).symm y), ?_⟩
  apply (I.X 0).unitHomEquiv.injective
  apply (sectionsEquivOfTerminal (I.X 0) hT).injective
  rw [SheafOfModules.unitHomEquiv_comp_apply, Equiv.apply_symm_apply, hev, ← hx]
  exact (congrArg _ ((sectionsEquivOfTerminal (I.X (-1)) hT).apply_symm_apply y)).trans hy

/-- The sections over an étale chart, as a functor from `𝒪_X`-modules to abelian groups. -/
abbrev chartSections (T : SmallEtale B S hS X) : Modules.{u, u} B S hS X hX ⥤ AddCommGrpCat.{u} :=
  Stacks.Cohomology.SiteInverseLimits.sectionsFunctor (smallEtaleRingedSite B S hS X hX) T

/-- The sections over an étale chart have a right derived functor on the unbounded derived
category, and it is computed by K-injective complexes. -/
theorem hasRightDerivedFunctor_chartSections_and_isIso (T : SmallEtale B S hS X) :
    ((chartSections (hX := hX) T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X hX) (ComplexShape.up ℤ)) ∧
      ∀ (I : CochainComplex (Modules.{u, u} B S hS X hX) ℤ), I.IsKInjective →
        ∀ [((chartSections (hX := hX) T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).HasRightDerivedFunctor
          (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X hX) (ComplexShape.up ℤ))],
        IsIso ((((chartSections (hX := hX) T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X hX) (ComplexShape.up ℤ))).app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) := by
  obtain ⟨h₁, h₂⟩ :=
    Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    ((chartSections (hX := hX) T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (exists_quasiIso_isKInjective_modules B S hS X hX)
  exact ⟨Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _,
    fun I hI _ => h₂ DerivedCategory.Qh _ _ I hI⟩

/-- The complex of sections over an affine chart of a K-injective complex with quasi-coherent
cohomology in degrees `≤ -1` is exact in degree zero. -/
theorem exactAt_chartSections_of_isLE (T : SmallEtale B S hS X) (hTa : IsAffineChart B S hS X T)
    (I : CochainComplex (Modules.{u, u} B S hS X hX) ℤ) (hI : I.IsKInjective)
    (hQqc : ∀ q : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) q).obj
      (DerivedCategory.Q.obj I)).IsQuasicoherentOnSite)
    (hle : (DerivedCategory.Q.obj I).IsLE (-1)) :
    (((chartSections (hX := hX) T).mapHomologicalComplex (ComplexShape.up ℤ)).obj I).ExactAt 0 := by
  let qI := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I
  obtain ⟨hRF, hiso⟩ := hasRightDerivedFunctor_chartSections_and_isIso (hX := hX) T
  have hiso' := hiso I hI
  let G := chartSections (hX := hX) T
  let RF := (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
    DerivedCategory.Qh (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X hX) (ComplexShape.up ℤ))
  let α := (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit
    DerivedCategory.Qh (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X hX) (ComplexShape.up ℤ))
  have eI : DerivedCategory.Qh.obj qI ≅ DerivedCategory.Q.obj I :=
    (DerivedCategory.quotientCompQhIso _).app I
  have hQqc' : QcohDerived B S hS ⟨X, hX⟩ (DerivedCategory.Qh.obj qI) :=
    ObjectProperty.prop_of_iso (QcohDerived B S hS ⟨X, hX⟩) eI.symm hQqc
  have hQle : (DerivedCategory.Qh.obj qI).IsLE (-1) :=
    DerivedCategory.TStructure.t.isLE_of_iso eI.symm (-1)
  have hRFle : (RF.obj (DerivedCategory.Qh.obj qI)).IsLE (-1) :=
    isLE_rightDerived_sectionsFunctor_obj_of_isAffineChart B S hS X hX T hTa RF α _ hQqc' (-1) hQle
  have : DerivedCategory.TStructure.t.IsLE ((DerivedCategory.Qh ⋙ RF).obj qI) (-1) := hRFle
  have hGle : (DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).IsLE
      (-1) :=
    DerivedCategory.TStructure.t.isLE_of_iso
      ((asIso (α.app qI)).symm ≪≫ (DerivedCategory.quotientCompQhIso _).app _) (-1)
  rw [DerivedCategory.isLE_Q_obj_iff] at hGle
  exact CochainComplex.exactAt_of_isLE ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) (-1) 0

/-- **A morphism from `𝒪_X[0]` into an object of `D_QCoh(𝒪_X)` of degrees `≤ -1` vanishes**, when
the small étale site has a final object with affine underlying scheme.

Represent the target by a K-injective complex `I`. The morphism is the class of a map of
complexes `𝒪_X[0] ⟶ I`, that is a `0`-cocycle `𝒪_X ⟶ I⁰`. The complex of sections of `I` over the
final object computes derived sections, which lie in degrees `≤ -1` because the higher
cohomology of a quasi-coherent module on an affine chart vanishes; so that cocycle is a
coboundary, and the map of complexes is null-homotopic. -/
theorem homFromUnit_eq_zero_of_isLE (T : SmallEtale B S hS X) (hT : IsTerminal T)
    (hTa : IsAffineChart B S hS X T) (F : DerivedCategory (Modules.{u, u} B S hS X hX))
    (hF : ∀ q : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) q).obj
      F).IsQuasicoherentOnSite)
    (hle : F.IsLE (-1))
    (f : (DerivedCategory.singleFunctor (Modules.{u, u} B S hS X hX) 0).obj
      (structureModule ⟨X, hX⟩) ⟶ F) : f = 0 := by
  obtain ⟨I, g, hI, hg⟩ := exists_quasiIso_isKInjective_modules B S hS X hX
    (DerivedCategory.Q.objPreimage F)
  let e : DerivedCategory.Q.obj I ≅ F :=
    (asIso (DerivedCategory.Q.map g)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso F
  let L := (CochainComplex.singleFunctor (Modules.{u, u} B S hS X hX) 0).obj
    (structureModule ⟨X, hX⟩)
  let qL := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L
  let qI := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I
  let φQ := DerivedCategory.quotientCompQhIso (Modules.{u, u} B S hS X hX)
  let f'' : DerivedCategory.Qh.obj qL ⟶ DerivedCategory.Qh.obj qI :=
    φQ.hom.app L ≫ f ≫ e.inv ≫ φQ.inv.app I
  suffices hf'' : f'' = 0 by
    have : f ≫ e.inv = 0 := by
      simpa [f''] using congrArg (fun k => φQ.inv.app L ≫ k ≫ φQ.hom.app I) hf''
    simpa using congrArg (· ≫ e.hom) this
  obtain ⟨ψ, hψ⟩ := (CochainComplex.IsKInjective.Qh_map_bijective qL I).2 f''
  obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_surjective ψ
  rw [← hψ]
  suffices hφ : (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map φ = 0 by
    rw [hφ, Functor.map_zero]
  have hQle : (DerivedCategory.Q.obj I).IsLE (-1) :=
    DerivedCategory.TStructure.t.isLE_of_iso e.symm (-1)
  have hex := exactAt_chartSections_of_isLE T hTa I hI
    (ObjectProperty.prop_of_iso (QcohDerived B S hS ⟨X, hX⟩) e.symm hF) hQle
  obtain ⟨s, hs, hsφ⟩ := CochainComplex.HomComplex.Cocycle.fromSingleMk_surjective
    (CochainComplex.HomComplex.Cocycle.ofHom φ) 0 (zero_add 0) 1 (zero_add 1)
  obtain ⟨t, ht⟩ := exists_comp_d_eq_of_exactAt T hT I hex s hs
  rw [HomotopyCategory.quotient_map_eq_zero_iff]
  have h01 : (0 : ℤ) + (-1) = -1 := zero_add _
  refine ⟨(CochainComplex.HomComplex.Cochain.equivHomotopy φ 0).symm
    ⟨CochainComplex.HomComplex.Cochain.fromSingleMk t h01, ?_⟩⟩
  rw [CochainComplex.HomComplex.Cochain.ofHom_zero, add_zero,
    CochainComplex.HomComplex.Cochain.δ_fromSingleMk t h01 0 0 (zero_add 0), ht]
  simpa using (congrArg (fun z : CochainComplex.HomComplex.Cocycle L I 0 =>
    (z : CochainComplex.HomComplex.Cochain L I 0)) hsφ).symm

/-- Having quasi-coherent cohomology is preserved by the truncations `τ_{≤ n}`. -/
theorem qcohDerived_truncLE (E : DerivedCategory (Modules.{u, u} B S hS X hX)) (n : ℤ)
    (hE : QcohDerived B S hS ⟨X, hX⟩ E) :
    QcohDerived B S hS ⟨X, hX⟩ ((DerivedCategory.TStructure.t.truncLE n).obj E) :=
  DerivedCategoryB.derivedCategoryB_truncLT_obj _
    (WeakSerre.isWeakSerre_of_isWeakSerreClass _) (n + 1) E hE

/-- Having quasi-coherent cohomology is preserved by the shift. -/
theorem qcohDerived_shift (E : DerivedCategory (Modules.{u, u} B S hS X hX)) (a : ℤ)
    (hE : QcohDerived B S hS ⟨X, hX⟩ E) : QcohDerived B S hS ⟨X, hX⟩ (E⟦a⟧) := fun n =>
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    (((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) 0).shiftIso a n (a + n)
      rfl).app E).symm (hE (a + n))

/-- **Morphisms `𝒪_X[0] ⟶ E` are morphisms `𝒪_X ⟶ H⁰(E)`**, for `E` in `D_QCoh(𝒪_X)`, when the
small étale site has a final object with affine underlying scheme: the comparison given by `H⁰`
is bijective. -/
theorem bijective_homologyFunctor_map_fromUnit (T : SmallEtale B S hS X) (hT : IsTerminal T)
    (hTa : IsAffineChart B S hS X T) (E : DerivedCategory (Modules.{u, u} B S hS X hX))
    (hE : QcohDerived B S hS ⟨X, hX⟩ E) :
    Function.Bijective (fun x : (DerivedCategory.singleFunctor _ 0).obj
        (structureModule ⟨X, hX⟩) ⟶ E =>
      (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) 0).map x) :=
  DerivedCategory.bijective_homologyFunctor_map_singleFunctor _ (QcohDerived B S hS ⟨X, hX⟩)
    (fun Y n hY => qcohDerived_truncLE Y n hY) (fun Y hY => qcohDerived_shift Y 1 hY)
    (fun Y hY hle f => homFromUnit_eq_zero_of_isLE T hT hTa Y hY hle f) E hE

/-- A quasi-coherent `𝒪_X`-module with no nonzero section over a final object `T` of the small
étale site, with `T` affine, is zero: over every affine chart its sections are a base change of
its sections over `T`. -/
theorem isZero_of_subsingleton_sections_terminal (T : SmallEtale B S hS X) (hT : IsTerminal T)
    (hTa : IsAffineChart B S hS X T) (M : Modules.{u, u} B S hS X hX)
    (hM : M.IsQuasicoherentOnSite) (h0 : Subsingleton (M.val.obj (op T))) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  refine Modules.eq_zero_of_forall_app_isAffine_eq_zero (X := ⟨X, hX⟩) B S hS (𝟙 M)
    fun U hU => ?_
  have hbij := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X hX M hM T U hTa hU
    (hT.from U)
  have : Subsingleton (M.val.obj (op U)) := by
    let := chartAlgebra (hF := hX) (hT.from U)
    have : Subsingleton (TensorProduct (chartRing B S hS X hX T) (chartRing B S hS X hX U)
        (M.val.obj (op T))) := inferInstance
    exact hbij.2.subsingleton
  exact ModuleCat.hom_ext (LinearMap.ext fun _ => Subsingleton.elim _ _)

/-- **`𝒪_X` detects each cohomology sheaf of an object of `D_QCoh(𝒪_X)`** when the small étale
site has a final object with affine underlying scheme: if every morphism `𝒪_X[0] ⟶ E⟦q⟧` vanishes,
then `H^q(E) = 0`. -/
theorem isZero_homology_of_forall_homFromUnit_eq_zero (T : SmallEtale B S hS X)
    (hT : IsTerminal T) (hTa : IsAffineChart B S hS X T)
    (E : DerivedCategory (Modules.{u, u} B S hS X hX)) (hE : QcohDerived B S hS ⟨X, hX⟩ E)
    (q : ℤ) (hq : ∀ g : (DerivedCategory.singleFunctor _ 0).obj
      (structureModule ⟨X, hX⟩) ⟶ E⟦q⟧, g = 0) :
    IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) q).obj E) := by
  have hbij := bijective_homologyFunctor_map_fromUnit T hT hTa (E⟦q⟧) (qcohDerived_shift E q hE)
  have hsub : Subsingleton ((DerivedCategory.homologyFunctor _ 0).obj
      ((DerivedCategory.singleFunctor _ 0).obj (structureModule ⟨X, hX⟩)) ⟶
      (DerivedCategory.homologyFunctor _ 0).obj (E⟦q⟧)) :=
    ⟨fun a b => by
      obtain ⟨x, rfl⟩ := hbij.2 a
      obtain ⟨y, rfl⟩ := hbij.2 b
      simp only [hq x, hq y]⟩
  let eH : (DerivedCategory.homologyFunctor _ 0).obj (E⟦q⟧) ≅
      (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) q).obj E :=
    ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) 0).shiftIso q 0 q
      (add_zero q)).app E
  let e1 := (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (Modules.{u, u} B S hS X hX) 0).app (structureModule ⟨X, hX⟩)
  have hsub' : Subsingleton (structureModule ⟨X, hX⟩ ⟶
      (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) q).obj E) :=
    ⟨fun a b => by simpa using hsub.elim (e1.hom ≫ a ≫ eH.inv) (e1.hom ≫ b ≫ eH.inv)⟩
  refine isZero_of_subsingleton_sections_terminal T hT hTa _ (hE q) ⟨fun a b => ?_⟩
  set M := (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) q).obj E
  exact (sectionsEquivOfTerminal M hT).symm.injective
    ((SheafOfModules.unitHomEquiv M).symm.injective (hsub'.elim _ _))

/-- **`𝒪_X` generates `D_QCoh(𝒪_X)`** when the small étale site has a final object with affine
underlying scheme: an object of `D_QCoh(𝒪_X)` receiving only zero morphisms from the shifts of
`𝒪_X[0]` is zero. -/
theorem isZero_of_forall_homFromUnit_eq_zero (T : SmallEtale B S hS X) (hT : IsTerminal T)
    (hTa : IsAffineChart B S hS X T) (E : DerivedCategory (Modules.{u, u} B S hS X hX))
    (hE : QcohDerived B S hS ⟨X, hX⟩ E)
    (h : ∀ (q : ℤ) (g : (DerivedCategory.singleFunctor _ 0).obj
      (structureModule ⟨X, hX⟩) ⟶ E⟦q⟧), g = 0) : IsZero E := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  exact fun q => isZero_homology_of_forall_homFromUnit_eq_zero T hT hTa E hE q (h q)

/-! ### The structure sheaf as an object of `D_QCoh(𝒪_X)` -/

/-- `𝒪_X[0]` has quasi-coherent cohomology sheaves. -/
theorem qcohDerived_singleFunctor_structureModule :
    QcohDerived B S hS ⟨X, hX⟩ ((DerivedCategory.singleFunctor _ 0).obj
      (structureModule ⟨X, hX⟩)) := by
  intro i
  rcases lt_trichotomy i 0 with hi | rfl | hi
  · exact SheafOfModules.IsQuasicoherentOnSite.of_isZero
      (DerivedCategory.isZero_of_isGE _ 0 i hi)
  · exact SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _).symm
      (SheafOfModules.isQuasicoherentOnSite_unit _ :
        (structureModule ⟨X, hX⟩).IsQuasicoherentOnSite)
  · exact SheafOfModules.IsQuasicoherentOnSite.of_isZero
      (DerivedCategory.isZero_of_isLE _ 0 i hi)

variable (hX) in
/-- `𝒪_X[0]`, as an object of `D_QCoh(𝒪_X)`. -/
def unitQuasicoherent : QuasicoherentDerivedCategory.{u, u} B S hS X hX :=
  ⟨(DerivedCategory.singleFunctor _ 0).obj (structureModule ⟨X, hX⟩),
    qcohDerived_singleFunctor_structureModule⟩

/-- `H⁰(𝒪_X[0]) ≅ 𝒪_X`. -/
abbrev homologyUnitIso :
    (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) 0).obj
        ((DerivedCategory.singleFunctor _ 0).obj (structureModule ⟨X, hX⟩)) ≅
      structureModule ⟨X, hX⟩ :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app (structureModule ⟨X, hX⟩)

/-- The comparison of morphisms `𝒪_X[0] ⟶ E` with sections of `H⁰(E)` over a final object `T`:
apply `H⁰` and take the global section of `H⁰(E)` that the resulting map `𝒪_X ⟶ H⁰(E)`
corresponds to. -/
def homFromUnitSections (T : SmallEtale B S hS X) (hT : IsTerminal T)
    (E : DerivedCategory (Modules.{u, u} B S hS X hX)) :
    ((DerivedCategory.singleFunctor _ 0).obj (structureModule ⟨X, hX⟩) ⟶ E) →+
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) 0).obj E).val.obj (op T) :=
  let M := (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) 0).obj E
  let toFun : ((DerivedCategory.singleFunctor _ 0).obj (structureModule ⟨X, hX⟩) ⟶ E) →
      M.val.obj (op T) := fun x =>
    sectionsEquivOfTerminal M hT (M.unitHomEquiv
      ((homologyUnitIso (hX := hX)).inv ≫
        (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) 0).map x))
  { toFun := toFun
    map_zero' := by
      simp only [toFun, Functor.map_zero, Limits.comp_zero]
      rfl
    map_add' := fun x y => by
      simp only [toFun, Functor.map_add, Preadditive.comp_add]
      rfl }

/-- The comparison of `homFromUnitSections` is natural. -/
theorem homFromUnitSections_comp (T : SmallEtale B S hS X) (hT : IsTerminal T)
    {E E' : DerivedCategory (Modules.{u, u} B S hS X hX)}
    (x : (DerivedCategory.singleFunctor _ 0).obj (structureModule ⟨X, hX⟩) ⟶ E) (g : E ⟶ E') :
    homFromUnitSections T hT E' (x ≫ g) =
      (((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) 0).map g).val.app
        (op T)).hom (homFromUnitSections T hT E x) := by
  simp only [homFromUnitSections, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Functor.map_comp,
    SheafOfModules.unitHomEquiv_comp_apply]
  rfl

/-- The comparison of `homFromUnitSections` is bijective on `D_QCoh(𝒪_X)`, when `T` is a final
object of the small étale site with affine underlying scheme. -/
theorem bijective_homFromUnitSections (T : SmallEtale B S hS X) (hT : IsTerminal T)
    (hTa : IsAffineChart B S hS X T) (E : DerivedCategory (Modules.{u, u} B S hS X hX))
    (hE : QcohDerived B S hS ⟨X, hX⟩ E) :
    Function.Bijective (homFromUnitSections T hT E) := by
  set M := (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) 0).obj E
  let e1 := homologyUnitIso (hX := hX)
  have key : ⇑(homFromUnitSections T hT E) =
      (sectionsEquivOfTerminal M hT) ∘ (M.unitHomEquiv) ∘ (fun y => e1.inv ≫ y) ∘
        (fun x => (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) 0).map x) :=
    rfl
  rw [key]
  exact (sectionsEquivOfTerminal M hT).bijective.comp ((M.unitHomEquiv).bijective.comp
    (Function.Bijective.comp ⟨fun a b h => by simpa using congrArg (e1.hom ≫ ·) h,
      fun y => ⟨e1.hom ≫ y, by simp⟩⟩ (bijective_homologyFunctor_map_fromUnit T hT hTa E hE)))

/-- **`𝒪_X[0]` is a compact object of `D_QCoh(𝒪_X)`**, when the small étale site has a final
object `T` with affine underlying scheme: morphisms out of it are the sections over `T` of the
zeroth cohomology sheaf, cohomology commutes with direct sums, and so do the sections over the
quasi-compact object `T`. -/
theorem isCompactObject_unitQuasicoherent (T : SmallEtale B S hS X) (hT : IsTerminal T)
    (hTa : IsAffineChart B S hS X T) :
    IsCompactObject.{u} (unitQuasicoherent hX) := by
  constructor
  intro I _ E _
  classical
  let P := QcohDerived B S hS ⟨X, hX⟩
  have hclosed : P.IsClosedUnderColimitsOfShape (Discrete I) :=
    isClosedUnderCoproducts_quasicoherentDerivedCategory B S hS X hX I
      fun M hM => isQuasicoherentOnSite_sigma_of_h03DX B S hS X hX
        (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS X hX) M hM
  have hH := Stacks.Duality.preservesColimitsOfShape_derivedHomologyFunctor
    (Modules.{u, u} B S hS X hX) (J := I) 0
  let H := P.ι ⋙ DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) 0
  let c : Cofan (fun i => H.obj (E i)) := Cofan.mk (H.obj (∐ E)) fun i => H.map (Sigma.ι E i)
  have hc' : IsColimit c := Cofan.isColimitMapCoconeEquiv H E (Cofan.mk (∐ E) (Sigma.ι E))
    (isColimitOfPreserves H (coproductIsCoproduct E))
  have hσ := Stacks.Sites.bijective_coproductSectionsMap c hc' T
    (isQuasiCompactObject_of_isAffine B S hS X T hTa)
  let ψ₀ : ∀ Y : QuasicoherentDerivedCategory.{u, u} B S hS X hX,
      (unitQuasicoherent hX ⟶ Y) →+ (H.obj Y).val.obj (op T) := fun Y =>
    (homFromUnitSections T hT Y.obj).comp (Functor.mapAddHom (F := P.ι))
  have hψ₀ : ∀ Y, Function.Bijective (ψ₀ Y) := fun Y =>
    (bijective_homFromUnitSections T hT hTa Y.obj Y.property).comp
      (P.fullyFaithfulι.map_bijective _ _)
  have hnat : ∀ {Y Y' : QuasicoherentDerivedCategory.{u, u} B S hS X hX}
      (x : unitQuasicoherent hX ⟶ Y) (g : Y ⟶ Y'),
      ψ₀ Y' (x ≫ g) = ((H.map g).val.app (op T)).hom (ψ₀ Y x) := fun x g =>
    homFromUnitSections_comp T hT (P.ι.map x) (P.ι.map g)
  let α : (DirectSum I fun i => (unitQuasicoherent hX ⟶ E i)) ≃+
      DirectSum I fun i => ((H.obj (E i)).val.obj (op T) : Type u) :=
    DFinsupp.mapRange.addEquiv fun i => AddEquiv.ofBijective (ψ₀ (E i)) (hψ₀ (E i))
  have hcomm : (ψ₀ (∐ E)).comp (DirectSum.toAddMonoid fun i =>
        Preadditive.rightComp (unitQuasicoherent hX) (Sigma.ι E i)) =
      (Stacks.Sites.coproductSectionsMap c (op T)).toAddMonoidHom.comp α.toAddMonoidHom := by
    refine DirectSum.addHom_ext fun i x => ?_
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, DirectSum.toAddMonoid_of,
      AddEquiv.coe_toAddMonoidHom, LinearMap.toAddMonoidHom_coe]
    rw [show (Preadditive.rightComp (unitQuasicoherent hX) (Sigma.ι E i)) x = x ≫ Sigma.ι E i
      from rfl, hnat, show α (DirectSum.of _ i x) = DirectSum.of _ i (ψ₀ (E i) x) from
      DFinsupp.mapRange_single (f := fun i => ψ₀ (E i)) (hf := fun i => map_zero _)]
    exact (Stacks.Sites.coproductSectionsMap_lof c (op T) i _).symm
  have h1 : Function.Bijective ((ψ₀ (∐ E)) ∘ (DirectSum.toAddMonoid fun i =>
      Preadditive.rightComp (unitQuasicoherent hX) (Sigma.ι E i))) := by
    rw [← AddMonoidHom.coe_comp, hcomm, AddMonoidHom.coe_comp]
    exact hσ.comp α.bijective
  exact (Function.Bijective.of_comp_iff' (hψ₀ (∐ E)) _).1 h1

/-- **`𝒪_X[0]` is a weak generator of `D_QCoh(𝒪_X)`**, when the small étale site has a final
object with affine underlying scheme. -/
theorem isWeakTriangulatedGenerator_unitQuasicoherent (T : SmallEtale B S hS X)
    (hT : IsTerminal T) (hTa : IsAffineChart B S hS X T) :
    (ObjectProperty.singleton (unitQuasicoherent hX)).IsWeakTriangulatedGenerator := by
  rw [ObjectProperty.isWeakTriangulatedGenerator_iff]
  intro K hK
  by_contra hcon
  push Not at hcon
  refine hK (ObjectProperty.isZero_fullSubcategory_of_isZero_obj ?_)
  refine isZero_of_forall_homFromUnit_eq_zero T hT hTa K.obj K.property fun q g => ?_
  let P := QcohDerived B S hS ⟨X, hX⟩
  let e := (P.ι.commShiftIso q).app K
  have h0 := hcon _ ((ObjectProperty.singleton_iff _ _).2 rfl) q
    (P.fullyFaithfulι.preimage (X := unitQuasicoherent hX) (Y := K⟦q⟧) (g ≫ e.inv))
  have h1 : g ≫ e.inv = 0 := by
    have h2 := congrArg P.ι.map h0
    rwa [Functor.FullyFaithful.map_preimage, Functor.map_zero] at h2
  simpa using congrArg (· ≫ e.hom) h1

/-! ### Affine algebraic spaces -/

variable (B S hS) in
/-- The étale chart of a presheaf presented by an isomorphism with a representable presheaf. -/
abbrev chartOfIso {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (T₀ : BigFppfOver B S hS)
    (i : X ≅ yoneda.obj T₀) : SmallEtale B S hS X :=
  ⟨CostructuredArrow.mk i.inv, isEtaleChart_of_isIso B S hS T₀ i.inv⟩

/-- The étale chart presented by an isomorphism with a representable presheaf is a final object
of the small étale site. -/
def isTerminalChartOfIso {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (T₀ : BigFppfOver B S hS)
    (i : X ≅ yoneda.obj T₀) : IsTerminal (chartOfIso B S hS T₀ i) :=
  IsTerminal.ofUniqueHom
    (fun A => ObjectProperty.homMk (CostructuredArrow.homMk
      (yoneda.preimage (A.obj.hom ≫ i.hom)) (by simp)))
    (fun A f => by
      apply ObjectProperty.hom_ext
      apply CostructuredArrow.hom_ext
      apply yoneda.map_injective
      have hw : yoneda.map f.hom.left ≫ i.inv = A.obj.hom := CostructuredArrow.w f.hom
      simp only [ObjectProperty.homMk_hom, CostructuredArrow.homMk_left, Functor.map_preimage]
      rw [← hw, Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- **`𝒪_X[0]` is a compact generator of `D_QCoh(𝒪_X)` for an affine algebraic space `X`.** -/
theorem isCompactObject_and_isWeakTriangulatedGenerator_unitQuasicoherent
    (hXa : IsAffineSpace B S hS X) :
    IsCompactObject.{u} (unitQuasicoherent hX) ∧
      (ObjectProperty.singleton (unitQuasicoherent hX)).IsWeakTriangulatedGenerator := by
  obtain ⟨T₀, hT₀, ⟨i⟩⟩ := hXa
  have hT := isTerminalChartOfIso T₀ i
  have hTa : IsAffineChart B S hS X (chartOfIso B S hS T₀ i) := hT₀
  exact ⟨isCompactObject_unitQuasicoherent _ hT hTa,
    isWeakTriangulatedGenerator_unitQuasicoherent _ hT hTa⟩

end AlgebraicGeometry.Space

end
