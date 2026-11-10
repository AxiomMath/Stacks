module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UnderlyingAbelianSheafCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SectionsWithSupport
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
import StacksCore.Tactic.StacksAttribute

/-!
# Sections with support and the underlying abelian sheaf

Let `Z` be a closed subset of a ringed space `X` with open complement `U = X ∖ Z`, and let `K`
be an object of the unbounded derived category `D(O_X)`.  Writing `K_ab` for the image of `K`
in the unbounded derived category of abelian sheaves on `X`, the canonical comparison
`RΓ_Z(X, K) ⟶ RΓ_Z(X, K_ab)` is an isomorphism in `D(Ab)`: forgetting the module structure
does not change cohomology with support in `Z`.

## Main definitions

* `abelianSectionsWithSupport`: global sections of an abelian sheaf vanishing on `U`, that is
  the kernel of restriction from `X` to `U`.
* `ordinarySectionsWithSupportForgetIso`: the underived comparison, an isomorphism because
  both forgetful functors preserve the kernel defining sections with support.
* `sectionsWithSupportForgetComparison`: the canonical map `RΓ_Z(X, K) ⟶ RΓ_Z(X, K_ab)`.

## Main results

* `sectionsWithSupportForgetComparison_isIso` (Tag 0G74, part (1)): the canonical map is an
  isomorphism.

## Implementation notes

As in Tag 0G71 the two derived functors are quantified over rather than fixed: the statement
is made for arbitrary functors on the unbounded derived category equipped with
`Functor.IsRightDerivedFunctor` data, and `exists_rightDerivedFunctor_sectionsWithSupport`
records that such data exists on both sides, so the statement is not about an empty family.

The comparison is invertible because it is invertible on K-injective complexes of
`O_X`-modules, and those suffice since modules on a ringed space form a Grothendieck abelian
category.  On a K-injective complex `I` with injective terms the argument is the source's,
in the following form.  Sections with support are a kernel, so it is enough to know that the
comparison for sections over `X` and over `U` is invertible at `I`, which is Tag 0D5Y, and
that the two short complexes `Γ_Z ⟶ Γ(X, -) ⟶ Γ(U, -)` computing the kernel are short exact
on the complexes involved.  Short exactness needs surjectivity of restriction to `U`, which is
Tag 01EA for an injective module sheaf and its abelian-sheaf form for an injective abelian
sheaf; the abelian K-injective resolution supplied by Tag 079P has injective terms, so both
apply.  Two of the three vertical maps of the resulting morphism of short exact sequences are
then quasi-isomorphisms, hence so is the third, by the two-out-of-three property for
distinguished triangles of Tag 014A.

A general K-injective complex of `O_X`-modules is replaced at the outset by one with injective
terms, which is the functorial resolution of Tag 079P; the replacement is harmless because the
comparison between two K-injective complexes connected by a quasi-isomorphism is an
isomorphism in the homotopy category.

## References

* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Lemma 20.32.7 (Tag 0D5Y)](https://stacks.math.columbia.edu/tag/0D5Y)
* [Stacks Project, Lemma 20.8.1 (Tag 01EA)](https://stacks.math.columbia.edu/tag/01EA)
* [Stacks Project, Lemma 20.26.4 (Tag 079P)](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Lemma 13.4.3 (Tag 014A)](https://stacks.math.columbia.edu/tag/014A)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.Pretriangulated
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.OpenSubspace
open Stacks.Cohomology.Localization (derivedUnit_isIsoOnKInjective
  enoughKInjectives rightDerived_of_kInjectives)
open Stacks.Cohomology.SectionsWithSupport
open Stacks.Cohomology.UnderlyingAbelianSheaf

universe u

namespace Stacks.Cohomology.UnderlyingAbelianSectionsWithSupport

attribute [local instance] HasDerivedCategory.standard

/-! ### Two out of three for a morphism of short exact sequences of complexes -/

/-- If the middle and right vertical maps of a morphism of short exact sequences of cochain
complexes are quasi-isomorphisms, then so is the left one. -/
private lemma quasiIso_τ₁_of_shortExact {C : Type*} [Category* C] [Abelian C]
    {S T : ShortComplex (CochainComplex C ℤ)} (φ : S ⟶ T)
    (hS : S.ShortExact) (hT : T.ShortExact)
    [QuasiIso φ.τ₂] [QuasiIso φ.τ₃] : QuasiIso φ.τ₁ := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  refine isIso₁_of_isIso₂₃ (DerivedCategory.triangleOfSES.map hS hT φ)
    (DerivedCategory.triangleOfSES_distinguished hS)
    (DerivedCategory.triangleOfSES_distinguished hT) ?_ ?_
  · change IsIso (DerivedCategory.Q.map φ.τ₂)
    infer_instance
  · change IsIso (DerivedCategory.Q.map φ.τ₃)
    infer_instance

/-- A morphism of complexes on which two additive functors act by quasi-isomorphisms acts by a
quasi-isomorphism on the kernel of a natural transformation between them, provided that
transformation is degreewise epimorphic on both complexes. -/
private lemma quasiIso_map_kernel_of_epi
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Abelian D]
    (F G : C ⥤ D) [F.Additive] [G.Additive] (τ : F ⟶ G) [(kernel τ).Additive]
    {I J : CochainComplex C ℤ} (q : I ⟶ J)
    (hI : ∀ n, Epi (τ.app (I.X n))) (hJ : ∀ n, Epi (τ.app (J.X n)))
    [QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map q)]
    [QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map q)] :
    QuasiIso (((kernel τ).mapHomologicalComplex (ComplexShape.up ℤ)).map q) := by
  let S (K : CochainComplex C ℤ) : ShortComplex (CochainComplex D ℤ) :=
    ShortComplex.mk (((kernel.ι τ).mapHomologicalComplex (ComplexShape.up ℤ)).app K)
      ((τ.mapHomologicalComplex (ComplexShape.up ℤ)).app K) (by
        ext n
        exact NatTrans.congr_app (kernel.condition τ) (K.X n))
  have hS (K : CochainComplex C ℤ) (hK : ∀ n, Epi (τ.app (K.X n))) : (S K).ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro n
    have := hK n
    refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · exact (ShortComplex.kernelSequence_exact τ).map
        ((CategoryTheory.evaluation C D).obj (K.X n))
    · exact inferInstanceAs (Mono (((CategoryTheory.evaluation C D).obj (K.X n)).map
        (kernel.ι τ)))
    · exact hK n
  let φ : S I ⟶ S J :=
    { τ₁ := ((kernel τ).mapHomologicalComplex (ComplexShape.up ℤ)).map q
      τ₂ := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map q
      τ₃ := (G.mapHomologicalComplex (ComplexShape.up ℤ)).map q
      comm₁₂ := ((kernel.ι τ).mapHomologicalComplex (ComplexShape.up ℤ)).naturality q
      comm₂₃ := (τ.mapHomologicalComplex (ComplexShape.up ℤ)).naturality q }
  exact quasiIso_τ₁_of_shortExact φ (hS I hI) (hS J hJ)

/-! ### Transporting invertibility of a derivation unit along a quasi-isomorphism -/

/-- For a transformation into a functor inverting a morphism, invertibility at the source is
equivalent to invertibility of the functor on that morphism, given invertibility at the
target. -/
private lemma isIso_map_iff_of_unit {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (L : C ⥤ D) (F : C ⥤ E) (RF : D ⥤ E) (α : F ⟶ L ⋙ RF)
    {I J : C} (q : I ⟶ J) [IsIso (L.map q)] [IsIso (α.app J)] :
    IsIso (F.map q) ↔ IsIso (α.app I) := by
  have : IsIso ((L ⋙ RF).map q) := by
    dsimp
    infer_instance
  rw [← isIso_comp_right_iff (F.map q) (α.app J), α.naturality, isIso_comp_right_iff]

/-- Along a quasi-isomorphism whose target already has invertible derivation unit, the unit is
invertible at the source exactly when the functor sends the quasi-isomorphism to one. -/
private lemma quasiIso_map_iff_of_derivedUnit {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] (RF : DerivedCategory C ⥤ DerivedCategory D)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    {I J : CochainComplex C ℤ} (q : I ⟶ J) [QuasiIso q]
    [IsIso (α.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj J))] :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map q) ↔
      IsIso (α.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I)) := by
  change HomologicalComplex.quasiIso D (ComplexShape.up ℤ) _ ↔ _
  rw [← HomotopyCategory.quotient_map_mem_quasiIso_iff, ← DerivedCategory.isIso_Qh_map_iff,
    ← F.mapHomotopyCategory_map q]
  have : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map q)) := by
    rw [DerivedCategory.isIso_Qh_map_iff, HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact ‹QuasiIso q›
  exact isIso_map_iff_of_unit DerivedCategory.Qh _ RF α _

/-- The derivation unit of a kernel functor is invertible wherever the units of the two
functors it is built from are, along a quasi-isomorphism that is degreewise epimorphic for the
transformation defining the kernel. -/
private lemma isIso_kernel_unit_app_of_epi {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F G : C ⥤ D) [F.Additive] [G.Additive] (τ : F ⟶ G) (hτ : (kernel τ).Additive)
    (RF RG RK : DerivedCategory C ⥤ DerivedCategory D)
    (αF : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (αG : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RG)
    (αK : (kernel τ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RK)
    {I J : CochainComplex C ℤ} (q : I ⟶ J) (hq : QuasiIso q)
    (hI : ∀ n, Epi (τ.app (I.X n))) (hJ : ∀ n, Epi (τ.app (J.X n)))
    (hFI : IsIso (αF.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I)))
    (hGI : IsIso (αG.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I)))
    (hFJ : IsIso (αF.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj J)))
    (hGJ : IsIso (αG.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj J)))
    (hKJ : IsIso (αK.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj J))) :
    IsIso (αK.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I)) := by
  let := hτ
  let := hq
  let := hFI
  let := hGI
  let := hFJ
  let := hGJ
  let := hKJ
  have : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map q) :=
    (quasiIso_map_iff_of_derivedUnit F RF αF q).mpr hFI
  have : QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map q) :=
    (quasiIso_map_iff_of_derivedUnit G RG αG q).mpr hGI
  exact (quasiIso_map_iff_of_derivedUnit (kernel τ) RK αK q).mp
    (quasiIso_map_kernel_of_epi F G τ q hI hJ)

/-! ### Sections with support of an abelian sheaf -/

variable (X : RingedSpace.{u, u}) (Z : Set X) (hZ : IsClosed Z)

/-- Abelian sheaves on the underlying space of a ringed space. -/
abbrev AbelianSheavesOnSpace : Type (u + 1) :=
  Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}

/-- Restriction of a global section of an abelian sheaf to the complement of `Z`. -/
abbrev abelianRestrictionToComplement :
    abelianSectionsOnOpen X.carrier ⊤ ⟶ abelianSectionsOnOpen X.carrier (openComplement Z hZ) :=
  (sheafSections (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).map
    (homOfLE (le_top : openComplement Z hZ ≤ ⊤)).op

/-- Global sections of an abelian sheaf whose restriction to `X ∖ Z` vanishes.  For closed `Z`
these are exactly the global sections supported on `Z`. -/
def abelianSectionsWithSupport : AbelianSheavesOnSpace X ⥤ AddCommGrpCat.{u} :=
  kernel (abelianRestrictionToComplement X Z hZ)

/-- Taking abelian sections with support is additive. -/
instance abelianSectionsWithSupport_additive :
    (abelianSectionsWithSupport X Z hZ).Additive := by
  change (kernel (abelianRestrictionToComplement X Z hZ)).Additive
  constructor
  intro A B f g
  apply (cancel_mono ((kernel.ι (abelianRestrictionToComplement X Z hZ)).app B)).1
  rw [(kernel.ι (abelianRestrictionToComplement X Z hZ)).naturality]
  simp

/-- Abelian sheaves on a topological space form a Grothendieck abelian category, the site of
opens being essentially small.  This is deliberately not an instance: it would enlarge the
instance tables of every importer of the root umbrella for no gain, the only uses being inside
this file. -/
lemma abelianSheaves_isGrothendieckAbelian :
    IsGrothendieckAbelian.{u} (AbelianSheavesOnSpace X) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

attribute [local instance] abelianSheaves_isGrothendieckAbelian

/-- Modules over the ring of global functions, with their module structure forgotten. -/
abbrev forgetGlobalModules : GlobalModules X ⥤ AddCommGrpCat.{u} :=
  forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) AddCommGrpCat.{u}

/-- Forgetting the module structure on the unbounded derived category of modules over the
ring of global functions. -/
abbrev underlyingDerivedGlobalModules :
    DerivedCategory (GlobalModules X) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  (forgetGlobalModules X).mapDerivedCategory

/-- Apply abelian sections with support degreewise, then pass to the derived category. -/
abbrev homotopyAbelianSectionsWithSupport :
    HomotopyCategory (AbelianSheavesOnSpace X) (ComplexShape.up ℤ) ⥤
      DerivedCategory AddCommGrpCat.{u} :=
  (abelianSectionsWithSupport X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh

/-- The underived comparison: sections with support of a sheaf of modules, with the module
structure forgotten, are the sections with support of the underlying abelian sheaf.  Both
sides are the kernel of restriction to `X ∖ Z`, which the two forgetful functors preserve. -/
def ordinarySectionsWithSupportForgetIso :
    sectionsWithSupport X Z hZ ⋙ forgetGlobalModules X ≅
      SheafOfModules.toSheaf (structureSheafRing X) ⋙ abelianSectionsWithSupport X Z hZ :=
  PreservesKernel.iso ((Functor.whiskeringRight _ _ _).obj (forgetGlobalModules X))
      (restrictionToComplement X Z hZ) ≪≫
    (PreservesKernel.iso ((Functor.whiskeringLeft _ _ _).obj
      (SheafOfModules.toSheaf (structureSheafRing X))) (abelianRestrictionToComplement X Z hZ)).symm

/-! ### Existence of the derived functors -/

/-- Every functor out of the homotopy category of a Grothendieck abelian category has a total
right derived functor, since every complex admits a quasi-isomorphism into a K-injective one. -/
private lemma hasRightDerivedFunctor_of_grothendieckAbelian {C : Type (u + 1)} [Category.{u} C]
    [Abelian C] [IsGrothendieckAbelian.{u} C] {H : Type (u + 1)} [Category.{u + 1} H]
    (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ H) :
    F.HasRightDerivedFunctor (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  have := (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{u,
      u + 1, u + 1, u + 1, u + 1, u + 1} F
      (Stacks.Cohomology.Localization.enoughKInjectives (C := C))).1
  infer_instance

/-- Every functor out of the homotopy category of abelian sheaves on `X` has a total right
derived functor: abelian sheaves are Grothendieck abelian, so every complex admits a
quasi-isomorphism into a K-injective one. -/
lemma hasRightDerivedFunctor_abelianSheaves {H : Type (u + 1)} [Category.{u + 1} H]
    (F : HomotopyCategory (AbelianSheavesOnSpace X) (ComplexShape.up ℤ) ⥤ H) :
    F.HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (AbelianSheavesOnSpace X) (ComplexShape.up ℤ)) :=
  hasRightDerivedFunctor_of_grothendieckAbelian F

/-- Every functor out of the homotopy category of modules on the ringed space `X` has a total
right derived functor, modules on a ringed space being Grothendieck abelian. -/
lemma hasRightDerivedFunctor_moduleSheaves {H : Type (u + 1)} [Category.{u + 1} H]
    (F : HomotopyCategory (ModuleSheaves X) (ComplexShape.up ℤ) ⥤ H) :
    F.HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)) :=
  hasRightDerivedFunctor_of_grothendieckAbelian F

/-! ### The comparison on homotopy categories -/

variable (RΓZab : DerivedCategory (AbelianSheavesOnSpace X) ⥤ DerivedCategory AddCommGrpCat.{u})
  (aZab : homotopyAbelianSectionsWithSupport X Z hZ ⟶ DerivedCategory.Qh ⋙ RΓZab)

/-- The comparison on homotopy categories built from the underived comparison of sections with
support and the comparison map of a right derived functor of abelian sections with support. -/
def sectionsWithSupportForgetUnit :
    homotopyToDerived X (sectionsWithSupport X Z hZ) ⋙ underlyingDerivedGlobalModules X ⟶
      DerivedCategory.Qh ⋙ (underlyingDerivedSheaf (structureSheafRing X) ⋙ RΓZab) :=
  Functor.whiskerLeft
      ((sectionsWithSupport X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ))
      (forgetGlobalModules X).mapDerivedCategoryFactorsh.hom ≫
    (Functor.associator
      ((sectionsWithSupport X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ))
      ((forgetGlobalModules X).mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh).inv ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (ordinarySectionsWithSupportForgetIso X Z hZ)
        (ComplexShape.up ℤ)).hom DerivedCategory.Qh ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl
          (SheafOfModules.toSheaf (structureSheafRing X) ⋙ abelianSectionsWithSupport X Z hZ))
        (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    (Functor.associator
      ((SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory (ComplexShape.up ℤ))
      ((abelianSectionsWithSupport X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh).hom ≫
    Functor.whiskerLeft
      ((SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory (ComplexShape.up ℤ))
        aZab ≫
    Functor.whiskerRight
      (SheafOfModules.toSheaf (structureSheafRing X)).mapDerivedCategoryFactorsh.inv RΓZab

/-- The comparison on homotopy categories is invertible at a complex exactly when the
comparison map of the abelian derived functor is invertible at the underlying complex of
abelian sheaves: all the other factors are isomorphisms. -/
lemma sectionsWithSupportForgetUnit_app_isIso_iff
    (K : HomotopyCategory (ModuleSheaves X) (ComplexShape.up ℤ)) :
    IsIso ((sectionsWithSupportForgetUnit X Z hZ RΓZab aZab).app K) ↔
      IsIso (aZab.app
        (((SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K)) := by
  dsimp only [sectionsWithSupportForgetUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  simp only [isIso_comp_left_iff, isIso_comp_right_iff]

/-! ### Tag 0D5Y, read on derivation units -/

/-- **Tag 0D5Y, read on derivation units.**  If the derivation unit for sections of modules
over an open is invertible at a complex, then the derivation unit for abelian sections over
that open is invertible at the underlying complex of abelian sheaves. -/
private lemma abelianSectionsUnit_isIso_of_moduleSectionsUnit_isIso {Y : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}) (U : Opens Y)
    (K : HomotopyCategory (SheafOfModules.{u} O) (ComplexShape.up ℤ))
    [IsIso (((homotopySectionsOnOpen O U).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))).app K)] :
    IsIso (((homotopyAbelianSectionsOnOpen Y U).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
        (ComplexShape.up ℤ))).app
      (((SheafOfModules.toSheaf O).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) := by
  have := sectionsForgetComparison_isIso O U
  have h : IsIso ((sectionsForgetUnit O U).app K) := by
    rw [← Functor.rightDerived_fac_app (derivedSectionsOnOpen O U)
      ((homotopySectionsOnOpen O U).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)))
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))]
    change IsIso (_ ≫ (sectionsForgetComparison O U).app (DerivedCategory.Qh.obj K))
    infer_instance
  dsimp only [sectionsForgetUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app] at h
  simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using h

/-! ### Invertibility of the abelian derivation unit for sections with support -/

/-- The derivation unit for abelian sections with support is invertible at any complex of
abelian sheaves on which restriction to the complement of `Z` is degreewise surjective.  The
complex is compared with its K-injective resolution of Tag 079P, whose terms are injective,
hence also have surjective restriction by the abelian form of Tag 01EA; the units for sections
over `X` and over `X ∖ Z` are invertible at both, so the kernel inherits invertibility. -/
private lemma abelianSupportUnit_isIso_of_sectionsUnits
    (RF RG : DerivedCategory (AbelianSheavesOnSpace X) ⥤ DerivedCategory AddCommGrpCat.{u})
    (αF : homotopyAbelianSectionsOnOpen X.carrier ⊤ ⟶ DerivedCategory.Qh ⋙ RF)
    (αG : homotopyAbelianSectionsOnOpen X.carrier (openComplement Z hZ) ⟶
      DerivedCategory.Qh ⋙ RG)
    [RF.IsRightDerivedFunctor αF
      (HomotopyCategory.quasiIso (AbelianSheavesOnSpace X) (ComplexShape.up ℤ))]
    [RG.IsRightDerivedFunctor αG
      (HomotopyCategory.quasiIso (AbelianSheavesOnSpace X) (ComplexShape.up ℤ))]
    [RΓZab.IsRightDerivedFunctor aZab
      (HomotopyCategory.quasiIso (AbelianSheavesOnSpace X) (ComplexShape.up ℤ))]
    (I : CochainComplex (AbelianSheavesOnSpace X) ℤ)
    (hI : ∀ n, Epi ((abelianRestrictionToComplement X Z hZ).app (I.X n)))
    (hFI : IsIso (αF.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)))
    (hGI : IsIso (αG.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) :
    IsIso (aZab.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) := by
  let J := (Stacks.Injectives.kInjectiveResolutionFunctor (AbelianSheavesOnSpace X)).obj I
  let q : I ⟶ J := (Stacks.Injectives.kInjectiveResolutionInclusion (AbelianSheavesOnSpace X)).app I
  have hJ : ∀ n, Epi ((abelianRestrictionToComplement X Z hZ).app (J.X n)) := by
    intro n
    have : Injective (J.X n) :=
      Stacks.Injectives.kInjectiveResolutionFunctor_obj_X_injective (AbelianSheavesOnSpace X) I n
    exact (AddCommGrpCat.epi_iff_surjective _).mpr
      (@Stacks.Cohomology.InjectiveRestriction.injective_abelian_restriction_surjective
        X.carrier (J.X n) this _ _ le_top)
  exact isIso_kernel_unit_app_of_epi _ _ (abelianRestrictionToComplement X Z hZ)
    (inferInstanceAs (abelianSectionsWithSupport X Z hZ).Additive)
    RF RG RΓZab αF αG aZab q inferInstance hI hJ hFI hGI
    (Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ RF αF J)
    (Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ RG αG J)
    (Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ RΓZab aZab J)

/-! ### Invertibility on K-injective complexes of modules -/

/-- At a K-injective complex of `O_X`-modules with injective terms the comparison on homotopy
categories is invertible.  Restriction to `X ∖ Z` is surjective on the terms by Tag 01EA, and
the comparison for sections over `X` and over `X ∖ Z` is invertible there by Tag 0D5Y. -/
private lemma sectionsWithSupportForgetUnit_isIso_of_injective_kInjective
    [RΓZab.IsRightDerivedFunctor aZab
      (HomotopyCategory.quasiIso (AbelianSheavesOnSpace X) (ComplexShape.up ℤ))]
    (I : CochainComplex (ModuleSheaves X) ℤ) [I.IsKInjective]
    (hI : ∀ n, Injective (I.X n)) :
    IsIso ((sectionsWithSupportForgetUnit X Z hZ RΓZab aZab).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) := by
  let hM (U : Opens X.carrier) :
      (homotopySectionsOnOpen (structureSheafRing X) U).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)) :=
    hasRightDerivedFunctor_moduleSheaves X _
  let hA (U : Opens X.carrier) :
      (homotopyAbelianSectionsOnOpen X.carrier U).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso (AbelianSheavesOnSpace X) (ComplexShape.up ℤ)) :=
    hasRightDerivedFunctor_abelianSheaves X _
  have hunit (U : Opens X.carrier) :
      IsIso (((homotopyAbelianSectionsOnOpen X.carrier U).totalRightDerivedUnit
        DerivedCategory.Qh (HomotopyCategory.quasiIso (AbelianSheavesOnSpace X)
          (ComplexShape.up ℤ))).app
        (((SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
    have := Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective
      (homotopySectionsOnOpen (structureSheafRing X) U)
      (derivedSectionsOnOpen (structureSheafRing X) U)
      ((homotopySectionsOnOpen (structureSheafRing X) U).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))) I
    exact abelianSectionsUnit_isIso_of_moduleSectionsUnit_isIso (structureSheafRing X) U _
  refine (sectionsWithSupportForgetUnit_app_isIso_iff X Z hZ RΓZab aZab _).mpr ?_
  refine abelianSupportUnit_isIso_of_sectionsUnits X Z hZ RΓZab aZab
    ((homotopyAbelianSectionsOnOpen X.carrier ⊤).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (AbelianSheavesOnSpace X) (ComplexShape.up ℤ)))
    ((homotopyAbelianSectionsOnOpen X.carrier (openComplement Z hZ)).totalRightDerived
      DerivedCategory.Qh (HomotopyCategory.quasiIso (AbelianSheavesOnSpace X) (ComplexShape.up ℤ)))
    ((homotopyAbelianSectionsOnOpen X.carrier ⊤).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (AbelianSheavesOnSpace X) (ComplexShape.up ℤ)))
    ((homotopyAbelianSectionsOnOpen X.carrier (openComplement Z hZ)).totalRightDerivedUnit
      DerivedCategory.Qh (HomotopyCategory.quasiIso (AbelianSheavesOnSpace X) (ComplexShape.up ℤ)))
    (((SheafOfModules.toSheaf (structureSheafRing X)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I) ?_ (hunit ⊤) (hunit (openComplement Z hZ))
  intro n
  have := hI n
  exact (AddCommGrpCat.epi_iff_surjective _).mpr
    (Stacks.Cohomology.InjectiveRestriction.injective_restriction_surjective
      (structureSheafRing X) (I.X n) (le_top : openComplement Z hZ ≤ ⊤))

/-- At any K-injective complex of `O_X`-modules the comparison on homotopy categories is
invertible: the complex is compared with the K-injective resolution of Tag 079P, whose terms
are injective, and a quasi-isomorphism between K-injective complexes is already invertible in
the homotopy category. -/
private lemma sectionsWithSupportForgetUnit_isIso_of_kInjective
    [RΓZab.IsRightDerivedFunctor aZab
      (HomotopyCategory.quasiIso (AbelianSheavesOnSpace X) (ComplexShape.up ℤ))]
    (I : CochainComplex (ModuleSheaves X) ℤ) [I.IsKInjective] :
    IsIso ((sectionsWithSupportForgetUnit X Z hZ RΓZab aZab).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) := by
  let J := (Stacks.Injectives.kInjectiveResolutionFunctor (ModuleSheaves X)).obj I
  let q : I ⟶ J := (Stacks.Injectives.kInjectiveResolutionInclusion (ModuleSheaves X)).app I
  have hq : IsIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map q) := by
    apply Localization.inverts (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences (ModuleSheaves X) (ComplexShape.up ℤ))
    exact (CochainComplex.IsKInjective.quasiIso_iff q).mp inferInstance
  rw [NatTrans.isIso_app_iff_of_iso (sectionsWithSupportForgetUnit X Z hZ RΓZab aZab)
    (asIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map q))]
  exact sectionsWithSupportForgetUnit_isIso_of_injective_kInjective X Z hZ RΓZab aZab J
    (fun n => Stacks.Injectives.kInjectiveResolutionFunctor_obj_X_injective
      (ModuleSheaves X) I n)

/-- The composite of a right derived functor of abelian sections with support with forgetting
the module structure *is* a right derived functor of sections with support of modules, with
comparison `sectionsWithSupportForgetUnit`. -/
lemma isRightDerivedFunctor_sectionsWithSupportForgetUnit
    [RΓZab.IsRightDerivedFunctor aZab
      (HomotopyCategory.quasiIso (AbelianSheavesOnSpace X) (ComplexShape.up ℤ))] :
    (underlyingDerivedSheaf (structureSheafRing X) ⋙ RΓZab).IsRightDerivedFunctor
      (sectionsWithSupportForgetUnit X Z hZ RΓZab aZab)
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.Localization.rightDerived_of_kInjectives _ _ _
    (fun I _ => sectionsWithSupportForgetUnit_isIso_of_kInjective X Z hZ RΓZab aZab I)

/-! ### The canonical comparison of Tag 0G74 (1) -/

variable (RΓZ : DerivedModuleSheaves X ⥤ DerivedGlobalModules X)
  (aZ : homotopyToDerived X (sectionsWithSupport X Z hZ) ⟶ DerivedCategory.Qh ⋙ RΓZ)

/-- The comparison map of a right derived functor of sections with support, composed with
forgetting the module structure on the derived category. -/
def forgetfulSectionsWithSupportUnit :
    homotopyToDerived X (sectionsWithSupport X Z hZ) ⋙ underlyingDerivedGlobalModules X ⟶
      DerivedCategory.Qh ⋙ (RΓZ ⋙ underlyingDerivedGlobalModules X) :=
  Functor.whiskerRight aZ (underlyingDerivedGlobalModules X) ≫ (Functor.associator _ _ _).hom

/-- Forgetting the module structure on the derived category of modules over the global
functions is exact, so it carries a right derived functor of sections with support to one
again. -/
instance isRightDerivedFunctor_forgetfulSectionsWithSupportUnit
    [RΓZ.IsRightDerivedFunctor aZ
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))] :
    (RΓZ ⋙ underlyingDerivedGlobalModules X).IsRightDerivedFunctor
      (forgetfulSectionsWithSupportUnit X Z hZ RΓZ aZ)
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)) := by
  refine Stacks.Cohomology.Localization.rightDerived_of_kInjectives _ _ _ (fun I _ => ?_)
  have := Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ RΓZ aZ I
  dsimp only [forgetfulSectionsWithSupportUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.associator_hom_app]
  infer_instance

/-- **Stacks 0G74, part (1): the canonical map.**  Let `Z` be a closed subset of a ringed space
`X`, let `RΓZ` be a right derived functor of sections with support in `Z` of sheaves of
`O_X`-modules and `RΓZab` one of sections with support in `Z` of abelian sheaves.  This is the
canonical map `RΓ_Z(X, K) ⟶ RΓ_Z(X, K_ab)` in `D(Ab)`, natural in `K`, induced through the
universal property of `RΓZ` by the underived comparison of sections with support. -/
@[stacks 0G74
  "part (1), the canonical map, for given right derived functors of sections with support"]
def sectionsWithSupportForgetComparison
    [RΓZ.IsRightDerivedFunctor aZ
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))]
    [RΓZab.IsRightDerivedFunctor aZab
      (HomotopyCategory.quasiIso (AbelianSheavesOnSpace X) (ComplexShape.up ℤ))] :
    RΓZ ⋙ underlyingDerivedGlobalModules X ⟶
      underlyingDerivedSheaf (structureSheafRing X) ⋙ RΓZab :=
  (RΓZ ⋙ underlyingDerivedGlobalModules X).rightDerivedDesc
    (forgetfulSectionsWithSupportUnit X Z hZ RΓZ aZ)
    (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)) _
    (sectionsWithSupportForgetUnit X Z hZ RΓZab aZab)

/-- The canonical map of Tag 0G74 (1) is pinned down by its composite with the comparison map
of `RΓ_Z(X, -)`: it is the unique transformation compatible with the underived comparison. -/
lemma sectionsWithSupportForgetComparison_fac
    [RΓZ.IsRightDerivedFunctor aZ
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))]
    [RΓZab.IsRightDerivedFunctor aZab
      (HomotopyCategory.quasiIso (AbelianSheavesOnSpace X) (ComplexShape.up ℤ))] :
    forgetfulSectionsWithSupportUnit X Z hZ RΓZ aZ ≫ Functor.whiskerLeft DerivedCategory.Qh
        (sectionsWithSupportForgetComparison X Z hZ RΓZab aZab RΓZ aZ) =
      sectionsWithSupportForgetUnit X Z hZ RΓZab aZab :=
  Functor.rightDerived_fac _ _ _ _ _

/-- **Stacks 0G74, part (1).**  Let `(X, O_X)` be a ringed space, `Z ⊆ X` a closed subset and
`K` an object of `D(O_X)` with image `K_ab` in `D(ℤ_X)`.  The canonical map
`RΓ_Z(X, K) ⟶ RΓ_Z(X, K_ab)` is an isomorphism in `D(Ab)`, naturally in `K`. -/
@[stacks 0G74
  "part (1), the map is an isomorphism, for given right derived functors of Gamma_Z"]
instance sectionsWithSupportForgetComparison_isIso
    [RΓZ.IsRightDerivedFunctor aZ
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))]
    [RΓZab.IsRightDerivedFunctor aZab
      (HomotopyCategory.quasiIso (AbelianSheavesOnSpace X) (ComplexShape.up ℤ))] :
    IsIso (sectionsWithSupportForgetComparison X Z hZ RΓZab aZab RΓZ aZ) := by
  have := isRightDerivedFunctor_sectionsWithSupportForgetUnit X Z hZ RΓZab aZab
  exact (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc
    (RΓZ ⋙ underlyingDerivedGlobalModules X)
    (forgetfulSectionsWithSupportUnit X Z hZ RΓZ aZ)
    (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)) _
    (sectionsWithSupportForgetUnit X Z hZ RΓZab aZab)).mp inferInstance

/-- Both sides of the comparison of Tag 0G74 (1) have models, so the statement is not about an
empty family: total right derived functors exist for sections with support of modules and of
abelian sheaves alike. -/
lemma exists_rightDerivedFunctor_sectionsWithSupport :
    (homotopyToDerived X (sectionsWithSupport X Z hZ)).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)) ∧
      (homotopyAbelianSectionsWithSupport X Z hZ).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso (AbelianSheavesOnSpace X) (ComplexShape.up ℤ)) :=
  ⟨hasRightDerivedFunctor_moduleSheaves X _, hasRightDerivedFunctor_abelianSheaves X _⟩

end Stacks.Cohomology.UnderlyingAbelianSectionsWithSupport

end
