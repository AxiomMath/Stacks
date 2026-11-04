module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechAndResolutions.KInjectiveRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.DerivedSectionsPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupProductAndDerivedPushforward
public import StacksFrontier.Algebra.Homology.DerivedCategory.PostcomposedTotalRightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomologyCompIso

/-!
# Derived sections over an open and derived direct images

Let `f : X ⟶ Y` be a morphism of ringed spaces and `V ⊆ Y` an open. By the Leray identification
`RΓ(V, Rf_* -) = RΓ(f⁻¹V, -)` of [Stacks, Tag 0D5W], a morphism `φ` of `D(𝒪_X)` induces a bijection
on `H^k(V, Rf_* -)` exactly when it induces a bijection on `H^k(f⁻¹V, -)`
(`bijective_homology_map_derivedPushforward_iff`).

Let `h : X' ⟶ X` be an open immersion of ringed spaces and `U ⊆ X` an open inside its image. For
every complex `M` of `𝒪_X`-modules, the unit `M ⟶ h_*h^*M` followed by the comparison
`h_* ⟶ Rh_*` induces an isomorphism `RΓ(U, M) ⟶ RΓ(U, Rh_*h^*M)`
(`isIso_derivedSectionsOverOpen_map_pullbackUnitQ`): on a K-injective complex `I` both sides are
sections over `U`, `h^*I` being K-injective, and on sections over `U` the unit is invertible.
Combined with Tag 0D5W this is the identification `H^k(U, M) = H^k(h⁻¹U, h^*M)` of
[Stacks, Tag 0D5V].

## Main results

* `Stacks.Cohomology.OpenImmersionSections.bijective_homology_map_derivedPushforward_iff`.
* `Stacks.Cohomology.OpenImmersionSections.isIso_derivedSectionsOverOpen_map_pullbackUnitQ`.

## References

* [Stacks Project, Tag 0D5V](https://stacks.math.columbia.edu/tag/0D5V)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsLeray Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces
  (pushforwardComparisonQ pushforwardComparisonQ_naturality)
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces (pushforwardComplex)

universe u

namespace Stacks.Cohomology.OpenImmersionSections

attribute [local instance] HasDerivedCategory.standard

section Leray

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (V : Opens Y.carrier)

/-- Restriction of scalars along `f^♯ : Γ(V, 𝒪_Y) ⟶ Γ(f⁻¹V, 𝒪_X)`. -/
abbrev restrictPreimage :
    ModuleCat.{u} ((structureSheafRing X).obj.obj (op ((opensMap f).obj V))) ⥤
      ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V)) :=
  ModuleCat.restrictScalars ((structureSheafHom f).hom.app (op V)).hom

/-- Restriction of scalars along `f^♯` is an additive functor. -/
instance restrictPreimage_additive : (restrictPreimage f V).Additive where
  map_add := rfl

/-- Restriction of scalars along `f^♯` preserves finite limits. -/
instance restrictPreimage_preservesFiniteLimits : PreservesFiniteLimits (restrictPreimage f V) :=
  inferInstanceAs (PreservesFiniteLimits
    (ModuleCat.restrictScalars.{u} ((structureSheafHom f).hom.app (op V)).hom))

/-- Restriction of scalars along `f^♯` preserves finite colimits. -/
instance restrictPreimage_preservesFiniteColimits :
    PreservesFiniteColimits (restrictPreimage f V) :=
  inferInstanceAs (PreservesFiniteColimits
    (ModuleCat.restrictScalars.{u} ((structureSheafHom f).hom.app (op V)).hom))

/-- Derived sections over `f⁻¹V` with scalars restricted along `f^♯` are the derived functor of
sections over `f⁻¹V` with scalars restricted: restriction of scalars is exact. -/
def preimageSectionsOverOpenIso :
    derivedSectionsOverOpen X ((opensMap f).obj V) ⋙ (restrictPreimage f V).mapDerivedCategory ≅
      derivedPreimageSections f V :=
  Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedMapDerivedCategoryIso
    (sectionsOverOpen X ((opensMap f).obj V)) (restrictPreimage f V)

/-- **A morphism of `D(𝒪_X)` induces a bijection on `H^k(V, Rf_* -)` exactly when it induces a
bijection on `H^k(f⁻¹V, -)`**, by the Leray identification of [Stacks, Tag 0D5W]. -/
theorem bijective_homology_map_derivedPushforward_iff
    {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} (φ : K ⟶ L) (k : ℤ) :
    Function.Bijective ((DerivedCategory.homologyFunctor _ k).map
        ((derivedSectionsOverOpen Y V).map ((derivedPushforward f).map φ))) ↔
      Function.Bijective ((DerivedCategory.homologyFunctor _ k).map
        ((derivedSectionsOverOpen X ((opensMap f).obj V)).map φ)) := by
  rw [← ConcreteCategory.isIso_iff_bijective, ← ConcreteCategory.isIso_iff_bijective]
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) k
  let res := restrictPreimage f V
  have e₄ : IsIso (res.map ((DerivedCategory.homologyFunctor _ k).map
        ((derivedSectionsOverOpen X ((opensMap f).obj V)).map φ))) ↔
      IsIso ((DerivedCategory.homologyFunctor _ k).map
        ((derivedSectionsOverOpen X ((opensMap f).obj V)).map φ)) := by
    rw [ConcreteCategory.isIso_iff_bijective, ConcreteCategory.isIso_iff_bijective]
    exact Iff.rfl
  exact (NatIso.isIso_map_iff
      (Functor.isoWhiskerRight (derivedSectionsPushforwardIso f V) H) φ).trans
    ((NatIso.isIso_map_iff
        (Functor.isoWhiskerRight (preimageSectionsOverOpenIso f V) H) φ).symm.trans
      ((NatIso.isIso_map_iff
        (Functor.isoWhiskerLeft (derivedSectionsOverOpen X ((opensMap f).obj V))
          (res.mapDerivedCategoryHomologyFunctorIso k)) φ).trans e₄))

end Leray

section OpenImmersion

variable {X' X : RingedSpace.{u, u}} (h : X' ⟶ X) [SheafedSpace.IsOpenImmersion h]

/-- The unit `M ⟶ h_*h^*M` of the adjunction `h^* ⊣ h_*`, applied degreewise to a complex. -/
abbrev pullbackUnitComplex (M : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    M ⟶ (pushforwardComplex h).obj
      (((modulePullback h).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) :=
  (Adjunction.mapHomologicalComplexAdjunction (modulePullbackPushforwardAdjunction h)
    (ComplexShape.up ℤ)).unit.app M

/-- The unit `M ⟶ h_*h^*M` followed by the comparison `h_* ⟶ Rh_*`. -/
abbrev pullbackUnitQ (M : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    DerivedCategory.Q.obj M ⟶ (derivedPushforward h).obj (DerivedCategory.Q.obj
      (((modulePullback h).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) :=
  DerivedCategory.Q.map (pullbackUnitComplex h M) ≫ pushforwardComparisonQ h _

omit [SheafedSpace.IsOpenImmersion h] in
/-- The comparison `pullbackUnitQ` is natural in the complex. -/
theorem pullbackUnitQ_naturality
    {M N : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ} (q : M ⟶ N) :
    pullbackUnitQ h M ≫ (derivedPushforward h).map (DerivedCategory.Q.map
        (((modulePullback h).mapHomologicalComplex (ComplexShape.up ℤ)).map q)) =
      DerivedCategory.Q.map q ≫ pullbackUnitQ h N := by
  have h₁ := (Adjunction.mapHomologicalComplexAdjunction (modulePullbackPushforwardAdjunction h)
    (ComplexShape.up ℤ)).unit.naturality q
  have h₂ := pushforwardComparisonQ_naturality h
    (((modulePullback h).mapHomologicalComplex (ComplexShape.up ℤ)).map q)
  have h₃ : DerivedCategory.Q.map (pullbackUnitComplex h M) ≫ DerivedCategory.Q.map
      ((pushforwardComplex h).map (((modulePullback h).mapHomologicalComplex
        (ComplexShape.up ℤ)).map q)) =
      DerivedCategory.Q.map q ≫ DerivedCategory.Q.map (pullbackUnitComplex h N) :=
    (DerivedCategory.Q.map_comp _ _).symm.trans ((congrArg DerivedCategory.Q.map h₁.symm).trans
      (DerivedCategory.Q.map_comp _ _))
  exact (Category.assoc _ _ _).trans
    ((congrArg (DerivedCategory.Q.map (pullbackUnitComplex h M) ≫ ·) h₂.symm).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pushforwardComparisonQ h _) h₃).trans
        (Category.assoc _ _ _))))

/-- Any functor out of the derived category inverts `quotientCompQhIso.hom`. -/
private theorem isIso_map_quotientCompQhIso_hom_app
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A] {D : Type*} [Category D]
    (F : DerivedCategory A ⥤ D) (K : CochainComplex A ℤ) :
    IsIso (F.map ((DerivedCategory.quotientCompQhIso A).hom.app K)) :=
  Functor.map_isIso _ _

omit [SheafedSpace.IsOpenImmersion h] in
/-- On a K-injective complex the comparison `h_* ⟶ Rh_*` is an isomorphism. -/
private theorem isIso_pushforwardComparisonQ_of_isKInjective
    (J : CochainComplex (SheafOfModules.{u} (structureSheafRing X')) ℤ)
    (hJ : CochainComplex.IsKInjective J) :
    IsIso (pushforwardComparisonQ h J) := by
  have hu := isIso_derivedPushforwardUnit_app_of_isKInjective h _ hJ
  unfold pushforwardComparisonQ
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance (@IsIso.comp_isIso _ _ _ _ _ _ _ hu
    (isIso_map_quotientCompQhIso_hom_app (derivedPushforward h) J))

variable (U : Opens X.carrier) (hU : (U : Set X.carrier) ⊆ Set.range h.hom.base)

include hU in
/-- The unit `M ⟶ h_*h^*M` is an isomorphism on sections over an open inside the image of `h`. -/
private theorem isIso_sectionsOverOpen_map_pullbackUnitComplex
    (M : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    IsIso (((sectionsOverOpen X U).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (pullbackUnitComplex h M)) := by
  have : ∀ n, IsIso ((((sectionsOverOpen X U).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (pullbackUnitComplex h M)).f n) := fun n => openImmersion_unit_app_isIso h (M.X n) U hU
  exact HomologicalComplex.Hom.isIso_of_components _

include hU in
/-- On a K-injective complex the unit induces an isomorphism on derived sections over an open
inside the image of `h`, seen through the homotopy category. -/
private theorem isIso_derivedSectionsOverOpen_map_Qh_pullbackUnitComplex_of_isKInjective
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) [I.IsKInjective] :
    IsIso ((derivedSectionsOverOpen X U).map (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (pullbackUnitComplex h I)))) := by
  have hFI : CochainComplex.IsKInjective
      (((modulePullback h).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    openImmersionModulePullback_preservesKInjective h I
  have hΓ := isIso_sectionsOverOpen_map_pullbackUnitComplex h U hU I
  have hΓh : IsIso ((homotopySectionsOverOpen X U).map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (pullbackUnitComplex h I))) := by
    show IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      (((sectionsOverOpen X U).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (pullbackUnitComplex h I))))
    infer_instance
  have hu₁ : IsIso ((derivedSectionsOverOpenUnit X U).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
        u, u + 1, u + 1, u + 1, u + 1, u + 1}
        (homotopySectionsOverOpen X U) (exists_quasiIso_isKInjective X)).2
      DerivedCategory.Qh (derivedSectionsOverOpen X U) (derivedSectionsOverOpenUnit X U) I
      inferInstance
  have hu₂ : IsIso ((derivedSectionsOverOpenUnit X U).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj ((pushforwardComplex h).obj
        (((modulePullback h).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)))) :=
    Stacks.Cohomology.DerivedSectionsPullback.isIso_derivedSectionsOverOpenUnit_app_pushforward
      h U _ hFI
  exact IsIso.of_isIso_fac_left (f := (derivedSectionsOverOpenUnit X U).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))
    ((derivedSectionsOverOpenUnit X U).naturality _).symm

include hU in
/-- On a K-injective complex the unit induces an isomorphism on derived sections over an open
inside the image of `h`. -/
private theorem isIso_derivedSectionsOverOpen_map_Q_pullbackUnitComplex_of_isKInjective
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) [I.IsKInjective] :
    IsIso ((derivedSectionsOverOpen X U).map
      (DerivedCategory.Q.map (pullbackUnitComplex h I))) := by
  have hQh := isIso_derivedSectionsOverOpen_map_Qh_pullbackUnitComplex_of_isKInjective h U hU I
  have e := DerivedCategory.quotientCompQhIso_hom_naturality (pullbackUnitComplex h I)
  have e' : DerivedCategory.Q.map (pullbackUnitComplex h I) =
      (DerivedCategory.quotientCompQhIso _).inv.app I ≫ DerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (pullbackUnitComplex h I)) ≫
      (DerivedCategory.quotientCompQhIso _).hom.app _ := by
    rw [e, Iso.inv_hom_id_app_assoc]
  have := isIso_map_quotientCompQhIso_hom_app (derivedSectionsOverOpen X U)
    ((pushforwardComplex h).obj
      (((modulePullback h).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))
  rw [e', Functor.map_comp, Functor.map_comp]
  infer_instance

include hU in
/-- On a K-injective complex the unit and the comparison induce an isomorphism on derived
sections over an open inside the image of `h`. -/
theorem isIso_derivedSectionsOverOpen_map_pullbackUnitQ_of_isKInjective
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) [I.IsKInjective] :
    IsIso ((derivedSectionsOverOpen X U).map (pullbackUnitQ h I)) := by
  have hpc := isIso_pushforwardComparisonQ_of_isKInjective h _
    (openImmersionModulePullback_preservesKInjective h I)
  have hQ := isIso_derivedSectionsOverOpen_map_Q_pullbackUnitComplex_of_isKInjective h U hU I
  refine (congrArg IsIso ((derivedSectionsOverOpen X U).map_comp _ _)).mpr ?_
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hQ (@Functor.map_isIso _ _ _ _ _ _ _ _ hpc)

include hU in
/-- **The unit of `h^* ⊣ h_*` followed by `h_* ⟶ Rh_*` is an isomorphism on derived sections over
an open inside the image of the open immersion `h`**, for every complex: this is
[Stacks, Tag 0D5V] read through Tag 0D5W. -/
theorem isIso_derivedSectionsOverOpen_map_pullbackUnitQ
    (M : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    IsIso ((derivedSectionsOverOpen X U).map (pullbackUnitQ h M)) := by
  obtain ⟨I, q, hI, hq⟩ := exists_quasiIso_isKInjective X M
  have := hI
  have := isIso_derivedSectionsOverOpen_map_pullbackUnitQ_of_isKInjective h U hU I
  have : (modulePullback h).PreservesHomology := openImmersionModulePullback_preservesHomology h
  have hQq : IsIso (DerivedCategory.Q.map q) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hq
  have hQFq : IsIso (DerivedCategory.Q.map
      (((modulePullback h).mapHomologicalComplex (ComplexShape.up ℤ)).map q)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  have e := congrArg (derivedSectionsOverOpen X U).map (pullbackUnitQ_naturality h q)
  rw [Functor.map_comp, Functor.map_comp] at e
  exact IsIso.of_isIso_fac_right e

end OpenImmersion

end Stacks.Cohomology.OpenImmersionSections
