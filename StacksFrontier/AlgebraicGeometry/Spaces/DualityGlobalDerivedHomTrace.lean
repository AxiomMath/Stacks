module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedGlobalSectionsAtModel
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedGlobalSectionsPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityPullbackComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityPushforwardTrace
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPushforwardAffine
public import StacksFrontier.Algebra.Homology.HomotopyCategory.HomComplexFromSinglePostcomp
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.Existence
public import StacksFrontier.Homology.Injectives.Ext.SpectralSequenceIntoFunctoriality
import StacksCore.Tactic.StacksAttribute

/-!
# The trace map on global derived homs for algebraic spaces

Let `f : X ⟶ Y` be a morphism of quasi-compact and quasi-separated algebraic spaces, `a` the
right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, `L` in `D_QCoh(𝒪_X)` and `K` in
`D_QCoh(𝒪_Y)`. The map `Rf_*R𝓗om(L, a(K)) ⟶ R𝓗om(Rf_*L, K)` of Stacks 0E57 induces, through
`RΓ(X, -) = RΓ(Y, Rf_* -)` (Stacks 0D6H), a map of global derived homs

`RHom_X(L, a(K)) = RΓ(X, R𝓗om(L, a(K))) ⟶ RΓ(Y, R𝓗om(Rf_*L, K)) = RHom_Y(Rf_*L, K)`,

read in `D(Γ(Y, 𝒪_Y))`, and it is an isomorphism (Stacks 0E59): the map of Stacks 0E57 induces
bijections on morphisms out of every object of `D_QCoh(𝒪_Y)` (the proof of Stacks 0E58), in
particular out of the shifts of `𝒪_Y`, and these compute the cohomology of `RΓ(Y, -)`.

## Main results

* `AlgebraicGeometry.Space.isIso_derivedModuleGlobalSectionsSmallEtale_map`: `RΓ(Y, -)` inverts
  a morphism inducing bijections on morphisms out of every object of `D_QCoh(𝒪_Y)`.
* `AlgebraicGeometry.Space.globalDerivedHomTrace`: the map of global derived homs.
* `AlgebraicGeometry.Space.isIso_globalDerivedHomTrace`: **Stacks 0E59**.

## References

* [Stacks Project, Tag 0E59](https://stacks.math.columbia.edu/tag/0E59)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
attribute [local instance] ModuleCat.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules CochainComplex.HomComplex

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 20000] ModuleCat.hasDerivedCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Global sections of a morphism of complexes of `𝒪_Y`-modules is a quasi-isomorphism as soon as
postcomposition with each of its shifts is bijective on morphisms out of `𝒪_Y[0]` in the homotopy
category: global sections are corepresented by `𝒪_Y`. -/
theorem quasiIso_moduleGlobalSectionsSmallEtale_map (Y : AlgebraicSpaces B S hS)
    {I J : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ} (s : I ⟶ J)
    (h : ∀ n : ℤ, Function.Bijective
      (fun a : (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).obj
            (SheafOfModules.unit
              (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))) ⟶
          (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (I⟦n⟧) =>
        a ≫ (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (s⟦n⟧'))) :
    QuasiIso (((moduleGlobalSectionsSmallEtale.{u, u} B S hS Y.1 Y.2).mapHomologicalComplex
      (ComplexShape.up ℤ)).map s) := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (forget₂ (ModuleCat.{u + 1} (globalSectionRingSmallEtale B S hS Y.1 Y.2))
      AddCommGrpCat.{u + 1}), quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : IsIso (HomologicalComplex.homologyMap (homComplexPostcomp
      ((CochainComplex.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).obj
        (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))) s)
      n) :=
    Stacks.Injectives.isIso_homologyMap_homComplexPostcomp _ s n (h n)
  exact (NatIso.isIso_map_iff (Functor.isoWhiskerRight
    (NatIso.mapHomologicalComplex
      (coyonedaUnitGlobalSectionsIso
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
      (ComplexShape.up ℤ))
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℤ) n)) s).1
    (isIso_homologyMap_coyonedaComplexMap _ s n)

/-- Every object of `D(𝒪_Y)` is the image in the derived category of a K-injective complex. -/
private theorem exists_isKInjective_qh_iso (Y : AlgebraicSpaces B S hS)
    (A : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) :
    ∃ I : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ, I.IsKInjective ∧
      Nonempty (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I) ≅
        A) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := exists_isKInjective_iso_modules B S hS A
  exact ⟨I, hI, ⟨(DerivedCategory.quotientCompQhIso _).app I ≪≫ e.symm⟩⟩

/-- **`RΓ(Y, -)` inverts a morphism inducing bijections on morphisms out of `D_QCoh(𝒪_Y)`.**
If `φ : A ⟶ A'` in `D(𝒪_Y)` induces a bijection `Hom(M, A) ⟶ Hom(M, A')` for every `M` with
quasi-coherent cohomology, then `RΓ(Y, φ)` is an isomorphism: `H^n(Y, -) = Hom(𝒪_Y, -[n])`. -/
theorem isIso_derivedModuleGlobalSectionsSmallEtale_map (Y : AlgebraicSpaces B S hS)
    {A A' : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)} (φ : A ⟶ A')
    (h : ∀ M : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2), QcohDerived B S hS Y M →
      Function.Bijective fun g : M ⟶ A => g ≫ φ) :
    IsIso ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS Y.1 Y.2).map φ) := by
  have := isGrothendieckAbelian_modules B S hS Y.1 Y.2
  let q := HomotopyCategory.quotient (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ)
  obtain ⟨I, hI, ⟨eI⟩⟩ := exists_isKInjective_qh_iso Y A
  obtain ⟨J, hJ, ⟨eJ⟩⟩ := exists_isKInjective_qh_iso Y A'
  have := hI
  have := hJ
  obtain ⟨t, ht⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (q.obj I) J).2
    (eI.hom ≫ φ ≫ eJ.inv)
  obtain ⟨s, rfl⟩ := q.map_surjective t
  let F := q ⋙ DerivedCategory.Qh
  have hF : ∀ M : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2), QcohDerived B S hS Y M →
      Function.Bijective fun g : M ⟶ F.obj I => g ≫ F.map s :=
    InternalHomTrace.bijective_comp_of_arrow_iso h eI.symm eJ.symm
      (by simp [F, ht])
  -- the structure sheaf in degree zero, in the homotopy category
  let P := q.obj ((CochainComplex.singleFunctor (Modules.{u, u} B S hS Y.1 Y.2) 0).obj
    (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)))
  have hP : QcohDerived B S hS Y (DerivedCategory.Qh.obj P) :=
    (QcohDerived B S hS Y).prop_of_iso ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _ ≪≫
        (((DerivedCategory.quotientCompQhIso _).app _).symm : _ ≅ DerivedCategory.Qh.obj P))
      (derivedCategoryB_singleFunctor_obj B S hS Y.1 Y.2 _ inferInstance)
  have hqi := quasiIso_moduleGlobalSectionsSmallEtale_map Y s fun n => by
    have h₁ := InternalHomTrace.bijective_comp_shift (F.map s)
      (fun n M hM => (QcohDerived B S hS Y).le_shift n M hM) hF n _ hP
    have h₂ := InternalHomTrace.bijective_comp_of_arrow_iso
      (P := fun M => M = DerivedCategory.Qh.obj P)
      (fun M hM => hM ▸ h₁) ((F.commShiftIso n).app I).symm ((F.commShiftIso n).app J).symm
      ((F.commShiftIso n).inv.naturality s) _ rfl
    refine (Function.Bijective.of_comp_iff'
      (CochainComplex.IsKInjective.Qh_map_bijective P (J⟦n⟧)) _).1 ?_
    have hcomp : (DerivedCategory.Qh.map : (P ⟶ q.obj (J⟦n⟧)) → _) ∘
        (fun a : P ⟶ q.obj (I⟦n⟧) => a ≫ q.map (s⟦n⟧')) =
        (fun b : DerivedCategory.Qh.obj P ⟶ F.obj (I⟦n⟧) => b ≫ F.map (s⟦n⟧')) ∘
          (DerivedCategory.Qh.map : (P ⟶ q.obj (I⟦n⟧)) → _) :=
      funext fun a => DerivedCategory.Qh.map_comp a _
    rw [hcomp]
    exact h₂.comp (CochainComplex.IsKInjective.Qh_map_bijective P (I⟦n⟧))
  let Γh := (moduleGlobalSectionsSmallEtale.{u, u} B S hS Y.1 Y.2).mapHomotopyCategory
    (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  let α := Γh.totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))
  have hαI : IsIso (α.app (q.obj I)) :=
    Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective Γh DerivedCategory.Qh _ α I hI
  have hαJ : IsIso (α.app (q.obj J)) :=
    Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective Γh DerivedCategory.Qh _ α J hJ
  have hΓ : IsIso (Γh.map (q.map s)) := by
    change IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
      (((moduleGlobalSectionsSmallEtale.{u, u} B S hS Y.1 Y.2).mapHomologicalComplex
        (ComplexShape.up ℤ)).map s)))
    rwa [DerivedCategory.isIso_Qh_map_iff, HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomologicalComplex.mem_quasiIso_iff]
  have hR : IsIso ((derivedModuleGlobalSectionsSmallEtaleAtModel B S hS Y.1 Y.2).map
      (DerivedCategory.Qh.map (q.map s))) := by
    have : IsIso (α.app (q.obj I) ≫ (DerivedCategory.Qh ⋙ Γh.totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))).map
          (q.map s)) := by
      rw [← α.naturality (q.map s)]
      infer_instance
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ (α.app (q.obj I)) _ hαI this
  have hφ : φ = eI.inv ≫ DerivedCategory.Qh.map (q.map s) ≫ eJ.hom := by
    rw [ht]
    simp
  rw [hφ, Functor.map_comp, Functor.map_comp]
  infer_instance

variable (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
  (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
  (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)

/-- **The map of global derived homs induced by Stacks 0E57**,
`RHom_X(L, a(K)) = RΓ(X, R𝓗om(L, a(K))) ≅ RΓ(Y, Rf_*R𝓗om(L, a(K))) ⟶ RΓ(Y, R𝓗om(Rf_*L, K))
= RHom_Y(Rf_*L, K)`, read in `D(Γ(Y, 𝒪_Y))`. -/
def globalDerivedHomTrace (L : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    (derivedModuleGlobalSectionsRestricted B S hS f).obj
        (((smallEtaleDerivedSheafHom B S hS X).obj (op L.obj)).obj
          ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj K).obj) ⟶
      (derivedModuleGlobalSectionsSmallEtaleAtModel B S hS Y.1 Y.2).obj
        (((smallEtaleDerivedSheafHom B S hS Y).obj
          (op ((derivedModulePushforward B S hS f).obj L.obj))).obj K.obj) :=
  (derivedModulePushforwardGlobalSectionsIso B S hS f).inv.app _ ≫
    (derivedModuleGlobalSectionsSmallEtaleAtModel B S hS Y.1 Y.2).map
      (smallEtalePushforwardTrace hZ f hXqc hXqs hYqs L K)

/-- **Stacks 0E59.** Let `f : X ⟶ Y` be a morphism of quasi-separated and quasi-compact algebraic
spaces. For all `L` in `D_QCoh(𝒪_X)` and `K` in `D_QCoh(𝒪_Y)` the map of Stacks 0E57 induces an
isomorphism `RHom_X(L, a(K)) ⟶ RHom_Y(Rf_*L, K)` of global derived homs. -/
@[stacks 0E59]
theorem isIso_globalDerivedHomTrace (L : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    IsIso (globalDerivedHomTrace hZ f hXqc hXqs hYqs L K) := by
  have hfqc := isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hXqc f.hom
  have hfqs := isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X.2 hXqs f.hom
  have h := isIso_derivedModuleGlobalSectionsSmallEtale_map Y
    (smallEtalePushforwardTrace hZ f hXqc hXqs hYqs L K) fun M hM => by
      let adj := quasicoherentDerivedRightAdjointAdjunction hZ f hXqc hXqs hYqs hfqc hfqs
      let E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 :=
        ⟨((smallEtaleDerivedTensor B S hS X).obj
            ((smallEtaleDerivedModulePullback B S hS f).obj M)).obj L.obj,
          qcohDerived_smallEtaleDerivedTensor X _ _
            (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ f M hM) L.property⟩
      refine InternalHomTrace.bijective_comp_pushforwardTrace _ _ _ _ _ _ _ _ L.obj _ M
        (isIso_smallEtaleProjectionFormulaMapSnd B S hS f hfqc hfqs M hM L.obj L.property) ?_
      have key : (fun v : E.obj ⟶
          ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj K).obj =>
          (derivedModulePushforward B S hS f).map v ≫ (adj.counit.app K).hom) =
          (fun w => w.hom) ∘ (adj.homEquiv E K).symm ∘
            ((ObjectProperty.fullyFaithfulι (QcohDerived B S hS X)).homEquiv (X := E)
              (Y := (quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj K)).symm := by
        funext v
        simp only [Function.comp_apply, Adjunction.homEquiv_counit]
        rfl
      exact key ▸ ((ObjectProperty.fullyFaithfulι (QcohDerived B S hS Y)).homEquiv.bijective.comp
        ((adj.homEquiv E K).symm.bijective.comp
          (ObjectProperty.fullyFaithfulι (QcohDerived B S hS X)).homEquiv.symm.bijective))
  rw [globalDerivedHomTrace]
  exact @IsIso.comp_isIso' _ _ _ _ _ _ _
    ((derivedModulePushforwardGlobalSectionsIso B S hS f).app _).isIso_inv h

end AlgebraicGeometry.Space

end
