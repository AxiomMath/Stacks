module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPointCohomologyFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRelocalize
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPerfect

/-!
# Perfect objects do not see the base scheme

Let `h : S ⟶ S'` be a morphism of schemes of a big fppf site, `X` an algebraic space over `S` and
`Λ_h X` the same space viewed over `S'` (the lower shriek of Stacks 03I5 (2); the absolute view
`AlgebraicGeometry.Space.viewOverIntegers` is the case `S' = Spec ℤ`). The small étale sites of `X`
and of `Λ_h X` are equivalent, by an equivalence which does not change the underlying schemes of
the charts (`AlgebraicGeometry.Space.SmallEtale.relocalizeEquivalence`), and the structure sheaf of
`X` is the restriction of that of `Λ_h X`. So restriction along the equivalence identifies the
`𝒪_{Λ_h X}`-modules with the `𝒪_X`-modules, and this identification preserves perfect objects of
the derived categories (Stacks 08G5) in both directions.

This is the first step of the reduction, in the proof of Stacks 0CTM, of a statement over an
arbitrary base scheme to the same statement over `Spec ℤ`, where Noetherian approximation of the
base ring is available.

## Main definitions

* `AlgebraicGeometry.Space.relocalizeModulesEquiv`: the `𝒪_{Λ_h X}`-modules are the
  `𝒪_X`-modules.
* `AlgebraicGeometry.Space.relocalizeGlobalSectionsIso`: global sections read as
  `Γ(T, 𝒪_T)`-modules along `f : X ⟶ T` are global sections along a morphism `Λ_h X ⟶ Λ_h T`
  pulling back the same functions to the charts.

## Main results

* `CategoryTheory.hasLimitsOfShape_structuredArrow_op_of_isEquivalence`: structured arrows on the
  opposite of an equivalence have an initial object, so restriction of sheaves along an equivalence
  of large sites is an equivalence.
* `AlgebraicGeometry.Space.isPerfect_relocalizeModulesEquiv_functor`,
  `AlgebraicGeometry.Space.isPerfect_relocalizeModulesEquiv_inverse`: the identification preserves
  perfect objects in both directions.
* `AlgebraicGeometry.Space.isRightDerivedFunctor_equivalenceTransport`: the direct image to the
  point, read through an equivalence of module categories, is a right derived functor of any
  functor identified with it.
* `AlgebraicGeometry.Space.isPseudoCoherent_pointDerivedEquiv_derivedPushforward_of_relocalize`:
  pseudo-coherence of `Rf_*E` over `Γ(T, 𝒪_T)` for perfect `E` passes from `Λ_h X ⟶ Λ_h T` to
  `X ⟶ T`.

## References

* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 0CTM](https://stacks.math.columbia.edu/tag/0CTM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.DenseSubsiteModules
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace CategoryTheory

/-- Structured arrows on the opposite of an equivalence have an initial object, so every functor
out of them has a limit: the hypothesis under which restriction of sheaves along a dense subsite
is an equivalence, for the dense subsite given by an equivalence of large categories. -/
theorem hasLimitsOfShape_structuredArrow_op_of_isEquivalence {C D : Type*} [Category* C]
    [Category* D] (F : C ⥤ D) [F.IsEquivalence] (A : Type*) [Category* A] (X : Dᵒᵖ) :
    Limits.HasLimitsOfShape (StructuredArrow X F.op) A :=
  have : Limits.HasInitial (StructuredArrow X F.op) :=
    (mkInitialOfLeftAdjoint F.op F.op.asEquivalence.symm.toAdjunction X).hasInitial
  ⟨fun _ => inferInstance⟩

end CategoryTheory

namespace AlgebraicGeometry.Space

attribute [local instance] hasLimitsOfShape_structuredArrow_op_of_isEquivalence
attribute [local instance 2000] SmallEtale.instHasSheafify SmallEtale.instHasSheafifyOver
  SmallEtale.instWEqualsLocallyBijective SmallEtale.instWEqualsLocallyBijectiveOver

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.Sites.overPost_isDenseSubsite

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (h : B.obj hS ⟶ B.obj hS') (X : AlgebraicSpaces B S hS)
  (hX' : IsAlgebraicSpace B S' hS' ((OverShriek.relocalizePresheafFunctor h).obj X.1))

/-- The small étale ringed site of the relocalized space, written as a structure literal. -/
abbrev relocalizeRingedSite : RingedSite.{u + 1, u, u} where
  C := SmallEtale B S' hS' ((OverShriek.relocalizePresheafFunctor h).obj X.1)
  J := SmallEtale.topology B S' hS' ((OverShriek.relocalizePresheafFunctor h).obj X.1)
  O := structureSheaf B S' hS' _ hX'

/-- **The `𝒪_{Λ_h X}`-modules are the `𝒪_X`-modules**: the Comparison Lemma along the equivalence
of small étale sites, the structure sheaf of `X` being the restriction of that of `Λ_h X`. -/
def relocalizeModulesEquiv :
    Modules.{u, u} B S' hS' _ hX' ≌ Modules.{u, u} B S hS X.1 X.2 :=
  (relocalizeRingedSite B S S' hS hS' h X hX').denseSubsiteModulesEquiv
    (SmallEtale.topology B S hS X.1) (SmallEtale.relocalizeEquivalence B S S' hS hS' h X.1).functor

/-- The identification of module categories is additive. -/
instance additive_relocalizeModulesEquiv_functor :
    (relocalizeModulesEquiv B S S' hS hS' h X hX').functor.Additive :=
  (exact_functor_of_equivalence _).1

/-- The inverse identification of module categories is additive. -/
instance additive_relocalizeModulesEquiv_inverse :
    (relocalizeModulesEquiv B S S' hS hS' h X hX').inverse.Additive :=
  (exact_functor_of_equivalence (relocalizeModulesEquiv B S S' hS hS' h X hX').symm).1

/-- **Restriction from `Λ_h X` to `X` preserves perfect objects.** -/
theorem isPerfect_relocalizeModulesEquiv_functor
    (K : DerivedCategory (Modules.{u, u} B S' hS' _ hX'))
    (hK : (smallEtaleRingedSite B S' hS' _ hX').IsPerfect K) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect
      ((relocalizeModulesEquiv B S S' hS hS' h X hX').functor.mapDerivedCategory.obj K) :=
  RingedSite.isPerfect_mapDerivedCategory_moduleRestriction.{u + 1, u, u + 1, u, u}
    (relocalizeRingedSite B S S' hS hS' h X hX')
    (SmallEtale.topology B S hS X.1) (SmallEtale.relocalizeEquivalence B S S' hS hS' h X.1).functor
    K hK

/-- **Extension from `X` to `Λ_h X` preserves perfect objects.** -/
theorem isPerfect_relocalizeModulesEquiv_inverse
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hK : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect K) :
    (smallEtaleRingedSite B S' hS' _ hX').IsPerfect
      ((relocalizeModulesEquiv B S S' hS hS' h X hX').inverse.mapDerivedCategory.obj K) :=
  RingedSite.isPerfect_mapDerivedCategory_moduleRestrictionEquivalence_inverse.{u + 1, u, u + 1, u,
    u}
    (relocalizeRingedSite B S S' hS hS' h X hX')
    (SmallEtale.topology B S hS X.1) (SmallEtale.relocalizeEquivalence B S S' hS hS' h X.1).functor
    K hK

/-! ### Global sections -/

section GlobalSections

variable {T : BigFppfOver B S hS} (f : X ⟶ schemeSpace T)
  (f' : (⟨(OverShriek.relocalizePresheafFunctor h).obj X.1, hX'⟩ : AlgebraicSpaces B S' hS') ⟶
    schemeSpace ((Over.map h).obj T))

/-- Morphisms out of `𝒪_X` into the restriction of an `𝒪_{Λ_h X}`-module `N` are morphisms out of
`𝒪_{Λ_h X}` into `N`. -/
def relocalizeUnitHomEquiv (N : Modules.{u, u} B S' hS' _ hX') :
    (unitModule B S hS X.2 ⟶ (relocalizeModulesEquiv B S S' hS hS' h X hX').functor.obj N) ≃
      (unitModule B S' hS' hX' ⟶ N) :=
  ((relocalizeModulesEquiv B S S' hS hS' h X hX').fullyFaithfulFunctor.homEquiv
    (X := unitModule B S' hS' hX') (Y := N)).symm

variable {f f'} in
/-- Restriction carries multiplication by a global function of `Λ_h X` pulled back from `T` to
multiplication by the corresponding global function of `X`, when the two pullbacks agree on the
charts of `X`. -/
theorem relocalizeModulesEquiv_functor_map_unitModuleMul
    (hcompat : ∀ (r : baseRing B S hS T) (V : SmallEtale B S hS X.1),
      (globalFunctionsOfMap f' r).1
          (op ((SmallEtale.relocalizeEquivalence B S S' hS hS' h X.1).functor.obj V)) =
        (globalFunctionsOfMap f r).1 (op V))
    (r : baseRing B S hS T) :
    (relocalizeModulesEquiv B S S' hS hS' h X hX').functor.map
        (unitModuleMul B S' hS' _ (globalFunctionsOfMap f' r)) =
      unitModuleMul B S hS X (globalFunctionsOfMap f r) := by
  refine (SheafOfModules.unitHomEquiv (unitModule B S hS X.2)).injective ?_
  refine Subtype.ext (funext fun V => ?_)
  have h₁ := unitModuleMul_val_app_one B S' hS'
    (⟨(OverShriek.relocalizePresheafFunctor h).obj X.1, hX'⟩ : AlgebraicSpaces B S' hS')
    (globalFunctionsOfMap f' r)
    ((SmallEtale.relocalizeEquivalence B S S' hS hS' h X.1).functor.obj V.unop)
  have h₂ := unitModuleMul_val_app_one B S hS X (globalFunctionsOfMap f r) V.unop
  exact h₁.trans ((hcompat r V.unop).trans h₂.symm)

variable {f f'}
variable (hcompat : ∀ (r : baseRing B S hS T) (V : SmallEtale B S hS X.1),
      (globalFunctionsOfMap f' r).1
          (op ((SmallEtale.relocalizeEquivalence B S S' hS hS' h X.1).functor.obj V)) =
        (globalFunctionsOfMap f r).1 (op V))

/-- The comparison of global sections underlying `relocalizeGlobalSectionsIso`. -/
def relocalizeSectionsEquiv (N : Modules.{u, u} B S' hS' _ hX') :
    (baseRingGlobalSectionsModule B S hS X (baseRingHomOfMap f)).obj
        ((relocalizeModulesEquiv B S S' hS hS' h X hX').functor.obj N) ≃
      (baseRingGlobalSectionsModule B S' hS'
        (⟨(OverShriek.relocalizePresheafFunctor h).obj X.1, hX'⟩ : AlgebraicSpaces B S' hS')
        (baseRingHomOfMap f')).obj N :=
  ((modelSectionsHomEquiv B S hS X (baseRingHomOfMap f) _).trans
    (relocalizeUnitHomEquiv B S S' hS hS' h X hX' N)).trans
      (modelSectionsHomEquiv B S' hS' _ (baseRingHomOfMap f') N).symm

/-- `relocalizeUnitHomEquiv` is inverse to restriction. -/
theorem relocalizeUnitHomEquiv_map (N : Modules.{u, u} B S' hS' _ hX')
    (a : unitModule B S hS X.2 ⟶ (relocalizeModulesEquiv B S S' hS hS' h X hX').functor.obj N) :
    (relocalizeModulesEquiv B S S' hS hS' h X hX').functor.map
      (relocalizeUnitHomEquiv B S S' hS hS' h X hX' N a) = a :=
  ((relocalizeModulesEquiv B S S' hS hS' h X hX').fullyFaithfulFunctor.homEquiv
    (X := unitModule B S' hS' hX') (Y := N)).apply_symm_apply a

/-- `relocalizeUnitHomEquiv` is additive. -/
theorem relocalizeUnitHomEquiv_add (N : Modules.{u, u} B S' hS' _ hX')
    (a b : unitModule B S hS X.2 ⟶ (relocalizeModulesEquiv B S S' hS hS' h X hX').functor.obj N) :
    relocalizeUnitHomEquiv B S S' hS hS' h X hX' N (a + b) =
      relocalizeUnitHomEquiv B S S' hS hS' h X hX' N a +
        relocalizeUnitHomEquiv B S S' hS hS' h X hX' N b :=
  (relocalizeModulesEquiv B S S' hS hS' h X hX').functor.map_injective
    (by simp [relocalizeUnitHomEquiv_map]; rfl)

/-- `relocalizeUnitHomEquiv` commutes with precomposition by an endomorphism of the unit. -/
theorem relocalizeUnitHomEquiv_comp (N : Modules.{u, u} B S' hS' _ hX')
    (a : unitModule B S' hS' hX' ⟶ unitModule B S' hS' hX')
    (b : unitModule B S hS X.2 ⟶ (relocalizeModulesEquiv B S S' hS hS' h X hX').functor.obj N) :
    relocalizeUnitHomEquiv B S S' hS hS' h X hX' N
        ((relocalizeModulesEquiv B S S' hS hS' h X hX').functor.map a ≫ b) =
      a ≫ relocalizeUnitHomEquiv B S S' hS hS' h X hX' N b :=
  (relocalizeModulesEquiv B S S' hS hS' h X hX').functor.map_injective
    (by simp [relocalizeUnitHomEquiv_map]; rfl)

/-- `relocalizeUnitHomEquiv` is natural in the module. -/
theorem relocalizeUnitHomEquiv_naturality {N N' : Modules.{u, u} B S' hS' _ hX'} (g : N ⟶ N')
    (b : unitModule B S hS X.2 ⟶ (relocalizeModulesEquiv B S S' hS hS' h X hX').functor.obj N) :
    relocalizeUnitHomEquiv B S S' hS hS' h X hX' N'
        (b ≫ (relocalizeModulesEquiv B S S' hS hS' h X hX').functor.map g) =
      relocalizeUnitHomEquiv B S S' hS hS' h X hX' N b ≫ g :=
  (relocalizeModulesEquiv B S S' hS hS' h X hX').functor.map_injective
    (by simp [relocalizeUnitHomEquiv_map]; rfl)

include hcompat in
/-- `relocalizeSectionsEquiv` is linear. -/
def relocalizeSectionsLinearEquiv (N : Modules.{u, u} B S' hS' _ hX') :
    (baseRingGlobalSectionsModule B S hS X (baseRingHomOfMap f)).obj
        ((relocalizeModulesEquiv B S S' hS hS' h X hX').functor.obj N) ≃ₗ[baseRing B S hS T]
      (baseRingGlobalSectionsModule B S' hS'
        (⟨(OverShriek.relocalizePresheafFunctor h).obj X.1, hX'⟩ : AlgebraicSpaces B S' hS')
        (baseRingHomOfMap f')).obj N where
  toEquiv := relocalizeSectionsEquiv B S S' hS hS' h X hX' N
  map_add' a b := by
    change (modelSectionsHomEquiv B S' hS' _ (baseRingHomOfMap f') N).symm
        (relocalizeUnitHomEquiv B S S' hS hS' h X hX' N
          (modelSectionsHomEquiv B S hS X (baseRingHomOfMap f) _ (a + b))) =
      (modelSectionsHomEquiv B S' hS' _ (baseRingHomOfMap f') N).symm
        (relocalizeUnitHomEquiv B S S' hS hS' h X hX' N
          (modelSectionsHomEquiv B S hS X (baseRingHomOfMap f) _ a)) +
      (modelSectionsHomEquiv B S' hS' _ (baseRingHomOfMap f') N).symm
        (relocalizeUnitHomEquiv B S S' hS hS' h X hX' N
          (modelSectionsHomEquiv B S hS X (baseRingHomOfMap f) _ b))
    rw [modelSectionsHomEquiv_add, relocalizeUnitHomEquiv_add, modelSectionsHomEquiv_symm_add]
  map_smul' r a := by
    change (modelSectionsHomEquiv B S' hS' _ (baseRingHomOfMap f') N).symm
        (relocalizeUnitHomEquiv B S S' hS hS' h X hX' N
          (modelSectionsHomEquiv B S hS X (baseRingHomOfMap f) _ (r • a))) =
      r • (modelSectionsHomEquiv B S' hS' _ (baseRingHomOfMap f') N).symm
        (relocalizeUnitHomEquiv B S S' hS hS' h X hX' N
          (modelSectionsHomEquiv B S hS X (baseRingHomOfMap f) _ a))
    rw [modelSectionsHomEquiv_smul,
      ← relocalizeModulesEquiv_functor_map_unitModuleMul B S S' hS hS' h X hX' hcompat r]
    refine (congrArg (modelSectionsHomEquiv B S' hS' _ (baseRingHomOfMap f') N).symm
      (relocalizeUnitHomEquiv_comp B S S' hS hS' h X hX' N
        (unitModuleMul B S' hS' _ (globalFunctionsOfMap f' r))
        (modelSectionsHomEquiv B S hS X (baseRingHomOfMap f) _ a))).trans ?_
    exact modelSectionsHomEquiv_symm_comp B S' hS' _ f' N r _

include hcompat in
/-- **Global sections do not see the base scheme.** Restricting an `𝒪_{Λ_h X}`-module to `X` and
taking global sections over `X` as `Γ(T, 𝒪_T)`-modules along `f : X ⟶ T` is taking global
sections over `Λ_h X` along `f' : Λ_h X ⟶ Λ_h T`, as soon as `f` and `f'` pull back the same
functions to the charts of `X`. -/
def relocalizeGlobalSectionsIso :
    (relocalizeModulesEquiv B S S' hS hS' h X hX').functor ⋙
        baseRingGlobalSectionsModule B S hS X (baseRingHomOfMap f) ≅
      baseRingGlobalSectionsModule B S' hS'
        (⟨(OverShriek.relocalizePresheafFunctor h).obj X.1, hX'⟩ : AlgebraicSpaces B S' hS')
        (baseRingHomOfMap f') :=
  NatIso.ofComponents
    (fun N => (relocalizeSectionsLinearEquiv B S S' hS hS' h X hX' hcompat N).toModuleIso)
    (fun {_ N'} g => ModuleCat.hom_ext (LinearMap.ext fun a =>
      (congrArg (fun v => (modelSectionsHomEquiv B S' hS' _ (baseRingHomOfMap f') N').symm
          (relocalizeUnitHomEquiv B S S' hS hS' h X hX' N' v))
          (modelSectionsHomEquiv_naturality B S hS X (baseRingHomOfMap f)
            ((relocalizeModulesEquiv B S S' hS hS' h X hX').functor.map g) a)).trans
        ((congrArg (modelSectionsHomEquiv B S' hS' _ (baseRingHomOfMap f') N').symm
          (relocalizeUnitHomEquiv_naturality B S S' hS hS' h X hX' g
            (modelSectionsHomEquiv B S hS X (baseRingHomOfMap f) _ a))).trans
        (modelSectionsHomEquiv_symm_naturality B S' hS' _ (baseRingHomOfMap f') g _))))

end GlobalSections

/-! ### The direct image to the point, read through an equivalence of module categories -/

section Transport

attribute [local instance] hasCoproducts_derivedCategory_modules

variable {Y : AlgebraicSpaces B S' hS'} {R : Type u} [CommRing R]
  (ψ : R →+* modelGlobalFunctions B S' hS' Y)
  (e : (spacesEtaleModelRingedTopos B S' hS' Y).Modules ≌ Modules.{u, u} B S hS X.1 X.2)
  [e.inverse.Additive] (Γ : Modules.{u, u} B S hS X.1 X.2 ⥤ ModuleCat.{u} R) [Γ.Additive]
  (ι : e.inverse ⋙ (spacesEtaleModelToBaseRing B S' hS' Y ψ).pushforwardTopos ⋙
      (baseRingPointModulesEquiv (R := R)).functor ≅ Γ)
  (Rf : DerivedCategory (spacesEtaleModelRingedTopos B S' hS' Y).Modules ⥤
    DerivedCategory (pointRingedTopos (CommRingCat.of R)).Modules)
  (αf : (spacesEtaleModelToBaseRing B S' hS' Y ψ).pushforwardTopos.mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)

include ι in
/-- The unit exhibiting `Rf_*`, read through an equivalence `e` of module categories and in
`D(R)`, as a right derived functor of a functor `Γ` identified with the direct image read through
`e`. -/
def equivalenceTransportUnit :
    Γ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (e.inverse.mapDerivedCategory ⋙
        Rf ⋙ (baseRingPointModulesEquiv (R := R)).functor.mapDerivedCategory) :=
  Functor.whiskerRight (mapHomotopyCategoryIsoOfIso ι.symm).hom DerivedCategory.Qh ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl _)
      (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    Functor.whiskerLeft (e.inverse.mapHomotopyCategory (ComplexShape.up ℤ))
      (Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl _)
          (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
        Functor.whiskerLeft
          ((spacesEtaleModelToBaseRing B S' hS' Y ψ).pushforwardTopos.mapHomotopyCategory
            (ComplexShape.up ℤ))
          (baseRingPointModulesEquiv (R := R)).functor.mapDerivedCategoryFactorsh.inv ≫
        Functor.whiskerRight αf (baseRingPointModulesEquiv (R := R)).functor.mapDerivedCategory) ≫
    Functor.whiskerRight e.inverse.mapDerivedCategoryFactorsh.inv
      (Rf ⋙ (baseRingPointModulesEquiv (R := R)).functor.mapDerivedCategory)

variable [Rf.IsRightDerivedFunctor αf (HomotopyCategory.quasiIso
      (spacesEtaleModelRingedTopos B S' hS' Y).Modules (ComplexShape.up ℤ))]

include ι αf in
/-- The transported unit is invertible at every K-injective complex. -/
theorem isIso_equivalenceTransportUnit_app (I : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (hI : I.IsKInjective) :
    IsIso ((equivalenceTransportUnit B S S' hS hS' X (ψ := ψ) (e := e) (Γ := Γ) (ι := ι) (Rf := Rf)
        (αf := αf)).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) := by
  have hEI : CochainComplex.IsKInjective
      ((e.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    have := hI
    have := (exact_functor_of_equivalence e).1
    CochainComplex.isKInjective_mapHomologicalComplex_of_exact e.inverse e.functor
      e.toAdjunction I
  have hf : IsIso (αf.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      ((e.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) := by
    obtain ⟨Rs⟩ := Stacks.Injectives.exists_functorial_quasiIso_isKInjective.{u}
      (spacesEtaleModelRingedTopos B S' hS' Y).Modules
    exact (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      ((spacesEtaleModelToBaseRing B S' hS' Y ψ).pushforwardTopos.mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (fun K ↦ ⟨Rs.functor.obj K, Rs.inclusion.app K, Rs.isKInjective K, Rs.quasiIso K⟩)).2
        DerivedCategory.Qh Rf αf _ hEI
  have : IsIso (αf.app ((e.inverse.mapHomotopyCategory
      (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := hf
  simp only [equivalenceTransportUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  infer_instance

include ι αf in
/-- **`Rf_*`, read through an equivalence of module categories and in `D(R)`, is a right derived
functor of any functor identified with the direct image read through the equivalence.** -/
theorem isRightDerivedFunctor_equivalenceTransport :
    Functor.IsRightDerivedFunctor (e.inverse.mapDerivedCategory ⋙
        Rf ⋙ (baseRingPointModulesEquiv (R := R)).functor.mapDerivedCategory)
      (equivalenceTransportUnit B S S' hS hS' X (ψ := ψ) (e := e) (Γ := Γ) (ι := ι) (Rf := Rf)
        (αf := αf))
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) := by
  have hgr : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS X.1 X.2) :=
    isGrothendieckAbelian_modules B S hS X.1 X.2
  exact Stacks.Cohomology.UnboundedComplexes.isRightDerivedFunctor_of_isIso_app_isKInjective
    _ DerivedCategory.Qh _ _ fun I hI ↦ isIso_equivalenceTransportUnit_app B S S' hS hS' X
      (ψ := ψ) (e := e) (Γ := Γ) (ι := ι) (Rf := Rf) (αf := αf) I hI

end Transport

/-! ### Pseudo-coherence of `Rf_*E` does not see the base scheme -/

section Invariance

attribute [local instance] hasCoproducts_derivedCategory_modules

variable {T : BigFppfOver B S hS} {f : X ⟶ schemeSpace T}
  {f' : (⟨(OverShriek.relocalizePresheafFunctor h).obj X.1, hX'⟩ : AlgebraicSpaces B S' hS') ⟶
    schemeSpace ((Over.map h).obj T)}
  (hcompat : ∀ (r : baseRing B S hS T) (V : SmallEtale B S hS X.1),
      (globalFunctionsOfMap f' r).1
          (op ((SmallEtale.relocalizeEquivalence B S S' hS hS' h X.1).functor.obj V)) =
        (globalFunctionsOfMap f r).1 (op V))

include hcompat in
/-- **Pseudo-coherence of `RΓ(X, E)` does not see the base scheme.** Let `f : X ⟶ T` and
`f' : Λ_h X ⟶ Λ_h T` pull back the same functions to the charts of `X`, both read as morphisms to
the point `(pt, Γ(T, 𝒪_T))` on the spaces-étale models. If `Rf'_*E'` is pseudo-coherent in
`D(Γ(T, 𝒪_T))` for every perfect `E'` on the model of `Λ_h X`, then so is `Rf_*E` for every perfect
`E` on the model of `X`.

Both `Rf_*` and `Rf'_*`, read through the identifications of the module categories and in
`D(Γ(T, 𝒪_T))`, are right derived functors of global sections of `𝒪_X`-modules
(`AlgebraicGeometry.Space.isRightDerivedFunctor_pointModulesTransport`,
`AlgebraicGeometry.Space.isRightDerivedFunctor_equivalenceTransport` with
`AlgebraicGeometry.Space.relocalizeGlobalSectionsIso`), hence isomorphic, and perfect objects
correspond (`AlgebraicGeometry.Space.isPerfect_relocalizeModulesEquiv_inverse`). -/
theorem isPseudoCoherent_pointDerivedEquiv_derivedPushforward_of_relocalize
    (H : ∀ E' : DerivedCategory (spacesEtaleModelRingedTopos B S' hS'
        (⟨(OverShriek.relocalizePresheafFunctor h).obj X.1, hX'⟩ :
          AlgebraicSpaces B S' hS')).Modules,
      (spacesEtaleModelRingedTopos B S' hS' _).toRingedSite.IsPerfect E' →
      StacksDraft.PseudoCoherence.IsPseudoCoherent
        ((pointDerivedEquiv (R := baseRing B S hS T)).functor.obj
          ((derivedPushforward (spacesEtaleModelToBaseRing B S' hS' _ (baseRingHomOfMap f'))).obj
            E')))
    (E : DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules)
    (hE : (spacesEtaleModelRingedTopos B S hS X).toRingedSite.IsPerfect E) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((pointDerivedEquiv (R := baseRing B S hS T)).functor.obj
        ((derivedPushforward (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))).obj
          E)) := by
  let X' : AlgebraicSpaces B S' hS' := ⟨(OverShriek.relocalizePresheafFunctor h).obj X.1, hX'⟩
  let Ee := spacesEtaleModelModulesEquiv B S hS X
  let Ee' := spacesEtaleModelModulesEquiv B S' hS' X'
  let ρ := relocalizeModulesEquiv B S S' hS hS' h X hX'
  let e := Ee'.trans ρ
  let P := (baseRingPointModulesEquiv (R := baseRing B S hS T)).functor
  have hgr := isGrothendieckAbelian_modules B S hS X.1 X.2
  have := enoughInjectives_modules B S hS X.1 X.2
  have : e.inverse.Additive := (exact_functor_of_equivalence e.symm).1
  have : (baseRingGlobalSectionsModule B S hS X (baseRingHomOfMap f)).Additive :=
    (baseRingTensorModuleAdjunction B S hS X (baseRingHomOfMap f)).right_adjoint_additive
  let ι : e.inverse ⋙
      (spacesEtaleModelToBaseRing B S' hS' X' (baseRingHomOfMap f')).pushforwardTopos ⋙
      P ≅ baseRingGlobalSectionsModule B S hS X (baseRingHomOfMap f) :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft ρ.inverse
        (pushforwardPointModulesIso B S' hS' (baseRingHomOfMap f')) ≪≫
      Functor.isoWhiskerLeft ρ.inverse
        (relocalizeGlobalSectionsIso B S S' hS hS' h X hX' hcompat).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ρ.counitIso _ ≪≫ Functor.leftUnitor _
  have h₁ := isRightDerivedFunctor_pointModulesTransport B S hS (baseRingHomOfMap f) _
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforwardUnit
      (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f)))
  have h₂ := isRightDerivedFunctor_equivalenceTransport B S S' hS hS' X (baseRingHomOfMap f') e
    (baseRingGlobalSectionsModule B S hS X (baseRingHomOfMap f)) ι _
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforwardUnit
      (spacesEtaleModelToBaseRing B S' hS' X' (baseRingHomOfMap f')))
  let u := Functor.rightDerivedUnique _ _
    (pointModulesTransportUnit B S hS (baseRingHomOfMap f) _
      (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforwardUnit
        (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))))
    (equivalenceTransportUnit B S S' hS hS' X (ψ := baseRingHomOfMap f') (e := e)
      (Γ := baseRingGlobalSectionsModule B S hS X (baseRingHomOfMap f)) (ι := ι) (Rf := _)
      (αf := Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforwardUnit
        (spacesEtaleModelToBaseRing B S' hS' X' (baseRingHomOfMap f'))))
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))
  let K := Ee.functor.mapDerivedCategory.obj E
  have hK := isPerfect_spacesEtaleModelModulesEquiv_functor B S hS X E hE
  have hK' : (spacesEtaleModelRingedTopos B S' hS' X').toRingedSite.IsPerfect
      (e.inverse.mapDerivedCategory.obj K) := by
    have : PreservesFiniteLimits ρ.inverse := (exact_functor_of_equivalence ρ.symm).2.1
    have : PreservesFiniteColimits ρ.inverse := (exact_functor_of_equivalence ρ.symm).2.2
    have : PreservesFiniteLimits Ee'.inverse := (exact_functor_of_equivalence Ee'.symm).2.1
    have : PreservesFiniteColimits Ee'.inverse := (exact_functor_of_equivalence Ee'.symm).2.2
    have : Ee'.inverse.Additive := (exact_functor_of_equivalence Ee'.symm).1
    obtain ⟨L, hL, ⟨i⟩⟩ := isPerfect_spacesEtaleModelModulesEquiv_inverse B S' hS' X' _
      (isPerfect_relocalizeModulesEquiv_inverse B S S' hS hS' h X hX' K hK)
    exact ⟨L, hL, ⟨i ≪≫ ((Stacks.DerivedFunctor.mapDerivedCategoryCompIso ρ.inverse
      Ee'.inverse).app K)⟩⟩
  let Eqv := Stacks.DerivedGlueing.mapDerivedCategoryEquivalence Ee.functor Ee.inverse
    Ee.unitIso Ee.counitIso
  exact StacksDraft.PseudoCoherence.IsPseudoCoherent.ofIso (H _ hK') ((u.app K).symm ≪≫
    P.mapDerivedCategory.mapIso
      ((derivedPushforward (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))).mapIso
        (Eqv.unitIso.app E).symm))

end Invariance

end AlgebraicGeometry.Space

end
