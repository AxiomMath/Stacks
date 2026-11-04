module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.Adjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.SupportedCounitStalkFibers
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.SupportedCounitSupportSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.SupportedDerivedCounit
public import StacksFrontier.Homology.Tor.FlatExtendRestrictCounitComplex

/-!
# The fibre of the counit `f^*f_*M ⟶ M` in the proof of Stacks 0AEU

Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` and `ȳ` a geometric point of
`Y` with image `x̄`. The proof of Stacks 0AEU checks the derived counit `Lf^*Rf_*Q ⟶ Q` at a
K-injective representative `J` on the stalks of `Lf^*(f_*J) ⟶ f^*(f_*J) ⟶ J` (Stacks 0FPI). The
second map is the degreewise counit of the adjunction `f^* ⊣ f_*` of the morphism of small étale
ringed topoi (`AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules`); this file
computes its stalk at `ȳ`.

## Main results

* `CategoryTheory.Adjunction.counit_app_eq_conjugateIso`: two adjunctions with isomorphic right
  adjoints have conjugate counits.
* `AlgebraicGeometry.Space.ringedToposCounit_app_eq`: the counit of the ringed-topos adjunction
  is the counit of `AlgebraicGeometry.Space.modulePullbackAdjunction`, up to the identification
  `AlgebraicGeometry.Space.pushforwardModulesIsoModulePushforward` of the two direct images and
  the conjugate identification `AlgebraicGeometry.Space.ringedToposPullbackIsoModulePullback` of
  the two pullbacks.
* `AlgebraicGeometry.Space.sheafModuleFiber_map_ringedToposCounit_app`: the fibre at `ȳ` of the
  counit `f^*f_*M ⟶ M` is, through `(f^*N)_ȳ ≅ 𝒪_{Y,ȳ} ⊗ N_x̄` (Stacks 05V5,
  `AlgebraicGeometry.Space.counitFiberIso`), the extension of scalars of
  `θ : (f_*M)_x̄ ⟶ M_ȳ` (`AlgebraicGeometry.Space.directImageFiberMap`) followed by the action map
  `𝒪_{Y,ȳ} ⊗ M_ȳ ⟶ M_ȳ`.
* `AlgebraicGeometry.Space.quasiIso_sheafModuleFiber_ringedToposCounit`: hence the stalk complex
  of the degreewise counit `f^*f_*J ⟶ J` is a quasi-isomorphism as soon as `θ` is invertible in
  every degree and the degreewise action map `𝒪_{Y,ȳ} ⊗ J_ȳ ⟶ J_ȳ` is a quasi-isomorphism.
* `CategoryTheory.Functor.isIso_mapDerivedCategory_map_Qh_map_quotient_map_iff`: an exact
  functor inverts the image of a map of complexes in the derived category exactly when it
  carries the map to a quasi-isomorphism.

## Implementation notes

The modules of the small étale site are spelled three ways that agree only up to unfolding:
`AlgebraicGeometry.Space.Modules`, the modules over
`Stacks.SheafOfModules.Tensor.ringSheaf` of the small étale ringed topos (the spelling of the
ringed-topos adjunction), and the modules over `Stacks.commRingSheafToRingSheaf` (the spelling of
`Stacks.sheafModuleFiberOfCommRing`). Equations mixing them are proved as chains of small
lemmas, each with its sides written out, rather than by rewriting, which has to check the
spellings against each other under reducible transparency. The instances
`Stacks.Cohomology.SiteModules.moduleSheavesAbelian` and
`Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck`, which are in scope here, are
disabled: they leave universe constraints unsolved on these categories.

## References

* [Stacks Project, Tag 0AEU](https://stacks.math.columbia.edu/tag/0AEU)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Adjunction

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- **Two adjunctions with isomorphic right adjoints have conjugate counits.** For `L₁ ⊣ R₁`,
`L₂ ⊣ R₂` and `e : R₁ ≅ R₂`, the counit of the first is the image under `L₁` of `e`, followed
by the conjugate isomorphism `L₁ ≅ L₂` and the counit of the second. -/
theorem counit_app_eq_conjugateIso {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁)
    (adj₂ : L₂ ⊣ R₂) (e : R₁ ≅ R₂) (d : D) :
    adj₁.counit.app d = L₁.map (e.hom.app d) ≫
      ((conjugateIsoEquiv adj₂ adj₁).symm e.symm).hom.app (R₂.obj d) ≫ adj₂.counit.app d := by
  have h := conjugateEquiv_counit_symm adj₂ adj₁ e.inv d
  show _ = _ ≫ ((conjugateEquiv adj₂ adj₁).symm e.inv).app (R₂.obj d) ≫ adj₂.counit.app d
  rw [← h, ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id, Category.id_comp]

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {C₁ : Type u₁} [Category.{v₁} C₁] {_ : Abelian C₁} {C₂ : Type u₂} [Category.{v₂} C₂]
  {_ : Abelian C₂} {_ : HasDerivedCategory C₁} {_ : HasDerivedCategory C₂} (F : C₁ ⥤ C₂)
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **An exact functor inverts the image of a map of complexes in the derived category exactly
when it carries the map to a quasi-isomorphism.**

The abelian structures and the models of the derived categories are implicit arguments rather
than instance arguments, so that they are read off the morphism at hand. -/
theorem isIso_mapDerivedCategory_map_Qh_map_quotient_map_iff {K L : CochainComplex C₁ ℤ}
    (φ : K ⟶ L) :
    IsIso (F.mapDerivedCategory.map
        (DerivedCategory.Qh.map ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).map φ))) ↔
      QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) := by
  have h₁ : DerivedCategory.Qh.map ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).map φ) =
      _ := (NatIso.naturality_2 (DerivedCategory.quotientCompQhIso C₁) φ).symm
  have h₂ : F.mapDerivedCategory.map (DerivedCategory.Q.map φ) = _ :=
    (NatIso.naturality_2 F.mapDerivedCategoryFactors φ).symm
  rw [h₁, Functor.map_comp, Functor.map_comp, isIso_comp_left_iff, isIso_comp_right_iff, h₂,
    isIso_comp_left_iff, isIso_comp_right_iff]
  exact DerivedCategory.isIso_Q_map_iff_quasiIso C₂ _

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Counit

variable {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)

/-- The pullback of modules of the morphism of small étale ringed topoi, through the two-field
morphism of ringed topoi, is `AlgebraicGeometry.Space.modulePullback`: the two are left adjoint
to isomorphic direct images. -/
def ringedToposPullbackIsoModulePullback :
    (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules ≅
      modulePullback B S hS f :=
  (conjugateIsoEquiv (modulePullbackAdjunction B S hS f)
    (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS f))).symm
    (pushforwardModulesIsoModulePushforward B S hS f).symm

/-- **The counit of the ringed-topos adjunction `f^* ⊣ f_*` is the counit of
`AlgebraicGeometry.Space.modulePullbackAdjunction`**, up to the identifications of the two
direct images and of the two pullbacks. -/
theorem ringedToposCounit_app_eq (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (RingedToposHom.pullbackAdjPushforwardModules
        (smallEtaleRingedToposHom B S hS f)).counit.app M =
      (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.map
          ((pushforwardModulesIsoModulePushforward B S hS f).hom.app M) ≫
        (ringedToposPullbackIsoModulePullback B S hS f).hom.app
          ((modulePushforward B S hS f).obj M) ≫
        (modulePullbackAdjunction B S hS f).counit.app M :=
  Adjunction.counit_app_eq_conjugateIso _ _ _ M

/-- The fibre at a geometric point `ȳ` of `f^*f_*M`, for the pullback of the ringed topoi, is
`𝒪_{Y,ȳ} ⊗ (f_*M)_x̄`, naturally in `M` (Stacks 05V5). -/
def counitFiberIso (y : GeometricPoint B S hS Y.1) :
    (smallEtaleRingedToposHom B S hS f).pushforwardModules ⋙
        (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules ⋙
          Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
            (smallEtaleRingedTopos B S hS Y).O ≅
      modulePushforward B S hS f ⋙
        Stacks.sheafModuleFiberOfCommRing
            (etaleSitePoint B S hS X.1 (geometricPointMap f.hom y) X.2)
            (smallEtaleRingedTopos B S hS X).O ⋙
          ModuleCat.extendScalars (smallEtaleStalkPullbackRingMap B S hS f y) :=
  Functor.isoWhiskerRight (pushforwardModulesIsoModulePushforward B S hS f) _ ≪≫
    Functor.isoWhiskerLeft (modulePushforward B S hS f)
      (Functor.isoWhiskerRight (ringedToposPullbackIsoModulePullback B S hS f) _ ≪≫
        modulePullbackFiberIso B S hS f y)

/-- The component of `AlgebraicGeometry.Space.counitFiberIso`, written out. -/
theorem counitFiberIso_hom_app (y : GeometricPoint B S hS Y.1)
    (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (counitFiberIso B S hS f y).hom.app M =
      (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
          (smallEtaleRingedTopos B S hS Y).O).map
          ((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.map
            ((pushforwardModulesIsoModulePushforward B S hS f).hom.app M)) ≫
        (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
          (smallEtaleRingedTopos B S hS Y).O).map
          ((ringedToposPullbackIsoModulePullback B S hS f).hom.app
            ((modulePushforward B S hS f).obj M)) ≫
        (modulePullbackFiberIso B S hS f y).hom.app ((modulePushforward B S hS f).obj M) :=
  rfl

/-- The fibre at `ȳ` of the three factors of the counit of the ringed-topos adjunction
(`AlgebraicGeometry.Space.ringedToposCounit_app_eq`). -/
theorem sheafModuleFiber_map_ringedToposCounit_app_eq_comp (y : GeometricPoint B S hS Y.1)
    (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
        (smallEtaleRingedTopos B S hS Y).O).map
        ((RingedToposHom.pullbackAdjPushforwardModules
          (smallEtaleRingedToposHom B S hS f)).counit.app M) =
      (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
        (smallEtaleRingedTopos B S hS Y).O).map
        ((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.map
          ((pushforwardModulesIsoModulePushforward B S hS f).hom.app M)) ≫
      (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
        (smallEtaleRingedTopos B S hS Y).O).map
        ((ringedToposPullbackIsoModulePullback B S hS f).hom.app
          ((modulePushforward B S hS f).obj M)) ≫
      (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
        (smallEtaleRingedTopos B S hS Y).O).map
        ((modulePullbackAdjunction B S hS f).counit.app M) :=
  (congrArg (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
    (smallEtaleRingedTopos B S hS Y).O).map (ringedToposCounit_app_eq B S hS f M)).trans
    ((Functor.map_comp _ _ _).trans (congrArg (_ ≫ ·) (Functor.map_comp _ _ _)))

/-- `AlgebraicGeometry.Space.counitFiberIso` followed by the transpose of `θ` is the fibre of
the three factors of the counit of the ringed-topos adjunction. -/
theorem counitFiberIso_hom_app_comp_directImageFiberMapTranspose (y : GeometricPoint B S hS Y.1)
    (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (counitFiberIso B S hS f y).hom.app M ≫ directImageFiberMapTranspose B S hS f y M =
      (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
        (smallEtaleRingedTopos B S hS Y).O).map
        ((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.map
          ((pushforwardModulesIsoModulePushforward B S hS f).hom.app M)) ≫
      (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
        (smallEtaleRingedTopos B S hS Y).O).map
        ((ringedToposPullbackIsoModulePullback B S hS f).hom.app
          ((modulePushforward B S hS f).obj M)) ≫
      (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
        (smallEtaleRingedTopos B S hS Y).O).map
        ((modulePullbackAdjunction B S hS f).counit.app M) := by
  rw [counitFiberIso_hom_app, directImageFiberMapTranspose_eq]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

/-- **The fibre of the counit `f^*f_*M ⟶ M` at `ȳ` is `𝒪_{Y,ȳ} ⊗ θ` followed by the action
map**, read through `AlgebraicGeometry.Space.counitFiberIso`. -/
theorem sheafModuleFiber_map_ringedToposCounit_app (y : GeometricPoint B S hS Y.1)
    (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
        (smallEtaleRingedTopos B S hS Y).O).map
        ((RingedToposHom.pullbackAdjPushforwardModules
          (smallEtaleRingedToposHom B S hS f)).counit.app M) =
      (counitFiberIso B S hS f y).hom.app M ≫
        (ModuleCat.extendScalars (smallEtaleStalkPullbackRingMap B S hS f y)).map
          ((directImageFiberMap B S hS f y).app M) ≫
        (ModuleCat.extendRestrictScalarsAdj.{u}
          (smallEtaleStalkPullbackRingMap B S hS f y)).counit.app _ :=
  (sheafModuleFiber_map_ringedToposCounit_app_eq_comp B S hS f y M).trans
    ((counitFiberIso_hom_app_comp_directImageFiberMapTranspose B S hS f y M).symm.trans
      (congrArg ((counitFiberIso B S hS f y).hom.app M ≫ ·)
        (extendScalars_map_directImageFiberMap_comp_counit B S hS f y M).symm))

/-- The pullback of modules along the morphism of small étale ringed topoi is additive. -/
theorem additive_smallEtalePullbackModules :
    (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.Additive :=
  RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHom B S hS f)

attribute [local instance] additive_smallEtalePullbackModules

/-- The direct image of modules along the morphism of small étale ringed topoi is additive,
being a right adjoint. -/
theorem additive_smallEtalePushforwardModules :
    (smallEtaleRingedToposHom B S hS f).pushforwardModules.Additive :=
  (RingedToposHom.pullbackAdjPushforwardModules
    (smallEtaleRingedToposHom B S hS f)).right_adjoint_additive

attribute [local instance] additive_smallEtalePushforwardModules

/-- The comparison `(f^*f_*J)_ȳ ⟶ 𝒪_{Y,ȳ} ⊗ J_ȳ` of complexes: degreewise the identification
`AlgebraicGeometry.Space.counitFiberIso` followed by `𝒪_{Y,ȳ} ⊗ θ`. -/
def counitFiberComplexMap (y : GeometricPoint B S hS Y.1)
    (J : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ) :
    ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
        (smallEtaleRingedTopos B S hS Y).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((((smallEtaleRingedToposHom B S hS f).pushforwardModules ⋙
          (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj J) ⟶
      ((ModuleCat.restrictScalars (smallEtaleStalkPullbackRingMap B S hS f y) ⋙
        ModuleCat.extendScalars (smallEtaleStalkPullbackRingMap B S hS f y)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
          (smallEtaleRingedTopos B S hS Y).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            J) where
  f n := (counitFiberIso B S hS f y).hom.app (J.X n) ≫
    (ModuleCat.extendScalars (smallEtaleStalkPullbackRingMap B S hS f y)).map
      ((directImageFiberMap B S hS f y).app (J.X n))
  comm' i j _ := by
    have h₁ := (counitFiberIso B S hS f y).hom.naturality (J.d i j)
    have h₂ := congrArg (ModuleCat.extendScalars (smallEtaleStalkPullbackRingMap B S hS f y)).map
      ((directImageFiberMap B S hS f y).naturality (J.d i j))
    rw [Functor.map_comp, Functor.map_comp] at h₂
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₂.symm).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₁.symm).trans
        (Category.assoc _ _ _))))

/-- The components of `AlgebraicGeometry.Space.counitFiberComplexMap`. -/
theorem counitFiberComplexMap_f (y : GeometricPoint B S hS Y.1)
    (J : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ) (n : ℤ) :
    (counitFiberComplexMap B S hS f y J).f n = (counitFiberIso B S hS f y).hom.app (J.X n) ≫
      (ModuleCat.extendScalars (smallEtaleStalkPullbackRingMap B S hS f y)).map
        ((directImageFiberMap B S hS f y).app (J.X n)) :=
  rfl

/-- `AlgebraicGeometry.Space.counitFiberComplexMap` is an isomorphism of complexes when `θ` is
invertible in every degree. -/
theorem isIso_counitFiberComplexMap (y : GeometricPoint B S hS Y.1)
    (J : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ)
    (hθ : ∀ n, IsIso ((directImageFiberMap B S hS f y).app (J.X n))) :
    IsIso (counitFiberComplexMap B S hS f y J) := by
  have : ∀ n, IsIso ((counitFiberComplexMap B S hS f y J).f n) := fun n ↦ by
    have := hθ n
    rw [counitFiberComplexMap_f]
    exact IsIso.comp_isIso' (Iso.isIso_hom ((counitFiberIso B S hS f y).app (J.X n)))
      (Functor.map_isIso _ _)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The components of the degreewise counit of the ringed-topos adjunction. -/
theorem mapHomologicalComplex_ringedToposCounit_app_f
    (J : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ) (n : ℤ) :
    ((NatTrans.mapHomologicalComplex (RingedToposHom.pullbackAdjPushforwardModules
        (smallEtaleRingedToposHom B S hS f)).counit (ComplexShape.up ℤ)).app J).f n =
      (RingedToposHom.pullbackAdjPushforwardModules
        (smallEtaleRingedToposHom B S hS f)).counit.app (J.X n) :=
  rfl

/-- The components of the fibre at `ȳ` of the degreewise counit of the ringed-topos
adjunction. -/
theorem sheafModuleFiber_mapHomologicalComplex_ringedToposCounit_f (y : GeometricPoint B S hS Y.1)
    (J : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ) (n : ℤ) :
    (((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
        (smallEtaleRingedTopos B S hS Y).O).mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((NatTrans.mapHomologicalComplex (RingedToposHom.pullbackAdjPushforwardModules
        (smallEtaleRingedToposHom B S hS f)).counit (ComplexShape.up ℤ)).app J)).f n =
      (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
        (smallEtaleRingedTopos B S hS Y).O).map ((RingedToposHom.pullbackAdjPushforwardModules
        (smallEtaleRingedToposHom B S hS f)).counit.app (J.X n)) :=
  congrArg (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
    (smallEtaleRingedTopos B S hS Y).O).map
      (mapHomologicalComplex_ringedToposCounit_app_f B S hS f J n)

/-- The components of `AlgebraicGeometry.Space.counitFiberComplexMap` followed by the degreewise
action map. -/
theorem counitFiberComplexMap_comp_f (y : GeometricPoint B S hS Y.1)
    (J : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ) (n : ℤ) :
    (counitFiberComplexMap B S hS f y J ≫
        (NatTrans.mapHomologicalComplex
          (ModuleCat.extendRestrictScalarsAdj.{u}
            (smallEtaleStalkPullbackRingMap B S hS f y)).counit
          (ComplexShape.up ℤ)).app
          (((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
            (smallEtaleRingedTopos B S hS Y).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              J)).f n =
      ((counitFiberIso B S hS f y).hom.app (J.X n) ≫
        (ModuleCat.extendScalars (smallEtaleStalkPullbackRingMap B S hS f y)).map
          ((directImageFiberMap B S hS f y).app (J.X n))) ≫
        (ModuleCat.extendRestrictScalarsAdj.{u}
          (smallEtaleStalkPullbackRingMap B S hS f y)).counit.app _ :=
  rfl

/-- **The fibre at `ȳ` of the degreewise counit `f^*f_*J ⟶ J`** is
`AlgebraicGeometry.Space.counitFiberComplexMap` followed by the degreewise action map
`𝒪_{Y,ȳ} ⊗ J_ȳ ⟶ J_ȳ`. -/
theorem sheafModuleFiber_mapHomologicalComplex_ringedToposCounit (y : GeometricPoint B S hS Y.1)
    (J : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ) :
    ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
        (smallEtaleRingedTopos B S hS Y).O).mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((NatTrans.mapHomologicalComplex (RingedToposHom.pullbackAdjPushforwardModules
        (smallEtaleRingedToposHom B S hS f)).counit (ComplexShape.up ℤ)).app J) =
      counitFiberComplexMap B S hS f y J ≫
        (NatTrans.mapHomologicalComplex
          (ModuleCat.extendRestrictScalarsAdj.{u}
            (smallEtaleStalkPullbackRingMap B S hS f y)).counit
          (ComplexShape.up ℤ)).app
          (((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
            (smallEtaleRingedTopos B S hS Y).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) :=
  HomologicalComplex.hom_ext _ _ fun n ↦
    (sheafModuleFiber_mapHomologicalComplex_ringedToposCounit_f B S hS f y J n).trans
      ((sheafModuleFiber_map_ringedToposCounit_app B S hS f y (J.X n)).trans
        ((Category.assoc _ _ _).symm.trans (counitFiberComplexMap_comp_f B S hS f y J n).symm))

/-- **The fibre at `ȳ` of the degreewise counit `f^*f_*J ⟶ J` is a quasi-isomorphism** when
the comparison `θ : (f_*Jⁿ)_x̄ ⟶ Jⁿ_ȳ` is invertible in every degree and the degreewise action map
`𝒪_{Y,ȳ} ⊗ J_ȳ ⟶ J_ȳ` is a quasi-isomorphism. -/
theorem quasiIso_sheafModuleFiber_ringedToposCounit (y : GeometricPoint B S hS Y.1)
    (J : CochainComplex (Modules.{u, u} B S hS Y.1 Y.2) ℤ)
    (hθ : ∀ n, IsIso ((directImageFiberMap B S hS f y).app (J.X n)))
    (hc : QuasiIso ((NatTrans.mapHomologicalComplex (ModuleCat.extendRestrictScalarsAdj.{u}
        (smallEtaleStalkPullbackRingMap B S hS f y)).counit (ComplexShape.up ℤ)).app
      (((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
        (smallEtaleRingedTopos B S hS Y).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj J))) :
    QuasiIso (((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS Y.1 y Y.2)
        (smallEtaleRingedTopos B S hS Y).O).mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((NatTrans.mapHomologicalComplex (RingedToposHom.pullbackAdjPushforwardModules
        (smallEtaleRingedToposHom B S hS f)).counit (ComplexShape.up ℤ)).app J)) := by
  have := isIso_counitFiberComplexMap B S hS f y J hθ
  rw [sheafModuleFiber_mapHomologicalComplex_ringedToposCounit]
  infer_instance

end Counit

end AlgebraicGeometry.Space

end
