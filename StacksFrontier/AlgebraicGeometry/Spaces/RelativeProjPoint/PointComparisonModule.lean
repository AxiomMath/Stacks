module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitStepTwo
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.PullRestrictionTranspose
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCompTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiReadingInvertibleQuotients
public import StacksFrontier.CategoryTheory.Adjunction.TransportEquivalence
public import StacksFrontier.CategoryTheory.Adjunction.UniqueComp

/-!
# The comparison of restricted algebras, degree by degree

Let `τ : T' ⟶ T` be a morphism of test objects, `φ` the morphism of represented algebraic spaces it
induces, `f` a scheme point of an algebraic space `X` at `T` and `𝒜` a graded `𝒪_X`-algebra.  In
each degree the comparison `τ^*(f^*𝒜)_Zar ⟶ ((f ∘ τ)^*𝒜)_Zar` of the restricted algebras is the
base-change map of the Zariski reading at `f^*𝒜_n` followed by the Zariski reading of the
composition comparison `φ^* f^* ≅ (f ∘ φ)^*` of Stacks 03LU.

## Main results

* `AlgebraicGeometry.Space.modulePullbackCompIso_eq_leftAdjointUniq`: the composition comparison
  of Stacks 03LU is the comparison of left adjoints for the etale module adjunctions.
* `AlgebraicGeometry.Space.gradedPullRestrictionApp_comp_rfl_eq`: the restriction map of
  pulled-back graded algebras is, degreewise, the unit of `φ^* ⊣ φ_*` followed by the direct image
  of the composition comparison.
* `AlgebraicGeometry.Space.pointComparison_app_eq_zariskiReadingPullbackHom`: the degreewise
  description of the comparison of restricted algebras.

## Implementation notes

The etale module adjunctions are written as
`AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModulesViaComparison` rather than through
the abbreviation `AlgebraicGeometry.Space.etaleModuleAdjunction`: with the abbreviation in a
statement the kernel check of the equations below exceeds its budget.
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull gradedPush gradedAdj)

universe u

/-- Transporting the right adjoints of the three adjunctions of a comparison of left adjoints
along equalities of functors does not change the comparison. -/
theorem CategoryTheory.Adjunction.leftAdjointUniq_comp_ofNatIsoRight_compIsoCongr
    {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
    {L₁ : C₀ ⥤ C₁} {L₂ : C₁ ⥤ C₂} {L₃ : C₀ ⥤ C₂}
    {R₁ R₁' : C₁ ⥤ C₀} {R₂ R₂' : C₂ ⥤ C₁} {R₃ R₃' : C₂ ⥤ C₀} (b₁ : L₁ ⊣ R₁) (b₂ : L₂ ⊣ R₂)
    (b₃ : L₃ ⊣ R₃) (e : R₂ ⋙ R₁ ≅ R₃) (h₁ : R₁ = R₁') (h₂ : R₂ = R₂') (h₃ : R₃ = R₃') :
    Adjunction.leftAdjointUniq (((b₁.ofNatIsoRight (eqToIso h₁)).comp
        (b₂.ofNatIsoRight (eqToIso h₂))).ofNatIsoRight (Functor.compIsoCongr h₂ h₁ h₃ e))
      (b₃.ofNatIsoRight (eqToIso h₃)) =
    Adjunction.leftAdjointUniq ((b₁.comp b₂).ofNatIsoRight e) b₃ := by
  subst h₁ h₂ h₃
  simp only [eqToIso_refl, Adjunction.ofNatIsoRight_refl, Functor.compIsoCongr_eq,
    Iso.refl_trans, Iso.trans_refl]

/-- A morphism `L₁M ⟶ R₂(L₃M)` whose transpose along `L₁ ⊣ R₁` is the unit of `L₃ ⊣ R₃` read
through `e : R₂ ⋙ R₁ ≅ R₃` is the transpose along `L₂ ⊣ R₂` of the comparison of left adjoints. -/
theorem CategoryTheory.Adjunction.eq_unit_comp_map_leftAdjointUniq {C₀ C₁ C₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂] {L₁ : C₀ ⥤ C₁} {L₂ : C₁ ⥤ C₂} {L₃ : C₀ ⥤ C₂}
    {R₁ : C₁ ⥤ C₀} {R₂ : C₂ ⥤ C₁} {R₃ : C₂ ⥤ C₀} (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    (e : R₂ ⋙ R₁ ≅ R₃) (M : C₀) (r : L₁.obj M ⟶ R₂.obj (L₃.obj M))
    (hr : a₁.unit.app M ≫ R₁.map r = a₃.unit.app M ≫ e.inv.app _) :
    r = a₂.unit.app (L₁.obj M) ≫
      R₂.map ((Adjunction.leftAdjointUniq ((a₁.comp a₂).ofNatIsoRight e) a₃).hom.app M) := by
  apply (a₁.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, hr, ← Iso.app_inv, Iso.comp_inv_eq,
    ← Adjunction.unit_leftAdjointUniq_hom_app ((a₁.comp a₂).ofNatIsoRight e) a₃ M]
  have hu : ((a₁.comp a₂).ofNatIsoRight e).unit.app M =
      (a₁.comp a₂).unit.app M ≫ e.hom.app _ := by
    simp [Adjunction.ofNatIsoRight]
  rw [hu, Adjunction.comp_unit_app]
  have hnat := e.hom.naturality ((Adjunction.leftAdjointUniq ((a₁.comp a₂).ofNatIsoRight e)
    a₃).hom.app M)
  simp only [Functor.comp_map] at hnat
  simp only [Functor.map_comp, Category.assoc, Iso.app_hom, hnat]

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {P P' X : AlgebraicSpaces B S hS}

/-- The composition comparison of Stacks 03LU, spelled with the etale module adjunctions. -/
theorem modulePullbackCompIso_eq_leftAdjointUniq_etale (φ : P' ⟶ P) (f : P ⟶ X) :
    modulePullbackCompIso B S hS φ f =
      Adjunction.leftAdjointUniq (((etaleModuleAdjunction f).comp
          (etaleModuleAdjunction φ)).ofNatIsoRight (pushforwardModulesCompAt B S hS φ f))
        (etaleModuleAdjunction (φ ≫ f)) := by
  rw [modulePullbackCompIso_eq, moduleCompAdjunction_eq,
    modulePullbackAdjunction_eq_etaleModuleAdjunction_ofNatIsoRight,
    modulePullbackAdjunction_eq_etaleModuleAdjunction_ofNatIsoRight,
    modulePullbackAdjunction_eq_etaleModuleAdjunction_ofNatIsoRight,
    modulePushforwardCompIso_eq_compIsoCongr]
  exact Adjunction.leftAdjointUniq_comp_ofNatIsoRight_compIsoCongr _ _ _ _ _ _ _

/-- **The composition comparison of Stacks 03LU is the comparison of left adjoints for the etale
module adjunctions**, the two right adjoints being compared by the comparison of direct images
of the ringed topoi. -/
theorem modulePullbackCompIso_eq_leftAdjointUniq (φ : P' ⟶ P) (f : P ⟶ X) :
    modulePullbackCompIso B S hS φ f =
      Adjunction.leftAdjointUniq
        (((smallEtaleRingedToposHom B S hS f).pullbackAdjPushforwardModulesViaComparison.comp
          (smallEtaleRingedToposHom B S hS
              φ).pullbackAdjPushforwardModulesViaComparison).ofNatIsoRight
            (pushforwardModulesCompAt B S hS φ f))
        (smallEtaleRingedToposHom B S hS (φ ≫ f)).pullbackAdjPushforwardModulesViaComparison :=
  modulePullbackCompIso_eq_leftAdjointUniq_etale φ f

/-- The restriction map of pulled-back graded algebras, transposed back along the adjunction of
`f`, is the unit of the composite followed by the comparison of direct images. -/
theorem unit_comp_map_gradedPullRestriction (φ : P' ⟶ P) (f : P ⟶ X)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)) :
    (gradedAdj (X := smallEtaleRingedTopos B S hS P) (Y := smallEtaleRingedTopos B S hS X)
        (smallEtaleRingedToposHom B S hS f)).unit.app A ≫
      (gradedPush (X := smallEtaleRingedTopos B S hS P) (Y := smallEtaleRingedTopos B S hS X)
        (smallEtaleRingedToposHom B S hS f)).map (gradedPullRestriction φ f (φ ≫ f) rfl A) =
    (gradedAdj (X := smallEtaleRingedTopos B S hS P') (Y := smallEtaleRingedTopos B S hS X)
        (smallEtaleRingedToposHom B S hS (φ ≫ f))).unit.app A ≫
      (gradedAlgebraPushforwardCompIso B S hS φ f).inv.app _ :=
  Adjunction.unit_comp_map_unitTranspose _ _ _ _ A

/-- The degree-`n` component of the unit of the graded adjunction is the unit of the module
adjunction. -/
theorem viaComparison_unit_app_piece (f : P ⟶ X)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)) (n : ℤ) :
    (smallEtaleRingedToposHom B S hS f).pullbackAdjPushforwardModulesViaComparison.unit.app
        (A.piece n) =
      ((gradedAdj (X := smallEtaleRingedTopos B S hS P) (Y := smallEtaleRingedTopos B S hS X)
        (smallEtaleRingedToposHom B S hS f)).unit.app A).app n :=
  rfl

/-- The direct image of the restriction map, in degree `n`. -/
theorem pushforwardModules_map_gradedPullRestrictionApp (φ : P' ⟶ P) (f : P ⟶ X)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)) (n : ℤ) :
    (smallEtaleRingedToposHom B S hS f).pushforwardModules.map
          (gradedPullRestrictionApp φ f (φ ≫ f) rfl A n) =
      ((gradedPush (X := smallEtaleRingedTopos B S hS P) (Y := smallEtaleRingedTopos B S hS X)
        (smallEtaleRingedToposHom B S hS f)).map (gradedPullRestriction φ f (φ ≫ f) rfl A)).app n :=
  rfl

/-- **The restriction map of pulled-back graded algebras in degree `n`, transposed back along the
module adjunction of `f`**, is the unit of the composite followed by the comparison of direct
images. -/
theorem unit_comp_map_gradedPullRestrictionApp (φ : P' ⟶ P) (f : P ⟶ X)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)) (n : ℤ) :
    (smallEtaleRingedToposHom B S hS f).pullbackAdjPushforwardModulesViaComparison.unit.app
        (A.piece n) ≫
      (smallEtaleRingedToposHom B S hS f).pushforwardModules.map
          (gradedPullRestrictionApp φ f (φ ≫ f) rfl A n) =
    (smallEtaleRingedToposHom B S hS (φ ≫ f)).pullbackAdjPushforwardModulesViaComparison.unit.app
        (A.piece n) ≫
      (pushforwardModulesCompAt B S hS φ f).inv.app _ :=
  (congrArg₂ (· ≫ ·) (viaComparison_unit_app_piece f A n)
      (pushforwardModules_map_gradedPullRestrictionApp φ f A n)).trans
    ((SheafOfModules.GradedAlgebra.categoryStruct_comp_app _ _ n).symm.trans
      ((congrArg (fun k => SheafOfModules.GradedAlgebra.Hom.app k n)
        (unit_comp_map_gradedPullRestriction φ f A)).trans
        ((SheafOfModules.GradedAlgebra.categoryStruct_comp_app _ _ n).trans
          (congrArg₂ (· ≫ ·) (viaComparison_unit_app_piece (φ ≫ f) A n).symm
            (gradedAlgebraPushforwardCompIso_inv_app_app φ f _ n)))))

/-- The restriction map of pulled-back graded algebras in degree `n`, through the comparison of
left adjoints of the etale module adjunctions. -/
theorem gradedPullRestrictionApp_comp_rfl_eq_leftAdjointUniq (φ : P' ⟶ P) (f : P ⟶ X)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)) (n : ℤ) :
    gradedPullRestrictionApp φ f (φ ≫ f) rfl A n =
      (smallEtaleRingedToposHom B S hS φ).pullbackAdjPushforwardModulesViaComparison.unit.app
          ((smallEtaleRingedToposHom B S hS f).toRingedToposModulesHom.pullbackModules.obj
            (A.piece n)) ≫
        (smallEtaleRingedToposHom B S hS φ).pushforwardModules.map
          ((Adjunction.leftAdjointUniq
            (((smallEtaleRingedToposHom B S hS f).pullbackAdjPushforwardModulesViaComparison.comp
              (smallEtaleRingedToposHom B S hS
                  φ).pullbackAdjPushforwardModulesViaComparison).ofNatIsoRight
                (pushforwardModulesCompAt B S hS φ f))
            (smallEtaleRingedToposHom B S hS
                (φ ≫ f)).pullbackAdjPushforwardModulesViaComparison).hom.app
              (A.piece n)) :=
  Adjunction.eq_unit_comp_map_leftAdjointUniq
    (smallEtaleRingedToposHom B S hS f).pullbackAdjPushforwardModulesViaComparison
    (smallEtaleRingedToposHom B S hS φ).pullbackAdjPushforwardModulesViaComparison
    (smallEtaleRingedToposHom B S hS (φ ≫ f)).pullbackAdjPushforwardModulesViaComparison
    (pushforwardModulesCompAt B S hS φ f) (A.piece n)
    (gradedPullRestrictionApp φ f (φ ≫ f) rfl A n)
    (unit_comp_map_gradedPullRestrictionApp φ f A n)

/-- **The restriction map of pulled-back graded algebras is, in each degree, the transpose of the
composition comparison of Stacks 03LU**: the degree-`n` component of `f^*𝒜 ⟶ φ_*((f ∘ φ)^*𝒜)` is
the unit of `φ^* ⊣ φ_*` followed by `φ_*` of `φ^*f^*𝒜_n ≅ (f ∘ φ)^*𝒜_n`. -/
theorem gradedPullRestrictionApp_comp_rfl_eq (φ : P' ⟶ P) (f : P ⟶ X)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)) (n : ℤ) :
    gradedPullRestrictionApp φ f (φ ≫ f) rfl A n =
      (smallEtaleRingedToposHom B S hS φ).pullbackAdjPushforwardModulesViaComparison.unit.app
          ((smallEtaleRingedToposHom B S hS f).toRingedToposModulesHom.pullbackModules.obj
            (A.piece n)) ≫
        (smallEtaleRingedToposHom B S hS φ).pushforwardModules.map
          ((modulePullbackCompIso B S hS φ f).hom.app (A.piece n)) :=
  (gradedPullRestrictionApp_comp_rfl_eq_leftAdjointUniq φ f A n).trans
    (congrArg (fun c =>
        (smallEtaleRingedToposHom B S hS φ).pullbackAdjPushforwardModulesViaComparison.unit.app
          ((smallEtaleRingedToposHom B S hS f).toRingedToposModulesHom.pullbackModules.obj
            (A.piece n)) ≫ (smallEtaleRingedToposHom B S hS φ).pushforwardModules.map c)
      (congrArg (fun e => e.hom.app (A.piece n))
        (modulePullbackCompIso_eq_leftAdjointUniq φ f)).symm)

section ZariskiReading

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (ringedSpaceHom)

variable {T T' : BigFppfOver B S hS} (τ : T' ⟶ T)
  (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
  (L : Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))
  (c : (modulePullback B S hS (representedSpaceMap B S hS τ)).obj N ⟶ L)

/-- The base-change map of the Zariski reading followed by the Zariski reading of a morphism, as
a transpose along `τ^* ⊣ τ_*`. -/
theorem zariskiReadingPullbackHom_app_comp_eq_homEquiv_symm :
    (zariskiReadingPullbackHom τ).app N ≫ (zariskiReadingFunctor T').map c =
      ((Stacks.RingedSpace.pullbackAdjunction
        (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).homEquiv _ _).symm
        (((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).map
            ((etaleModuleAdjunction (representedSpaceMap B S hS τ)).unit.app N) ≫
          (zariskiDirectImageNatTrans τ).app _) ≫
          (Stacks.RingedSpace.pushforwardFunctor
            (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).map
            ((zariskiReadingFunctor T').map c)) :=
  (congrArg (· ≫ (zariskiReadingFunctor T').map c) (zariskiReadingPullbackHom_app τ N)).trans
    (Adjunction.homEquiv_naturality_right_symm
      (Stacks.RingedSpace.pullbackAdjunction (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ)))
      ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).map
          ((etaleModuleAdjunction (representedSpaceMap B S hS τ)).unit.app N) ≫
        (zariskiDirectImageNatTrans τ).app _) ((zariskiReadingFunctor T').map c)).symm

/-- The naturality of the identification of sections of a direct image, at a morphism out of an
inverse image. -/
theorem zariskiDirectImageNatTrans_naturality_pullback :
    (SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).map
        ((smallEtaleRingedToposHom B S hS
            (representedSpaceMap B S hS τ)).pushforwardModules.map c) ≫
        (zariskiDirectImageNatTrans τ).app L =
      (zariskiDirectImageNatTrans τ).app ((modulePullback B S hS
          (representedSpaceMap B S hS τ)).obj N) ≫
        (Stacks.RingedSpace.pushforwardFunctor (ringedSpaceHom
            ((BigFppfOver.toScheme B S hS).map τ))).map
          ((zariskiReadingFunctor T').map c) :=
  (zariskiDirectImageNatTrans τ).naturality c

/-- The identification of sections of a direct image, moved past a morphism. -/
theorem zariskiDirectImageNatTrans_comp_map :
    ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).map
          ((etaleModuleAdjunction (representedSpaceMap B S hS τ)).unit.app N) ≫
        (zariskiDirectImageNatTrans τ).app ((modulePullback B S hS
            (representedSpaceMap B S hS τ)).obj N)) ≫
      (Stacks.RingedSpace.pushforwardFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).map
        ((zariskiReadingFunctor T').map c) =
    (SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).map
        ((etaleModuleAdjunction (representedSpaceMap B S hS τ)).unit.app N ≫
          (smallEtaleRingedToposHom B S hS
              (representedSpaceMap B S hS τ)).pushforwardModules.map c) ≫
      (zariskiDirectImageNatTrans τ).app L :=
  (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (zariskiDirectImageNatTrans_naturality_pullback τ N L c).symm).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (zariskiDirectImageNatTrans τ).app L)
        ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).map_comp _ _).symm)))

/-- The base-change map of the Zariski reading followed by the Zariski reading of a morphism out of
the inverse image, transposed along `τ^* ⊣ τ_*`. -/
theorem zariskiReadingPullbackHom_app_comp :
    (zariskiReadingPullbackHom τ).app N ≫ (zariskiReadingFunctor T').map c =
      ((Stacks.RingedSpace.pullbackAdjunction
        (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).homEquiv _ _).symm
        ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).map
            ((etaleModuleAdjunction (representedSpaceMap B S hS τ)).unit.app N ≫
              (smallEtaleRingedToposHom B S hS
                  (representedSpaceMap B S hS τ)).pushforwardModules.map c) ≫
          (zariskiDirectImageNatTrans τ).app L) :=
  (zariskiReadingPullbackHom_app_comp_eq_homEquiv_symm τ N L c).trans
    (congrArg _ (zariskiDirectImageNatTrans_comp_map τ N L c))

/-- Transposes along `τ^* ⊣ τ_*` of equal morphisms into a direct image agree. -/
theorem homEquiv_symm_pushforward_map_comp_zariskiDirectImageNatTrans_congr
    {x y : N ⟶ (smallEtaleRingedToposHom B S hS
        (representedSpaceMap B S hS τ)).pushforwardModules.obj L}
    (h : x = y) :
    ((Stacks.RingedSpace.pullbackAdjunction
        (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).homEquiv
          ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).obj N)
          ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T')).obj L)).symm
        ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).map x ≫
          (zariskiDirectImageNatTrans τ).app L) =
      ((Stacks.RingedSpace.pullbackAdjunction
        (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).homEquiv
          ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).obj N)
          ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T')).obj L)).symm
        ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).map y ≫
          (zariskiDirectImageNatTrans τ).app L) :=
  h ▸ rfl

end ZariskiReading

section PointComparison

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (ringedSpaceHom)

variable (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
  {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (f : yoneda.obj T ⟶ X.1) (n : ℤ)

/-- The restriction map of the restricted algebras at a scheme point, in degree `n`. -/
theorem pointGradedPullRestrictionApp_eq :
    gradedPullRestrictionApp (representedSpaceMap B S hS τ) (pointHom f)
        (representedSpaceMap B S hS τ ≫ pointHom f) rfl A n =
      (etaleModuleAdjunction (representedSpaceMap B S hS τ)).unit.app
          ((modulePullback B S hS (pointHom f)).obj (A.piece n)) ≫
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS τ)).pushforwardModules.map
          ((modulePullbackCompIso B S hS (representedSpaceMap B S hS τ) (pointHom f)).hom.app
            (A.piece n)) :=
  gradedPullRestrictionApp_comp_rfl_eq (representedSpaceMap B S hS τ) (pointHom f) A n

/-- The comparison of restricted algebras in degree `n`, as a transpose along `τ^* ⊣ τ_*`. -/
theorem pointComparison_app_eq_homEquiv_symm :
    (pointComparison A τ f (yoneda.map τ ≫ f) rfl).app n =
      ((Stacks.RingedSpace.pullbackAdjunction
        (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).homEquiv
          ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).obj (((gradedPull
              (X := smallEtaleRingedTopos B S hS (yonedaSpace B S hS T))
                  (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS
                      (pointHom f))).obj A).piece n))
          ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T')).obj (((gradedPull
              (X := smallEtaleRingedTopos B S hS (yonedaSpace B S hS T'))
                  (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS
                      (representedSpaceMap B S hS τ ≫ pointHom f))).obj A).piece n))).symm
        ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).map (gradedPullRestrictionApp
            (representedSpaceMap B S hS τ) (pointHom f)
                (representedSpaceMap B S hS τ ≫ pointHom f) rfl A n) ≫
          (zariskiDirectImageNatTrans τ).app (((gradedPull (X := smallEtaleRingedTopos B S hS
              (yonedaSpace B S hS T')) (Y := smallEtaleRingedTopos B S hS X)
                  (smallEtaleRingedToposHom B S hS
                      (representedSpaceMap B S hS τ ≫ pointHom f))).obj A).piece n)) := rfl

/-- The transpose of a restriction map, with its objects written as inverse images of modules. -/
theorem homEquiv_symm_gradedPullRestrictionApp_modulePullback (g : yonedaSpace B S hS T ⟶ X)
    (g' : yonedaSpace B S hS T' ⟶ X) (h : representedSpaceMap B S hS τ ≫ g = g') :
      ((Stacks.RingedSpace.pullbackAdjunction
        (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).homEquiv
          ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).obj (((gradedPull
              (X := smallEtaleRingedTopos B S hS (yonedaSpace B S hS T))
                  (Y := smallEtaleRingedTopos B S hS X)
                      (smallEtaleRingedToposHom B S hS g)).obj A).piece n))
          ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T')).obj (((gradedPull
              (X := smallEtaleRingedTopos B S hS (yonedaSpace B S hS T'))
                  (Y := smallEtaleRingedTopos B S hS X)
                      (smallEtaleRingedToposHom B S hS g')).obj A).piece n))).symm
        ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).map (gradedPullRestrictionApp
            (representedSpaceMap B S hS τ) g g' h A n) ≫
          (zariskiDirectImageNatTrans τ).app (((gradedPull (X := smallEtaleRingedTopos B S hS
              (yonedaSpace B S hS T')) (Y := smallEtaleRingedTopos B S hS X)
                  (smallEtaleRingedToposHom B S hS g')).obj A).piece n)) =
      ((Stacks.RingedSpace.pullbackAdjunction
        (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).homEquiv
          ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).obj
              ((modulePullback B S hS g).obj (A.piece n)))
          ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T')).obj
              ((modulePullback B S hS g').obj (A.piece n)))).symm
        ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).map (gradedPullRestrictionApp
            (representedSpaceMap B S hS τ) g g' h A n) ≫
          (zariskiDirectImageNatTrans τ).app ((modulePullback B S hS g').obj (A.piece n))) :=
  rfl

/-- The comparison of restricted algebras in degree `n`, as a transpose along `τ^* ⊣ τ_*`, with
its objects written as inverse images of modules. -/
theorem pointComparison_app_eq_homEquiv_symm_modulePullback :
    (pointComparison A τ f (yoneda.map τ ≫ f) rfl).app n =
      ((Stacks.RingedSpace.pullbackAdjunction
        (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).homEquiv
          ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).obj ((modulePullback B S hS
              (pointHom f)).obj (A.piece n)))
          ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T')).obj
              ((modulePullback B S hS (representedSpaceMap B S hS τ ≫ pointHom f)).obj
                  (A.piece n)))).symm
        ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).map (gradedPullRestrictionApp
            (representedSpaceMap B S hS τ) (pointHom f)
                (representedSpaceMap B S hS τ ≫ pointHom f) rfl A n) ≫
          (zariskiDirectImageNatTrans τ).app ((modulePullback B S hS
              (representedSpaceMap B S hS τ ≫ pointHom f)).obj (A.piece n))) :=
  (pointComparison_app_eq_homEquiv_symm A τ f n).trans
    (homEquiv_symm_gradedPullRestrictionApp_modulePullback A τ n (pointHom f)
      (representedSpaceMap B S hS τ ≫ pointHom f) rfl)

/-- The transpose of the restriction map, rewritten through the composition comparison. -/
theorem homEquiv_symm_pointGradedPullRestrictionApp :
    ((Stacks.RingedSpace.pullbackAdjunction
        (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).homEquiv
          ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).obj ((modulePullback B S hS
              (pointHom f)).obj (A.piece n)))
          ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T')).obj
              ((modulePullback B S hS (representedSpaceMap B S hS τ ≫ pointHom f)).obj
                  (A.piece n)))).symm
        ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).map (gradedPullRestrictionApp
            (representedSpaceMap B S hS τ) (pointHom f)
                (representedSpaceMap B S hS τ ≫ pointHom f) rfl A n) ≫
          (zariskiDirectImageNatTrans τ).app ((modulePullback B S hS
              (representedSpaceMap B S hS τ ≫ pointHom f)).obj (A.piece n))) =
                  ((Stacks.RingedSpace.pullbackAdjunction
        (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).homEquiv
          ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).obj ((modulePullback B S hS
              (pointHom f)).obj (A.piece n)))
          ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T')).obj
              ((modulePullback B S hS (representedSpaceMap B S hS τ ≫ pointHom f)).obj
                  (A.piece n)))).symm
        ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).map ((etaleModuleAdjunction
            (representedSpaceMap B S hS τ)).unit.app ((modulePullback B S hS (pointHom f)).obj
                (A.piece n)) ≫
              (smallEtaleRingedToposHom B S hS
                  (representedSpaceMap B S hS τ)).pushforwardModules.map
                ((modulePullbackCompIso B S hS (representedSpaceMap B S hS τ) (pointHom f)).hom.app
                  (A.piece n))) ≫
          (zariskiDirectImageNatTrans τ).app ((modulePullback B S hS
              (representedSpaceMap B S hS τ ≫ pointHom f)).obj (A.piece n))) :=
  homEquiv_symm_pushforward_map_comp_zariskiDirectImageNatTrans_congr τ ((modulePullback B S hS
      (pointHom f)).obj (A.piece n)) ((modulePullback B S hS
          (representedSpaceMap B S hS τ ≫ pointHom f)).obj (A.piece n))
              (pointGradedPullRestrictionApp_eq A τ f n)

/-- The base-change map of the Zariski reading followed by the Zariski reading of the composition
comparison, as a transpose along `τ^* ⊣ τ_*`. -/
theorem zariskiReadingPullbackHom_app_comp_modulePullbackCompIso :
    (zariskiReadingPullbackHom τ).app ((modulePullback B S hS (pointHom f)).obj (A.piece n)) ≫
        (zariskiReadingFunctor T').map
          ((modulePullbackCompIso B S hS (representedSpaceMap B S hS τ) (pointHom f)).hom.app
            (A.piece n)) = ((Stacks.RingedSpace.pullbackAdjunction
        (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).homEquiv
          ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).obj ((modulePullback B S hS
              (pointHom f)).obj (A.piece n)))
          ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T')).obj
              ((modulePullback B S hS (representedSpaceMap B S hS τ ≫ pointHom f)).obj
                  (A.piece n)))).symm
        ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).map ((etaleModuleAdjunction
            (representedSpaceMap B S hS τ)).unit.app ((modulePullback B S hS (pointHom f)).obj
                (A.piece n)) ≫
              (smallEtaleRingedToposHom B S hS
                  (representedSpaceMap B S hS τ)).pushforwardModules.map
                ((modulePullbackCompIso B S hS (representedSpaceMap B S hS τ) (pointHom f)).hom.app
                  (A.piece n))) ≫
          (zariskiDirectImageNatTrans τ).app ((modulePullback B S hS
              (representedSpaceMap B S hS τ ≫ pointHom f)).obj (A.piece n))) :=
  zariskiReadingPullbackHom_app_comp τ ((modulePullback B S hS (pointHom f)).obj (A.piece n))
      ((modulePullback B S hS (representedSpaceMap B S hS τ ≫ pointHom f)).obj (A.piece n))
      ((modulePullbackCompIso B S hS (representedSpaceMap B S hS τ) (pointHom f)).hom.app
          (A.piece n))

/-- The comparison of restricted algebras in degree `n`, with its source written as an inverse
image of modules. -/
theorem pointComparison_app_eq_zariskiReadingPullbackHom_modulePullback :
    (pointComparison A τ f (yoneda.map τ ≫ f) rfl).app n =
      (zariskiReadingPullbackHom τ).app ((modulePullback B S hS (pointHom f)).obj (A.piece n)) ≫
        (zariskiReadingFunctor T').map
          ((modulePullbackCompIso B S hS (representedSpaceMap B S hS τ) (pointHom f)).hom.app
            (A.piece n)) :=
  ((pointComparison_app_eq_homEquiv_symm_modulePullback A τ f n).trans
      (homEquiv_symm_pointGradedPullRestrictionApp A τ f n)).trans
          (zariskiReadingPullbackHom_app_comp_modulePullbackCompIso A τ f n).symm

/-- **The comparison of restricted algebras, degree by degree.**  For `τ : T' ⟶ T` and a scheme
point `f` at `T`, the degree-`n` comparison `τ^*(f^*𝒜)_Zar ⟶ ((f ∘ τ)^*𝒜)_Zar` is the base-change
map of the Zariski reading at `f^*𝒜_n` followed by the Zariski reading of the composition
comparison `φ^* f^* ≅ (f ∘ φ)^*`. -/
theorem pointComparison_app_eq_zariskiReadingPullbackHom :
    (pointComparison A τ f (yoneda.map τ ≫ f) rfl).app n =
      (zariskiReadingPullbackHom τ).app ((etalePointAlgebra A T f).piece n) ≫
        (zariskiReadingFunctor T').map
          ((modulePullbackCompIso B S hS (representedSpaceMap B S hS τ) (pointHom f)).hom.app
            (A.piece n)) :=
  pointComparison_app_eq_zariskiReadingPullbackHom_modulePullback A τ f n

end PointComparison

end AlgebraicGeometry.Space

end
