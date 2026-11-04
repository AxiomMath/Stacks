module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CyclotomicRepresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.GlobalSections
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianInternalHomGModules
public import StacksFrontier.CategoryTheory.Sites.InternalHomDenseSubsite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleSheafHomForget
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.FiniteRingModuleUnderlyingAbelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLiftPushforward

/-!
# `Hom(ℱ_M, ℱ_W) = ℱ_{Hom(M, W)}`

Let `X` be a connected scheme with a geometric point `x`, `Λ` a finite ring, `M` a finite
`Λ`-module and `W` a finite `ℤ/n`-module, both with continuous actions of `π₁(X, x)`. Then the
internal Hom of the sheaves `ℱ_M` and `ℱ_W` attached to them by Tag 0DV5 is the sheaf attached to
`Hom_ℤ(M, W)` with the conjugation action.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.ConstantSheaf Stacks.GroupCohomology

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1]
  (x : GeometricPoint X.1) (Λ : Type) [Ring Λ] [Finite Λ]

omit [ConnectedSpace X.1] in
/-- The abelian sheaf of a module sheaf of the domain of Tag 0DV5 (3) is its underlying abelian
sheaf. -/
lemma finiteTypeLocallyConstantModuleSheafAbelian_obj
    (F : ObjectProperty.FullSubcategory
        (fun F : Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ) ↦
          IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B X.1 X.2) F)) :
    (finiteTypeLocallyConstantModuleSheafAbelian B X Λ F).obj =
      (sheafCompose (SmallEtale.topology B X.1 X.2)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F.obj :=
  rfl

/-- The discrete `π₁(X, x)`-module of the abelian sheaf underlying a module sheaf is the abelian
group underlying its module of Tag 0DV5 (3). -/
lemma finiteLocallyConstantAbelianSheafEquivalence_functor_obj_abelian
    (F : ObjectProperty.FullSubcategory
        (fun F : Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} Λ) ↦
          IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B X.1 X.2) F)) :
    (finiteLocallyConstantAbelianSheafEquivalence B X x).functor.obj
        (finiteTypeLocallyConstantModuleSheafAbelian B X Λ F) =
      (finiteTypeContinuousModuleForgetAbelian Λ (EtaleFundamentalGroup X.1 x)).obj
        ((finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).functor.obj F) :=
  rfl

section Small

variable (n : ℕ) [NeZero n] [Algebra (ZMod n) Λ]

/-- The sheaf of `Λ`-modules of Tag 0DV5 (3) attached to `M`, on the site of Stacks 021B. -/
abbrev representationModuleSheafSmall (Λ : Type) [Ring Λ] [Finite Λ]
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :=
  (finiteTypeLocallyConstantModuleSheafEquivalence B X x Λ).inverse.obj M

/-- Its underlying finite locally constant abelian sheaf. -/
abbrev representationAbelianSheafSmall (Λ : Type) [Ring Λ] [Finite Λ]
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    (isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1}
      (SmallEtale.topology B X.1 X.2)).FullSubcategory :=
  finiteTypeLocallyConstantModuleSheafAbelian B X Λ (representationModuleSheafSmall B X x Λ M)

/-- The counit of Tag 0DV5 (3) on the underlying discrete `π₁(X, x)`-modules: Tag 0DV5 (2)
applied to the abelian sheaf of `ℱ_N` gives back the discrete module underlying `N`. -/
def representationAbelianCounitIso (R : Type) [Ring R] [Finite R]
    (N : FiniteTypeContinuousModule.{0, u + 1, u + 1} R (EtaleFundamentalGroup X.1 x)) :
    (finiteLocallyConstantAbelianSheafEquivalence B X x).functor.obj
        (representationAbelianSheafSmall B X x R N) ≅
      (finiteTypeContinuousModuleForgetAbelian R (EtaleFundamentalGroup X.1 x)).obj N :=
  (finiteTypeContinuousModuleForgetAbelian R (EtaleFundamentalGroup X.1 x)).mapIso
    ((finiteTypeLocallyConstantModuleSheafEquivalence B X x R).counitIso.app N)

/-- **The internal Hom of the abelian sheaves of `M` and `W` is finite locally constant**: it is
the abelian sheaf underlying the internal Hom of sheaves of `ℤ/n`-modules. -/
theorem isFiniteLocallyConstantAbelianSheaf_internalHomSheaf_representation
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
    (W : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod n) (EtaleFundamentalGroup X.1 x)) :
    isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1} (SmallEtale.topology B X.1 X.2)
      (internalHomSheaf (SmallEtale.topology B X.1 X.2)
        (representationAbelianSheafSmall B X x Λ M).obj
        (representationAbelianSheafSmall B X x (ZMod n) W).obj) := by
  have h := isFiniteLocallyConstantAbelianSheaf_internalHomSheaf_zmodSheafForget.{u, u + 1}
    (SmallEtale.topology B X.1 X.2) n
  let F₁ : Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} (ZMod n)) :=
    (sheafCompose (SmallEtale.topology B X.1 X.2)
      (ModuleCat.restrictScalars.{u + 1} (algebraMap (ZMod n) Λ))).obj
        (representationModuleSheafSmall B X x Λ M).obj
  let F₂ : Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} (ZMod n)) :=
    (representationModuleSheafSmall B X x (ZMod n) W).obj
  exact h F₁ F₂ (representationAbelianSheafSmall B X x Λ M).property
    (representationAbelianSheafSmall B X x (ZMod n) W).property

/-- **`ℋom(ℱ_M, ℱ_W) ≅ ℱ_{Hom_ℤ(M, W)}` on the site of Stacks 021B, as abelian sheaves**: the
internal Hom of the abelian sheaves of `M` and `W` is the abelian sheaf Tag 0DV5 (2) attaches to
the finite discrete `π₁(X, x)`-module `Hom_ℤ(M, W)` with the conjugation action. -/
def internalHomRepresentationSmallIso
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
    (W : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod n) (EtaleFundamentalGroup X.1 x)) :
    (⟨internalHomSheaf (SmallEtale.topology B X.1 X.2)
        (representationAbelianSheafSmall B X x Λ M).obj
        (representationAbelianSheafSmall B X x (ZMod n) W).obj,
      isFiniteLocallyConstantAbelianSheaf_internalHomSheaf_representation B X x Λ n M W⟩ :
        (isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1}
          (SmallEtale.topology B X.1 X.2)).FullSubcategory) ≅
      (finiteLocallyConstantAbelianSheafEquivalence B X x).inverse.obj
        (ContinuousGAddCommGrp.homIsFinite
          ((finiteTypeContinuousModuleForgetAbelian Λ (EtaleFundamentalGroup X.1 x)).obj M)
          ((finiteTypeContinuousModuleForgetAbelian (ZMod n)
            (EtaleFundamentalGroup X.1 x)).obj W)) :=
  internalHomTransportCongrIso (SmallEtale.topology B X.1 X.2)
    (finiteLocallyConstantSetsEquivalence' B X x)
    (representationAbelianSheafSmall B X x (ZMod n) W)
    (isFiniteLocallyConstantAbelianSheaf_internalHomSheaf_representation B X x Λ n M W)
    (representationAbelianCounitIso B X x Λ M) (representationAbelianCounitIso B X x (ZMod n) W)

/-- A finite `ℤ/n`-module with a continuous action is finite, as an abelian group. -/
instance finite_continuousModuleForget_obj
    (W : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod n) (EtaleFundamentalGroup X.1 x)) :
    Finite ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
      (EtaleFundamentalGroup X.1 x)).obj W.obj).obj.obj.V :=
  haveI : Module.Finite (ZMod n) W.obj.obj.obj.V := W.property
  haveI : Finite W.obj.obj.obj.V := Module.finite_of_finite (ZMod n)
  inferInstanceAs (Finite W.obj.obj.obj.V)

/-- **`Hom_ℤ(M, W)` of the underlying discrete `π₁(X, x)`-modules is the discrete module
underlying `homDualFunctor`**: the same additive maps with the same conjugation action. -/
def homIsFiniteForgetAbelianIso
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
    (W : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod n) (EtaleFundamentalGroup X.1 x)) :
    ContinuousGAddCommGrp.homIsFinite
        ((finiteTypeContinuousModuleForgetAbelian Λ (EtaleFundamentalGroup X.1 x)).obj M)
        ((finiteTypeContinuousModuleForgetAbelian (ZMod n) (EtaleFundamentalGroup X.1 x)).obj W) ≅
      (finiteTypeContinuousModuleForgetAbelian Λᵐᵒᵖ (EtaleFundamentalGroup X.1 x)).obj
        ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
          (EtaleFundamentalGroup X.1 x)).obj W.obj)).obj (op M)) where
  hom := ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    { hom := AddCommGrpCat.ofHom (AddMonoidHom.id (M.obj.obj.obj.V →+ W.obj.obj.obj.V))
      comm := fun _ ↦ rfl }))
  inv := ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    { hom := AddCommGrpCat.ofHom (AddMonoidHom.id (M.obj.obj.obj.V →+ W.obj.obj.obj.V))
      comm := fun _ ↦ rfl }))

/-- **The abelian sheaf of `ℱ_N` on the site of Stacks 021B is `E⁻¹` of the discrete module
underlying `N`**, by the counit of Tag 0DV5 (3). -/
def representationAbelianSheafSmallIso (R : Type) [Ring R] [Finite R]
    (N : FiniteTypeContinuousModule.{0, u + 1, u + 1} R (EtaleFundamentalGroup X.1 x)) :
    representationAbelianSheafSmall B X x R N ≅
      (finiteLocallyConstantAbelianSheafEquivalence B X x).inverse.obj
        ((finiteTypeContinuousModuleForgetAbelian R (EtaleFundamentalGroup X.1 x)).obj N) :=
  (finiteLocallyConstantAbelianSheafEquivalence B X x).unitIso.app _ ≪≫
    (finiteLocallyConstantAbelianSheafEquivalence B X x).inverse.mapIso
      (representationAbelianCounitIso B X x R N)

/-- **`ℋom(ℱ_M, ℱ_W) ≅ ℱ_{Hom_ℤ(M, W)}` on the site of Stacks 021B**, as abelian sheaves, the
right-hand side being the abelian sheaf of the `Λᵐᵒᵖ`-module `Hom_ℤ(M, W)`. -/
def internalHomRepresentationSmallDualIso
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
    (W : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod n) (EtaleFundamentalGroup X.1 x)) :
    internalHomSheaf (SmallEtale.topology B X.1 X.2)
        (representationAbelianSheafSmall B X x Λ M).obj
        (representationAbelianSheafSmall B X x (ZMod n) W).obj ≅
      (representationAbelianSheafSmall B X x Λᵐᵒᵖ
        ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
          (EtaleFundamentalGroup X.1 x)).obj W.obj)).obj (op M))).obj :=
  (ObjectProperty.ι _).mapIso
    (internalHomRepresentationSmallIso B X x Λ n M W ≪≫
      (finiteLocallyConstantAbelianSheafEquivalence B X x).inverse.mapIso
        (homIsFiniteForgetAbelianIso B X x Λ n M W) ≪≫
      (representationAbelianSheafSmallIso B X x Λᵐᵒᵖ _).symm)

/-- Forgetting the module structure of a sheaf of modules whose coefficients were lifted to a
universe forgets the lift: the sections `ULift M` are `M`. -/
def sheafComposeForgetUliftIso (R : Type) [Ring R]
    (S : Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} R)) :
    (sheafCompose (SmallEtale.topology B X.1 X.2)
        (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).obj
        ((sheafCompose (SmallEtale.topology B X.1 X.2)
          (ModuleCat.uliftFunctor.{0, u + 1} R)).obj S) ≅
      (sheafCompose (SmallEtale.topology B X.1 X.2)
        (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).obj S :=
  (fullyFaithfulSheafToPresheaf (SmallEtale.topology B X.1 X.2) AddCommGrpCat.{u + 1}).preimageIso
    (NatIso.ofComponents (fun _ ↦ AddEquiv.toAddCommGrpIso AddEquiv.ulift) (fun _ ↦ rfl))

/-- The equivalence of abelian sheaves on the two presentations of the small étale site is
additive: its inverse is restriction along the dense subsite inclusion, which is additive. -/
instance additive_sheafEquiv_functor :
    (SmallEtale.sheafEquiv B X.1 X.2 AddCommGrpCat.{u + 1}).functor.Additive :=
  haveI : (SmallEtale.sheafEquiv B X.1 X.2 AddCommGrpCat.{u + 1}).symm.functor.Additive :=
    { map_add := rfl }
  Equivalence.inverse_additive (SmallEtale.sheafEquiv B X.1 X.2 AddCommGrpCat.{u + 1}).symm

/-- **Sheaves of `R`-modules move from the site of Stacks 021B to Mathlib's small étale site as
their underlying abelian sheaves do**: the equivalence of sheaves of `R`-modules is the lift
(`Stacks.ModuleCatLift.moduleLift`) of the equivalence of abelian sheaves, both being left
adjoint to restriction along the dense subsite inclusion. -/
def sheafEquivFunctorIsoModuleLift (R : Type) [Ring R] :
    letI := Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize.{u, u, 0, u + 1} R
    (SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} R)).functor ≅
      Stacks.ModuleCatLift.moduleLift.{u + 1} R (SmallEtale.topology B X.1 X.2)
        X.1.smallEtaleTopology
        (SmallEtale.sheafEquiv B X.1 X.2 AddCommGrpCat.{u + 1}).functor :=
  letI := Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize.{u, u, 0, u + 1} R
  Stacks.ModuleCatLift.leftAdjointIsoModuleLift.{u + 1} R (SmallEtale.toEtaleSite B X.1 X.2) _ _
    (SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} R)).toAdjunction
    (SmallEtale.sheafEquiv B X.1 X.2 AddCommGrpCat.{u + 1}).toAdjunction

/-- **The abelian sheaf underlying `ℱ_N` on Mathlib's small étale site** is the abelian sheaf of
Tag 0DV5 on the site of Stacks 021B, moved across the equivalence of the two sites. -/
def representationSheafForgetIso (R : Type) [Ring R] [Finite R]
    (N : FiniteTypeContinuousModule.{0, u + 1, u + 1} R (EtaleFundamentalGroup X.1 x)) :
    (sheafCompose X.1.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).obj
        ((representationSheaf B X x R).obj N) ≅
      (SmallEtale.sheafEquiv B X.1 X.2 AddCommGrpCat.{u + 1}).functor.obj
        (representationAbelianSheafSmall B X x R N).obj :=
  (sheafCompose X.1.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).mapIso
      ((sheafEquivFunctorIsoModuleLift B X R).app
        ((sheafCompose (SmallEtale.topology B X.1 X.2) (ModuleCat.uliftFunctor.{0, u + 1} R)).obj
          (representationModuleSheafSmall B X x R N).obj)) ≪≫
    (SmallEtale.sheafEquiv B X.1 X.2 AddCommGrpCat.{u + 1}).functor.mapIso
      (sheafComposeForgetUliftIso B X R (representationModuleSheafSmall B X x R N).obj)

/-- **The internal Hom of abelian sheaves commutes with the equivalence of the sheaves on the two
presentations of the small étale site**, by `Stacks.Sites.internalHomSheafPushforwardIso` for the
dense subsite inclusion `toEtaleSite`. -/
def internalHomSheafEquivFunctorIso
    (𝒜 ℬ : Sheaf (SmallEtale.topology B X.1 X.2) AddCommGrpCat.{u + 1}) :
    internalHomSheaf X.1.smallEtaleTopology
        ((SmallEtale.sheafEquiv B X.1 X.2 AddCommGrpCat.{u + 1}).functor.obj 𝒜)
        ((SmallEtale.sheafEquiv B X.1 X.2 AddCommGrpCat.{u + 1}).functor.obj ℬ) ≅
      (SmallEtale.sheafEquiv B X.1 X.2 AddCommGrpCat.{u + 1}).functor.obj
        (internalHomSheaf (SmallEtale.topology B X.1 X.2) 𝒜 ℬ) :=
  ((SmallEtale.sheafEquiv B X.1 X.2 AddCommGrpCat.{u + 1}).counitIso.app _).symm ≪≫
    (SmallEtale.sheafEquiv B X.1 X.2 AddCommGrpCat.{u + 1}).functor.mapIso
      (Stacks.Sites.internalHomSheafPushforwardIso (J := SmallEtale.topology B X.1 X.2)
          (SmallEtale.toEtaleSite B X.1 X.2)
          ((SmallEtale.sheafEquiv B X.1 X.2 AddCommGrpCat.{u + 1}).functor.obj 𝒜)
          ((SmallEtale.sheafEquiv B X.1 X.2 AddCommGrpCat.{u + 1}).functor.obj ℬ) ≪≫
        Stacks.Sites.internalHomSheafCongr (SmallEtale.topology B X.1 X.2)
          ((SmallEtale.sheafEquiv B X.1 X.2 AddCommGrpCat.{u + 1}).unitIso.app 𝒜).symm
          ((SmallEtale.sheafEquiv B X.1 X.2 AddCommGrpCat.{u + 1}).unitIso.app ℬ).symm)

/-- **`ℋom(ℱ_M, ℱ_W) ≅ ℱ_{Hom_ℤ(M, W)}` on Mathlib's small étale site, as abelian sheaves.** -/
def internalHomRepresentationSheafForgetIso
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
    (W : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod n) (EtaleFundamentalGroup X.1 x)) :
    internalHomSheaf X.1.smallEtaleTopology
        ((sheafCompose X.1.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          ((representationSheaf B X x Λ).obj M))
        ((sheafCompose X.1.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1})).obj
          ((representationSheaf B X x (ZMod n)).obj W)) ≅
      (sheafCompose X.1.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λᵐᵒᵖ) AddCommGrpCat.{u + 1})).obj
        ((representationSheaf B X x Λᵐᵒᵖ).obj
          ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
            (EtaleFundamentalGroup X.1 x)).obj W.obj)).obj (op M))) :=
  Stacks.Sites.internalHomSheafCongr X.1.smallEtaleTopology
      (representationSheafForgetIso B X x Λ M)
      (representationSheafForgetIso B X x (ZMod n) W) ≪≫
    internalHomSheafEquivFunctorIso B X _ _ ≪≫
    (SmallEtale.sheafEquiv B X.1 X.2 AddCommGrpCat.{u + 1}).functor.mapIso
      (internalHomRepresentationSmallDualIso B X x Λ n M W) ≪≫
    (representationSheafForgetIso B X x Λᵐᵒᵖ _).symm

/-- **The sheaf `Hom_{ℤ/n}(ℱ_M, ℱ_W) ≅ ℱ_{Hom_ℤ(M, W)}`** (an input of Tag 03VM). For a
connected scheme `X` with a geometric point `x`, a finite ring `Λ` which is a `ℤ/n`-algebra, a
finite `Λ`-module `M` and a finite `ℤ/n`-module `W` with continuous actions of `π₁(X, x)`, the
internal Hom of sheaves of `ℤ/n`-modules `SheafHom_{ℤ/n}(ℱ_M, ℱ_W)` is the sheaf attached to the
`Λᵐᵒᵖ`-module `Hom_ℤ(M, W)` with the conjugation action
(`Stacks.GroupCohomology.homDualFunctor`), read as a sheaf of `ℤ/n`-modules. -/
def representationSheafModuleSheafHomIso
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
    (W : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod n) (EtaleFundamentalGroup X.1 x)) :
    Stacks.ConstantSheaf.moduleSheafHom X.1.smallEtaleTopology (ZMod n)
        ((sheafCompose X.1.smallEtaleTopology
          (ModuleCat.restrictScalars.{u + 1} (algebraMap (ZMod n) Λ))).obj
          ((representationSheaf B X x Λ).obj M))
        ((representationSheaf B X x (ZMod n)).obj W) ≅
      (sheafCompose X.1.smallEtaleTopology
          (ModuleCat.restrictScalars.{u + 1} (algebraMap (ZMod n) Λᵐᵒᵖ))).obj
        ((representationSheaf B X x Λᵐᵒᵖ).obj
          ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
            (EtaleFundamentalGroup X.1 x)).obj W.obj)).obj (op M))) :=
  zmodSheafIsoOfForgetIso.{u, u + 1} X.1.smallEtaleTopology n
    (moduleSheafHomForgetIso.{u, u + 1} X.1.smallEtaleTopology n _ _ ≪≫
      internalHomRepresentationSheafForgetIso B X x Λ n M W)

end Small

end AlgebraicGeometry

end
