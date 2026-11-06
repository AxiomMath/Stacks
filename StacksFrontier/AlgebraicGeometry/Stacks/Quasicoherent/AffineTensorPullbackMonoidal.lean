module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineTensorPullbackComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineDirectImageComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineDirectImageTensor
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.PointPullbackDescent
public import StacksFrontier.CategoryTheory.Monoidal.NatTransIsMonoidalOfTensor

/-!
# The comparison of Stacks 0GRQ is an isomorphism of tensor functors

Let `g : U = Spec A ⟶ 𝒳` be an affine 1-morphism from an affine scheme to an algebraic stack and
`F : QCoh(𝒪_𝒳) ⥤ Mod_R` a right exact functor commuting with direct sums which is braided monoidal
for the strict tensor product (II) of `QCoh(𝒪_𝒳)` (the tensor product sheaf of Tag 01CA). With
`C = F(g_*𝒪_U)` and `A ⟶ C` of Stacks 0GRK, the proof of Stacks 0GRQ uses the comparison

  `θ : F(-) ⊗_R C ≅ Γ(U, g^*(-)) ⊗_A C ≅ y^*`,  `c ⊗ m ↦ c • κ(F(η_M) m)`,

for a point `y` over `Spec C` above the chart point `g(U)`, where `κ : F ∘ g_* ≅ Γ(U, -) ⊗_A C` is
the isomorphism of Stacks 0GRK and `η` the unit of `g^* ⊣ g_*`. The descent of `y` to `Spec R`
needs `θ` to be an isomorphism of tensor functors. This file proves it:

* `κ` is lax monoidal (`AlgebraicGeometry.Stack.AlgebraicStacks.localizedTensorLeft_eq`):
  `κ(F(λ)(μ(a ⊗ b))) = (Γ μ)(κ(a) ⊗ κ(b))` for the lax structure `λ` of `g_*`
  (`AlgebraicGeometry.Stack.AlgebraicStacks.directImageTensor`). Both sides are natural in the
  second factor and `M ↦ F(g_*M~)` commutes with colimits, so they agree once they agree on `𝒪_U`
  (`ModuleCat.natTrans_ext_of_app_self`), where `λ` is the action of `g_*𝒪_U` and the identity is
  the `C`-linearity of `κ` (the crux, read for (II) through
  `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModulesComparisonInverse_μ_hom`);
* `η` is compatible with the tensor products
  (`AlgebraicGeometry.Stack.AlgebraicStacks.affineQuasicoherentUnit_tensor`);
* hence `θ` is compatible with the tensorators, and with the units by
  `CategoryTheory.NatTrans.isMonoidal_of_tensor`.

The isomorphism `κ` of the base is stated for `F` braided for the localized structure (I); the
statements here are for `F` braided for (II), through the wrappers
`AlgebraicGeometry.Stack.AlgebraicStacks.localizedGlobalSectionsIso`,
`AlgebraicGeometry.Stack.AlgebraicStacks.localizedPullbackTensorComparison` and
`AlgebraicGeometry.Stack.AlgebraicStacks.localizedPointPullbackTensorIso`, which apply the base
constructions to `F` seen as a functor out of (I).

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.localizedTensorLeft_eq`: Stacks 0GRK is lax monoidal.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isMonoidal_localizedPointPullbackTensorIso`:
  `θ : F(-) ⊗_R C ≅ y^*` is an isomorphism of tensor functors.

## References

* [Stacks Project, Tag 0GRK](https://stacks.math.columbia.edu/tag/0GRK)
* [Stacks Project, Tag 0GRQ](https://stacks.math.columbia.edu/tag/0GRQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct ChangeOfRings

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u w

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {U : BigFppfOver B S hS}

variable (U) in
/-- On the structure sheaf, the objectwise counit `𝒪(T) ⊗_A Γ(U, 𝒪_U) ⟶ 𝒪(T)` is the
identification `𝒪(T) ⊗_A A ≅ 𝒪(T)`. -/
theorem tildeCounitPresheaf_unit :
    tildeCounitPresheaf (SheafOfModules.unit
        (AlgebraicStacks.fppfStructureRingSheaf B S hS (schemeStack.{u, w} B S hS U))) =
      (tildePresheafSelfIso.{u, w} U).hom := by
  refine PresheafOfModules.hom_ext fun T => Stacks.PullbackModel.extendScalars_hom_ext _ fun a => ?_
  refine (tildeCounitPresheafApp_one_tmul _ T a).trans ?_
  refine Eq.trans ?_ (tildePresheafSelfIso_hom_app_tmul.{u, w} U T 1 a).symm
  exact (one_mul (globalRingHomApp U T a)).symm

variable (U) in
/-- On the structure sheaf, the counit `Γ(U, 𝒪_U)~ ⟶ 𝒪_U` is `A~ ≅ 𝒪_U`. -/
theorem tildeCounit_unit :
    tildeCounit (SheafOfModules.unit
        (AlgebraicStacks.fppfStructureRingSheaf B S hS (schemeStack.{u, w} B S hS U))) =
      (tildeSelfIso.{u, w} U).hom :=
  congrArg (fun k => (Stacks.SheafOfModules.sheafifyFunctor
      (AlgebraicStacks.fppfStructureSheaf B S hS (schemeStack.{u, w} B S hS U)).obj
      (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS (schemeStack.{u, w} B S hS U))).map k ≫
    (Stacks.SheafOfModules.sheafifyValIso
      (AlgebraicStacks.fppfStructureSheaf B S hS (schemeStack.{u, w} B S hS U)).obj
      (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS (schemeStack.{u, w} B S hS U))
      (SheafOfModules.unit _)).hom) (tildeCounitPresheaf_unit U)

/-- On the structure sheaf, the counit isomorphism `Γ(U, -)~ ≅ 𝟭` is `A~ ≅ 𝒪_U`. -/
theorem tildeCounitIso_hom_app_structureSheaf (hU : IsAffineOver B S hS U) :
    (tildeCounitIso.{u, w} U hU).hom.app (quasicoherentStructureSheaf.{u, w} (U := U)) =
      (tildeQuasicoherentSelfIso.{u, w} U).hom :=
  ObjectProperty.hom_ext _ (tildeCounit_unit U)

section Functor

attribute [local instance] FibredSite.monoidalCategoryQuasicoherentModules
  AlgebraicStacks.quasicoherentSymmetricCategory

variable {𝒳 : AlgebraicStacks.{u, w} B S hS}
  (g : schemeStack.{u, w} B S hS U ⟶ 𝒳) (hg : AlgebraicStacks.IsAffineHom B S hS g)
  {R : Type u} [CommRing R]
  (F : AlgebraicStacks.quasicoherentModules B S hS 𝒳 ⥤ ModuleCat.{u} R) [F.LaxBraided]
  [F.Additive] [PreservesFiniteColimits F] [∀ J : Type u, PreservesColimitsOfShape (Discrete J) F]

/-- **Stacks 0GRK (global-sections form) on the structure sheaf**:
`C = F(g_*𝒪_U) ≅ Γ(U, 𝒪_U) ⊗_A C` is `c ↦ c ⊗ 1`. -/
theorem affineTensorFunctorGlobalSectionsIso_hom_app_structureSheaf (hU : IsAffineOver B S hS U)
    (c : affineTensorAlgebra g hg F) :
    ((affineTensorFunctorGlobalSectionsIso g hg F hU).hom.app
        (quasicoherentStructureSheaf.{u, w} (U := U))).hom c =
      (ModuleCat.ExtendScalars.objSelfIso (affineTensorRingHom g hg F)).inv.hom c := by
  have hκ : (affineTensorFunctorIso g hg F).hom.app (ModuleCat.of _ (schemeGlobalRing U)) =
      (affineTensorFreeIso g hg F).hom :=
    ModuleCat.isoOfRegularAction_hom_app _ _ _ _ _ _
  have h1 : (tildeCounitIso.{u, w} U hU).inv.app (quasicoherentStructureSheaf.{u, w} (U := U)) ≫
      (tildeQuasicoherentSelfIso.{u, w} U).hom = 𝟙 _ := by
    rw [← tildeCounitIso_hom_app_structureSheaf hU, Iso.inv_hom_id_app]
  have h3 : F.map ((affineQuasicoherentPushforward g hg).map
        ((tildeCounitIso.{u, w} U hU).inv.app (quasicoherentStructureSheaf.{u, w} (U := U)))) ≫
      F.map ((affineQuasicoherentPushforward g hg).map (tildeQuasicoherentSelfIso.{u, w} U).hom) =
        𝟙 _ :=
    (F.map_comp _ _).symm.trans ((congrArg F.map
      (((affineQuasicoherentPushforward g hg).map_comp _ _).symm.trans
        ((congrArg (affineQuasicoherentPushforward g hg).map h1).trans
          ((affineQuasicoherentPushforward g hg).map_id _)))).trans (F.map_id _))
  have h2 := congrArg (fun k => k.hom c) h3
  refine (congrArg (fun k => k.hom ((F.map ((affineQuasicoherentPushforward g hg).map
    ((tildeCounitIso.{u, w} U hU).inv.app (quasicoherentStructureSheaf.{u, w} (U := U))))).hom c))
      hκ).trans ?_
  exact (AlgebraicStacks.affineTensorFreeIso_hom_apply g hg F _).trans
    (congrArg (ModuleCat.ExtendScalars.objSelfIso (affineTensorRingHom g hg F)).inv.hom h2)

end Functor

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Stack.AlgebraicStacks

attribute [local instance] hasSheafCompose_forget_ringCat
  hasSheafCompose_forget_commRingCat Stacks.hasSheafCompose_forget₂_commRingCat
  FlatFppf.hasSheafify_addCommGrpCat FlatFppf.wEqualsLocallyBijective_addCommGrpCat
  FlatFppf.hasSheafify_fppf_addCommGrpCat FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat
  FlatFppf.hasSheafify_associatedTopology_ab
  FlatFppf.wEqualsLocallyBijective_fppfTopology_addCommGrpCat

section Inverse

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- **The tensorator of the inverse comparison** `QCoh(𝒪_𝒳)` (I) `⥤` (II) is the inverse of
`Stacks.SheafOfModules.tensorObjIso`. -/
theorem quasicoherentModulesComparisonInverse_μ_hom (X Y : quasicoherentModules B S hS 𝒳) :
    (@Functor.LaxMonoidal.μ _ _ (FibredSite.monoidalCategoryQuasicoherentModules B S hS
        𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) _ _ (quasicoherentModulesMonoidal B S hS 𝒳) _
      (@Functor.Monoidal.toLaxMonoidal _ _ _ _ _ _ _
        (quasicoherentModulesComparisonInverseMonoidal B S hS 𝒳)) X Y).hom =
      (Stacks.SheafOfModules.tensorObjIso (FlatFppf.fppfRingedTopos B S hS 𝒳).O.obj
        (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf
          (FlatFppf.fppfRingedTopos B S hS 𝒳).O) X.obj Y.obj).inv := by
  have h := @Adjunction.map_μ_comp_counit_app_tensor _ _ (quasicoherentModulesMonoidal B S hS 𝒳)
    _ _ (FibredSite.monoidalCategoryQuasicoherentModules B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids) _ _ (quasicoherentModulesComparison B S hS 𝒳).toAdjunction
    (@Functor.Monoidal.toOplaxMonoidal _ _ _ _ _ _ _
      (quasicoherentModulesComparisonMonoidal B S hS 𝒳))
    (@Functor.Monoidal.toLaxMonoidal _ _ _ _ _ _ _
      (quasicoherentModulesComparisonInverseMonoidal B S hS 𝒳))
    (isMonoidal_quasicoherentModulesComparison B S hS 𝒳) X Y
  have h3 := congrArg (fun f => f.hom)
    (@Functor.Monoidal.μ_δ _ _ (quasicoherentModulesMonoidal B S hS 𝒳) _ _
      (FibredSite.monoidalCategoryQuasicoherentModules B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids) _ (quasicoherentModulesComparisonMonoidal B S hS 𝒳) X Y)
  have ht := @MonoidalCategory.id_tensorHom_id _ _ (FibredSite.monoidalCategoryQuasicoherentModules
    B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) X Y
  refine ((Category.comp_id _).symm.trans (congrArg (fun f => f.hom) h)).trans ?_
  refine (congrArg (fun k => InducedCategory.Hom.hom
    (@Functor.OplaxMonoidal.δ _ _ (quasicoherentModulesMonoidal B S hS 𝒳) _ _
      (FibredSite.monoidalCategoryQuasicoherentModules B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids) (quasicoherentModulesComparison B S hS 𝒳).functor
      (@Functor.Monoidal.toOplaxMonoidal _ _ _ _ _ _ _
        (quasicoherentModulesComparisonMonoidal B S hS 𝒳)) X Y ≫ k)) ht).trans ?_
  refine (congrArg InducedCategory.Hom.hom (Category.comp_id _)).trans ?_
  exact (Iso.hom_comp_eq_id _).1 h3

end Inverse

section Localized

attribute [local instance] fppfModulesMonoidal fppfModulesBraided fppfModulesSymmetric

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U : BigFppfOver B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
  (g : schemeStack.{u, w} B S hS U ⟶ 𝒳) (hg : IsAffineHom B S hS g)
  {R : Type u} [CommRing R] (F : quasicoherentModules B S hS 𝒳 ⥤ ModuleCat.{u} R) [hF : F.Braided]
  [hFa : F.Additive] [hFc : PreservesFiniteColimits F]
  [hFs : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) F] (hU : IsAffineOver B S hS U)

/-- The strict monoidal structure (II) on `Mod(𝒪_U)` for a scheme `U`, keyed at
`AlgebraicGeometry.Stack.schemeStack` so that instance search finds it. -/
local instance schemeStackFppfModulesMonoidal :
    MonoidalCategory (Stack.fppfModules B S hS (schemeStack.{u, w} B S hS U)) :=
  fppfModulesMonoidal B S hS _

/-- The strict monoidal structure (II) on `QCoh(𝒪_U)` for a scheme `U`, keyed at
`AlgebraicGeometry.Stack.schemeStack` so that instance search finds it. -/
local instance schemeStackQuasicoherentModulesMonoidal :
    MonoidalCategory (quasicoherentModules B S hS (schemeStack.{u, w} B S hS U)) :=
  quasicoherentModulesMonoidal B S hS _

/-- The action `g_*N ⊗ g_*𝒪_U ⟶ g_*N` in `QCoh(𝒪_𝒳)` for the strict structure (II). -/
def directImageActStrict (N : quasicoherentModules B S hS (schemeStack.{u, w} B S hS U)) :
    (affineQuasicoherentPushforward g hg).obj N ⊗ affineQuasicoherentStructureSheaf g hg ⟶
      (affineQuasicoherentPushforward g hg).obj N :=
  ObjectProperty.homMk (directImageAct g hg N.obj)

/-- **Stacks 0GRK (global-sections form) for a functor braided monoidal for (II)**:
`F(g_*N) ≅ Γ(U, N) ⊗_A C`, with `C` and `A ⟶ C` of
`AlgebraicGeometry.Stack.AlgebraicStacks.comparisonTensorAlgebra`. -/
def localizedGlobalSectionsIso :
    affineQuasicoherentPushforward g hg ⋙ F ≅
      quasicoherentGlobalSections.{u, w} U ⋙
        ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF) ⋙
          ModuleCat.restrictScalars (algebraMap R (comparisonTensorAlgebra g hg F hF)) :=
  letI := localizedLaxBraided F hF
  letI := additive_comparisonInverse_comp F
  letI : PreservesFiniteColimits ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F) := hFc
  letI : ∀ J : Type u, PreservesColimitsOfShape (Discrete J)
      ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F) := hFs
  affineTensorFunctorGlobalSectionsIso g hg
    ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F) hU

/-- Applying a functor to an equation `f ≫ g = h` of morphisms evaluates on elements. -/
private theorem map_hom_comp_apply_eq {R : Type*} [CommRing R] {C : Type*} [Category C]
    (G : C ⥤ ModuleCat R) {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (e : f ≫ g = h)
    (x : G.obj X) : (G.map g).hom ((G.map f).hom x) = (G.map h).hom x :=
  e ▸ congrArg (fun k => k.hom x) (G.map_comp f g).symm

/-- **The 0GRK isomorphism is `C`-linear, for the strict structure (II)**: on
`F(g_*N) ≅ Γ(U, N) ⊗_A C`, `z ↦ F(act)(μ(z ⊗ c))` corresponds to the multiplication by `c`. -/
theorem localizedGlobalSectionsIso_hom_app_map_directImageActStrict_μ
    (c : comparisonTensorAlgebra g hg F hF)
    (N : quasicoherentModules B S hS (schemeStack.{u, w} B S hS U))
    (z : F.obj ((affineQuasicoherentPushforward g hg).obj N)) :
    ((localizedGlobalSectionsIso g hg F hU).hom.app N).hom
        ((F.map (directImageActStrict g hg N)).hom
          ((Functor.LaxMonoidal.μ F _ (affineQuasicoherentStructureSheaf g hg)).hom (z ⊗ₜ c))) =
      @HSMul.hSMul (comparisonTensorAlgebra g hg F hF)
        ((ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).obj
          ((quasicoherentGlobalSections.{u, w} U).obj N)) _ instHSMul c
        (((localizedGlobalSectionsIso g hg F hU).hom.app N).hom z) := by
  let := localizedBraided F hF
  let := additive_comparisonInverse_comp F
  let : PreservesFiniteColimits ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F) := hFc
  let : ∀ J : Type u, PreservesColimitsOfShape (Discrete J)
      ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F) := hFs
  let m := @Functor.LaxMonoidal.μ _ _ (FibredSite.monoidalCategoryQuasicoherentModules B S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) _ _ (quasicoherentModulesMonoidal B S hS 𝒳) _
      (@Functor.Monoidal.toLaxMonoidal _ _ _ _ _ _ _
        (quasicoherentModulesComparisonInverseMonoidal B S hS 𝒳))
      ((affineQuasicoherentPushforward g hg).obj N) (affineQuasicoherentStructureSheaf g hg)
  have e : m ≫ quasicoherentDirectImageAct g hg N = directImageActStrict g hg N :=
    ObjectProperty.hom_ext _ ((congrArg (· ≫ _)
      (quasicoherentModulesComparisonInverse_μ_hom _ _)).trans (Iso.inv_hom_id_assoc _ _))
  let w := (Functor.LaxMonoidal.μ F _ (affineQuasicoherentStructureSheaf g hg)).hom (z ⊗ₜ c)
  have key : (F.map (directImageActStrict g hg N)).hom w =
      ((directImageSMul g hg ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F) c).app
        N).hom z :=
    (map_hom_comp_apply_eq F e w).symm
  exact (congrArg ((localizedGlobalSectionsIso g hg F hU).hom.app N).hom key).trans
    (affineTensorFunctorGlobalSectionsIso_hom_app_directImageSMul g hg
      ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F) hU c N z)

/-- The lax structure `g_*P ⊗ g_*Q ⟶ g_*(P ⊗ Q)` of `g_{QCoh,*}` for the strict structure (II). -/
def quasicoherentDirectImageTensor
    (P Q : quasicoherentModules B S hS (schemeStack.{u, w} B S hS U)) :
    (affineQuasicoherentPushforward g hg).obj P ⊗ (affineQuasicoherentPushforward g hg).obj Q ⟶
      (affineQuasicoherentPushforward g hg).obj (P ⊗ Q) :=
  ObjectProperty.homMk (directImageTensor g hg P.obj Q.obj)

/-- `λ_{P,𝒪} ≫ g_*(ρ_P)` is the action of `g_*𝒪_U` on `g_*P`, in `QCoh(𝒪_𝒳)`. -/
theorem quasicoherentDirectImageTensor_comp_rightUnitor
    (P : quasicoherentModules B S hS (schemeStack.{u, w} B S hS U)) :
    quasicoherentDirectImageTensor g hg P (𝟙_ _) ≫
        (affineQuasicoherentPushforward g hg).map (ρ_ P).hom =
      directImageActStrict g hg P :=
  ObjectProperty.hom_ext _ (directImageTensor_comp_rightUnitor g hg P.obj)

/-- The lax structure of `g_{QCoh,*}` is natural in the right factor. -/
theorem quasicoherentDirectImageTensor_naturality_right
    (P : quasicoherentModules B S hS (schemeStack.{u, w} B S hS U))
    {Q Q' : quasicoherentModules B S hS (schemeStack.{u, w} B S hS U)} (f : Q ⟶ Q') :
    (affineQuasicoherentPushforward g hg).obj P ◁ (affineQuasicoherentPushforward g hg).map f ≫
        quasicoherentDirectImageTensor g hg P Q' =
      quasicoherentDirectImageTensor g hg P Q ≫ (affineQuasicoherentPushforward g hg).map (P ◁ f) :=
  ObjectProperty.hom_ext _ ((congrArg (· ≫ directImageTensor g hg P.obj Q'.obj)
    (MonoidalCategory.id_tensorHom _ _).symm).trans ((directImageTensor_naturality_right g hg P.obj
      f.hom).trans (congrArg (fun k => directImageTensor g hg P.obj Q.obj ≫
        (affinePushforward.{u, w, u} g hg).map k) (MonoidalCategory.id_tensorHom _ _))))

/-- The tensor comparison `Γ(U, P) ⊗_A Γ(U, Q) ⟶ Γ(U, P ⊗ Q)` of global sections: the
sheafification unit at the final object. -/
def globalSectionsTensor (P Q : quasicoherentModules B S hS (schemeStack.{u, w} B S hS U)) :
    (quasicoherentGlobalSections.{u, w} U).obj P ⊗ (quasicoherentGlobalSections.{u, w} U).obj Q ⟶
      (quasicoherentGlobalSections.{u, w} U).obj (P ⊗ Q) :=
  (Stacks.SheafOfModules.TensorSheafification.toSheafify
    (fppfStructurePresheaf B S hS (schemeStack.{u, w} B S hS U))
    (fppfStructurePresheaf_isSheaf B S hS (schemeStack.{u, w} B S hS U))
    (PresheafOfModulesOfCommRing.Monoidal.tensorObj P.obj.val Q.obj.val)).app (op (siteTop.{u, w} U))

/-- The tensor comparison of global sections is natural in the right factor. -/
theorem globalSectionsTensor_naturality_right
    (P : quasicoherentModules B S hS (schemeStack.{u, w} B S hS U))
    {Q Q' : quasicoherentModules B S hS (schemeStack.{u, w} B S hS U)} (f : Q ⟶ Q') :
    (quasicoherentGlobalSections.{u, w} U).obj P ◁ (quasicoherentGlobalSections.{u, w} U).map f ≫
        globalSectionsTensor P Q' =
      globalSectionsTensor P Q ≫ (quasicoherentGlobalSections.{u, w} U).map (P ◁ f) :=
  ModuleCat.MonoidalCategory.tensor_ext fun p q =>
    (Stacks.SheafOfModules.whiskerLeft_val_app_toSheafify_tmul
      (fppfStructurePresheaf B S hS (schemeStack.{u, w} B S hS U))
      (fppfStructurePresheaf_isSheaf B S hS (schemeStack.{u, w} B S hS U)) f.hom
      (op (siteTop.{u, w} U)) p q).symm

/-- `b ↦ κ'(F(λ)(μ(a ⊗ b)))`, natural in `Q`, for a fixed `a ∈ F(g_*P)`. -/
def localizedTensorLeft (P : quasicoherentModules B S hS (schemeStack.{u, w} B S hS U))
    (a : F.obj ((affineQuasicoherentPushforward g hg).obj P)) :
    affineQuasicoherentPushforward g hg ⋙ F ⟶
      MonoidalCategory.tensorLeft P ⋙ quasicoherentGlobalSections.{u, w} U ⋙
        ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF) ⋙
          ModuleCat.restrictScalars (algebraMap R (comparisonTensorAlgebra g hg F hF)) where
  app Q := ModuleCat.ofHom (TensorProduct.mk R _ _ a) ≫ Functor.LaxMonoidal.μ F _ _ ≫
    F.map (quasicoherentDirectImageTensor g hg P Q) ≫
      (localizedGlobalSectionsIso g hg F hU).hom.app (P ⊗ Q)
  naturality Q Q' f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun b => ?_)
    have h1 := congrArg (fun k => k.hom (a ⊗ₜ b)) (Functor.LaxMonoidal.μ_natural_right F
      ((affineQuasicoherentPushforward g hg).obj P) ((affineQuasicoherentPushforward g hg).map f))
    let w := (Functor.LaxMonoidal.μ F _ _).hom (a ⊗ₜ b)
    have h2 := (congrArg (fun k => ModuleCat.Hom.hom k w) (F.map_comp _ _)).symm.trans
      ((congrArg (fun k => (F.map k).hom w)
        (quasicoherentDirectImageTensor_naturality_right g hg P f)).trans
          (congrArg (fun k => ModuleCat.Hom.hom k w) (F.map_comp _ _)))
    have h3 := congrArg (fun k => k.hom ((F.map (quasicoherentDirectImageTensor g hg P Q)).hom w))
      ((localizedGlobalSectionsIso g hg F hU).hom.naturality (P ◁ f))
    exact (congrArg (fun z => ((localizedGlobalSectionsIso g hg F hU).hom.app (P ⊗ Q')).hom
      ((F.map (quasicoherentDirectImageTensor g hg P Q')).hom z)) h1).trans
        ((congrArg ((localizedGlobalSectionsIso g hg F hU).hom.app (P ⊗ Q')).hom h2).trans h3)

/-- `y ↦ (Γ μ)(μ(v ⊗ y))`: multiplication by a fixed `v ∈ Γ(U, P) ⊗_A C`, natural in `Q`. -/
def localizedTensorRight (P : quasicoherentModules B S hS (schemeStack.{u, w} B S hS U))
    (v : (ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).obj
      ((quasicoherentGlobalSections.{u, w} U).obj P)) :
    quasicoherentGlobalSections.{u, w} U ⋙
        ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF) ⋙
          ModuleCat.restrictScalars (algebraMap R (comparisonTensorAlgebra g hg F hF)) ⟶
      MonoidalCategory.tensorLeft P ⋙ quasicoherentGlobalSections.{u, w} U ⋙
        ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF) ⋙
          ModuleCat.restrictScalars (algebraMap R (comparisonTensorAlgebra g hg F hF)) where
  app Q := (ModuleCat.restrictScalars (algebraMap R (comparisonTensorAlgebra g hg F hF))).map
    (ModuleCat.ofHom (R := comparisonTensorAlgebra g hg F hF)
      (X := (ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).obj
          ((quasicoherentGlobalSections.{u, w} U).obj Q))
      (Y := TensorProduct (comparisonTensorAlgebra g hg F hF)
        ((ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).obj
          ((quasicoherentGlobalSections.{u, w} U).obj P))
        ((ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).obj
          ((quasicoherentGlobalSections.{u, w} U).obj Q)))
      (TensorProduct.mk _ _ _ v) ≫
      Functor.LaxMonoidal.μ (ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)) _ _ ≫
        (ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).map
          (globalSectionsTensor P Q))
  naturality Q Q' f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
    have h1 := congrArg (fun k => k.hom (v ⊗ₜ y)) (Functor.LaxMonoidal.μ_natural_right
      (ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF))
      ((quasicoherentGlobalSections.{u, w} U).obj P) ((quasicoherentGlobalSections.{u, w} U).map f))
    let x := (Functor.LaxMonoidal.μ (ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF))
      _ _).hom (v ⊗ₜ y)
    have h2 := (congrArg (fun k => ModuleCat.Hom.hom k x)
      ((ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).map_comp _ _)).symm.trans
      ((congrArg (fun k => ((ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).map
        k).hom x) (globalSectionsTensor_naturality_right P f)).trans
          (congrArg (fun k => ModuleCat.Hom.hom k x)
            ((ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).map_comp _ _)))
    exact (congrArg (fun z => ((ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).map
      (globalSectionsTensor P Q')).hom z) h1).trans h2

omit hFc hFs in
/-- After `Γ(U, ρ_P)`, multiplication by `c ⊗ 1 ∈ Γ(U, 𝒪_U) ⊗_A C` through the tensor comparisons
is the scalar action of `c`. -/
theorem extendScalars_map_rightUnitor_globalSectionsTensor_μ
    (P : quasicoherentModules B S hS (schemeStack.{u, w} B S hS U))
    (v : (ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).obj
      ((quasicoherentGlobalSections.{u, w} U).obj P))
    (c : comparisonTensorAlgebra g hg F hF) :
    ((ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).map
        ((quasicoherentGlobalSections.{u, w} U).map (ρ_ P).hom)).hom
      (((ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).map
        (globalSectionsTensor P (𝟙_ _))).hom
        ((Functor.LaxMonoidal.μ (ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF))
          ((quasicoherentGlobalSections.{u, w} U).obj P)
          ((quasicoherentGlobalSections.{u, w} U).obj (𝟙_ _))).hom
          (v ⊗ₜ ((ModuleCat.ExtendScalars.objSelfIso
            (comparisonTensorRingHom g hg F hF)).inv.hom c)))) = c • v := by
  let Y := (ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).obj
    ((quasicoherentGlobalSections.{u, w} U).obj (𝟙_ _))
  let w : Y := (ModuleCat.ExtendScalars.objSelfIso (comparisonTensorRingHom g hg F hF)).inv.hom c
  have H : ModuleCat.ofHom (R := comparisonTensorAlgebra g hg F hF)
        (X := (ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).obj
          ((quasicoherentGlobalSections.{u, w} U).obj P))
        (Y := TensorProduct (comparisonTensorAlgebra g hg F hF)
          ((ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).obj
            ((quasicoherentGlobalSections.{u, w} U).obj P))
          ((ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).obj
            ((quasicoherentGlobalSections.{u, w} U).obj (𝟙_ _))))
        ((TensorProduct.mk (comparisonTensorAlgebra g hg F hF)
          ((ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).obj
            ((quasicoherentGlobalSections.{u, w} U).obj P))
          ((ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).obj
            ((quasicoherentGlobalSections.{u, w} U).obj (𝟙_ _)))).flip w) ≫
      Functor.LaxMonoidal.μ (ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)) _ _ ≫
        (ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).map
          (globalSectionsTensor P (𝟙_ _)) ≫
        (ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).map
          ((quasicoherentGlobalSections.{u, w} U).map (ρ_ P).hom) =
      ModuleCat.ofHom (R := comparisonTensorAlgebra g hg F hF)
        (X := (ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).obj
          ((quasicoherentGlobalSections.{u, w} U).obj P))
        (Y := (ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).obj
          ((quasicoherentGlobalSections.{u, w} U).obj P)) (c • LinearMap.id) := by
    refine ModuleCat.ExtendScalars.hom_ext fun p => ?_
    have e1 : w = c • ((ModuleCat.ExtendScalars.objSelfIso
        (comparisonTensorRingHom g hg F hF)).inv.hom 1 : Y) :=
      (congrArg (ModuleCat.ExtendScalars.objSelfIso (comparisonTensorRingHom g hg F hF)).inv.hom
        (mul_one c).symm).trans (map_smul _ c 1)
    have e3 := Stacks.SheafOfModules.rightUnitor_hom_val_app_tmul
      (fppfStructurePresheaf B S hS (schemeStack.{u, w} B S hS U))
      (fppfStructurePresheaf_isSheaf B S hS (schemeStack.{u, w} B S hS U)) P.obj
      (op (siteTop.{u, w} U)) p 1
    let X := (ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).obj
      ((quasicoherentGlobalSections.{u, w} U).obj P)
    let i1 : Y := (ModuleCat.ExtendScalars.objSelfIso (comparisonTensorRingHom g hg F hF)).inv.hom 1
    let L₁ := (ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).map
      ((quasicoherentGlobalSections.{u, w} U).map (ρ_ P).hom)
    let L₂ := (ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).map
      (globalSectionsTensor P (𝟙_ _))
    let L₃ := Functor.LaxMonoidal.μ (ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF))
      ((quasicoherentGlobalSections.{u, w} U).obj P)
      ((quasicoherentGlobalSections.{u, w} U).obj (𝟙_ _))
    let i0 : (quasicoherentGlobalSections.{u, w} U).obj (𝟙_ _) := (1 : schemeGlobalRing U)
    let x : X := (1 : comparisonTensorAlgebra g hg F hF) ⊗ₜ[schemeGlobalRing U,
      comparisonTensorRingHom g hg F hF] p
    have s1 : (x ⊗ₜ w : TensorProduct (comparisonTensorAlgebra g hg F hF) X Y) = c • (x ⊗ₜ i1) :=
      (congrArg (x ⊗ₜ ·) e1).trans (TensorProduct.tmul_smul c x i1)
    have s2 : L₁.hom (L₂.hom (L₃.hom (c • (x ⊗ₜ i1)))) = c • L₁.hom (L₂.hom (L₃.hom (x ⊗ₜ i1))) :=
      (congrArg (fun z => L₁.hom (L₂.hom z)) (map_smul L₃.hom c _)).trans
        ((congrArg L₁.hom (map_smul L₂.hom c _)).trans (map_smul L₁.hom c _))
    have s3 : L₁.hom (L₂.hom (L₃.hom (x ⊗ₜ i1))) = x :=
      (congrArg (fun z => L₁.hom (L₂.hom (L₃.hom (x ⊗ₜ z))))
        (ModuleCat.ExtendScalars.objSelfIso_inv_apply (comparisonTensorRingHom g hg F hF) 1)).trans
        ((congrArg (fun z => L₁.hom (L₂.hom z)) (ModuleCat.extendScalars_μ_one_tmul_one_tmul
          (comparisonTensorRingHom g hg F hF) ((quasicoherentGlobalSections.{u, w} U).obj P)
          ((quasicoherentGlobalSections.{u, w} U).obj (𝟙_ _)) p i0)).trans
          (congrArg (fun z => ((1 : comparisonTensorAlgebra g hg F hF) ⊗ₜ[schemeGlobalRing U,
            comparisonTensorRingHom g hg F hF] z : X)) (e3.trans (one_smul _ _))))
    exact (congrArg (fun z => L₁.hom (L₂.hom (L₃.hom z))) s1).trans
      (s2.trans (congrArg (c • ·) s3))
  exact congrArg (fun k => ModuleCat.Hom.hom k v) H

/-- **The 0GRK isomorphism is lax monoidal** in the following sense: for `a ∈ F(g_*P)`,
`b ↦ κ'(F(λ)(μ(a ⊗ b)))` is `b ↦ (Γ μ)(μ(κ'(a) ⊗ κ'(b)))`, naturally in `Q`. Both sides are natural
transformations out of `Q ↦ F(g_*Q)`, which commutes with colimits on `Q = M~`, so they agree once
they agree on `𝒪_U` (`ModuleCat.natTrans_ext_of_app_self`); there both become the multiplication
by `c ∈ C` after `Γ(U, ρ_P)`, by the `C`-linearity of Stacks 0GRK. -/
theorem localizedTensorLeft_eq (P : quasicoherentModules B S hS (schemeStack.{u, w} B S hS U))
    (a : F.obj ((affineQuasicoherentPushforward g hg).obj P)) :
    localizedTensorLeft g hg F hU P a =
      (localizedGlobalSectionsIso g hg F hU).hom ≫
        localizedTensorRight g hg F P
          (((localizedGlobalSectionsIso g hg F hU).hom.app P).hom a) := by
  let := localizedBraided F hF
  let := additive_comparisonInverse_comp F
  let : PreservesFiniteColimits ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F) := hFc
  let : ∀ J : Type u, PreservesColimitsOfShape (Discrete J)
      ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F) := hFs
  have : PreservesColimitsOfSize.{u, u}
      (tildeQuasicoherent.{u, w} U ⋙ affineQuasicoherentPushforward g hg ⋙ F) :=
    preservesColimits_tildeQuasicoherent_comp_comp g hg
      ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F)
  have : PreservesColimitsOfSize.{0, 0}
      (tildeQuasicoherent.{u, w} U ⋙ affineQuasicoherentPushforward g hg ⋙ F) :=
    preservesColimitsOfSize_shrink.{0, u, 0, u} _
  let κ := (localizedGlobalSectionsIso g hg F hU).hom
  let α := localizedTensorLeft g hg F hU P a
  let β := κ ≫ localizedTensorRight g hg F P ((κ.app P).hom a)
  have h0 : α.app (𝟙_ _) = β.app (𝟙_ _) := by
    refine ModuleCat.hom_ext (LinearMap.ext fun c => ?_)
    refine (ConcreteCategory.bijective_of_isIso ((quasicoherentGlobalSections.{u, w} U ⋙
      ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF) ⋙
        ModuleCat.restrictScalars (algebraMap R (comparisonTensorAlgebra g hg F hF))).map
          (ρ_ P).hom)).1 ?_
    let w := (Functor.LaxMonoidal.μ F _ _).hom (a ⊗ₜ c)
    have n1 := congrArg (fun k => ModuleCat.Hom.hom k
      ((F.map (quasicoherentDirectImageTensor g hg P (𝟙_ _))).hom w)) (κ.naturality (ρ_ P).hom)
    have n2 : (F.map ((affineQuasicoherentPushforward g hg).map (ρ_ P).hom)).hom
        ((F.map (quasicoherentDirectImageTensor g hg P (𝟙_ _))).hom w) =
        (F.map (directImageActStrict g hg P)).hom w :=
      map_hom_comp_apply_eq F (quasicoherentDirectImageTensor_comp_rightUnitor g hg P) w
    have n3 := localizedGlobalSectionsIso_hom_app_map_directImageActStrict_μ g hg F hU c P a
    have n4 := affineTensorFunctorGlobalSectionsIso_hom_app_structureSheaf g hg
      ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F) hU c
    have n5 := extendScalars_map_rightUnitor_globalSectionsTensor_μ g hg F P ((κ.app P).hom a) c
    refine n1.symm.trans ((congrArg (κ.app P).hom n2).trans (n3.trans (n5.symm.trans ?_)))
    exact congrArg (fun z => ((ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).map
        ((quasicoherentGlobalSections.{u, w} U).map (ρ_ P).hom)).hom
      (((ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).map
        (globalSectionsTensor P (𝟙_ _))).hom
        ((Functor.LaxMonoidal.μ (ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF))
          ((quasicoherentGlobalSections.{u, w} U).obj P)
          ((quasicoherentGlobalSections.{u, w} U).obj (𝟙_ _))).hom
          (((κ.app P).hom a : (ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).obj
            ((quasicoherentGlobalSections.{u, w} U).obj P)) ⊗ₜ z)))) n4.symm
  have hw : Functor.whiskerLeft (tildeQuasicoherent.{u, w} U) α =
      Functor.whiskerLeft (tildeQuasicoherent.{u, w} U) β := by
    refine ModuleCat.natTrans_ext_of_app_self ?_
    let σ : (tildeQuasicoherent.{u, w} U).obj (ModuleCat.of _ (schemeGlobalRing U)) ≅
        𝟙_ (quasicoherentModules B S hS (schemeStack.{u, w} B S hS U)) :=
      tildeQuasicoherentSelfIso.{u, w} U
    exact (Iso.cancel_iso_hom_right _ _ ((MonoidalCategory.tensorLeft P ⋙
        quasicoherentGlobalSections.{u, w} U ⋙
        ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF) ⋙
          ModuleCat.restrictScalars (algebraMap R (comparisonTensorAlgebra g hg F hF))).mapIso
            σ)).1 ((α.naturality σ.hom).symm.trans
              ((congrArg (_ ≫ ·) h0).trans (β.naturality σ.hom)))
  refine NatTrans.ext (funext fun Q => ?_)
  let e : (tildeQuasicoherent.{u, w} U).obj ((quasicoherentGlobalSections.{u, w} U).obj Q) ≅ Q :=
    (tildeCounitIso.{u, w} U hU).app Q
  have hQ := congrArg (fun γ => γ.app ((quasicoherentGlobalSections.{u, w} U).obj Q)) hw
  exact (Iso.cancel_iso_hom_left ((affineQuasicoherentPushforward g hg ⋙ F).mapIso e) _ _).1
    ((α.naturality e.hom).trans ((congrArg (· ≫ _) hQ).trans (β.naturality e.hom).symm))

omit [CommRing R] in
/-- The tensor comparison `g^*X ⊗ g^*Y ⟶ g^*(X ⊗ Y)` in `QCoh(𝒪_U)` (strict structure (II)). -/
def quasicoherentPullbackTensor (X Y : quasicoherentModules B S hS 𝒳) :
    quasicoherentPullbackObj B S hS g X ⊗ quasicoherentPullbackObj B S hS g Y ⟶
      quasicoherentPullbackObj B S hS g (X ⊗ Y) :=
  ObjectProperty.homMk (pullbackTensor g X.obj Y.obj)

/-- **The unit `X ⟶ g_*g^*X` is compatible with the tensor products**, in `QCoh(𝒪_𝒳)`. -/
theorem affineQuasicoherentUnit_tensor (X Y : quasicoherentModules B S hS 𝒳) :
    affineQuasicoherentUnit g hg (X ⊗ Y) =
      (affineQuasicoherentUnit g hg X ⊗ₘ affineQuasicoherentUnit g hg Y) ≫
        quasicoherentDirectImageTensor g hg _ _ ≫
          (affineQuasicoherentPushforward g hg).map (quasicoherentPullbackTensor g X Y) :=
  ObjectProperty.hom_ext _ (unit_app_tensor g hg X.obj Y.obj)

omit hF hFa hFc hFs in
/-- **The identification `g(U)^* ≅ Γ(U, g^*(-))` is compatible with the tensor products.** -/
theorem pointPullbackChartIso_inv_μ (X Y : quasicoherentModules B S hS 𝒳) :
    ((pointPullbackChartIso g hU).inv.app X ⊗ₘ (pointPullbackChartIso g hU).inv.app Y) ≫
        Functor.LaxMonoidal.μ (pointPullback B S hS 𝒳 _ (chartPointIso g hU)) X Y =
      globalSectionsTensor _ _ ≫
        (quasicoherentGlobalSections.{u, w} U).map (quasicoherentPullbackTensor g X Y) ≫
          (pointPullbackChartIso g hU).inv.app (X ⊗ Y) :=
  ModuleCat.MonoidalCategory.tensor_ext fun a b =>
    (pointPullbackμ_tmul B S hS 𝒳 _ (chartPointIso g hU) X Y a b).trans
      (pullbackTensor_val_app_toSheafify g X.obj Y.obj (op (siteTop.{u, w} U)) a b).symm

/-- The comparison `F(-) ⊗_R C ⟶ Γ(U, g^*(-)) ⊗_A C` of Stacks 0GRQ, for `F` braided monoidal
for the strict structure (II). -/
def localizedPullbackTensorComparison :
    F ⋙ ModuleCat.extendScalars (algebraMap R (comparisonTensorAlgebra g hg F hF)) ⟶
      quasicoherentPullback B S hS g ⋙ quasicoherentGlobalSections.{u, w} U ⋙
        ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF) :=
  letI := localizedBraided F hF
  letI := additive_comparisonInverse_comp F
  letI : PreservesFiniteColimits ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F) := hFc
  letI : ∀ J : Type u, PreservesColimitsOfShape (Discrete J)
      ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F) := hFs
  pullbackTensorComparison g hg ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F) hU

/-- `localizedPullbackTensorComparison` sends `c ⊗ m` to `c • η(m)`, where `η(m)` is the image
of `m` under `F` of the unit `M ⟶ g_*g^*M` followed by `F(g_*g^*M) ≅ Γ(U, g^*M) ⊗_A C`. -/
theorem localizedPullbackTensorComparison_app_tmul (M : quasicoherentModules B S hS 𝒳)
    (c : comparisonTensorAlgebra g hg F hF) (m : F.obj M) :
    ((localizedPullbackTensorComparison g hg F hU).app M).hom
        (c ⊗ₜ[R, algebraMap R (comparisonTensorAlgebra g hg F hF)] m) =
      @HSMul.hSMul (comparisonTensorAlgebra g hg F hF)
        ((ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).obj
          ((quasicoherentGlobalSections.{u, w} U).obj (quasicoherentPullbackObj B S hS g M))) _
        instHSMul c (((localizedGlobalSectionsIso g hg F hU).hom.app
          (quasicoherentPullbackObj B S hS g M)).hom
            ((F.map (affineQuasicoherentUnit g hg M)).hom m)) :=
  rfl

/-- **The comparison of Stacks 0GRQ on `1 ⊗ μ(m ⊗ n)`**: it is the tensor product of the
comparisons on `1 ⊗ m` and `1 ⊗ n`, followed by the tensor comparisons of `Γ(U, -)` and `g^*`. -/
theorem localizedPullbackTensorComparison_app_one_tmul_μ (X Y : quasicoherentModules B S hS 𝒳)
    (m : F.obj X) (n : F.obj Y) :
    ((localizedPullbackTensorComparison g hg F hU).app (X ⊗ Y)).hom
        ((1 : comparisonTensorAlgebra g hg F hF) ⊗ₜ[R,
          algebraMap R (comparisonTensorAlgebra g hg F hF)]
          (Functor.LaxMonoidal.μ F X Y).hom (m ⊗ₜ n)) =
      ((ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).map
          (globalSectionsTensor _ _ ≫
            (quasicoherentGlobalSections.{u, w} U).map (quasicoherentPullbackTensor g X Y))).hom
        ((Functor.LaxMonoidal.μ (ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF))
          _ _).hom
          (((localizedPullbackTensorComparison g hg F hU).app X).hom
              ((1 : comparisonTensorAlgebra g hg F hF) ⊗ₜ[R,
                algebraMap R (comparisonTensorAlgebra g hg F hF)] m) ⊗ₜ
            ((localizedPullbackTensorComparison g hg F hU).app Y).hom
              ((1 : comparisonTensorAlgebra g hg F hF) ⊗ₜ[R,
                algebraMap R (comparisonTensorAlgebra g hg F hF)] n))) := by
  let κ := (localizedGlobalSectionsIso g hg F hU).hom
  let ηX := affineQuasicoherentUnit g hg X
  let ηY := affineQuasicoherentUnit g hg Y
  let w := (Functor.LaxMonoidal.μ F X Y).hom (m ⊗ₜ n)
  have sA : (F.map (affineQuasicoherentUnit g hg (X ⊗ Y))).hom w =
      (F.map ((affineQuasicoherentPushforward g hg).map (quasicoherentPullbackTensor g X Y))).hom
        ((F.map (quasicoherentDirectImageTensor g hg _ _)).hom ((F.map (ηX ⊗ₘ ηY)).hom w)) :=
    (map_hom_comp_apply_eq F (affineQuasicoherentUnit_tensor g hg X Y).symm w).symm.trans
      (map_hom_comp_apply_eq F rfl _).symm
  have sB : (F.map (ηX ⊗ₘ ηY)).hom w =
      (Functor.LaxMonoidal.μ F _ _).hom ((F.map ηX).hom m ⊗ₜ (F.map ηY).hom n) :=
    (congrArg (fun k => ModuleCat.Hom.hom k (m ⊗ₜ n))
      (Functor.LaxMonoidal.μ_natural F ηX ηY)).symm
  have sC := congrArg (fun k => ModuleCat.Hom.hom k ((F.map (quasicoherentDirectImageTensor g hg
      _ _)).hom ((Functor.LaxMonoidal.μ F _ _).hom ((F.map ηX).hom m ⊗ₜ (F.map ηY).hom n))))
    (κ.naturality (quasicoherentPullbackTensor g X Y))
  have sD := congrArg (fun α => ModuleCat.Hom.hom (α.app (quasicoherentPullbackObj B S hS g Y))
      ((F.map ηY).hom n))
    (localizedTensorLeft_eq g hg F hU (quasicoherentPullbackObj B S hS g X) ((F.map ηX).hom m))
  have sE := congrArg (fun k => ModuleCat.Hom.hom k
      ((Functor.LaxMonoidal.μ (ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)) _ _).hom
        (((κ.app (quasicoherentPullbackObj B S hS g X)).hom ((F.map ηX).hom m) :
          (ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).obj
            ((quasicoherentGlobalSections.{u, w} U).obj (quasicoherentPullbackObj B S hS g X))) ⊗ₜ
        ((κ.app (quasicoherentPullbackObj B S hS g Y)).hom ((F.map ηY).hom n) :
          (ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).obj
            ((quasicoherentGlobalSections.{u, w} U).obj (quasicoherentPullbackObj B S hS g Y))))))
    ((ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).map_comp
      (globalSectionsTensor _ _)
      ((quasicoherentGlobalSections.{u, w} U).map (quasicoherentPullbackTensor g X Y)))
  refine (localizedPullbackTensorComparison_app_tmul g hg F hU (X ⊗ Y) 1 w).trans ?_
  refine (one_smul _ _).trans ?_
  refine (congrArg (κ.app (quasicoherentPullbackObj B S hS g (X ⊗ Y))).hom (sA.trans
    (congrArg (fun z => (F.map ((affineQuasicoherentPushforward g hg).map
      (quasicoherentPullbackTensor g X Y))).hom ((F.map (quasicoherentDirectImageTensor g hg
        _ _)).hom z)) sB))).trans ?_
  refine sC.trans ?_
  refine (congrArg ((ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).map
    ((quasicoherentGlobalSections.{u, w} U).map (quasicoherentPullbackTensor g X Y))).hom
      sD).trans ?_
  refine sE.symm.trans ?_
  refine congrArg (fun z => ((ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)).map
    (globalSectionsTensor _ _ ≫ (quasicoherentGlobalSections.{u, w} U).map
      (quasicoherentPullbackTensor g X Y))).hom
        ((Functor.LaxMonoidal.μ (ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF))
          _ _).hom z)) ?_
  exact congrArg₂ (fun x y => x ⊗ₜ y)
    (localizedPullbackTensorComparison_app_tmul g hg F hU X 1 m ▸ (one_smul _ _).symm)
    (localizedPullbackTensorComparison_app_tmul g hg F hU Y 1 n ▸ (one_smul _ _).symm)

/-- **The comparison `F(-) ⊗_R C ≅ g(U)^*(-) ⊗_A C` of Stacks 0GRQ is an isomorphism of tensor
functors**, for `F` braided monoidal for the strict structure (II). -/
theorem isMonoidal_localizedPullbackTensorComparison_comp :
    NatTrans.IsMonoidal (localizedPullbackTensorComparison g hg F hU ≫
      Functor.whiskerRight (pointPullbackChartIso g hU).inv
        (ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF))) := by
  let := localizedBraided F hF
  let := additive_comparisonInverse_comp F
  let : PreservesFiniteColimits ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F) := hFc
  let : ∀ J : Type u, PreservesColimitsOfShape (Discrete J)
      ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F) := hFs
  have : IsIso (localizedPullbackTensorComparison g hg F hU) :=
    isIso_pullbackTensorComparison g hg ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F) hU
  refine NatTrans.isMonoidal_of_tensor _ fun X Y => ?_
  let ext := ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF)
  let τ := localizedPullbackTensorComparison g hg F hU ≫
    Functor.whiskerRight (pointPullbackChartIso g hU).inv ext
  let θ := localizedPullbackTensorComparison g hg F hU
  let iX := (pointPullbackChartIso g hU).inv.app X
  let iY := (pointPullbackChartIso g hU).inv.app Y
  let iXY := (pointPullbackChartIso g hU).inv.app (X ⊗ Y)
  let μu := Functor.LaxMonoidal.μ (pointPullback B S hS 𝒳 _ (chartPointIso g hU)) X Y
  let μΓ := globalSectionsTensor _ _ ≫
    (quasicoherentGlobalSections.{u, w} U).map (quasicoherentPullbackTensor g X Y)
  have key' : (ModuleCat.extendScalars (algebraMap R (comparisonTensorAlgebra g hg F hF))).map
        (Functor.LaxMonoidal.μ F X Y) ≫ θ.app (X ⊗ Y) =
      Functor.OplaxMonoidal.δ (ModuleCat.extendScalars
        (algebraMap R (comparisonTensorAlgebra g hg F hF))) (F.obj X) (F.obj Y) ≫
        (θ.app X ⊗ₘ θ.app Y) ≫ Functor.LaxMonoidal.μ ext _ _ ≫ ext.map μΓ :=
    ModuleCat.ExtendScalars.hom_ext_tmul fun m n =>
      localizedPullbackTensorComparison_app_one_tmul_μ g hg F hU X Y m n
  have e' : μΓ ≫ iXY = (iX ⊗ₘ iY) ≫ μu :=
    (Category.assoc _ _ _).trans (pointPullbackChartIso_inv_μ g hU X Y).symm
  have key : (ModuleCat.extendScalars (algebraMap R (comparisonTensorAlgebra g hg F hF))).map
        (Functor.LaxMonoidal.μ F X Y) ≫ τ.app (X ⊗ Y) =
      Functor.OplaxMonoidal.δ (ModuleCat.extendScalars
        (algebraMap R (comparisonTensorAlgebra g hg F hF))) (F.obj X) (F.obj Y) ≫
        (τ.app X ⊗ₘ τ.app Y) ≫
          Functor.LaxMonoidal.μ (pointPullback B S hS 𝒳 _ (chartPointIso g hU) ⋙ ext) X Y := by
    show _ ≫ θ.app (X ⊗ Y) ≫ ext.map iXY = _ ≫ ((θ.app X ≫ ext.map iX) ⊗ₘ
      (θ.app Y ≫ ext.map iY)) ≫ Functor.LaxMonoidal.μ ext _ _ ≫ ext.map μu
    rw [← Category.assoc, key', ← MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.assoc]
    rw [Functor.LaxMonoidal.μ_natural_assoc, ← Functor.map_comp, ← e']
    simp only [Category.assoc]
    exact (congrArg (fun k => _ ≫ _ ≫ _ ≫ k) (ext.map_comp μΓ iXY)).symm
  rw [Functor.LaxMonoidal.comp_μ, Category.assoc, key, Functor.Monoidal.μ_δ_assoc]

section Point

variable {y : 𝒳.val.val.obj}
  (ey : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y) ≅
    Spec (CommRingCat.of (comparisonTensorAlgebra g hg F hF)))
  (ψ : y ⟶ g.hom.hom.toFunctor.obj (siteTop.{u, w} U))
  (hψ : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map ψ) ≫ (chartPointIso g hU).hom =
    ey.hom ≫ Spec.map (CommRingCat.ofHom (comparisonTensorRingHom g hg F hF)))

/-- **`θ : F(-) ⊗_R C ≅ y^*`** of Stacks 0GRQ for `F` braided monoidal for the strict structure
(II): `AlgebraicGeometry.Stack.AlgebraicStacks.pointPullbackTensorIso` of `F` seen as a functor
out of the localized structure (I). -/
def localizedPointPullbackTensorIso :
    F ⋙ ModuleCat.extendScalars (algebraMap R (comparisonTensorAlgebra g hg F hF)) ≅
      pointPullback B S hS 𝒳 y ey :=
  letI := localizedBraided F hF
  letI := additive_comparisonInverse_comp F
  letI : PreservesFiniteColimits ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F) := hFc
  letI : ∀ J : Type u, PreservesColimitsOfShape (Discrete J)
      ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F) := hFs
  pointPullbackTensorIso g hg ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F) hU ey ψ hψ

/-- **`θ : F(-) ⊗_R C ≅ y^*` is an isomorphism of tensor functors** (Stacks 0GRQ, proof): the
comparison `F(-) ⊗_R C ≅ g(U)^*(-) ⊗_A C` is monoidal
(`AlgebraicGeometry.Stack.AlgebraicStacks.isMonoidal_localizedPullbackTensorComparison_comp`)
and so is the base change along `A ⟶ C`. -/
instance isMonoidal_localizedPointPullbackTensorIso :
    NatTrans.IsMonoidal (localizedPointPullbackTensorIso g hg F hU ey ψ hψ).hom := by
  haveI := isMonoidal_localizedPullbackTensorComparison_comp g hg F hU
  have e : (localizedPointPullbackTensorIso g hg F hU ey ψ hψ).hom =
      (localizedPullbackTensorComparison g hg F hU ≫
        Functor.whiskerRight (pointPullbackChartIso g hU).inv
          (ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF))) ≫
        (pointPullbackBaseChangeIso B S hS 𝒳 (comparisonTensorRingHom g hg F hF)
          (chartPointIso g hU) ey ψ hψ).hom :=
    (Category.assoc _ _ _).symm
  rw [e]
  infer_instance

end Point

end Localized

end AlgebraicGeometry.Stack.AlgebraicStacks
