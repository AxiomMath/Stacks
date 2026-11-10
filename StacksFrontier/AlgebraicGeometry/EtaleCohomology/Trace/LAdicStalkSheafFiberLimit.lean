module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DirectImageLevelStalkBridge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriekEnd

/-!
# The ℓ-adic stalk inside the limit of the stalks of the levels on Mathlib's site

Let `M` be an ℓ-adic sheaf on `X` and `s̄` a geometric point. The finite-level stalk `(Mₙ)_s̄` on
the bounded small étale site of Stacks 021B, read as a `ℤ_ℓ`-module, is the stalk at `s̄` on
Mathlib's small étale site of the `n`-th level of `M` as a sheaf of `ℤ_ℓ`-modules
(`Stacks.EtaleCohomology.padicLevelStalkFiberMap`), compatibly with the transition maps, with the
morphisms of ℓ-adic sheaves and with the endomorphisms of `s̄`. Hence the ℓ-adic stalk `M_s̄` maps
injectively into the limit of `n ↦ (Mₙ)_s̄` on Mathlib's site
(`Stacks.EtaleCohomology.LAdicSheaf.stalkSheafFiberLimitMap`), naturally and equivariantly.

## Main definitions

* `Stacks.EtaleCohomology.padicLevelStalkFiberMap`
* `Stacks.EtaleCohomology.LAdicSheaf.stalkSheafFiberLimitMap`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.SmallEtale
open AlgebraicGeometry.SmallEtale.LAdicSheaf

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable {B : BigEtaleSite.{u}} {X : B.Scheme} (s : GeometricPoint X.1) {ℓ : ℕ}
  [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.obj]

/-- **The level-`n` stalk on the two small étale sites**: the stalk `(Mₙ)_s̄` on the bounded site,
read as a `ℤ_ℓ`-module, is the stalk on Mathlib's site of `Mₙ` as a sheaf of `ℤ_ℓ`-modules. -/
def padicLevelStalkFiberIso (M : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    (ModuleCat.restrictScalars.{u + 1} (PadicInt.toZModPow (p := ℓ) (n + 1))).obj
        (finiteLevelStalk B X ℓ M s n) ≅
      (Scheme.pointSmallEtale s.hom).sheafFiber.obj
        ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} ℤ_[ℓ])).functor.obj
          (LAdicSheaf.padicLevel B X ℓ M n)) :=
  preservesColimitIso (ModuleCat.restrictScalars.{u + 1} (PadicInt.toZModPow (p := ℓ) (n + 1)))
      ((Functor.Elements.π (geometricPointFiber B X.1 X.2 s)).op ⋙ (M.level n).obj) ≪≫
    ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X ℤ_[ℓ] s).app
      (LAdicSheaf.padicLevel B X ℓ M n)).symm

/-- The level-`n` stalk comparison as a morphism. -/
abbrev padicLevelStalkFiberMap (M : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :=
  (padicLevelStalkFiberIso s M n).hom

/-- The level stalk map on germs. -/
theorem padicLevelStalkFiberMap_germ (M : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ)
    (j : (geometricPointFiber B X.1 X.2 s).Elementsᵒᵖ)
    (x : (M.level n).obj.obj ((Functor.Elements.π (geometricPointFiber B X.1 X.2 s)).op.obj j)) :
    (padicLevelStalkFiberMap s M n).hom
        ((colimit.ι ((Functor.Elements.π (geometricPointFiber B X.1 X.2 s)).op ⋙
          (M.level n).obj) j).hom x) =
      ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X ℤ_[ℓ] s).inv.app
          (LAdicSheaf.padicLevel B X ℓ M n)).hom
        ((colimit.ι ((Functor.Elements.π (geometricPointFiber B X.1 X.2 s)).op ⋙
          (LAdicSheaf.padicLevel B X ℓ M n).obj) j).hom x) :=
  congrArg ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X ℤ_[ℓ] s).inv.app
      (LAdicSheaf.padicLevel B X ℓ M n)).hom
    (ConcreteCategory.congr_hom (ι_preservesColimitIso_hom
      (ModuleCat.restrictScalars.{u + 1} (PadicInt.toZModPow (p := ℓ) (n + 1)))
      ((Functor.Elements.π (geometricPointFiber B X.1 X.2 s)).op ⋙ (M.level n).obj) j) x)

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.obj] in
/-- The comparison of stalk functors is natural, on germs. -/
theorem sheafEquivCompSheafFiberIso_inv_germ_naturality
    {F₁ F₂ : Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} ℤ_[ℓ])} (g : F₁ ⟶ F₂)
    (j : (geometricPointFiber B X.1 X.2 s).Elementsᵒᵖ)
    (y : F₁.obj.obj ((Functor.Elements.π (geometricPointFiber B X.1 X.2 s)).op.obj j)) :
    ((Scheme.pointSmallEtale s.hom).sheafFiber.map
        ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map g)).hom
        (((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X ℤ_[ℓ] s).inv.app F₁).hom
          ((colimit.ι ((Functor.Elements.π (geometricPointFiber B X.1 X.2 s)).op ⋙
            F₁.obj) j).hom y)) =
      ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X ℤ_[ℓ] s).inv.app F₂).hom
        ((colimit.ι ((Functor.Elements.π (geometricPointFiber B X.1 X.2 s)).op ⋙ F₂.obj) j).hom
          ((g.hom.app ((Functor.Elements.π (geometricPointFiber B X.1 X.2 s)).op.obj j)).hom
            y)) := by
  have h := ConcreteCategory.congr_hom
    ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X ℤ_[ℓ] s).inv.naturality g)
    ((colimit.ι ((Functor.Elements.π (geometricPointFiber B X.1 X.2 s)).op ⋙ F₁.obj) j).hom y)
  have h2 := ConcreteCategory.congr_hom (colimit.ι_map (Functor.whiskerLeft
    ((Functor.Elements.π (geometricPointFiber B X.1 X.2 s)).op) g.hom) j) y
  exact h.symm.trans (congrArg ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X ℤ_[ℓ] s).inv.app
    F₂).hom h2)

/-- Two composites out of an étale stalk agree if they agree on all germs. -/
private theorem etaleStalk_comp_apply_eq {Y : B.Scheme} (s : GeometricPoint Y.1) {R : Type} [Ring R]
    (P : (SmallEtale B Y.1 Y.2)ᵒᵖ ⥤ ModuleCat.{u + 1} R) {A D E : Type (u + 1)} [AddCommGroup A]
    [AddCommGroup D] [AddCommGroup E] {F₁ F₂ G₁ G₂ : Type*}
    [FunLike F₁ (etaleStalk B Y.1 Y.2 s P : ModuleCat.{u + 1} R) A]
    [AddMonoidHomClass F₁ (etaleStalk B Y.1 Y.2 s P : ModuleCat.{u + 1} R) A]
    [FunLike F₂ A E] [AddMonoidHomClass F₂ A E]
    [FunLike G₁ (etaleStalk B Y.1 Y.2 s P : ModuleCat.{u + 1} R) D]
    [AddMonoidHomClass G₁ (etaleStalk B Y.1 Y.2 s P : ModuleCat.{u + 1} R) D]
    [FunLike G₂ D E] [AddMonoidHomClass G₂ D E] (f₁ : F₁) (f₂ : F₂) (g₁ : G₁) (g₂ : G₂)
    (h : ∀ (j : (geometricPointFiber B Y.1 Y.2 s).Elementsᵒᵖ)
      (x : P.obj ((Functor.Elements.π (geometricPointFiber B Y.1 Y.2 s)).op.obj j)),
      f₂ (f₁ ((colimit.ι ((Functor.Elements.π (geometricPointFiber B Y.1 Y.2 s)).op ⋙ P) j).hom
        x)) = g₂ (g₁ ((colimit.ι ((Functor.Elements.π (geometricPointFiber B Y.1 Y.2 s)).op ⋙
          P) j).hom x)))
    (w : (etaleStalk B Y.1 Y.2 s P : ModuleCat.{u + 1} R)) : f₂ (f₁ w) = g₂ (g₁ w) :=
  DFunLike.congr_fun (etaleStalk_addMonoidHom_ext Y.1 Y.2 s P
    (g₁ := (f₂ : A →+ E).comp (f₁ : _ →+ A)) (g₂ := (g₂ : D →+ E).comp (g₁ : _ →+ D)) h) w

/-- The level stalk comparison intertwines a map of the levels, on germs. -/
private theorem padicLevelStalkFiberMap_germ_naturality {M₁ M₂ : LAdicSheaf.{u, u + 1} B X ℓ}
    {n₁ n₂ : ℕ} (g : LAdicSheaf.padicLevel B X ℓ M₁ n₁ ⟶ LAdicSheaf.padicLevel B X ℓ M₂ n₂)
    (j : (geometricPointFiber B X.1 X.2 s).Elementsᵒᵖ)
    (x : (M₁.level n₁).obj.obj ((Functor.Elements.π (geometricPointFiber B X.1 X.2 s)).op.obj j))
    (y : (M₂.level n₂).obj.obj ((Functor.Elements.π (geometricPointFiber B X.1 X.2 s)).op.obj j))
    (hy : (g.hom.app ((Functor.Elements.π (geometricPointFiber B X.1 X.2 s)).op.obj j)).hom x =
      y) :
    (padicLevelStalkFiberMap s M₂ n₂).hom
        ((colimit.ι ((Functor.Elements.π (geometricPointFiber B X.1 X.2 s)).op ⋙
          (M₂.level n₂).obj) j).hom y) =
      ((Scheme.pointSmallEtale s.hom).sheafFiber.map
        ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map g)).hom
        ((padicLevelStalkFiberMap s M₁ n₁).hom
          ((colimit.ι ((Functor.Elements.π (geometricPointFiber B X.1 X.2 s)).op ⋙
            (M₁.level n₁).obj) j).hom x)) := by
  subst hy
  exact (padicLevelStalkFiberMap_germ s M₂ n₂ j _).trans
    ((sheafEquivCompSheafFiberIso_inv_germ_naturality s g j x).symm.trans
      (congrArg _ (padicLevelStalkFiberMap_germ s M₁ n₁ j x).symm))

/-- **The level stalk comparison commutes with the transition maps.** -/
theorem padicLevelStalkFiberMap_transition (M : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ)
    (w : finiteLevelStalk B X ℓ M s (n + 1)) :
    (padicLevelStalkFiberMap s M n).hom (LAdicSheaf.stalkTransition B X ℓ M s n w) =
      ((Scheme.pointSmallEtale s.hom).sheafFiber.map
        ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
          (LAdicSheaf.padicTransition B X ℓ M n))).hom
        ((padicLevelStalkFiberMap s M (n + 1)).hom w) :=
  etaleStalk_comp_apply_eq s (M.level (n + 1)).obj _ _ _ _
    (fun j x => (congrArg _ (stalkTransition_germ s M n j x)).trans
      (padicLevelStalkFiberMap_germ_naturality s (LAdicSheaf.padicTransition B X ℓ M n) j x _ rfl))
    w

/-- **The level stalk comparison is natural in the ℓ-adic sheaf.** -/
theorem padicLevelStalkFiberMap_stalkMap {M M' : LAdicSheaf.{u, u + 1} B X ℓ} (ψ : M ⟶ M')
    (n : ℕ) (w : finiteLevelStalk B X ℓ M s n) :
    (padicLevelStalkFiberMap s M' n).hom ((finiteLevelStalkMap ψ s n).hom w) =
      ((Scheme.pointSmallEtale s.hom).sheafFiber.map
        ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
          (LAdicSheaf.padicLevelMap ψ n))).hom ((padicLevelStalkFiberMap s M n).hom w) :=
  etaleStalk_comp_apply_eq s (M.level n).obj _ _ _ _
    (fun j x => (congrArg _ (ConcreteCategory.congr_hom (colimit.ι_map (Functor.whiskerLeft
        ((Functor.Elements.π (geometricPointFiber B X.1 X.2 s)).op) (ψ.app n).hom) j) x)).trans
      (padicLevelStalkFiberMap_germ_naturality s (LAdicSheaf.padicLevelMap ψ n) j x _ rfl))
    w

/-- **The level stalk comparison commutes with the endomorphisms of the geometric point.** -/
theorem padicLevelStalkFiberMap_stalkEnd (M : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ)
    (a : GeometricPoint.Hom s s) (w : finiteLevelStalk B X ℓ M s n) :
    (padicLevelStalkFiberMap s M n).hom ((finiteLevelStalkEnd B X ℓ M a n).hom w) =
      ((GrothendieckTopology.Point.Hom.sheafFiber (smallEtalePointHom X.1 a)).app
        ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} ℤ_[ℓ])).functor.obj
          (LAdicSheaf.padicLevel B X ℓ M n))).hom ((padicLevelStalkFiberMap s M n).hom w) := by
  let T := (GrothendieckTopology.Point.Hom.sheafFiber (smallEtalePointHom X.1 a)).app
    ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} ℤ_[ℓ])).functor.obj
      (LAdicSheaf.padicLevel B X ℓ M n))
  let Sinv := (sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X ℤ_[ℓ] s).inv.app
    (LAdicSheaf.padicLevel B X ℓ M n)
  have hb := NatTrans.congr_app
    (sheafEquivCompSheafFiberIso_inv_naturality.{u, u + 1, 0} B X ℤ_[ℓ] a)
    (LAdicSheaf.padicLevel B X ℓ M n)
  exact etaleStalk_comp_apply_eq s (M.level n).obj _ _ _ _
    (fun j x => by
      have hpre := ConcreteCategory.congr_hom (colimit.ι_pre
        ((Functor.Elements.π (geometricPointFiber B X.1 X.2 s)).op ⋙ (M.level n).obj)
        (neighborhoodFunctor B X.1 X.2 a).op j) x
      have hpre' := ConcreteCategory.congr_hom (colimit.ι_pre
        ((Functor.Elements.π (geometricPointFiber B X.1 X.2 s)).op ⋙
          (LAdicSheaf.padicLevel B X ℓ M n).obj)
        (neighborhoodFunctor B X.1 X.2 a).op j) x
      have hb' := ConcreteCategory.congr_hom hb
        ((colimit.ι ((Functor.Elements.π (geometricPointFiber B X.1 X.2 s)).op ⋙
          (LAdicSheaf.padicLevel B X ℓ M n).obj) j).hom x)
      exact (congrArg _ hpre).trans
        ((padicLevelStalkFiberMap_germ s M n ((neighborhoodFunctor B X.1 X.2 a).op.obj j) x).trans
        ((congrArg Sinv.hom hpre').symm.trans
        (hb'.symm.trans (congrArg T.hom (padicLevelStalkFiberMap_germ s M n j x).symm)))))
    w

/-! ### The ℓ-adic stalk in the limit -/

/-- The cone over `n ↦ (Mₙ)_s̄` on Mathlib's site given by the ℓ-adic stalk. -/
def LAdicSheaf.stalkSheafFiberCone (M : LAdicSheaf.{u, u + 1} B X ℓ) :
    Cone (LAdicSheaf.padicTower B X ℓ M ⋙ (Scheme.pointSmallEtale s.hom).sheafFiber) where
  pt := ModuleCat.of ℤ_[ℓ] (LAdicSheaf.stalk B X ℓ M s)
  π := NatTrans.ofOpSequence
    (fun n => ModuleCat.ofHom (((padicLevelStalkFiberMap s M n).hom).comp
      (LAdicSheaf.stalkProjection B X ℓ M s n)))
    (fun n => by
      refine ModuleCat.hom_ext (LinearMap.ext fun v => ?_)
      change (padicLevelStalkFiberMap s M n).hom (v.1 n) =
        ((Scheme.pointSmallEtale s.hom).sheafFiber.map ((LAdicSheaf.padicTower B X ℓ M).map
          (homOfLE (n.le_add_right 1)).op)).hom
          ((padicLevelStalkFiberMap s M (n + 1)).hom (v.1 (n + 1)))
      rw [LAdicSheaf.padicTower_map_succ]
      exact (congrArg (padicLevelStalkFiberMap s M n).hom (v.2 n)).symm.trans
        (padicLevelStalkFiberMap_transition s M n (v.1 (n + 1))))

/-- **The ℓ-adic stalk maps into the limit of the stalks of the levels on Mathlib's site.** -/
def LAdicSheaf.stalkSheafFiberLimitMap (M : LAdicSheaf.{u, u + 1} B X ℓ) :
    ModuleCat.of ℤ_[ℓ] (LAdicSheaf.stalk B X ℓ M s) ⟶
      limit (LAdicSheaf.padicTower B X ℓ M ⋙ (Scheme.pointSmallEtale s.hom).sheafFiber) :=
  limit.lift _ (LAdicSheaf.stalkSheafFiberCone s M)

/-- The `n`-th component of the image of `v` in the limit is the image of the level-`n`
component of `v` under `padicLevelStalkFiberMap`. -/
theorem LAdicSheaf.stalkSheafFiberLimitMap_π (M : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ)
    (v : LAdicSheaf.stalk B X ℓ M s) :
    (limit.π (LAdicSheaf.padicTower B X ℓ M ⋙ (Scheme.pointSmallEtale s.hom).sheafFiber)
        (op n)).hom ((LAdicSheaf.stalkSheafFiberLimitMap s M).hom v) =
      (padicLevelStalkFiberMap s M n).hom (v.1 n) :=
  ConcreteCategory.congr_hom (limit.lift_π (LAdicSheaf.stalkSheafFiberCone s M) (op n)) v

/-- The map from the ℓ-adic stalk into the limit of the stalks of the levels is injective. -/
theorem LAdicSheaf.injective_stalkSheafFiberLimitMap (M : LAdicSheaf.{u, u + 1} B X ℓ) :
    Function.Injective (LAdicSheaf.stalkSheafFiberLimitMap s M).hom := by
  intro v v' h
  refine Subtype.ext (funext fun n => ?_)
  have h' := congrArg (limit.π (LAdicSheaf.padicTower B X ℓ M ⋙
    (Scheme.pointSmallEtale s.hom).sheafFiber) (op n)).hom h
  rw [LAdicSheaf.stalkSheafFiberLimitMap_π, LAdicSheaf.stalkSheafFiberLimitMap_π] at h'
  exact (ConcreteCategory.bijective_of_isIso (padicLevelStalkFiberMap s M n)).1 h'

/-- **The map into the limit carries an endomorphism of the geometric point to the induced map
of stalk functors.** -/
theorem LAdicSheaf.stalkSheafFiberLimitMap_stalkEnd (M : LAdicSheaf.{u, u + 1} B X ℓ)
    (a : GeometricPoint.Hom s s) :
    ModuleCat.ofHom (LAdicSheaf.stalkEnd B X ℓ M a) ≫ LAdicSheaf.stalkSheafFiberLimitMap s M =
      LAdicSheaf.stalkSheafFiberLimitMap s M ≫ limMap (Functor.whiskerLeft
        (LAdicSheaf.padicTower B X ℓ M)
        (GrothendieckTopology.Point.Hom.sheafFiber (A := ModuleCat.{u + 1} ℤ_[ℓ])
          (smallEtalePointHom X.1 a))) := by
  refine limit.hom_ext fun n => ?_
  induction n using Opposite.rec with
  | op n =>
    refine ModuleCat.hom_ext (LinearMap.ext fun v => ?_)
    have h := ConcreteCategory.congr_hom (limMap_π (Functor.whiskerLeft
      (LAdicSheaf.padicTower B X ℓ M)
      (GrothendieckTopology.Point.Hom.sheafFiber (A := ModuleCat.{u + 1} ℤ_[ℓ])
        (smallEtalePointHom X.1 a))) (op n)) ((LAdicSheaf.stalkSheafFiberLimitMap s M).hom v)
    exact (LAdicSheaf.stalkSheafFiberLimitMap_π s M n _).trans
      ((padicLevelStalkFiberMap_stalkEnd s M n a (v.1 n)).trans
        ((congrArg _ (LAdicSheaf.stalkSheafFiberLimitMap_π s M n v)).symm.trans h.symm))

/-- **The map into the limit is natural in the ℓ-adic sheaf.** -/
theorem LAdicSheaf.stalkSheafFiberLimitMap_stalkMap {M M' : LAdicSheaf.{u, u + 1} B X ℓ}
    (ψ : M ⟶ M') :
    ModuleCat.ofHom (LAdicSheaf.stalkMap ψ s) ≫ LAdicSheaf.stalkSheafFiberLimitMap s M' =
      LAdicSheaf.stalkSheafFiberLimitMap s M ≫ limMap (Functor.whiskerRight
        (LAdicSheaf.padicTowerMap ψ) (Scheme.pointSmallEtale s.hom).sheafFiber) := by
  refine limit.hom_ext fun n => ?_
  induction n using Opposite.rec with
  | op n =>
    refine ModuleCat.hom_ext (LinearMap.ext fun v => ?_)
    have h := ConcreteCategory.congr_hom (limMap_π (Functor.whiskerRight
      (LAdicSheaf.padicTowerMap ψ) (Scheme.pointSmallEtale s.hom).sheafFiber) (op n))
      ((LAdicSheaf.stalkSheafFiberLimitMap s M).hom v)
    exact (LAdicSheaf.stalkSheafFiberLimitMap_π s M' n _).trans
      ((padicLevelStalkFiberMap_stalkMap s ψ n (v.1 n)).trans
        ((congrArg _ (LAdicSheaf.stalkSheafFiberLimitMap_π s M n v)).symm.trans h.symm))

end Stacks.EtaleCohomology
