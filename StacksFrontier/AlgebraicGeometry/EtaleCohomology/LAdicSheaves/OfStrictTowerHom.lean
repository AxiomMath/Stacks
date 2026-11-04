module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriek
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicCompactSupportFunctoriality

/-!
# Morphisms into the ℓ-adic sheaf of a strict tower

A morphism of ℓ-adic sheaves `F ⟶ G` ([Tag 03UM](https://stacks.math.columbia.edu/tag/03UM)) is a
compatible family of morphisms of the finite levels. The levels, read as sheaves of `ℤ_ℓ`-modules
on Mathlib's small étale site, form the tower `Stacks.EtaleCohomology.LAdicSheaf.padicTower`, and a
morphism of these towers is the same as a morphism of ℓ-adic sheaves: a `ℤ_ℓ`-linear map between
sheaves killed by `ℓⁿ⁺¹` is `ℤ/ℓⁿ⁺¹ℤ`-linear, and the equivalence of the two small étale sites is
fully faithful.

In particular a compatible map of towers `padicTower F ⟶ H` into a strict ℓ-adic tower `H` with
constructible levels gives a morphism into the ℓ-adic sheaf `LAdicSheaf.ofStrictTower H` of `H`,
and a map of towers into the stable image tower of `n ↦ R^r g_! G'ₙ` gives a morphism into the
ℓ-adic sheaf `R^r g_! G` (`Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriek`). This is how
maps into `R^r g_! G` (such as the Gysin map of the Leray step of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) are built.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.homOfPadicTower`: a morphism of towers of levels gives a
  morphism of ℓ-adic sheaves.
* `Stacks.EtaleCohomology.LAdicSheaf.ofStrictTowerHom`: a morphism into the ℓ-adic sheaf of a
  strict tower.
* `Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriekHom`: a morphism into `R^r g_! G`,
  from a map of towers into the stable image tower.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.LAdicTower
open AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize underlyingLevelFunctor_full

/-- Composing with the inverse of an isomorphism of functors and then its hom gives back the
component. -/
private theorem comp_inv_app_hom_app {C D : Type*} [Category C] [Category D] {F G K : C ⥤ D}
    (α : F ⟶ K) (e : G ≅ K) (X : C) : (α ≫ e.inv).app X ≫ e.hom.app X = α.app X := by
  simp

section Tower

variable {B : BigEtaleSite.{u}} {X : B.Scheme} {ℓ : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime]

attribute [local instance] strictTower_hasLimitsOfSize_moduleCat strictTower_hasSheafCompose_forget₂

/-- The underlying abelian sheaf of a morphism of levels read as sheaves of `ℤ_ℓ`-modules. -/
abbrev padicLevelUnderlyingMap {F G : LAdicSheaf.{u, u + 1} B X ℓ} (n : ℕ)
    (β : LAdicSheaf.padicLevel B X ℓ F n ⟶ LAdicSheaf.padicLevel B X ℓ G n) :
    (underlyingLevelFunctor B X ℓ n).obj (F.level n) ⟶
      (underlyingLevelFunctor B X ℓ n).obj (G.level n) :=
  (sheafCompose (SmallEtale.topology B X.1 X.property)
    (forget₂ (ModuleCat.{u + 1} ℤ_[ℓ]) AddCommGrpCat.{u + 1})).map β

/-- The component at level `n` of a morphism of towers of levels, between the levels read on
Mathlib's small étale site. -/
abbrev LAdicSheaf.padicTowerApp {F G : LAdicSheaf.{u, u + 1} B X ℓ}
    (γ : LAdicSheaf.padicTower B X ℓ F ⟶ LAdicSheaf.padicTower B X ℓ G) (n : ℕ) :
    (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.obj
        (LAdicSheaf.padicLevel B X ℓ F n) ⟶
      (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.obj
        (LAdicSheaf.padicLevel B X ℓ G n) :=
  γ.app (op n)

/-- The level-`n` component of `Stacks.EtaleCohomology.LAdicSheaf.homOfPadicTower`: the
`ℤ_ℓ`-linear map of levels, which is `ℤ/ℓⁿ⁺¹ℤ`-linear. -/
def LAdicSheaf.homOfPadicTowerApp {F G : LAdicSheaf.{u, u + 1} B X ℓ}
    (γ : LAdicSheaf.padicTower B X ℓ F ⟶ LAdicSheaf.padicTower B X ℓ G) (n : ℕ) :
    F.level n ⟶ G.level n :=
  (underlyingLevelFunctor B X ℓ n).preimage (padicLevelUnderlyingMap n
    ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.preimage
      (LAdicSheaf.padicTowerApp γ n)))

/-- The underlying abelian map of `Stacks.EtaleCohomology.LAdicSheaf.homOfPadicTowerApp γ n` is
the underlying abelian map of the component of `γ` at level `n`. -/
theorem LAdicSheaf.underlyingLevelFunctor_map_homOfPadicTowerApp
    {F G : LAdicSheaf.{u, u + 1} B X ℓ}
    (γ : LAdicSheaf.padicTower B X ℓ F ⟶ LAdicSheaf.padicTower B X ℓ G) (n : ℕ) :
    (underlyingLevelFunctor B X ℓ n).map (LAdicSheaf.homOfPadicTowerApp γ n) =
      padicLevelUnderlyingMap n
        ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.preimage
          (LAdicSheaf.padicTowerApp γ n)) :=
  (underlyingLevelFunctor B X ℓ n).map_preimage _

/-- The underlying abelian map of the transition of an ℓ-adic sheaf, read on the `ℤ_ℓ`-levels. -/
theorem LAdicSheaf.padicLevelUnderlyingMap_padicTransition (F : LAdicSheaf.{u, u + 1} B X ℓ)
    (n : ℕ) :
    (sheafCompose (SmallEtale.topology B X.1 X.property)
        (forget₂ (ModuleCat.{u + 1} ℤ_[ℓ]) AddCommGrpCat.{u + 1})).map
        (LAdicSheaf.padicTransition B X ℓ F n) =
      (underlyingLevelFunctor B X ℓ (n + 1)).map (F.transition n) := by
  ext U x
  rfl

/-- **A morphism of the towers of levels is a morphism of ℓ-adic sheaves.** -/
def LAdicSheaf.homOfPadicTower {F G : LAdicSheaf.{u, u + 1} B X ℓ}
    (γ : LAdicSheaf.padicTower B X ℓ F ⟶ LAdicSheaf.padicTower B X ℓ G) : F ⟶ G where
  app := LAdicSheaf.homOfPadicTowerApp γ
  naturality n := by
    let e := SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])
    let Φ := sheafCompose (SmallEtale.topology B X.1 X.property)
      (forget₂ (ModuleCat.{u + 1} ℤ_[ℓ]) AddCommGrpCat.{u + 1})
    have h : e.functor.map (LAdicSheaf.padicTransition B X ℓ F n) ≫
        LAdicSheaf.padicTowerApp γ n =
        LAdicSheaf.padicTowerApp γ (n + 1) ≫
          e.functor.map (LAdicSheaf.padicTransition B X ℓ G n) := by
      have h' := γ.naturality (homOfLE (n.le_add_right 1)).op
      rwa [LAdicSheaf.padicTower_map_succ, LAdicSheaf.padicTower_map_succ] at h'
    have hγ : LAdicSheaf.padicTransition B X ℓ F n ≫ e.functor.preimage
        (LAdicSheaf.padicTowerApp γ n) =
        e.functor.preimage (LAdicSheaf.padicTowerApp γ (n + 1)) ≫
          LAdicSheaf.padicTransition B X ℓ G n := by
      apply e.functor.map_injective
      simpa only [Functor.map_comp, Functor.map_preimage] using h
    apply (underlyingLevelFunctor B X ℓ (n + 1)).map_injective
    rw [Functor.map_comp, Functor.map_comp, underlyingLevelFunctor_restrict_map,
      LAdicSheaf.underlyingLevelFunctor_map_homOfPadicTowerApp,
      LAdicSheaf.underlyingLevelFunctor_map_homOfPadicTowerApp,
      ← LAdicSheaf.padicLevelUnderlyingMap_padicTransition,
      ← LAdicSheaf.padicLevelUnderlyingMap_padicTransition]
    change Φ.map _ ≫ Φ.map _ = Φ.map _ ≫ Φ.map _
    rw [← Φ.map_comp, ← Φ.map_comp, hγ]

/-- The level maps of `Stacks.EtaleCohomology.LAdicSheaf.homOfPadicTower γ`, read on the tower of
levels, are the components of `γ`. -/
theorem LAdicSheaf.sheafEquiv_map_padicLevelMap_homOfPadicTower {F G : LAdicSheaf.{u, u + 1} B X ℓ}
    (γ : LAdicSheaf.padicTower B X ℓ F ⟶ LAdicSheaf.padicTower B X ℓ G) (n : ℕ) :
    (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
        (LAdicSheaf.padicLevelMap (LAdicSheaf.homOfPadicTower γ) n) =
      LAdicSheaf.padicTowerApp γ n := by
  have h : LAdicSheaf.padicLevelMap (LAdicSheaf.homOfPadicTower γ) n =
      (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.preimage
        (LAdicSheaf.padicTowerApp γ n) := by
    ext U x
    exact ConcreteCategory.congr_hom (congrArg (fun t => t.hom.app U)
      (LAdicSheaf.underlyingLevelFunctor_map_homOfPadicTowerApp γ n))
      (show ((underlyingLevelFunctor B X ℓ n).obj (F.level n)).obj.obj U from x)
  rw [h, Functor.map_preimage]

variable (H : ℕᵒᵖ ⥤ EtaleModules.{u, 0} ℤ_[ℓ] X.1) (hH : IsStrict H ℓ)
  (hc : ∀ n, IsConstructibleModuleSheaf B X (ZMod (ℓ ^ (n + 1))) (strictTowerLevel H hH n))

/-- **A compatible map of towers into a strict tower `H` gives a morphism into the ℓ-adic sheaf
of `H`.** -/
def LAdicSheaf.ofStrictTowerHom {F : LAdicSheaf.{u, u + 1} B X ℓ}
    (α : LAdicSheaf.padicTower B X ℓ F ⟶ H) : F ⟶ LAdicSheaf.ofStrictTower H hH hc :=
  LAdicSheaf.homOfPadicTower (α ≫ (LAdicSheaf.padicTowerOfStrictTowerIso H hH hc).inv)

/-- The morphism into the ℓ-adic sheaf of a strict tower, read on the towers of levels, is the
given map of towers. -/
theorem LAdicSheaf.sheafEquiv_map_padicLevelMap_ofStrictTowerHom
    {F : LAdicSheaf.{u, u + 1} B X ℓ} (α : LAdicSheaf.padicTower B X ℓ F ⟶ H) (n : ℕ) :
    (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
        (LAdicSheaf.padicLevelMap (LAdicSheaf.ofStrictTowerHom H hH hc α) n) ≫
      (LAdicSheaf.padicTowerOfStrictTowerIso H hH hc).hom.app (op n) = α.app (op n) := by
  rw [LAdicSheaf.ofStrictTowerHom, LAdicSheaf.sheafEquiv_map_padicLevelMap_homOfPadicTower]
  exact comp_inv_app_hom_app α _ _

end Tower

section HigherDirectImageShriek

attribute [local instance] HasDerivedCategory.standard

variable {B : BigEtaleSite.{u}} {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {U W : B.Scheme} [IsNoetherian U.1] [IsNoetherian W.1] (g : U ⟶ W)
  (jg : CompactificationOf (Over.mk (B.inclusion.map g)))

/-- **A map of towers into the stable images of `n ↦ R^r g_! G'ₙ` gives a morphism into the
ℓ-adic sheaf `R^r g_! G`**, under the hypotheses
`Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageShriekCondition` defining it. -/
def LAdicSheaf.higherDirectImageShriekHom (G : LAdicSheaf.{u, u + 1} B U ℓ) (r : ℕ)
    (h : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g jg G r)
    {F : LAdicSheaf.{u, u + 1} B W ℓ}
    (α : haveI := h.fst
      LAdicSheaf.padicTower B W ℓ F ⟶
        (LAdicSheaf.lowerShriekTowerLES B ℓ g jg G r).stableImageTower) :
    F ⟶ LAdicSheaf.higherDirectImageShriek B ℓ g jg G r :=
  haveI := h.fst
  LAdicSheaf.homOfPadicTower
    (α ≫ (LAdicSheaf.padicTowerHigherDirectImageShriekIso B ℓ g jg G r h).inv)

/-- The morphism into `R^r g_! G`, read on the towers of levels, is the given map of towers. -/
theorem LAdicSheaf.sheafEquiv_map_padicLevelMap_higherDirectImageShriekHom
    (G : LAdicSheaf.{u, u + 1} B U ℓ) (r : ℕ)
    (h : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g jg G r)
    {F : LAdicSheaf.{u, u + 1} B W ℓ}
    (α : haveI := h.fst
      LAdicSheaf.padicTower B W ℓ F ⟶
        (LAdicSheaf.lowerShriekTowerLES B ℓ g jg G r).stableImageTower)
    (n : ℕ) :
    haveI := h.fst
    (SmallEtale.sheafEquiv B W.1 W.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
        (LAdicSheaf.padicLevelMap (LAdicSheaf.higherDirectImageShriekHom g jg G r h α) n) ≫
      (LAdicSheaf.padicTowerHigherDirectImageShriekIso B ℓ g jg G r h).hom.app (op n) =
      α.app (op n) := by
  have := h.fst
  rw [LAdicSheaf.higherDirectImageShriekHom,
    LAdicSheaf.sheafEquiv_map_padicLevelMap_homOfPadicTower]
  exact comp_inv_app_hom_app α _ _

end HigherDirectImageShriek

end Stacks.EtaleCohomology
