module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.OfStrictTowerHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicCoefficientExtension

/-!
# Functoriality of `Rʳ g_! G` in the endomorphisms of `G`

An endomorphism `φ` of an ℓ-adic sheaf `G` induces an endomorphism of its torsion-free model
`G' = ℓᴺ G` (`Stacks.EtaleCohomology.LAdicSheaf.torsionFreeModelMap`), hence of the tower
`n ↦ Rʳ g_! G'ₙ`, of its stable images, and of the ℓ-adic sheaf `Rʳ g_! G`
(`Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriek`). This gives a ring homomorphism
`End G →+* End (Rʳ g_! G)` (`Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriekEndRingHom`),
described levelwise by `Rʳ g_!(φ'ₙ)` on the stable images
(`Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriekEnd_padicLevelMap`), and the
coefficient sheaf `Rʳ g_! F` of a coefficient sheaf `F`. This is the action of the coefficients
on the higher direct images in the Leray step of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.LAdicTower
open AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

section TorsionFreeModel

variable {B : BigEtaleSite.{u}} {X : B.Scheme} {ℓ : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [Fact ℓ.Prime] [IsNoetherian X.1]

attribute [local instance] underlyingLevelFunctor_additive
  underlyingLevelFunctor_preservesMonomorphisms underlyingLevelFunctor_full

namespace LAdicSheaf

/-- A morphism `F ⟶ F'` kills the kernel of `ℓᴺ` on `F_{N+n}` after `ℓᴺ` on `F'_{N+n}`. -/
theorem torsionFreeModelMap_kernel_condition {F F' : LAdicSheaf.{u, u + 1} B X ℓ} (φ : F ⟶ F')
    (N n : ℕ) :
    kernel.ι (torsionFreeModelπ F N n) ≫
      (underlyingLevelFunctor B X ℓ (N + n)).map (φ.app (N + n)) ≫ torsionFreeModelπ F' N n =
        0 := by
  rw [← cancel_mono (torsionFreeModelι F' N n), Category.assoc, Category.assoc,
    torsionFreeModelπ_ι, zero_comp, Preadditive.comp_nsmul, Category.comp_id,
    ← Category.id_comp ((underlyingLevelFunctor B X ℓ (N + n)).map (φ.app (N + n))),
    ← Preadditive.nsmul_comp, ← torsionFreeModelπ_ι_assoc, kernel.condition_assoc, zero_comp]

/-- The map `ℓᴺ F_{N+n} ⟶ ℓᴺ F'_{N+n}` of the underlying sheaves induced by `F ⟶ F'`. -/
def torsionFreeModelUnderlyingMap {F F' : LAdicSheaf.{u, u + 1} B X ℓ} (φ : F ⟶ F') (N n : ℕ) :
    (underlyingLevelFunctor B X ℓ n).obj (torsionFreeModelLevel F N n) ⟶
      (underlyingLevelFunctor B X ℓ n).obj (torsionFreeModelLevel F' N n) :=
  Abelian.epiDesc (torsionFreeModelπ F N n)
    ((underlyingLevelFunctor B X ℓ (N + n)).map (φ.app (N + n)) ≫ torsionFreeModelπ F' N n)
    (torsionFreeModelMap_kernel_condition φ N n)

/-- The projection `F_{N+n} ⟶ ℓᴺ F_{N+n}` intertwines `φ` with the induced underlying map. -/
@[reassoc]
theorem torsionFreeModelπ_underlyingMap {F F' : LAdicSheaf.{u, u + 1} B X ℓ} (φ : F ⟶ F')
    (N n : ℕ) :
    torsionFreeModelπ F N n ≫ torsionFreeModelUnderlyingMap φ N n =
      (underlyingLevelFunctor B X ℓ (N + n)).map (φ.app (N + n)) ≫ torsionFreeModelπ F' N n :=
  Abelian.comp_epiDesc _ _ _

/-- The underlying maps commute with the transitions of `ℓᴺ F` and `ℓᴺ F'`. -/
theorem torsionFreeModelUnderlyingMap_transition {F F' : LAdicSheaf.{u, u + 1} B X ℓ}
    (φ : F ⟶ F') (N n : ℕ) :
    torsionFreeModelUnderlyingMap φ N (n + 1) ≫ torsionFreeModelUnderlyingTransition F' N n =
      torsionFreeModelUnderlyingTransition F N n ≫ torsionFreeModelUnderlyingMap φ N n := by
  refine (cancel_epi (torsionFreeModelπ F N (n + 1))).1 ?_
  rw [torsionFreeModelπ_underlyingMap_assoc, torsionFreeModelπ_underlyingTransition,
    torsionFreeModelπ_underlyingTransition_assoc, torsionFreeModelπ_underlyingMap,
    ← Category.assoc, ← Category.assoc]
  congr 1
  have h := congrArg (underlyingLevelFunctor B X ℓ (N + n + 1)).map (φ.naturality (N + n))
  rw [Functor.map_comp, Functor.map_comp, underlyingLevelFunctor_restrict_map] at h
  exact h

/-- **The morphism `ℓᴺ F ⟶ ℓᴺ F'` of torsion-free models induced by `F ⟶ F'`.** -/
def torsionFreeModelMap {F F' : LAdicSheaf.{u, u + 1} B X ℓ} (φ : F ⟶ F') (N : ℕ) :
    torsionFreeModel F N ⟶ torsionFreeModel F' N where
  app n := (underlyingLevelFunctor B X ℓ n).preimage (X := (torsionFreeModel F N).level n)
    (Y := (torsionFreeModel F' N).level n) (torsionFreeModelUnderlyingMap φ N n)
  naturality n := by
    apply (underlyingLevelFunctor B X ℓ (n + 1)).map_injective
    have key := torsionFreeModelUnderlyingMap_transition φ N n
    rw [← underlyingLevelFunctor_map_torsionFreeModelTransition F' N n,
      ← underlyingLevelFunctor_map_torsionFreeModelTransition F N n,
      ← (underlyingLevelFunctor B X ℓ (n + 1)).map_preimage
        (torsionFreeModelUnderlyingMap φ N (n + 1)),
      ← (underlyingLevelFunctor B X ℓ n).map_preimage (torsionFreeModelUnderlyingMap φ N n)] at key
    rw [Functor.map_comp, Functor.map_comp, underlyingLevelFunctor_restrict_map]
    exact key

/-- The underlying map of the `n`-th component of `torsionFreeModelMap φ N` is
`torsionFreeModelUnderlyingMap φ N n`. -/
theorem underlyingLevelFunctor_map_torsionFreeModelMap {F F' : LAdicSheaf.{u, u + 1} B X ℓ}
    (φ : F ⟶ F') (N n : ℕ) :
    (underlyingLevelFunctor B X ℓ n).map ((torsionFreeModelMap φ N).app n) =
      torsionFreeModelUnderlyingMap φ N n :=
  (underlyingLevelFunctor B X ℓ n).map_preimage _

/-- The projection `F_{N+n} ⟶ ℓᴺ F_{N+n}` intertwines `φ` with the `n`-th component of
`torsionFreeModelMap φ N`. -/
@[reassoc]
theorem torsionFreeModelπ_map_app {F F' : LAdicSheaf.{u, u + 1} B X ℓ} (φ : F ⟶ F') (N n : ℕ) :
    torsionFreeModelπ F N n ≫
        (underlyingLevelFunctor B X ℓ n).map ((torsionFreeModelMap φ N).app n) =
      (underlyingLevelFunctor B X ℓ (N + n)).map (φ.app (N + n)) ≫ torsionFreeModelπ F' N n :=
  (congrArg (torsionFreeModelπ F N n ≫ ·)
      (underlyingLevelFunctor_map_torsionFreeModelMap φ N n)).trans
    (torsionFreeModelπ_underlyingMap φ N n)

/-- Morphisms out of `ℓᴺ F` are determined by their composites with `F_{N+n} ⟶ ℓᴺ F_{N+n}`. -/
theorem torsionFreeModel_hom_ext {F F' : LAdicSheaf.{u, u + 1} B X ℓ} {N : ℕ}
    {f f' : torsionFreeModel F N ⟶ torsionFreeModel F' N}
    (h : ∀ n, torsionFreeModelπ F N n ≫ (underlyingLevelFunctor B X ℓ n).map (f.app n) =
      torsionFreeModelπ F N n ≫ (underlyingLevelFunctor B X ℓ n).map (f'.app n)) : f = f' :=
  LAdicSheaf.Hom.ext _ _ _ fun n =>
    (underlyingLevelFunctor B X ℓ n).map_injective ((cancel_epi (torsionFreeModelπ F N n)).1 (h n))

/-- The identity of `F` induces the identity of `ℓᴺ F`. -/
theorem torsionFreeModelMap_id (F : LAdicSheaf.{u, u + 1} B X ℓ) (N : ℕ) :
    torsionFreeModelMap (𝟙 F) N = 𝟙 _ :=
  torsionFreeModel_hom_ext fun n => by
    rw [torsionFreeModelπ_map_app]
    show (underlyingLevelFunctor B X ℓ (N + n)).map (𝟙 _) ≫ _ =
      _ ≫ (underlyingLevelFunctor B X ℓ n).map (𝟙 _)
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
      Category.comp_id]

/-- The morphism of torsion-free models induced by a composite is the composite. -/
theorem torsionFreeModelMap_comp {F F' F'' : LAdicSheaf.{u, u + 1} B X ℓ} (φ : F ⟶ F')
    (ψ : F' ⟶ F'') (N : ℕ) :
    torsionFreeModelMap (φ ≫ ψ) N = torsionFreeModelMap φ N ≫ torsionFreeModelMap ψ N :=
  torsionFreeModel_hom_ext fun n =>
    (torsionFreeModelπ_map_app (φ ≫ ψ) N n).trans <|
      ((congrArg (· ≫ torsionFreeModelπ F'' N n)
          ((underlyingLevelFunctor B X ℓ (N + n)).map_comp (φ.app (N + n)) (ψ.app (N + n)))).trans
          (Category.assoc _ _ _)).trans <|
      (congrArg ((underlyingLevelFunctor B X ℓ (N + n)).map (φ.app (N + n)) ≫ ·)
          (torsionFreeModelπ_map_app ψ N n).symm).trans <|
      ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ (underlyingLevelFunctor B X ℓ n).map ((torsionFreeModelMap ψ N).app n))
            (torsionFreeModelπ_map_app φ N n).symm)).trans <|
      (Category.assoc _ _ _).trans (congrArg (torsionFreeModelπ F N n ≫ ·)
          ((underlyingLevelFunctor B X ℓ n).map_comp _ _).symm)

/-- The morphism of torsion-free models induced by a sum is the sum. -/
theorem torsionFreeModelMap_add {F F' : LAdicSheaf.{u, u + 1} B X ℓ} (φ ψ : F ⟶ F') (N : ℕ) :
    torsionFreeModelMap (φ + ψ) N = torsionFreeModelMap φ N + torsionFreeModelMap ψ N :=
  torsionFreeModel_hom_ext fun n =>
    (torsionFreeModelπ_map_app (φ + ψ) N n).trans <|
      (congrArg (· ≫ torsionFreeModelπ F' N n)
          ((underlyingLevelFunctor B X ℓ (N + n)).map_add (f := φ.app (N + n))
            (g := ψ.app (N + n)))).trans <|
      (Preadditive.add_comp _ _ _ _ _ _).trans <|
      (congrArg₂ (· + ·) (torsionFreeModelπ_map_app φ N n).symm
        (torsionFreeModelπ_map_app ψ N n).symm).trans <|
        (Preadditive.comp_add _ _ _ _ _ _).symm.trans (congrArg (torsionFreeModelπ F N n ≫ ·)
          ((underlyingLevelFunctor B X ℓ n).map_add).symm)

end LAdicSheaf

end TorsionFreeModel

/-! ### Morphisms of towers of levels -/

section PadicTower

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

attribute [local instance] moduleCat_hasLimitsOfSize underlyingLevelFunctor_full

/-- The morphism of towers of levels induced by a morphism of ℓ-adic sheaves. -/
def LAdicSheaf.padicTowerMap {F G : LAdicSheaf.{u, u + 1} B X ℓ} (φ : F ⟶ G) :
    LAdicSheaf.padicTower B X ℓ F ⟶ LAdicSheaf.padicTower B X ℓ G :=
  NatTrans.ofOpSequence
    (fun n => (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
      (LAdicSheaf.padicLevelMap φ n))
    (fun n => by
      have h := congrArg
        (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
        (LAdicSheaf.padicLevelMap_padicTransition φ n)
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at h
      rw [LAdicSheaf.padicTower_map_succ, LAdicSheaf.padicTower_map_succ]
      exact h.symm)

/-- The component at `n` of `padicTowerMap φ` is the image of the level map of `φ` at `n`. -/
theorem LAdicSheaf.padicTowerApp_padicTowerMap {F G : LAdicSheaf.{u, u + 1} B X ℓ} (φ : F ⟶ G)
    (n : ℕ) :
    LAdicSheaf.padicTowerApp (LAdicSheaf.padicTowerMap φ) n =
      (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
        (LAdicSheaf.padicLevelMap φ n) :=
  rfl

/-- The identity of `F` induces the identity of its tower of levels. -/
theorem LAdicSheaf.padicTowerMap_id (F : LAdicSheaf.{u, u + 1} B X ℓ) :
    LAdicSheaf.padicTowerMap (𝟙 F) = 𝟙 _ := by
  refine NatTrans.ext (funext fun n => ?_)
  exact (congrArg (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
    (LAdicSheaf.padicLevelMap_id F n.unop)).trans (CategoryTheory.Functor.map_id _ _)

/-- The morphism of towers of levels induced by a composite is the composite. -/
theorem LAdicSheaf.padicTowerMap_comp {F G H : LAdicSheaf.{u, u + 1} B X ℓ} (φ : F ⟶ G)
    (ψ : G ⟶ H) :
    LAdicSheaf.padicTowerMap (φ ≫ ψ) = LAdicSheaf.padicTowerMap φ ≫ LAdicSheaf.padicTowerMap ψ := by
  refine NatTrans.ext (funext fun n => ?_)
  exact (congrArg (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
    (LAdicSheaf.padicLevelMap_comp φ ψ n.unop)).trans (CategoryTheory.Functor.map_comp _ _ _)

/-- The morphism of towers of levels induced by a sum is the sum. -/
theorem LAdicSheaf.padicTowerMap_add {F G : LAdicSheaf.{u, u + 1} B X ℓ} (φ ψ : F ⟶ G) :
    LAdicSheaf.padicTowerMap (φ + ψ) = LAdicSheaf.padicTowerMap φ + LAdicSheaf.padicTowerMap ψ := by
  have := Equivalence.additive_functor'
    (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ]))
  refine NatTrans.ext (funext fun n => ?_)
  exact (congrArg (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
    (LAdicSheaf.padicLevelMap_add φ ψ n.unop)).trans (CategoryTheory.Functor.map_add _)

/-- A morphism of ℓ-adic sheaves is determined by its level maps. -/
theorem LAdicSheaf.hom_ext_of_padicLevelMap {F G : LAdicSheaf.{u, u + 1} B X ℓ} {φ ψ : F ⟶ G}
    (h : ∀ n, LAdicSheaf.padicLevelMap φ n = LAdicSheaf.padicLevelMap ψ n) : φ = ψ :=
  LAdicSheaf.Hom.ext _ _ _ fun n => (underlyingLevelFunctor B X ℓ n).map_injective (by
    ext U x
    exact ConcreteCategory.congr_hom (congrArg (fun t => t.hom.app U) (h n))
      (show (LAdicSheaf.padicLevel B X ℓ F n).obj.obj U from x))

/-- Morphisms of ℓ-adic sheaves are equal when their level maps agree after `sheafEquiv`. -/
private theorem hom_ext_of_sheafEquiv_map_padicLevelMap {F G : LAdicSheaf.{u, u + 1} B X ℓ}
    {φ ψ : F ⟶ G}
    (h : ∀ n, (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
      (LAdicSheaf.padicLevelMap φ n) =
      (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
        (LAdicSheaf.padicLevelMap ψ n)) : φ = ψ :=
  LAdicSheaf.hom_ext_of_padicLevelMap fun n =>
    (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map_injective (h n)

/-- The level map at `n` of the morphism induced by a morphism of towers `γ` is the preimage of
the component of `γ` at `n`. -/
theorem LAdicSheaf.padicLevelMap_homOfPadicTower {F G : LAdicSheaf.{u, u + 1} B X ℓ}
    (γ : LAdicSheaf.padicTower B X ℓ F ⟶ LAdicSheaf.padicTower B X ℓ G) (n : ℕ) :
    LAdicSheaf.padicLevelMap (LAdicSheaf.homOfPadicTower γ) n =
      (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.preimage
        (LAdicSheaf.padicTowerApp γ n) :=
  (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map_injective (by
    rw [Functor.map_preimage, LAdicSheaf.sheafEquiv_map_padicLevelMap_homOfPadicTower])

/-- The morphism of ℓ-adic sheaves induced by a composite of morphisms of towers is the
composite. -/
theorem LAdicSheaf.homOfPadicTower_comp {F G H : LAdicSheaf.{u, u + 1} B X ℓ}
    (γ : LAdicSheaf.padicTower B X ℓ F ⟶ LAdicSheaf.padicTower B X ℓ G)
    (γ' : LAdicSheaf.padicTower B X ℓ G ⟶ LAdicSheaf.padicTower B X ℓ H) :
    LAdicSheaf.homOfPadicTower (γ ≫ γ') =
      LAdicSheaf.homOfPadicTower γ ≫ LAdicSheaf.homOfPadicTower γ' :=
  hom_ext_of_sheafEquiv_map_padicLevelMap fun n => by
    rw [LAdicSheaf.padicLevelMap_comp, CategoryTheory.Functor.map_comp,
      LAdicSheaf.sheafEquiv_map_padicLevelMap_homOfPadicTower,
      LAdicSheaf.sheafEquiv_map_padicLevelMap_homOfPadicTower,
      LAdicSheaf.sheafEquiv_map_padicLevelMap_homOfPadicTower]
    rfl

/-- The identity of the tower of levels of `F` induces the identity of `F`. -/
theorem LAdicSheaf.homOfPadicTower_id (F : LAdicSheaf.{u, u + 1} B X ℓ) :
    LAdicSheaf.homOfPadicTower (𝟙 (LAdicSheaf.padicTower B X ℓ F)) = 𝟙 F :=
  hom_ext_of_sheafEquiv_map_padicLevelMap fun n => by
    rw [LAdicSheaf.sheafEquiv_map_padicLevelMap_homOfPadicTower, LAdicSheaf.padicLevelMap_id,
      CategoryTheory.Functor.map_id]
    rfl

/-- The morphism of ℓ-adic sheaves induced by a sum of morphisms of towers is the sum. -/
theorem LAdicSheaf.homOfPadicTower_add {F G : LAdicSheaf.{u, u + 1} B X ℓ}
    (γ γ' : LAdicSheaf.padicTower B X ℓ F ⟶ LAdicSheaf.padicTower B X ℓ G) :
    LAdicSheaf.homOfPadicTower (γ + γ') =
      LAdicSheaf.homOfPadicTower γ + LAdicSheaf.homOfPadicTower γ' := by
  have := Equivalence.additive_functor'
    (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ]))
  refine hom_ext_of_sheafEquiv_map_padicLevelMap fun n => ?_
  rw [LAdicSheaf.padicLevelMap_add, CategoryTheory.Functor.map_add,
    LAdicSheaf.sheafEquiv_map_padicLevelMap_homOfPadicTower,
    LAdicSheaf.sheafEquiv_map_padicLevelMap_homOfPadicTower,
    LAdicSheaf.sheafEquiv_map_padicLevelMap_homOfPadicTower]
  rfl

end PadicTower

/-! ### Endomorphisms of the stable image tower -/

section StableImage

variable {C : Type*} [Category* C] [Abelian C] {T S : ℕᵒᵖ ⥤ C} {ℓ : ℕ}
  (D : LESData T S ℓ) [IsNoetherianObject (towerObj S 0)]

/-- The component at `n` of the endomorphism of the stable images induced by `α : T ⟶ T`. -/
def _root_.CategoryTheory.LAdicTower.LESData.stableImageMapApp (α : T ⟶ T) (n : ℕ) :
    D.stableImageTower.obj (op n) ⟶ D.stableImageTower.obj (op n) :=
  imageSubobjectMap (Arrow.homMk (α.app (op (n + D.shift + 1))) (α.app (op n))
    (α.naturality _).symm :
      Arrow.mk (towerMap T (show n ≤ n + D.shift + 1 by omega)) ⟶
        Arrow.mk (towerMap T (show n ≤ n + D.shift + 1 by omega)))

/-- The component `stableImageMapApp α n` commutes with the inclusion of the stable image into
`T(n)` and `α`. -/
@[reassoc]
theorem _root_.CategoryTheory.LAdicTower.LESData.stableImageMapApp_ι (α : T ⟶ T) (n : ℕ) :
    D.stableImageMapApp α n ≫ D.stableImageι.app (op n) =
      D.stableImageι.app (op n) ≫ α.app (op n) :=
  imageSubobjectMap_arrow _

/-- An endomorphism of the tower `T` restricts to its stable images. -/
def _root_.CategoryTheory.LAdicTower.LESData.stableImageMap (α : T ⟶ T) :
    D.stableImageTower ⟶ D.stableImageTower :=
  NatTrans.ofOpSequence (D.stableImageMapApp α) (fun n => by
    have hι := D.stableImageι.naturality (homOfLE (n.le_add_right 1)).op
    have hα := α.naturality (homOfLE (n.le_add_right 1)).op
    refine (cancel_mono (D.stableImageι.app (op n))).1 ?_
    simp only [Category.assoc, D.stableImageMapApp_ι, D.stableImageMapApp_ι_assoc,
      hι, reassoc_of% hι, hα])

/-- The endomorphism `stableImageMap α` commutes with the inclusion of the stable images and
`α`. -/
@[reassoc (attr := simp)]
theorem _root_.CategoryTheory.LAdicTower.LESData.stableImageMap_ι (α : T ⟶ T) :
    D.stableImageMap α ≫ D.stableImageι = D.stableImageι ≫ α := by
  ext n
  exact D.stableImageMapApp_ι α n.unop

/-- Endomorphisms of the stable image tower are determined by their composites with the inclusion
into `T`. -/
theorem _root_.CategoryTheory.LAdicTower.LESData.stableImageMap_ext
    {β β' : D.stableImageTower ⟶ D.stableImageTower}
    (h : β ≫ D.stableImageι = β' ≫ D.stableImageι) : β = β' := by
  ext n
  exact (cancel_mono (D.stableImageι.app (op n.unop))).1
    (congrArg (fun t => NatTrans.app t (op n.unop)) h)

/-- The identity of `T` restricts to the identity of the stable images. -/
theorem _root_.CategoryTheory.LAdicTower.LESData.stableImageMap_id :
    D.stableImageMap (𝟙 T) = 𝟙 _ :=
  D.stableImageMap_ext (by simp)

/-- The restriction to the stable images of a composite is the composite of the restrictions. -/
theorem _root_.CategoryTheory.LAdicTower.LESData.stableImageMap_comp (α α' : T ⟶ T) :
    D.stableImageMap (α ≫ α') = D.stableImageMap α ≫ D.stableImageMap α' :=
  D.stableImageMap_ext (by simp)

/-- The restriction to the stable images of a sum is the sum of the restrictions. -/
theorem _root_.CategoryTheory.LAdicTower.LESData.stableImageMap_add (α α' : T ⟶ T) :
    D.stableImageMap (α + α') = D.stableImageMap α + D.stableImageMap α' :=
  D.stableImageMap_ext (by simp [Preadditive.add_comp, Preadditive.comp_add])

/-- The zero endomorphism of `T` restricts to the zero endomorphism of the stable images. -/
theorem _root_.CategoryTheory.LAdicTower.LESData.stableImageMap_zero :
    D.stableImageMap (0 : T ⟶ T) = 0 :=
  D.stableImageMap_ext (by simp)

end StableImage

/-! ### The endomorphisms of `Rʳ g_! G` -/

section HigherDirectImage

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
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

/-- The endomorphism of the tower `n ↦ Rʳ g_! G'ₙ` induced by an endomorphism `φ` of `G`, through
the induced endomorphism `φ'` of the flat model. -/
def LAdicSheaf.lowerShriekTowerEnd (G : LAdicSheaf B U ℓ) (r : ℤ) (φ : G ⟶ G) :
    LAdicSheaf.lowerShriekTower B ℓ g jg G r ⟶ LAdicSheaf.lowerShriekTower B ℓ g jg G r :=
  Functor.whiskerRight (LAdicSheaf.padicTowerMap
      (LAdicSheaf.torsionFreeModelMap φ (LAdicSheaf.torsionBound G)))
    (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r)

open Classical in
/-- **The endomorphism of `Rʳ g_! G` induced by an endomorphism `φ` of `G`**: on the levels, the
endomorphism of the stable images induced by `Rʳ g_!(φ'ₙ)`; `0` when `Rʳ g_! G` is `0`. -/
def LAdicSheaf.higherDirectImageShriekEnd (G : LAdicSheaf B U ℓ) (r : ℕ) (φ : G ⟶ G) :
    LAdicSheaf.higherDirectImageShriek B ℓ g jg G r ⟶
      LAdicSheaf.higherDirectImageShriek B ℓ g jg G r :=
  if h : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g jg G r then
    haveI := h.fst
    LAdicSheaf.homOfPadicTower
      ((LAdicSheaf.padicTowerHigherDirectImageShriekIso B ℓ g jg G r h).hom ≫
      (LAdicSheaf.lowerShriekTowerLES B ℓ g jg G r).stableImageMap
        (LAdicSheaf.lowerShriekTowerEnd B ℓ g jg G r φ) ≫
      (LAdicSheaf.padicTowerHigherDirectImageShriekIso B ℓ g jg G r h).inv)
  else 0

omit [AlgebraicGeometry.IsNoetherian W.1] in
/-- The identity of `G` induces the identity of the tower `n ↦ Rʳ g_! G'ₙ`. -/
theorem LAdicSheaf.lowerShriekTowerEnd_id (G : LAdicSheaf B U ℓ) (r : ℤ) :
    LAdicSheaf.lowerShriekTowerEnd B ℓ g jg G r (𝟙 G) = 𝟙 _ := by
  unfold LAdicSheaf.lowerShriekTowerEnd
  rw [LAdicSheaf.torsionFreeModelMap_id, LAdicSheaf.padicTowerMap_id]
  refine NatTrans.ext (funext fun n => ?_)
  exact (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r).map_id _

omit [AlgebraicGeometry.IsNoetherian W.1] in
/-- The endomorphism of `n ↦ Rʳ g_! G'ₙ` induced by `φ ≫ ψ` is the composite of those induced by
`φ` and `ψ`. -/
theorem LAdicSheaf.lowerShriekTowerEnd_comp (G : LAdicSheaf B U ℓ) (r : ℤ) (φ ψ : G ⟶ G) :
    LAdicSheaf.lowerShriekTowerEnd B ℓ g jg G r (φ ≫ ψ) =
      LAdicSheaf.lowerShriekTowerEnd B ℓ g jg G r φ ≫
        LAdicSheaf.lowerShriekTowerEnd B ℓ g jg G r ψ := by
  unfold LAdicSheaf.lowerShriekTowerEnd
  rw [LAdicSheaf.torsionFreeModelMap_comp, LAdicSheaf.padicTowerMap_comp]
  refine NatTrans.ext (funext fun n => ?_)
  exact (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r).map_comp _ _

omit [AlgebraicGeometry.IsNoetherian W.1] in
/-- The endomorphism of `n ↦ Rʳ g_! G'ₙ` induced by `φ + ψ` is the sum of those induced by `φ`
and `ψ`. -/
theorem LAdicSheaf.lowerShriekTowerEnd_add (G : LAdicSheaf B U ℓ) (r : ℤ) (φ ψ : G ⟶ G) :
    LAdicSheaf.lowerShriekTowerEnd B ℓ g jg G r (φ + ψ) =
      LAdicSheaf.lowerShriekTowerEnd B ℓ g jg G r φ +
        LAdicSheaf.lowerShriekTowerEnd B ℓ g jg G r ψ := by
  unfold LAdicSheaf.lowerShriekTowerEnd
  rw [LAdicSheaf.torsionFreeModelMap_add, LAdicSheaf.padicTowerMap_add]
  refine NatTrans.ext (funext fun n => ?_)
  exact (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r).map_add

/-- Under `HigherDirectImageShriekCondition`, the endomorphism of `Rʳ g_! G` induced by `φ` is
obtained from the endomorphism of the stable images of `n ↦ Rʳ g_! G'ₙ` induced by `φ`. -/
theorem LAdicSheaf.higherDirectImageShriekEnd_of_condition (G : LAdicSheaf B U ℓ) (r : ℕ)
    (h : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g jg G r) (φ : G ⟶ G) :
    haveI := h.fst
    LAdicSheaf.higherDirectImageShriekEnd B ℓ g jg G r φ =
      LAdicSheaf.homOfPadicTower
        ((LAdicSheaf.padicTowerHigherDirectImageShriekIso B ℓ g jg G r h).hom ≫
        (LAdicSheaf.lowerShriekTowerLES B ℓ g jg G r).stableImageMap
          (LAdicSheaf.lowerShriekTowerEnd B ℓ g jg G r φ) ≫
        (LAdicSheaf.padicTowerHigherDirectImageShriekIso B ℓ g jg G r h).inv) :=
  dite_eq_left h

/-- Without `HigherDirectImageShriekCondition`, the ℓ-adic sheaf `Rʳ g_! G` is zero. -/
theorem LAdicSheaf.isZero_higherDirectImageShriek (G : LAdicSheaf B U ℓ) (r : ℕ)
    (h : ¬ LAdicSheaf.HigherDirectImageShriekCondition B ℓ g jg G r) :
    IsZero (LAdicSheaf.higherDirectImageShriek B ℓ g jg G r) := by
  rw [LAdicSheaf.higherDirectImageShriek, dite_eq_right h]
  exact LAdicSheaf.zeroSystem_isZero B W ℓ

/-- **The ring homomorphism `End G →+* End (Rʳ g_! G)`.** -/
def LAdicSheaf.higherDirectImageShriekEndRingHom (G : LAdicSheaf B U ℓ) (r : ℕ) :
    End G →+* End (LAdicSheaf.higherDirectImageShriek B ℓ g jg G r) :=
  RingHom.mk'
    { toFun := LAdicSheaf.higherDirectImageShriekEnd B ℓ g jg G r
      map_one' := by
        by_cases h : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g jg G r
        · have := h.fst
          rw [LAdicSheaf.higherDirectImageShriekEnd_of_condition B ℓ g jg G r h, End.one_def,
            End.one_def, LAdicSheaf.lowerShriekTowerEnd_id, LESData.stableImageMap_id,
            Category.id_comp, Iso.hom_inv_id, LAdicSheaf.homOfPadicTower_id]
        · exact (LAdicSheaf.isZero_higherDirectImageShriek B ℓ g jg G r h).eq_of_src _ _
      map_mul' := fun φ ψ => by
        by_cases h : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g jg G r
        · have := h.fst
          rw [LAdicSheaf.higherDirectImageShriekEnd_of_condition B ℓ g jg G r h,
            LAdicSheaf.higherDirectImageShriekEnd_of_condition B ℓ g jg G r h,
            LAdicSheaf.higherDirectImageShriekEnd_of_condition B ℓ g jg G r h, End.mul_def,
            End.mul_def, LAdicSheaf.lowerShriekTowerEnd_comp, LESData.stableImageMap_comp,
            ← LAdicSheaf.homOfPadicTower_comp]
          simp only [Category.assoc, Iso.inv_hom_id_assoc]
        · exact (LAdicSheaf.isZero_higherDirectImageShriek B ℓ g jg G r h).eq_of_src _ _ }
    (fun φ ψ => by
      by_cases h : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g jg G r
      · have := h.fst
        change LAdicSheaf.higherDirectImageShriekEnd B ℓ g jg G r (φ + ψ) =
          LAdicSheaf.higherDirectImageShriekEnd B ℓ g jg G r φ +
            LAdicSheaf.higherDirectImageShriekEnd B ℓ g jg G r ψ
        rw [LAdicSheaf.higherDirectImageShriekEnd_of_condition B ℓ g jg G r h,
          LAdicSheaf.higherDirectImageShriekEnd_of_condition B ℓ g jg G r h,
          LAdicSheaf.higherDirectImageShriekEnd_of_condition B ℓ g jg G r h,
          LAdicSheaf.lowerShriekTowerEnd_add, LESData.stableImageMap_add, Preadditive.add_comp,
          Preadditive.comp_add, LAdicSheaf.homOfPadicTower_add]
      · exact (LAdicSheaf.isZero_higherDirectImageShriek B ℓ g jg G r h).eq_of_src _ _)

/-- The ring homomorphism `End G →+* End (Rʳ g_! G)` sends `φ` to
`higherDirectImageShriekEnd φ`. -/
theorem LAdicSheaf.higherDirectImageShriekEndRingHom_apply (G : LAdicSheaf B U ℓ) (r : ℕ)
    (φ : End G) :
    LAdicSheaf.higherDirectImageShriekEndRingHom B ℓ g jg G r φ =
      LAdicSheaf.higherDirectImageShriekEnd B ℓ g jg G r φ :=
  rfl

/-- **The endomorphism of `Rʳ g_! G` induced by `φ`, levelwise**: under the identification of the
tower of levels of `Rʳ g_! G` with the stable images of `n ↦ Rʳ g_! G'ₙ`, it is the endomorphism
of the stable images induced by `Rʳ g_!(φ'ₙ)`. -/
theorem LAdicSheaf.higherDirectImageShriekEnd_padicLevelMap (G : LAdicSheaf B U ℓ) (r : ℕ)
    (h : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g jg G r) (φ : G ⟶ G) (n : ℕ) :
    haveI := h.fst
    (SmallEtale.sheafEquiv B W.1 W.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
        (LAdicSheaf.padicLevelMap (LAdicSheaf.higherDirectImageShriekEnd B ℓ g jg G r φ) n) ≫
      (LAdicSheaf.padicTowerHigherDirectImageShriekIso B ℓ g jg G r h).hom.app (op n) =
    (LAdicSheaf.padicTowerHigherDirectImageShriekIso B ℓ g jg G r h).hom.app (op n) ≫
      ((LAdicSheaf.lowerShriekTowerLES B ℓ g jg G r).stableImageMap
        (LAdicSheaf.lowerShriekTowerEnd B ℓ g jg G r φ)).app (op n) := by
  have := h.fst
  rw [LAdicSheaf.higherDirectImageShriekEnd_of_condition B ℓ g jg G r h,
    LAdicSheaf.sheafEquiv_map_padicLevelMap_homOfPadicTower]
  simp only [LAdicSheaf.padicTowerApp, NatTrans.comp_app]
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (Iso.inv_hom_id_app _ _)).trans (Category.comp_id _))))

/-- **`Rʳ g_! F` of a coefficient sheaf `F`**, with the induced action of the coefficients. -/
def LAdicSheaf.CoefficientSheaf.higherDirectImageShriek {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O]
    (F : LAdicSheaf.CoefficientSheaf B U ℓ O) (r : ℕ) : LAdicSheaf.CoefficientSheaf B W ℓ O where
  toLAdicSheaf := LAdicSheaf.higherDirectImageShriek B ℓ g jg F.toLAdicSheaf r
  act := (LAdicSheaf.higherDirectImageShriekEndRingHom B ℓ g jg F.toLAdicSheaf r).comp F.act

end HigherDirectImage

end Stacks.EtaleCohomology
