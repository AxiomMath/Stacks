module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.KummerClassMapLevel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.PadicForgetLift
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.ModuleForgetHigherDirectImageRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.TwistNegOne
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTowerSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicLowerShriekTower

/-!
# The purity maps of the levels of an ℓ-adic sheaf, as a morphism of towers

Let `G` be an ℓ-adic sheaf on `U`, `j : U₀ ⟶ U` the open complement of a divisor `Z` with local
equations, and `ℓ` invertible on `U`. At level `n`, with `N = ℓⁿ⁺¹` and `Gₙ` the `n`-th level, the
purity map `𝓗om(μ_N, Gₙ) ⟶ R¹ j_*(j⁻¹ Gₙ)`, `α ↦ α_* s_N` for `s_N` the fundamental class of `Z`
(`Stacks.EtaleCohomology.Purity.kummerClassMapAb`), read on `ℤ_ℓ`-module sheaves, is a morphism
from level `n` of the tower `n ↦ 𝓗om(μ_{ℓⁿ⁺¹}, Gₙ)` of the Tate twist
(`Stacks.EtaleCohomology.LAdicSheaf.twistNegOneTower`) to level `n` of the tower
`n ↦ R¹ j_*(j⁻¹ Gₙ)` of `ℤ_ℓ`-sheaves (`Stacks.EtaleCohomology.Purity.purityTowerTarget`).
These maps are compatible with the transitions (`Stacks.EtaleCohomology.Purity.purityTowerMap`).

This is the morphism of towers whose inverse image on `Z` the tower form of cohomological purity
proves to be an isomorphism ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main definitions

* `Stacks.EtaleCohomology.Purity.purityTowerTarget`.
* `Stacks.EtaleCohomology.Purity.purityTowerLevelMap`.
* `Stacks.EtaleCohomology.Purity.purityTowerMap`.

## Main results

* `LAdicSheaf.restrictScalars_etaleTransition_comp_sheafEquivRestrictScalarsIso`, in the namespace
  `Stacks.EtaleCohomology`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.SmallEtale Stacks.InverseSystem CategoryTheory.LAdicTower

universe w u

namespace Stacks.EtaleCohomology

attribute [local instance] neZero_pow_of_fact_prime neZero_natCast_pow moduleCat_hasLimitsOfSize

variable {B : BigEtaleSite.{u}} {U : B.Scheme} {ℓ : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B U.1 U.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian U.1] [Fact ℓ.Prime]

/-- A diagram chase: the coherence of the comparisons of restriction of scalars with reading
sheaves on Mathlib's site, on variables. -/
private lemma paste_transition_aux {C : Type*} [Category* C] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : C}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (b' : X₂ ⟶ X₁) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) (f₁ : X₁ ⟶ X₅)
    (g : X₅ ⟶ X₄) (ε : X₀ ⟶ X₆) (m : X₆ ⟶ X₅) (hA : c ≫ d = b' ≫ f₁ ≫ g)
    (hB : a ≫ f₁ = ε ≫ m) (hbb : b ≫ b' = 𝟙 _) :
    (a ≫ b) ≫ c ≫ d = ε ≫ m ≫ g := by
  rw [hA, Category.assoc, reassoc_of% hbb, reassoc_of% hB]

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **The transitions of an ℓ-adic sheaf, read over `ℤ_ℓ` on Mathlib's small étale site**: the
comparisons of restriction of scalars with reading sheaves on Mathlib's site carry the transition
`Gₙ₊₁ ⟶ Gₙ` of the levels to the transition of the tower of `ℤ_ℓ`-sheaves. -/
theorem LAdicSheaf.restrictScalars_etaleTransition_comp_sheafEquivRestrictScalarsIso
    (G : LAdicSheaf.{u, u + 1} B U ℓ) (n : ℕ) :
    (etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1 + 1)) U.1).map
        (LAdicSheaf.etaleTransition B U ℓ G n) ≫
      (etaleModuleRestrictScalarsComp (PadicInt.toZModPow (p := ℓ) (n + 1 + 1)) (levelCast ℓ n)
        (PadicInt.toZModPow (p := ℓ) (n + 1)) (toZModPow_succ_comp ℓ n) U.1).hom.app
        (LAdicSheaf.etaleLevel B U ℓ G n) ≫
      (sheafEquivRestrictScalarsIso B U.1 U.property
        (PadicInt.toZModPow (p := ℓ) (n + 1))).hom.app (G.level n) =
    (sheafEquivRestrictScalarsIso B U.1 U.property
        (PadicInt.toZModPow (p := ℓ) (n + 1 + 1))).hom.app (G.level (n + 1)) ≫
      (LAdicSheaf.padicTower B U ℓ G).map (homOfLE (n.le_add_right 1)).op := by
  have hA := sheafEquivRestrictScalarsIso_comp B U.1 U.property
    (PadicInt.toZModPow (p := ℓ) (n + 1 + 1)) (levelCast ℓ n) (PadicInt.toZModPow (p := ℓ) (n + 1))
    (toZModPow_succ_comp ℓ n) (G.level n)
  have hB : (etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1 + 1)) U.1).map
        ((SmallEtale.sheafEquiv B U.1 U.property
          (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1 + 1))))).functor.map (G.transition n)) ≫
      (sheafEquivRestrictScalarsIso B U.1 U.property
        (PadicInt.toZModPow (p := ℓ) (n + 1 + 1))).hom.app
        ((sheafCompose (SmallEtale.topology B U.1 U.property)
          (ModuleCat.restrictScalars.{u + 1} (levelCast ℓ n))).obj (G.level n)) =
      (sheafEquivRestrictScalarsIso B U.1 U.property
        (PadicInt.toZModPow (p := ℓ) (n + 1 + 1))).hom.app (G.level (n + 1)) ≫
      (SmallEtale.sheafEquiv B U.1 U.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
        ((sheafCompose (SmallEtale.topology B U.1 U.property)
          (ModuleCat.restrictScalars.{u + 1} (PadicInt.toZModPow (p := ℓ) (n + 2)))).map
          (G.transition n)) :=
    (sheafEquivRestrictScalarsIso B U.1 U.property
      (PadicInt.toZModPow (p := ℓ) (n + 1 + 1))).hom.naturality (G.transition n)
  have hbb : (etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1 + 1)) U.1).map
        ((sheafEquivRestrictScalarsIso B U.1 U.property (levelCast ℓ n)).inv.app (G.level n)) ≫
      (etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1 + 1)) U.1).map
        ((sheafEquivRestrictScalarsIso B U.1 U.property (levelCast ℓ n)).hom.app (G.level n)) =
      𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  rw [LAdicSheaf.padicTower_map_succ, LAdicSheaf.etaleTransition, LAdicSheaf.padicTransition,
    CategoryTheory.Functor.map_comp]
  exact (paste_transition_aux _ _ _ _ _ _ _ _ _ hA hB hbb).trans
    (congrArg (_ ≫ ·) (CategoryTheory.Functor.map_comp _ _ _).symm)

namespace Purity

-- `AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives` has a free universe; with it in scope
-- the instance problems `EnoughInjectives (EtaleModules Λ X)` get stuck on a universe constraint.
attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

variable {U₀ : Scheme.{u}} (j : U₀ ⟶ U.1) [IsOpenImmersion j] (G : LAdicSheaf.{u, u + 1} B U ℓ)

/-- **The tower `n ↦ R¹ j_*(j⁻¹ Gₙ)`** of sheaves of `ℤ_ℓ`-modules on `U`, for `Gₙ` the levels of
an ℓ-adic sheaf `G` and `j : U₀ ⟶ U` an open immersion. -/
abbrev purityTowerTarget : ℕᵒᵖ ⥤ EtaleModules.{u, 0} ℤ_[ℓ] U.1 :=
  LAdicSheaf.padicTower B U ℓ G ⋙ etaleModuleRestriction.{u, 0} ℤ_[ℓ] j ⋙
    (etaleModuleDirectImage.{u, 0} ℤ_[ℓ] j).rightDerived 1

/-- The levels of the tower `n ↦ R¹ j_*(j⁻¹ Gₙ)` are killed by the powers of `ℓ`. -/
theorem purityTowerTarget_annihilated (n : ℕ) :
    ℓ ^ (n + 1) • 𝟙 ((purityTowerTarget j G).obj (op n)) = 0 := by
  show ℓ ^ (n + 1) • 𝟙 (((etaleModuleDirectImage.{u, 0} ℤ_[ℓ] j).rightDerived 1).obj
    ((etaleModuleRestriction.{u, 0} ℤ_[ℓ] j).obj (towerObj (LAdicSheaf.padicTower B U ℓ G) n))) = 0
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, ← CategoryTheory.Functor.map_id,
    ← Functor.map_nsmul, LAdicSheaf.padicTower_annihilated, Functor.map_zero, Functor.map_zero]

variable [HasDerivedCategory.{w} (Sheaf (smallEtaleTopology U₀) Ab.{u + 1})]
  [HasDerivedCategory.{w} (Sheaf (smallEtaleTopology U.1) Ab.{u + 1})]
  (hℓ₀ : IsUnit ((ℓ : ℕ) : Γ(U₀, ⊤))) (hℓ : IsUnit ((ℓ : ℕ) : Γ(U.1, ⊤)))
  {Z : Scheme.{u}} (i : Z ⟶ U.1) [IsClosedImmersion i] (hj : Set.range j.base ⊆ (Set.range i.base)ᶜ)
  (hcov : ∀ x : U.1, ∃ (V : U.1.Opens) (t : Γ(U.1, V)), x ∈ V ∧ IsLocalEquation i V t)
  {k : Type u} [Field k] (fX : U.1 ⟶ Spec (.of k)) [NeZero (ℓ : k)]

/-- **The purity map at level `n`, on underlying abelian sheaves**:
`𝓗om(μ_{ℓⁿ⁺¹}, Gₙ) ⟶ R¹ j_*(j⁻¹ Gₙ)`, `α ↦ α_* s` for `s` the fundamental class of `Z`, followed
by the identification of `Gₙ` read over `ℤ_ℓ` with the level `n` of the tower of `G`. -/
def purityTowerLevelMapAb (n : ℕ) :
    (etaleModuleForgetAb.{u, 0} ℤ_[ℓ] U.1).obj ((LAdicSheaf.twistNegOneTower fX G).obj (op n)) ⟶
      (etaleModuleForgetAb.{u, 0} ℤ_[ℓ] U.1).obj ((purityTowerTarget j G).obj (op n)) :=
  kummerClassMapAb j (ℓ ^ (n + 1)) (by rw [Nat.cast_pow]; exact hℓ₀.pow _)
      (by rw [Nat.cast_pow]; exact hℓ.pow _) i hj hcov (LAdicSheaf.etaleLevel B U ℓ G n) ≫
    ((smallEtalePushforwardAb j).rightDerived 1).map ((smallEtalePullbackAb j).map
      ((etaleModuleForgetAb.{u, 0} ℤ_[ℓ] U.1).map
        ((sheafEquivRestrictScalarsIso B U.1 U.property
          (PadicInt.toZModPow (p := ℓ) (n + 1))).hom.app (G.level n)))) ≫
    (etaleModuleForgetHigherDirectImageRestrictionIso ℤ_[ℓ] j
      ((LAdicSheaf.padicTower B U ℓ G).obj (op n)) 1).inv

/-- **The purity map at level `n`**, `𝓗om(μ_{ℓⁿ⁺¹}, Gₙ) ⟶ R¹ j_*(j⁻¹ Gₙ)`, as a morphism of
sheaves of `ℤ_ℓ`-modules: both sides are killed by `ℓⁿ⁺¹`. -/
def purityTowerLevelMap (n : ℕ) :
    (LAdicSheaf.twistNegOneTower fX G).obj (op n) ⟶ (purityTowerTarget j G).obj (op n) :=
  etaleModulePadicLift (n + 1) (LAdicSheaf.twistNegOneTower_annihilated fX G n)
    (purityTowerTarget_annihilated j G n) (purityTowerLevelMapAb j G hℓ₀ hℓ i hj hcov fX n)

/-- On underlying abelian sheaves, the purity map at level `n` is
`Stacks.EtaleCohomology.Purity.purityTowerLevelMapAb`. -/
theorem etaleModuleForgetAb_map_purityTowerLevelMap (n : ℕ) :
    (etaleModuleForgetAb.{u, 0} ℤ_[ℓ] U.1).map (purityTowerLevelMap j G hℓ₀ hℓ i hj hcov fX n) =
      purityTowerLevelMapAb j G hℓ₀ hℓ i hj hcov fX n :=
  rfl

/-- Six morphisms in two commuting squares and a third one, pasted: the shape of the
compatibility of the purity maps with the transitions. -/
private lemma paste_tower_aux {C : Type*} [Category* C] {A₀ A₁ B₀ B₁ C₀ C₁ D₀ D₁ : C}
    (tT : A₀ ⟶ A₁) (c : A₁ ⟶ B₁) (c' : A₀ ⟶ B₀) (r : B₀ ⟶ B₁) (e : B₁ ⟶ C₁) (φ : C₁ ⟶ D₁)
    (e' : B₀ ⟶ C₀) (φ' : C₀ ⟶ D₀) (p : C₀ ⟶ C₁) (L : D₀ ⟶ D₁)
    (hE : tT ≫ c = c' ≫ r) (hF : r ≫ e = e' ≫ p) (hN : φ' ≫ L = p ≫ φ) :
    tT ≫ c ≫ e ≫ φ = (c' ≫ e' ≫ φ') ≫ L := by
  rw [reassoc_of% hE, reassoc_of% hF, Category.assoc, Category.assoc, hN]

/-- A commuting square of isomorphisms and morphisms, read with the inverses. -/
private lemma inv_square_aux {C : Type*} [Category* C] {X₀ X₁ Y₀ Y₁ : C} (L : X₀ ⟶ X₁)
    (α : X₁ ≅ Y₁) (β : X₀ ≅ Y₀) (p : Y₀ ⟶ Y₁) (h : L ≫ α.hom = β.hom ≫ p) :
    β.inv ≫ L = p ≫ α.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- A functor carries an equality of two composites to an equality of the composites of images. -/
private lemma map_comp_eq_aux {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {X Y Z : C} {X' : C} {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X ⟶ X'} {g' : X' ⟶ Z} (h : f ≫ g = f' ≫ g') :
    F.map f ≫ F.map g = F.map f' ≫ F.map g' := by
  rw [← F.map_comp, ← F.map_comp, h]

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **The purity maps are compatible with the transitions**: the square formed by the transitions
of the twisted tower `n ↦ 𝓗om(μ_{ℓⁿ⁺¹}, Gₙ)`, those of `n ↦ R¹ j_*(j⁻¹ Gₙ)` and the purity maps
at levels `n` and `n + 1` commutes. -/
theorem purityTowerLevelMap_naturality (n : ℕ) :
    (LAdicSheaf.twistNegOneTower fX G).map (homOfLE (n.le_add_right 1)).op ≫
        purityTowerLevelMap j G hℓ₀ hℓ i hj hcov fX n =
      purityTowerLevelMap j G hℓ₀ hℓ i hj hcov fX (n + 1) ≫
        (purityTowerTarget j G).map (homOfLE (n.le_add_right 1)).op := by
  apply (etaleModuleForgetAb.{u, 0} ℤ_[ℓ] U.1).map_injective
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    etaleModuleForgetAb_map_purityTowerLevelMap, etaleModuleForgetAb_map_purityTowerLevelMap,
    LAdicSheaf.twistNegOneTower_map_succ]
  have htT : (etaleModuleForgetAb.{u, 0} ℤ_[ℓ] U.1).map
      ((etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1 + 1)) U.1).map
          (LAdicSheaf.twistNegOneTransition fX G n) ≫
        (etaleModuleRestrictScalarsComp (PadicInt.toZModPow (p := ℓ) (n + 1 + 1)) (levelCast ℓ n)
          (PadicInt.toZModPow (p := ℓ) (n + 1)) (toZModPow_succ_comp ℓ n) U.1).hom.app
          (LAdicSheaf.twistNegOneLevel G n)) =
      (sheafCompose (smallEtaleTopology U.1) (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1 + 1))))
        AddCommGrpCat.{u + 1})).map (LAdicSheaf.twistNegOneTransition fX G n) := rfl
  have ht : (etaleModuleForgetAb.{u, 0} ℤ_[ℓ] U.1).map
        ((etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1 + 1)) U.1).map
          (LAdicSheaf.etaleTransition B U ℓ G n)) ≫
      (etaleModuleForgetAb.{u, 0} ℤ_[ℓ] U.1).map
        ((etaleModuleRestrictScalarsComp (PadicInt.toZModPow (p := ℓ) (n + 1 + 1)) (levelCast ℓ n)
          (PadicInt.toZModPow (p := ℓ) (n + 1)) (toZModPow_succ_comp ℓ n) U.1).hom.app
          (LAdicSheaf.etaleLevel B U ℓ G n)) =
      (sheafCompose (smallEtaleTopology U.1) (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1 + 1))))
        AddCommGrpCat.{u + 1})).map (LAdicSheaf.etaleTransition B U ℓ G n) := rfl
  have hE := twistNegOneModuleTransition_comp_kummerClassMapAb j ℓ (ℓ ^ (n + 1)) (ℓ ^ (n + 1 + 1))
    (mul_pow_succ_eq ℓ n) (by rw [Nat.cast_pow]; exact hℓ₀.pow _)
    (by rw [Nat.cast_pow]; exact hℓ.pow _) (by rw [Nat.cast_pow]; exact hℓ₀.pow _)
    (by rw [Nat.cast_pow]; exact hℓ.pow _) i hj hcov (LAdicSheaf.etaleLevel B U ℓ G n) fX
    (LAdicSheaf.etaleLevel B U ℓ G (n + 1)) (LAdicSheaf.etaleTransition B U ℓ G n)
  have hF0 := congrArg (etaleModuleForgetAb.{u, 0} ℤ_[ℓ] U.1).map
    (LAdicSheaf.restrictScalars_etaleTransition_comp_sheafEquivRestrictScalarsIso G n)
  have hF :
      (sheafCompose (smallEtaleTopology U.1) (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1 + 1))))
          AddCommGrpCat.{u + 1})).map (LAdicSheaf.etaleTransition B U ℓ G n) ≫
        (etaleModuleForgetAb.{u, 0} ℤ_[ℓ] U.1).map
          ((sheafEquivRestrictScalarsIso B U.1 U.property
            (PadicInt.toZModPow (p := ℓ) (n + 1))).hom.app (G.level n)) =
      (etaleModuleForgetAb.{u, 0} ℤ_[ℓ] U.1).map
          ((sheafEquivRestrictScalarsIso B U.1 U.property
            (PadicInt.toZModPow (p := ℓ) (n + 1 + 1))).hom.app (G.level (n + 1))) ≫
        (etaleModuleForgetAb.{u, 0} ℤ_[ℓ] U.1).map
          ((LAdicSheaf.padicTower B U ℓ G).map (homOfLE (n.le_add_right 1)).op) :=
    (congrArg (· ≫ _) ht.symm).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) ((etaleModuleForgetAb.{u, 0} ℤ_[ℓ] U.1).map_comp _ _).symm).trans
        (((etaleModuleForgetAb.{u, 0} ℤ_[ℓ] U.1).map_comp _ _).symm.trans
          (hF0.trans ((etaleModuleForgetAb.{u, 0} ℤ_[ℓ] U.1).map_comp _ _)))))
  have hF' :
      ((smallEtalePushforwardAb j).rightDerived 1).map ((smallEtalePullbackAb j).map
          ((sheafCompose (smallEtaleTopology U.1)
            (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1 + 1)))) AddCommGrpCat.{u + 1})).map
              (LAdicSheaf.etaleTransition B U ℓ G n))) ≫
        ((smallEtalePushforwardAb j).rightDerived 1).map ((smallEtalePullbackAb j).map
          ((etaleModuleForgetAb.{u, 0} ℤ_[ℓ] U.1).map
            ((sheafEquivRestrictScalarsIso B U.1 U.property
              (PadicInt.toZModPow (p := ℓ) (n + 1))).hom.app (G.level n)))) =
      ((smallEtalePushforwardAb j).rightDerived 1).map ((smallEtalePullbackAb j).map
          ((etaleModuleForgetAb.{u, 0} ℤ_[ℓ] U.1).map
            ((sheafEquivRestrictScalarsIso B U.1 U.property
              (PadicInt.toZModPow (p := ℓ) (n + 1 + 1))).hom.app (G.level (n + 1))))) ≫
        ((smallEtalePushforwardAb j).rightDerived 1).map ((smallEtalePullbackAb j).map
          ((etaleModuleForgetAb.{u, 0} ℤ_[ℓ] U.1).map
            ((LAdicSheaf.padicTower B U ℓ G).map (homOfLE (n.le_add_right 1)).op))) :=
    map_comp_eq_aux _ (map_comp_eq_aux _ hF)
  have hN := etaleModuleForgetHigherDirectImageRestrictionIso_hom_naturality ℤ_[ℓ] j 1
    ((LAdicSheaf.padicTower B U ℓ G).map (homOfLE (n.le_add_right 1)).op)
  have hN' := inv_square_aux _ _ _ _ hN
  refine (congrArg (· ≫ _) htT).trans ?_
  exact paste_tower_aux _ _ _ _ _ _ _ _ _ _ hE hF' hN'

/-- **The purity maps as a morphism of towers**: `𝓗om(μ_{ℓⁿ⁺¹}, Gₙ) ⟶ R¹ j_*(j⁻¹ Gₙ)`,
`α ↦ α_* s` at each level `n`, from the tower of the Tate twist of `G` to the tower
`n ↦ R¹ j_*(j⁻¹ Gₙ)` of sheaves of `ℤ_ℓ`-modules. -/
def purityTowerMap : LAdicSheaf.twistNegOneTower fX G ⟶ purityTowerTarget j G :=
  NatTrans.ofOpSequence (F := LAdicSheaf.twistNegOneTower fX G) (G := purityTowerTarget j G)
    (fun n => purityTowerLevelMap j G hℓ₀ hℓ i hj hcov fX n)
    (fun n => purityTowerLevelMap_naturality j G hℓ₀ hℓ i hj hcov fX n)

/-- The component at level `n` of the morphism of towers is the purity map at level `n`. -/
theorem purityTowerMap_app (n : ℕ) :
    (purityTowerMap j G hℓ₀ hℓ i hj hcov fX).app (op n) =
      purityTowerLevelMap j G hℓ₀ hℓ i hj hcov fX n :=
  NatTrans.ofOpSequence_app _ _ _

end Purity

end Stacks.EtaleCohomology


end
