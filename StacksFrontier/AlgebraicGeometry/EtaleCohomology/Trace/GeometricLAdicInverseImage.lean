module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicCompactSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalars

/-!
# The levels of the inverse image of an ℓ-adic sheaf, on Mathlib's small étale site

Let `g : X' ⟶ X` be a morphism of Noetherian schemes of a big étale site `B` and `F = (Fₙ)` an
ℓ-adic sheaf on `X`.  The compactly supported cohomology of `F` is formed from the levels `Fₙ`
read as sheaves of `ℤ_ℓ`-modules on Mathlib's small étale site
(`Stacks.EtaleCohomology.padicCoefficientComplex`).  This file identifies these levels for the
inverse image `g⁻¹F` (`AlgebraicGeometry.SmallEtale.LAdicSheaf.inverseImage`) with the inverse
images, on Mathlib's site, of the levels of `F`:

`(g⁻¹F)ₙ ≅ g⁻¹(Fₙ)`,

compatibly with the transition maps.  The identification is the composite of the comparison of
the inverse images of the two presentations of the small étale site
(`AlgebraicGeometry.SmallEtale.sheafEquivPullbackBaseChangeIso`) with the comparison of inverse
image with restriction of scalars from `ℤ/ℓⁿ⁺¹` to `ℤ_ℓ`
(`Stacks.EtaleCohomology.coefficientSheafPullbackTwoSquare`).  Its compatibility with the
transition maps is checked on adjoints: all comparisons are mates of strict commutations of
direct image with restriction of scalars.  This is the coefficient half of the reduction, in the
proof of [Stacks, Tag 03V0], of the trace formula for `π_X^m` to Tag 03V2 for `X ×_k k_m`.

## Main definitions

* `Stacks.EtaleCohomology.padicLevelInverseImageIso`: `(g⁻¹Fₙ)` read on Mathlib's site is
  `g⁻¹` of `Fₙ` read on Mathlib's site.

## Main results

* `Stacks.EtaleCohomology.padicLevelInverseImageIso_transition`: compatibility with the
  transition maps.

## References

* [Stacks Project, Tag 03V0](https://stacks.math.columbia.edu/tag/03V0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) {X X' : B.Scheme} (g : X' ⟶ X) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- Restriction of scalars from `ℤ/ℓⁿ⁺¹` to `ℤ_ℓ`, on sheaves on the small étale site of
Stacks 021B. -/
abbrev padicRestrict (Z : B.Scheme) (n : ℕ) :
    Sheaf (SmallEtale.topology B Z.1 Z.property) (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) ⥤
      Sheaf (SmallEtale.topology B Z.1 Z.property) (ModuleCat.{u + 1} ℤ_[ℓ]) :=
  sheafCompose (SmallEtale.topology B Z.1 Z.property)
    (ModuleCat.restrictScalars.{u + 1, 0, 0} (PadicInt.toZModPow (n + 1)))

/-- The comparison `g⁻¹ ∘ res ⟶ res ∘ g⁻¹` of inverse image along `g` with restriction of scalars
from `ℤ/ℓⁿ⁺¹` to `ℤ_ℓ`, on the small étale sites of Stacks 021B. -/
abbrev padicRestrictInverseImage (n : ℕ) :=
  (coefficientSheafPullbackTwoSquare (AlgebraicGeometry.smallEtaleBaseChange B g)
    (SmallEtale.topology B X.1 X.property) (SmallEtale.topology B X'.1 X'.property)
    (ModuleCat.restrictScalars.{u + 1, 0, 0} (PadicInt.toZModPow (p := ℓ) (n + 1)))).natTrans

/-- Sheaves of `ℤ_ℓ`-modules on the small étale site of Stacks 021B, read on Mathlib's small étale
site. -/
abbrev padicSheafEquiv (Z : B.Scheme) :
    Sheaf (SmallEtale.topology B Z.1 Z.property) (ModuleCat.{u + 1} ℤ_[ℓ]) ⥤
      EtaleModules.{u, 0} ℤ_[ℓ] Z.1 :=
  (SmallEtale.sheafEquiv B Z.1 Z.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor

/-- **The level `g⁻¹ Gₙ`, read on Mathlib's site, is the inverse image of `Gₙ` read on Mathlib's
site**, for a sheaf `G` of `ℤ/ℓⁿ⁺¹`-modules on the small étale site of Stacks 021B of `X`: the
comparison of the inverse images of the two presentations of the small étale site, then the
comparison of inverse image with restriction of scalars to `ℤ_ℓ`. -/
def padicLevelInverseImageIso (n : ℕ) (G : FiniteLevelSheaf.{u, u + 1} B X ℓ n) :
    (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map g)).obj
        ((padicSheafEquiv B ℓ X).obj ((padicRestrict B ℓ X n).obj G)) ≅
      (padicSheafEquiv B ℓ X').obj
        ((padicRestrict B ℓ X' n).obj ((LAdicSheaf.levelPullback g n).obj G)) :=
  (sheafEquivPullbackBaseChangeIso B g (ModuleCat.{u + 1} ℤ_[ℓ])
      (etaleModuleInverseImageAdj.{u, 0} ℤ_[ℓ] (B.inclusion.map g))
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafAdjunctionContinuous
        (ModuleCat.{u + 1} ℤ_[ℓ]) _ _)).app ((padicRestrict B ℓ X n).obj G) ≪≫
    (padicSheafEquiv B ℓ X').mapIso (asIso ((padicRestrictInverseImage B g ℓ n).app G))

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- The identification is natural in the sheaf of `ℤ/ℓⁿ⁺¹`-modules. -/
lemma padicLevelInverseImageIso_hom_naturality (n : ℕ)
    {G G' : FiniteLevelSheaf.{u, u + 1} B X ℓ n} (φ : G ⟶ G') :
    (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map g)).map
        ((padicSheafEquiv B ℓ X).map ((padicRestrict B ℓ X n).map φ)) ≫
      (padicLevelInverseImageIso B g ℓ n G').hom =
    (padicLevelInverseImageIso B g ℓ n G).hom ≫
      (padicSheafEquiv B ℓ X').map
        ((padicRestrict B ℓ X' n).map ((LAdicSheaf.levelPullback g n).map φ)) := by
  have h₁ := (sheafEquivPullbackBaseChangeIso B g (ModuleCat.{u + 1} ℤ_[ℓ])
      (etaleModuleInverseImageAdj.{u, 0} ℤ_[ℓ] (B.inclusion.map g))
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafAdjunctionContinuous
        (ModuleCat.{u + 1} ℤ_[ℓ]) _ _)).hom.naturality ((padicRestrict B ℓ X n).map φ)
  have h₂ := (padicRestrictInverseImage B g ℓ n).naturality φ
  dsimp only [Functor.comp_map, Functor.comp_obj] at h₁ h₂
  simp only [padicLevelInverseImageIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, asIso_hom,
    Category.assoc]
  rw [reassoc_of% h₁, ← Functor.map_comp, ← Functor.map_comp, h₂]

/-! ### Change of level -/

/-- The identification of the two restrictions of scalars to `ℤ_ℓ` of a sheaf of
`ℤ/ℓⁿ⁺¹`-modules, through `ℤ/ℓⁿ⁺²` or directly. -/
abbrev padicRestrictLevel (Z : B.Scheme) (n : ℕ) :
    LAdicSheaf.levelRestrict (ℓ := ℓ) Z n ⋙ padicRestrict B ℓ Z (n + 1) ⟶ padicRestrict B ℓ Z n :=
  sheafCompose_map (SmallEtale.topology B Z.1 Z.property)
    (ModuleCat.restrictScalarsComp'.{u + 1} (PadicInt.toZModPow (p := ℓ) (n + 2))
      (finiteLevelRingHom ℓ n) (PadicInt.toZModPow (n + 1)) (toZModPow_succ_comp ℓ n)).inv

/-- The comparison `g⁻¹ ∘ res ⟶ res ∘ g⁻¹` of inverse image with restriction of scalars from
`ℤ/ℓⁿ⁺²` to `ℤ/ℓⁿ⁺¹`: the adjoint of `res` of the unit.  The transition maps of `g⁻¹F` are the
inverse images of those of `F` followed by it. -/
def levelPullbackRestrict (n : ℕ) (H : FiniteLevelSheaf.{u, u + 1} B X ℓ n) :
    (LAdicSheaf.levelPullback g (n + 1)).obj ((LAdicSheaf.levelRestrict X n).obj H) ⟶
      (LAdicSheaf.levelRestrict X' n).obj ((LAdicSheaf.levelPullback g n).obj H) :=
  ((LAdicSheaf.levelAdjunction g (n + 1)).homEquiv _ _).symm
    ((LAdicSheaf.levelRestrict X n).map ((LAdicSheaf.levelAdjunction g n).unit.app H) ≫
      (LAdicSheaf.levelPushforwardRestrictIso g n).inv.app _)

variable [IsNoetherian X.1] [IsNoetherian X'.1]

omit [AlgebraicGeometry.IsNoetherian X'.1] in
/-- The transition maps of `g⁻¹F` are the inverse images of those of `F` followed by the
comparison of inverse image with restriction of scalars. -/
lemma inverseImageTransition_eq (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    LAdicSheaf.inverseImageTransition g F n =
      (LAdicSheaf.levelPullback g (n + 1)).map (F.transition n) ≫
        levelPullbackRestrict B g ℓ n (F.level n) := by
  rw [LAdicSheaf.inverseImageTransition, levelPullbackRestrict,
    ← Adjunction.homEquiv_naturality_left_symm]

/-- Rearranging the adjoint form of the change of level; stated on variables. -/
private lemma level_change_chain {D : Type*} [Category* D] {O₀ O₁ O₂ O₃ O₄ P₁ P₂ : D}
    {ηA : O₀ ⟶ O₁} {x₁ : O₁ ⟶ O₂} {y : O₂ ⟶ O₃} {z : O₃ ⟶ O₄} {r₁ : O₀ ⟶ O₂} {w : O₀ ⟶ O₃}
    {ι : O₀ ⟶ P₁} {r₀ : P₁ ⟶ O₄} {ηB : P₁ ⟶ P₂} {q : O₁ ⟶ P₂} {x₀ : P₂ ⟶ O₄}
    (U₁ : r₁ = ηA ≫ x₁) (K : r₁ ≫ y = w) (N : w ≫ z = ι ≫ r₀) (Nη : ι ≫ ηB = ηA ≫ q)
    (U₀ : r₀ = ηB ≫ x₀) : ηA ≫ x₁ ≫ y ≫ z = ηA ≫ q ≫ x₀ := by
  rw [← reassoc_of% U₁, reassoc_of% K, N, U₀, reassoc_of% Nη]

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.1] [AlgebraicGeometry.IsNoetherian X'.1] in
/-- **The comparisons of inverse image with restriction of scalars are compatible with the change
of level.**  Restricting scalars from `ℤ/ℓⁿ⁺²` to `ℤ_ℓ` through `ℤ/ℓⁿ⁺¹` or directly gives the
same comparison `g⁻¹ ∘ res ⟶ res ∘ g⁻¹`.  Both sides are maps out of an inverse image, and their
adjoints are both the restriction of scalars of the unit. -/
lemma padicRestrictInverseImage_levelPullbackRestrict (n : ℕ)
    (H : FiniteLevelSheaf.{u, u + 1} B X ℓ n) :
    (padicRestrictInverseImage B g ℓ (n + 1)).app ((LAdicSheaf.levelRestrict X n).obj H) ≫
        (padicRestrict B ℓ X' (n + 1)).map (levelPullbackRestrict B g ℓ n H) ≫
        (padicRestrictLevel B ℓ X' n).app ((LAdicSheaf.levelPullback g n).obj H) =
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPullback (ModuleCat.{u + 1} ℤ_[ℓ])
          (SmallEtale.topology B X.1 X.property) (SmallEtale.topology B X'.1 X'.property)).map
          ((padicRestrictLevel B ℓ X n).app H) ≫
        (padicRestrictInverseImage B g ℓ n).app H := by
  apply ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafAdjunctionContinuous
    (ModuleCat.{u + 1} ℤ_[ℓ]) (SmallEtale.topology B X.1 X.property)
    (SmallEtale.topology B X'.1 X'.property)).homEquiv _ _ |>.injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have U₁ := coefficientSheafPullbackTwoSquare_unit (AlgebraicGeometry.smallEtaleBaseChange B g)
    (SmallEtale.topology B X.1 X.property) (SmallEtale.topology B X'.1 X'.property)
    (ModuleCat.restrictScalars.{u + 1, 0, 0} (PadicInt.toZModPow (p := ℓ) (n + 1 + 1)))
    ((LAdicSheaf.levelRestrict X n).obj H)
  have U₀ := coefficientSheafPullbackTwoSquare_unit (AlgebraicGeometry.smallEtaleBaseChange B g)
    (SmallEtale.topology B X.1 X.property) (SmallEtale.topology B X'.1 X'.property)
    (ModuleCat.restrictScalars.{u + 1, 0, 0} (PadicInt.toZModPow (p := ℓ) (n + 1))) H
  have k : (LAdicSheaf.levelAdjunction g (n + 1)).unit.app ((LAdicSheaf.levelRestrict X n).obj H) ≫
      (LAdicSheaf.levelPushforward g (n + 1)).map (levelPullbackRestrict B g ℓ n H) =
      (LAdicSheaf.levelRestrict X n).map ((LAdicSheaf.levelAdjunction g n).unit.app H) ≫
        (LAdicSheaf.levelPushforwardRestrictIso g n).inv.app _ :=
    ((LAdicSheaf.levelAdjunction g (n + 1)).homEquiv_unit _ _ _).symm.trans
      (Equiv.apply_symm_apply _ _)
  have K : (padicRestrict B ℓ X (n + 1)).map
        ((LAdicSheaf.levelAdjunction g (n + 1)).unit.app ((LAdicSheaf.levelRestrict X n).obj H)) ≫
      (padicRestrict B ℓ X (n + 1)).map
        ((LAdicSheaf.levelPushforward g (n + 1)).map (levelPullbackRestrict B g ℓ n H)) =
      (padicRestrict B ℓ X (n + 1)).map
        ((LAdicSheaf.levelRestrict X n).map ((LAdicSheaf.levelAdjunction g n).unit.app H)) := by
    rw [← Functor.map_comp, k]
    congr 1
  have N := (padicRestrictLevel B ℓ X n).naturality ((LAdicSheaf.levelAdjunction g n).unit.app H)
  have Nη := ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafAdjunctionContinuous
    (ModuleCat.{u + 1} ℤ_[ℓ]) (SmallEtale.topology B X.1 X.property)
    (SmallEtale.topology B X'.1 X'.property)).unit.naturality ((padicRestrictLevel B ℓ X n).app H)
  exact level_change_chain U₁ K N Nη U₀

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.1] [AlgebraicGeometry.IsNoetherian X'.1] in
/-- **The identification of the levels is compatible with the change of level.** -/
lemma padicLevelInverseImageIso_levelRestrict (n : ℕ) (H : FiniteLevelSheaf.{u, u + 1} B X ℓ n) :
    (padicLevelInverseImageIso B g ℓ (n + 1) ((LAdicSheaf.levelRestrict X n).obj H)).hom ≫
        (padicSheafEquiv B ℓ X').map
          ((padicRestrict B ℓ X' (n + 1)).map (levelPullbackRestrict B g ℓ n H) ≫
            (padicRestrictLevel B ℓ X' n).app ((LAdicSheaf.levelPullback g n).obj H)) =
      (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map g)).map
          ((padicSheafEquiv B ℓ X).map ((padicRestrictLevel B ℓ X n).app H)) ≫
        (padicLevelInverseImageIso B g ℓ n H).hom := by
  have h₁ := (sheafEquivPullbackBaseChangeIso B g (ModuleCat.{u + 1} ℤ_[ℓ])
      (etaleModuleInverseImageAdj.{u, 0} ℤ_[ℓ] (B.inclusion.map g))
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafAdjunctionContinuous
        (ModuleCat.{u + 1} ℤ_[ℓ]) _ _)).hom.naturality ((padicRestrictLevel B ℓ X n).app H)
  dsimp only [Functor.comp_map, Functor.comp_obj] at h₁
  simp only [padicLevelInverseImageIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, asIso_hom,
    Category.assoc]
  rw [reassoc_of% h₁, ← Functor.map_comp, ← Functor.map_comp,
    padicRestrictInverseImage_levelPullbackRestrict]

/-- **The identification of the levels is compatible with the transition maps**: under
`(g⁻¹F)ₙ ≅ g⁻¹(Fₙ)`, the transition maps of `g⁻¹F` are the inverse images of those of `F`. -/
theorem padicLevelInverseImageIso_transition (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map g)).map
        ((padicSheafEquiv B ℓ X).map (LAdicSheaf.padicTransition B X ℓ F n)) ≫
      (padicLevelInverseImageIso B g ℓ n (F.level n)).hom =
    (padicLevelInverseImageIso B g ℓ (n + 1) (F.level (n + 1))).hom ≫
      (padicSheafEquiv B ℓ X').map
        (LAdicSheaf.padicTransition B X' ℓ (LAdicSheaf.inverseImage g F) n) := by
  have h := padicLevelInverseImageIso_hom_naturality B g ℓ (n + 1) (F.transition n)
  change (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map g)).map
        ((padicSheafEquiv B ℓ X).map ((padicRestrict B ℓ X (n + 1)).map (F.transition n) ≫
          (padicRestrictLevel B ℓ X n).app (F.level n))) ≫ _ =
    _ ≫ (padicSheafEquiv B ℓ X').map ((padicRestrict B ℓ X' (n + 1)).map
        (LAdicSheaf.inverseImageTransition g F n) ≫
          (padicRestrictLevel B ℓ X' n).app ((LAdicSheaf.levelPullback g n).obj (F.level n)))
  have hs := padicLevelInverseImageIso_levelRestrict B g ℓ n (F.level n)
  rw [inverseImageTransition_eq]
  simp only [Functor.map_comp, Category.assoc] at hs ⊢
  rw [← hs, reassoc_of% h]

end Stacks.EtaleCohomology

end
