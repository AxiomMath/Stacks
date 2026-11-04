module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicIntegralDirectImageCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteEtalePushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.SmallEtaleSitePresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimitCategory
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantIsConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Trace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.Presentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.Transition

/-!
# Direct image of lisse sheaves along a finite étale morphism

Let `π : X ⟶ Y` be a finite étale morphism of a big étale site. The direct image along `π` of a
sheaf of `Λ`-modules on `X_étale` which is locally constant of finite type is again locally
constant of finite type ([Tag 095B](https://stacks.math.columbia.edu/tag/095B)), on the small
étale sites of the big étale site: the bounded direct image is Mathlib's one read through
`AlgebraicGeometry.SmallEtale.sheafEquiv`
(`AlgebraicGeometry.SmallEtale.sheafEquivFunctorPushforwardBaseChangeIso`), where Tag 095B is
`Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_finiteEtalePushforward_modules`, and local
constancy of finite type transports along `sheafEquiv`.

Consequently, for an ℓ-adic sheaf `F` on `X` whose levels are locally constant of finite type
(for instance `ℱ_ρ`), the levels `π_* Fₙ` with the direct images of the transition maps form a
lisse ℓ-adic sheaf `π_* F` on `Y`. The reduction maps of `π_* F` are isomorphisms with no
compatibility between the adjunctions at different levels: the underlying map of the transition
of `F` exhibits `Fₙ` as the cokernel of `ℓⁿ⁺¹` on `Fₙ₊₁`, and `π_*`, which is a left adjoint for
`π` finite étale (`π_* ≅ π_!`, Tag 03S7), preserves that cokernel. The tower of levels of `π_* F`
is the direct image of that of `F`, the input of the comparison of `Hⁱ_c` along an integral
morphism of compactifications
(`Stacks.EtaleCohomology.LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIntegralIso`).

This is the step of the reduction of the weight bound of Weil II on curves (Weil II 3.3) to opens
of the affine line in which a lisse sheaf on a finite étale cover is pushed down.

## Main definitions

* `AlgebraicGeometry.SmallEtale.LAdicSheaf.levelDirectImageAdjunction`: `π_* ⊣ π⁻¹` at each level.
* `AlgebraicGeometry.SmallEtale.LAdicSheaf.directImage`: the ℓ-adic sheaf `π_* F`.
* `Stacks.EtaleCohomology.LAdicSheaf.padicTowerFiniteEtaleDirectImageIso`: its tower of levels.

## Main results

* `Stacks.EtaleCohomology.isFiniteTypeLocallyConstant_smallPushforward_of_isFinite_of_etale`.
* `AlgebraicGeometry.SmallEtale.LAdicSheaf.isIso_directImage_scalarReductionMap`.
* `AlgebraicGeometry.SmallEtale.LAdicSheaf.directImage_isLisse`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (π : X ⟶ Y) [IsFinite (B.inclusion.map π)]
  [Etale (B.inclusion.map π)] (Λ : Type) [Ring Λ]
  [∀ V : SmallEtale B X.1 X.property,
    HasWeakSheafify ((SmallEtale.topology B X.1 X.property).over V) (ModuleCat.{u + 1} Λ)]
  [∀ V : SmallEtale B Y.1 Y.property,
    HasWeakSheafify ((SmallEtale.topology B Y.1 Y.property).over V) (ModuleCat.{u + 1} Λ)]

/-- **Tag 095B on the small étale sites of a big étale site**: the direct image along a finite
étale morphism of a sheaf of `Λ`-modules which is locally constant of finite type is locally
constant of finite type. -/
public theorem isFiniteTypeLocallyConstant_smallPushforward_of_isFinite_of_etale
    (G : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} Λ))
    (hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B X.1 X.property)
      G) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B Y.1 Y.property)
      ((B.smallPushforward π (ModuleCat.{u + 1} Λ)).obj G) := by
  rw [← isFiniteTypeLocallyConstant_sheafEquiv_functor_iff.{u, 0} B Y Λ]
  have h1 := (isFiniteTypeLocallyConstant_sheafEquiv_functor_iff.{u, 0} B X Λ G).2 hG
  have h2 :=
    @Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_finiteEtalePushforward_modules.{u, 0, 0}
      X.obj Y.obj (B.inclusion.map π) _ _ Λ _
      (fun W => hasWeakSheafify_etaleSiteOver_moduleCat B X Λ W)
      (fun W => hasWeakSheafify_etaleSiteOver_moduleCat B Y Λ W) _ h1
  exact @Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant.of_iso Λ _ _ _ _
    (fun W => hasWeakSheafify_etaleSiteOver_moduleCat B Y Λ W) _ _
    ((SmallEtale.sheafEquivFunctorPushforwardBaseChangeIso B π (ModuleCat.{u + 1} Λ)).app G).symm h2

end Stacks.EtaleCohomology

namespace AlgebraicGeometry.SmallEtale.LAdicSheaf

variable {B : BigEtaleSite.{u}} {X Y : B.Scheme} (π : X ⟶ Y) [IsFinite (B.inclusion.map π)]
  [hπ : Etale (B.inclusion.map π)] {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- `π : X ⟶ Y`, finite étale, as an object of the small étale site of `Y`. -/
abbrev finiteEtaleObj : SmallEtale B Y.obj Y.property := ⟨Over.mk π, hπ⟩

/-- The structure morphism of `finiteEtaleObj π` is finite, since it is `π` itself. -/
instance : IsFinite (B.inclusion.map (finiteEtaleObj π).obj.hom) :=
  inferInstanceAs (IsFinite (B.inclusion.map π))

/-- The restriction `π⁻¹` at level `n`, along the postcomposition functor `X_ét ⟶ Y_ét`. -/
public abbrev levelRestriction (n : ℕ) :
    FiniteLevelSheaf.{u, u + 1} B Y ℓ n ⥤ FiniteLevelSheaf.{u, u + 1} B X ℓ n :=
  moduleRestriction.{u, 0} B Y.obj Y.property (finiteEtaleObj π) (ZMod (ℓ ^ (n + 1)))

/-- **`π_* ⊣ π⁻¹` at level `n`** for finite étale `π`: the extension-by-zero adjunction read
through `π_! ≅ π_*` (Tag 03S7, `AlgebraicGeometry.moduleExtensionByZeroIsoPushforward`). -/
public def levelDirectImageAdjunction (n : ℕ) :
    levelPushforward π n ⊣ levelRestriction (ℓ := ℓ) π n :=
  (moduleExtensionByZeroAdjunction.{u, 0} B Y.obj Y.property (finiteEtaleObj π)
    (ZMod (ℓ ^ (n + 1)))).ofNatIsoLeft
    (moduleExtensionByZeroIsoPushforward.{u, 0} B Y.obj Y.property (finiteEtaleObj π)
      (ZMod (ℓ ^ (n + 1))))

/-- The restriction commutes with restriction of scalars (on the nose). -/
public def levelRestrictionRestrictIso (n : ℕ) :
    levelRestrict Y n ⋙ levelRestriction π (n + 1) ≅
      levelRestriction (ℓ := ℓ) π n ⋙ levelRestrict X n :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun _ => rfl

attribute [local instance] Stacks.EtaleCohomology.underlyingLevelFunctor_additive
  Stacks.EtaleCohomology.underlyingLevelFunctor_isLeftAdjoint

variable [IsNoetherian X.obj] [IsNoetherian Y.obj]

/-- The transition maps of `π_* F`: the direct images of those of `F` (pushforward commutes with
restriction of scalars on the nose). -/
public abbrev directImageTransition (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    (levelPushforward π (n + 1)).obj (F.level (n + 1)) ⟶
      (levelRestrict Y n).obj ((levelPushforward π n).obj (F.level n)) :=
  (levelPushforward π (n + 1)).map (F.transition n)

omit [IsNoetherian Y.obj] in
/-- **The reduction maps of `π_* F` are isomorphisms** for finite étale `π`: the underlying map of
the transition of `F` exhibits `Fₙ` as `Fₙ₊₁/ℓⁿ⁺¹`, and `π_*`, a left adjoint
(`AlgebraicGeometry.SmallEtale.LAdicSheaf.levelDirectImageAdjunction`), followed by forgetting the
module structure, preserves that cokernel. -/
public theorem isIso_directImage_scalarReductionMap (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    IsIso (FiniteLevelSheaf.scalarReductionMap B Y ℓ n _ _ (directImageTransition π F n)) := by
  have : (levelPushforward (ℓ := ℓ) π (n + 1)).IsLeftAdjoint :=
    (levelDirectImageAdjunction π (n + 1)).isLeftAdjoint
  have : (levelPushforward (ℓ := ℓ) π (n + 1)).Additive := { map_add := by intros; rfl }
  have : (levelPushforward (ℓ := ℓ) π (n + 1) ⋙
      Stacks.EtaleCohomology.underlyingLevelFunctor B Y ℓ (n + 1)).IsLeftAdjoint := inferInstance
  have h := CategoryTheory.mapNsmulCokernel
    (levelPushforward π (n + 1) ⋙ Stacks.EtaleCohomology.underlyingLevelFunctor B Y ℓ (n + 1))
    (ℓ ^ (n + 1)) (F.transition n) (Stacks.EtaleCohomology.LAdicSheaf.transition_condition F n)
    (Stacks.EtaleCohomology.LAdicSheaf.transition_isCokernel F n)
  exact Stacks.EtaleCohomology.LAdicSheaf.reduction_isIso_of_underlying_cokernel B Y ℓ n _ _ _ _ h

/-- **The direct image `π_* F` of an ℓ-adic sheaf along a finite étale `π`**, for `F` whose levels
are locally constant of finite type (for instance a lisse sheaf `ℱ_ρ`): level `n` is `π_* Fₙ`. -/
public def directImage (F : LAdicSheaf.{u, u + 1} B X ℓ)
    (hF : ∀ n, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ (n + 1)))
      (SmallEtale.topology B X.1 X.property) (F.level n)) : LAdicSheaf.{u, u + 1} B Y ℓ where
  level n := (levelPushforward π n).obj (F.level n)
  constructible n := isConstructibleModuleSheaf_of_isFiniteTypeLocallyConstant B Y _ _
    (Stacks.EtaleCohomology.isFiniteTypeLocallyConstant_smallPushforward_of_isFinite_of_etale B π
      (ZMod (ℓ ^ (n + 1))) _ (hF n))
  transition := directImageTransition π F
  reduction_isIso := isIso_directImage_scalarReductionMap π F

/-- Level `n` of `π_* F` is the direct image `π_* Fₙ` of level `n` of `F` (by definition). -/
public theorem directImage_level (F : LAdicSheaf.{u, u + 1} B X ℓ) (hF) (n : ℕ) :
    (directImage π F hF).level n = (levelPushforward π n).obj (F.level n) :=
  rfl

/-- The levels of `π_* F` are locally constant of finite type. -/
public theorem isFiniteTypeLocallyConstant_directImage_level (F : LAdicSheaf.{u, u + 1} B X ℓ) (hF)
    (n : ℕ) : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ (n + 1)))
      (SmallEtale.topology B Y.1 Y.property) ((directImage π F hF).level n) :=
  Stacks.EtaleCohomology.isFiniteTypeLocallyConstant_smallPushforward_of_isFinite_of_etale B π
    (ZMod (ℓ ^ (n + 1))) _ (hF n)

/-- **`π_* F` is lisse**: its levels are locally constant (of finite type). -/
public theorem directImage_isLisse (F : LAdicSheaf.{u, u + 1} B X ℓ) (hF) :
    (directImage π F hF).IsLisse := fun n => by
  refine ⟨fun U => ?_⟩
  obtain ⟨I, V, f, hf, hdata⟩ := isFiniteTypeLocallyConstant_directImage_level π F hF n U
  refine ⟨I, V, f, hf, fun i => ?_⟩
  obtain ⟨E, -, hiso⟩ := hdata i
  exact ⟨E, hiso⟩

end AlgebraicGeometry.SmallEtale.LAdicSheaf


/-! ### The tower of levels of `π_* F` -/

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable {B : BigEtaleSite.{u}} (ℓ : ℕ) [Fact ℓ.Prime]
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
  {X Y : B.Scheme} [IsNoetherian X.obj] [IsNoetherian Y.obj] (π : X ⟶ Y)
  [IsFinite (B.inclusion.map π)] [Etale (B.inclusion.map π)]

/-- **The tower of levels of `π_* F` is the direct image of the tower of levels of `F`**, for a
finite étale `π`: the input of the comparison
`Stacks.EtaleCohomology.LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIntegralIso`. -/
public def LAdicSheaf.padicTowerFiniteEtaleDirectImageIso (F : LAdicSheaf.{u, u + 1} B X ℓ)
    (hF : ∀ n, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ (n + 1)))
      (SmallEtale.topology B X.1 X.property) (F.level n)) :
    LAdicSheaf.padicTower B Y ℓ (AlgebraicGeometry.SmallEtale.LAdicSheaf.directImage π F hF) ≅
      LAdicSheaf.padicTower B X ℓ F ⋙ etaleModuleDirectImage.{u, 0} ℤ_[ℓ] (B.inclusion.map π) :=
  LAdicSheaf.padicTowerDirectImageIso B ℓ π F _ (fun _ => Iso.refl _) (fun n => by
    simp only [Iso.refl_hom]
    rfl)

end Stacks.EtaleCohomology
