module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LevelCoinvariantsLimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTowerSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseCoefficientExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusElementDegree

/-!
# `H²_c(U_k̄, ℱ_τ ⊗ ℚ_ℓ)` from its finite levels

Let `U` be a curve over a finite field `k` with `q` elements, `τ : π₁(U, x̄) → GL_r(ℚ_ℓ)`
continuous with integral model `ρ` (`τ = P ρ P⁻¹` over `ℚ_ℓ`), `H` the geometric fundamental group
and `φ` an element of `π₁(U, x̄)`. This file reduces the identification

`H²_c(U_k̄, ℱ_τ ⊗ ℚ_ℓ) ≅ (ℚ_ℓ^r)_H`, with `π_U^* ↦ q · τ(φ)`,

of [Stacks, Tag 03VL] to its finite levels: if every level `H²_c(U_k̄, ℱ_{ρ,n+1})` is isomorphic,
compatibly with the geometric Frobenius and `q · ρ(φ)`, to the level coinvariants
`((ℤ/ℓ^{n+1})^r)_H`, and the transition maps of the inverse system `n ↦ H²_c(U_k̄, Fₙ)` are onto,
then the identification holds.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.nonempty_levelIsoSet_representationSheaf`: a level
  isomorphism with the level coinvariants gives one with the quotient of `(ℤ_ℓ^r)_H`.
* `Stacks.EtaleCohomology.LAdicSheaf.exists_linearEquiv_coinvariants_of_levels`: the reduction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Representation
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
  ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.1] [Fact ℓ.Prime]

variable {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **`Hⁱ_c(X_k̄, Fₙ)` with `ℤ_ℓ`-coefficients is `Hⁱ_c(X_k̄, Fₙ)` with `ℤ/ℓⁿ⁺¹`-coefficients**,
read as a `ℤ_ℓ`-module. -/
def LAdicSheaf.geometricCohomologyLevelIso (F : LAdicSheaf B X ℓ) (i : ℤ) (n : ℕ) :
    (LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F i).obj (op n) ≅
      (ModuleCat.restrictScalars.{u + 1} (PadicInt.toZModPow (n + 1))).obj
        (compactSupportFrobeniusCohomologyGroup.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
          (LAdicSheaf.levelComplex B X ℓ F n) i) :=
  (compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] f j kbar ⋙
      DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) i).mapIso
      (LAdicSheaf.padicCoefficientComplexLevelIso B X ℓ F n) ≪≫
    (compactSupportFrobeniusCohomologyGroupRestrictScalarsIso (PadicInt.toZModPow (n + 1)) f j kbar
      (LAdicSheaf.levelComplex B X ℓ F n) i).symm

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- The level comparison carries `π_X^*` to `π_X^*`. -/
theorem LAdicSheaf.geometricCohomologyLevelIso_frobenius (F : LAdicSheaf B X ℓ) (i : ℤ) (n : ℕ) :
    (LAdicSheaf.geometricCompactlySupportedCohomologySystemPullback B X ℓ f j kbar F i
        (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard)).app (op n) ≫
      (LAdicSheaf.geometricCohomologyLevelIso B X ℓ f j kbar F i n).hom =
    (LAdicSheaf.geometricCohomologyLevelIso B X ℓ f j kbar F i n).hom ≫
      (ModuleCat.restrictScalars.{u + 1} (PadicInt.toZModPow (n + 1))).map
        (canonicalCompactSupportFrobeniusGroup.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar p q hcard
          (LAdicSheaf.levelComplex B X ℓ F n) i) := by
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) i
  have h₁ := (H.map_comp _ _).symm.trans ((congrArg H.map
    ((canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard).naturality
      (LAdicSheaf.padicCoefficientComplexLevelIso B X ℓ F n).hom)).trans (H.map_comp _ _))
  exact endo_transport_aux _ _ _ h₁ _ _
    (restrictScalars_canonicalCompactSupportFrobeniusGroup (PadicInt.toZModPow (n + 1)) f j
      kbar p q hcard (LAdicSheaf.levelComplex B X ℓ F n) i)

/-! ### The quotients of the integral coinvariants -/

section Quotient

variable {Γ : Type*} [Group Γ] (H : Subgroup Γ) [H.Normal] {r : ℕ} (ρ : Γ →* GL (Fin r) ℤ_[ℓ])

/-- Reduction of the lifted coinvariants `(ℤ_ℓ^r)_H` to the level coinvariants
`((ℤ/ℓ^{n+1})^r)_H`, as a `ℤ_ℓ`-linear map into the restriction of scalars. -/
def integralCoinvariantsLevelMap (n : ℕ) :
    (integralCoinvariantsModule.{u + 1} H ρ : ModuleCat.{u + 1} ℤ_[ℓ]) →ₗ[ℤ_[ℓ]]
      (ModuleCat.restrictScalars.{u + 1} (PadicInt.toZModPow (n + 1))).obj
        (ModuleCat.of (ZMod (ℓ ^ (n + 1))) (ULift.{u + 1} (levelCoinvariants H ρ (n + 1)))) where
  toFun x := ULift.up (integralCoinvariantsReduction H ρ (n + 1) x.down)
  map_add' x y := ULift.ext (map_add (integralCoinvariantsReduction H ρ (n + 1)) x.down y.down)
  map_smul' c x := ULift.ext
    (LinearMap.map_smulₛₗ (integralCoinvariantsReduction H ρ (n + 1)) c x.down)

omit [H.Normal] in
/-- `integralCoinvariantsLevelMap` is the reduction `integralCoinvariantsReduction` on
underlying elements. -/
theorem integralCoinvariantsLevelMap_apply (n : ℕ) (x : integralCoinvariantsModule.{u + 1} H ρ) :
    (integralCoinvariantsLevelMap ℓ H ρ n x).down =
      integralCoinvariantsReduction H ρ (n + 1) x.down :=
  rfl

omit [H.Normal] in
open Pointwise in
/-- The kernel of `integralCoinvariantsLevelMap` is `ℓ^{n+1} (ℤ_ℓ^r)_H`. -/
theorem ker_integralCoinvariantsLevelMap (n : ℕ) :
    LinearMap.ker (integralCoinvariantsLevelMap ℓ H ρ n) =
      padicIdeal ℓ ^ (n + 1) • (⊤ : Submodule ℤ_[ℓ] (integralCoinvariantsModule.{u + 1} H ρ)) := by
  let eU : ULift.{u + 1} (integralCoinvariants H ρ) ≃ₗ[ℤ_[ℓ]] integralCoinvariants H ρ :=
    ULift.moduleEquiv
  have : LinearMap.ker (integralCoinvariantsLevelMap ℓ H ρ n) =
      (LinearMap.ker (integralCoinvariantsReduction H ρ (n + 1))).comap eU.toLinearMap :=
    Submodule.ext fun x => ⟨fun h => congrArg ULift.down h, fun h => ULift.ext h⟩
  rw [this, ker_integralCoinvariantsReduction', Submodule.comap_equiv_eq_map_symm,
    Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]

omit [H.Normal] in
/-- `integralCoinvariantsLevelMap` is surjective. -/
theorem surjective_integralCoinvariantsLevelMap (n : ℕ) :
    Function.Surjective (integralCoinvariantsLevelMap ℓ H ρ n) := fun y => by
  obtain ⟨x, hx⟩ := surjective_integralCoinvariantsReduction H ρ (n + 1) y.down
  exact ⟨ULift.up x, ULift.ext hx⟩

/-- **`(ℤ_ℓ^r)_H / ℓ^{n+1} ≅ ((ℤ/ℓ^{n+1})^r)_H`.** -/
def integralCoinvariantsQuotientEquiv (n : ℕ) :
    (padicQuotientTower (integralCoinvariantsModule.{u + 1} H ρ : ModuleCat.{u + 1} ℤ_[ℓ])).obj
        (op n) ≃ₗ[ℤ_[ℓ]]
      (ModuleCat.restrictScalars.{u + 1} (PadicInt.toZModPow (n + 1))).obj
        (ModuleCat.of (ZMod (ℓ ^ (n + 1))) (ULift.{u + 1} (levelCoinvariants H ρ (n + 1)))) :=
  (Submodule.quotEquivOfEq _ _ (ker_integralCoinvariantsLevelMap ℓ H ρ n).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (surjective_integralCoinvariantsLevelMap ℓ H ρ n))

omit [H.Normal] in
/-- `integralCoinvariantsQuotientEquiv` sends the class of `x` to the reduction of `x`. -/
theorem integralCoinvariantsQuotientEquiv_mk (n : ℕ) (x : integralCoinvariantsModule.{u + 1} H ρ) :
    (integralCoinvariantsQuotientEquiv ℓ H ρ n (Submodule.Quotient.mk x)).down =
      integralCoinvariantsReduction H ρ (n + 1) x.down :=
  rfl

variable (φ : Γ) (c : ℕ)

/-- The quotient isomorphism carries `c · ρ(φ)` to `c · ρ(φ)`. -/
theorem integralCoinvariantsQuotientEquiv_end (n : ℕ)
    (x : (padicQuotientTower (integralCoinvariantsModule.{u + 1} H ρ :
      ModuleCat.{u + 1} ℤ_[ℓ])).obj (op n)) :
    (integralCoinvariantsQuotientEquiv ℓ H ρ n
        (((padicQuotientTowerMap (integralCoinvariantsModuleEnd H ρ φ (c : ℤ_[ℓ]))).app
          (op n)).hom x)).down =
      (c : ZMod (ℓ ^ (n + 1))) • levelCoinvariantsFrobenius H ρ φ (n + 1)
        (integralCoinvariantsQuotientEquiv ℓ H ρ n x).down := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change integralCoinvariantsReduction H ρ (n + 1)
      ((c : ℤ_[ℓ]) • coinvariantsFrobenius H ρ φ y.down) = _
  rw [LinearMap.map_smulₛₗ, integralCoinvariantsReduction_coinvariantsFrobenius, map_natCast]
  rfl

end Quotient

/-! ### The levels of `H²_c` of `ℱ_τ` -/

section Representation

variable [ConnectedSpace X.1] (x : GeometricPoint X.1) {r : ℕ}
  (τ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ]) (hτ : Continuous τ)
  [CompactSpace (EtaleFundamentalGroup X.1 x)]
  (H : Subgroup (EtaleFundamentalGroup X.1 x)) [H.Normal] (φ : EtaleFundamentalGroup X.1 x)

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- **A level isomorphism with the level coinvariants is one with the quotient of
`(ℤ_ℓ^r)_H`**: an isomorphism `H²_c(X_k̄, ℱ_{ρ,n+1}) ≅ ((ℤ/ℓ^{n+1})^r)_H` carrying `π_X^*` to
`q · ρ(φ)` gives an element of the set `levelIsoSet` of level isomorphisms. -/
theorem LAdicSheaf.nonempty_levelIsoSet_representationSheaf (n : ℕ)
    (e : compactSupportFrobeniusCohomologyGroup.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ (LAdicSheaf.representationSheaf B X x τ hτ) n) 2
        ≃ₗ[ZMod (ℓ ^ (n + 1))] levelCoinvariants H (integralModel τ hτ) (n + 1))
    (he : ∀ t, e ((canonicalCompactSupportFrobeniusGroup.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar p q
        hcard (LAdicSheaf.levelComplex B X ℓ (LAdicSheaf.representationSheaf B X x τ hτ) n)
          2).hom t) =
      ((p ^ q : ℕ) : ZMod (ℓ ^ (n + 1))) •
        levelCoinvariantsFrobenius H (integralModel τ hτ) φ (n + 1) (e t)) :
    Nonempty (levelIsoSet (integralCoinvariantsModule.{u + 1} H (integralModel τ hτ))
      (LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar
        (LAdicSheaf.representationSheaf B X x τ hτ) 2)
      (LAdicSheaf.geometricCompactlySupportedCohomologySystemPullback B X ℓ f j kbar
        (LAdicSheaf.representationSheaf B X x τ hτ) 2
        (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard))
      (integralCoinvariantsModuleEnd H (integralModel τ hτ) φ ((p ^ q : ℕ) : ℤ_[ℓ])) n) := by
  let F := LAdicSheaf.representationSheaf B X x τ hτ
  let I := LAdicSheaf.geometricCohomologyLevelIso B X ℓ f j kbar F 2 n
  let e' := e.trans (ULift.moduleEquiv.{0, 0, u + 1} (R := ZMod (ℓ ^ (n + 1)))).symm
  let E2 := (ModuleCat.restrictScalars.{u + 1} (PadicInt.toZModPow (n + 1))).mapIso
    e'.toModuleIso
  let R := integralCoinvariantsQuotientEquiv ℓ H (integralModel τ hτ) n
  refine ⟨⟨(I ≪≫ E2).toLinearEquiv.trans R.symm, fun t => ?_⟩⟩
  apply R.injective
  apply ULift.ext
  rw [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, LinearEquiv.trans_apply,
    integralCoinvariantsQuotientEquiv_end, LinearEquiv.apply_symm_apply]
  have hI : I.hom.hom ((((LAdicSheaf.geometricCompactlySupportedCohomologySystemPullback B X ℓ f j
      kbar F 2 (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard)).app
        (op n)).hom t)) =
      (canonicalCompactSupportFrobeniusGroup.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar p q hcard
        (LAdicSheaf.levelComplex B X ℓ F n) 2).hom (I.hom.hom t) :=
    congrArg (fun g => g.hom t)
      (LAdicSheaf.geometricCohomologyLevelIso_frobenius B X ℓ f j kbar p q hcard F 2 n)
  exact (congrArg e hI).trans (he (I.hom.hom t))

open Pointwise in
/-- **The kernel of a transition map of the levels is `ℓ^{n+1}`**: when the transitions are onto
and every level is isomorphic to the corresponding quotient of a finite `ℤ_ℓ`-module `M`, the
kernel of the transition `Sₙ₊₁ → Sₙ` is `ℓ^{n+1} Sₙ₊₁`. -/
theorem ker_map_eq_of_levelIsoSet (M : ModuleCat.{u + 1} ℤ_[ℓ]) [Module.Finite ℤ_[ℓ] M] (ψ : M ⟶ M)
    (S : ℕᵒᵖ ⥤ ModuleCat.{u + 1} ℤ_[ℓ]) (σ : S ⟶ S)
    (hsurj : ∀ n, Function.Surjective (S.map (homOfLE (Nat.le_add_right n 1)).op).hom)
    (hlev : ∀ n, Nonempty (levelIsoSet M S σ ψ n)) (n : ℕ) :
    LinearMap.ker (S.map (homOfLE (Nat.le_add_right n 1)).op).hom =
      padicIdeal ℓ ^ (n + 1) • (⊤ : Submodule ℤ_[ℓ] (S.obj (op (n + 1)))) := by
  classical
  let t := (S.map (homOfLE (Nat.le_add_right n 1)).op).hom
  let I := padicIdeal ℓ ^ (n + 1)
  obtain ⟨e₁⟩ := hlev (n + 1)
  obtain ⟨e₀⟩ := hlev n
  have hkill : I • (⊤ : Submodule ℤ_[ℓ] (S.obj (op (n + 1)))) ≤ LinearMap.ker t := by
    rw [Submodule.smul_le]
    intro c hc s _
    rw [LinearMap.mem_ker, map_smul]
    apply e₀.1.injective
    rw [map_smul, map_zero]
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (e₀.1 (t s))
    rw [← hy]
    exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.smul_mem_smul hc Submodule.mem_top)
  refine le_antisymm ?_ hkill
  have := finite_padicQuotientTower_obj (M := M)
  have : Finite (S.obj (op (n + 1))) := Finite.of_equiv _ e₁.1.symm.toEquiv
  have : Finite (S.obj (op n)) := Finite.of_equiv _ e₀.1.symm.toEquiv
  let tbar := (I • (⊤ : Submodule ℤ_[ℓ] (S.obj (op (n + 1))))).liftQ t hkill
  have hsurjbar : Function.Surjective tbar := fun y => by
    obtain ⟨s, rfl⟩ := hsurj n y
    exact ⟨Submodule.Quotient.mk s, rfl⟩
  have hcard : Nat.card (S.obj (op (n + 1)) ⧸ I • (⊤ : Submodule ℤ_[ℓ] (S.obj (op (n + 1))))) =
      Nat.card (S.obj (op n)) := by
    have h₁ : Nat.card (S.obj (op (n + 1)) ⧸ I • (⊤ : Submodule ℤ_[ℓ] (S.obj (op (n + 1))))) =
        Nat.card (((padicQuotientTower M).obj (op (n + 1))) ⧸
          I • (⊤ : Submodule ℤ_[ℓ] ((padicQuotientTower M).obj (op (n + 1))))) := by
      refine Nat.card_congr (Submodule.Quotient.equiv _ _ e₁.1 ?_).toEquiv
      rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
    have h₂ : Nat.card (((padicQuotientTower M).obj (op (n + 1))) ⧸
          I • (⊤ : Submodule ℤ_[ℓ] ((padicQuotientTower M).obj (op (n + 1))))) =
        Nat.card ((padicQuotientTower M).obj (op n)) := by
      refine Nat.card_congr ((Submodule.quotEquivOfEq _ _
        (ker_padicQuotientTransition (M := M) n).symm).trans
        (LinearMap.quotKerEquivOfSurjective _ fun z => ?_)).toEquiv
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      exact ⟨Submodule.Quotient.mk y, rfl⟩
    rw [h₁, h₂]
    exact Nat.card_congr e₀.1.symm.toEquiv
  have hinj : Function.Injective tbar := by
    have : Finite (S.obj (op (n + 1)) ⧸ I • (⊤ : Submodule ℤ_[ℓ] (S.obj (op (n + 1))))) :=
      Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
    exact (Function.Surjective.bijective_of_nat_card_le hsurjbar hcard.le).1
  intro s hs
  exact (Submodule.Quotient.mk_eq_zero _).1 (hinj (by rwa [map_zero]))

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
include hτ in
/-- **`H²_c(X_k̄, ℱ_τ ⊗ ℚ_ℓ) ≅ (ℚ_ℓ^r)_H`, carrying `π_X^*` to `q · τ(φ)`, from the finite
levels**: given, at every level, an isomorphism `H²_c(X_k̄, ℱ_{ρ,n+1}) ≅ ((ℤ/ℓ^{n+1})^r)_H`
carrying the geometric Frobenius to `q · ρ(φ)`, and the surjectivity of the transitions of
`n ↦ H²_c(X_k̄, Fₙ)`. -/
theorem LAdicSheaf.exists_linearEquiv_coinvariants_of_levels
    (hlev : ∀ n : ℕ, ∃ e : compactSupportFrobeniusCohomologyGroup.{u, 0} (ZMod (ℓ ^ (n + 1))) f j
        kbar (LAdicSheaf.levelComplex B X ℓ (LAdicSheaf.representationSheaf B X x τ hτ) n) 2
        ≃ₗ[ZMod (ℓ ^ (n + 1))] levelCoinvariants H (integralModel τ hτ) (n + 1),
      ∀ t, e ((canonicalCompactSupportFrobeniusGroup.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar p q hcard
          (LAdicSheaf.levelComplex B X ℓ (LAdicSheaf.representationSheaf B X x τ hτ) n) 2).hom t) =
        ((p ^ q : ℕ) : ZMod (ℓ ^ (n + 1))) •
          levelCoinvariantsFrobenius H (integralModel τ hτ) φ (n + 1) (e t))
    (hsurj : ∀ n, Function.Surjective ((LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ
      f j kbar (LAdicSheaf.representationSheaf B X x τ hτ) 2).map
        (homOfLE (Nat.le_add_right n 1)).op).hom) :
    ∃ e : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
          (LAdicSheaf.representationSheaf B X x τ hτ) 2 ≃ₗ[ℚ_[ℓ]]
        Coinvariants ((matrixRepresentation τ).comp H.subtype),
      ∀ v, e ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
          (LAdicSheaf.representationSheaf B X x τ hτ) 2).hom v) =
        ((p ^ q : ℕ) : ℚ_[ℓ]) • coinvariantsFrobenius H τ φ (e v) := by
  let F := LAdicSheaf.representationSheaf B X x τ hτ
  let ρ := integralModel τ hτ
  let M : ModuleCat.{u + 1} ℤ_[ℓ] := integralCoinvariantsModule H ρ
  have : Module.Finite ℤ_[ℓ] M := Module.Finite.equiv ULift.moduleEquiv.symm
  let S := LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F 2
  let σ := LAdicSheaf.geometricCompactlySupportedCohomologySystemPullback B X ℓ f j kbar F 2
    (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard)
  let ψ := integralCoinvariantsModuleEnd H ρ φ ((p ^ q : ℕ) : ℤ_[ℓ])
  have hset : ∀ n, Nonempty (levelIsoSet M S σ ψ n) := fun n => (hlev n).elim
    (LAdicSheaf.nonempty_levelIsoSet_representationSheaf B X ℓ f j kbar p q hcard x τ hτ H φ n)
  obtain ⟨E, hE⟩ := exists_iso_padicQuotientTower_of_levels ψ S σ hsurj
    (ker_map_eq_of_levelIsoSet ℓ M ψ S σ hsurj hset) hset
  let P := (exists_conj_integral τ hτ).choose
  have hP : ∀ g, rationalGL ρ g = P⁻¹ * τ g * P := map_integralModel τ hτ
  obtain ⟨e, he⟩ := exists_extendScalars_limit_linearEquiv_coinvariants.{u + 1} H ρ φ τ P hP
    ((p ^ q : ℕ) : ℤ_[ℓ]) S E σ hE
  exact ⟨e, fun v => by rw [← map_natCast (algebraMap ℤ_[ℓ] ℚ_[ℓ])]; exact he v⟩

end Representation

end Stacks.EtaleCohomology

end
