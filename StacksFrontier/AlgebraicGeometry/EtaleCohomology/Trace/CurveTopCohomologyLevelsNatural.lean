module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopCohomologyLevels
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LevelCoinvariantsLimitFamily
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoinvariantsMatrixMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTwistedTower

/-!
# `H²_c(U_k̄, ℱ_τ ⊗ ℚ_ℓ)` from its finite levels, naturally in the intertwiners

A version of `Stacks.EtaleCohomology.LAdicSheaf.exists_linearEquiv_coinvariants_of_levels` for
level isomorphisms which are moreover natural in a family of integral intertwiners `A a` of the
integral model `ρ` of `τ`: the resulting identification `H²_c(X_k̄, ℱ_τ ⊗ ℚ_ℓ) ≅ (ℚ_ℓ^r)_H` also
carries the endomorphism of `ℱ_τ` induced by `A a` to the endomorphism of the coinvariants of
`P A_a P⁻¹`, where `τ = P ρ P⁻¹`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.geometricCohomologyLevelIso_map`: the level comparison is
  natural in the morphisms of ℓ-adic sheaves.
* `Stacks.EtaleCohomology.LAdicSheaf.exists_linearEquiv_coinvariants_of_levels_natural`:
  `H²_c(X_k̄, ℱ_τ ⊗ ℚ_ℓ) ≅ (ℚ_ℓ^r)_H`, compatibly with the Frobenius and with the endomorphisms of
  the intertwiners, from level isomorphisms natural in the intertwiners.
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

/-- **The level comparison is natural in the morphisms of ℓ-adic sheaves.** -/
theorem LAdicSheaf.geometricCohomologyLevelIso_map (F : LAdicSheaf B X ℓ) (ψ : F ⟶ F) (i : ℤ)
    (n : ℕ) :
    (LAdicSheaf.geometricCompactlySupportedCohomologySystemMap f j kbar ψ i).app (op n) ≫
        (LAdicSheaf.geometricCohomologyLevelIso B X ℓ f j kbar F i n).hom =
      (LAdicSheaf.geometricCohomologyLevelIso B X ℓ f j kbar F i n).hom ≫
        (ModuleCat.restrictScalars.{u + 1} (PadicInt.toZModPow (n + 1))).map
          ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) i).map
            ((compactSupportFrobeniusFunctor.{u, 0} _ f j kbar).map
              (LAdicSheaf.levelComplexMap ψ n))) := by
  let H := compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] f j kbar ⋙
    DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) i
  have h₁ := LAdicSheaf.padicCoefficientComplexLevelIso_hom_naturality ψ n
  have h₁' := (H.map_comp _ _).symm.trans ((congrArg H.map h₁).trans (H.map_comp _ _))
  exact endo_transport_aux _ _ _ h₁'.symm _ _
    (compactSupportFrobeniusCohomologyGroupRestrictScalarsIso_naturality
      (PadicInt.toZModPow (n + 1)) f j kbar (LAdicSheaf.levelComplexMap ψ n) i)

/-! ### Intertwiners on the integral coinvariants -/

section Quotient

universe w

variable {Γ : Type*} [Group Γ] (H : Subgroup Γ) [H.Normal] {r : ℕ} (ρ : Γ →* GL (Fin r) ℤ_[ℓ])
  (A : Matrix (Fin r) (Fin r) ℤ_[ℓ]) (hA : ∀ g, A * (ρ g).val = (ρ g).val * A)

/-- The endomorphism of the lifted coinvariants `(ℤ_ℓ^r)_H` given by an intertwiner of `ρ`. -/
def integralCoinvariantsModuleMatrixEnd :
    (integralCoinvariantsModule.{w} H ρ : ModuleCat.{w} ℤ_[ℓ]) ⟶ integralCoinvariantsModule H ρ :=
  ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap ∘ₗ coinvariantsMatrixMap H ρ A hA ∘ₗ
    ULift.moduleEquiv.toLinearMap)

/-- The quotient isomorphism carries the endomorphism of an intertwiner to that of its
reduction. -/
theorem integralCoinvariantsQuotientEquiv_matrixEnd (n : ℕ)
    (x : (padicQuotientTower (integralCoinvariantsModule.{u + 1} H ρ :
      ModuleCat.{u + 1} ℤ_[ℓ])).obj (op n)) :
    (integralCoinvariantsQuotientEquiv ℓ H ρ n
        (((padicQuotientTowerMap (integralCoinvariantsModuleMatrixEnd ℓ H ρ A hA)).app
          (op n)).hom x)).down =
      coinvariantsMatrixMap H (levelMatrixRepresentation ρ (n + 1))
        (A.map (PadicInt.toZModPow (n + 1))) (map_toZModPow_commute ρ A hA (n + 1))
        (integralCoinvariantsQuotientEquiv ℓ H ρ n x).down := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change integralCoinvariantsReduction H ρ (n + 1) (coinvariantsMatrixMap H ρ A hA y.down) = _
  rw [integralCoinvariantsReduction_coinvariantsMatrixMap]
  rfl

end Quotient

section Representation

variable [ConnectedSpace X.1] (x : GeometricPoint X.1) {r : ℕ}
  (τ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ]) (hτ : Continuous τ)
  [CompactSpace (EtaleFundamentalGroup X.1 x)]
  (H : Subgroup (EtaleFundamentalGroup X.1 x)) [H.Normal] (φ : EtaleFundamentalGroup X.1 x)
  {ι : Type*} (A : ι → Matrix (Fin r) (Fin r) ℤ_[ℓ])
  (hA : ∀ a g, A a * (integralModel τ hτ g).val = (integralModel τ hτ g).val * A a)

/-- The endomorphism of `ℱ_τ` given by an integral intertwiner of the integral model. -/
abbrev LAdicSheaf.representationSheafIntertwiner (a : ι) :
    LAdicSheaf.representationSheaf B X x τ hτ ⟶ LAdicSheaf.representationSheaf B X x τ hτ :=
  representationLAdicSheafMap B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
    (continuous_integralModel τ hτ) (continuous_integralModel τ hτ) (A a) (hA a)

/-- The geometric Frobenius together with the endomorphisms of the intertwiners, on the tower
`n ↦ H²_c(X_k̄, Fₙ)`. -/
abbrev LAdicSheaf.representationSystemEndFamily :
    Option ι → (LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar
      (LAdicSheaf.representationSheaf B X x τ hτ) 2 ⟶
      LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar
        (LAdicSheaf.representationSheaf B X x τ hτ) 2) :=
  fun o => o.elim (LAdicSheaf.geometricCompactlySupportedCohomologySystemPullback B X ℓ f j kbar
      (LAdicSheaf.representationSheaf B X x τ hτ) 2
      (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard))
    fun a => LAdicSheaf.geometricCompactlySupportedCohomologySystemMap f j kbar
      (LAdicSheaf.representationSheafIntertwiner B X ℓ x τ hτ A hA a) 2

/-- `q · ρ(φ)` together with the endomorphisms of the intertwiners, on `(ℤ_ℓ^r)_H`. -/
abbrev integralCoinvariantsEndFamily :
    Option ι → ((integralCoinvariantsModule.{u + 1} H (integralModel τ hτ) :
      ModuleCat.{u + 1} ℤ_[ℓ]) ⟶ integralCoinvariantsModule H (integralModel τ hτ)) :=
  fun o => o.elim (integralCoinvariantsModuleEnd H (integralModel τ hτ) φ ((p ^ q : ℕ) : ℤ_[ℓ]))
    fun a => integralCoinvariantsModuleMatrixEnd ℓ H (integralModel τ hτ) (A a) (hA a)

/-- **Level isomorphisms compatible with the Frobenius and natural in the intertwiners give an
element of `levelIsoSetFamily` at level `n`.** -/
theorem LAdicSheaf.nonempty_levelIsoSetFamily_representationSheaf (n : ℕ)
    (e : compactSupportFrobeniusCohomologyGroup.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ (LAdicSheaf.representationSheaf B X x τ hτ) n)
          2 ≃ₗ[ZMod (ℓ ^ (n + 1))]
      levelCoinvariants H (integralModel τ hτ) (n + 1))
    (he : ∀ t, e ((canonicalCompactSupportFrobeniusGroup.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar p q
        hcard (LAdicSheaf.levelComplex B X ℓ (LAdicSheaf.representationSheaf B X x τ hτ) n)
          2).hom t) =
      ((p ^ q : ℕ) : ZMod (ℓ ^ (n + 1))) •
        levelCoinvariantsFrobenius H (integralModel τ hτ) φ (n + 1) (e t))
    (hen : ∀ a t, e (((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        2).map ((compactSupportFrobeniusFunctor.{u, 0} _ f j kbar).map
          (LAdicSheaf.levelComplexMap
            (LAdicSheaf.representationSheafIntertwiner B X ℓ x τ hτ A hA a) n))).hom t) =
      coinvariantsMatrixMap H (levelMatrixRepresentation (integralModel τ hτ) (n + 1))
        ((A a).map (PadicInt.toZModPow (n + 1)))
        (map_toZModPow_commute (integralModel τ hτ) (A a) (hA a) (n + 1)) (e t)) :
    Nonempty (levelIsoSetFamily (integralCoinvariantsModule.{u + 1} H (integralModel τ hτ))
      (LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar
        (LAdicSheaf.representationSheaf B X x τ hτ) 2)
      (LAdicSheaf.representationSystemEndFamily B X ℓ f j kbar p q hcard x τ hτ A hA)
      (integralCoinvariantsEndFamily B X ℓ p q x τ hτ H φ A hA) n) := by
  let F := LAdicSheaf.representationSheaf B X x τ hτ
  let I := LAdicSheaf.geometricCohomologyLevelIso B X ℓ f j kbar F 2 n
  let e' := e.trans (ULift.moduleEquiv.{0, 0, u + 1} (R := ZMod (ℓ ^ (n + 1)))).symm
  let E2 := (ModuleCat.restrictScalars.{u + 1} (PadicInt.toZModPow (n + 1))).mapIso
    e'.toModuleIso
  let R := integralCoinvariantsQuotientEquiv ℓ H (integralModel τ hτ) n
  refine ⟨⟨(I ≪≫ E2).toLinearEquiv.trans R.symm, fun o t => ?_⟩⟩
  apply R.injective
  apply ULift.ext
  rw [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, LinearEquiv.trans_apply]
  cases o with
  | some a =>
    dsimp only [LAdicSheaf.representationSystemEndFamily, integralCoinvariantsEndFamily,
      Option.elim]
    rw [integralCoinvariantsQuotientEquiv_matrixEnd, LinearEquiv.apply_symm_apply]
    have hI := congrArg (fun g => g.hom t)
      (LAdicSheaf.geometricCohomologyLevelIso_map B X ℓ f j kbar F
        (LAdicSheaf.representationSheafIntertwiner B X ℓ x τ hτ A hA a) 2 n)
    exact (congrArg e hI).trans (hen a (I.hom.hom t))
  | none =>
    dsimp only [LAdicSheaf.representationSystemEndFamily, integralCoinvariantsEndFamily,
      Option.elim]
    rw [integralCoinvariantsQuotientEquiv_end, LinearEquiv.apply_symm_apply]
    have hI := congrArg (fun g => g.hom t)
      (LAdicSheaf.geometricCohomologyLevelIso_frobenius B X ℓ f j kbar p q hcard F 2 n)
    exact (congrArg e hI).trans (he (I.hom.hom t))

include hτ in
/-- **`H²_c(X_k̄, ℱ_τ ⊗ ℚ_ℓ) ≅ (ℚ_ℓ^r)_H`, carrying `π_X^*` to `q · τ(φ)` and the endomorphism of
an intertwiner `A_a` of the integral model to that of `P A_a P⁻¹`, from the finite levels.** -/
theorem LAdicSheaf.exists_linearEquiv_coinvariants_of_levels_natural
    (hlev : ∀ n : ℕ, ∃ e : compactSupportFrobeniusCohomologyGroup.{u, 0} (ZMod (ℓ ^ (n + 1))) f j
        kbar (LAdicSheaf.levelComplex B X ℓ (LAdicSheaf.representationSheaf B X x τ hτ) n)
          2 ≃ₗ[ZMod (ℓ ^ (n + 1))]
        levelCoinvariants H (integralModel τ hτ) (n + 1),
      (∀ t, e ((canonicalCompactSupportFrobeniusGroup.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar p q hcard
          (LAdicSheaf.levelComplex B X ℓ (LAdicSheaf.representationSheaf B X x τ hτ) n) 2).hom t) =
        ((p ^ q : ℕ) : ZMod (ℓ ^ (n + 1))) •
          levelCoinvariantsFrobenius H (integralModel τ hτ) φ (n + 1) (e t)) ∧
      ∀ a t, e (((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
          2).map ((compactSupportFrobeniusFunctor.{u, 0} _ f j kbar).map
            (LAdicSheaf.levelComplexMap
              (LAdicSheaf.representationSheafIntertwiner B X ℓ x τ hτ A hA a) n))).hom t) =
        coinvariantsMatrixMap H (levelMatrixRepresentation (integralModel τ hτ) (n + 1))
          ((A a).map (PadicInt.toZModPow (n + 1)))
          (map_toZModPow_commute (integralModel τ hτ) (A a) (hA a) (n + 1)) (e t))
    (B' : ι → Matrix (Fin r) (Fin r) ℚ_[ℓ]) (hB' : ∀ a g, B' a * (τ g).val = (τ g).val * B' a)
    (hAB : ∀ a, ((exists_conj_integral τ hτ).choose).val *
        (A a).map (PadicInt.Coe.ringHom (p := ℓ)) =
      B' a * ((exists_conj_integral τ hτ).choose).val)
    (hsurj : ∀ n, Function.Surjective ((LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ
      f j kbar (LAdicSheaf.representationSheaf B X x τ hτ) 2).map
        (homOfLE (Nat.le_add_right n 1)).op).hom) :
    ∃ e : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
          (LAdicSheaf.representationSheaf B X x τ hτ) 2 ≃ₗ[ℚ_[ℓ]]
        Coinvariants ((matrixRepresentation τ).comp H.subtype),
      (∀ v, e ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
          (LAdicSheaf.representationSheaf B X x τ hτ) 2).hom v) =
        ((p ^ q : ℕ) : ℚ_[ℓ]) • coinvariantsFrobenius H τ φ (e v)) ∧
      ∀ a v, e (((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
          (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar
            (LAdicSheaf.representationSheafIntertwiner B X ℓ x τ hτ A hA a) 2)).hom v) =
        coinvariantsMatrixMap H τ (B' a) (hB' a) (e v) := by
  let F := LAdicSheaf.representationSheaf B X x τ hτ
  let ρ := integralModel τ hτ
  let M : ModuleCat.{u + 1} ℤ_[ℓ] := integralCoinvariantsModule H ρ
  have : Module.Finite ℤ_[ℓ] M := Module.Finite.equiv ULift.moduleEquiv.symm
  let S := LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F 2
  let σ := LAdicSheaf.geometricCompactlySupportedCohomologySystemPullback B X ℓ f j kbar F 2
    (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard)
  let ψ := integralCoinvariantsModuleEnd H ρ φ ((p ^ q : ℕ) : ℤ_[ℓ])
  have hsetF : ∀ n, Nonempty (levelIsoSetFamily M S
      (LAdicSheaf.representationSystemEndFamily B X ℓ f j kbar p q hcard x τ hτ A hA)
      (integralCoinvariantsEndFamily B X ℓ p q x τ hτ H φ A hA) n) := fun n =>
    (hlev n).elim fun e ⟨he, hen⟩ =>
      LAdicSheaf.nonempty_levelIsoSetFamily_representationSheaf B X ℓ f j kbar p q hcard x τ hτ
        H φ A hA n e he hen
  have hset : ∀ n, Nonempty (levelIsoSet M S σ ψ n) := fun n =>
    (hsetF n).map fun e => ⟨e.1, e.2 none⟩
  obtain ⟨E, hE⟩ := exists_iso_padicQuotientTower_of_levels_family
    (integralCoinvariantsEndFamily B X ℓ p q x τ hτ H φ A hA) S
    (LAdicSheaf.representationSystemEndFamily B X ℓ f j kbar p q hcard x τ hτ A hA) hsurj
    (ker_map_eq_of_levelIsoSet ℓ M ψ S σ hsurj hset) hsetF
  let P := (exists_conj_integral τ hτ).choose
  have hP : ∀ g, rationalGL ρ g = P⁻¹ * τ g * P := fun g => map_integralModel τ hτ g
  obtain ⟨e, he, hn⟩ := exists_extendScalars_limit_linearEquiv_coinvariants_natural.{u + 1}
    H ρ φ τ P hP ((p ^ q : ℕ) : ℤ_[ℓ]) S E σ (hE none)
  refine ⟨e, fun v => ?_, fun a v => ?_⟩
  · rw [← map_natCast (algebraMap ℤ_[ℓ] ℚ_[ℓ])]
    exact he v
  · refine hn _ (integralCoinvariantsModuleMatrixEnd ℓ H ρ (A a) (hA a))
      (coinvariantsMatrixMap H τ (B' a) (hB' a)) (hE (some a)) (fun y => ?_) v
    change rationalCoinvariantsConjEquiv H τ P hP
      (integralCoinvariantsRationalization H ρ (coinvariantsMatrixMap H ρ (A a) (hA a) y)) = _
    rw [integralCoinvariantsRationalization_coinvariantsMatrixMap,
      rationalCoinvariantsConjEquiv_coinvariantsMatrixMap H τ P hP _ _ (B' a) (hB' a) (hAB a)]

end Representation

end Stacks.EtaleCohomology

end
