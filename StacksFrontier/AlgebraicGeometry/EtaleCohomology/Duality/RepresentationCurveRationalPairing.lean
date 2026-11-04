module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.RepresentationLevelPairingAdjoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LAdicPerfectPairingBalanced
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LAdicPoincarePurity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationDualCoefficients

/-!
# Poincaré duality over `ℚ_ℓ` for a representation on an open curve, balanced for intertwiners

Let `X` be a nonempty connected noetherian scheme, smooth of dimension one, with a
compactification `j : X ⟶ X̄` over a finite field `k` of characteristic `p ≠ ℓ` such that `X̄_k̄`
is a smooth curve over the algebraic closure `k̄`, `#k = q`. Let `ρ₀ : π₁(X, x̄) → GL_r(ℤ_ℓ)` be
continuous, `F = ℱ_{ρ₀}`, `F' = ℱ_{ρ₀^∨}`, and suppose the local terms of `F` at the boundary
are killed by a power of `ℓ`. Then there is a perfect `ℚ_ℓ`-bilinear pairing
`B : H¹_c(X_k̄, F ⊗ ℚ_ℓ) × H¹_c(X_k̄, F' ⊗ ℚ_ℓ) → ℚ_ℓ` with `B(π^* v, π^* w) = q B(v, w)` for the
geometric Frobenius `π^*`, and for every family of intertwiners `Aᵢ` of `ρ₀`,
`B(ℱ_{Aᵢ} v, w) = B(v, ℱ_{Aᵢᵀ} w)`
(`Stacks.EtaleCohomology.LAdicSheaf.exists_isPerfPair_representationCurve`).

The pairing is the limit of the cup product pairings of the levels
(`Stacks.EtaleCohomology.LAdicSheaf.curveLevelPairing` for the coefficient pairing
`Stacks.EtaleCohomology.LAdicSheaf.representationCurveLevelPairing`), whose kernels are bounded
(`Stacks.EtaleCohomology.LAdicSheaf.curveLevelPairing_bounds`) and for which `ℱ_A`, `ℱ_{Aᵀ}` are
adjoint (`Stacks.EtaleCohomology.LAdicSheaf.representationCurveLevelPairing_adjoint`); the
cohomology of the levels forms a perfect tower, so
`Stacks.LAdicPairing.exists_isPerfPair_extendScalars_of_levels_balanced` applies. This is the
Poincaré duality of the fibres of the Fourier family in the purity half of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), with the `E`-actions balanced.

The finite-level complexes `RΓ_c(X_k̄, Fₙ)` and their perfectness live in the standard model of
the derived category (`HasDerivedCategory.standard`), whence the local instance.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.exists_isPerfPair_representationCurve`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale Matrix Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

section Rational

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  Sheaf.monoidalCategory
  etaleModuleInverseImageSheafPullbackMonoidal etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  etaleModuleDirectImage_preservesFiniteColimits_of_universalHomeomorphism

attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

/-- The morphisms inverted by sheafification form a monoidal class of étale module sheaves. -/
local instance isMonoidal_W_etaleModules_representationCurveRational (Λ : Type) [CommRing Λ]
    (S : Scheme.{u}) : (S.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal :=
  isMonoidal_W_etaleModules (Λ := Λ) S

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
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
  [IsNoetherian X.1] [Fact ℓ.Prime] [ConnectedSpace X.1] (x : GeometricPoint X.1) {r : ℕ}
  (ρ₀ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]) (hρ₀ : Continuous ρ₀)
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
  [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p]
  (hcard : Fintype.card k = p ^ q)

omit [IsAlgClosed kbar] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- **The cup product pairings of the levels are balanced for `ℱ_A` and `ℱ_{Aᵀ}`**, for an
intertwiner `A` of `ρ₀`: `εₙ(ℱ_A x, y) = εₙ(x, ℱ_{Aᵀ} y)` for the pairing
`Stacks.EtaleCohomology.LAdicSheaf.curveLevelPairing` of `ℱ_{ρ₀}` and `ℱ_{ρ₀^∨}` along the
coefficient pairing `Stacks.EtaleCohomology.LAdicSheaf.representationCurveLevelPairing`, any traces
`t`. -/
theorem LAdicSheaf.representationCurveLevelPairing_balanced
    (t : ∀ n : ℕ, Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChange (Over.mk j.toBase) kbar)))
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology) 2 →+ ZMod (ℓ ^ (n + 1)))
    (hflat : ∀ (n : ℕ) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (.of Ω) ⟶ fieldBaseChange (Over.mk j.toBase) kbar),
      Module.Flat (ZMod (ℓ ^ (n + 1)))
        ((((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
              (LAdicSheaf.etaleLevel B X ℓ (representationLAdicSheaf B X x
                (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) (contragredient ρ₀)
                (continuous_contragredient hρ₀)) n)))))
    (A : Matrix (Fin r) (Fin r) ℤ_[ℓ]) (hA : ∀ g, A * (ρ₀ g).val = (ρ₀ g).val * A) (n : ℕ)
    (a : (geometricCompactSupportPadicCohomology B X ℓ f j kbar 1).obj
      (LAdicSheaf.padicLevel B X ℓ (representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ₀ hρ₀) n))
    (b : (geometricCompactSupportPadicCohomology B X ℓ f j kbar 1).obj
      (LAdicSheaf.padicLevel B X ℓ (representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) (contragredient ρ₀)
        (continuous_contragredient hρ₀)) n)) :
    LAdicSheaf.curveLevelPairing B X ℓ f j kbar t
        (representationLAdicSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
          ρ₀ hρ₀)
        (representationLAdicSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
          (contragredient ρ₀) (continuous_contragredient hρ₀))
        (fun n => LAdicSheaf.representationCurveLevelPairing B X x ρ₀ hρ₀ n f j)
        hflat n
        ((geometricCompactSupportPadicCohomology B X ℓ f j kbar 1).map
          (LAdicSheaf.padicLevelMap (representationLAdicSheafMap B X x
            (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ₀ hρ₀ A hA) n) a) b =
      LAdicSheaf.curveLevelPairing B X ℓ f j kbar t
        (representationLAdicSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
          ρ₀ hρ₀)
        (representationLAdicSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
          (contragredient ρ₀) (continuous_contragredient hρ₀))
        (fun n => LAdicSheaf.representationCurveLevelPairing B X x ρ₀ hρ₀ n f j)
        hflat n a
        ((geometricCompactSupportPadicCohomology B X ℓ f j kbar 1).map
          (LAdicSheaf.padicLevelMap (representationLAdicSheafMap B X x
            (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
            (continuous_contragredient hρ₀) (continuous_contragredient hρ₀) Aᵀ
            (transpose_mul_contragredient hA)) n) b) :=
  LAdicSheaf.curveLevelPairing_map B X ℓ f j kbar t
    (representationLAdicSheafMap B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
      hρ₀ hρ₀ A hA)
    (representationLAdicSheafMap B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
      (continuous_contragredient hρ₀) (continuous_contragredient hρ₀) Aᵀ
      (transpose_mul_contragredient hA))
    (fun n => LAdicSheaf.representationCurveLevelPairing B X x ρ₀ hρ₀ n f j)
    (fun n => LAdicSheaf.representationCurveLevelPairing B X x ρ₀ hρ₀ n f j) hflat hflat
    (fun n => LAdicSheaf.representationCurveLevelPairing_adjoint B X x ρ₀ hρ₀ n f j A hA) n a b

omit [ConnectedSpace X.1] [IsAlgClosed kbar] [CharP kbar p] in
/-- **Balanced Poincaré duality over `ℚ_ℓ` from finite levels**, for ℓ-adic sheaves `F`, `F'` with
pow-exact levels and perfect `RΓ_c(X_k̄, Fₙ)`, `RΓ_c(X_k̄, F'ₙ)`: pairings `εₙ` of
`Hⁱ_c(X_k̄, Fₙ)` and `H^{i'}_c(X_k̄, F'ₙ)` into `ℤ/ℓⁿ⁺¹` with left kernels killed by `ℓ^{K₁}`,
right kernels killed by `ℓ^{K₂}`, scaled by `c` under the geometric Frobenius and balanced for
families of endomorphisms `φᵢ` of `F` and `ψᵢ` of `F'` give a perfect pairing of
`Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` and `H^{i'}_c(X_k̄, F' ⊗ ℚ_ℓ)` into `ℚ_ℓ`, scaled by `c` under the Frobenius
and balanced for `φᵢ`, `ψᵢ`. -/
theorem LAdicSheaf.exists_isPerfPair_of_levelPairing_balanced (F F' : LAdicSheaf B X ℓ)
    (hF : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F n))
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ F n))))
    (hF' : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F' n))
    (hP' : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ F' n))))
    (i i' : ℤ) (c K₁ K₂ : ℕ)
    (ε : ∀ n, (geometricCompactSupportPadicCohomology B X ℓ f j kbar i).obj
        (LAdicSheaf.padicLevel B X ℓ F n) →+
      (geometricCompactSupportPadicCohomology B X ℓ f j kbar i').obj
        (LAdicSheaf.padicLevel B X ℓ F' n) →+ ZMod (ℓ ^ (n + 1)))
    (hl : ∀ n x, (∀ y, ε n x y = 0) → (ℓ ^ K₁) • x = 0)
    (hr : ∀ n y, (∀ x, ε n x y = 0) → (ℓ ^ K₂) • y = 0)
    (hε : ∀ n x y, ε n ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f j kbar p q hcard
        ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F n)) i).hom x)
      ((canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f j kbar p q hcard
        ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F' n)) i').hom y) =
        (c : ZMod (ℓ ^ (n + 1))) * ε n x y)
    {I : Type*} (φ : I → (F ⟶ F)) (ψ : I → (F' ⟶ F'))
    (hb : ∀ s n x y, ε n ((geometricCompactSupportPadicCohomology B X ℓ f j kbar i).map
        (LAdicSheaf.padicLevelMap (φ s) n) x) y =
      ε n x ((geometricCompactSupportPadicCohomology B X ℓ f j kbar i').map
        (LAdicSheaf.padicLevelMap (ψ s) n) y)) :
    ∃ Bp : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i →ₗ[ℚ_[ℓ]]
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F' i' →ₗ[ℚ_[ℓ]] ℚ_[ℓ],
      Bp.IsPerfPair ∧
      (∀ v w, Bp ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
          F i).hom v)
          ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
            F' i').hom w) = (c : ℚ_[ℓ]) * Bp v w) ∧
      ∀ s v w, Bp (((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
          (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar (φ s) i)).hom v) w =
        Bp v (((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
          (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar (ψ s) i')).hom w) := by
  let e := LAdicSheaf.geometricLevelCohomologySystemIso B X ℓ f j kbar p q hcard F hF hP i
  let e' := LAdicSheaf.geometricLevelCohomologySystemIso B X ℓ f j kbar p q hcard F' hF' hP' i'
  have : Module.Finite ℤ_[ℓ]
      (LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f j kbar F i) :=
    Stacks.InverseSystem.finite_limit_of_iso _ i e
  have : Module.Finite ℤ_[ℓ]
      (LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f j kbar F' i') :=
    Stacks.InverseSystem.finite_limit_of_iso _ i' e'
  obtain ⟨c₁, h₁⟩ :=
    Stacks.InverseSystem.exists_eq_pow_smul_of_limit_π_eq_zero_and_pow_smul_mem_range _ i e
  obtain ⟨c₂, h₂⟩ :=
    Stacks.InverseSystem.exists_eq_pow_smul_of_limit_π_eq_zero_and_pow_smul_mem_range _ i' e'
  have hraise {N M : Type (u + 1)} [AddCommGroup N] [AddCommGroup M] (π : M →+ N) (c K : ℕ)
      (hcK : c ≤ K) (h : ∀ y, ∃ a, π a = (ℓ ^ c) • y) (y : N) : ∃ a, π a = (ℓ ^ K) • y := by
    obtain ⟨a, ha⟩ := h y
    refine ⟨(ℓ ^ (K - c)) • a, ?_⟩
    rw [map_nsmul, ha, smul_smul, ← pow_add, Nat.sub_add_cancel hcK]
  exact LAdicPairing.exists_isPerfPair_extendScalars_of_levels_balanced
    (LAdicSheaf.geometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F i)
    (LAdicSheaf.geometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F' i')
    c (max c₁ c₂) K₁ K₂
    (fun n => (LAdicSheaf.geometricCompactlySupportedCohomologyπ B X ℓ f j kbar F i
      n).hom.toAddMonoidHom)
    (fun n => (LAdicSheaf.geometricCompactlySupportedCohomologyπ B X ℓ f j kbar F' i'
      n).hom.toAddMonoidHom)
    (fun n => (canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f j kbar p q hcard
        ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F n))
          i).hom.toAddMonoidHom)
    (fun n => (canonicalCompactSupportFrobeniusGroup.{u, 0} ℤ_[ℓ] f j kbar p q hcard
        ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F' n))
          i').hom.toAddMonoidHom)
    (fun n a => congrArg (fun φ => φ.hom a)
      (LAdicSheaf.geometricCompactlySupportedFrobenius_π B X ℓ f j kbar p q hcard F i n))
    (fun n b => congrArg (fun φ => φ.hom b)
      (LAdicSheaf.geometricCompactlySupportedFrobenius_π B X ℓ f j kbar p q hcard F' i' n))
    (fun n => (h₁ n).1) (fun n => (h₂ n).1)
    (fun n => hraise _ c₁ _ (le_max_left _ _) (h₁ n).2)
    (fun n => hraise _ c₂ _ (le_max_right _ _) (h₂ n).2)
    (fun s => LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar (φ s) i)
    (fun s => LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar (ψ s) i')
    (fun s n => ((geometricCompactSupportPadicCohomology B X ℓ f j kbar i).map
      (LAdicSheaf.padicLevelMap (φ s) n)).hom.toAddMonoidHom)
    (fun s n => ((geometricCompactSupportPadicCohomology B X ℓ f j kbar i').map
      (LAdicSheaf.padicLevelMap (ψ s) n)).hom.toAddMonoidHom)
    (fun s n a => congrArg (fun g => g.hom a)
      (LAdicSheaf.geometricCompactlySupportedCohomologyMap_π f j kbar (φ s) i n))
    (fun s n b => congrArg (fun g => g.hom b)
      (LAdicSheaf.geometricCompactlySupportedCohomologyMap_π f j kbar (ψ s) i' n))
    ε hl hr hε hb

/-- **Poincaré duality over `ℚ_ℓ` on an open curve for `ℱ_{ρ₀}` and `ℱ_{ρ₀^∨}`, Frobenius-scaled
and balanced for intertwiners.** If `X̄_k̄` is a smooth curve, `X` is nonempty, `ℓ ≠ p` and the
local terms of `ℱ_{ρ₀}` at the boundary are killed by `ℓ ^ K`, there is a perfect pairing `B` of
`H¹_c(X_k̄, ℱ_{ρ₀} ⊗ ℚ_ℓ)` and `H¹_c(X_k̄, ℱ_{ρ₀^∨} ⊗ ℚ_ℓ)` into `ℚ_ℓ` with
`B(π^* v, π^* w) = q B(v, w)`, `q = p ^ q'`, and `B(ℱ_{Aᵢ} v, w) = B(v, ℱ_{Aᵢᵀ} w)` for every
family of matrices `Aᵢ` commuting with `ρ₀`. -/
theorem LAdicSheaf.exists_isPerfPair_representationCurve [Algebra.IsAlgebraic k kbar]
    [IsCurve kbar (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))]
    [Smooth (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))]
    [Nonempty X.1] (hℓp : ℓ ≠ p) {K : ℕ}
    (hF : LAdicSheaf.LocalTermsKilledBy B X ℓ f j kbar (representationLAdicSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ₀ hρ₀) K)
    {I : Type*} (A : I → Matrix (Fin r) (Fin r) ℤ_[ℓ])
    (hA : ∀ i g, A i * (ρ₀ g).val = (ρ₀ g).val * A i) :
    ∃ Bp : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
        (representationLAdicSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
          ρ₀ hρ₀) 1 →ₗ[ℚ_[ℓ]]
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
        (representationLAdicSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
          (contragredient ρ₀) (continuous_contragredient hρ₀)) 1 →ₗ[ℚ_[ℓ]] ℚ_[ℓ],
      Bp.IsPerfPair ∧
      (∀ v w, Bp ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
          (representationLAdicSheaf B X x
            (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ₀ hρ₀) 1).hom v)
          ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
            (representationLAdicSheaf B X x
              (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) (contragredient ρ₀)
              (continuous_contragredient hρ₀)) 1).hom w) =
        ((p ^ q : ℕ) : ℚ_[ℓ]) * Bp v w) ∧
      ∀ i v w, Bp (((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
          (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar
            (representationLAdicSheafMap B X x
              (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ₀ hρ₀ (A i) (hA i))
            1)).hom v) w =
        Bp v (((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
          (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar
            (representationLAdicSheafMap B X x
              (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
              (continuous_contragredient hρ₀) (continuous_contragredient hρ₀) (A i)ᵀ
              (transpose_mul_contragredient (hA i))) 1)).hom w) := by
  have hp : ℓ.Prime := Fact.out
  have hℓ : IsUnit (ℓ : kbar) := by
    refine isUnit_iff_ne_zero.2 fun h0 => hℓp ?_
    exact ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hp).1
      ((CharP.cast_eq_zero_iff kbar p ℓ).1 h0)).symm
  obtain ⟨t, ht⟩ := exists_injective_curveLevelTrace B X ℓ f j kbar hℓ
  have hflat := fun n => flat_sheafFiber_inverseImage_extensionByZero_representationLAdicSheaf
    B X ℓ x (contragredient ρ₀) (continuous_contragredient hρ₀) f j kbar n
  obtain ⟨hl, hr, hε⟩ := LAdicSheaf.curveLevelPairing_bounds B X ℓ f j kbar p q hcard hℓ t ht
    (representationLAdicSheaf B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
      ρ₀ hρ₀)
    (representationLAdicSheaf B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
      (contragredient ρ₀) (continuous_contragredient hρ₀))
    hF (fun n => LAdicSheaf.representationCurveLevelPairing B X x ρ₀ hρ₀ n f j)
    (fun n => isFiniteTypeLocallyConstant_inverseImage_etaleLevel_representationLAdicSheaf
      B X ℓ x (contragredient ρ₀) (continuous_contragredient hρ₀) f kbar n)
    hflat (fun n => LAdicSheaf.bijective_sheafFiber_representationCurveLevelPairing B X x ρ₀ hρ₀ n
      f j kbar)
  exact LAdicSheaf.exists_isPerfPair_of_levelPairing_balanced B X ℓ f j kbar p q hcard
    (representationLAdicSheaf B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
      ρ₀ hρ₀)
    (representationLAdicSheaf B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
      (contragredient ρ₀) (continuous_contragredient hρ₀))
    (fun n => powExact_etaleLevel_representationLAdicSheaf B X x ρ₀ hρ₀ n)
    (fun n => isPerfect_compactSupportFrobeniusCohomology_levelComplex_representationLAdicSheaf
      B X ℓ x ρ₀ hρ₀ f j kbar p q hcard hℓp n)
    (fun n => powExact_etaleLevel_representationLAdicSheaf B X x (contragredient ρ₀)
      (continuous_contragredient hρ₀) n)
    (fun n => isPerfect_compactSupportFrobeniusCohomology_levelComplex_representationLAdicSheaf
      B X ℓ x (contragredient ρ₀) (continuous_contragredient hρ₀) f j kbar p q hcard hℓp n)
    1 1 (p ^ q) K (K + K)
    (fun n => LAdicSheaf.curveLevelPairing B X ℓ f j kbar t
      (representationLAdicSheaf B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
      ρ₀ hρ₀)
    (representationLAdicSheaf B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
      (contragredient ρ₀) (continuous_contragredient hρ₀))
      (fun n => LAdicSheaf.representationCurveLevelPairing B X x ρ₀ hρ₀ n f j) hflat n)
    hl (fun n y hy => by rw [pow_add]; exact hr n y hy) hε
    (fun s => representationLAdicSheafMap B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ₀ hρ₀ (A s) (hA s))
    (fun s => representationLAdicSheafMap B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
      (continuous_contragredient hρ₀) (continuous_contragredient hρ₀) (A s)ᵀ
      (transpose_mul_contragredient (hA s)))
    (fun s => LAdicSheaf.representationCurveLevelPairing_balanced B X ℓ x ρ₀ hρ₀ f j kbar t hflat
      (A s) (hA s))

end Rational

end Stacks.EtaleCohomology
