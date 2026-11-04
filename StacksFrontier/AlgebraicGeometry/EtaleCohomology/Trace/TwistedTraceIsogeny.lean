module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TwistedTraceTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicIsogeny

/-!
# Twisted traces along an isogeny of ℓ-adic sheaves

Morphisms `a : F ⟶ F'` and `a' : F' ⟶ F` of ℓ-adic sheaves with `a ≫ a' = K` and `a' ≫ a = K`
for a nonzero integer `K` induce mutually inverse (up to `K`) maps on `Hⁱ_c(X_k̄, -) ⊗ ℚ_ℓ`. If
`a` carries an endomorphism `ψ` of `F` to an endomorphism `ψ'` of `F'`, then
`Tr(ψ ∘ (π_X^*)^N | Hⁱ_c(X_k̄, F) ⊗ ℚ_ℓ) = Tr(ψ' ∘ (π_X^*)^N | Hⁱ_c(X_k̄, F') ⊗ ℚ_ℓ)`.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.rationalCohomologyMap`: the map on `Hⁱ_c(X_k̄, -) ⊗ ℚ_ℓ`
  induced by a morphism of ℓ-adic sheaves.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.trace_rationalMap_comp_rationalFrobenius_pow_of_isogeny`:
  the twisted traces of `ψ` and `ψ'` on `Hⁱ_c(X_k̄, -) ⊗ ℚ_ℓ` agree along an isogeny.

## Implementation notes

The statements are formed in the standard model `HasDerivedCategory.standard` of the derived
category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

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
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- The rational map on `Hⁱ_c` of a morphism of ℓ-adic sheaves. -/
public abbrev LAdicSheaf.rationalCohomologyMap {F F' : LAdicSheaf B X ℓ} (a : F ⟶ F') (i : ℤ) :=
  ((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
    (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar a i)).hom

/-- The rational map of a composite. -/
public theorem LAdicSheaf.rationalCohomologyMap_comp {F F' F'' : LAdicSheaf B X ℓ} (a : F ⟶ F')
    (a' : F' ⟶ F'') (i : ℤ) :
    LAdicSheaf.rationalCohomologyMap f j kbar (a ≫ a') i =
      LAdicSheaf.rationalCohomologyMap f j kbar a' i ∘ₗ
        LAdicSheaf.rationalCohomologyMap f j kbar a i := by
  simp only [LAdicSheaf.rationalCohomologyMap,
    LAdicSheaf.geometricCompactlySupportedCohomologyMap_comp, Functor.map_comp, ModuleCat.hom_comp]

/-- The rational map of `N • 𝟙` is multiplication by `N`. -/
public theorem LAdicSheaf.rationalCohomologyMap_nsmul_id (F : LAdicSheaf B X ℓ) (N : ℕ) (i : ℤ) :
    LAdicSheaf.rationalCohomologyMap f j kbar (N • 𝟙 F) i = (N : ℚ_[ℓ]) • LinearMap.id := by
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ]))
  have := Functor.additive_of_preservesBinaryBiproducts
    (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ]))
  rw [LAdicSheaf.rationalCohomologyMap,
    LAdicSheaf.geometricCompactlySupportedCohomologyMap_nsmul_id, Functor.map_nsmul,
    CategoryTheory.Functor.map_id]
  refine LinearMap.ext fun v => ?_
  show N • v = (N : ℚ_[ℓ]) • v
  rw [Nat.cast_smul_eq_nsmul]

/-- **Twisted traces on compactly supported cohomology along an isogeny of ℓ-adic sheaves.**
If `a ≫ a' = K • 𝟙 F` and `a' ≫ a = K • 𝟙 F'` for a nonzero `K` and `a ≫ ψ' = ψ ≫ a`, then
`ψ` and `ψ'` composed with the `N`-th power of the geometric Frobenius have the same trace on
`Hⁱ_c(X_k̄, -) ⊗ ℚ_ℓ`. -/
public theorem LAdicSheaf.trace_rationalMap_comp_rationalFrobenius_pow_of_isogeny
    {F F' : LAdicSheaf B X ℓ} (a : F ⟶ F') (a' : F' ⟶ F) (K : ℕ) (hK : K ≠ 0)
    (haa' : a ≫ a' = K • 𝟙 F) (ha'a : a' ≫ a = K • 𝟙 F') (ψ : F ⟶ F) (ψ' : F' ⟶ F')
    (h : a ≫ ψ' = ψ ≫ a) (i : ℤ) (N : ℕ) :
    LinearMap.trace ℚ_[ℓ] _
        (LAdicSheaf.rationalCohomologyMap f j kbar ψ i ∘ₗ
          (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius
            B X ℓ f j kbar p q hcard F i).hom ^ N) =
      LinearMap.trace ℚ_[ℓ] _
        (LAdicSheaf.rationalCohomologyMap f j kbar ψ' i ∘ₗ
          (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius
            B X ℓ f j kbar p q hcard F' i).hom ^ N) := by
  have hK' : (K : ℚ_[ℓ]) ≠ 0 := Nat.cast_ne_zero.2 hK
  have hinv : ∀ {G G' : LAdicSheaf B X ℓ} (b : G ⟶ G') (b' : G' ⟶ G), b ≫ b' = K • 𝟙 G → ∀ v,
      LAdicSheaf.rationalCohomologyMap f j kbar b' i
        (LAdicSheaf.rationalCohomologyMap f j kbar b i v) = (K : ℚ_[ℓ]) • v :=
    fun b b' hb v => by
    have := LinearMap.congr_fun (LAdicSheaf.rationalCohomologyMap_comp f j kbar b b' i) v
    rw [hb, LAdicSheaf.rationalCohomologyMap_nsmul_id] at this
    exact this.symm
  let L : _ ≃ₗ[ℚ_[ℓ]] _ :=
    { toFun := LAdicSheaf.rationalCohomologyMap f j kbar a i
      invFun := fun v => ((K : ℚ_[ℓ])⁻¹) • LAdicSheaf.rationalCohomologyMap f j kbar a' i v
      map_add' := map_add _
      map_smul' := map_smul _
      left_inv := fun v => by
        show ((K : ℚ_[ℓ])⁻¹) • _ = v
        rw [hinv a a' haa', smul_smul, inv_mul_cancel₀ hK', one_smul]
      right_inv := fun v => by
        show LAdicSheaf.rationalCohomologyMap f j kbar a i (((K : ℚ_[ℓ])⁻¹) • _) = v
        rw [map_smul, hinv a' a ha'a, smul_smul, inv_mul_cancel₀ hK', one_smul] }
  refine trace_eq_of_linearEquiv_comm L _ _ ?_
  refine comp_pow_comp_of_comm _ _ _ _ _ ?_ ?_ N
  · show LAdicSheaf.rationalCohomologyMap f j kbar a i ∘ₗ _ = _ ∘ₗ
      LAdicSheaf.rationalCohomologyMap f j kbar a i
    rw [← LAdicSheaf.rationalCohomologyMap_comp, ← LAdicSheaf.rationalCohomologyMap_comp, h]
  · have hc := congrArg (fun g => ((ModuleCat.extendScalars.{0, 0, u + 1}
      (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map g).hom)
      (LAdicSheaf.geometricCompactlySupportedCohomologyMap_frobenius f j kbar p q hcard a i)
    simp only [Functor.map_comp, ModuleCat.hom_comp] at hc
    exact hc.symm

end Stacks.EtaleCohomology

end
