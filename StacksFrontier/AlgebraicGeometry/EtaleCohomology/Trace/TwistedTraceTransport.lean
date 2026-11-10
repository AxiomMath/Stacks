module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TwistedFrobeniusPointExtension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicCompactSupportFunctoriality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LFunctionRationalSheaf

/-!
# Twisted traces along an isomorphism of ℓ-adic sheaves

An isomorphism `Φ : F ≅ F'` of ℓ-adic sheaves carrying an endomorphism `ψ` of `F` to an
endomorphism `ψ'` of `F'` identifies the twisted traces of Frobenius on the stalks,
`Tr(ψ ∘ π_yᵏ | F_ȳ ⊗ ℚ_ℓ) = Tr(ψ' ∘ π_yᵏ | F'_ȳ ⊗ ℚ_ℓ)`, and on compactly supported cohomology,
`Tr(ψ ∘ (π_X^*)^N | Hⁱ_c(X_k̄, F) ⊗ ℚ_ℓ) = Tr(ψ' ∘ (π_X^*)^N | Hⁱ_c(X_k̄, F') ⊗ ℚ_ℓ)`.

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.trace_rationalStalkMap_comp_rationalStalkFrobenius_of_iso`
* `Stacks.EtaleCohomology.LAdicSheaf.trace_rationalMap_comp_rationalFrobenius_pow_of_iso`
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

/-- The map of rational stalks of a composite. -/
public theorem LAdicSheaf.rationalStalkMap_comp' {F G H : LAdicSheaf B X ℓ} (φ : F ⟶ G)
    (ψ : G ⟶ H) (s : GeometricPoint X.1) :
    LAdicSheaf.rationalStalkMap (φ ≫ ψ) s =
      LAdicSheaf.rationalStalkMap ψ s ∘ₗ LAdicSheaf.rationalStalkMap φ s := by
  simp only [LAdicSheaf.rationalStalkMap, LAdicSheaf.stalkMap_comp, LinearMap.baseChange_comp]

/-- The map of rational stalks of the identity. -/
public theorem LAdicSheaf.rationalStalkMap_id' (F : LAdicSheaf B X ℓ) (s : GeometricPoint X.1) :
    LAdicSheaf.rationalStalkMap (𝟙 F) s = LinearMap.id := by
  simp only [LAdicSheaf.rationalStalkMap, LAdicSheaf.stalkMap_id, LinearMap.baseChange_id]

/-- The rational stalks of isomorphic ℓ-adic sheaves. -/
public def LAdicSheaf.rationalStalkLinearEquiv {F F' : LAdicSheaf B X ℓ} (Φ : F ≅ F')
    (s : GeometricPoint X.1) :
    LAdicSheaf.rationalStalkLeft B X ℓ F s ≃ₗ[ℚ_[ℓ]] LAdicSheaf.rationalStalkLeft B X ℓ F' s :=
  LinearEquiv.ofLinearMap (LAdicSheaf.rationalStalkMap Φ.hom s)
    (LAdicSheaf.rationalStalkMap Φ.inv s)
    (by rw [← LAdicSheaf.rationalStalkMap_comp', Φ.inv_hom_id, LAdicSheaf.rationalStalkMap_id'])
    (by rw [← LAdicSheaf.rationalStalkMap_comp', Φ.hom_inv_id, LAdicSheaf.rationalStalkMap_id'])

/-- If `L` intertwines `A` with `A'` and `B` with `B'`, then `A ∘ Bᵏ` and `A' ∘ B'ᵏ` have the same
trace. -/
private theorem trace_comp_pow_eq_of_linearEquiv_comm {K V W : Type*} [Field K] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] (L : V ≃ₗ[K] W) (A B : V →ₗ[K] V)
    (A' B' : W →ₗ[K] W) (hA : L.toLinearMap ∘ₗ A = A' ∘ₗ L.toLinearMap)
    (hB : L.toLinearMap ∘ₗ B = B' ∘ₗ L.toLinearMap) (k : ℕ) :
    LinearMap.trace K V (A ∘ₗ B ^ k) = LinearMap.trace K W (A' ∘ₗ B' ^ k) :=
  trace_eq_of_linearEquiv_comm L _ _ (comp_pow_comp_of_comm _ _ _ _ _ hA hB k)

/-- **Twisted traces of Frobenius on the stalks along an isomorphism of ℓ-adic sheaves.** -/
public theorem LAdicSheaf.trace_rationalStalkMap_comp_rationalStalkFrobenius_of_iso
    {F F' : LAdicSheaf B X ℓ} (Φ : F ≅ F') (ψ : F ⟶ F) (ψ' : F' ⟶ F')
    (h : Φ.hom ≫ ψ' = ψ ≫ Φ.hom) (y : X.1) (hy : Finite (X.1.residueField y)) (k : ℕ) :
    LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkMap ψ (geometricPointAt X.1 y) ∘ₗ
        LAdicSheaf.rationalStalkFrobenius B X ℓ F y hy ^ k) =
      LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkMap ψ' (geometricPointAt X.1 y) ∘ₗ
        LAdicSheaf.rationalStalkFrobenius B X ℓ F' y hy ^ k) := by
  have := hy
  refine trace_comp_pow_eq_of_linearEquiv_comm (LAdicSheaf.rationalStalkLinearEquiv Φ _)
    _ _ _ _ ?_ ?_ k
  · change LAdicSheaf.rationalStalkMap Φ.hom _ ∘ₗ _ = _ ∘ₗ LAdicSheaf.rationalStalkMap Φ.hom _
    rw [← LAdicSheaf.rationalStalkMap_comp', ← LAdicSheaf.rationalStalkMap_comp', h]
  · exact (LAdicSheaf.rationalStalkEnd_comp_rationalStalkMap Φ.hom (frobeniusPointHom X.1 y)).symm

variable {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- The compactly supported cohomology of isomorphic ℓ-adic sheaves. -/
public def LAdicSheaf.geometricCompactlySupportedCohomologyMapIso {F F' : LAdicSheaf B X ℓ}
    (Φ : F ≅ F') (i : ℤ) :
    LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f j kbar F i ≅
      LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f j kbar F' i where
  hom := LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar Φ.hom i
  inv := LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar Φ.inv i
  hom_inv_id := by
    rw [← LAdicSheaf.geometricCompactlySupportedCohomologyMap_comp, Φ.hom_inv_id,
      LAdicSheaf.geometricCompactlySupportedCohomologyMap_id]
  inv_hom_id := by
    rw [← LAdicSheaf.geometricCompactlySupportedCohomologyMap_comp, Φ.inv_hom_id,
      LAdicSheaf.geometricCompactlySupportedCohomologyMap_id]

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- **Twisted traces on compactly supported cohomology along an isomorphism of ℓ-adic
sheaves.** -/
public theorem LAdicSheaf.trace_rationalMap_comp_rationalFrobenius_pow_of_iso
    {F F' : LAdicSheaf B X ℓ} (Φ : F ≅ F') (ψ : F ⟶ F) (ψ' : F' ⟶ F')
    (h : Φ.hom ≫ ψ' = ψ ≫ Φ.hom) (i : ℤ) (N : ℕ) :
    LinearMap.trace ℚ_[ℓ] _
        (((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
            (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar ψ i)).hom ∘ₗ
          (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
            F i).hom ^ N) =
      LinearMap.trace ℚ_[ℓ] _
        (((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
            (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar ψ' i)).hom ∘ₗ
          (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
            F' i).hom ^ N) := by
  let E := ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])
  let I := E.mapIso (LAdicSheaf.geometricCompactlySupportedCohomologyMapIso f j kbar Φ i)
  refine trace_comp_pow_eq_of_linearEquiv_comm I.toLinearEquiv _ _ _ _ ?_ ?_ N
  · change (E.map _).hom ∘ₗ (E.map _).hom = (E.map _).hom ∘ₗ (E.map _).hom
    rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, ← E.map_comp, ← E.map_comp]
    dsimp only [LAdicSheaf.geometricCompactlySupportedCohomologyMapIso]
    rw [← LAdicSheaf.geometricCompactlySupportedCohomologyMap_comp,
      ← LAdicSheaf.geometricCompactlySupportedCohomologyMap_comp, h]
  · have hc := congrArg (fun g => (E.map g).hom)
      (LAdicSheaf.geometricCompactlySupportedCohomologyMap_frobenius f j kbar p q hcard Φ.hom i)
    simp only [Functor.map_comp, ModuleCat.hom_comp] at hc
    exact hc.symm

end Stacks.EtaleCohomology

end
