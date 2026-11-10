module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ComponentWeilCount

/-!
# The traces of a twisted Frobenius on `Hⁱ(Y, μ_{ℓ^m})` for a disjoint union of curves

Let `f : Y ⟶ Spec Ω` be proper and smooth of relative dimension one over an algebraically
closed field and `φ` an endomorphism of `Y` over `Ω` with a Frobenius-twisting automorphism `Ψ`.
In every degree `q`, `H^q(Y, μ_{ℓ^m})` has a finite free model over `ℤ/ℓ^m` in which the trace of
`φ^*` is the sum, over the components `C_i` sent into themselves, of the traces of `φ_i^*` on
`H^q(C_i, μ_{ℓ^m})`: `1`, `Tr(φ_i^* | Pic(C_i)[ℓ^m])`, `deg φ_i`, `0`.

## Main results

* `Stacks.EtaleCohomology.exists_model_rootsOfUnityPullbackMap_eq_sum`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Frobenius Stacks.Kummer

universe u

namespace Stacks.EtaleCohomology

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of Ω))
  [IsProper f] [SmoothOfRelativeDimension 1 f] (φ : Y ⟶ Y) (w : φ ≫ f = f)
  (p : ℕ) [Fact p.Prime] (hY : IsInCharacteristic Y p) (e : ℕ) (Ψ : Y ≅ Y)
  (hΨ : Ψ.hom ≫ φ = absoluteFrobeniusPow Y p hY e)
  (hΨ' : φ ≫ Ψ.hom = absoluteFrobeniusPow Y p hY e) (ℓ m : ℕ) [Fact ℓ.Prime]

open Classical in
/-- The sum over the components sent into themselves of the traces of `φ_i^*` in degree `q`. -/
def componentTraceSum (q : ℕ) : ZMod (ℓ ^ m) :=
  ∑ i, if h : IsSelfComponent f φ i then
    curvePullbackTraceValue (componentι f i ≫ f) ℓ m (componentSelfMap f φ i h)
      (componentSelfMap_comp_structure f φ w i h)
      (componentSelfMap_not_constant f φ p hY e Ψ hΨ' i h) q else 0

open Classical in
/-- **The trace of `φ^*` on `H^q(Y, μ_{ℓ^m})`** is the sum over the components sent into
themselves of the traces on their cohomology. -/
theorem exists_model_rootsOfUnityPullbackMap_eq_sum (hm : 1 ≤ m) (hℓ : (ℓ : Ω) ≠ 0) (q : ℕ) :
    ∃ (r : Fin (componentCount Y) → ℕ)
      (E : Sheaf.H.{u + 1} (rootsOfUnitySheaf.{u, 0} Y (ℓ ^ m)) q ≃+
        (∀ i, Fin (r i) → ZMod (ℓ ^ m))),
      modelTrace (ℓ ^ m) E (rootsOfUnityPullbackMap.{u, 0, u + 1} φ (ℓ ^ m) q) =
        componentTraceSum f φ w p hY e Ψ hΨ' ℓ m q := by
  have hmod : ∀ i, ∃ (r : ℕ) (e : Sheaf.H.{u + 1}
      (rootsOfUnitySheaf.{u, u + 1} (componentOpens f i).toScheme (ℓ ^ m)) q ≃+
      (Fin r → ZMod (ℓ ^ m))), ∀ (φ' : _ ⟶ _) (w' : φ' ≫ (componentι f i ≫ f) = componentι f i ≫ f)
        (hnc : ¬ ∃ y, ∀ x, φ'.base x = y),
        modelTrace (ℓ ^ m) e (rootsOfUnityPullbackMap.{u, u + 1, u + 1} φ' (ℓ ^ m) q) =
          curvePullbackTraceValue (componentι f i ≫ f) ℓ m φ' w' hnc q := fun i => by
    have : Smooth (componentι f i ≫ f) := SmoothOfRelativeDimension.smooth 1 _
    exact exists_curveModel (componentι f i ≫ f) hm hℓ q
  choose r em hem using hmod
  have hn : IsUnit ((ℓ ^ m : ℕ) : Γ(Y, ⊤)) := by
    refine isUnit_natCast_sections Ω f ?_
    rw [Nat.cast_pow]; exact (isUnit_iff_ne_zero.mpr hℓ).pow m
  refine ⟨r, disjointUnionModel.{u + 1, u, 0} (componentι f) (pairwise_disjoint_range_componentι f)
    (iUnion_range_componentι f) hn q em, ?_⟩
  rw [modelTrace_rootsOfUnityPullbackMap_eq_sum.{u + 1, u, 0} (componentι f)
    (pairwise_disjoint_range_componentι f)
    (iUnion_range_componentι f) hn q φ (IsSelfComponent f φ) (componentSelfMap f φ)
    (componentSelfMap_comp f φ) (exists_componentMove f φ) em, componentTraceSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · exact hem i _ (componentSelfMap_comp_structure f φ w i h)
      (componentSelfMap_not_constant f φ p hY e Ψ hΨ' i h)
  · rfl

end Stacks.EtaleCohomology

end
