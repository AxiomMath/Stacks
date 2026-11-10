module

public import StacksFrontier.RingTheory.DiscreteValuationRing.AbhyankarFieldFactor
public import StacksFrontier.RingTheory.DiscreteValuationRing.UnramifiedEtaleModel
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Abhyankar's lemma at a dominating discrete valuation ring

Let `O ⊆ O'` be discrete valuation rings with fraction fields `K ⊆ K''`, `K''/K` finite separable,
`O'` integral over `O`, and suppose a uniformizer `π` of `O` is the `e`-th power of a uniformizer
of `O'`. If `L/K` is tamely ramified with respect to `O` and all its ramification indices divide
`e`, then every field factor of `L ⊗_K K''` is unramified with respect to `O'`. This is a form of
Abhyankar's lemma ([Stacks, Tag 0BRM]).

## Main results

* `AlgebraicGeometry.Abhyankar.isUnramifiedWithRespectTo_of_tensor`: the statement above.

## References

* [Stacks Project, Tag 0BRM](https://stacks.math.columbia.edu/tag/0BRM)
* [Stacks Project, Tag 0EYG](https://stacks.math.columbia.edu/tag/0EYG)
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Abhyankar

/-- **Abhyankar's lemma at a dominating discrete valuation ring.** Let `O → O'` be discrete
valuation rings with fraction fields `K → K''`, `K''/K` finite separable and `O'` integral over
`O`, and let a uniformizer `π` of `O` map to `ϖ ^ e` for a uniformizer `ϖ` of `O'`. If `L/K` is
tamely ramified with respect to `O`, with all ramification indices dividing `e`, then every field
`L''` which is a quotient of `L ⊗_K K''` is unramified with respect to `O'`. -/
@[sga "1 X 3.6" "special case"]
theorem isUnramifiedWithRespectTo_of_tensor
    {O K L : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Field L]
    [Algebra O K] [IsFractionRing O K] [Algebra K L] [Algebra O L] [IsScalarTower O K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (htame : IsDiscreteValuationRing.IsTamelyRamifiedWithRespectTo O K L) {e : ℕ} (he : 0 < e)
    (hdiv : ∀ m : Ideal (integralClosure O L), m.IsMaximal → m.LiesOver (maximalIdeal O) →
      Ideal.ramificationIdx' (maximalIdeal O) m ∣ e)
    {O' K'' : Type u} [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Field K'']
    [Algebra O O'] [Algebra O' K''] [IsFractionRing O' K''] [Algebra K K''] [Algebra O K'']
    [IsScalarTower O O' K''] [IsScalarTower O K K'']
    [FiniteDimensional K K''] [Algebra.IsSeparable K K'']
    (hint : ∀ w : O', _root_.IsIntegral O (algebraMap O' K'' w))
    (π : O) (hπ : maximalIdeal O = Ideal.span {π}) (ϖ : O')
    (hϖ : maximalIdeal O' = Ideal.span {ϖ}) (hπϖ : algebraMap O O' π = ϖ ^ e)
    {L'' : Type u} [Field L''] [Algebra K'' L''] [FiniteDimensional K'' L'']
    [Algebra.IsSeparable K'' L''] [Algebra O' L''] [IsScalarTower O' K'' L'']
    [Algebra K L''] [IsScalarTower K K'' L'']
    (t : L ⊗[K] K'' →ₐ[K] L'') (ht : Function.Surjective t)
    (htF : ∀ f, t (1 ⊗ₜ f) = algebraMap K'' L'' f) :
    IsDiscreteValuationRing.IsUnramifiedWithRespectTo O' K'' L'' := by
  classical
  let A₁ := integralClosure O K''
  have hO'K : Function.Injective (algebraMap O' K'') := IsFractionRing.injective O' K''
  let f : O' →+* A₁ :=
    (algebraMap O' K'').codRestrict A₁.toSubring fun w ↦ hint w
  have hf : ∀ w, ((f w : A₁) : K'') = algebraMap O' K'' w := fun _ ↦ rfl
  have hfinj : Function.Injective f := fun w₁ w₂ h ↦ hO'K (congrArg Subtype.val h)
  have hfsurj : Function.Surjective f := by
    rintro ⟨z, hz⟩
    obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hz.tower_top (A := O'))
    exact ⟨w, Subtype.ext hw⟩
  let ε := RingEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  let σ : A₁ ≃+* O' := ε.symm
  have hσ : ∀ a : A₁, algebraMap O' K'' (σ a) = (a : K'') := by
    intro a
    obtain ⟨w, rfl⟩ := hfsurj a
    rw [show σ (f w) = w from ε.symm_apply_apply w]
    rfl
  have : IsDiscreteValuationRing A₁ :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing ε
  have : IsFractionRing A₁ K'' := by
    have : FaithfulSMul A₁ K'' :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
    refine IsFractionRing.of_field A₁ (K := K'') fun z ↦ ?_
    obtain ⟨w₁, w₂, -, rfl⟩ := IsFractionRing.div_surjective (A := O') z
    exact ⟨f w₁, f w₂, rfl⟩
  have hfO : ∀ o : O, f (algebraMap O O' o) = algebraMap O A₁ o := fun o ↦ Subtype.ext (by
    rw [hf, ← IsScalarTower.algebraMap_apply]
    rfl)
  have hϖ₁ : maximalIdeal A₁ = Ideal.span {f ϖ} := by
    rw [← map_ringEquiv_maximalIdeal ε, hϖ, Ideal.map_span,
      Set.image_singleton]
    rfl
  have hϖ0 : f ϖ ≠ 0 := fun h ↦ IsDiscreteValuationRing.not_a_field A₁
    (by rw [hϖ₁, h, Ideal.span_singleton_eq_bot.mpr rfl])
  have hπA : algebraMap O A₁ π = f ϖ ^ e := by rw [← hfO, hπϖ, map_pow]
  have hmap : (maximalIdeal O).map (algebraMap O A₁) = maximalIdeal A₁ ^ e := by
    rw [hπ, Ideal.map_span, Set.image_singleton, hπA, hϖ₁, Ideal.span_singleton_pow]
  have : Module.IsTorsionFree O A₁ := by
    apply Module.isTorsionFree_iff_algebraMap_injective.mpr
    intro a b h
    apply IsFractionRing.injective O K
    apply (algebraMap K K'').injective
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    exact congrArg Subtype.val h
  have : (maximalIdeal A₁).LiesOver (maximalIdeal O) := by
    constructor
    have hle : maximalIdeal O ≤ (maximalIdeal A₁).comap (algebraMap O A₁) := by
      rw [hπ, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, hπA, hϖ₁]
      exact Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) e he
    exact (IsLocalRing.maximalIdeal.isMaximal O).eq_of_le
      (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal A₁).ne_top) hle
  have hram : (maximalIdeal A₁).ramificationIdx O = e := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx _ _ (IsDiscreteValuationRing.not_a_field O)]
    apply Ideal.ramificationIdx'_spec
    · rw [hmap]
    · rw [hmap, hϖ₁, Ideal.span_singleton_pow, Ideal.span_singleton_pow,
        Ideal.span_singleton_le_span_singleton]
      rintro ⟨c, hc⟩
      have h1 : f ϖ ^ e * 1 = f ϖ ^ e * (f ϖ * c) := by rwa [mul_one, ← mul_assoc, ← pow_succ]
      have h2 := mul_left_cancel₀ (pow_ne_zero e hϖ0) h1
      exact (IsLocalRing.maximalIdeal.isMaximal A₁).ne_top (Ideal.eq_top_of_isUnit_mem _
        (by rw [hϖ₁]; exact Ideal.mem_span_singleton_self _)
        (IsUnit.of_mul_eq_one _ h2.symm))
  let : Algebra L L'' := (t.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom).toAlgebra
  have htL : ∀ l : L, t (l ⊗ₜ 1) = algebraMap L L'' l := fun _ ↦ rfl
  have : IsScalarTower K L L'' := IsScalarTower.of_algebraMap_eq fun k ↦ by
    rw [← htL, ← Algebra.TensorProduct.algebraMap_apply]
    exact (t.commutes k).symm
  let : Algebra O L'' := ((algebraMap K L'').comp (algebraMap O K)).toAlgebra
  have : IsScalarTower O K L'' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower O K'' L'' := IsScalarTower.of_algebraMap_eq fun o ↦ by
    change algebraMap K L'' (algebraMap O K o) = _
    rw [IsScalarTower.algebraMap_apply K K'' L'', ← IsScalarTower.algebraMap_apply O K K'']
  have : IsScalarTower O L L'' := IsScalarTower.of_algebraMap_eq fun o ↦ by
    change algebraMap K L'' (algebraMap O K o) = _
    rw [IsScalarTower.algebraMap_apply O K L, ← IsScalarTower.algebraMap_apply K L L'']
  have hunr :=
    IsDiscreteValuationRing.isUnramifiedWithRespectTo_integralClosure_of_tensorProduct_quotient
      O K L K'' L'' t ht htL htF htame (fun m hm hlo ↦ hram ▸ hdiv m hm hlo)
  exact IsDiscreteValuationRing.IsUnramifiedWithRespectTo.of_ringEquiv σ hσ hunr

end AlgebraicGeometry.Abhyankar
