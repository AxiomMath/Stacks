module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Unramified.Field
public import StacksCore.Tactic.StacksAttribute

/-!
# A separable algebraic extension is a localization of `k' ⊗_k k'`

Let `k` be a field and let `k'` be a separable algebraic field extension of `k`, and let

  `m : k' ⊗_k k' → k'`

be the multiplication map, the `k`-algebra homomorphism with `m (a ⊗ b) = a * b`. Then
there is a submonoid `S ⊆ k' ⊗_k k'` such that `m` exhibits `k'` as the localization of
`k' ⊗_k k'` at `S`. Equivalently, there is a submonoid `S` and a ring isomorphism
`φ : S⁻¹(k' ⊗_k k') ≃+* k'` with `φ ∘ ℓ = m`, where `ℓ` is the canonical localization
homomorphism.

## Conventions

The multiplication map is `Algebra.TensorProduct.lmul' k`, a surjective ring
homomorphism, and `k'` is made a `(k' ⊗_k k')`-algebra by taking that map as its
`algebraMap` via `RingHom.toAlgebra`. Localization at a multiplicative subset is
expressed by the typeclass `IsLocalization S T`, which encodes the universal property;
"separable algebraic" is `Algebra.IsAlgebraic k k'` together with
`Algebra.IsSeparable k k'`. The `IsLocalization S k'` form is the primary statement and
the explicit isomorphism `φ` with `φ ∘ ℓ = m` is the equivalent restatement.
-/

@[expose] public section

open scoped TensorProduct

/-- **Descent lemma.** For a separable algebraic extension `k'/k`, the
multiplication map `m = lmul' k : k' ⊗_k k' → k'` enjoys the following property:
every `a` in its kernel is annihilated by some `t` with `m t = 1`.

The proof works by descent to a finite (hence essentially finite type) separable
subextension `L = k(σ₁, …, σₙ)` containing all the field elements `σⱼ` that
appear in a representation `a = ∑ⱼ cⱼ · (1 ⊗ σⱼ - σⱼ ⊗ 1)` of `a` as a member of
the diagonal ideal. There, formal unramifiedness
(`Algebra.FormallyUnramified.of_isSeparable`) provides via
`Algebra.FormallyUnramified.iff_exists_tensorProduct` a diagonal idempotent `t'`
with `m_L t' = 1` and `(1 ⊗ s - s ⊗ 1) · t' = 0` for all `s : L`. Pushing `t'`
forward along `L ⊗_k L → k' ⊗_k k'` gives the required `t`. -/
theorem keyDescent (k k' : Type*) [Field k] [Field k'] [Algebra k k']
    [Algebra.IsAlgebraic k k'] [Algebra.IsSeparable k k']
    (a : k' ⊗[k] k') (ha : Algebra.TensorProduct.lmul' (R := k) (S := k') a = 0) :
    ∃ t : k' ⊗[k] k', Algebra.TensorProduct.lmul' (R := k) (S := k') t = 1 ∧ t * a = 0 := by
  have hmem : a ∈ KaehlerDifferential.ideal k k' := ha
  rw [← KaehlerDifferential.span_range_eq_ideal, Ideal.span, Submodule.mem_span_set'] at hmem
  obtain ⟨n, f, g, hsum⟩ := hmem
  have hg : ∀ i, ∃ σ : k', 1 ⊗ₜ[k] σ - σ ⊗ₜ[k] 1 = (g i : k' ⊗[k] k') := fun i => (g i).property
  choose σ hσ using hg
  set L := IntermediateField.adjoin k (Set.range σ)
  have hfin : FiniteDimensional k L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have : Algebra.EssFiniteType k L := Algebra.EssFiniteType.of_finiteType k L
  have : Algebra.FormallyUnramified k L := Algebra.FormallyUnramified.of_isSeparable k L
  obtain ⟨t', ht1, ht2⟩ :=
    (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := k) (S := L)).mp inferInstance
  set F : L ⊗[k] L →ₐ[k] k' ⊗[k] k' := Algebra.TensorProduct.map L.val L.val with hF
  -- `m` commutes with the forward map `F` and the inclusion `L.val`.
  have hcomp : (Algebra.TensorProduct.lmul' (R := k) (S := k')).comp F
      = L.val.comp (Algebra.TensorProduct.lmul' (R := k) (S := L)) := by
    ext x <;> simp [hF, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul]
  refine ⟨F t', ?_, ?_⟩
  · -- `m (F t') = L.val (m_L t') = L.val 1 = 1`.
    have := AlgHom.congr_fun hcomp t'
    simp only [AlgHom.comp_apply] at this
    rw [this, ht2]
    simp
  · -- `F t'` annihilates each generator `1 ⊗ σⱼ - σⱼ ⊗ 1`, hence annihilates `a`.
    have hterm : ∀ i, F t' * (↑(g i) : k' ⊗[k] k') = 0 := by
      intro i
      have hmemL : σ i ∈ L := IntermediateField.subset_adjoin k _ ⟨i, rfl⟩
      set σ' : L := ⟨σ i, hmemL⟩
      have hval : L.val σ' = σ i := rfl
      have hgF : (↑(g i) : k' ⊗[k] k') = F (1 ⊗ₜ[k] σ' - σ' ⊗ₜ[k] 1) := by
        rw [← hσ i, map_sub, hF, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
        simp [hval]
      rw [hgF, ← map_mul, mul_comm t', ht1 σ', map_zero]
    rw [← hsum, Finset.mul_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [smul_eq_mul, ← mul_assoc, mul_comm (F t') (f i), mul_assoc, hterm i, mul_zero]

/-- Stacks Tag 0C2X (Lemma 10.43.8), primary `IsLocalization` formulation.
For a separable algebraic field extension `k'/k`, equipping `k'` with the
`(k' ⊗_k k')`-algebra structure given by the multiplication map
`m = Algebra.TensorProduct.lmul' k`, there is a submonoid `S ⊆ k' ⊗_k k'` such
that `k'` is the localization of `k' ⊗_k k'` at `S`. -/
@[stacks 0C2X]
theorem exists_isLocalization_lmul'_of_isSeparable_isAlgebraic
    (k k' : Type*) [Field k] [Field k'] [Algebra k k']
    [Algebra.IsAlgebraic k k'] [Algebra.IsSeparable k k'] :
    letI : Algebra (k' ⊗[k] k') k' :=
      RingHom.toAlgebra (Algebra.TensorProduct.lmul' (R := k) (S := k')).toRingHom
    ∃ S : Submonoid (k' ⊗[k] k'), IsLocalization S k' := by
  let : Algebra (k' ⊗[k] k') k' :=
      RingHom.toAlgebra (Algebra.TensorProduct.lmul' (R := k) (S := k')).toRingHom
  have halg : (algebraMap (k' ⊗[k] k') k')
      = (Algebra.TensorProduct.lmul' (R := k) (S := k')).toRingHom :=
    RingHom.algebraMap_toAlgebra _
  set m := Algebra.TensorProduct.lmul' (R := k) (S := k') with hm
  -- The multiplicative set: preimage of the units (= nonzero elements) of `k'`.
  refine ⟨(IsUnit.submonoid k').comap m.toRingHom, ?_⟩
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · -- every element of `S` maps to a unit
    intro y
    rw [halg]
    exact y.property
  · -- `m` is surjective, so the localization condition `surj` is immediate
    intro z
    refine ⟨⟨z ⊗ₜ[k] 1, 1⟩, ?_⟩
    simp only [halg]
    change z * m 1 = m (z ⊗ₜ[k] 1)
    rw [map_one, mul_one, hm, Algebra.TensorProduct.lmul'_apply_tmul, mul_one]
  · -- if `m x = m y`, the descent lemma produces `t ∈ S` with `t·x = t·y`
    intro x y hxy
    rw [halg] at hxy
    have hxy' : m x = m y := hxy
    have ha : m (x - y) = 0 := by rw [map_sub, hxy', sub_self]
    obtain ⟨t, ht1, ht2⟩ := keyDescent k k' (x - y) ha
    refine ⟨⟨t, ?_⟩, ?_⟩
    · change IsUnit (m t)
      rw [hm, ht1]
      exact isUnit_one
    · linear_combination ht2

/-- Stacks Tag 0C2X (Lemma 10.43.8), equivalent isomorphism formulation.
There exists a submonoid `S ⊆ k' ⊗_k k'` and a ring isomorphism
`φ : S⁻¹(k' ⊗_k k') ≃+* k'` such that `φ ∘ ℓ = m`, where
`ℓ : k' ⊗_k k' → S⁻¹(k' ⊗_k k')` is the canonical localization homomorphism and
`m = Algebra.TensorProduct.lmul' k` is the multiplication map. -/
theorem exists_localizationRingEquiv_lmul'_of_isSeparable_isAlgebraic
    (k k' : Type*) [Field k] [Field k'] [Algebra k k']
    [Algebra.IsAlgebraic k k'] [Algebra.IsSeparable k k'] :
    ∃ (S : Submonoid (k' ⊗[k] k'))
      (φ : Localization S ≃+* k'),
      ∀ x : k' ⊗[k] k',
        φ (algebraMap (k' ⊗[k] k') (Localization S) x)
          = Algebra.TensorProduct.lmul' (R := k) (S := k') x := by
  let : Algebra (k' ⊗[k] k') k' :=
      RingHom.toAlgebra (Algebra.TensorProduct.lmul' (R := k) (S := k')).toRingHom
  obtain ⟨S, hS⟩ := exists_isLocalization_lmul'_of_isSeparable_isAlgebraic k k'
  have : IsLocalization S k' := hS
  -- the unique `(k' ⊗ k')`-algebra isomorphism between the two localizations
  refine ⟨S, (IsLocalization.algEquiv S (Localization S) k').toRingEquiv, ?_⟩
  intro x
  simp only [AlgEquiv.coe_ringEquiv]
  -- `algEquiv` commutes with the structure maps, and `algebraMap` here is `lmul'`
  exact (IsLocalization.algEquiv S (Localization S) k').commutes x
