module

public import StacksCore.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.RingTheory.TensorProduct.Connected
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u v

/-!
# Geometric connectedness is detected by the finite separable extensions

Let `k` be a field and let `R` be a `k`-algebra. Then `R` is geometrically connected over `k`,
that is, `Spec (K ⊗[k] R)` is connected for every field extension `K/k`, if and only if
`Spec (K ⊗[k] R)` is connected for every finite separable field extension `K/k`.

## Main results

* `Stacks.GeometricallyConnectedCriterion.solution`: a `k`-algebra `R` over a field `k` is
  geometrically connected over `k` if and only if `Spec (K ⊗[k] R)` is connected for every finite
  separable field extension `K/k`.
* `Algebra.isGeometricallyConnected_iff_forall_finite_separable`: the same statement, in the
  namespace `Algebra`.

## References

* [Stacks 037S](https://stacks.math.columbia.edu/tag/037S)
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.GeometricallyConnectedCriterion

/-! ### Idempotents of the base change to the separable closure -/

/-- If the spectrum of `K ⊗[k] R` is connected for every finite separable extension `K/k`, then
`k^sep ⊗[k] R` has no nontrivial idempotent. -/
private theorem eq_zero_or_one_of_separableClosure (k : Type u) (R : Type v) [Field k] [CommRing R]
    [Algebra k R]
    (h : ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K] [Algebra.IsSeparable k K],
      ConnectedSpace (PrimeSpectrum (K ⊗[k] R)))
    (e : SeparableClosure k ⊗[k] R) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  classical
  obtain ⟨G, hG⟩ := TensorProduct.exists_finset e
  set F : Finset (SeparableClosure k) := G.image Prod.fst with hF
  set K : IntermediateField k (SeparableClosure k) :=
    IntermediateField.adjoin k (F : Set (SeparableClosure k))
  have : FiniteDimensional k K :=
    IntermediateField.finiteDimensional_adjoin fun x _ ↦ Algebra.IsIntegral.isIntegral x
  have : Algebra.IsSeparable k K :=
    Algebra.isSeparable_tower_bot_of_isSeparable k K (SeparableClosure k)
  set Φ := Algebra.TensorProduct.map K.val (AlgHom.id k R) with hΦ
  have hinj : Function.Injective Φ :=
    Stacks.TensorProduct.IdempotentBijection.tensorProduct_map_injective K.val (AlgHom.id k R)
      (by simp [IntermediateField.coe_val]) fun _ _ hab ↦ hab
  have hmem : e ∈ Φ.range := by
    rw [hG]
    refine Subalgebra.sum_mem _ fun p hp ↦ ?_
    refine ⟨(⟨p.1, IntermediateField.subset_adjoin k _ (by
      simp only [hF, Finset.coe_image, Set.mem_image, Finset.mem_coe]
      exact ⟨p, hp, rfl⟩)⟩ : K) ⊗ₜ[k] p.2, ?_⟩
    simp [hΦ]
  obtain ⟨e', he'⟩ := hmem
  have he'e : Φ e' = e := he'
  have he'i : IsIdempotentElem e' := hinj (by rw [map_mul, he'e, he])
  have hpc : PreconnectedSpace (PrimeSpectrum (K ⊗[k] R)) := (h K).toPreconnectedSpace
  rcases PrimeSpectrum.preconnectedSpace_iff_isIdempotentElem.mp hpc e' he'i with h1 | h1
  · exact Or.inl (by rw [← he'e, h1, map_zero])
  · exact Or.inr (by rw [← he'e, h1, map_one])

/-! ### From the separable closure to an arbitrary field extension -/

/-- If the spectrum of `k^sep ⊗[k] R` is connected for a separable closure `k^sep/k`, then the
spectrum of `K ⊗[k] R` is connected for every field extension `K/k`. -/
private theorem connectedSpace_primeSpectrum_of_separableClosure (k : Type u) (R : Type v) [Field k]
    [CommRing R] [Algebra k R] [Nontrivial R]
    [ConnectedSpace (PrimeSpectrum (SeparableClosure k ⊗[k] R))] (K : Type u) [Field K]
    [Algebra k K] : ConnectedSpace (PrimeSpectrum (K ⊗[k] R)) := by
  set φ : SeparableClosure k →ₐ[k] AlgebraicClosure K := IsAlgClosed.lift
  let _ : Algebra (SeparableClosure k) (AlgebraicClosure K) := φ.toRingHom.toAlgebra
  have : IsScalarTower k (SeparableClosure k) (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (φ.commutes x).symm
  set η := Algebra.TensorProduct.cancelBaseChange k (SeparableClosure k) (AlgebraicClosure K)
    (AlgebraicClosure K) R
  have hL : ∀ e : AlgebraicClosure K ⊗[k] R, IsIdempotentElem e → e = 0 ∨ e = 1 :=
    fun e he ↦ Stacks.TensorProduct.ConnectedSpectrum.eq_zero_or_one_of_injective
      (f := η.symm.toRingHom) η.symm.injective
      (fun x hx ↦ PrimeSpectrum.preconnectedSpace_iff_isIdempotentElem.mp inferInstance x hx) he
  refine PrimeSpectrum.connectedSpace_iff_isIdempotentElem.mpr fun e he ↦ ?_
  refine Stacks.TensorProduct.ConnectedSpectrum.eq_zero_or_one_of_injective
    (f := (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k K (AlgebraicClosure K))
      (AlgHom.id k R)).toRingHom)
    (Stacks.TensorProduct.IdempotentBijection.tensorProduct_map_injective _ _ ?_
      fun _ _ hab ↦ hab) hL he
  exact (algebraMap K (AlgebraicClosure K)).injective

/-! ### The lemma -/

/-- A `k`-algebra `R` over a field `k` is geometrically connected over `k` if and only if the
spectrum of `K ⊗[k] R` is connected for every finite separable field extension `K/k`. -/
public theorem solution (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R] :
    Algebra.IsGeometricallyConnected k R ↔
      ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K] [Algebra.IsSeparable k K],
        ConnectedSpace (PrimeSpectrum (K ⊗[k] R)) := by
  refine ⟨fun hR K _ _ _ _ ↦ hR.connectedSpace_primeSpectrum_tensorProduct K, fun h ↦ ?_⟩
  have hR : Nontrivial R :=
    have : Nontrivial (k ⊗[k] R) := PrimeSpectrum.nonempty_iff_nontrivial.mp (h k).toNonempty
    (Algebra.TensorProduct.lid k R).symm.toRingHom.domain_nontrivial
  have : ConnectedSpace (PrimeSpectrum (SeparableClosure k ⊗[k] R)) :=
    PrimeSpectrum.connectedSpace_iff_isIdempotentElem.mpr
      (eq_zero_or_one_of_separableClosure k R h)
  exact ⟨fun K _ _ ↦ connectedSpace_primeSpectrum_of_separableClosure k R K⟩

end Stacks.GeometricallyConnectedCriterion

end

@[expose] public section

open scoped TensorProduct

namespace Algebra

/-- **Geometric connectedness is detected by the finite separable extensions.** Let `k` be a
field and let `R` be a `k`-algebra. Then `R` is geometrically connected over `k`, that is,
`Spec (K ⊗[k] R)` is connected for every field extension `K/k`, if and only if `Spec (K ⊗[k] R)`
is connected for every finite separable field extension `K/k`. -/
@[stacks 037S "Geometric connectedness of a `k`-algebra need only be tested on the finite
  separable extensions of `k`. Condition (1) of the lemma is `Algebra.IsGeometricallyConnected`
  (Stacks 037T), which is that condition verbatim; `Spec` is `PrimeSpectrum` and `connected` is
  `ConnectedSpace`, which includes nonemptiness as the source's notion does.", ega "IV 8.4.5"
    "affine case", ega "IV 8.4.5" "affine case"]
public theorem isGeometricallyConnected_iff_forall_finite_separable (k : Type u) (R : Type v)
    [Field k] [CommRing R] [Algebra k R] :
    IsGeometricallyConnected k R ↔
      ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K] [Algebra.IsSeparable k K],
        ConnectedSpace (PrimeSpectrum (K ⊗[k] R)) :=
  Stacks.GeometricallyConnectedCriterion.solution k R

end Algebra

end
