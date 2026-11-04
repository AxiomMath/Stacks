module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Polynomial.Quotient
public import StacksFrontier.RingTheory.GeometricallyIrreducible.Subalgebra
public import StacksFrontier.RingTheory.GeometricallyIrreducible.TFAE
public import StacksFrontier.RingTheory.GeometricallyIrreducible.Tower

/-!
# Geometric irreducibility is detected at the generic point

Let `A` be an algebra over a field `k` whose nilradical `I` is prime, so that `Spec A` is
irreducible with generic point `I`. The following are equivalent: `A` is geometrically irreducible
over `k`; the residue field `κ(I)` is geometrically irreducible over `k`; the separable closure of
`k` in `κ(I)` is `k`. This is the affine case of Stacks 054Q.

## Main results

* `Algebra.isGeometricallyIrreducible_iff_of_isLocalization`: geometric irreducibility is
  invariant under localization at a submonoid with nilpotent kernel.
* `Algebra.isGeometricallyIrreducible_iff_quotient_of_le_nilradical`: geometric irreducibility
  only depends on the reduction.
* `Algebra.isGeometricallyIrreducible_iff_isFractionRing`: a domain over `k` is geometrically
  irreducible exactly when its fraction field is.
* `Algebra.isGeometricallyIrreducible_iff_residueField`: `A` is geometrically irreducible exactly
  when its residue field at the generic point is.
* `Algebra.isGeometricallyIrreducible_tfae_residueField`: the affine case of Stacks 054Q.
* `Algebra.separableClosure_ratFunc_eq_bot`: the separable closure of `k` in `k(X)` is `k`.
* `Algebra.isGeometricallyIrreducible_quotient_span_X_sq`: the dual numbers `k[X]/(X²)` are
  geometrically irreducible over `k`.
* `Algebra.not_isGeometricallyIrreducible_complex`: `ℂ` is not geometrically irreducible over `ℝ`.

## References

* [Stacks Project, Tag 054Q](https://stacks.math.columbia.edu/tag/054Q)
* [Stacks Project, Tag 037L](https://stacks.math.columbia.edu/tag/037L)
* [Stacks Project, Tag 0G33](https://stacks.math.columbia.edu/tag/0G33)
* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559)
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Algebra

/-! ## Transfer along dense embeddings of spectra -/

/-- A space that embeds densely into another is irreducible exactly when the other is. -/
theorem irreducibleSpace_iff_of_isEmbedding_denseRange {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {f : α → β} (hf : Topology.IsEmbedding f) (hd : DenseRange f) :
    IrreducibleSpace α ↔ IrreducibleSpace β := by
  refine ⟨fun hα => ?_, fun hβ => ?_⟩
  · have := hα
    exact irreducibleSpace_of_denseRange hf.continuous hd
  · have := hβ
    have hrange : IsIrreducible (Set.range f) := by
      rw [← isIrreducible_iff_closure, hd.closure_range]
      exact IrreducibleSpace.isIrreducible_univ β
    exact hf.toHomeomorph.irreducibleSpace_iff.mpr (Subtype.irreducibleSpace hrange)

/-- If `f : R →+* S` has nilpotent kernel and `comap f` is a topological embedding, then
`Spec S` and `Spec R` are simultaneously irreducible. -/
theorem irreducibleSpace_primeSpectrum_iff_of_isEmbedding {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hemb : Topology.IsEmbedding (PrimeSpectrum.comap f))
    (hker : RingHom.ker f ≤ nilradical R) :
    IrreducibleSpace (PrimeSpectrum S) ↔ IrreducibleSpace (PrimeSpectrum R) :=
  irreducibleSpace_iff_of_isEmbedding_denseRange hemb
    ((PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).mpr hker)

/-! ## The two moves between an algebra and its generic residue field -/

/-- Two `k`-algebras are simultaneously geometrically irreducible as soon as the spectra of their
base changes to every field extension `k'` of `k` are simultaneously irreducible. -/
private theorem isGeometricallyIrreducible_iff_of_forall_irreducibleSpace_iff (k A B : Type u)
    [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (key : ∀ (k' : Type u) [Field k'] [Algebra k k'],
      IrreducibleSpace (PrimeSpectrum (A ⊗[k] k')) ↔ IrreducibleSpace (PrimeSpectrum (B ⊗[k] k'))) :
    IsGeometricallyIrreducible k A ↔ IsGeometricallyIrreducible k B := by
  rw [isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_tensorProduct,
    isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_tensorProduct]
  exact ⟨fun h k' _ _ => (key k').mp (h k'), fun h k' _ _ => (key k').mpr (h k')⟩

/-- If `L` is a localization of the `k`-algebra `A` at a submonoid, and the kernel of `A → L`
consists of nilpotents, then `A` is geometrically irreducible over `k` if and only if `L` is. -/
theorem isGeometricallyIrreducible_iff_of_isLocalization (k A L : Type u) [Field k] [CommRing A]
    [CommRing L] [Algebra k A] [Algebra A L] [Algebra k L] [IsScalarTower k A L]
    (M : Submonoid A) [IsLocalization M L]
    (hker : RingHom.ker (algebraMap A L) ≤ nilradical A) :
    IsGeometricallyIrreducible k A ↔ IsGeometricallyIrreducible k L := by
  refine isGeometricallyIrreducible_iff_of_forall_irreducibleSpace_iff k A L
    fun k' _ _ => Iff.symm ?_
  let ψ : A ⊗[k] k' →ₐ[k] L ⊗[k] k' :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A L) (AlgHom.id k k')
  let : Algebra (A ⊗[k] k') (L ⊗[k] k') := ψ.toRingHom.toAlgebra
  let : Algebra A (L ⊗[k] k') := Algebra.TensorProduct.leftAlgebra
  let : IsScalarTower A (A ⊗[k] k') (L ⊗[k] k') := IsScalarTower.of_algebraMap_eq' (by
    ext x
    show (algebraMap A L x) ⊗ₜ[k] (1 : k') = ψ (x ⊗ₜ[k] (1 : k'))
    simp [ψ])
  have hcomm : (algebraMap (A ⊗[k] k') (L ⊗[k] k')).comp
      Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom := by
    ext x
    show ψ ((1 : A) ⊗ₜ[k] x) = (1 : L) ⊗ₜ[k] x
    simp [ψ]
  have : IsLocalization (Algebra.algebraMapSubmonoid (A ⊗[k] k') M) (L ⊗[k] k') :=
    IsLocalization.tensorProduct_tensorProduct k k' M L hcomm
  exact irreducibleSpace_primeSpectrum_iff_of_isEmbedding
    (algebraMap (A ⊗[k] k') (L ⊗[k] k'))
    (PrimeSpectrum.localization_comap_isEmbedding (L ⊗[k] k')
      (Algebra.algebraMapSubmonoid (A ⊗[k] k') M))
    (geomIrred_kernel_residue_denseRange k A L (IsScalarTower.toAlgHom k A L) hker k')

/-- If `I` is an ideal of nilpotents of the `k`-algebra `A`, then `A` is geometrically irreducible
over `k` if and only if `A ⧸ I` is. -/
theorem isGeometricallyIrreducible_iff_quotient_of_le_nilradical (k A : Type u) [Field k]
    [CommRing A] [Algebra k A] (I : Ideal A) (hI : I ≤ nilradical A) :
    IsGeometricallyIrreducible k A ↔ IsGeometricallyIrreducible k (A ⧸ I) := by
  refine isGeometricallyIrreducible_iff_of_forall_irreducibleSpace_iff k A (A ⧸ I)
    fun k' _ _ => Iff.symm ?_
  have hker : RingHom.ker (Ideal.Quotient.mkₐ k I).toRingHom ≤ nilradical A := by
    rwa [show (Ideal.Quotient.mkₐ k I).toRingHom = Ideal.Quotient.mk I from rfl, Ideal.mk_ker]
  exact irreducibleSpace_primeSpectrum_iff_of_isEmbedding
    (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I) (AlgHom.id k k')).toRingHom
    (PrimeSpectrum.isEmbedding_comap_of_surjective _ _
      (Algebra.TensorProduct.map_surjective _ _ Ideal.Quotient.mk_surjective
        Function.surjective_id))
    (geomIrred_kernel_residue_denseRange k A (A ⧸ I) (Ideal.Quotient.mkₐ k I) hker k')

/-- Geometric irreducibility is invariant under isomorphism of `k`-algebras. -/
theorem isGeometricallyIrreducible_congr (k A B : Type u) [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B) :
    IsGeometricallyIrreducible k A ↔ IsGeometricallyIrreducible k B := by
  refine isGeometricallyIrreducible_iff_of_forall_irreducibleSpace_iff k A B fun k' _ _ => ?_
  let E : A ⊗[k] k' ≃ₐ[k] B ⊗[k] k' :=
    Algebra.TensorProduct.congr e (AlgEquiv.refl (R := k) (A₁ := k'))
  exact ⟨fun h => have := h
      irreducibleSpace_primeSpectrum_of_injective E.symm.toRingHom E.symm.injective,
    fun h => have := h
      irreducibleSpace_primeSpectrum_of_injective E.toRingHom E.injective⟩

/-! ## The affine case of Stacks 054Q -/

/-- A domain `A` over a field `k` is geometrically irreducible over `k` if and only if its
fraction field `L` is. -/
theorem isGeometricallyIrreducible_iff_isFractionRing (k A L : Type u) [Field k] [CommRing A]
    [IsDomain A] [Field L] [Algebra A L] [IsFractionRing A L] [Algebra k A] [Algebra k L]
    [IsScalarTower k A L] :
    IsGeometricallyIrreducible k A ↔ IsGeometricallyIrreducible k L :=
  isGeometricallyIrreducible_iff_of_isLocalization k A L (nonZeroDivisors A)
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective A L)]; exact bot_le)

/-- Let `A` be an algebra over a field `k` whose spectrum is irreducible, so that the nilradical
`I` of `A` is prime and is the generic point of `Spec A`. Then `A` is geometrically irreducible
over `k` if and only if the residue field `κ(I)` at the generic point is. -/
theorem isGeometricallyIrreducible_iff_residueField (k A : Type u) [Field k] [CommRing A]
    [Algebra k A] (I : Ideal A) [I.IsPrime] (hI : I = nilradical A) :
    IsGeometricallyIrreducible k A ↔ IsGeometricallyIrreducible k I.ResidueField :=
  (isGeometricallyIrreducible_iff_quotient_of_le_nilradical k A I hI.le).trans
    (isGeometricallyIrreducible_iff_of_isLocalization k (A ⧸ I) I.ResidueField
      (nonZeroDivisors (A ⧸ I))
      (by
        rw [(RingHom.injective_iff_ker_eq_bot _).mp
          I.injective_algebraMap_quotient_residueField]
        exact bot_le))

/-- Let `A` be an algebra over a field `k` whose spectrum is
irreducible, i.e. whose nilradical `I` is prime; `I` is then the generic point of `Spec A` and
`κ(I)` is the function field. The following are equivalent.

1. `A` is geometrically irreducible over `k`;
2. `κ(I)` is geometrically irreducible over `k`;
3. the separable closure of `k` in `κ(I)` is `k` itself. -/
@[stacks 054Q "The affine case. The source states this for an irreducible scheme `X` over `k` and
  the residue field at its generic point; here `X = Spec A`, and that the spectrum is irreducible
  is expressed by the hypothesis that the nilradical of `A` is the prime `I`. The scheme-level
  statement is NOT proved here: deducing it needs in addition the reduction of geometric
  irreducibility to affine opens (Stacks 038G, formalized as
  `AlgebraicGeometry.geometricallyIrreducible_tfae_local`) and the identification of the residue
  field at the generic point with the generic residue field of an affine open's ring of
  sections."]
theorem isGeometricallyIrreducible_tfae_residueField (k A : Type u) [Field k] [CommRing A]
    [Algebra k A] (I : Ideal A) [I.IsPrime] (hI : I = nilradical A) :
    List.TFAE [IsGeometricallyIrreducible k A, IsGeometricallyIrreducible k I.ResidueField,
      separableClosure k I.ResidueField = ⊥] := by
  tfae_have 1 ↔ 2 := isGeometricallyIrreducible_iff_residueField k A I hI
  tfae_have 2 ↔ 3 :=
    (separableClosure.eq_bot_iff_geometricallyIrreducible k I.ResidueField).symm
  tfae_finish

/-! ## Examples -/

/-- The separable closure of `k` in the rational function field `k(X)` is `k`. -/
theorem separableClosure_ratFunc_eq_bot (k : Type u) [Field k] :
    separableClosure k (RatFunc k) = ⊥ :=
  (separableClosure.eq_bot_iff_geometricallyIrreducible k (RatFunc k)).mpr
    ((isGeometricallyIrreducible_iff_isFractionRing k (Polynomial k) (RatFunc k)).mp
      (isGeometricallyIrreducible_polynomial k))

/-- The dual numbers `k[X]/(X²)` are geometrically irreducible over `k`. -/
theorem isGeometricallyIrreducible_quotient_span_X_sq (k : Type u) [Field k] :
    IsGeometricallyIrreducible k
      (Polynomial k ⧸ Ideal.span {(Polynomial.X : Polynomial k) ^ 2}) := by
  have hle : Ideal.span {(Polynomial.X : Polynomial k) ^ 2} ≤
      Ideal.span {(Polynomial.X : Polynomial k)} := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_span_singleton]
    exact ⟨Polynomial.X, sq Polynomial.X⟩
  have hnil : Ideal.map (Ideal.Quotient.mkₐ k (Ideal.span {(Polynomial.X : Polynomial k) ^ 2}))
      (Ideal.span {(Polynomial.X : Polynomial k)}) ≤
      nilradical (Polynomial k ⧸ Ideal.span {(Polynomial.X : Polynomial k) ^ 2}) := by
    rw [Ideal.map_le_iff_le_comap, Ideal.span_le, Set.singleton_subset_iff]
    refine ⟨2, ?_⟩
    show (Ideal.Quotient.mk _ (Polynomial.X : Polynomial k)) ^ 2 = 0
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  rw [isGeometricallyIrreducible_iff_quotient_of_le_nilradical k _ _ hnil]
  refine (isGeometricallyIrreducible_congr k _ k ?_).mpr (isGeometricallyIrreducible_self k)
  refine (DoubleQuot.quotQuotEquivQuotOfLEₐ k hle).trans
    ((Ideal.quotientEquivAlgOfEq k ?_).trans (Polynomial.quotientSpanXSubCAlgEquiv (0 : k)))
  simp

/-- `ℂ` is not geometrically irreducible over `ℝ`. -/
theorem not_isGeometricallyIrreducible_complex : ¬ IsGeometricallyIrreducible ℝ ℂ := by
  intro hgi
  have h : separableClosure ℝ ℂ = ⊥ :=
    (separableClosure.eq_bot_iff_geometricallyIrreducible ℝ ℂ).mpr hgi
  have hI : Complex.I ∈ separableClosure ℝ ℂ :=
    mem_separableClosure_iff.mpr (Algebra.IsSeparable.isSeparable ℝ Complex.I)
  rw [h, IntermediateField.mem_bot] at hI
  obtain ⟨r, hr⟩ := hI
  simpa using congrArg Complex.im hr

end Algebra

end
