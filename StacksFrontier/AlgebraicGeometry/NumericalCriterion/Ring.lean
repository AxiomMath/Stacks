module

public import StacksFrontier.RingTheory.RelativeDimension.Basic
public import StacksFrontier.RingTheory.Smooth.RegularLocalRing
public import StacksFrontier.RingTheory.Smooth.SmoothAt
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.Smooth.Locus

/-!
# Smoothness at a prime from a flatness-and-rank criterion

Let `R → A` be a ring map of finite presentation and let `𝔮` be a prime of `A` lying over
`𝔭 = R ∩ 𝔮`.  **This file proves that `A` is smooth at `𝔮` over `R` as soon as `A_𝔮` is flat over
`R` and the fibre `κ(𝔮) ⊗_A Ω_{A/R}` has dimension at most the relative dimension `dim_𝔮(A/R)`.**

It is the commutative algebra behind the implication `(4) ⟹ (1)` of Stacks Tag 01V9, and it is
the composite of two results of the library: Tag 00TT
(`Algebra.isSmoothAt_tfae_localKrullDim_and_isRegularLocalRing`), which turns the rank bound into
smoothness of the *fibre ring* `κ(𝔭) ⊗_R A` at the prime over `𝔮`, and Tag 00TF
(`Algebra.exists_notMem_smooth_of_isSmoothAt_fiber`), which descends smoothness of the fibre ring
back to `A` in the presence of flatness.

## Main results

* `Stacks.Tag01V9NumericalCriterion.finrank_tensor_residueField_eq`: the dimension of the
  residue-field fibre of a module is unchanged by enlarging the residue field along a tower, so
  the fibre may be computed over either of the two residue fields at hand.
* `Stacks.Tag01V9NumericalCriterion.finrank_fiberKaehler_eq`: the differentials of the fibre ring
  over `κ(𝔭)`, read at the prime over `𝔮`, have the same dimension as `κ(𝔮) ⊗_A Ω_{A/R}`.
* `Stacks.Tag01V9NumericalCriterion.isSmoothAt_of_flat_of_finrank_le`: **the criterion**.

## Implementation notes

The two residue fields in play are `κ(𝔮) = Ideal.ResidueField 𝔮`, over which the hypothesis is
stated, and `κ(𝔔) = Ideal.ResidueField 𝔔` for `𝔔` the prime of the fibre ring over `𝔮`, over
which Tag 00TT states its conclusion.  The map `κ(𝔮) → κ(𝔔)` is
`Ideal.ResidueField.mapₐ` of `Algebra.TensorProduct.includeRight`, and it is an extension of
fields, along which `Module.finrank` of a base change is invariant — that is
`finrank_tensor_residueField_eq`, proved by cancelling the base change.

## References

* [Stacks Project, Tag 00TF](https://stacks.math.columbia.edu/tag/00TF)
* [Stacks Project, Tag 00TT](https://stacks.math.columbia.edu/tag/00TT)
* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Stacks.Tag01V9NumericalCriterion

/-- **The dimension of a residue-field fibre does not change along an extension of the residue
field.**  If `κ → K` is an extension of fields over a common base ring `A`, then the `κ`-dimension
of `κ ⊗_A M` and the `K`-dimension of `K ⊗_A M` agree: the second is the base change of the first
along `κ → K`. -/
public theorem finrank_tensor_residueField_eq (A κ K : Type u) (M : Type v) [CommRing A]
    [Field κ] [Field K] [AddCommGroup M] [Module A M]
    [Algebra A κ] [Algebra A K] [Algebra κ K] [IsScalarTower A κ K] :
    Module.finrank κ (κ ⊗[A] M) = Module.finrank K (K ⊗[A] M) :=
  (Module.finrank_baseChange (R := K) (S := κ) (M' := κ ⊗[A] M)).symm.trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A κ K K M).finrank_eq

section Fiber

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (q : Ideal A) [q.IsPrime] (p : Ideal R) [p.IsPrime]
  (Q : Ideal (p.Fiber A)) [Q.IsPrime]

/-- The residue field at `𝔔` as an extension of the residue field at `𝔮`, through
`Algebra.TensorProduct.includeRight : A → κ(𝔭) ⊗_R A`. -/
public noncomputable abbrev algebraResidueFieldFiber
    (hQ : Q.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] p.Fiber A) = q) :
    Algebra q.ResidueField Q.ResidueField :=
  (Ideal.ResidueField.mapₐ q Q
    (Algebra.TensorProduct.includeRight : A →ₐ[R] p.Fiber A) hQ.symm).toRingHom.toAlgebra

/-- The tower `A → κ(𝔮) → κ(𝔔)`. -/
public theorem isScalarTower_residueFieldFiber
    (hQ : Q.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] p.Fiber A) = q) :
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := p.ResidueField) (B := A)
    letI := algebraResidueFieldFiber q p Q hQ
    IsScalarTower A q.ResidueField Q.ResidueField := by
  let _ : Algebra A (p.Fiber A) := Algebra.TensorProduct.rightAlgebra
  let _ := algebraResidueFieldFiber q p Q hQ
  refine IsScalarTower.of_algebraMap_eq fun a => ?_
  rw [IsScalarTower.algebraMap_eq A (p.Fiber A) Q.ResidueField]
  exact (Ideal.ResidueField.map_algebraMap q Q
    (Algebra.TensorProduct.includeRight : A →ₐ[R] p.Fiber A).toRingHom hQ.symm a).symm

/-- **The differentials of the fibre ring have the same residue-field fibre as the differentials
of `A`.**  Tag 00TT states its rank bound for the fibre ring `κ(𝔭) ⊗_R A` over `κ(𝔭)` at the
prime `𝔔`; conditions (3) and (4) of Tag 01V9 state theirs for `A` over `R` at `𝔮`.  The two
dimensions agree: `Ω` base changes along `A → κ(𝔭) ⊗_R A` by
`KaehlerDifferential.tensorKaehlerEquiv`, and the residue field may be enlarged from `κ(𝔮)` to
`κ(𝔔)` by `Stacks.Tag01V9NumericalCriterion.finrank_tensor_residueField_eq`. -/
public theorem finrank_fiberKaehler_eq
    (hQ : Q.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] p.Fiber A) = q) :
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := p.ResidueField) (B := A)
    Module.finrank Q.ResidueField
        (Q.ResidueField ⊗[p.Fiber A] Ω[(p.Fiber A)⁄p.ResidueField])
      = Module.finrank q.ResidueField (q.ResidueField ⊗[A] Ω[A⁄R]) := by
  let _ : Algebra A (p.Fiber A) := Algebra.TensorProduct.rightAlgebra
  let _ := algebraResidueFieldFiber q p Q hQ
  let _ := isScalarTower_residueFieldFiber q p Q hQ
  have e : Q.ResidueField ⊗[A] Ω[A⁄R] ≃ₗ[Q.ResidueField]
      Q.ResidueField ⊗[p.Fiber A] Ω[(p.Fiber A)⁄p.ResidueField] :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A (p.Fiber A) Q.ResidueField
        Q.ResidueField Ω[A⁄R]).symm.trans
      ((KaehlerDifferential.tensorKaehlerEquiv R p.ResidueField A (p.Fiber A)).baseChange
        _ Q.ResidueField _ _)
  exact e.finrank_eq.symm.trans
    (finrank_tensor_residueField_eq A q.ResidueField Q.ResidueField Ω[A⁄R]).symm

end Fiber

/-- **A flat algebra of finite presentation whose differential fibre is small is smooth at the
prime** (Stacks Tag 01V9, `(4) ⟹ (1)` at the level of rings).  If `A_𝔮` is flat over `R` and the
`κ(𝔮)`-dimension of `κ(𝔮) ⊗_A Ω_{A/R}` is at most the relative dimension `dim_𝔮(A/R)`, then `A`
is smooth at `𝔮` over `R`.

The route is the source's: Tag 00TT applied to the fibre ring `κ(𝔭) ⊗_R A`, which is of finite
type over the field `κ(𝔭)`, gives smoothness of the fibre ring at the prime over `𝔮`; Tag 00TF
then descends it to `A`, flatness being the hypothesis it needs. -/
public theorem isSmoothAt_of_flat_of_finrank_le {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.FinitePresentation R A] (q : Ideal A) [q.IsPrime]
    [Module.Flat R (Localization.AtPrime q)]
    (h : (Module.finrank q.ResidueField (q.ResidueField ⊗[A] Ω[A⁄R]) : WithBot ℕ∞) ≤
      Algebra.relativeDimensionAt R q) :
    Algebra.IsSmoothAt R q := by
  set p := q.under R
  obtain ⟨Q, hQprime, hQq⟩ := Ideal.Fiber.exists_comap_includeRight_eq q p rfl
  have _ : Q.IsPrime := hQprime
  let _ : Algebra A (p.Fiber A) := Algebra.TensorProduct.rightAlgebra
  have _ : Algebra.FiniteType p.ResidueField (p.Fiber A) := Algebra.FiniteType.baseChange _
  have hdim : (Module.finrank Q.ResidueField
      (Q.ResidueField ⊗[p.Fiber A] Ω[(p.Fiber A)⁄p.ResidueField]) : WithBot ℕ∞) ≤
      TopologicalSpace.localKrullDim (PrimeSpectrum (p.Fiber A)) ⟨Q, hQprime⟩ := by
    rwa [finrank_fiberKaehler_eq q p Q hQq,
      ← Algebra.relativeDimensionAt_eq_localKrullDim q p rfl Q hQq]
  have _ : Algebra.IsSmoothAt p.ResidueField Q :=
    ((Algebra.isSmoothAt_tfae_localKrullDim_and_isRegularLocalRing
      (k := p.ResidueField) ⟨Q, hQprime⟩ (Localization.AtPrime Q)).1.out 1 2).mpr hdim
  obtain ⟨g, hg, hsm⟩ := Algebra.exists_notMem_smooth_of_isSmoothAt_fiber p Q q hQq
    ⟨1, (Ideal.ne_top_iff_one q).mp ‹q.IsPrime›.ne_top, inferInstance⟩
  change (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum A) ∈ Algebra.smoothLocus R A
  exact Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr hsm hg

end Stacks.Tag01V9NumericalCriterion

end
