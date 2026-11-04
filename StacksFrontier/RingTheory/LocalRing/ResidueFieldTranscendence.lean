module

public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# A field of large transcendence degree inside a local algebra over a field

Let `K` be a field and `A` a local `K`-algebra. Lifting a transcendence basis of the residue
field `κ(A)` over `K` to elements `y_i` of `A`, every nonzero polynomial in the `y_i` has nonzero
image in `κ(A)`, hence is a unit of `A`; so the rational function field in the `y_i` maps into
`A` over `K`. Its transcendence degree over `K` is that of `κ(A)`.

This is the embedding `K(t_1, …, t_a) ⟶ 𝒪^{sh}_{X,x}`, `a = trdeg_K κ(x)`, used in Stacks 0F0U and
in Interlude I of the proof of Stacks 0F0V, for an arbitrary local `K`-algebra.

## Main results

* `IsLocalRing.exists_algHom_field_trdeg_residueField_le`: there is a field `L` over `K` with a
  `K`-algebra map `L ⟶ A` and `trdeg_K κ(A) ≤ trdeg_K L`.

## References

* [Stacks Project, Tag 0F0U](https://stacks.math.columbia.edu/tag/0F0U)
* [Stacks Project, Tag 0F0V](https://stacks.math.columbia.edu/tag/0F0V)
-/

@[expose] public section

universe u

namespace IsLocalRing

/-- **A local algebra over a field contains a field as transcendental as its residue field.**
Let `K` be a field and `A` a local `K`-algebra. There is a field `L` over `K` with a `K`-algebra
map `L ⟶ A` such that `trdeg_K κ(A) ≤ trdeg_K L`: lift a transcendence basis `x` of `κ(A)` over
`K` to `y` in `A`; a nonzero polynomial `p` has `p(x) ≠ 0`, so `p(y)` is a unit, and the fraction
field of `K[X_i]` maps into `A`. -/
theorem exists_algHom_field_trdeg_residueField_le (K A : Type u) [Field K] [CommRing A]
    [IsLocalRing A] [Algebra K A] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : L →ₐ[K] A),
      Algebra.trdeg K (ResidueField A) ≤ Algebra.trdeg K L := by
  classical
  have : FaithfulSMul K (ResidueField A) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap K (ResidueField A)).injective
  obtain ⟨ι, x, hx⟩ := exists_isTranscendenceBasis' K (ResidueField A)
  choose y hy using fun i => residue_surjective (R := A) (x i)
  let P := MvPolynomial ι K
  let ρ : A →ₐ[K] ResidueField A := IsScalarTower.toAlgHom K A (ResidueField A)
  have hρφ : ρ.comp (MvPolynomial.aeval y) = MvPolynomial.aeval x := by
    ext i
    simp [ρ, ← hy i]
  have hunit : ∀ p : nonZeroDivisors P, IsUnit (MvPolynomial.aeval (R := K) y p.1) := by
    rintro ⟨p, hp⟩
    rw [← residue_ne_zero_iff_isUnit]
    intro h0
    exact nonZeroDivisors.ne_zero hp
      (hx.1 (((DFunLike.congr_fun hρφ p).symm.trans h0).trans (map_zero _).symm))
  let ψ : FractionRing P →ₐ[K] A := IsLocalization.liftAlgHom hunit
  refine ⟨FractionRing P, inferInstance, inferInstance, ψ, ?_⟩
  have hcomp : (ρ.comp ψ) ∘ (fun i => algebraMap P (FractionRing P) (MvPolynomial.X i)) = x := by
    funext i
    simp [ψ, ρ, P, ← hy i]
  exact hx.cardinalMk_eq_trdeg.ge.trans
    (AlgebraicIndependent.of_comp (ρ.comp ψ) (hcomp ▸ hx.1)).cardinalMk_le_trdeg

end IsLocalRing
