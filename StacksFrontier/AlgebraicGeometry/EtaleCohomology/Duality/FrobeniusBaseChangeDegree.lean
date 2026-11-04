module

public import StacksFrontier.AlgebraicGeometry.Curves.TwistedFrobeniusDegree
public import StacksFrontier.AlgebraicGeometry.Picard.CurvePullbackDegree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ArithmeticFrobeniusInverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisActionFibreCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricFrobeniusUniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.CoverDense

/-!
# Pullback along `π̄ = π_X × id` multiplies degrees by `q`

Let `k` be a finite field with `q = p ^ f` elements, `Y` a scheme over `k` and `K` an
algebraically closed extension of `k` such that `Y_K` is a smooth proper curve over `K`. The base
change `π̄ = π_Y × id` of the geometric Frobenius is a morphism over `K` with
`(id × Spec(frob_k)) ≫ π̄ = F^f`, the `f`-fold absolute Frobenius of `Y_K`; since
`id × Spec(frob_k)` is an automorphism, `π̄` has degree `p ^ f = q`, and pulling back line
bundles along it multiplies degrees by `q` ([Stacks, Tag 0AYZ]).

## Main results

* `Stacks.Frobenius.galoisBaseChangeIso`: `id × Spec(σ)` as an automorphism of `Y_K`.
* `Stacks.Frobenius.not_constant_geometricFrobeniusBaseChange`: `π̄` is not constant.
* `Stacks.Frobenius.picardDegree_schemePullbackClassHom_geometricFrobeniusBaseChange`: pulling
  back a line bundle along `π̄` multiplies its degree by `q = #k`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Frobenius

section Iso

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) (K : Type u) [Field K] [Algebra k K]

/-- The automorphism `id_X × Spec(σ)` of `X_K`, with inverse `id_X × Spec(σ⁻¹)`. -/
def galoisBaseChangeIso (σ : K ≃ₐ[k] K) : fieldBaseChange X K ≅ fieldBaseChange X K where
  hom := galoisBaseChange X K σ
  inv := galoisBaseChange X K σ⁻¹
  hom_inv_id := by rw [← galoisBaseChange_mul, mul_inv_cancel, galoisBaseChange_one]
  inv_hom_id := by rw [← galoisBaseChange_mul, inv_mul_cancel, galoisBaseChange_one]

end Iso

variable {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k))) (K : Type u) [Field K]
  [Algebra k K] [IsAlgClosed K] (p f : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ f)
  [IsCurve K (pullback.snd Y.hom (specAlgebraMap k K))]

omit [IsAlgClosed K] in
/-- The morphism `π̄ = π_Y × id` of the curve `Y_K` is not constant. -/
theorem not_constant_geometricFrobeniusBaseChange :
    ¬ ∃ y : fieldBaseChange Y K, ∀ x : fieldBaseChange Y K,
      (geometricFrobeniusBaseChange Y K p f hcard).base x = y := by
  rintro ⟨y, hy⟩
  have hinj := (Stacks.EtaleCohomology.isHomeomorph_base_of_universalHomeomorphism
    (geometricFrobeniusBaseChange Y K p f hcard)).injective
  have : Subsingleton (fieldBaseChange Y K : Type u) :=
    ⟨fun a b => hinj ((hy a).trans (hy b).symm)⟩
  have : DiscreteTopology (fieldBaseChange Y K : Type u) := Subsingleton.discreteTopology
  have hle := topologicalKrullDim_zero_of_discreteTopology (fieldBaseChange Y K : Type u)
  rw [IsCurve.topologicalKrullDim_eq_one (pullback.snd Y.hom (specAlgebraMap k K))] at hle
  norm_num at hle

variable [Smooth (pullback.snd Y.hom (specAlgebraMap k K))]
  [IsProper (pullback.snd Y.hom (specAlgebraMap k K))]

/-- Pullback along `π̄ = π_Y × id` multiplies degrees of line bundles by `q = #k`, on a smooth
proper curve `Y_K` over an algebraically closed extension `K` of the finite field `k`. -/
theorem picardDegree_schemePullbackClassHom_geometricFrobeniusBaseChange
    (L : Picard.ofScheme (fieldBaseChange Y K)) :
    Picard.picardDegree (pullback.snd Y.hom (specAlgebraMap k K))
        (IsCurve.topologicalKrullDim_eq_one (f := pullback.snd Y.hom (specAlgebraMap k K))).le
        (Picard.schemePullbackClassHom (geometricFrobeniusBaseChange Y K p f hcard) L) =
      (Fintype.card k : ℤ) * Picard.picardDegree (pullback.snd Y.hom (specAlgebraMap k K))
        (IsCurve.topologicalKrullDim_eq_one (f := pullback.snd Y.hom (specAlgebraMap k K))).le
        L := by
  have : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  have hX := isInCharacteristic_fieldBaseChange Y K p
  have hnc := not_constant_geometricFrobeniusBaseChange Y K p f hcard
  have w := geometricFrobeniusBaseChange_comp_snd Y K p f hcard
  have hdeg := degreeOver_eq_pow_of_comp_eq_absoluteFrobeniusPow (k := K) p
    (pullback.snd Y.hom (specAlgebraMap k K)) hX (geometricFrobeniusBaseChange Y K p f hcard) w
    hnc f (Nat.pos_of_ne_zero (ne_zero_of_card_eq_pow hcard))
    (galoisBaseChangeIso Y K (arithmeticFrobenius k K p f hcard))
    (arithmeticFrobenius_comp_geometricFrobeniusBaseChange Y K p f hcard)
  rw [Picard.picardDegree_schemePullbackClassHom _ _ _ _ _ w hnc, hdeg, hcard]

end Stacks.Frobenius

end
