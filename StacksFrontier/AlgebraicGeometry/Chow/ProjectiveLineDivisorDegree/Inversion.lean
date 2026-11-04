module

public import Mathlib.Algebra.Polynomial.Reverse
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardDivisor

/-!
# The coordinate inversion of the projective line and the order at the origin

The projective line over a field `k` is covered by two affine lines glued along the inversion
`t ↦ t⁻¹` of the coordinate. On rational functions this gluing is the `k`-algebra endomorphism
`tau` of `RatFunc k` determined by `tau X = X⁻¹`, which exchanges the origin of one chart with
the point at infinity of the other. The order of `tau g` at the origin is minus the integer degree
of `g`, that is, the order of `g` at infinity in the sense of `Stacks.Chow.ordAtInfty`.

## Main results

* `Stacks.Chow.ordAt_eq_zero_of_not_irreducible` — `Stacks.Chow.ordAt p` vanishes when `p` is
  not irreducible.
* `Stacks.Chow.ordAt_X_eq_neg_intDegree` — for a `k`-algebra ring endomorphism `tau` of
  `RatFunc k` inverting the coordinate, `ordAt X (tau g) = -g.intDegree` for every nonzero `g`.

## References

* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
-/

@[expose] public noncomputable section

open Polynomial UniqueFactorizationMonoid

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k] [DecidableEq k]

/-- The order `ordAt p g` vanishes when `p` is not irreducible. -/
theorem ordAt_eq_zero_of_not_irreducible {k : Type u} [Field k] [DecidableEq k]
    {p : Polynomial k} (hp : ¬ Irreducible p) (g : RatFunc k) : ordAt p g = 0 := by
  have key : ∀ q : k[X], (normalizedFactors q).count p = 0 := fun q =>
    Multiset.count_eq_zero_of_notMem fun hmem => hp (irreducible_of_normalized_factor _ hmem)
  simp [ordAt, key]

/-- The multiplicity of `X` in a power of `X` is the exponent. -/
private theorem count_X_normalizedFactors_X_pow (d : ℕ) :
    (normalizedFactors (Polynomial.X ^ d : k[X])).count Polynomial.X = d := by
  rw [normalizedFactors_pow, normalizedFactors_irreducible irreducible_X,
    monic_X.normalize_eq_self, Multiset.count_nsmul, Multiset.count_singleton_self, mul_one]

/-- `X` is not a normalized factor of the reverse of a nonzero polynomial. -/
private theorem count_X_normalizedFactors_reverse {a : k[X]} (ha : a ≠ 0) :
    (normalizedFactors a.reverse).count Polynomial.X = 0 := by
  refine Multiset.count_eq_zero_of_notMem fun hmem => ?_
  have hdvd : (Polynomial.X : k[X]) ∣ a.reverse := dvd_of_mem_normalizedFactors hmem
  rw [Polynomial.X_dvd_iff, coeff_zero_reverse] at hdvd
  exact leadingCoeff_ne_zero.mpr ha hdvd

omit [DecidableEq k] in
/-- An endomorphism of `RatFunc k` fixing the constants and sending the coordinate to `y` is
evaluation at `y` on polynomials. -/
private theorem tau_algebraMap_eq_eval₂ (tau : RatFunc k →+* RatFunc k)
    (hconst : ∀ x : k, tau (algebraMap k (RatFunc k) x) = algebraMap k (RatFunc k) x)
    {y : RatFunc k} (hX : tau RatFunc.X = y) (a : k[X]) :
    tau (algebraMap k[X] (RatFunc k) a) = Polynomial.eval₂ (algebraMap k (RatFunc k)) y a := by
  have h : tau.comp (algebraMap k[X] (RatFunc k)) =
      Polynomial.eval₂RingHom (algebraMap k (RatFunc k)) y := by
    refine Polynomial.ringHom_ext (fun x => ?_) ?_
    · simpa [RatFunc.algebraMap_eq_C, RatFunc.algebraMap_C] using hconst x
    · simpa [RatFunc.algebraMap_X] using hX
  exact congrArg (fun f : k[X] →+* RatFunc k => f a) h

omit [DecidableEq k] in
/-- Evaluation at `RatFunc.X` is the structure map `k[X] → RatFunc k`. -/
private theorem eval₂_X_eq_algebraMap (a : k[X]) :
    Polynomial.eval₂ (algebraMap k (RatFunc k)) (RatFunc.X : RatFunc k) a =
      algebraMap k[X] (RatFunc k) a :=
  (tau_algebraMap_eq_eval₂ (RingHom.id _) (fun _ => rfl) rfl a).symm

omit [DecidableEq k] in
/-- An endomorphism of `RatFunc k` fixing the constants and inverting the coordinate carries a
polynomial `a` to its reverse divided by `X ^ a.natDegree`. -/
private theorem tau_algebraMap (tau : RatFunc k →+* RatFunc k)
    (hconst : ∀ x : k, tau (algebraMap k (RatFunc k) x) = algebraMap k (RatFunc k) x)
    (hX : tau RatFunc.X = (RatFunc.X : RatFunc k)⁻¹) (a : k[X]) :
    tau (algebraMap k[X] (RatFunc k) a) =
      algebraMap k[X] (RatFunc k) a.reverse /
        algebraMap k[X] (RatFunc k) (Polynomial.X ^ a.natDegree) := by
  have hXinv : (RatFunc.X : RatFunc k)⁻¹ ≠ 0 := inv_ne_zero RatFunc.X_ne_zero
  let _ : Invertible ((RatFunc.X : RatFunc k)⁻¹) := invertibleOfNonzero hXinv
  have hinvOf : ⅟((RatFunc.X : RatFunc k)⁻¹) = RatFunc.X := by simp
  have key := Polynomial.eval₂_reverse_mul_pow (algebraMap k (RatFunc k))
    ((RatFunc.X : RatFunc k)⁻¹) a
  rw [hinvOf, eval₂_X_eq_algebraMap] at key
  rw [tau_algebraMap_eq_eval₂ tau hconst hX, ← key, map_pow, RatFunc.algebraMap_X,
    inv_pow, ← div_eq_mul_inv]

/-- A `k`-algebra ring endomorphism of `RatFunc k` inverting the coordinate carries a
polynomial to a rational function whose order at the origin is minus the degree. -/
private theorem ordAt_X_tau_algebraMap (tau : RatFunc k →+* RatFunc k)
    (hconst : ∀ x : k, tau (algebraMap k (RatFunc k) x) = algebraMap k (RatFunc k) x)
    (hX : tau RatFunc.X = (RatFunc.X : RatFunc k)⁻¹) {a : k[X]} (ha : a ≠ 0) :
    ordAt (Polynomial.X : k[X]) (tau (algebraMap k[X] (RatFunc k) a)) = -(a.natDegree : ℤ) := by
  have hrev : a.reverse ≠ 0 := by
    simpa [Polynomial.reverse_eq_zero] using ha
  have hpow : (Polynomial.X ^ a.natDegree : k[X]) ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
  rw [tau_algebraMap tau hconst hX, ordAt_div _ hrev hpow,
    count_X_normalizedFactors_reverse ha, count_X_normalizedFactors_X_pow]
  simp

/-- A `k`-algebra ring endomorphism of `RatFunc k` inverting the coordinate carries a nonzero
rational function to one whose order at the origin is minus the integer degree. -/
theorem ordAt_X_eq_neg_intDegree {k : Type u} [Field k] [DecidableEq k]
    (tau : RatFunc k →+* RatFunc k)
    (hconst : ∀ x : k, tau (algebraMap k (RatFunc k) x) = algebraMap k (RatFunc k) x)
    (hX : tau RatFunc.X = (RatFunc.X : RatFunc k)⁻¹)
    (g : RatFunc k) (hg : g ≠ 0) :
    ordAt (Polynomial.X : Polynomial k) (tau g) = - g.intDegree := by
  have hnum : g.num ≠ 0 := RatFunc.num_ne_zero hg
  have hden : g.denom ≠ 0 := RatFunc.denom_ne_zero g
  have hne : ∀ a : k[X], a ≠ 0 → tau (algebraMap k[X] (RatFunc k) a) ≠ 0 := fun a ha =>
    (map_ne_zero_iff _ tau.injective).mpr
      ((map_ne_zero_iff _ (RatFunc.algebraMap_injective k)).mpr ha)
  have htaunum := hne _ hnum
  have htauden := hne _ hden
  have hsplit : tau g = tau (algebraMap k[X] (RatFunc k) g.num) *
      (tau (algebraMap k[X] (RatFunc k) g.denom))⁻¹ := by
    rw [← map_inv₀, ← map_mul, ← div_eq_mul_inv, RatFunc.num_div_denom]
  have hinvden : ordAt (Polynomial.X : k[X])
      ((tau (algebraMap k[X] (RatFunc k) g.denom))⁻¹) =
        -ordAt (Polynomial.X : k[X]) (tau (algebraMap k[X] (RatFunc k) g.denom)) := by
    have := ordAt_mul (Polynomial.X : k[X]) (inv_ne_zero htauden) htauden
    rw [inv_mul_cancel₀ htauden, ordAt_one] at this
    lia
  rw [hsplit, ordAt_mul _ htaunum (inv_ne_zero htauden), hinvden,
    ordAt_X_tau_algebraMap tau hconst hX hnum, ordAt_X_tau_algebraMap tau hconst hX hden,
    RatFunc.intDegree]
  lia

end Stacks.Chow

end
