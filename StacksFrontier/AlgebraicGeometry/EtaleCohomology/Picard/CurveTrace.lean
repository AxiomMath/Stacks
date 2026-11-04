module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Picard.RootsOfUnitySecondCohomology

/-!
# The trace map `H²(X, μ_n) ≅ ℤ/n` of a smooth projective curve, from the degree

Let `X` be a smooth curve over an algebraically closed field `k` and `n` invertible in `k`. The
Kummer sequence and Stacks 03RM give `H²(X, μ_n) ≅ Pic(X)/n Pic(X)`
(`Stacks.Kummer.h2RootsOfUnityAddEquivPicardQuotient_of_smoothCurve`). For `X` projective the
degree `deg : Pic(X) → ℤ` is onto (a closed point has degree one) and its kernel `Pic⁰(X)` is
`n`-divisible (it is the group of `k`-points of the Jacobian, an abelian variety); then `deg` mod
`n` identifies `Pic(X)/n` with `ℤ/n`, and the composite

`tr : H²(X, μ_n) ≅ Pic(X)/n ≅ ℤ/n`

is the trace map of the curve, the last isomorphism of Stacks 03RQ in degree two and the trace of
the Poincaré duality of a curve used in the purity half of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH). It sends the image of the class of an
invertible module `ℒ` to `deg ℒ mod n`, which is what makes it compatible with Frobenius.

The degree map and the two facts about it are inputs from the Jacobian
(`Stacks.Picard.ofSchemeDegree`, which is not in this library). Here the degree is an
argument `deg` with the hypotheses `hdeg` (onto) and `hdiv` (`n`-divisible kernel), so the
declarations below become unconditional when instantiated at that degree map. No declaration of
this file is registered.

## Main definitions

* `Stacks.Kummer.curveTrace`: the trace `H²(X, μ_n) ≃+ ℤ/n` attached to a degree.

## Main results

* `Stacks.Kummer.quotientNsmulAddEquivZModOfSurjective_mk`: the class of `x` goes to `d x mod n`.
* `Stacks.Kummer.curveTrace_symm_mk`: the trace of the class of `ℒ` is `deg ℒ mod n`.
* `Stacks.Kummer.natCard_sheafH_two_rootsOfUnity_of_degree`: `#H²(X, μ_n) = n`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Kummer

/-- **The class of `x` in `P/nP` goes to `d x mod n`** under the identification
`Stacks.Kummer.quotientNsmulAddEquivZModOfSurjective`. -/
@[simp]
theorem quotientNsmulAddEquivZModOfSurjective_mk {P : Type*} [AddCommGroup P] (d : P →+ ℤ)
    (hd : Function.Surjective d) (n : ℕ) (hdiv : ∀ x : P, d x = 0 → ∃ y : P, n • y = x)
    (x : P) :
    quotientNsmulAddEquivZModOfSurjective d hd n hdiv (QuotientAddGroup.mk x) = (d x : ZMod n) :=
  rfl

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] {n : ℕ} (hn : IsUnit (n : k))
  (deg : Picard.ofScheme X →+ ℤ) (hdeg : Function.Surjective deg)
  (hdiv : ∀ L : Picard.ofScheme X, deg L = 0 → ∃ M : Picard.ofScheme X, n • M = L)

/-- **The trace map `H²(X, μ_n) ≅ ℤ/n` of a smooth curve over an algebraically closed field**,
attached to an onto degree `deg : Pic(X) → ℤ` with `n`-divisible kernel: the Kummer isomorphism
`H²(X, μ_n) ≅ Pic(X)/n` followed by `deg` mod `n`. -/
def curveTrace : Sheaf.H.{u + 1, u + 1} (rootsOfUnitySheaf.{u, u + 1} X n) 2 ≃+ ZMod n :=
  (h2RootsOfUnityAddEquivPicardQuotient_of_smoothCurve f hn).trans
    (quotientNsmulAddEquivZModOfSurjective deg hdeg n hdiv)

/-- **The trace of the class of an invertible module is its degree mod `n`.** -/
theorem curveTrace_symm_mk (L : Picard.ofScheme X) :
    curveTrace f hn deg hdeg hdiv
        ((h2RootsOfUnityAddEquivPicardQuotient_of_smoothCurve f hn).symm
          (QuotientAddGroup.mk L)) = (deg L : ZMod n) := by
  simp [curveTrace]

include f hn deg hdeg hdiv in
/-- **`#H²(X, μ_n) = n`** for a smooth curve over an algebraically closed field with an onto degree
whose kernel is `n`-divisible. -/
theorem natCard_sheafH_two_rootsOfUnity_of_degree :
    Nat.card (Sheaf.H.{u + 1, u + 1} (rootsOfUnitySheaf.{u, u + 1} X n) 2) = n := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have : NeZero n := ⟨hn0⟩
  rw [Nat.card_congr (curveTrace f hn deg hdeg hdiv).toEquiv, Nat.card_zmod]

end Stacks.Kummer

end
