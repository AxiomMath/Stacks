module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CurveEulerBridge.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.TensorCoherence.Basic
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Uniqueness
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Degree

/-!
# The numerical intersection number of an invertible module with a proper curve

Let `X` be a proper scheme of dimension at most one over a field `k` and let `𝓛` be an invertible
`𝒪_X`-module. The numerical intersection number `(𝓛 · X)` of [Stacks, Tag 0BEP] is the
coefficient of `n₁ ⋯ n_d` in the rational polynomial of total degree at most `d = dim X` whose
value at an integer vector `n` is `χ(X, 𝒪_X ⊗ 𝓛^{⊗ n₁} ⊗ ⋯ ⊗ 𝓛^{⊗ n_d})`. On a curve that
number is the degree of `𝓛` in the sense of [Stacks, Tag 0AYR]:

`deg_𝓛(X) = (𝓛 · X) = deg(𝓛)`.

## Main definitions

* `AlgebraicGeometry.IsSelfIntersectionNumber`: `c` is the self-intersection number
  `(𝓛^d · X)` of an invertible module with the whole of `X`.

## Main results

* `AlgebraicGeometry.twistedSheafUnitOneIso`: the twist of `𝒪_X` by the first tensor power of
  `𝓛` is `𝓛`.
* `AlgebraicGeometry.eq_invertibleCurveDegree_of_isSelfIntersectionNumber`:
  **[Stacks, Tag 0BS1] and [Stacks, Tag 0BS0]**, `(𝓛 · X) = deg(𝓛)`.
* `AlgebraicGeometry.isSelfIntersectionNumber_one_iff_of_topologicalKrullDim_eq_one`: on a scheme
  of dimension one the number of factors prescribed by [Stacks, Tag 0BEW] is one, which is the
  left equality `deg_𝓛(X) = (𝓛 · X)` of [Stacks, Tag 0BS1].
* `AlgebraicGeometry.IsSelfIntersectionNumber.unique`: a scheme has at most one self-intersection
  number with a given invertible module and number of factors.

## Implementation notes

The intersection number is formalized as a predicate on a rational number rather than as a
rational-valued function. The function would have to be the coefficient of the polynomial
produced by [Stacks, Tag 0BEM], and that existence statement is available in this development
only conditionally:
`AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_finiteDimensional_cohomology` carries
the finite-dimensionality of the cohomology of a coherent module on a proper scheme over a field
([Stacks, Tag 02O6]) as a hypothesis, and nothing in the development proves it. The
predicate needs no existence input, and `AlgebraicGeometry.eulerPolynomial_twistedSheaf_unique`
shows the polynomial is unique, so the predicate determines at most one number — which is
`AlgebraicGeometry.IsSelfIntersectionNumber.unique`. A proof of the identity for every polynomial
representing the Euler characteristics is therefore a proof of it for *the* polynomial, with the
definitional presupposition of the source's notation `(𝓛 · X)` made explicit.

The degree bound is `P.totalDegree ≤ d`, with no disjunct for the zero polynomial. [Stacks,
Tag 0BEM] states its bound as `P = 0 ∨ deg P ≤ dim Supp ℱ` because the dimension of an empty
support is `⊥`; the zero polynomial has total degree `0`, so over a bound in `ℕ` the disjunction
is subsumed and nothing is lost.

Only the two exponents `0` and `1` are used, through
`AlgebraicGeometry.twistedSheafZeroIso` and `AlgebraicGeometry.twistedSheafUpdateIso`. The degree
bound is what makes those two values determine the coefficient, and it is the only place the
dimension of `X` enters the proof: ampleness of `𝓛` plays no part, so the identity below holds
for every invertible module. In the source ampleness is what makes the notation `deg_𝓛(X)` of
[Stacks, Tag 0BEW] defined and the integer positive, the latter being [Stacks, Tag 0B5X].

## References

* [Stacks Project, Tag 0BS1](https://stacks.math.columbia.edu/tag/0BS1)
* [Stacks Project, Tag 0BS0](https://stacks.math.columbia.edu/tag/0BS0)
* [Stacks Project, Tag 0BEP](https://stacks.math.columbia.edu/tag/0BEP)
* [Stacks Project, Tag 0BEW](https://stacks.math.columbia.edu/tag/0BEW)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.SheafOfModules.TensorSheafification
open Stacks.SheafOfModules.Invertible (tensorProductIso tensorProductLeftUnitor)

universe u

namespace MvPolynomial

/-- **A rational polynomial in one variable of total degree at most one, evaluated at a constant
tuple.** Its value is the constant coefficient plus the linear coefficient times the point. -/
theorem eval_const_eq_of_totalDegree_le_one {P : MvPolynomial (Fin 1) ℚ}
    (h : P.totalDegree ≤ 1) (t : ℚ) :
    eval (fun _ ↦ t) P = constantCoeff P + P.coeff (Finsupp.single 0 1) * t := by
  have hne : (Finsupp.single (0 : Fin 1) (1 : ℕ)) ≠ 0 := by simp
  have key : ∀ d : Fin 1 →₀ ℕ, d ∈ P.support → d = 0 ∨ d = Finsupp.single 0 1 := by
    intro d hdmem
    have hsum : d.sum (fun _ e ↦ e) ≤ 1 := (le_totalDegree hdmem).trans h
    rw [Finsupp.sum_fintype _ _ (fun _ ↦ rfl)] at hsum
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton] at hsum
    have hd : d = Finsupp.single 0 (d 0) := Finsupp.ext fun j ↦ by
      obtain rfl : j = 0 := Fin.fin_one_eq_zero j
      simp
    rcases Nat.lt_or_ge (d 0) 1 with h0 | h1
    · exact Or.inl (by rw [hd, Nat.lt_one_iff.mp h0]; simp)
    · exact Or.inr (by rw [hd, le_antisymm hsum h1])
  have hP : P = C (constantCoeff P) + C (P.coeff (Finsupp.single 0 1)) * X 0 := by
    ext d
    by_cases h0 : d = 0
    · subst h0; simp [coeff_C, coeff_X, constantCoeff, hne]
    by_cases h1 : d = Finsupp.single 0 1
    · subst h1; simp [coeff_C, coeff_X, Ne.symm hne]
    · have hns : d ∉ P.support := fun hm ↦ by
        rcases key d hm with h | h
        exacts [h0 h, h1 h]
      rw [notMem_support_iff.mp hns]
      simp [coeff_C, coeff_X, Ne.symm h0, Ne.symm h1]
  rw [hP]
  simp [Ne.symm hne]

end MvPolynomial

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- **The self-intersection number `(𝓛^d · X)` of [Stacks, Tag 0BEP], for the closed subscheme
`X` of itself.** The rational number `c` is the self-intersection number of the invertible module
`𝓛` with `d` factors when some rational polynomial of total degree at most `d` takes the Euler
characteristics of the twists of `𝒪_X` by integer powers of `𝓛` as its values at the integer
vectors and has `c` as the coefficient of `n₁ ⋯ n_d`. -/
@[sga "6 XIII 2.1" "Y = X and all L_i equal"]
def IsSelfIntersectionNumber (d : ℕ) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (c : ℚ) : Prop :=
  haveI : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f
  ∃ P : MvPolynomial (Fin d) ℚ, P.totalDegree ≤ d ∧
    (∀ n : Fin d → ℤ, MvPolynomial.eval (fun j ↦ (n j : ℚ)) P =
      (@eulerCharacteristic k _ X f _
        (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) (fun _ ↦ L) n)
        (twistedSheaf_isCoherent _ _ n) : ℚ)) ∧
    P.coeff (∑ j : Fin d, Finsupp.single j 1) = c

/-- **The twist of `𝒪_X` by the first tensor power of an invertible module is that module.**
Raising the single exponent from `0` to `1` tensors the empty twist of `𝒪_X` by `𝓛`, and
`𝒪_X ⊗ 𝓛 ≅ 𝓛`. -/
def twistedSheafUnitOneIso (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    twistedSheaf (SheafOfModules.unit X.ringCatSheaf) (fun _ : Fin 1 ↦ L)
      (fun _ ↦ (1 : ℤ)) ≅ L :=
  have hupd : Function.update (0 : Fin 1 → ℤ) 0 ((0 : Fin 1 → ℤ) 0 + 1) = fun _ ↦ (1 : ℤ) := by
    funext j
    obtain rfl : j = 0 := Fin.fin_one_eq_zero j
    simp
  eqToIso (congrArg
      (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) (fun _ : Fin 1 ↦ L)) hupd.symm) ≪≫
    twistedSheafUpdateIso (SheafOfModules.unit X.ringCatSheaf) (fun _ : Fin 1 ↦ L) 0 0 ≪≫
    tensorProductIso X.presheaf X.ringCatSheaf.2
      (twistedSheafZeroIso (SheafOfModules.unit X.ringCatSheaf) (fun _ : Fin 1 ↦ L))
      (Iso.refl L) ≪≫
    tensorProductLeftUnitor X.presheaf X.ringCatSheaf.2 L

/-- **[Stacks, Tag 0BS1] and [Stacks, Tag 0BS0]**: on a proper scheme of dimension at most one
over a field, the numerical intersection number of an invertible module with the whole space is
the degree of that module,

`(𝓛 · X) = deg(𝓛)`.

The polynomial of [Stacks, Tag 0BEM] has total degree at most one, so it is determined by its
values at `0` and `1`, where the twists of `𝒪_X` are `𝒪_X` and `𝓛`; its linear coefficient is
therefore `χ(X, 𝓛) - χ(X, 𝒪_X)`, which is the degree of [Stacks, Tag 0AYR]. -/
@[stacks 0BS0 "the numerical intersection number is the degree",
  stacks 0BS1 "the intersection number and the degree"]
theorem eq_invertibleCurveDegree_of_isSelfIntersectionNumber
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] {c : ℚ}
    (hc : IsSelfIntersectionNumber k f 1 L c) :
    c = (invertibleCurveDegree k f hdim L : ℚ) := by
  have hO : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f
  have hL : SheafOfModules.IsCoherent L :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k f L 1
  obtain ⟨P, hdeg, hval, hcoeff⟩ := hc
  -- The twist at the zero exponent is `𝒪_X`, and the twist at the exponent one is `𝓛`.
  have hzero : @eulerCharacteristic k _ X f _
      (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) (fun _ : Fin 1 ↦ L) (fun _ ↦ (0 : ℤ)))
      (twistedSheaf_isCoherent _ _ _) =
      eulerCharacteristic k f (SheafOfModules.unit X.ringCatSheaf) :=
    @eulerCharacteristic_eq_of_iso k _ X f _ _ _ (twistedSheaf_isCoherent _ _ _) hO
      (twistedSheafZeroIso (SheafOfModules.unit X.ringCatSheaf) (fun _ : Fin 1 ↦ L))
  have hone : @eulerCharacteristic k _ X f _
      (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) (fun _ : Fin 1 ↦ L) (fun _ ↦ (1 : ℤ)))
      (twistedSheaf_isCoherent _ _ _) = eulerCharacteristic k f L :=
    @eulerCharacteristic_eq_of_iso k _ X f _ _ _ (twistedSheaf_isCoherent _ _ _) hL
      (twistedSheafUnitOneIso L)
  -- The two values of the polynomial pin down its linear coefficient.
  have hlin : ∀ t : ℤ, MvPolynomial.constantCoeff P +
      P.coeff (Finsupp.single 0 1) * (t : ℚ) = @eulerCharacteristic k _ X f _
        (twistedSheaf (SheafOfModules.unit X.ringCatSheaf) (fun _ : Fin 1 ↦ L) (fun _ ↦ t))
        (twistedSheaf_isCoherent _ _ _) :=
    fun t ↦ (MvPolynomial.eval_const_eq_of_totalDegree_le_one hdeg t).symm.trans
      (hval fun _ ↦ t)
  have h0 := hlin 0
  have h1 := hlin 1
  rw [hzero] at h0
  rw [hone] at h1
  have hsingle : (∑ j : Fin 1, Finsupp.single j 1) = Finsupp.single (0 : Fin 1) (1 : ℕ) := by
    simp
  rw [hsingle] at hcoeff
  rw [@invertibleCurveDegree_eq_eulerCharacteristic_sub k _ X f _ hdim L _ hL hO]
  rw [← hcoeff]
  push_cast at h0 h1 ⊢
  linarith [h0, h1]

/-- **The number of factors that [Stacks, Tag 0BEW] prescribes on a scheme of dimension one is
one.** This is the left equality `deg_𝓛(X) = (𝓛 · X)` of [Stacks, Tag 0BS1]: the degree of `X`
with respect to `𝓛` is the self-intersection number with `dim X` factors.

Ampleness of `𝓛`, which [Stacks, Tag 0BEW] assumes, is not needed: it makes the notation
`deg_𝓛(X)` defined and the integer positive, the latter being [Stacks, Tag 0B5X]. -/
@[stacks 0BS1 "the degree of X with respect to an invertible module"]
theorem isSelfIntersectionNumber_one_iff_of_topologicalKrullDim_eq_one
    (hdim : topologicalKrullDim X = 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (c : ℚ) :
    IsSelfIntersectionNumber k f ((topologicalKrullDim X).unbotD 0).toNat L c ↔
      IsSelfIntersectionNumber k f 1 L c := by
  rw [hdim]
  rfl

/-- **A scheme has at most one self-intersection number with a given invertible module.** The
rational polynomial representing the Euler characteristics of the twists is unique, by
`AlgebraicGeometry.eulerPolynomial_twistedSheaf_unique`, so its coefficients are determined. -/
theorem IsSelfIntersectionNumber.unique {d : ℕ} (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] {c₁ c₂ : ℚ}
    (h₁ : IsSelfIntersectionNumber k f d L c₁) (h₂ : IsSelfIntersectionNumber k f d L c₂) :
    c₁ = c₂ := by
  have : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f
  obtain ⟨P, -, hvalP, hP⟩ := h₁
  obtain ⟨Q, -, hvalQ, hQ⟩ := h₂
  have hPQ : P = Q := eulerPolynomial_twistedSheaf_unique k f (fun _ ↦ L)
    (SheafOfModules.unit X.ringCatSheaf) ‹_› hvalP hvalQ
  rw [← hP, ← hQ, hPQ]

end AlgebraicGeometry

end
