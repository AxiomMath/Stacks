module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.GRing.Henselization
public import StacksFrontier.RingTheory.Smoothing.ApproximationHenselianPair
public import StacksFrontier.RingTheory.Smoothing.PopescuTheorem
import StacksFrontier.RingTheory.Henselian.Pair.LocalRing

/-!
# Approximation of solutions over a henselian pair, and over a henselian G-ring

Let `(A, I)` be a henselian pair with `A` Noetherian and let `A^∧` be the `I`-adic completion of
`A`. A system of polynomial equations over `A` which has a solution in `A^∧` has, for every
`N ≥ 1`, a solution in `A` congruent to the given one modulo `I ^ N`. That is Lemma 0AH5, and
the source offers three alternative hypotheses under which it holds; this file proves it under
each of them. When `(A, I)` is a henselian *local* ring with its maximal ideal, this is the
approximation property of Theorem 07QY.

The mathematics of 0AH5 is in
`StacksFrontier/RingTheory/Smoothing/ApproximationHenselianPair.lean`, which carries out the
source's argument from the presentation of `A → A^∧` as a filtered colimit of smooth ring maps.
Each of the source's three hypotheses yields that presentation through Popescu's Theorem 07GC,
and 07GC is proved only downstream of that file, which is why the lemma is stated here.

## Main results

* `Stacks.Smoothing.indSmooth_adicCompletion_of_isGRing`: the adic completion of a G-ring is a
  filtered colimit of smooth algebras over it.
* `Stacks.Smoothing.indSmooth_adicCompletion_maximalIdeal_of_isLocalization`: for a local G-ring
  `R` which is a localization of a Noetherian ring `A`, the completion of `R` at its maximal
  ideal is a filtered colimit of smooth `A`-algebras — the form needed to present
  `Spec 𝒪^∧_{S,s}` over an affine open of `S` rather than over `Spec 𝒪_{S,s}`.
* `Stacks.Smoothing.isIndSmoothAdicCompletion_of_isGRing`: the same, in the spelling in which
  Lemma 0AH5 and Theorem 07QZ consume it.
* `Stacks.Smoothing.exists_solution_of_henselianPair_of_isRegularRingMap`,
  `Stacks.Smoothing.exists_solution_of_henselianPair_of_isGRing` and
  `Stacks.Smoothing.exists_solution_of_henselianPair_of_isGRing_henselization`: Lemma 0AH5 under
  the source's first, second and third alternative hypotheses.
* `Stacks.Smoothing.exists_approximate_solution_of_henselian_isGRing`: Theorem 07QY, the
  approximation property for henselian G-rings.

## Implementation notes

"`R` is a G-ring" is `IsGRing` (Tag 07GH) and the completion is Mathlib's `AdicCompletion`, so
`𝔪 ^ N R^∧` is `((maximalIdeal R) ^ N).map (algebraMap R (AdicCompletion (maximalIdeal R) R))`
and a solution of `f₁, …, f_m` in an `R`-algebra is a tuple annihilating each `f j` under
`MvPolynomial.aeval`. `N = 0` is admitted: the congruence is then vacuous and the solution is
obtained from the case `N = 1`.

The G-ring hypothesis enters exactly where the source puts it. Lemma 0AH2
(`isRegularRingHom_algebraMap_adicCompletion`) makes `A → A^∧` regular, Situation 07F2's spelling
of regularity is reached by `isRegularRingMap_of_regularRingHom`, and Popescu's
theorem (Tag 07GC, `indSmooth_of_isRegularRingMap`) then presents `A^∧` as a filtered colimit of
smooth `A`-algebras. That presentation is `IsIndSmoothAdicCompletion A I`, the input of
`exists_solution_of_henselianPair`. Popescu's theorem is unconditional, Lemma 07FJ — the
characteristic-`p` resolution of a local smoothing situation — being proved as
`Stacks.Smoothing.canBeResolvedInPositiveCharacteristic`, whose own λ-choice repair in the proof
of Stacks 07FH is due to Brian Nugent. So nothing below carries any hypothesis beyond the
source's own.

The three routes to `IsIndSmoothAdicCompletion A I` are the source's own reductions
(3) ⟹ (2) ⟹ (1):

* (1) is Popescu's theorem applied to `A → A^∧` directly. Regularity is taken in the Situation
  07F2 spelling `Stacks.Smoothing.IsRegularRingMap`, which is what Popescu's theorem consumes
  and which `Stacks.Smoothing.isRegularRingMap_of_regularRingHom` reaches from the general
  `IsRegularRingHom` of Tag 07BJ, the form in which every producer in this library — Lemma 0AH2
  among them — delivers it;
* (2) adds Lemma 0AH2, which makes `A → A^∧` regular for a G-ring `A`;
* (3) adds Lemma 0AH3 (`isGRing_henselization`), which makes the henselization of a pair over a
  G-ring a G-ring, and then applies (2). The henselization is described by the hypotheses of
  0AH3 themselves: `A` is an algebra over the Noetherian G-ring `C`, the pair `(A, J A)` is
  henselian, and `A` has the universal property of the henselization of `(C, J)`. That is the
  shape `exists_henselization` (Tag 0A02) produces, so a caller holding that datum can use the
  wrapper directly.

Theorem 07QY is the second route at the henselian pair `(R, 𝔪)` (`henselianPair_maximalIdeal`),
with `N = 0` admitted: the congruence is then vacuous and the solution is obtained from the case
`N = 1`. So the three cited inputs of its proof in the source are all present: 07GC here, and
07M7 and 04GG inside 0AH5.

## References

* [Stacks Project, Tag 07QY](https://stacks.math.columbia.edu/tag/07QY)
* [Stacks Project, Tag 07GC](https://stacks.math.columbia.edu/tag/07GC)
* [Stacks Project, Tag 0AH2](https://stacks.math.columbia.edu/tag/0AH2)
* [Stacks Project, Tag 0AH5](https://stacks.math.columbia.edu/tag/0AH5)
* [Stacks Project, Tag 0AH3](https://stacks.math.columbia.edu/tag/0AH3)
* [Stacks Project, Tag 07GH](https://stacks.math.columbia.edu/tag/07GH)
-/

@[expose] public section

open IsLocalRing

open scoped TensorProduct

universe u

namespace Stacks.Smoothing

/-- **Popescu's theorem for the completion of a G-ring.** The `I`-adic completion of a G-ring is
a filtered colimit of smooth algebras over it. -/
theorem indSmooth_adicCompletion_of_isGRing
    {R : Type u} [CommRing R] (hG : IsGRing R) (I : Ideal R) :
    IndSmooth R (AdicCompletion I R) := by
  let : IsNoetherianRing R := hG.1
  exact indSmooth_of_isRegularRingMap R (AdicCompletion I R)
    (isRegularRingMap_of_regularRingHom R (AdicCompletion I R)
      (isRegularRingHom_algebraMap_adicCompletion hG I))

/-- **Popescu's theorem for the completion of a local G-ring, read over a ring it localizes.**
Let `R` be a local G-ring which is a localization of a Noetherian ring `A`, and let `R^∧` be the
completion of `R` at its maximal ideal.  Then `R^∧` is a filtered colimit of smooth `A`-algebras,
for the `A`-algebra structure on `R^∧` given by `A → R → R^∧`.

This is the form in which the presentation is used over a *scheme*: for an affine open `U` of `S`
containing `s`, the local ring `𝒪_{S,s}` is a localization of `Γ(S, U)`, and the conclusion
presents `𝒪^∧_{S,s}` as a filtered colimit of algebras smooth over `Γ(S, U)` rather than merely
over `𝒪_{S,s}`.  Over `𝒪_{S,s}` alone the presentation carries no information about `S`, because
`Spec 𝒪_{S,s} → S` is not of finite type.

The two regular ring maps being composed are `A → R`, regular because it is a localization of a
Noetherian ring (`isRegularRingHom_of_isLocalization`), and `R → R^∧`, regular by Lemma
0AH2 (`isRegularRingHom_algebraMap_adicCompletion`); the composite is regular by Lemma
07QI (`isRegularRingHom_comp`), whose Noetherian-fibre hypothesis holds because `R^∧` is
Noetherian. -/
theorem indSmooth_adicCompletion_maximalIdeal_of_isLocalization
    {A R : Type u} [CommRing A] [CommRing R] [IsNoetherianRing A] [IsLocalRing R] [Algebra A R]
    (M : Submonoid A) [IsLocalization M R] (hG : IsGRing R) :
    letI : Algebra A (AdicCompletion (maximalIdeal R) R) :=
      ((algebraMap R (AdicCompletion (maximalIdeal R) R)).comp (algebraMap A R)).toAlgebra
    IndSmooth A (AdicCompletion (maximalIdeal R) R) := by
  let : IsNoetherianRing R := hG.1
  let : Algebra A (AdicCompletion (maximalIdeal R) R) :=
    ((algebraMap R (AdicCompletion (maximalIdeal R) R)).comp (algebraMap A R)).toAlgebra
  exact indSmooth_of_isRegularRingMap A (AdicCompletion (maximalIdeal R) R)
    (isRegularRingMap_of_regularRingHom A (AdicCompletion (maximalIdeal R) R)
      (isRegularRingHom_comp (algebraMap A R)
        (algebraMap R (AdicCompletion (maximalIdeal R) R))
        (isRegularRingHom_of_isLocalization M)
        (isRegularRingHom_algebraMap_adicCompletion hG (maximalIdeal R))
        (fun p _ ↦ p.isNoetherianRing_fiber _)))

/-- The hypothesis that Lemma 0AH5 and Theorem 07QZ carry in place of their appeal to Popescu's
theorem holds for a G-ring. -/
theorem isIndSmoothAdicCompletion_of_isGRing
    {R : Type u} [CommRing R] (hG : IsGRing R) (I : Ideal R) :
    IsIndSmoothAdicCompletion R I :=
  indSmooth_adicCompletion_of_isGRing hG I

/-! ### Lemma 0AH5 under each of the source's three hypotheses -/

/-- **Stacks 0AH5 under the source's first hypothesis.** Let `(A, I)` be a henselian pair with
`A` Noetherian such that `A → A^∧` is a regular ring map. A system of polynomial equations over
`A` with a solution in the completion has, for every `N ≥ 1`, a solution in `A` congruent to it
modulo `I ^ N`. -/
@[stacks 0AH5 "the conclusion under the source's FIRST alternative hypothesis, that `A → A^∧` is \
a regular ring map, with no other hypothesis: the appeal to Popescu's Theorem 07GC that the \
source makes here is `indSmooth_of_isRegularRingMap`, which is proved. Regularity is the \
Situation 07F2 spelling `IsRegularRingMap`, reached from the general `IsRegularRingHom` of 07BJ \
by the public `isRegularRingMap_of_regularRingHom`. The conclusion is the full one: a solution \
in `A` of the same system, congruent to the given one modulo the extension of `I ^ N` to `A^∧`, \
for every `N ≥ 1`. See also the two sibling wrappers for the source's other two alternatives."]
theorem exists_solution_of_henselianPair_of_isRegularRingMap
    {A : Type u} [CommRing A] {I : Ideal A} [IsNoetherianRing A]
    (hAI : HenselianPair A I) (hreg : IsRegularRingMap A (AdicCompletion I A))
    {m n : ℕ} (f : Fin m → MvPolynomial (Fin n) A)
    (â : Fin n → AdicCompletion I A) (hâ : ∀ j, MvPolynomial.aeval â (f j) = 0)
    {N : ℕ} (hN : N ≠ 0) :
    ∃ a : Fin n → A,
      (∀ i, â i - algebraMap A (AdicCompletion I A) (a i) ∈
        (I ^ N).map (algebraMap A (AdicCompletion I A))) ∧
      ∀ j, MvPolynomial.aeval a (f j) = 0 :=
  exists_solution_of_henselianPair hAI
    (indSmooth_of_isRegularRingMap A (AdicCompletion I A) hreg) f â hâ hN

/-- **Stacks 0AH5 under the source's second hypothesis.** Let `(A, I)` be a henselian pair with
`A` a Noetherian G-ring. A system of polynomial equations over `A` with a solution in the
completion has, for every `N ≥ 1`, a solution in `A` congruent to it modulo `I ^ N`. -/
@[stacks 0AH5 "the conclusion under the source's SECOND alternative hypothesis, that `A` is a \
Noetherian G-ring (`IsGRing`, Tag 07GH, whose first component is Noetherianness), with no other \
hypothesis. The source's reduction (2) ⟹ (1) is Lemma 0AH2 \
(`isRegularRingHom_algebraMap_adicCompletion`), and the appeal to Popescu's Theorem 07GC is \
`indSmooth_of_isRegularRingMap`, which is proved. The conclusion is the full one, as in the \
sibling wrapper for alternative (1)."]
theorem exists_solution_of_henselianPair_of_isGRing
    {A : Type u} [CommRing A] {I : Ideal A} (hG : IsGRing A) (hAI : HenselianPair A I)
    {m n : ℕ} (f : Fin m → MvPolynomial (Fin n) A)
    (â : Fin n → AdicCompletion I A) (hâ : ∀ j, MvPolynomial.aeval â (f j) = 0)
    {N : ℕ} (hN : N ≠ 0) :
    ∃ a : Fin n → A,
      (∀ i, â i - algebraMap A (AdicCompletion I A) (a i) ∈
        (I ^ N).map (algebraMap A (AdicCompletion I A))) ∧
      ∀ j, MvPolynomial.aeval a (f j) = 0 := by
  let : IsNoetherianRing A := hG.1
  exact exists_solution_of_henselianPair hAI (isIndSmoothAdicCompletion_of_isGRing hG I) f â hâ hN

/-- **Stacks 0AH5 under the source's third hypothesis.** Let `C` be a Noetherian G-ring, let
`J ⊂ C` be an ideal and let `A` be a henselization of the pair `(C, J)`. A system of polynomial
equations over `A` with a solution in the `J A`-adic completion of `A` has, for every `N ≥ 1`, a
solution in `A` congruent to it modulo `(J A) ^ N`. -/
@[stacks 0AH5 "the conclusion under the source's THIRD alternative hypothesis, that `(A, I)` is \
the henselization of a pair `(C, J)` with `C` a Noetherian G-ring, with no other hypothesis. The \
henselization is described exactly as in Lemma 0AH3 (`isGRing_henselization`): the \
pair `(A, J A)` is henselian and `A` has the universal property of the henselization of \
`(C, J)`, which is the datum `exists_henselization` (Tag 0A02) produces. The source's reduction \
(3) ⟹ (2) is that lemma, (2) ⟹ (1) is Lemma 0AH2, and the appeal to Popescu's Theorem 07GC is \
`indSmooth_of_isRegularRingMap`, which is proved. The conclusion is the full one, as in the \
sibling wrappers for alternatives (1) and (2)."]
theorem exists_solution_of_henselianPair_of_isGRing_henselization
    {C : Type u} [CommRing C] (hC : IsGRing C) (J : Ideal C)
    (A : Type u) [CommRing A] [Algebra C A]
    (hh : HenselianPair A (J.map (algebraMap C A)))
    (hι : ∀ (B : Type u) (_ : CommRing B) (K : Ideal B), HenselianPair B K →
      ∀ g : C →+* B, J ≤ K.comap g →
        ∃! t : A →+* B, t.comp (algebraMap C A) = g ∧ J.map (algebraMap C A) ≤ K.comap t)
    {m n : ℕ} (f : Fin m → MvPolynomial (Fin n) A)
    (â : Fin n → AdicCompletion (J.map (algebraMap C A)) A)
    (hâ : ∀ j, MvPolynomial.aeval â (f j) = 0) {N : ℕ} (hN : N ≠ 0) :
    ∃ a : Fin n → A,
      (∀ i, â i - algebraMap A (AdicCompletion (J.map (algebraMap C A)) A) (a i) ∈
        ((J.map (algebraMap C A)) ^ N).map
          (algebraMap A (AdicCompletion (J.map (algebraMap C A)) A))) ∧
      ∀ j, MvPolynomial.aeval a (f j) = 0 :=
  exists_solution_of_henselianPair_of_isGRing (isGRing_henselization hC J A hh hι) hh f â hâ hN

/-! ### Theorem 07QY -/

/-- **Stacks 07QY (the approximation property for G-rings).** Let `(R, 𝔪)` be a henselian local
G-ring. A system of polynomial equations over `R` with a solution in the `𝔪`-adic completion
`R^∧` has, for every `N`, a solution in `R` congruent to the given one modulo `𝔪 ^ N R^∧`. -/
@[stacks 07QY "the full conclusion for a henselian local G-ring -- general `m`, `n` and
every `N`, including `N = 0` -- with `𝔪^N R^∧` as the extension of `𝔪^N` to
`AdicCompletion (maximalIdeal R) R`, and with NO carried hypotheses. All three of the source's
cited inputs are formalized and used: Popescu's Theorem 07GC, reached from the G-ring hypothesis
through Lemma 0AH2; and 07M7 and 04GG, which are consumed inside Lemma 0AH5 applied
to the henselian pair `(R, 𝔪)`. Nothing else is assumed."]
theorem exists_approximate_solution_of_henselian_isGRing
    {R : Type u} [CommRing R] [HenselianLocalRing R] (hG : IsGRing R)
    {m n : ℕ} (f : Fin m → MvPolynomial (Fin n) R)
    (a : Fin n → AdicCompletion (maximalIdeal R) R)
    (ha : ∀ j, MvPolynomial.aeval a (f j) = 0) (N : ℕ) :
    ∃ b : Fin n → R,
      (∀ i, a i - algebraMap R (AdicCompletion (maximalIdeal R) R) (b i) ∈
        ((maximalIdeal R) ^ N).map (algebraMap R (AdicCompletion (maximalIdeal R) R))) ∧
      ∀ j, MvPolynomial.aeval b (f j) = 0 := by
  obtain ⟨b, hb, hsol⟩ := exists_solution_of_henselianPair_of_isGRing hG
    (henselianPair_maximalIdeal R) f a ha
    (N := max N 1) (Nat.one_le_iff_ne_zero.mp (le_max_right N 1))
  exact ⟨b, fun i => Ideal.map_mono (Ideal.pow_le_pow_right (le_max_left N 1)) (hb i), hsol⟩

end Stacks.Smoothing

end
