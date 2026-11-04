module

public import StacksFrontier.AlgebraicGeometry.AffineMorphismEuler.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.BaseFieldInvariance
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.HilbertPolynomialNumerical
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.HyperplaneRegularity
public import StacksCore.Tactic.StacksAttribute

/-!
# The Hilbert polynomial of a coherent sheaf on projective space is a polynomial

For a field `k`, an integer `n ≥ 0` and a coherent sheaf `ℱ` on `ℙⁿ_k`, the function
`d ↦ χ(ℙⁿ_k, ℱ(d))` is a polynomial. This is [Stacks, Tag 08AC], read here through
[Stacks, Tag 00JX]'s notion of a numerical polynomial, `IsNumericalPolynomial`, which constrains
the function for `d ≫ 0`. **No hypothesis.** The tag's full every-integer reading — a `P ∈ ℚ[X]`
with `χ(ℙⁿ_k, ℱ(d)) = P(d)` for all `d ∈ ℤ` — is
`AlgebraicGeometry.exists_polynomial_eval_eq_hilbertPolynomial`, in
`StacksFrontier.AlgebraicGeometry.Variety.EulerChar.HilbertPolynomialFiniteDetermination`: it needs
the degree bound this file's induction is refined into there.

`AlgebraicGeometry.isNumericalPolynomial_hilbertPolynomial` carries out the source's induction on
`n` and its base case, granted one geometric input: the hypothesis `hstep`, the hyperplane
difference formula, which asserts that the first difference of the Hilbert polynomial of a
coherent sheaf on `ℙ^{m+1}_k` is again the Hilbert polynomial of a coherent sheaf, now on `ℙᵐ_k`.
**This file discharges `hstep`**, and so proves the tag outright.

## Main results

* `AlgebraicGeometry.exists_coherent_hilbertPolynomial_sub_eq`: **the hyperplane difference
  formula over an infinite field** — `hstep`, for an infinite base field.
* `AlgebraicGeometry.isNumericalPolynomial_hilbertPolynomial_of_infinite`: hence
  [Stacks, Tag 08AC] over an infinite field.
* `AlgebraicGeometry.isNumericalPolynomial_hilbertPolynomial'`: **[Stacks, Tag 08AC]** in the
  eventual reading of [Stacks, Tag 00JX], over an arbitrary field.

## How `hstep` is discharged

Over an **infinite** field the geometry is
`AlgebraicGeometry.exists_restrictionSequences`: for coherent `𝒢` on `ℙ^{m+1}_k` it produces a
coherent `ℋ` on `ℙᵐ_k`, an affine morphism `j : ℙᵐ_k ⟶ ℙ^{m+1}_k` over `Spec k`, and for every
`d` a short exact sequence `0 ⟶ 𝒢(d-1) ⟶ 𝒢(d) ⟶ j_*ℋ(d) ⟶ 0`. That is [Stacks, Tag 08A0]'s
sequence, twisted as in [Stacks, Tag 0EGK], with the hyperplane identified with `ℙᵐ_k` as in
[Stacks, Tag 089Z]. Three steps turn it into the displayed equation of the source's proof.

* **Additivity**, [Stacks, Tag 08AA]: the first difference of `d ↦ χ(ℙ^{m+1}_k, 𝒢(d))` is
  `d ↦ χ(ℙ^{m+1}_k, j_*ℋ(d))`. This is
  `AlgebraicGeometry.hilbertPolynomial_sub_eq_eulerCharacteristic_of_shortExact'`, whose single
  hypothesis `AlgebraicGeometry.CohomologyFiniteDimensionalOverField` — [Stacks, Tag 02O6] over a
  field base — is the theorem
  `AlgebraicGeometry.cohomologyFiniteDimensionalOverField_of_isProper`, itself
  `AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology` with its scalars restricted
  to `k`. So nothing is assumed here.
* **Descent along `j`**, [Stacks, Tag 089W]: `χ(ℙ^{m+1}_k, j_*ℋ(d)) = χ(ℙᵐ_k, ℋ(d))`, which is
  `AlgebraicGeometry.eulerCharacteristic_pushforward_of_isAffineHom`, `j` being affine.
* **`j` is a morphism over `Spec k`**, the last clause of `exists_restrictionSequences`. This is
  what makes the two Euler characteristics in the previous step comparable at all: both are
  alternating sums of `k`-dimensions, and the `k`-structure on the cohomology of `ℋ(d)` is read
  off the structure morphism, so a `j` not known to lie over `Spec k` would compute the right-hand
  side against a possibly different `k`-algebra structure on `Γ(ℙᵐ_k, 𝒪)` and no comparison of
  dimensions would be available. It also makes `j` proper — `j ≫ (ℙ^{m+1}_k ↘ Spec k)` is the
  structure morphism of `ℙᵐ_k`, and a morphism whose composite with a separated morphism is proper
  is proper — which is what makes `j_*ℋ(d)` coherent, by [Stacks, Tag 02O5].

Over an **arbitrary** field the source reduces to the infinite case by [Stacks, Tag 08AB], and so
does this file: the infinite extension is `RatFunc k`, the field of rational functions, infinite
by `AlgebraicGeometry.infinite_ratFunc`. `ℙⁿ_{RatFunc k}` is the base change of `ℙⁿ_k` along
`Spec (RatFunc k) ⟶ Spec k` (`AlgebraicGeometry.isPullback_projectiveSpaceFieldExtensionMap`),
the twists base-change (`AlgebraicGeometry.projectiveTwistPullbackIso`), and the Euler
characteristic of a coherent sheaf on a proper scheme is unchanged by extension of the ground
field (`AlgebraicGeometry.eulerCharacteristic_baseChange_field`, which is [Stacks, Tag 08AB]). So
the two Hilbert polynomials agree degree by degree and one is a numerical polynomial exactly when
the other is.

## Implementation notes

**[Stacks, Tag 08AC] is attached**, with no qualifier, to
`AlgebraicGeometry.isNumericalPolynomial_hilbertPolynomial'`. The clause-qualified attribute on
`AlgebraicGeometry.isNumericalPolynomial_hilbertPolynomial` is left where it is: that theorem is
the source's induction with `hstep` as an explicit hypothesis, which is still the reusable form,
and the two registrations together say that the induction and its one geometric input are both
accounted for.

**Why the Euler characteristic needs a congruence lemma for the structure morphism.**
`AlgebraicGeometry.eulerCharacteristic` takes the morphism to `Spec k` as an argument, so
`χ` along `j ≫ (ℙ^{m+1}_k ↘ Spec k)` and `χ` along `ℙᵐ_k ↘ Spec k` are, before the equation of
the two morphisms is used, different terms; `eulerCharacteristic_congr_structureMorphism`
substitutes one for the other. Its properness arguments are passed explicitly because the
right-hand side of the equation to be proved is a `hilbertPolynomial`, which carries no properness
argument for unification to fix.

## References

* [Stacks Project, Tag 08AC](https://stacks.math.columbia.edu/tag/08AC)
* [Stacks Project, Tag 08AB](https://stacks.math.columbia.edu/tag/08AB)
* [Stacks Project, Tag 08AA](https://stacks.math.columbia.edu/tag/08AA)
* [Stacks Project, Tag 08A0](https://stacks.math.columbia.edu/tag/08A0)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 089Z](https://stacks.math.columbia.edu/tag/089Z)
* [Stacks Project, Tag 00JX](https://stacks.math.columbia.edu/tag/00JX)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 0EGK](https://stacks.math.columbia.edu/tag/0EGK)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

attribute [local instance] isCoherent_projectiveTwist

/-- **The Euler characteristic depends on the structure morphism only through its value.** Two
equal morphisms `X ⟶ Spec k` give the same Euler characteristic of the same module, the
properness arguments being propositions. -/
public theorem eulerCharacteristic_congr_structureMorphism (k : Type u) [Field k]
    {X : Scheme.{u}} {f g : X ⟶ Spec (CommRingCat.of k)} (hfg : f = g)
    (hf : IsProper f) (hg : IsProper g) (F : X.Modules) (hF : F.IsCoherent) :
    @eulerCharacteristic k _ X f hf F hF = @eulerCharacteristic k _ X g hg F hF := by
  subst hfg
  rfl

/-- Projective space over a field is locally Noetherian. -/
private theorem isLocallyNoetherian_projectiveSpaceOverRing (k : Type u) [Field k] (n : ℕ) :
    IsLocallyNoetherian (projectiveSpaceOverRing n (CommRingCat.of k)) :=
  projectiveSpaceOver_isLocallyNoetherian n (Spec (CommRingCat.of k))

/-- **The hyperplane difference formula over an infinite field**, the hypothesis `hstep` of
`AlgebraicGeometry.isNumericalPolynomial_hilbertPolynomial`: for a coherent sheaf `𝒢` on
`ℙ^{m+1}_k` there is a coherent sheaf `ℋ` on `ℙᵐ_k` whose Hilbert polynomial is the first
difference of that of `𝒢`.

This is the displayed equation of the proof of [Stacks, Tag 08AC], read through the identification
of the hyperplane with `ℙᵐ_k`. The sequence is
`AlgebraicGeometry.exists_restrictionSequences`; additivity of the Euler characteristic along it
is [Stacks, Tag 08AA] with [Stacks, Tag 02O6] discharged, and the passage from `ℙ^{m+1}_k` down to
`ℙᵐ_k` is [Stacks, Tag 089W] along the affine morphism `j`, which lies over `Spec k`. -/
public theorem exists_coherent_hilbertPolynomial_sub_eq (k : Type u) [Field k] [Infinite k] :
    ∀ (m : ℕ) (G : (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)).Modules)
      (_ : G.IsCoherent), ∃ (H : (projectiveSpaceOverRing m (CommRingCat.of k)).Modules)
        (hH : H.IsCoherent), ∀ d : ℤ,
          hilbertPolynomial k (m + 1) G d - hilbertPolynomial k (m + 1) G (d - 1) =
            @hilbertPolynomial k _ m H hH d := by
  intro m G hG
  have := hG
  have := isLocallyNoetherian_projectiveSpaceOverRing k (m + 1)
  obtain ⟨H, hH, j, hjaff, hjover, -, -, -, hseq⟩ := exists_restrictionSequences k m G hG
  have := hH
  have := hjaff
  have hcomp : IsProper (j ≫ (projectiveSpaceOverRing (m + 1) (CommRingCat.of k) ↘
      Spec (CommRingCat.of k))) := by
    rw [hjover]
    infer_instance
  have : IsProper j :=
    IsProper.of_comp j (projectiveSpaceOverRing (m + 1) (CommRingCat.of k) ↘
      Spec (CommRingCat.of k))
  have hpm : IsProper (projectiveSpaceOverRing m (CommRingCat.of k) ↘
    Spec (CommRingCat.of k)) := inferInstance
  refine ⟨H, hH, fun d => ?_⟩
  obtain ⟨a, b, w, hS⟩ := hseq d
  have h3 : (projectiveTwist m H d).IsCoherent := isCoherent_projectiveTwist m H d
  have : (projectiveTwist m H d).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have h4 : ((Scheme.Modules.pushforward j).obj (projectiveTwist m H d)).IsCoherent :=
    ProperCoherenceWitness.isCoherent_pushforward j (projectiveTwist m H d)
  have := h4
  have hdiff := hilbertPolynomial_sub_eq_eulerCharacteristic_of_shortExact' k (m + 1)
    G d hS (Iso.refl _) (Iso.refl _)
  have heq : eulerCharacteristic k (projectiveSpaceOverRing (m + 1) (CommRingCat.of k) ↘
        Spec (CommRingCat.of k)) ((Scheme.Modules.pushforward j).obj (projectiveTwist m H d))
      = @hilbertPolynomial k _ m H hH d := by
    rw [eulerCharacteristic_pushforward_of_isAffineHom k j
      (projectiveSpaceOverRing (m + 1) (CommRingCat.of k) ↘ Spec (CommRingCat.of k))
      (projectiveTwist m H d) h3 h4]
    exact eulerCharacteristic_congr_structureMorphism k hjover hcomp hpm
      (projectiveTwist m H d) h3
  exact hdiff.trans heq

/-- **[Stacks, Tag 08AC] over an infinite field.** For an infinite field `k`, an integer `n ≥ 0`
and a coherent sheaf `ℱ` on `ℙⁿ_k`, the function `d ↦ χ(ℙⁿ_k, ℱ(d))` is a numerical polynomial.

The source's induction on `n` is
`AlgebraicGeometry.isNumericalPolynomial_hilbertPolynomial`; its hypothesis is discharged by
`AlgebraicGeometry.exists_coherent_hilbertPolynomial_sub_eq`. -/
public theorem isNumericalPolynomial_hilbertPolynomial_of_infinite (k : Type u) [Field k]
    [Infinite k] (n : ℕ) (F : (projectiveSpaceOverRing n (CommRingCat.of k)).Modules)
    [F.IsCoherent] : IsNumericalPolynomial (hilbertPolynomial k n F) :=
  isNumericalPolynomial_hilbertPolynomial k n (exists_coherent_hilbertPolynomial_sub_eq k) F

/-- **The Hilbert polynomial is unchanged by extension of the ground field.** For a field
extension `K/k` and a coherent sheaf `ℱ` on `ℙⁿ_k`, the Hilbert polynomial of the pullback of `ℱ`
to `ℙⁿ_K` agrees with that of `ℱ` in every twist degree.

`ℙⁿ_K` is the base change of `ℙⁿ_k` along `Spec K ⟶ Spec k`, the twist of the pullback is the
pullback of the twist, and the Euler characteristic of a coherent sheaf on a scheme proper over a
field does not change under extension of that field, which is [Stacks, Tag 08AB]. -/
@[ega "III 7.9.12" "7.9.12.3", ega "III 7.9.7" "special case"]
public theorem hilbertPolynomial_pullback_fieldExtension (k K : Type u) [Field k] [Field K]
    [Algebra k K] (n : ℕ) (F : (projectiveSpaceOverRing n (CommRingCat.of k)).Modules)
    [F.IsCoherent]
    (hFK : ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj F).IsCoherent)
    (d : ℤ) :
    @hilbertPolynomial K _ n ((Scheme.Modules.pullback
          (projectiveSpaceFieldExtensionMap k K n)).obj F) hFK d =
      hilbertPolynomial k n F d := by
  have := isLocallyNoetherian_projectiveSpaceOverRing K n
  have := hFK
  have : ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj
      (projectiveTwist n F d)).IsCoherent :=
    isCoherent_pullback (projectiveSpaceFieldExtensionMap k K n) (projectiveTwist n F d)
  have etw : (Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj
        (projectiveTwist n F d)
      ≅ projectiveTwist n ((Scheme.Modules.pullback
        (projectiveSpaceFieldExtensionMap k K n)).obj F) d :=
    (projectiveTwistPullbackIso (CommRingCat.ofHom (algebraMap k K)) n d F).symm
  have hbc := eulerCharacteristic_baseChange_field k K
    (projectiveSpaceFieldExtensionMap k K n)
    (projectiveSpaceOverRing n (CommRingCat.of K) ↘ Spec (CommRingCat.of K))
    (projectiveSpaceOverRing n (CommRingCat.of k) ↘ Spec (CommRingCat.of k))
    (isPullback_projectiveSpaceFieldExtensionMap k K n) (projectiveTwist n F d)
  have hiso := eulerCharacteristic_eq_of_iso K
    (projectiveSpaceOverRing n (CommRingCat.of K) ↘ Spec (CommRingCat.of K)) etw
  exact hiso.symm.trans hbc.symm

/-- **[Stacks, Tag 08AC] in its eventual reading.** For a field `k`, an integer `n ≥ 0` and a
coherent sheaf `ℱ` on `ℙⁿ_k`, the function `d ↦ χ(ℙⁿ_k, ℱ(d))` is a numerical polynomial.
**No hypothesis.**

The source reduces to an infinite base field by [Stacks, Tag 08AB], and so does this proof: the
extension is `RatFunc k`, the Hilbert polynomial is unchanged by it
(`AlgebraicGeometry.hilbertPolynomial_pullback_fieldExtension`), and over an infinite field the
statement is `AlgebraicGeometry.isNumericalPolynomial_hilbertPolynomial_of_infinite`.

`IsNumericalPolynomial` is [Stacks, Tag 00JX]'s notion, which constrains the function only for
`d ≫ 0`. The tag as stated — a polynomial identity at every `d ∈ ℤ` — is
`AlgebraicGeometry.exists_polynomial_eval_eq_hilbertPolynomial`. -/
@[stacks 08AC "the conclusion in the eventual reading of Tag 00JX: the Hilbert polynomial agrees \
with a sum of binomial coefficients for d >> 0; the tag's own every-integer reading is \
AlgebraicGeometry.exists_polynomial_eval_eq_hilbertPolynomial"]
public theorem isNumericalPolynomial_hilbertPolynomial' (k : Type u) [Field k] (n : ℕ)
    (F : (projectiveSpaceOverRing n (CommRingCat.of k)).Modules) [F.IsCoherent] :
    IsNumericalPolynomial (hilbertPolynomial k n F) := by
  have : Infinite (RatFunc k) := infinite_ratFunc k
  have := isLocallyNoetherian_projectiveSpaceOverRing (RatFunc k) n
  have hFK : ((Scheme.Modules.pullback
      (projectiveSpaceFieldExtensionMap k (RatFunc k) n)).obj F).IsCoherent :=
    isCoherent_pullback (projectiveSpaceFieldExtensionMap k (RatFunc k) n) F
  have := hFK
  exact (isNumericalPolynomial_hilbertPolynomial_of_infinite (RatFunc k) n
    ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k (RatFunc k) n)).obj F)).congr
    (Filter.Eventually.of_forall
      (hilbertPolynomial_pullback_fieldExtension k (RatFunc k) n F hFK))

end AlgebraicGeometry

end
