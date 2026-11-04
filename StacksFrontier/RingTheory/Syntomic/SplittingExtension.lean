module

public import StacksFrontier.RingTheory.Syntomic.RelativeGlobalCompleteIntersection

@[expose] public section

universe u

/-!
# Splitting a monic polynomial in a finite free faithfully flat extension

Let `A` be a ring and let `P = x^n + b_1x^{n-1} + … + b_n ∈ A[x]` be monic. This file proves
Stacks 03HS: there is an `A`-algebra `A'` which is finite and free as an `A`-module, faithfully
flat and syntomic (Definition 00SL), together with `β_1, …, β_n ∈ A'` such that
`P = ∏_{i = 1}^{n} (x - β_i)` in `A'[x]`.

The extension is built one root at a time: `A ⊂ A[x]/(P) ⊂ …`, splitting off the factor
`x - β_1` and recursing on the complementary factor, which is monic of degree `n - 1`. A single
step `B = A[x]/(P)` is free over `A` on `1, x, …, x^{n-1}`, hence — for `n ≥ 1`, that is unless `P`
is a unit — nontrivial and free and therefore faithfully flat; finiteness, freeness and faithful
flatness of the whole tower are the transitivity of those three properties.

Syntomicity is not obtained by composing syntomic maps. Instead the tower is presented in one
piece: a single step is presented by one variable and one relation, `B = A[x_1]/(P(x_1))`, and
composing `n` such presentations (`Algebra.Presentation.comp`) presents `A'` over `A` by `n`
variables and `n` relations. Since `A'` is finite as an `A`-module, every nonempty fibre
`κ(p) ⊗_A A'` is a finite-dimensional algebra over the field `κ(p)`, hence artinian, hence of
Krull dimension `0 = n - n`. So `A → A'` is a relative global complete intersection (Definition
00SP) and therefore syntomic by Lemma 00SW.

## Main results

* `Stacks.Syntomic.SplittingAlgebra.solution`: the statement of Stacks 03HS.

## Implementation notes

*The route is the iterated `AdjoinRoot`, not the base change of the universal example.* The source
takes `A' = A ⊗_R S` for `R = ℤ[a_1, …, a_n] → S = ℤ[α_1, …, α_n]` the universal splitting algebra
of Example 00SR, whose four properties it obtains from Lemma 00SW and then inherits by base
change. The two ingredients that route needs — that `R → S` is a relative global complete
intersection, which is the theory of symmetric functions, and that each of the four properties
descends along a base change, of which only the first is Lemma 00SS (1) — are both absent from
Mathlib, whereas `A[x]/(P)` for monic `P` comes with `Polynomial.Monic.free_adjoinRoot` and
`Polynomial.Monic.finite_adjoinRoot` and the induction is Mathlib's own
`Polynomial.Monic.exists_splits_map`. The mathematics is the same: the universal example is
exactly this tower for the free monic polynomial, and both proofs rest on Lemma 00SW for
syntomicity.

*A tower of presentations, rather than a composition law for syntomic maps.* Syntomicity is not
visibly stable under composition in Mathlib (the fibrewise local complete intersection condition
is the obstruction), and the source does not need it either. Carrying the presentation with as
many relations as variables through the induction, and reading off `dim = 0` from
module-finiteness at the end, replaces such a composition law by
`Algebra.Presentation.comp` and one appeal to Lemma 00SW.

## References

* [StacksProject 03HS](https://stacks.math.columbia.edu/tag/03HS), Lemma 10.136.16
* [StacksProject 00SW](https://stacks.math.columbia.edu/tag/00SW), Lemma 10.136.13, that a
  relative global complete intersection is syntomic
* [StacksProject 00SP](https://stacks.math.columbia.edu/tag/00SP), Definition 10.136.5, the
  relative global complete intersections
-/

namespace Stacks.Syntomic.SplittingAlgebra

open Polynomial



/-- `n = m + 1` monic linear factors indexed by `Fin.cons a v` are the factor `x - a` times the
`m` factors indexed by `v`; this is `Fin.prod_univ_succ` transported along `n = m + 1`. -/
private lemma prod_X_sub_C_cons {R : Type*} [CommRing R] {n m : ℕ} (hn : n = m + 1) (a : R)
    (v : Fin m → R) :
    ∏ i : Fin n, (X - C (Fin.cons (α := fun _ => R) a v (finCongr hn i))) =
      (X - C a) * ∏ i, (X - C (v i)) := by
  subst hn; simp [Fin.prod_univ_succ]

/-- A monic polynomial with a root `b` in a nontrivial ring splits off the factor `x - b`: it is
`(x - b) q` with `q` monic of degree one less. -/
private lemma exists_monic_eq_X_sub_C_mul_of_isRoot {B : Type*} [CommRing B] [Nontrivial B]
    {P : B[X]} (hP : P.Monic) {b : B} (hb : P.IsRoot b) :
    ∃ q : B[X], q.Monic ∧ P.natDegree = q.natDegree + 1 ∧ P = (X - C b) * q := by
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hb
  have hqm : q.Monic := .of_mul_monic_left (monic_X_sub_C b) (hq ▸ hP)
  refine ⟨q, hqm, ?_, hq⟩
  rw [hq, (monic_X_sub_C b).natDegree_mul hqm, natDegree_X_sub_C, Nat.add_comm]

/-- A presentation `A' = A[x_i, i ∈ ι]/(f_j, j ∈ σ)` of a module-finite algebra with as many
relations as variables is a relative global complete intersection (Definition 00SP): a nonempty
fibre `κ(p) ⊗_A A'` is a finite-dimensional algebra over the field `κ(p)`, hence artinian, hence
of Krull dimension `0 = #ι - #σ`. -/
private lemma isRelativeGlobalCompleteIntersection_of_card_eq {A A' : Type*} [CommRing A]
    [CommRing A'] [Algebra A A'] [Module.Finite A A'] {ι σ : Type*} [Finite ι] [Finite σ]
    (P : Algebra.Presentation A A' ι σ) (h : Nat.card σ = Nat.card ι) :
    P.IsRelativeGlobalCompleteIntersection :=
  ⟨fun p _ _ => by
    have : IsArtinianRing (p.Fiber A') := IsArtinianRing.of_finite p.ResidueField _
    rw [ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance]
    simp [h]⟩

/-- `A'` **has a square presentation** over `A` if it can be written as
`A[x_1, …, x_m]/(f_1, …, f_m)` with as many relations as variables. Together with
`Module.Finite A A'` this is what makes `A → A'` a relative global complete intersection
(Definition 00SP), the fibre dimension being `0 = m - m`. -/
private def HasSquarePresentation (A A' : Type*) [CommRing A] [CommRing A'] [Algebra A A'] :
    Prop :=
  ∃ m : ℕ, Nonempty (Algebra.Presentation A A' (Fin m) (Fin m))

/-- A ring has a square presentation over itself: no variables and no relations. -/
private lemma HasSquarePresentation.refl (A : Type*) [CommRing A] : HasSquarePresentation A A :=
  ⟨0, ⟨(Algebra.Presentation.id A : Algebra.Presentation A A PEmpty.{1} PEmpty.{1}).reindex
    (Equiv.equivPEmpty _) (Equiv.equivPEmpty _)⟩⟩

/-- A tower of two square presentations is a square presentation: variables and relations are
each added by `Algebra.Presentation.comp`. -/
private lemma HasSquarePresentation.trans {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (h₁ : HasSquarePresentation A B) (h₂ : HasSquarePresentation B C) :
    HasSquarePresentation A C := by
  obtain ⟨m, ⟨P⟩⟩ := h₁
  obtain ⟨m', ⟨Q⟩⟩ := h₂
  exact ⟨m' + m, ⟨(Q.comp P).reindex finSumFinEquiv.symm finSumFinEquiv.symm⟩⟩

/-- Adjoining a root of a polynomial is a square presentation: `A[x]/(P)` is presented by the one
variable `x_1` and the one relation `P(x_1)`. -/
private lemma HasSquarePresentation.adjoinRoot {A : Type*} [CommRing A] (P : A[X]) :
    HasSquarePresentation A (AdjoinRoot P) := by
  have e : MvPolynomial (Fin 1) A ≃ₐ[A] A[X] := MvPolynomial.uniqueAlgEquiv A (Fin 1)
  refine ⟨1, ⟨(Algebra.Presentation.naive (v := fun _ : Fin 1 => e.symm P)).ofAlgEquiv
    (Ideal.quotientEquivAlg _ (Ideal.span {P}) e ?_)⟩⟩
  rw [Ideal.map_span]
  simp

/-- An algebra that is finite as a module and has a square presentation is a relative global
complete intersection (Definition 00SP). -/
private lemma HasSquarePresentation.isRelativeGlobalCompleteIntersection {A A' : Type*}
    [CommRing A] [CommRing A'] [Algebra A A'] [Module.Finite A A']
    (h : HasSquarePresentation A A') : Algebra.IsRelativeGlobalCompleteIntersection A A' :=
  have ⟨m, ⟨P⟩⟩ := h
  ⟨m, m, P, isRelativeGlobalCompleteIntersection_of_card_eq P rfl⟩

/-- The extension of 03HS, with syntomicity replaced by the square presentation from which, given
finiteness, it follows. This is the induction: `A' = A` when `P` is a unit, and otherwise
`A ⊂ A[x]/(P) ⊂ A'` with `A'` splitting the complementary factor of `x - β_1`. -/
private lemma exists_aux {A : Type u} [CommRing A] {P : A[X]} (hP : P.Monic) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Module.Finite A A')
      (_ : Module.Free A A') (_ : Module.FaithfullyFlat A A') (β : Fin P.natDegree → A'),
      HasSquarePresentation A A' ∧ P.map (algebraMap A A') = ∏ i, (X - C (β i)) := by
  induction hn : P.natDegree using Nat.strong_induction_on generalizing A with | h n IH =>
  by_cases hpu : IsUnit P
  · obtain rfl := hP.eq_one_of_isUnit hpu
    obtain rfl : n = 0 := by simpa using hn.symm
    exact ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      fun _ => 0, .refl A, by simp⟩
  · have : Nontrivial (AdjoinRoot P) := Ideal.Quotient.nontrivial_iff.mpr (by simpa)
    have := hP.free_adjoinRoot
    have := hP.finite_adjoinRoot
    obtain ⟨q, hqm, hdq, hq⟩ := exists_monic_eq_X_sub_C_mul_of_isRoot
      (hP.map (algebraMap A (AdjoinRoot P))) (b := AdjoinRoot.root P)
      (by rw [AdjoinRoot.algebraMap_eq]; exact AdjoinRoot.isRoot_root P)
    have hdd : n = q.natDegree + 1 := by
      rw [← hn, ← hP.natDegree_map (algebraMap A (AdjoinRoot P)), hdq]
    obtain ⟨A', _, _, _, _, _, β', hpres, hβ'⟩ := IH q.natDegree (by omega) hqm rfl
    algebraize [(algebraMap (AdjoinRoot P) A').comp (algebraMap A (AdjoinRoot P))]
    have : Module.FaithfullyFlat A A' := Module.FaithfullyFlat.trans A (AdjoinRoot P) A'
    refine ⟨A', ‹_›, ‹_›, .trans (AdjoinRoot P) _, .trans (S := AdjoinRoot P) .., ‹_›,
      fun i => Fin.cons (α := fun _ => A')
        (algebraMap (AdjoinRoot P) A' (AdjoinRoot.root P)) β' (finCongr hdd i),
      (HasSquarePresentation.adjoinRoot P).trans hpres, ?_⟩
    rw [prod_X_sub_C_cons hdd, ← hβ', IsScalarTower.algebraMap_eq A (AdjoinRoot P) A',
      ← Polynomial.map_map, hq, Polynomial.map_mul]
    simp

/-- **A monic polynomial splits in a finite free faithfully flat syntomic extension**
(Stacks 03HS). For a monic `P ∈ A[x]` there is an `A`-algebra `A'`, finite and free as an
`A`-module, faithfully flat and syntomic, with `β_1, …, β_n ∈ A'` such that
`P = ∏ (x - β_i)` in `A'[x]`, where `n` is the degree of `P`. -/
public theorem solution {A : Type u} [CommRing A] {P : A[X]} (hP : P.Monic) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Module.Finite A A')
      (_ : Module.Free A A') (_ : Module.FaithfullyFlat A A') (_ : Algebra.Syntomic A A')
      (β : Fin P.natDegree → A'), P.map (algebraMap A A') = ∏ i, (X - C (β i)) := by
  obtain ⟨A', hring, halg, hfin, hfree, hflat, β, hpres, hβ⟩ := exists_aux hP
  have := hpres.isRelativeGlobalCompleteIntersection
  exact ⟨A', hring, halg, hfin, hfree, hflat,
    Algebra.Syntomic.of_isRelativeGlobalCompleteIntersection A A', β, hβ⟩

end Stacks.Syntomic.SplittingAlgebra

/-!
# Splitting a monic polynomial in a finite free faithfully flat extension

Let `A` be a ring and let `P = x^n + b_1 x^{n-1} + … + b_n ∈ A[x]` be a monic polynomial. Then
`P` splits into linear factors after a single faithfully flat base change which is as good as one
could ask for: there is an extension `A ⊂ A'` which is finite and free as an `A`-module,
faithfully flat, and syntomic (Definition 00SL), together with `β_1, …, β_n ∈ A'` such that
`P = ∏_{i = 1}^{n} (x - β_i)` in `A'[x]`.

The source's proof is one base change of a single universal example. Let
`R = ℤ[a_1, …, a_n] → S = ℤ[α_1, …, α_n]` send `a_i` to the `i`-th elementary symmetric function
of the `α_j`, so that `x^n + a_1x^{n-1} + … + a_n = ∏ (x + α_i)` in `S[x]` (Example 00SR). By the
theory of symmetric functions `S` is finite free over `R` on the `n!` monomials
`α_1^{e_1} ⋯ α_n^{e_n}` with `0 ≤ e_i ≤ n - i`, so its fibres are finite, of dimension `0 = n - n`,
and `S` is a relative global complete intersection over `R` (Definition 00SP), hence syntomic by
Lemma 00SW; the rank being positive, `R → S` is faithfully flat. Now let `R → A` send `a_i` to
`b_i` and put `A' = A ⊗_R S`, `β_i = -1 ⊗ α_i`; each of the four properties is stable under base
change.

Geometrically, `Spec A' → Spec A` is a surjective finite locally free — indeed syntomic — cover of
`Spec A` over which the finite flat `A`-algebra `A[x]/(P)` becomes a union of `n` copies of the
base, and that is how the lemma is used: to trivialize a standard étale algebra `R[x]_g/(f)` after
a finite flat cover (00UF, 053K, and Morphisms 03HW), and to write `f' h` in `B[x]/(f)` in terms
of the roots of `f` (03GD).

## Main results

* `Polynomial.Monic.exists_finite_free_faithfullyFlat_syntomic_map_eq_prod_X_sub_C`: a monic
  polynomial becomes a product of monic linear factors over a finite free, faithfully flat,
  syntomic extension of its ring of coefficients, 03HS.

## Implementation notes

*The source's `A ⊂ A'` is not a conjunct.* An `A`-algebra `A'` with `Module.FaithfullyFlat A A'`
has `FaithfulSMul A A'` by `Module.FaithfullyFlat.faithfulSMul`, so `algebraMap A A'` is injective
by `FaithfulSMul.algebraMap_injective`, and `A'` is nontrivial as soon as `A` is. Asserting the
inclusion again would add nothing to the statement, whereas asserting it *instead of* faithful
flatness would lose the surjectivity of `Spec A' → Spec A` that every consumer uses.

*The splitting is the explicit product, not `Polynomial.Splits`.* Mathlib's predicate
`Polynomial.Splits` only says that the polynomial lies in the submonoid generated by the constants
and the monic linear polynomials; the form stated here names the `n` roots and pins their number
to `P.natDegree`, which is what the consumers need (00UF and 03HW form the `n` algebra maps
`A[x]/(P) → A'`, `x ↦ β_i`, and 03GD sums over the roots). It is strictly stronger, and it implies
`(P.map (algebraMap A A')).Splits` at once.

*Degree `n` is `P.natDegree`, and no `Nontrivial A` is assumed.* The source's `P` is monic of
degree `n`; for monic `P` that is `P.natDegree = n`, so writing `Fin P.natDegree` removes a
variable and a hypothesis rather than adding one. The Mathlib sibling
`Polynomial.Monic.exists_splits_map` assumes `Nontrivial A` because it also concludes
`Nontrivial A'`; here the statement is true for the zero ring as well, `A' = A` serving, so the
hypothesis is dropped. `A'` is produced in the same universe as `A`, as in that sibling, and the
properties are carried as instance-existentials in the same style, so that
`obtain ⟨A', _, _, _, _, _, _, β, hβ⟩` puts them all in the context.

Faithfulness. (1) The single hypothesis is used by the conclusion and is not decoration: a product
of `P.natDegree` monic linear polynomials is monic of that degree, and `algebraMap A A'` is
injective, so `P.Monic` is implied by the conclusion — it can be neither dropped nor weakened.
(2) The scalars and the base are the source's: `A'` is an algebra over `A` itself, finiteness,
freeness, faithful flatness and syntomicity are all over `A` and not over a localization of it,
and it is the image `P.map (algebraMap A A')` of the given `P` that factors, not an unrelated lift.
(3) The canonical map is pinned: the extension is `algebraMap A A'`, the factorization is the
equation `P.map (algebraMap A A') = ∏ i, (X - C (β i))` in `A'[X]` rather than the mere existence
of a splitting, and `β` is the tuple of roots that equation determines up to order. (4) The
instantiation is not degenerate: for `A = ℤ` and `P = x^2 + 1` one may take `A' = ℤ[i]`, free of
rank `2`, faithfully flat, syntomic as `ℤ[x]/(x^2+1)` is a relative global complete intersection,
with `β = (i, -i)`; and the conclusion has no trivial witness over a nontrivial `A`, since the zero
algebra is not faithfully flat and `A' = A` fails already for `P = x^2 + 1` over `ℤ`.

## References

* [StacksProject 03HS](https://stacks.math.columbia.edu/tag/03HS), Lemma 10.136.16, in Section
  10.136 "Syntomic morphisms"
* [StacksProject 00SR](https://stacks.math.columbia.edu/tag/00SR), Example 10.136.8, the universal
  splitting algebra `ℤ[a_1, …, a_n] → ℤ[α_1, …, α_n]` the proof base changes
* [StacksProject 00SW](https://stacks.math.columbia.edu/tag/00SW), Lemma 10.136.13, that a
  relative global complete intersection is syntomic,
  `Algebra.Syntomic.of_isRelativeGlobalCompleteIntersection`
* [StacksProject 00SL](https://stacks.math.columbia.edu/tag/00SL), Definition 10.136.1, the
  syntomic ring maps, `Algebra.Syntomic`
-/

@[expose] public section



open Polynomial in
/-- **Stacks 03HS.** Let `A` be a ring and let `P ∈ A[x]` be monic. There is a finite free,
faithfully flat, syntomic extension `A ⊂ A'` and elements `β_1, …, β_n ∈ A'`, `n = deg P`, with
`P = ∏ (x - β_i)` in `A'[x]`. The inclusion `A ⊂ A'` is the faithful flatness: it gives
`FaithfulSMul A A'`, hence `algebraMap A A'` injective. -/
@[stacks 03HS "The source's finite free faithfully flat *extension* `A ⊂ A'`: the injectivity of
`algebraMap A A'` is not a conjunct, being `FaithfulSMul.algebraMap_injective` applied to
`Module.FaithfullyFlat A A'`. The splitting is the explicit product over `Fin P.natDegree`, which
names the roots the consumers use and is stronger than `Polynomial.Splits`. Unlike the Mathlib
sibling `Polynomial.Monic.exists_splits_map`, no `Nontrivial A` is assumed and the extension is
also faithfully flat and syntomic (Definition 00SL). See the module docstring."]
public theorem Polynomial.Monic.exists_finite_free_faithfullyFlat_syntomic_map_eq_prod_X_sub_C
    {A : Type u} [CommRing A] {P : A[X]} (hP : P.Monic) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Module.Finite A A')
      (_ : Module.Free A A') (_ : Module.FaithfullyFlat A A') (_ : Algebra.Syntomic A A')
      (β : Fin P.natDegree → A'), P.map (algebraMap A A') = ∏ i, (X - C (β i)) :=
    by apply Stacks.Syntomic.SplittingAlgebra.solution ; assumption

end
