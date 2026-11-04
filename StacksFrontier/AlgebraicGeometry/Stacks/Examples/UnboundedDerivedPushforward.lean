module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.ZMod.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.ProductOfStructureSheavesNotQuasiCoherent

/-!
# Unbounded derived pushforward need not preserve quasi-coherent cohomology

**Stacks 07DD** asserts that a quasi-compact, quasi-separated morphism `f : 𝒳 ⟶ 𝒴` of algebraic
stacks need *not* induce a functor `Rf_* : D_QCoh(𝒪_𝒳) ⟶ D_QCoh(𝒪_𝒴)`.  Its proof is the one
line "see discussion above", and the mathematics lives in the discussion of **Stacks 07DC**:
take `k` of characteristic `p > 0`, `S = Spec k[x]`, `G = ℤ/pℤ` acting trivially,
`𝒳 = [S/G]` and `f : 𝒳 ⟶ S`.  The covering `S ⟶ 𝒳` has affine fibre products `S × G^n`, so
`Rf_*𝒪_𝒳` is computed by the group-cohomology complex of `G` with coefficients `k[x]`, giving
`Rf_*𝒪_𝒳 = ⊕_{n ≥ 0} 𝒪_S[-n]`.  For `E = ⊕_{m ≥ 0} 𝒪_𝒳[m]`, which equals `∏_{m ≥ 0} 𝒪_𝒳[m]`
by **Stacks 08IY** and **Stacks 08IZ**, one gets `Rf_*E = ∏_{m ≥ 0} ⊕_{n ≥ 0} 𝒪_S[m - n]`, whose
degree-zero cohomology sheaf is a countable product of copies of `𝒪_S` — and *that* sheaf is not
quasi-coherent, so `Rf_*E` does not lie in `D_QCoh(𝒪_S)`.

What this file proves is the last step, over the source's own base `S = Spec k[x]`, together
with the obstruction it rests on.

## Main results

* `Stacks.Examples.UnboundedDerivedPushforward.not_isQuasicoherent_piStructureSheaf_polynomial`:
  the countable product `∏_{m ≥ 0} 𝒪_{Spec k[x]}`, taken in the modules over the structure
  sheaf, is not quasi-coherent as soon as `k` is nontrivial.
* `Stacks.Examples.UnboundedDerivedPushforward.not_forall_isQuasicoherent_pi`: hence the
  quasi-coherent modules on `Spec k[x]` are *not* closed under countable products, witnessed by
  the constant family `𝒪_{Spec k[x]}`, each member of which is quasi-coherent.  This is the
  obstruction the source's discussion turns on: the derived pushforward commutes with products,
  while `D_QCoh` does not contain the products of its own objects formed in `D(𝒪_S)`.
* `Stacks.Examples.UnboundedDerivedPushforward.not_isQuasicoherent_of_iso_piStructureSheaf`:
  **Stacks 07DD** in the form reached here.  A module on `Spec k[x]` identified with that
  countable product — which is what the source's computation produces as the degree-zero
  cohomology sheaf of `Rf_*E` — is not quasi-coherent, so `Rf_*E` is not an object of
  `D_QCoh(𝒪_S)`.
* `Stacks.Examples.UnboundedDerivedPushforward.not_isQuasicoherent_piStructureSheaf_zmod`: the
  source's literal base ring, `k = ℤ/pℤ` for `p` prime, for which the characteristic hypothesis
  of the discussion holds on the nose.

## What is carried, and why it is satisfiable

`not_isQuasicoherent_of_iso_piStructureSheaf` carries one hypothesis, `hH`: an isomorphism of
the module under consideration with `∏_{m : ℕ} 𝒪_{Spec k[x]}`.  It is used, and only used, to
transport non-quasi-coherence along `ObjectProperty.prop_of_iso`.  It is satisfiable on the
nose — the product exists in the modules over the structure sheaf, and `H` may be taken to be
it — so the statement is not vacuous.  Its mathematical content is the source's identification
of the degree-zero cohomology sheaf of `Rf_*E`.

The base-ring hypotheses are satisfiable at the source's own inputs: `k = ℤ/pℤ` for `p` prime
is nontrivial and of characteristic `p`, which is
`not_isQuasicoherent_piStructureSheaf_zmod`.  Nontriviality is what the obstruction needs, and
it cannot be dropped: over a field the base would still be a line, but over the *zero* ring
`Spec k[x]` is empty and every module on it is quasi-coherent.

## The source's steps against what this repository has

* `[S/G]` as an algebraic stack, and `f : [S/G] ⟶ S` quasi-compact and quasi-separated.  **Not
  available.**  `AlgebraicGeometry.AbstractGroupQuotientStack` is a category over the big fppf
  site with no theorem placing it in `AlgebraicGeometry.Stack.AlgebraicStacks`, and there is no
  quasi-compactness or quasi-separatedness result for any quotient stack.
* `Rf_*` on `D⁺_QCoh`, the positive result **Stacks 07BC** that 07DD contrasts with.
  *Available*, as `AlgebraicGeometry.Stack.derivedPushforwardPlusLocallyQuasicoherentFlatBaseChange`
  in
  `StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/DerivedPushforwardQuasicoherent.lean`.
  The statements below are about an unbounded object, so they do not touch it.
* `H^n(ℤ/pℤ, k[x]) ≅ k[x]` in every degree `n ≥ 0` for the trivial action in characteristic
  `p`, the computation behind `Rf_*𝒪_𝒳 = ⊕_{n ≥ 0} 𝒪_S[-n]`.  *Available*, as
  `Stacks.GroupCohomology.TrivialCyclic.polynomialCohomologyIso` in
  `StacksFrontier/RingTheory/GroupCohomology/CyclicTrivialModule.lean`.
* The descent spectral sequence reducing `RΓ(𝒳, 𝒪_𝒳)` to that complex.  Available only in the
  restricted forms of **Stacks 072G** and **Stacks 076Z**, which carry their own hypotheses.
* `⊕_{m ≥ 0} 𝒪_𝒳[m] = ∏_{m ≥ 0} 𝒪_𝒳[m]`, **Stacks 08IZ**.  *Available*, as
  `AlgebraicGeometry.Stack.isIso_coproductToProduct_shiftedLqcFbc`, over the carried predicate
  `AlgebraicGeometry.Stack.HasAffineAcyclicLqcFbcModules`.
* `Rf_*E = ∏_m ⊕_n 𝒪_S[m - n]` and the passage to its degree-zero cohomology sheaf.  **Not
  available**: this is the hypothesis `hH` below.
* A countable product of copies of `𝒪_S` is not quasi-coherent.  *This file*, from
  `Stacks.Duality.not_isQuasicoherent_piStructureSheaf`.
* The bridge from quasi-coherence on `Spec k[x]` to
  `AlgebraicGeometry.Stack.IsLocallyQuasicoherent` on the big fppf site, which is the predicate
  cutting out `D_QCoh` in **Stacks 07B6**.  **Not available**: no result relates local
  quasi-coherence to quasi-coherence of a module over a ring.  The statements below are
  therefore about quasi-coherence of a module on the scheme `S`, which is the form the source's
  phrase "not even locally quasi-coherent" refers to.

## References

* [Stacks Project, Tag 07DD](https://stacks.math.columbia.edu/tag/07DD)
* [Stacks Project, Tag 07DC](https://stacks.math.columbia.edu/tag/07DC)
* [Stacks Project, Tag 07BC](https://stacks.math.columbia.edu/tag/07BC)
* [Stacks Project, Tag 08IZ](https://stacks.math.columbia.edu/tag/08IZ)
* [Stacks Project, Tag 0GEU](https://stacks.math.columbia.edu/tag/0GEU)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.Examples.UnboundedDerivedPushforward

universe u

/-! ### The base of the counterexample -/

/-- In `k[x]` over a nontrivial ring no equation `x^j = x^{j+1} b` holds: the coefficient of
`x^j` in `x^j (1 - x b)` is `1`. -/
private theorem pow_X_mul_one_sub_mul_ne_zero {k : Type u} [CommRing k] [Nontrivial k] (j : ℕ)
    (b : Polynomial k) :
    (Polynomial.X : Polynomial k) ^ j * (1 - Polynomial.X * b) ≠ 0 := by
  intro hzero
  have hcomm : (1 - Polynomial.X * b) * (Polynomial.X : Polynomial k) ^ j = 0 := by
    rw [mul_comm]; exact hzero
  have hcoeff : ((1 - Polynomial.X * b) * (Polynomial.X : Polynomial k) ^ j).coeff (0 + j) =
      (1 - Polynomial.X * b).coeff 0 :=
    Polynomial.coeff_mul_X_pow _ _ _
  have hone : (1 - Polynomial.X * b).coeff 0 = (1 : k) := by
    simp [Polynomial.coeff_sub, Polynomial.mul_coeff_zero]
  rw [hcomm, Polynomial.coeff_zero, hone] at hcoeff
  exact zero_ne_one hcoeff

/-- **A countable product of copies of the structure sheaf of `Spec k[x]` is not
quasi-coherent.**  This is the sheaf the discussion of **Stacks 07DC** produces as the
degree-zero cohomology sheaf of `Rf_*E`, over the base `S = Spec k[x]` of its own
counterexample, and its failure to be quasi-coherent is the whole point of the example.

The argument is `Stacks.Duality.not_isQuasicoherent_piStructureSheaf`: a quasi-coherent module
on an affine has localizing sections, so a section over `D(x)` is a global section divided by a
*single* power of `x`, while the product has a section over `D(x)` whose `n`-th coordinate is
`1/x^n`.  The hypothesis that ring element admits no equation `t^j = t^{j+1} b` holds for
`t = x` in `k[x]` as soon as `k` is nontrivial. -/
public theorem not_isQuasicoherent_piStructureSheaf_polynomial (k : Type u) [CommRing k]
    [Nontrivial k] :
    ¬ (∏ᶜ (fun _ : ℕ => SheafOfModules.unit
      (Spec (CommRingCat.of (Polynomial k))).ringCatSheaf)).IsQuasicoherent :=
  Stacks.Duality.not_isQuasicoherent_piStructureSheaf (CommRingCat.of (Polynomial k))
    Polynomial.X fun j b => pow_X_mul_one_sub_mul_ne_zero j b

/-- The source's literal base ring: for `p` prime, `k = ℤ/pℤ` has characteristic `p`, so the
whole discussion of **Stacks 07DC** applies to it, and the countable product
`∏_{m ≥ 0} 𝒪_{Spec 𝔽_p[x]}` is not quasi-coherent. -/
public theorem not_isQuasicoherent_piStructureSheaf_zmod (p : ℕ) [Fact p.Prime] :
    ¬ (∏ᶜ (fun _ : ℕ => SheafOfModules.unit
      (Spec (CommRingCat.of (Polynomial (ZMod p)))).ringCatSheaf)).IsQuasicoherent :=
  have : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  not_isQuasicoherent_piStructureSheaf_polynomial (ZMod p)

/-! ### The obstruction: `D_QCoh` misses the products of its own objects -/

/-- **The quasi-coherent modules on `Spec k[x]` are not closed under countable products.**  The
witness is the constant family `𝒪_{Spec k[x]}`, every member of which is quasi-coherent, while
its product is not.

This is the obstruction the discussion of **Stacks 07DC** exploits.  The derived pushforward,
being a right derived functor, commutes with products, and the counterexample's `E` is a
countable product in `D_QCoh(𝒪_𝒳)` by **Stacks 08IZ**; the product of the resulting family
formed in `D(𝒪_S)` then leaves `D_QCoh(𝒪_S)`, already in degree zero.  Boundedness is what
rules this out in **Stacks 07BC**: a product of a family bounded below *uniformly* is again
bounded below, and the counterexample's family is not. -/
public theorem not_forall_isQuasicoherent_pi (k : Type u) [CommRing k] [Nontrivial k] :
    ¬ ∀ M : ℕ → (Spec (CommRingCat.of (Polynomial k))).Modules,
      (∀ n, (M n).IsQuasicoherent) → (∏ᶜ M).IsQuasicoherent := by
  intro hclosed
  refine not_isQuasicoherent_piStructureSheaf_polynomial k (hclosed _ fun _ => ?_)
  exact (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr inferInstance

/-! ### Stacks 07DD -/

/-- **Stacks 07DD**, in the form this development reaches.  The discussion of **Stacks 07DC**
exhibits a quasi-compact and quasi-separated `f : 𝒳 = [Spec k[x] / (ℤ/pℤ)] ⟶ S = Spec k[x]` and
an object `E = ⊕_{m ≥ 0} 𝒪_𝒳[m]` of `D_QCoh(𝒪_𝒳)` whose derived pushforward
`Rf_*E = ∏_{m ≥ 0} ⊕_{n ≥ 0} 𝒪_S[m - n]` has, in degree zero, a countable product of copies of
`𝒪_S`.  Here that identification is the hypothesis `hH`, and the conclusion is the source's:
the sheaf so obtained is not quasi-coherent, hence `Rf_*E` is not an object of `D_QCoh(𝒪_S)` and
`Rf_*` does not restrict to a functor `D_QCoh(𝒪_𝒳) ⟶ D_QCoh(𝒪_S)`.

The hypothesis is satisfiable: the product exists, so `H` may be taken to be it with `hH` the
identity.  Its content — the quotient stack, the morphism, and the computation of the
pushforward — is what this repository does not have; see this file's module documentation for
the step-by-step comparison. -/
@[stacks 07DD "the last step of the discussion of Tag 07DC, over its own base S = Spec k[x]: a \
module identified with the countable product of copies of O_S, which is what that discussion \
produces as the degree-zero cohomology sheaf of Rf_*E, is not quasi-coherent, so Rf_*E does \
not lie in D_QCoh(O_S). Carried as the hypothesis hH is exactly that identification, and with \
it the quotient stack [Spec k[x]/(Z/pZ)], the quasi-compactness and quasi-separatedness of its \
structure morphism, the computation Rf_*O_X = sum of O_S[-n] and the identification of E with \
a product; none of those is established here. Quasi-coherence is that of a module on the \
scheme S, the sense of the source's `not even locally quasi-coherent`, and not the local \
quasi-coherence of Tag 06WJ on the big fppf site"]
public theorem not_isQuasicoherent_of_iso_piStructureSheaf {k : Type u} [CommRing k]
    [Nontrivial k] (H : (Spec (CommRingCat.of (Polynomial k))).Modules)
    (hH : H ≅ ∏ᶜ (fun _ : ℕ => SheafOfModules.unit
      (Spec (CommRingCat.of (Polynomial k))).ringCatSheaf)) :
    ¬ H.IsQuasicoherent := by
  intro hqc
  have hpi : (∏ᶜ (fun _ : ℕ => SheafOfModules.unit
      (Spec (CommRingCat.of (Polynomial k))).ringCatSheaf)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent
      (Spec (CommRingCat.of (Polynomial k))).ringCatSheaf).prop_of_iso hH hqc
  exact not_isQuasicoherent_piStructureSheaf_polynomial k hpi

end Stacks.Examples.UnboundedDerivedPushforward

end
