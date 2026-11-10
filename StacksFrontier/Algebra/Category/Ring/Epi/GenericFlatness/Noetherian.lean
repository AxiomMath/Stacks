module


import StacksCore.Algebra.Module.FinitePresentation
public import StacksFrontier.RingTheory.FinitePresentation.FreeAway
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Data.Finsupp.PWO
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Generic flatness

A finite type algebra over a domain becomes free, and finitely presented, after inverting a single
nonzero element of the domain. This file proves the six lemmas of Stacks section 051Q which make
that precise, in increasing order of strength, together with the two local-global properties of the
locus where it happens.

For a ring map `R → S` and an `S`-module `M`, Equation 051U singles out those `f : R` for which,
after inverting `f`, the algebra `S_f` is of finite presentation over `R_f`, the module `M_f` is of
finite presentation over `S_f`, and both `S_f` and `M_f` are free over `R_f`; that condition is the
predicate `Algebra.IsFinitePresentationFreeAway`. Equation 051V collects the standard opens `D(f)`
of such `f` into the *generic freeness locus*
```
U(R → S, M) = ⋃ {D(f) | Algebra.IsFinitePresentationFreeAway R S M f} ⊆ Spec R.
```

Three lemmas produce elements of that locus, under successively weaker hypotheses on the base: over
a Noetherian domain for a finite module over a finite type algebra (051R), over an arbitrary domain
for a finitely presented module over a finitely presented algebra (051S), and over an arbitrary
domain for a finite module over a finite type algebra, the finite presentation then being part of
the conclusion rather than of the hypotheses (051T). Two more describe the locus itself: it is
stable under extensions of the module (051W), and it is local on the base (051X), whence density of
the locus may be checked on a dense open (051Y).

## Main results

* `Module.exists_ne_zero_free_localizedModule_away`: generic freeness over a Noetherian domain
  (051R).
* `Module.FinitePresentation.exists_ne_zero_free_localizedModule_away`: generic freeness for a
  finitely presented module over a finitely presented algebra over a domain (051S).
* `Algebra.exists_ne_zero_isFinitePresentationFreeAway`: generic freeness together with generic
  finite presentation over a domain, i.e. the locus is nonempty (051T).
* `Algebra.IsFinitePresentationFreeAway.of_dvd`: the condition 051U is inherited by every multiple
  of an element satisfying it, so two good elements can be replaced by the single good element
  `g₁ * g₂`.
* `Algebra.isFinitePresentationFreeAway_of_finitePresentation_of_free`: every element of the base
  satisfies 051U as soon as the algebra and the module are already of finite presentation and free.
* `Algebra.iUnion_basicOpen_isFinitePresentationFreeAway_inter_subset_of_shortExact`: for a short
  exact sequence `0 → M₁ → M₂ → M₃ → 0`, one has
  `U(R → S, M₁) ∩ U(R → S, M₃) ⊆ U(R → S, M₂)` (051W).
* `Algebra.image_comap_iUnion_basicOpen_isFinitePresentationFreeAway`: under the identification
  `Spec(R_f) = D(f)`, one has `U(R_f → S_f, M_f) = D(f) ∩ U(R → S, M)` (051X).
* `Algebra.dense_iUnion_basicOpen_isFinitePresentationFreeAway_of_localizationAway`: if the `D(f)`,
  `f ∈ s`, have dense union and each `U(R_f → S_f, M_f)` is dense in `Spec(R_f)`, then
  `U(R → S, M)` is dense (051Y).

## Implementation notes

**The route to 051R is not the source's.** The source argues by induction on `dim (K ⊗_R S)`, `K`
the fraction field of `R`, using a prime filtration of `M` over the Noetherian ring `S` and a
factorization `R ⊂ R[y_1, …, y_d] ⊂ S` with the second extension finite. The proof here instead
uses the division algorithm for the degree-lexicographic monomial order, which settles the key case
outright. Writing `S` as a quotient of `A = R[y_1, …, y_d]` and filtering a finite `A`-module by
cyclic submodules reduces the statement to `M = A ⧸ I`; for that case, Dickson's lemma gives
finitely many `p_1, …, p_k ∈ I` whose leading exponents `μ_i` divide the leading exponent of every
nonzero element of `I`, and after inverting the product `f` of their leading coefficients, division
with remainder by the `p_i` exhibits `B[y] ⧸ I B[y]` as free on the monomials `y^ν` with `ν`
divisible by no `μ_i` (Macaulay's basis theorem, `free_quotient_of_degrees` below).

*Consequently `IsNoetherianRing R` is not used in the proof of 051R.* Nothing in the route above
needs it: the staircase of leading exponents of an arbitrary ideal of `A` is finitely generated by
Dickson's lemma rather than by Noetherianity, and the filtration of a module with `n` generators by
cyclic submodules has `n` steps. The hypothesis is kept because it is the source's, and because
051R is the Noetherian member of the family; the private lemmas it is proved from assume only
`IsDomain R`.

**Generic freeness is proved in the base-change model.** The private lemmas leading to 051R
conclude that `B ⊗[R] M` is free over *every* localization `B` of `R` in which a suitable `f`
becomes invertible. That form is what makes the induction work, since two successive choices of `f`
are combined by multiplying them and `B` is then a localization at neither alone;
`IsLocalizedModule.isBaseChange` converts it to the stated conclusion.

**The localizations in 051R, 051S and 051X are abstract.** Those three conclusions are asserted for
every model of the localizations involved — for 051R and 051S, every `R`-algebra `Rf` with
`IsLocalization.Away f Rf` and every `R`-linear `g : M → Mf` with
`IsLocalizedModule (Submonoid.powers f) g`. Any two such models being isomorphic over `R`, this is
equivalent to the single concrete assertion about `Localization.Away f` and
`LocalizedModule.Away f M`, which is the shape of the Mathlib sibling
`Module.FinitePresentation.exists_free_localizedModule_powers`; the quantified form is what a user
localizing along a standard open of `Spec R` applies without transporting along a chosen
construction. In 051T, 051W and 051Y the models are instead the canonical ones fixed by
`Algebra.IsFinitePresentationFreeAway`, and `Algebra.isFinitePresentationFreeAway_iff` moves those
conclusions to any other models; in 051Y taking abstract models would mean three families of types
indexed by `s` together with some fifteen families of instances, none of them mathematics.

**The `R`-module structure on `M`** in 051R and 051S is the one induced by `R → S`, recorded as
`[Module R M]` with `[IsScalarTower R S M]`, since the source's `M_f` is the localization of `M` as
an `R`-module. No finiteness of `M` over `R` is available: `M` is finite over `S` only, and `M_f`
will in general have infinite rank over `R_f` — already for `S = R[x]`, `M = S` — so the conclusion
is `Module.Free` alone. In 051T, 051W, 051X and 051Y no `R`-module structure on `M` occurs at all,
the `R_f`-action on `M_f` being the restriction of its `S_f`-action.

**The locus `U(R → S, M)` is written out** as the union of standard opens it is, since the library
has no definition for the construction 051V. Membership of a prime then unfolds to "some `f` outside
it satisfies 051U", which is how the source's proofs read. Openness of the locus, asserted by the
source alongside Equation 051V, is `isOpen_iUnion`. Mathlib's `Module.freeLocus R M` is the
pointwise analogue for one module over one ring and neither contains nor is contained in this
locus.

**Short exact sequences are given as two maps** with injectivity, surjectivity and
`Function.Exact`, rather than as a `CategoryTheory.ShortComplex.ShortExact` in `ModuleCat S`: the
conclusions are statements about the three types and their localizations, and passing through
`ModuleCat` would force them into a common universe and make every consumer package a submodule and
a quotient into a short complex. For the same reason the extension lemma used is
`free_of_shortExact` below rather than `ModuleCat.free_shortExact`.

## References

* [StacksProject 051Q](https://stacks.math.columbia.edu/tag/051Q)
* [StacksProject 051R](https://stacks.math.columbia.edu/tag/051R)
* [StacksProject 051S](https://stacks.math.columbia.edu/tag/051S)
* [StacksProject 051T](https://stacks.math.columbia.edu/tag/051T)
* [StacksProject 051W](https://stacks.math.columbia.edu/tag/051W)
* [StacksProject 051X](https://stacks.math.columbia.edu/tag/051X)
* [StacksProject 051Y](https://stacks.math.columbia.edu/tag/051Y)

## Tags

generic freeness, generic flatness, finite presentation, free module, localization, dense open
-/

/-!
## This file

The first of the four parts of `StacksFrontier.Algebra.Category.Ring.Epi.GenericFlatness`, whose
overview of Stacks section 051Q is the module docstring above. This part contains the shared lemmas
on extensions of free modules and flat base change, and generic freeness over a Noetherian domain,
`Module.exists_ne_zero_free_localizedModule_away` (051R). Stacks 051S is in
`StacksFrontier.Algebra.Category.Ring.Epi.GenericFlatness.FinitePresentation`, 051T in
`StacksFrontier.Algebra.Category.Ring.Epi.GenericFlatness.GenericFinitePresentation`, and the
generic freeness locus (051W, 051X, 051Y) in
`StacksFrontier.Algebra.Category.Ring.Epi.GenericFlatness.Locus`.
-/

@[expose] public section

universe u v w

/-- **An extension of free modules is free.** If `0 → N₁ → N₂ → N₃ → 0` is a short exact sequence
of `A`-modules with `N₁` and `N₃` free, then `N₂` is free: `N₃` is free, hence projective, so the
sequence splits and `N₂ ≃ N₁ × N₃`. This is `ModuleCat.free_shortExact` for three modules in three
different universes. -/
private theorem free_of_shortExact {A N₁ N₂ N₃ : Type*} [Ring A] [AddCommGroup N₁] [Module A N₁]
    [AddCommGroup N₂] [Module A N₂] [AddCommGroup N₃] [Module A N₃] {i : N₁ →ₗ[A] N₂}
    {q : N₂ →ₗ[A] N₃} (hi : Function.Injective i) (hq : Function.Surjective q)
    (hiq : Function.Exact i q) [Module.Free A N₁] [Module.Free A N₃] : Module.Free A N₂ := by
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective q (LinearMap.range_eq_top.mpr hq)
  exact Module.Free.of_equiv (lequivProdOfRightSplitExact hi (LinearMap.exact_iff.mp hiq).symm hs)

/-- Base change along a flat algebra preserves injectivity. This is
`Module.Flat.lTensor_preserves_injective_linearMap` for `LinearMap.baseChange`. -/
private theorem baseChange_injective {S : Type*} [CommSemiring S] (T : Type*) [Semiring T]
    [Algebra S T] [Module.Flat S T] {M N : Type*} [AddCommMonoid M] [Module S M] [AddCommMonoid N]
    [Module S N] {f : M →ₗ[S] N} (hf : Function.Injective f) :
    Function.Injective (f.baseChange T) := by
  rw [LinearMap.baseChange_eq_lTensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap f hf

/-- Base change along a flat algebra preserves exactness. This is `Module.Flat.lTensor_exact` for
`LinearMap.baseChange`. -/
private theorem baseChange_exact {S : Type*} [CommRing S] (T : Type*) [Ring T] [Algebra S T]
    [Module.Flat S T] {M N P : Type*} [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    [AddCommGroup P] [Module S P] {f : M →ₗ[S] N} {g : N →ₗ[S] P} (h : Function.Exact f g) :
    Function.Exact (f.baseChange T) (g.baseChange T) := by
  rw [LinearMap.baseChange_eq_lTensor, LinearMap.baseChange_eq_lTensor]
  exact Module.Flat.lTensor_exact T h

/-! ### Generic freeness over a Noetherian domain (051R) -/

section
open MvPolynomial MonomialOrder TensorProduct

/-- **Dickson's lemma**, over an arbitrary well-quasi-ordered partial order: every set `U` has a
finite subset `D` of minimal elements such that every element of `U` dominates one of them. For
exponents this is the classical statement, the instance being `Finsupp.wellQuasiOrderedLE`. -/
private theorem exists_finset_forall_exists_le {α : Type*} [PartialOrder α]
    [WellQuasiOrderedLE α] (U : Set α) :
    ∃ D : Finset α, ↑D ⊆ U ∧ ∀ ν ∈ U, ∃ μ ∈ D, μ ≤ ν := by
  classical
  have hanti : IsAntichain (· ≤ ·) {a | Minimal (· ∈ U) a} :=
    fun a ha b hb hne hab => hne (le_antisymm hab (hb.2 ha.1 hab))
  refine ⟨(WellQuasiOrderedLE.finite_of_isAntichain hanti).toFinset,
    fun a ha => ?_, fun ν hν => ?_⟩
  · simpa using ((Set.Finite.mem_toFinset _).mp ha).1
  · obtain ⟨μ, hμν, hμ⟩ := (Set.isPWO_of_wellQuasiOrderedLE U).exists_le_minimal hν
    exact ⟨μ, by simpa using hμ, hμν⟩

/-- A polynomial lies in the `B`-span of the monomials `y ^ ν` with `ν ∈ s` exactly when its
support is contained in `s`; the module analogue of `MvPolynomial.mem_ideal_span_monomial_image`.
-/
private theorem mem_span_monomial_image_iff {σ B : Type*} [CommRing B] {s : Set (σ →₀ ℕ)}
    {p : MvPolynomial σ B} :
    p ∈ Submodule.span B ((fun ν => monomial ν (1 : B)) '' s) ↔ ↑p.support ⊆ s := by
  rw [show ((fun ν => monomial ν (1 : B)) '' s) = ⇑(basisMonomials σ B) '' s by
    rw [coe_basisMonomials], (basisMonomials σ B).mem_span_image]
  rfl

/-- The leading exponent of a polynomial is unchanged by an injective change of coefficients. -/
private theorem degree_map_of_injective {σ : Type*} (m : MonomialOrder σ) {R B : Type*}
    [CommRing R] [CommRing B] {φ : R →+* B} (hφ : Function.Injective φ) (q : MvPolynomial σ R) :
    m.degree (MvPolynomial.map φ q) = m.degree q := by
  unfold MonomialOrder.degree
  rw [MvPolynomial.support_map_of_injective _ hφ]

/-- The leading coefficient of a polynomial is transported by an injective change of
coefficients. -/
private theorem leadingCoeff_map_of_injective {σ : Type*} (m : MonomialOrder σ) {R B : Type*}
    [CommRing R] [CommRing B] {φ : R →+* B} (hφ : Function.Injective φ) (q : MvPolynomial σ R) :
    m.leadingCoeff (MvPolynomial.map φ q) = φ (m.leadingCoeff q) := by
  rw [MonomialOrder.leadingCoeff, MonomialOrder.leadingCoeff, degree_map_of_injective m hφ,
    MvPolynomial.coeff_map]

/-- **Macaulay's basis theorem.** If a set `D` of exponents dominates the leading exponents of all
nonzero elements of an ideal `J` of `B[y]`, and every `μ ∈ D` is the leading exponent of an element
of `J` with unit leading coefficient, then `B[y] ⧸ J` is a free `B`-module on the standard
monomials, those `y ^ ν` with `ν` divisible by no element of `D`.

Independence holds because the standard monomials are part of the monomial basis of `B[y]` and an
element of `J` supported on them would have a standard leading exponent; spanning is division with
remainder (`MonomialOrder.div_set`) by the elements realizing `D`. -/
private theorem free_quotient_of_degrees {σ B : Type*} [CommRing B] [LinearOrder σ]
    [WellFoundedGT σ] (J : Ideal (MvPolynomial σ B)) (D : Set (σ →₀ ℕ))
    (hD : ∀ μ ∈ D, ∃ p ∈ J, degLex.degree p = μ ∧ IsUnit (degLex.leadingCoeff p))
    (hD' : ∀ p ∈ J, p ≠ 0 → ∃ μ ∈ D, μ ≤ degLex.degree p) :
    Module.Free B (MvPolynomial σ B ⧸ J) := by
  classical
  set Std : Set (σ →₀ ℕ) := {ν | ∀ μ ∈ D, ¬μ ≤ ν}
  set π : MvPolynomial σ B →ₗ[B] MvPolynomial σ B ⧸ J := (Ideal.Quotient.mkₐ B J).toLinearMap
  have hrange : Set.range (fun ν : Std => monomial (ν : σ →₀ ℕ) (1 : B))
      = (fun ν => monomial ν (1 : B)) '' Std :=
    (Set.image_eq_range (fun ν => monomial ν (1 : B)) Std).symm
  have hspan : Submodule.span B (Set.range fun ν : Std => π (monomial (ν : σ →₀ ℕ) 1))
      = (Submodule.span B ((fun ν => monomial ν (1 : B)) '' Std)).map π := by
    rw [Submodule.map_span, ← hrange, ← Set.range_comp]; rfl
  refine Module.Free.of_basis (Module.Basis.mk
    (v := fun ν : Std => π (monomial (ν : σ →₀ ℕ) 1)) ?_ ?_)
  · refine ((basisMonomials σ B).linearIndependent.comp _ Subtype.val_injective).map ?_
    rw [Submodule.disjoint_def]
    intro p hp hpJ
    rw [show ⇑(basisMonomials σ B) ∘ (fun ν : Std => (ν : σ →₀ ℕ)) =
      fun ν : Std => monomial (ν : σ →₀ ℕ) (1 : B) by rw [coe_basisMonomials]; rfl,
      hrange, mem_span_monomial_image_iff] at hp
    by_contra hp0
    obtain ⟨μ, hμD, hμle⟩ := hD' p (Ideal.Quotient.eq_zero_iff_mem.mp hpJ) hp0
    exact hp (degLex.degree_mem_support hp0) μ hμD hμle
  · intro X _
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective X
    obtain ⟨g, r, hqr, -, hrsupp⟩ := degLex.div_set
      (B := {p : MvPolynomial σ B | p ∈ J ∧ IsUnit (degLex.leadingCoeff p)}) (fun b hb => hb.2) q
    have hgJ : Finsupp.linearCombination (MvPolynomial σ B)
        (fun b : {p : MvPolynomial σ B | p ∈ J ∧ IsUnit (degLex.leadingCoeff p)} =>
          (b : MvPolynomial σ B)) g ∈ J := by
      rw [Finsupp.linearCombination_apply]
      exact Submodule.sum_mem _ fun b _ => Ideal.mul_mem_left _ _ b.2.1
    have hrq : Ideal.Quotient.mk J q = π r := by
      rw [hqr, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hgJ, zero_add]; rfl
    have hrStd : ↑r.support ⊆ Std := fun ν hν μ hμD => by
      obtain ⟨p, hpJ, hpdeg, hpunit⟩ := hD μ hμD
      exact hpdeg ▸ hrsupp ν hν p ⟨hpJ, hpunit⟩
    rw [hrq, hspan]
    exact Submodule.mem_map_of_mem (mem_span_monomial_image_iff.mpr hrStd)

section Localization

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- **The key case of generic freeness.** Let `R` be a domain and `I` an ideal of
`A = R[y_1, …, y_d]`. Then there is a nonzero `f ∈ R` such that for every localization `B` of `R`
in which `f` becomes invertible, the ring `B[y_1, …, y_d] ⧸ I B[y_1, …, y_d]` is a free
`B`-module: for `f` take the product of the leading coefficients of finitely many elements of `I`
whose leading exponents dominate all the others. -/
private theorem exists_ne_zero_free_quotient_map {R : Type u} [CommRing R] [IsDomain R] {d : ℕ}
    (I : Ideal (MvPolynomial (Fin d) R)) :
    ∃ f : R, f ≠ 0 ∧ ∀ (N : Submonoid R) (B : Type v) [CommRing B] [Algebra R B]
      [IsLocalization N B], IsUnit (algebraMap R B f) →
      Module.Free B (MvPolynomial (Fin d) B ⧸
        Ideal.map (MvPolynomial.map (algebraMap R B)) I) := by
  classical
  obtain ⟨D, hDU, hDle⟩ := exists_finset_forall_exists_le
    {ν : Fin d →₀ ℕ | ∃ p ∈ I, p ≠ 0 ∧ degLex.degree p = ν}
  choose! p hpI hp0 hpdeg using fun μ (hμ : μ ∈ D) => hDU hμ
  refine ⟨∏ μ ∈ D, degLex.leadingCoeff (p μ), Finset.prod_ne_zero_iff.mpr fun μ hμ =>
    degLex.leadingCoeff_ne_zero_iff.mpr (hp0 μ hμ), fun N B _ _ _ hfunit => ?_⟩
  rcases subsingleton_or_nontrivial B with hB | hB
  · exact Module.Free.of_subsingleton' B _
  have hNnzd : N ≤ nonZeroDivisors R := fun n hn =>
    mem_nonZeroDivisors_of_ne_zero fun h =>
      absurd (IsLocalization.subsingleton (S := B) (h ▸ hn)) (not_subsingleton B)
  have hinj : Function.Injective (algebraMap R B) := IsLocalization.injective B hNnzd
  refine free_quotient_of_degrees _ (↑D : Set (Fin d →₀ ℕ)) (fun μ hμ => ?_) (fun q hq hq0 => ?_)
  · refine ⟨MvPolynomial.map (algebraMap R B) (p μ), Ideal.mem_map_of_mem _ (hpI μ hμ), by
      rw [degree_map_of_injective _ hinj, hpdeg μ hμ], ?_⟩
    rw [leadingCoeff_map_of_injective _ hinj]
    exact isUnit_of_dvd_unit
      (map_dvd _ (Finset.dvd_prod_of_mem (fun μ => degLex.leadingCoeff (p μ)) hμ)) hfunit
  · -- clear denominators: `q` becomes an element `y` of `I` with the same leading exponent
    obtain ⟨⟨⟨y, hyI⟩, s⟩, hs⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (M := N.map (MvPolynomial.C (σ := Fin d)))
        (S := MvPolynomial (Fin d) B)).mp hq
    obtain ⟨c, hcN, hcs⟩ := s.2
    have hcunit : IsUnit (algebraMap R B c) := IsLocalization.map_units B (⟨c, hcN⟩ : N)
    have halg : ∀ z : MvPolynomial (Fin d) R,
        algebraMap (MvPolynomial (Fin d) R) (MvPolynomial (Fin d) B) z =
          MvPolynomial.map (algebraMap R B) z := fun _ => rfl
    have hs' : q * MvPolynomial.C (algebraMap R B c) = MvPolynomial.map (algebraMap R B) y := by
      rw [halg, halg, show (s : MvPolynomial (Fin d) R) = MvPolynomial.C c from hcs.symm,
        MvPolynomial.map_C] at hs
      exact hs
    have hy0 : y ≠ 0 := fun hy => hq0 (by
      rw [hy, map_zero] at hs'
      simpa using ((hcunit.map (MvPolynomial.C (σ := Fin d))).mul_left_eq_zero).mp hs')
    have hdegq : degLex.degree y = degLex.degree q := by
      rw [← degree_map_of_injective degLex hinj y, ← hs',
        degLex.degree_mul_of_isRegular_right hq0
          (by rw [degLex.leadingCoeff_C]; exact hcunit.isRegular),
        degLex.degree_C, add_zero]
    obtain ⟨μ, hμD, hμle⟩ := hDle _ ⟨y, hyI, hy0, rfl⟩
    exact ⟨μ, by simpa using hμD, hdegq ▸ hμle⟩

end Localization

/-- **A flat base change of an extension of free modules is free.** If `B` is a flat `R`-algebra
and `0 → M₁ → M₂ → M₃ → 0` is a short exact sequence of `R`-modules whose base changes
`B ⊗[R] M₁` and `B ⊗[R] M₃` are free over `B`, then `B ⊗[R] M₂` is free over `B`: flatness keeps
the base-changed sequence short exact. -/
private theorem free_baseChange_of_exact {R : Type u} [CommRing R] (B : Type v) [CommRing B]
    [Algebra R B] [Module.Flat R B] {M₁ M₂ M₃ : Type w} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    (ι : M₁ →ₗ[R] M₂) (π : M₂ →ₗ[R] M₃) (hι : Function.Injective ι)
    (hπ : Function.Surjective π) (hex : Function.Exact ι π)
    (h₁ : Module.Free B (B ⊗[R] M₁)) (h₃ : Module.Free B (B ⊗[R] M₃)) :
    Module.Free B (B ⊗[R] M₂) :=
  have := h₁
  have := h₃
  free_of_shortExact (baseChange_injective B hι) (LinearMap.baseChange_surjective B hπ)
    (baseChange_exact B hex)

/-- Freeness over `B` passes from `B[y] ⧸ I B[y]` to `B ⊗_R (R[y] ⧸ I)`, the two being isomorphic
as `B`-algebras. -/
private theorem free_tensor_quotient_of_free_quotient {R : Type u} [CommRing R] {σ : Type*}
    (B : Type v) [CommRing B] [Algebra R B] (I : Ideal (MvPolynomial σ R))
    (h : Module.Free B (MvPolynomial σ B ⧸
      Ideal.map (MvPolynomial.map (algebraMap R B)) I)) :
    Module.Free B (B ⊗[R] (MvPolynomial σ R ⧸ I)) := by
  have hcomp : (MvPolynomial.map (algebraMap R B) : MvPolynomial σ R →+* MvPolynomial σ B) =
      (MvPolynomial.algebraTensorAlgEquiv R B).toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := R) (A := B)
          (B := MvPolynomial σ R)).toRingHom :=
    RingHom.ext fun x => by
      rw [RingHom.comp_apply]
      exact ((MvPolynomial.algebraTensorAlgEquiv R B).eq_symm_apply.mp
        (MvPolynomial.algebraTensorAlgEquiv_symm_map R B x).symm).symm
  refine Module.Free.of_equiv' h
    (((Algebra.TensorProduct.tensorQuotientEquiv (R := R) B (MvPolynomial σ R) B I).trans
      (Ideal.quotientEquivAlg _ _ (MvPolynomial.algebraTensorAlgEquiv R B) ?_)).symm.toLinearEquiv)
  change Ideal.map (MvPolynomial.map (algebraMap R B)) I =
    Ideal.map (MvPolynomial.algebraTensorAlgEquiv R B).toAlgHom.toRingHom
      (Ideal.map (Algebra.TensorProduct.includeRight (R := R) (A := B)
        (B := MvPolynomial σ R)).toRingHom I)
  rw [Ideal.map_map, ← hcomp]

/-- Generators of `M` other than one lying in `Q` still generate `M ⧸ Q`. -/
private theorem span_image_mkQ_diff_singleton_eq_top {A M : Type*} [Ring A] [AddCommGroup M]
    [Module A M] (Q : Submodule A M) {t : Set M} {x : M} (hx : x ∈ Q)
    (ht : Submodule.span A t = ⊤) : Submodule.span A (Q.mkQ '' (t \ {x})) = ⊤ := by
  have h0 : Q.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero Q).mpr hx
  rw [← Submodule.span_insert_zero, ← h0, ← Set.image_insert_eq]
  refine top_le_iff.mp (le_trans ?_ (Submodule.span_mono
    (Set.image_mono (Set.subset_insert_sdiff_singleton x t))))
  rw [← Submodule.map_span, ht, Submodule.map_top, Submodule.range_mkQ]

/-- **The cyclic case of generic freeness.** A cyclic submodule `A ∙ x` of a module over
`A = R[y_1, …, y_d]` is `A ⧸ I` for the annihilator `I` of `x`, so by the key case there is a
nonzero `f ∈ R` making `B ⊗_R (A ∙ x)` free over every localization `B` of `R` in which `f`
becomes invertible. -/
private theorem exists_ne_zero_free_tensor_span_singleton {R : Type u} [CommRing R] [IsDomain R]
    {d : ℕ} {M : Type w} [AddCommGroup M] [Module R M] [Module (MvPolynomial (Fin d) R) M]
    [IsScalarTower R (MvPolynomial (Fin d) R) M] (x : M) :
    ∃ f : R, f ≠ 0 ∧ ∀ (N : Submonoid R) (B : Type v) [CommRing B] [Algebra R B]
      [IsLocalization N B], IsUnit (algebraMap R B f) →
      Module.Free B (B ⊗[R] Submodule.span (MvPolynomial (Fin d) R) ({x} : Set M)) := by
  obtain ⟨f, hf, hfree⟩ := exists_ne_zero_free_quotient_map (R := R) (d := d)
    (LinearMap.ker (LinearMap.toSpanSingleton (MvPolynomial (Fin d) R) M x))
  set A := MvPolynomial (Fin d) R
  have e : (A ⧸ LinearMap.ker (LinearMap.toSpanSingleton A M x)) ≃ₗ[A]
      Submodule.span A ({x} : Set M) :=
    (LinearMap.quotKerEquivRange (LinearMap.toSpanSingleton A M x)).trans
      (LinearEquiv.ofEq _ _ (LinearMap.span_singleton_eq_range A M x).symm)
  exact ⟨f, hf, fun N B _ _ _ hu => Module.Free.of_equiv'
    (free_tensor_quotient_of_free_quotient B _ (hfree N B hu))
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B) (e.restrictScalars R))⟩

/-- **Generic freeness for a finite module over a polynomial ring.** Let `R` be a domain and let
`M` be a module over `A = R[y_1, …, y_d]` generated by at most `n` elements. Then there is a
nonzero `f ∈ R` such that `B ⊗_R M` is free over every localization `B` of `R` in which `f` becomes
invertible.

The proof is induction on `n`: a generator `x` spans a cyclic submodule `C = A ∙ x`, free after
inverting some `f₁` by the cyclic case, `M ⧸ C` needs one generator fewer and so is free after
inverting some `f₂`, and `M` is an extension of the two, so `f₁ f₂` works. -/
@[ega "IV 6.11.9" "more general", sga "1 IV 6.7" "more general"]
private theorem exists_ne_zero_free_tensor {R : Type u} [CommRing R] [IsDomain R] (d : ℕ) :
    ∀ (n : ℕ) (M : Type w) [AddCommGroup M] [Module R M]
      [Module (MvPolynomial (Fin d) R) M] [IsScalarTower R (MvPolynomial (Fin d) R) M]
      (s : Finset M), s.card ≤ n →
      Submodule.span (MvPolynomial (Fin d) R) (s : Set M) = ⊤ →
      ∃ f : R, f ≠ 0 ∧ ∀ (N : Submonoid R) (B : Type v) [CommRing B] [Algebra R B]
        [IsLocalization N B], IsUnit (algebraMap R B f) → Module.Free B (B ⊗[R] M) := by
  classical
  intro n
  induction n with
  | zero =>
    intro M _ _ _ _ s hcard hspan
    obtain rfl := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    rw [Finset.coe_empty, Submodule.span_empty] at hspan
    have : Subsingleton M := subsingleton_of_forall_eq 0 fun y => by
      simpa using (hspan.ge Submodule.mem_top : y ∈ (⊥ : Submodule (MvPolynomial (Fin d) R) M))
    exact ⟨1, one_ne_zero, fun N B _ _ _ _ => Module.Free.of_subsingleton B _⟩
  | succ n ih =>
    intro M _ _ _ _ s hcard hspan
    rcases Finset.eq_empty_or_nonempty s with rfl | ⟨x, hx⟩
    · exact ih M ∅ (by simp) hspan
    set C : Submodule (MvPolynomial (Fin d) R) M := Submodule.span _ ({x} : Set M)
    obtain ⟨f₁, hf₁, hfree₁⟩ := exists_ne_zero_free_tensor_span_singleton (R := R) (d := d) x
    obtain ⟨f₂, hf₂, hfree₂⟩ := ih (M ⧸ C) ((s.erase x).image C.mkQ)
      (le_trans Finset.card_image_le (by rw [Finset.card_erase_of_mem hx]; omega))
      (by rw [Finset.coe_image, Finset.coe_erase]
          exact span_image_mkQ_diff_singleton_eq_top C
            (Submodule.mem_span_singleton_self x) hspan)
    refine ⟨f₁ * f₂, mul_ne_zero hf₁ hf₂, fun N B _ _ _ hu => ?_⟩
    rw [map_mul] at hu
    have : Module.Flat R B := IsLocalization.flat B N
    exact free_baseChange_of_exact B (C.subtype.restrictScalars R) (C.mkQ.restrictScalars R)
      C.injective_subtype C.mkQ_surjective (LinearMap.exact_subtype_mkQ C)
      (hfree₁ N B (isUnit_of_mul_isUnit_left hu)) (hfree₂ N B (isUnit_of_mul_isUnit_right hu))

/-- **Generic freeness, in the base-change model.** Let `R` be a domain, `S` an `R`-algebra of
finite type and `M` a finite `S`-module. Then there is a nonzero `f ∈ R` such that `B ⊗_R M` is
free over every localization `B` of `R` in which `f` becomes invertible: write `S` as a quotient of
`A = R[y_1, …, y_d]`, so that `M` is a finite `A`-module, and apply the previous lemma. -/
private theorem exists_ne_zero_free_tensor_of_finiteType {R : Type u} [CommRing R] [IsDomain R]
    (S : Type*) [CommRing S] [Algebra R S] [Algebra.FiniteType R S] (M : Type w) [AddCommGroup M]
    [Module R M] [Module S M] [IsScalarTower R S M] [Module.Finite S M] :
    ∃ f : R, f ≠ 0 ∧ ∀ (N : Submonoid R) (B : Type v) [CommRing B] [Algebra R B]
      [IsLocalization N B], IsUnit (algebraMap R B f) → Module.Free B (B ⊗[R] M) := by
  obtain ⟨d, ψ, hψ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R S)
  let _ : Algebra (MvPolynomial (Fin d) R) S := ψ.toRingHom.toAlgebra
  have _ : IsScalarTower R (MvPolynomial (Fin d) R) S :=
    IsScalarTower.of_algebraMap_eq fun r => (ψ.commutes r).symm
  let _ : Module (MvPolynomial (Fin d) R) M :=
    Module.compHom M (algebraMap (MvPolynomial (Fin d) R) S)
  have hsmul : ∀ (b : MvPolynomial (Fin d) R) (y : M),
      b • y = algebraMap (MvPolynomial (Fin d) R) S b • y := fun _ _ => rfl
  have _ : IsScalarTower (MvPolynomial (Fin d) R) S M :=
    ⟨fun a s m => by rw [hsmul, Algebra.smul_def, mul_smul]⟩
  have _ : IsScalarTower R (MvPolynomial (Fin d) R) M :=
    ⟨fun r a m => by
      rw [hsmul, hsmul, Algebra.smul_def, map_mul,
        ← IsScalarTower.algebraMap_apply R (MvPolynomial (Fin d) R) S, mul_smul, algebraMap_smul]⟩
  have _ : Module.Finite (MvPolynomial (Fin d) R) S :=
    Module.Finite.of_surjective (Algebra.linearMap (MvPolynomial (Fin d) R) S) fun y => by
      obtain ⟨z, hz⟩ := hψ y
      exact ⟨z, by rw [Algebra.linearMap_apply, RingHom.algebraMap_toAlgebra]; exact hz⟩
  have _ : Module.Finite (MvPolynomial (Fin d) R) M := Module.Finite.trans S M
  obtain ⟨s, hs⟩ := Module.finite_def.mp ‹Module.Finite (MvPolynomial (Fin d) R) M›
  exact exists_ne_zero_free_tensor (R := R) d s.card M s le_rfl hs

end

namespace Module

/-- **Stacks 051R** (generic freeness). Let `R` be a Noetherian domain, let `S` be an `R`-algebra
of finite type and let `M` be a finite `S`-module. Then there is a nonzero `f ∈ R` such that the
localization `M_f` is a free `R_f`-module.

The proof is not the source's induction on `dim (K ⊗_R S)`: it reduces to `M = A ⧸ I` over a
polynomial ring `A = R[y_1, …, y_d]` and settles that case by division with remainder, so
`IsNoetherianRing R` is not used. See the module docstring. -/
@[nolint unusedArguments, stacks 051R "The localizations are abstract: the conclusion asserts
freeness over every model `Rf` of `R_f` and `Mf` of `M_f`, pinned by `IsLocalization.Away` and
`IsLocalizedModule`. The `R`-module structure on `M` is the one induced by `R → S`. See the module
docstring.", ega "IV 6.9.2", ega "IV 8.9.4" "affine Noetherian case", sga "1 IV 6.7"]
public theorem exists_ne_zero_free_localizedModule_away
    {R S M : Type*} [CommRing R] [IsNoetherianRing R] [IsDomain R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M] :
    ∃ f : R, f ≠ 0 ∧ ∀ (Rf : Type*) [CommRing Rf] [Algebra R Rf] [IsLocalization.Away f Rf]
      (Mf : Type*) [AddCommGroup Mf] [Module R Mf] [Module Rf Mf] [IsScalarTower R Rf Mf]
      (g : M →ₗ[R] Mf) [IsLocalizedModule (Submonoid.powers f) g],
      Module.Free Rf Mf := by
  obtain ⟨f, hf, hfree⟩ := exists_ne_zero_free_tensor_of_finiteType (R := R) S M
  refine ⟨f, hf, fun Rf _ _ _ Mf _ _ _ _ g _ => Module.Free.of_equiv' (hfree (.powers f) Rf ?_)
    (IsLocalizedModule.isBaseChange (Submonoid.powers f) Rf g).equiv⟩
  exact IsLocalization.map_units Rf (⟨f, Submonoid.mem_powers f⟩ : Submonoid.powers f)

end Module

end
