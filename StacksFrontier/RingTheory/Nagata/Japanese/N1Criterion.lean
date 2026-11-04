module

import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.Henselian
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop

public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.Nagata
public import StacksFrontier.RingTheory.EssentialFiniteness.Defs
public import StacksFrontier.RingTheory.Nagata.Shrink
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Checking universal Japaneseness on N-1 finite type domains

This is Stacks project **Tag 0351** (Lemma 10.162.3).

Throughout, all rings are commutative with unit. For a ring map `R → S`, "of finite type"
means `S` is generated as an `R`-algebra by finitely many elements (`Algebra.FiniteType`).
For a domain `R`, write `Frac(R)` (or `K`) for its field of fractions (`IsFractionRing`).
For a ring extension / map `A → B`, the *integral closure of `A` in `B`* is the subring of
`B` consisting of all elements of `B` that are integral over `A` (Mathlib:
`integralClosure A B`). An `R`-module is *finite* if it is finitely generated
(`Module.Finite`).

The relevant definitions are from Stacks Tag 032F (Definition 10.161.1, N-1 / N-2) and
Tag 032R (Definition 10.162.1, universally Japanese).

## Main results
Let `R` be a ring. Suppose:

  (H) For every finite type ring map `R → S` with `S` a domain, the domain `S` is N-1.

Then `R` is universally Japanese.

## Implementation notes

- "Finite type" for a ring map refers to algebra-finiteness, whereas "finite" refers to
  module-finiteness; these are kept distinct (`Algebra.FiniteType` vs `Module.Finite`).
- A fraction field of a domain `R` is encoded as an arbitrary field `K` with
  `[Algebra R K] [IsFractionRing R K]`. Since any two such `K` are canonically isomorphic,
  quantifying over all such `K` faithfully captures "the fraction field".
-/

-- ===== merged from Sec162/Tag0351 =====

@[expose] public section

open AlgebraicGeometry
open scoped nonZeroDivisors
universe u v

/-- For a domain `A` with fraction field `Fr` inside a field `LL`, any `x : LL` integral
(equivalently algebraic) over `Fr` becomes integral over `A` after multiplying by a
suitable nonzero element of `A`. -/
theorem exists_integral_smul (A : Type*) [CommRing A] [IsDomain A] (Fr : Type*) [Field Fr]
    [Algebra A Fr] [IsFractionRing A Fr] (LL : Type*) [Field LL] [Algebra Fr LL] [Algebra A LL]
    [IsScalarTower A Fr LL] (x : LL) (hx : IsIntegral Fr x) :
    ∃ d : A, d ≠ 0 ∧ IsIntegral A (algebraMap A LL d * x) := by
  obtain ⟨m, hm⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors A) (Rₘ := Fr) x hx
  refine ⟨(m : A), nonZeroDivisors.coe_ne_zero m, ?_⟩
  rwa [Submonoid.smul_def, Algebra.smul_def] at hm

/-- The integral closure of `A` in `LL` has `LL` as its field of fractions, provided `LL`
is algebraic over the fraction field `Fr` of `A`. -/
@[ega "II 6.3.7" "special case", ega "II 6.3.9" "special case"]
theorem isFractionRing_integralClosure (A : Type*) [CommRing A] [IsDomain A] (Fr : Type*)
    [Field Fr] [Algebra A Fr] [IsFractionRing A Fr] (LL : Type*) [Field LL] [Algebra Fr LL]
    [Algebra A LL] [IsScalarTower A Fr LL] [Algebra.IsAlgebraic Fr LL] :
    IsFractionRing (integralClosure A LL) LL := by
  have : Algebra.IsAlgebraic A Fr := IsLocalization.isAlgebraic Fr (nonZeroDivisors A)
  have : Algebra.IsAlgebraic A LL := Algebra.IsAlgebraic.trans A Fr LL
  have := FaithfulSMul.trans A Fr LL
  exact integralClosure.isFractionRing_of_algebraic fun x hx =>
    FaithfulSMul.algebraMap_injective A LL (by rwa [map_zero])

-- Sub-lemmas for the proof sketch of Stacks Tag 0351.

open Polynomial in
/-- Scaling an element integral over `S` by `g : S` pushes the coefficients of its monic equation
below the leading one into `(g)`: the `i`-th coefficient of `Polynomial.scaleRoots P g` is
`g ^ (P.natDegree - i) * P.coeff i`. -/
private theorem exists_monic_dvd_coeff_aeval_eq_zero {S B : Type*} [CommRing S] [CommRing B]
    [Algebra S B] (g : S) {y : B} (hy : IsIntegral S y) :
    ∃ Q : S[X],
      Q.Monic ∧ (∀ i < Q.natDegree, g ∣ Q.coeff i) ∧ aeval (algebraMap S B g * y) Q = 0 := by
  obtain ⟨P, hPm, hPe⟩ := hy
  refine
    ⟨P.scaleRoots g, (monic_scaleRoots_iff g).2 hPm, fun j hj => ?_,
      scaleRoots_aeval_eq_zero (by simpa [aeval_def] using hPe)⟩
  rw [natDegree_scaleRoots] at hj
  obtain ⟨k, hk⟩ : ∃ k, P.natDegree - j = k + 1 := ⟨P.natDegree - j - 1, by omega⟩
  exact
    ⟨P.coeff j * g ^ k, by
      rw [coeff_scaleRoots, hk, pow_succ]; ring⟩

open Polynomial in
/-- **Step 1 (denominator-cleared, `g`-scaled generators).** Let `S` be a domain with fraction
field `K`, let `L / K` be a finite extension and let `g ≠ 0` in `S`. Then `L` is spanned over `K`
by a finite set of elements each of which is a root of a monic polynomial over `S` whose
coefficients below the leading one are all divisible by `g`.

For `g = 1` this says that `L` is spanned over `K` by finitely many elements integral over `S`:
a `K`-basis `b` of `L` becomes one after clearing the denominators of its members, since
`exists_integral_smul` provides `dᵢ ≠ 0` in `S` with `dᵢ * b i` integral over `S` and scaling a
basis by units of `K` leaves a basis. Scaling by the further unit `g` keeps the span, and
replaces the monic equation of `dᵢ * b i` by its `Polynomial.scaleRoots` at `g`, whose `i`-th
coefficient carries a factor `g ^ (d - i)`.

The divisibility is what makes the subalgebra generated by such a set *local* over a local `S`
with `g` in the maximal ideal; see Stacks Tag 0BI2. -/
theorem exists_clearedBasis_spanning {S : Type*} [CommRing S] [IsDomain S] {K : Type*} [Field K]
    [Algebra S K] [IsFractionRing S K] {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra S L] [IsScalarTower S K L] (g : S) (hg : g ≠ 0) :
    ∃ s : Finset L,
      (∀ x ∈ s, ∃ Q : S[X], Q.Monic ∧ (∀ i < Q.natDegree, g ∣ Q.coeff i) ∧ aeval x Q = 0) ∧
        Submodule.span K (s : Set L) = ⊤ := by
  classical
  have : Algebra.IsIntegral K L := Algebra.IsIntegral.of_finite K L
  set b := Module.finBasis K L
  choose d hd hdint using fun i =>
    exists_integral_smul S K L (b i) (Algebra.IsIntegral.isIntegral (b i))
  set w : Fin (Module.finrank K L) → Kˣ := fun i =>
    Units.mk0 (algebraMap S K (g * d i))
      (by simpa using (IsFractionRing.injective S K).ne (mul_ne_zero hg (hd i))) with
    hw
  have hb : ∀ i, (b.unitsSMul w) i = algebraMap S L g * (algebraMap S L (d i) * b i) := by
    intro i
    rw [Module.Basis.unitsSMul_apply, Units.smul_def, hw]
    simp [Algebra.smul_def, IsScalarTower.algebraMap_apply S K L, mul_assoc]
  refine ⟨Finset.image (b.unitsSMul w) Finset.univ, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    rw [hb i]
    exact exists_monic_dvd_coeff_aeval_eq_zero g (hdint i)
  · rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact (b.unitsSMul w).span_eq

/-- **Step 2 (`L` is the fraction field of the subalgebra).** An `S`-subalgebra `B` of a field
`L` whose span over the fraction field `K` of `S` is all of `L` has `L` as its own field of
fractions.

The elements of `L` admitting a denominator in `S` form a `K`-submodule of `L` — a denominator
for `c • z` is one for `z` times a denominator of `c` in `K` — and it contains `B`, hence is all
of `L` by `Submodule.span_le`; a single denominator then exhibits any `z : L` as a quotient of
two elements of `B`. Neither finiteness of `L` over `K` nor finite generation of `B` is used. -/
theorem isFractionRing_of_span_eq_top {S : Type*} [CommRing S] [IsDomain S] {K : Type*} [Field K]
    [Algebra S K] [IsFractionRing S K] {L : Type*} [Field L] [Algebra K L] [Algebra S L]
    [IsScalarTower S K L] (B : Subalgebra S L) (hspan : Submodule.span K (B : Set L) = ⊤) :
    IsFractionRing B L := by
  have := FaithfulSMul.trans S K L
  have hinj : ∀ a : S, a ≠ 0 → algebraMap S L a ≠ 0 := fun a ha =>
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective S L)).2 ha
  let D : Submodule K L :=
    { carrier := {z | ∃ a : S, a ≠ 0 ∧ algebraMap S L a * z ∈ B}
      zero_mem' := ⟨1, one_ne_zero, by simp⟩
      add_mem' := by
        rintro x y ⟨a, ha, hx⟩ ⟨c, hc, hy⟩
        refine ⟨a * c, mul_ne_zero ha hc, ?_⟩
        rw [show
            algebraMap S L (a * c) * (x + y) =
              algebraMap S L c * (algebraMap S L a * x) + algebraMap S L a * (algebraMap S L c * y)
            by
            rw [map_mul]; ring]
        exact add_mem (mul_mem (B.algebraMap_mem c) hx) (mul_mem (B.algebraMap_mem a) hy)
      smul_mem' := by
        rintro c x ⟨a, ha, hx⟩
        obtain ⟨r, q, hq⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors S) c
        refine ⟨a * r, mul_ne_zero ha (nonZeroDivisors.coe_ne_zero r), ?_⟩
        have hL : algebraMap S L (r : S) * algebraMap K L c = algebraMap S L q := by
          have := congrArg (algebraMap K L) hq
          rwa [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ←
            IsScalarTower.algebraMap_apply, eq_comm] at this
        rw [show algebraMap S L (a * r) * (c • x) = algebraMap S L q * (algebraMap S L a * x) by
            rw [Algebra.smul_def, map_mul]; linear_combination (algebraMap S L a * x) * hL]
        exact mul_mem (B.algebraMap_mem q) hx }
  refine IsFractionRing.of_field B L fun z => ?_
  obtain ⟨a, ha, hmem⟩ : z ∈ D :=
    (hspan.symm.trans_le (Submodule.span_le.2 fun x hx => ⟨1, one_ne_zero, by simpa using hx⟩) :
        (⊤ : Submodule K L) ≤ D)
      Submodule.mem_top
  refine ⟨⟨_, hmem⟩, ⟨algebraMap S L a, B.algebraMap_mem a⟩, ?_⟩
  show z = (algebraMap S L a * z) / algebraMap S L a
  rw [mul_comm, mul_div_assoc, div_self (hinj a ha), mul_one]

/-- N-1 for `S` is finiteness of the integral closure of `S` in *any* of its fraction fields: the
canonical isomorphism `Frac S ≃ₐ[S] L` carries one integral closure onto the other. -/
theorem module_finite_integralClosure_of_isN1 (S : Type*) [CommRing S] (L : Type*) [Field L]
    [Algebra S L] [IsFractionRing S L] (h : IsN1 S) : Module.Finite S (integralClosure S L) := by
  let e : FractionRing S ≃ₐ[S] L := IsLocalization.algEquiv (nonZeroDivisors S) _ _
  have he :
    Subalgebra.map (e : FractionRing S →ₐ[S] L) (integralClosure S (FractionRing S)) =
      integralClosure S L :=
    integralClosure_map_algEquiv e
  exact
    Module.Finite.equiv
      (he ▸
          Subalgebra.equivMapOfInjective (integralClosure S (FractionRing S))
            (e : FractionRing S →ₐ[S] L) e.injective).toLinearEquiv

/-- **Steps 2–4 assembled.** Let `S` be a domain of finite type over `R` with fraction field `K`,
let `L` be a field extension of `K` and let `s ⊆ L` be a finite set of elements integral over `S`
spanning `L` over `K`. If every domain of finite type over `R` is N-1, then the integral closure
of `S` in `L` is a finite `S`-module, i.e. `S` is N-2 for the extension `L`.

The extension `L / K` need not be finite: it is finite as soon as such an `s` exists.

The subalgebra `S' = S[s]` of `L` is module-finite over `S`, being generated by finitely many
integral elements, hence of finite type over `R`; it has `L` as its fraction field
(`isFractionRing_of_span_eq_top`), so N-1 for `S'` says that `integralClosure S' L` is a finite
`S'`-module, hence a finite `S`-module. Being integral over `S` and integrally closed in `L`, it
*is* the integral closure of `S` in `L` (Stacks Tag 0308), whence the conclusion. -/
theorem isN2_of_isN1_of_clearedBasis {R : Type*} [CommRing R] {S : Type*} [CommRing S] [IsDomain S]
    [Algebra R S] [Algebra.FiniteType R S] {K : Type*} [Field K] [Algebra S K] [IsFractionRing S K]
    {L : Type u} [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    (H : ∀ (T : Type u) [CommRing T] [IsDomain T] [Algebra R T] [Algebra.FiniteType R T], IsN1 T)
    (s : Finset L) (hsint : ∀ x ∈ s, IsIntegral S x) (hspan : Submodule.span K (s : Set L) = ⊤) :
    Module.Finite S (integralClosure S L) := by
  classical
  set S' := Algebra.adjoin S (s : Set L) with hS'
  -- (a) `S'` is module-finite over `S`, hence integral over `S`, and of finite type over `R`.
  have : Module.Finite S S' := Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet hsint
  have : Algebra.IsIntegral S S' := Algebra.IsIntegral.of_finite S S'
  let : Algebra R S' := ((algebraMap S S').comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType R S' := .trans (S := S) inferInstance (Module.Finite.finiteType S')
  -- (b) `L` is the fraction field of `S'`, so N-1 applies to `S'` with `K' = L`.
  have : IsFractionRing S' L :=
    isFractionRing_of_span_eq_top S'
      (le_antisymm le_top
        (hspan.symm.trans_le (Submodule.span_mono (Algebra.subset_adjoin (R := S)))))
  have : Module.Finite S' (integralClosure S' L) :=
    module_finite_integralClosure_of_isN1 S' L (H S')
  -- (c) `integralClosure S' L` is the integral closure of `S` in `L` (Stacks Tag 0308).
  have : Algebra.IsIntegral S (integralClosure S' L) := Algebra.IsIntegral.trans S'
  have : Module.Finite S (integralClosure S' L) := Module.Finite.trans S' _
  have : IsIntegralClosure (integralClosure S' L) S L := IsIntegralClosure.of_isIntegrallyClosedIn
  exact
    Module.Finite.equiv
      (IsIntegralClosure.equiv S (integralClosure S' L) L (integralClosure S L)).toLinearEquiv

/-- **Stacks Tag 0351.** Let `R` be a ring such that for every finite type ring map
`R → S` with `S` a domain, the domain `S` is N-1. Then `R` is universally Japanese. -/
@[stacks 0351, ega "IV 7.7.1" "N-1 ⇒ univ. Japanese"]
theorem isUniversallyJapanese_of_finiteType_isN1 (R : Type u) [CommRing R]
    (H : ∀ (S : Type u) [CommRing S] [IsDomain S] [Algebra R S] [Algebra.FiniteType R S], IsN1 S) :
    IsUniversallyJapaneseRing R := by
  -- Unfold to: given a finite-type domain `R`-algebra `S` and a finite extension `L` of
  -- `K = Frac S`, show `Module.Finite S (integralClosure S L)`.
  refine { japanese := fun S _ _ _ _ => { finite := fun L _ _ _ _ _ => ?_ } }
  -- Step 1: produce denominator-cleared generators that span `L` over `K` and are
  -- integral over `S` (no scaling is needed here, so `g = 1`).
  obtain ⟨s, hs, hspan⟩ :=
    exists_clearedBasis_spanning (K := FractionRing S) (L := L) (1 : S) one_ne_zero
  -- Steps 2–4: build `S' = S[s]`, apply N-1 to `S'`, transport finiteness back to `S`.
  exact
    isN2_of_isN1_of_clearedBasis (R := R) H s
      (fun x hx => by
        obtain ⟨Q, hQm, -, hQe⟩ := hs x hx; exact ⟨Q, hQm, hQe⟩)
      hspan
