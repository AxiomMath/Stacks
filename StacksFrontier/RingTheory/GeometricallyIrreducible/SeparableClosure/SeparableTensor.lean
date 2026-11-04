module

public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.FieldTheory.SeparablyGenerated
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-! # Finiteness of `[k' : k]` and base change along separable algebraic extensions

First part of the proof that `K` is geometrically irreducible over the separable algebraic
closure `k'` of `k` in `K`: the finiteness of `[k' : k]` for finitely generated `K/k`
(Stacks 037Q (2)), and the fact that base change of `K` along separable algebraic extensions
of a separably closed subfield stays a domain. -/

/-!
# Geometric irreducibility over the separable algebraic closure

Let `K/k` be a field extension and consider the subextension `K/k'/k` where `k'` consists of
the elements of `K` that are separably algebraic over `k`. Then `K` is geometrically
irreducible over `k'`, and if `K/k` is a finitely generated field extension then
`[k' : k] < ∞`.

Throughout, `k` is a field and `K/k` is a field extension, that is, `K` is a field and a
`k`-algebra via the structure map `k → K`.

## Conventions

An element `α ∈ K` is *separably algebraic over `k`* when it is algebraic over `k` and its
minimal polynomial over `k` is separable, which is `IsSeparable k α`.

The subextension `k' = {α ∈ K | α separably algebraic over k}` is an intermediate field
`k ⊆ k' ⊆ K`, the separable algebraic closure of `k` in `K`, namely
`separableClosure k K : IntermediateField k K`; its carrier is exactly the set of `α ∈ K` with
`IsSeparable k α`. We regard `K` as a `k'`-algebra in the natural way.

For a field `F` and an `F`-algebra `S`, `S` is *geometrically irreducible over `F`* when for
every field extension `F'/F` the space `Spec (S ⊗_F F')` is irreducible, irreducible spaces
being nonempty by convention; in Lean, `IrreducibleSpace (PrimeSpectrum (S ⊗[F] F'))` for every
field `F'` with an `F`-algebra structure. The main statement applies this with `F = k'` and
`S = K`.

Finally, `K/k` is *finitely generated as a field* when `K = k(x₁, …, x_n)` for finitely many
`xᵢ ∈ K`, that is, when the top intermediate field is generated as a field by a finite subset.
This is finite generation as a field, not as a `k`-algebra: `k(t)` is finitely generated as a
field but not as a `k`-algebra. The formalization is `(⊤ : IntermediateField k K).FG`, that is,
`∃ s : Finset K, IntermediateField.adjoin k (s : Set K) = ⊤`, and not `Algebra.FiniteType k K`.
-/

@[expose] public section

open scoped TensorProduct

/-! ## Part 2 sub-lemmas (finiteness of `[k' : k]`)

The mathematical argument (Stacks 037J / 037Q second half):

`k' = separableClosure k K` is by construction algebraic (indeed separable) over `k`
(`separableClosure.isAlgebraic`, `separableClosure.isSeparable`).  The remaining
content is that `k'` is *finite* over `k` when `K/k` is finitely generated as a
field.  In Mathlib, finite generation of the top intermediate field is exactly
essential finite type:

  `IntermediateField.fg_top_iff : (⊤ : IntermediateField k K).FG ↔ Algebra.EssFiniteType k K`.

Once we know `Algebra.EssFiniteType k k'`, the finisher is

  `Algebra.finite_of_essFiniteType_of_isAlgebraic`
    : `[EssFiniteType F E] [IsAlgebraic F E] → Module.Finite F E`,

applied with `F = k`, `E = k'` (`k'` is algebraic over `k`).

So the *only* real content is the sub-lemma `essFiniteType_separableClosure`:
from `Algebra.EssFiniteType k K` deduce `Algebra.EssFiniteType k k'`.
For an intermediate field this is, via `IntermediateField.essFiniteType_iff`,
the same as `(separableClosure k K).FG`.

Informal proof of `essFiniteType_separableClosure` (Stacks 037J transcendence-basis
argument): Since `K/k` is essentially of finite type, choose (via
`IntermediateField.exists_finset_maximalFor_isTranscendenceBasis_separableClosure`)
a finite set `s ⊆ K` which is a transcendence basis of `K/k` maximizing the
separable closure `separableClosure (k(s)) K` (as a subfield of `K`, restricted to
`k`).  Write `F₀ = k(s)`, a finitely generated *purely transcendental* extension of
`k`; `K/F₀` is algebraic and finitely generated as a field, hence finite-dimensional
once we pass to the separable-then-inseparable tower.  The maximality of `s`
guarantees that `K` is purely inseparable over the separable closure of `F₀` in `K`;
in particular the separable closure `separableClosure k K` is finite over `k`,
because separably algebraic elements of `K` over `k` are separably algebraic over
`F₀` and `F₀/k` is purely transcendental (so adds no separable algebraic elements),
and `K/F₀` has finite separable degree.  Concretely, `separableClosure k K` embeds
into `separableClosure F₀ K` which is finite over `F₀` (a finite separable extension
inside the f.g. algebraic part), and the transcendence degree being captured exactly
by `s` forces `separableClosure k K ⊆ adjoin k (finite set)`, giving `(separableClosure k K).FG`.
This is the analytic heart Stacks calls 037J, recorded here as a single named
sub-lemma. -/

-- KERNEL (Stacks 037J linear-disjointness heart): if `s` is a transcendence basis of
-- `K/k` and the separable closure of `F₀ = adjoin k s` in `K` is finite over `F₀`,
-- then `separableClosure k K` is finite over `k`.
--
-- INFORMAL PROOF:
--   Let `E := separableClosure F₀ K` (finite over `F₀` by hypothesis), `k' := separableClosure k
-- K`.
--   (1) `k' ≤ restrictScalars k E`: every `k`-separably-algebraic element of `K` is
--       `F₀`-separably-algebraic (`minpoly.dvd` over the larger base `F₀` +
--       `Polynomial.Separable.of_dvd`). Mathlib packages this as
--       `separableClosure.le_restrictScalars k F₀ K`.
--   (2) Degree bound `finrank k k' ≤ finrank F₀ E`: the LINEAR-DISJOINTNESS step.
--       `k'/k` is separable algebraic, `F₀/k` is purely transcendental (generated by
--       the algebraically independent `s`), so a `k`-basis of `k'` stays
--       `F₀`-linearly independent inside `K` (monomials in `s` are `M`-linearly
--       independent for `M/k` algebraic — the genuinely hard sub-fact `(LD)`). Hence
--       `finrank k k' = finrank F₀ (k'·F₀) ≤ finrank F₀ E < ∞`.
--   Relevant Mathlib API: `separableClosure.le_restrictScalars`, `separableClosure.isSeparable`,
--   `separableClosure.isAlgebraic`, `IntermediateField.LinearDisjoint` (+ `.finrank_sup` /
--   `.of_basis_mul`), `AlgebraicIndependent`/`IsTranscendenceBasis` API. The `(LD)` core
--   (alg. indep. over `k` is preserved over an algebraic extension `M`) is the obligation;
--   if no packaged lemma, eliminate the finitely many algebraic coefficients via their
--   minimal polynomials over `k`.
-- Auxiliary lemma (Stacks 037J linear-disjointness core, domain step):
-- if `k'/k` is any field extension and `ι` an index set, then
-- `k' ⊗[k] FractionRing (MvPolynomial ι k)` is a domain. Proved by recognizing the
-- tensor product as a localization of `MvPolynomial ι k' ≅ (MvPolynomial ι k) ⊗[k] k'`.
theorem finite_separableClosure_kernel_aux_domain
    (k : Type*) [Field k] (ι : Type*) (k' : Type*) [Field k'] [Algebra k k'] :
    IsDomain (TensorProduct k k' (FractionRing (MvPolynomial ι k))) := by
  let P := MvPolynomial ι k
  let B := FractionRing P
  let S := TensorProduct k P k'
  have hSdom : IsDomain S := by
    have e2 : TensorProduct k k' P ≃ₐ[k'] MvPolynomial ι k' := MvPolynomial.algebraTensorAlgEquiv k
        k'
    have : IsDomain (TensorProduct k k' P) := e2.toMulEquiv.isDomain (MvPolynomial ι k')
    have e1 : TensorProduct k P k' ≃ₐ[k] TensorProduct k k' P := Algebra.TensorProduct.comm k _ _
    exact e1.toMulEquiv.isDomain (TensorProduct k k' P)
  have hinj : Function.Injective (algebraMap P S) := FaithfulSMul.algebraMap_injective P S
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors P)) (TensorProduct P
      S B) :=
    IsLocalization.tensor B (nonZeroDivisors P)
  have hsub : Algebra.algebraMapSubmonoid S (nonZeroDivisors P) ≤ nonZeroDivisors S := by
    rintro x ⟨p, hp, rfl⟩
    have hp' : p ≠ 0 := by simpa [mem_nonZeroDivisors_iff_ne_zero] using hp
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact fun hh => hp' (hinj (by rw [hh]; simp))
  have hdom2 : IsDomain (TensorProduct P S B) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (TensorProduct P S B) hsub
  have ec : TensorProduct P B S ≃ₐ[B] TensorProduct k B k' :=
    Algebra.TensorProduct.cancelBaseChange k P B B k'
  have e0 : TensorProduct P S B ≃ₐ[P] TensorProduct P B S := Algebra.TensorProduct.comm P _ _
  have d1 : IsDomain (TensorProduct P B S) := e0.symm.toMulEquiv.isDomain (TensorProduct P S B)
  have d2 : IsDomain (TensorProduct k B k') := ec.symm.toMulEquiv.isDomain (TensorProduct P B S)
  have e2 : TensorProduct k B k' ≃ₐ[k] TensorProduct k k' B := Algebra.TensorProduct.comm k _ _
  exact e2.symm.toMulEquiv.isDomain (TensorProduct k B k')

/-- If `s` is a finite transcendence basis of `K/k` and the separable closure of
`F₀ = k(s)` in `K` is finite over `F₀`, then the separable closure of `k` in `K` is finite
over `k`. -/
theorem finite_separableClosure_kernel (k K : Type*) [Field k] [Field K] [Algebra k K]
    (s : Finset K) (htb : IsTranscendenceBasis k (fun x : (s : Set K) => (x : K)))
    (hfin : Module.Finite ↥(IntermediateField.adjoin k (s : Set K))
      ↥(separableClosure (↥(IntermediateField.adjoin k (s : Set K))) K)) :
    Module.Finite k ↥(separableClosure k K) := by
  set F₀ := IntermediateField.adjoin k (s : Set K) with hF₀def
  set k' := separableClosure k K with hk'def
  set E := separableClosure (↥F₀) K with hEdef
  -- Step (1): `k' ≤ restrictScalars k E` (separably algebraic over `k` ⟹ over `F₀`).
  have hstep1 : k' ≤ IntermediateField.restrictScalars k E :=
    separableClosure.le_restrictScalars k (↥F₀) K
  have halg : Algebra.IsAlgebraic k ↥k' := separableClosure.isAlgebraic k K
  -- Step (2), linear-disjointness core: `k'` (algebraic) and `F₀` (purely transcendental,
  -- `≅ FractionRing (MvPolynomial s k)`) are linearly disjoint over `k`. We prove it via
  -- `k' ⊗[k] F₀` being a field (domain + one side algebraic).
  have hld : k'.LinearDisjoint (↥F₀) := by
    have hai : AlgebraicIndependent k (fun x : (s : Set K) => (x : K)) := htb.left
    have hr : Set.range (fun x : (s : Set K) => (x : K)) = (s : Set K) := by ext y; simp
    have hadj : IntermediateField.adjoin k (Set.range (fun x : (s : Set K) => (x : K))) = F₀ := by
      rw [hF₀def, hr]
    have efield : FractionRing (MvPolynomial (s : Set K) k) ≃ₐ[k] ↥F₀ :=
      hai.aevalEquivField.trans (IntermediateField.equivOfEq hadj)
    have hdomFr : IsDomain (TensorProduct k ↥k' (FractionRing (MvPolynomial (s : Set K) k))) :=
      finite_separableClosure_kernel_aux_domain k (s : Set K) ↥k'
    have tcongr : TensorProduct k ↥k' (FractionRing (MvPolynomial (s : Set K) k)) ≃ₐ[k]
        TensorProduct k ↥k' ↥F₀ :=
      Algebra.TensorProduct.congr (AlgEquiv.refl) efield
    have hdomF₀ : IsDomain (TensorProduct k ↥k' ↥F₀) :=
      tcongr.symm.toMulEquiv.isDomain (TensorProduct k ↥k' (FractionRing (MvPolynomial (s : Set K)
          k)))
    have hisField : IsField (TensorProduct k ↥k' ↥F₀) :=
      Algebra.TensorProduct.isField_of_isAlgebraic k ↥k' ↥F₀ (Or.inl halg)
    exact IntermediateField.LinearDisjoint.of_isField hisField
  -- Degree transfer: `rank F₀ (F₀-adjoin k') = rank k k'` and `F₀-adjoin k' ≤ E`.
  have hrank : Module.rank (↥F₀) ↥(IntermediateField.adjoin (↥F₀) (↑k' : Set K)) = Module.rank k
      ↥k' :=
    hld.adjoin_rank_eq_rank_left_of_isAlgebraic_left
  have hle : IntermediateField.adjoin (↥F₀) (↑k' : Set K) ≤ E :=
    IntermediateField.adjoin_le_iff.mpr fun _ hx => hstep1 hx
  have : Module.Finite (↥F₀) ↥E := hfin
  have hle_rank : Module.rank (↥F₀) ↥(IntermediateField.adjoin (↥F₀) (↑k' : Set K)) ≤ Module.rank
      (↥F₀) ↥E :=
    LinearMap.rank_le_of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle)
  have hE_fin : Module.rank (↥F₀) ↥E < Cardinal.aleph0 := Module.rank_lt_aleph0_iff.mpr
      inferInstance
  have hkk'_fin : Module.rank k ↥k' < Cardinal.aleph0 := by
    rw [← hrank]
    exact hle_rank.trans_lt hE_fin
  exact Module.rank_lt_aleph0_iff.mp hkk'_fin

/-- `k' = separableClosure k K` is essentially of finite type over `k` whenever `K/k` is (i.e.
whenever the top intermediate field is finitely generated as a field). This is the Mathlib form
of Stacks 037J (the separable algebraic closure inside a finitely generated field extension is
finite over the base). -/
theorem essFiniteType_separableClosure (k K : Type*) [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] :
    Algebra.EssFiniteType k (separableClosure k K) := by
  -- Transcendence-basis scaffold (verified): pick a finite transcendence basis `s`
  -- maximizing the separable closure, set `F₀ = adjoin k s`; then `K/F₀` is finite,
  -- hence `separableClosure F₀ K` is finite over `F₀`. The remaining linear-disjointness
  -- content is isolated in `finite_separableClosure_kernel`.
  obtain ⟨s, hs⟩ :=
      IntermediateField.exists_finset_maximalFor_isTranscendenceBasis_separableClosure k K
  set F₀ := IntermediateField.adjoin k (s : Set K) with hF₀
  have htb : IsTranscendenceBasis k (fun x : (s : Set K) => (x : K)) := hs.left
  have h1 : Algebra.IsAlgebraic
      (↥(Algebra.adjoin k (Set.range (fun x : (s : Set K) => (x : K))))) K := htb.isAlgebraic
  have hr : Set.range (fun x : (s : Set K) => (x : K)) = (s : Set K) := by ext y; simp
  rw [hr] at h1
  have halg : Algebra.IsAlgebraic F₀ K := by
    constructor; intro x; rw [IntermediateField.isAlgebraic_adjoin_iff]; exact h1.isAlgebraic x
  have hEFT : Algebra.EssFiniteType F₀ K :=
    Algebra.EssFiniteType.of_comp k F₀ K
  have hfin : Module.Finite F₀ K :=
    @Algebra.finite_of_essFiniteType_of_isAlgebraic _ _ _ _ _ hEFT halg
  have hMfin : Module.Finite F₀ ↥(separableClosure F₀ K) := by
    have : FiniteDimensional F₀ K := hfin
    exact Module.Finite.of_injective
      (IsScalarTower.toAlgHom F₀ (separableClosure F₀ K) K).toLinearMap Subtype.val_injective
  have hkfin : Module.Finite k ↥(separableClosure k K) :=
    finite_separableClosure_kernel k K s htb hMfin
  infer_instance

/-- Statement 2 (Finiteness of `[k' : k]`). If `K/k` is a finitely generated field extension
(Definition 4 — finite generation as a field, encoded by `(⊤ : IntermediateField k K).FG`),
then `k'` is finite over `k`, i.e. `Module.Finite k k'` (equivalently `[k' : k] < ∞`). -/
@[stacks 037Q "(2)"]
theorem part2 (k K : Type*) [Field k] [Field K] [Algebra k K]
    (hfg : (⊤ : IntermediateField k K).FG) :
    Module.Finite k (separableClosure k K) := by
  -- Convert `hfg` to `EssFiniteType k K`.
  rw [IntermediateField.fg_top_iff] at hfg
  -- `k'` is essentially of finite type over `k` (Stacks 037J, sub-lemma).
  have hef : Algebra.EssFiniteType k (separableClosure k K) :=
    essFiniteType_separableClosure k K
  -- `k'` is algebraic over `k` by construction (`separableClosure.isAlgebraic`).
  -- Essentially-finite-type + algebraic ⇒ module-finite.
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

/-! ## Part 1 sub-lemmas (geometric irreducibility of `K` over `k'`)

The mathematical argument (Stacks 0G33 + 037K, second half of 037Q):

Set `k' = separableClosure k K`.  The defining property of `k'` is that it is
*separably algebraically closed in `K`*: every element of `K` separably algebraic
over `k'` already lies in `k'`.  In Mathlib this is the statement
`separableClosure (separableClosure k K) K = ⊥`, i.e.
`separableClosure.separableClosure_eq_bot` (applied to `F := k`, `E := K`).

By Stacks 0G33 / 037K, an extension `K/F` is geometrically irreducible exactly when
`F` is separably algebraically closed in `K`.  Concretely, for a field `F`,
`K/F` geometrically irreducible (Definition 3) ⟺ for every field extension `L/F`,
`Spec(K ⊗_F L)` is irreducible.

We reduce the topological statement to algebra.  For a commutative ring `A`,
`IrreducibleSpace (PrimeSpectrum A)` ⟺ `(nilradical A).IsPrime`
(`PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical`).  So `part1` becomes:
for every field `L/k'`, the nilradical of `K ⊗_{k'} L` is prime, equivalently
`(K ⊗_{k'} L) / nil` is an integral domain
(`Ideal.Quotient.isDomain_iff_prime`).

The content "the spectrum is irreducible because `k'` is separably closed in `K`"
is the analytic kernel.  The standard proof: it suffices to treat `L` an algebraic
closure of `k'` (by 037K reduction to finite separable / the algebraic closure),
and then `K ⊗_{k'} \bar{k'}` has a unique minimal prime because the geometric points
of `Spec(K)` over `k'` are not separated by any separable extension — precisely the
condition `separableClosure k' K = ⊥`.  Mathlib does not package this equivalence,
so we record the two genuine sub-lemmas:

  (P1a) `sepClosed_in_K`:  `separableClosure (separableClosure k K) K = ⊥`
        (this is exactly `separableClosure.separableClosure_eq_bot`; a *closable*
        leaf, kept as a named hypothesis-provider for the kernel below).

  (P1b) `geomIrred_of_sepClosed`:  the geometric-irreducibility kernel — for a field
        `F` that is separably closed in `K` (`separableClosure F K = ⊥`) and every
        field extension `L/F`, `Spec(K ⊗_F L)` is irreducible.  This is the
        unformalized Stacks 0G33/037K content and is the analytic heart of part1.
-/

-- (P1a) `k' = separableClosure k K` is separably algebraically closed inside `K`:
-- the separable closure of `k'` in `K` is trivial.
-- CLOSE HINT (verified to typecheck and close in isolation):
--   `exact separableClosure.separableClosure_eq_bot k K`
-- This is a direct one-liner from Mathlib; no further decomposition needed.
-- (P1b) Geometric-irreducibility kernel (Stacks 0G33 / 037K).  If a field `F` is
-- separably algebraically closed in a field extension `K` (i.e. `separableClosure
-- F K = ⊥`), then `K` is geometrically irreducible over `F`: for every field
-- extension `L/F` the spectrum `Spec(K ⊗_F L)` is irreducible.
--
-- INFORMAL PROOF (analytic kernel — NOT in Mathlib): Fix `L/F`.  Irreducibility of
-- `Spec(K ⊗_F L)` is, by `PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical`,
-- the statement that `nilradical (K ⊗_F L)` is prime, equivalently
-- `(K ⊗_F L)/nil` is a domain (`Ideal.Quotient.isDomain_iff_prime`); nonemptiness
-- (`Nonempty (PrimeSpectrum _)`) holds since `K ⊗_F L ≠ 0` (it is a nonzero
-- `L`-algebra, `L` a field, `K ≠ 0`).  By the Stacks 037K reduction it suffices to
-- prove this for `L = F^{sep}` a separable algebraic closure of `F` (the general
-- case follows since any `L` factors through, and base change along `F^{sep} → L`
-- of an irreducible spectrum stays irreducible when the source is geometrically
-- connected/irreducible).  For `L = F^{sep}`: the minimal primes of `K ⊗_F F^{sep}`
-- correspond to the `F`-embeddings of `F^{sep}` into `\bar{K}` up to the action that
-- fixes `K`; since `F` is separably closed in `K`, `F^{sep}` and `K` are linearly
-- disjoint over `F` in any common closure, so `K ⊗_F F^{sep}` has a unique minimal
-- prime — i.e. its reduction is a domain.  Linear disjointness here is precisely the
-- separable-closedness hypothesis `separableClosure F K = ⊥`.  This packages Stacks
-- 0G33 (geom. irred. ⟺ separably closed) together with 037K (reduction to the
-- separable closure).  Closing it formally requires building the
-- minimal-primes/linear-disjointness bridge that Mathlib currently lacks; the
-- relevant Mathlib primitives are `IntermediateField.LinearDisjoint.isDomain`,
-- `Algebra.TensorProduct.isField_of_isAlgebraic`, and the irreducibility
-- instance `PrimeSpectrum.irreducibleSpace` (`[IsDomain R]`).
--
-- FORMAL DECOMPOSITION (ring-level route).  We split the kernel into two
-- self-contained, NON-CIRCULAR sub-lemmas plus glue:
--
--   (B) `geomIrred_tensor_sep_isDomain` — the Stacks 0G33 algebraic core: if `F`
--       is separably closed in `K`, then `K ⊗[F] (SeparableClosure F)` is an
--       integral domain (linear disjointness of `K` and `F^sep` over `F`, via the
--       Galois-orbit / unique-minimal-prime analysis of separable base change).
--
--   (A) `geomIrred_descent` — the Stacks 037K topological descent: if the single
--       ring `K ⊗[F] (SeparableClosure F)` is a domain, then for EVERY field
--       extension `L/F` the spectrum `Spec(K ⊗[F] L)` is irreducible.  This packages
--       the reduction "test on the separable algebraic closure" together with the
--       purely-inseparable-Spec-homeomorphism + colimit/flat-base-change descent.
--
-- The glue is then a one-liner.  Note neither sub-lemma's STATEMENT mentions
-- `geomIrred_of_sepClosed` or the all-`L` irreducibility predicate as a hypothesis,
-- so the decomposition is acyclic.

-- (B) Stacks 0G33 algebraic core (NOT in Mathlib): `F` separably closed in `K`
-- ⟹ `K ⊗[F] F^sep` is a domain.  Proof idea (to be formalized): `F^sep/F` is
-- (separable) Galois (over the relative separable closure), `K ⊗[F] F^sep` is an
-- étale `K`-algebra, its minimal primes ↔ `Gal`-orbits of `F`-embeddings, and
-- `separableClosure F K = ⊥` forces a single orbit; étale ⟹ reduced ⟹ the unique
-- minimal prime gives a domain.  Relevant primitives:
-- `Algebra.TensorProduct.isField_of_isAlgebraic`, `IntermediateField.LinearDisjoint`,
-- `separableClosure.isSeparable`/`isPurelyInseparable`, Galois-orbit API.
-- ===========================================================================
-- FORMAL SKETCH of `geomIrred_tensor_sep_isDomain` (Stacks 0G33).
-- Informal proof, written against THIS goal `IsDomain (K ⊗[F] SeparableClosure F)` under
-- `separableClosure F K = ⊥`.  Four-step colimit-of-finite-separable argument.
-- We package the analytic content into three acyclic stub sub-lemmas (none of
-- which mentions `geomIrred_tensor_sep_isDomain`, `geomIrred_descent`,
-- `geomIrred_of_sepClosed` or the all-`L` irreducibility predicate, so the
-- decomposition is acyclic and strictly easier than the parent).
-- ===========================================================================

/-- (B3) Step 4 of the informal proof: a filtered/directed union of integral domains along
injective ring homomorphisms is an integral domain. Stated as the special case we need: if
every PAIR of elements of a commutative ring `R` lies in (the image of) some domain via a ring
hom — i.e. `R` is covered by a directed family of sub-domains — then `R` is a domain. We phrase
it as the `Ring.DirectLimit` of a directed system of domains with injective transitions.
Mathlib: `Ring.DirectLimit`, `Ring.DirectLimit.isDomain` style reasoning, or the elementary
two-element `NoZeroDivisors` argument on a directed `iSup` of subrings. The honest content is
purely the "directed union of domains is a domain" lemma; it does not use `hsc`. -/
@[ega "IV 5.13.3" "(i), special case"]
theorem directedUnion_subdomain_isDomain
    (R : Type*) [CommRing R] [Nontrivial R]
    (S : Set (Subalgebra ℕ R))
    -- `S` is a directed family of subrings, each an integral domain, covering `R`.
    (hdir : DirectedOn (· ≤ ·) S)
    (hcover : ∀ x : R, ∃ A ∈ S, x ∈ A)
    (hdom : ∀ A ∈ S, IsDomain A) :
    NoZeroDivisors R := by
  -- vacuity since Nontrivial R + hcover force S nonempty).
  -- Two-element argument: `a*b = 0`; pick `A ∈ S` containing both `a,b` (cover +
  -- directedness); `A` is a domain and the inclusion `A ↪ R` is a ring hom, so the
  -- equation holds in `A`, forcing `a = 0 ∨ b = 0`.
  refine ⟨fun {a b} hab => ?_⟩
  obtain ⟨A₁, hA₁, haA₁⟩ := hcover a
  obtain ⟨A₂, hA₂, hbA₂⟩ := hcover b
  obtain ⟨A, hA, hA₁A, hA₂A⟩ := hdir A₁ hA₁ A₂ hA₂
  have haA : a ∈ A := hA₁A haA₁
  have hbA : b ∈ A := hA₂A hbA₂
  have := hdom A hA
  set a' : ↥A := ⟨a, haA⟩ with ha'
  set b' : ↥A := ⟨b, hbA⟩ with hb'
  have hab' : a' * b' = 0 := by
    apply Subtype.ext
    push_cast
    simpa using hab
  rcases mul_eq_zero.mp hab' with h | h
  · left
    have : (a' : R) = 0 := by rw [h]; rfl
    simpa [ha'] using this
  · right
    have : (b' : R) = 0 := by rw [h]; rfl
    simpa [hb'] using this

-- (B1) THE HEART (Step 3 sub-claim of the informal proof): irreducibility of the
-- minimal polynomial is preserved under base change to `K`, when `F` is separably
-- closed in `K`.  For `α` separable-algebraic over `F`, the image in `K[X]` of
-- `minpoly F α` stays irreducible.  This is the ONLY place `hsc` is used.
-- Proof idea: a monic factor `g | (minpoly F α).map` over `K` splits over an
-- algebraic closure `K̄` into a subset of the (distinct, separable) roots; its
-- coefficients are signed elementary-symmetric functions of those roots, hence
-- lie in `K` AND are separable-algebraic over `F`, hence lie in
-- `separableClosure F K = ⊥ = F`; so `g` descends to `F[X]` (unique monic
-- division `Polynomial.modByMonic`) and divides `minpoly F α`, contradicting its
-- irreducibility.  Mathlib: `minpoly.irreducible`, `Polynomial.Separable.map`,
-- `Polynomial.eq_prod_roots_of_monic_of_splits`, `Multiset.esymm`,
-- `mem_separableClosure_iff`, `IntermediateField.mem_bot`, `Polynomial.modByMonic`.

-- Helper: a monic factor `f` of `(minpoly F α).map (algebraMap F K)` over `K` has all
-- of its coefficients separable algebraic over `F`.  Proof: pass to an algebraic
-- closure `Ω = AlgebraicClosure K` (with the canonical scalar tower `F → K → Ω`);
-- `f` splits there into linear factors whose roots are roots of the separable
-- polynomial `(minpoly F α)` mapped to `Ω`, hence separable over `F`, hence lie in
-- `separableClosure F Ω`.  The coefficients of `f` (as elementary symmetric functions
-- of those roots) therefore lie in the field `separableClosure F Ω`, i.e. are
-- separable over `F`; transferring back along the injection `K → Ω` (minpoly is
-- invariant under injective algebra maps) gives separability of `f.coeff n` over `F`.
private theorem coeff_isSeparable_of_factor
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    {E : Type*} [Field E] [Algebra F E] (α : E)
    (f : Polynomial K) (hfm : f.Monic) (hfd : f ∣ (minpoly F α).map (algebraMap F K))
    (hsα : (minpoly F α).Separable) (hα0 : minpoly F α ≠ 0) (n : ℕ) :
    IsSeparable F (f.coeff n) := by
  set Ω := AlgebraicClosure K
  set fΩ := f.map (algebraMap K Ω) with hfΩ
  have hfΩmonic : fΩ.Monic := hfm.map _
  have hsplit : fΩ.Splits := IsAlgClosed.splits fΩ
  have hpΩ : (minpoly F α).map (algebraMap F Ω)
      = ((minpoly F α).map (algebraMap F K)).map (algebraMap K Ω) := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq F K Ω]
  have hpΩne : (minpoly F α).map (algebraMap F Ω) ≠ 0 := by
    rw [hpΩ]
    exact (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective K Ω)).mpr
      ((Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective F K)).mpr hα0)
  have hfΩdvd : fΩ ∣ (minpoly F α).map (algebraMap F Ω) := by
    rw [hpΩ, hfΩ]; exact Polynomial.map_dvd _ hfd
  have hroots_mem : ∀ r ∈ fΩ.roots, r ∈ Set.range (algebraMap (separableClosure F Ω) Ω) := by
    intro r hr
    have hrp : r ∈ ((minpoly F α).map (algebraMap F Ω)).roots :=
      Multiset.mem_of_le (Polynomial.roots.le_of_dvd hpΩne hfΩdvd) hr
    rw [Polynomial.mem_roots hpΩne] at hrp
    have hev : (minpoly F α).map (algebraMap F Ω) |>.IsRoot r := hrp
    rw [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def] at hev
    have hsepr : IsSeparable F r := hsα.of_dvd (minpoly.dvd F r hev)
    exact ⟨⟨r, mem_separableClosure_iff.mpr hsepr⟩, rfl⟩
  have hlift : fΩ ∈ Polynomial.lifts (algebraMap (separableClosure F Ω) Ω) := by
    rw [Polynomial.Splits.eq_prod_roots_of_monic hsplit hfΩmonic]
    apply Subsemiring.multiset_prod_mem
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
    obtain ⟨s, hs⟩ := hroots_mem r hr
    rw [Polynomial.mem_lifts]
    refine ⟨(Polynomial.X : Polynomial (separableClosure F Ω)) - Polynomial.C s, ?_⟩
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hs]
  obtain ⟨c, hc⟩ := (Polynomial.lifts_iff_coeff_lifts fΩ).mp hlift n
  have hcfΩ : fΩ.coeff n = algebraMap K Ω (f.coeff n) := by rw [hfΩ, Polynomial.coeff_map]
  have hcsep : IsSeparable F (fΩ.coeff n) := by
    rw [← hc]
    have hcs : IsSeparable F c := Algebra.IsSeparable.isSeparable F c
    have hmap : minpoly F (algebraMap (separableClosure F Ω) Ω c) = minpoly F c :=
      minpoly.algebraMap_eq (FaithfulSMul.algebraMap_injective _ _) c
    unfold IsSeparable at hcs ⊢
    rwa [hmap]
  rw [hcfΩ] at hcsep
  have hmap2 : minpoly F (algebraMap K Ω (f.coeff n)) = minpoly F (f.coeff n) :=
    minpoly.algebraMap_eq (FaithfulSMul.algebraMap_injective K Ω) (f.coeff n)
  unfold IsSeparable at hcsep ⊢
  rwa [hmap2] at hcsep

/-- If the separable closure of `F` in `K` is trivial and `α` is separable and integral over
`F`, then the image of `minpoly F α` in `K[X]` remains irreducible. -/
theorem tensorSep_minpoly_irreducible (F K : Type*) [Field F] [Field K] [Algebra F K]
    (hsc : separableClosure F K = ⊥)
    {E : Type*} [Field E] [Algebra F E] (α : E)
    (hα : IsIntegral F α) (hsα : (minpoly F α).Separable) :
    Irreducible ((minpoly F α).map (algebraMap F K)) := by
  -- the separable-closedness hsc and separability hsα are both essential and used
  -- correctly; no counterexample — see search memory).
  set p := minpoly F α with hp
  have hpm : p.Monic := minpoly.monic hα
  have hpne : p ≠ 0 := hpm.ne_zero
  have hirr : Irreducible p := minpoly.irreducible hα
  have hpdeg : 0 < p.natDegree := hirr.natDegree_pos
  set pK := p.map (algebraMap F K) with hpK
  have hpKm : pK.Monic := hpm.map _
  have hpKdeg : pK.natDegree = p.natDegree := by rw [hpK]; exact hpm.natDegree_map _
  have hinjFK : Function.Injective (algebraMap F K) := FaithfulSMul.algebraMap_injective F K
  rw [Polynomial.Monic.irreducible_iff_natDegree hpKm]
  refine ⟨?_, ?_⟩
  · intro h1
    have : pK.natDegree = 0 := by rw [h1]; simp
    rw [hpKdeg] at this
    omega
  · intro g h hgm hhm hgh
    have hgdvd : g ∣ pK := ⟨h, hgh.symm⟩
    have hglift : g ∈ Polynomial.lifts (algebraMap F K) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      have hsep : IsSeparable F (g.coeff n) :=
        coeff_isSeparable_of_factor F K α g hgm (by rw [← hpK]; exact hgdvd)
          (by rw [← hp]; exact hsα) (by rw [← hp]; exact hpne) n
      have hmem : g.coeff n ∈ separableClosure F K := mem_separableClosure_iff.mpr hsep
      rw [hsc] at hmem
      exact IntermediateField.mem_bot.mp hmem
    obtain ⟨g₀, hg₀map, hg₀deg, hg₀mon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hglift hgm
    have hg₀dvd : g₀ ∣ p := by
      rw [← Polynomial.map_dvd_map (algebraMap F K) hinjFK hg₀mon, hg₀map, ← hpK]
      exact hgdvd
    obtain ⟨e, he⟩ := hg₀dvd
    rcases hirr.isUnit_or_isUnit he with hu | hu
    · left
      have hz : g₀.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
      omega
    · right
      have hez : e.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
      have hpdeg2 : p.natDegree = g₀.natDegree + e.natDegree := by
        rw [he]; exact Polynomial.natDegree_mul (hg₀mon.ne_zero)
          (by rintro rfl; simp only [mul_zero] at he; exact hpne (by rw [he]))
      have hghdeg : pK.natDegree = g.natDegree + h.natDegree := by
        rw [← hgh]; exact hgm.natDegree_mul hhm
      omega

open Polynomial in
/-- (B2) Step 3 conclusion of the informal proof: for a finite (separable) intermediate field `L`,
`K ⊗[F] L` is a FIELD. Via the primitive element theorem `L = F(α)`, `K ⊗[F] L ≅ K[X]/(minpoly
F α |_K)`, which is a field once the image of `minpoly F α` is irreducible over `K` (lemma B1).
In particular it is an integral domain. Mathlib: `Field.exists_primitive_element`,
`IntermediateField.adjoin.powerBasis`, `AdjoinRoot`,
`Algebra.TensorProduct.*`/`Polynomial.lTensorAlgEquiv`,
`PrincipalIdealRing.isMaximal_of_irreducible`, `Ideal.Quotient.field`. -/
@[ega "IV 4.3.2" "special case",
  ega "IV 4.3.6" "special case",
  ega "IV 4.3.7" "special case",
  ega "IV 6.7.4.1" "special case"]
theorem tensorSep_finite_isField (F K : Type*) [Field F] [Field K] [Algebra F K]
    (hsc : separableClosure F K = ⊥)
    (L : IntermediateField F (SeparableClosure F)) [FiniteDimensional F L] :
    IsField (K ⊗[F] L) := by
  -- element L=F(α), minpoly stays irreducible over K by tensorSep_minpoly_irreducible
  -- since F sep-closed in K; K[X]/(p_K) is a field as K[X] is a PID and p_K irreducible;
  -- hsc essential — without it ℚ(√2)⊗ℚ(√2)≅ℚ(√2)×ℚ(√2) is not a field; no counterexample).
  -- L/F is finite separable (L sits inside the separable closure of F).
  have hsep : Algebra.IsSeparable F L := IntermediateField.isSeparable_tower_bot F L
  -- Primitive element: choose a power basis of L with generator α.
  set pb : PowerBasis F L := Field.powerBasisOfFiniteOfSeparable F L with hpb
  set p : F[X] := minpoly F pb.gen with hp
  set pK : K[X] := p.map (algebraMap F K) with hpK
  have hp0 : p ≠ 0 := minpoly.ne_zero (IsIntegral.of_finite F pb.gen)
  -- The image of the minimal polynomial stays irreducible over K (lemma B1); this is
  -- the only place the separable-closedness hypothesis `hsc` enters.
  have hirr : Irreducible pK :=
    tensorSep_minpoly_irreducible F K hsc pb.gen (IsIntegral.of_finite F pb.gen)
      (Algebra.IsSeparable.isSeparable F pb.gen)
  have : Fact (Irreducible pK) := ⟨hirr⟩
  have hpKne : pK ≠ 0 := hirr.ne_zero
  have : FiniteDimensional K (AdjoinRoot pK) := (AdjoinRoot.powerBasis hpKne).finite
  -- `root pK` is a root of `p` (viewed over K), so we can lift `α ↦ root pK`.
  have hroot : (aeval (AdjoinRoot.root pK) (minpoly F pb.gen) : AdjoinRoot pK) = 0 := by
    rw [← hp, ← Polynomial.aeval_map_algebraMap K, ← hpK, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  set g : L →ₐ[F] AdjoinRoot pK := pb.lift (AdjoinRoot.root pK) hroot with hg
  -- The K-algebra map `K ⊗[F] L →ₐ[K] AdjoinRoot pK` sending `k ⊗ x ↦ k · g x`.
  set φ := Algebra.TensorProduct.lift (Algebra.ofId K (AdjoinRoot pK)) g
    (fun x y => Commute.all _ _) with hφ
  have hφgen : φ ((1 : K) ⊗ₜ[F] pb.gen) = AdjoinRoot.root pK := by
    rw [hφ, Algebra.TensorProduct.lift_tmul]; simp [hg, PowerBasis.lift_gen]
  -- φ is surjective: its range is a subalgebra containing `root pK`, which generates.
  have hsurj : Function.Surjective φ := by
    rw [← AlgHom.range_eq_top, eq_top_iff, ← AdjoinRoot.adjoinRoot_eq_top, Algebra.adjoin_le_iff]
    rintro x rfl
    exact ⟨(1 : K) ⊗ₜ[F] pb.gen, hφgen⟩
  -- Both sides are K-vector spaces of dimension `p.natDegree`, so φ is also injective.
  have hdimL : Module.finrank F L = p.natDegree := by
    rw [pb.finrank, hp, pb.natDegree_minpoly]
  have hdimT : Module.finrank K (K ⊗[F] L) = p.natDegree := by
    rw [Module.finrank_tensorProduct, Module.finrank_self, one_mul, hdimL]
  have hdimA : Module.finrank K (AdjoinRoot pK) = p.natDegree := by
    rw [(AdjoinRoot.powerBasis hpKne).finrank, AdjoinRoot.powerBasis_dim, hpK,
      Polynomial.natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective F K)]
  have hdimeq : Module.finrank K (K ⊗[F] L) = Module.finrank K (AdjoinRoot pK) := by
    rw [hdimT, hdimA]
  have hinj : Function.Injective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdimeq).mpr hsurj
  -- Hence `K ⊗[F] L ≃ₐ[K] AdjoinRoot pK`, a field; transport the field structure back.
  let e : (K ⊗[F] L) ≃ₐ[K] AdjoinRoot pK := AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩
  exact MulEquiv.isField (Field.toIsField (AdjoinRoot pK)) e.toMulEquiv

/-- Base change of an injective `F`-algebra map `ι : A → B` along a field extension `K / F` is
injective. -/
private theorem map_id_injective_of_injective (F K : Type*) [Field F] [Field K] [Algebra F K]
    {A B : Type*} [Field A] [Field B] [Algebra F A] [Algebra F B] (ι : A →ₐ[F] B)
    (hι : Function.Injective ι) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id K K) ι) :=
  Module.Flat.lTensor_preserves_injective_linearMap (R := F) (M := K) ι.toLinearMap hι

set_option synthInstance.maxHeartbeats 40000 in
-- needed: instance search in `geomIrred_tensor_sep_isDomain` (the directed-colimit
-- field/domain instances) exceeds the default instance-search budget
/-- (B) Stacks 0G33 algebraic core: assemble the colimit argument. `F^sep = ⋃ finite separable L`,
so `K ⊗[F] F^sep = ⋃ (K ⊗[F] L)` along injective (flatness of `K/F`, Step 2) transition maps;
each `K ⊗[F] L` is a field/domain (B2); a directed union of domains is a domain (B3). -/
@[ega "IV 4.3.2" "special case", ega "IV 6.7.4.1" "special case", sga "1 XIII 2.0.2" "special case"]
theorem geomIrred_tensor_sep_isDomain (F K : Type*) [Field F] [Field K] [Algebra F K]
    (hsc : separableClosure F K = ⊥) :
    IsDomain (K ⊗[F] (SeparableClosure F)) := by
  -- algebraic closure — excludes inseparable nilpotents, so étale ⟹ reduced and
  -- separableClosure F K = ⊥ forces a single Galois orbit / unique minimal prime).
  -- Assembly (informal Steps 1,2,4): `K ⊗[F] F^sep` is the directed union of the
  -- subrings `Im(K ⊗[F] L)` over finite separable `L ⊆ F^sep`; each is a field
  -- (B2 `tensorSep_finite_isField`); a directed union of domains is a domain (B3
  -- `directedUnion_subdomain_isDomain`).  Nontriviality: `K ⊗[F] F^sep ≠ 0`
  -- (base ring `F ≠ 0`, `Algebra.TensorProduct.nontrivial` / it contains `K`).
  set R := K ⊗[F] (SeparableClosure F) with hR
  -- For each intermediate field `L` of `F^sep/F`, the induced `K`-algebra map
  -- `φ L : K ⊗[F] L →ₐ[K] R = K ⊗[F] F^sep` (Step 1's transition/colimit maps).
  let φ : (L : IntermediateField F (SeparableClosure F)) → (K ⊗[F] L →ₐ[K] R) :=
    fun L => Algebra.TensorProduct.map (AlgHom.id K K) L.val
  -- Step 2: each `φ L` is injective (flatness/freeness of `K` over the field `F`).
  have hφinj : ∀ (L : IntermediateField F (SeparableClosure F)), Function.Injective (φ L) :=
    fun L => map_id_injective_of_injective F K L.val L.val.injective
  -- The transition maps are monotone on ranges: `L₁ ≤ L₂ ⟹ range (φ L₁) ≤ range (φ L₂)`.
  have hmono : ∀ (L₁ L₂ : IntermediateField F (SeparableClosure F)), L₁ ≤ L₂ →
      (φ L₁).range ≤ (φ L₂).range := by
    intro L₁ L₂ h
    have hfac : φ L₁ = (φ L₂).comp
        (Algebra.TensorProduct.map (AlgHom.id K K) (IntermediateField.inclusion h)) := by
      show Algebra.TensorProduct.map (AlgHom.id K K) (L₁.val) = _
      rw [← Algebra.TensorProduct.map_comp]; congr 1
    rw [hfac, AlgHom.range_comp]
    rintro x ⟨y, -, rfl⟩
    exact ⟨_, rfl⟩
  -- The directed family of `ℕ`-subalgebras realizing the colimit (Step 1).
  let S : Set (Subalgebra ℕ R) :=
    { A | ∃ L : IntermediateField F (SeparableClosure F),
        FiniteDimensional F L ∧ A = ((φ L).range).restrictScalars ℕ }
  -- Cover: every element of `R` lies in some `range (φ L)` with `L` finite (Step 1).
  have hcov : ∀ x : R, ∃ L : IntermediateField F (SeparableClosure F),
      FiniteDimensional F L ∧ x ∈ (φ L).range := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨⊥, inferInstance, Subalgebra.zero_mem _⟩
    | tmul k s =>
        refine ⟨IntermediateField.adjoin F {s}, ?_, ?_⟩
        · exact IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral s)
        · refine ⟨k ⊗ₜ[F] ⟨s, ?_⟩, ?_⟩
          · exact IntermediateField.subset_adjoin F {s} (Set.mem_singleton s)
          · show Algebra.TensorProduct.map (AlgHom.id K K) _ _ = _
            rw [Algebra.TensorProduct.map_tmul]; rfl
    | add a b ha hb =>
        obtain ⟨L₁, hL₁, haL₁⟩ := ha
        obtain ⟨L₂, hL₂, hbL₂⟩ := hb
        refine ⟨L₁ ⊔ L₂, IntermediateField.finiteDimensional_sup L₁ L₂, ?_⟩
        exact Subalgebra.add_mem _ (hmono L₁ (L₁ ⊔ L₂) le_sup_left haL₁)
          (hmono L₂ (L₁ ⊔ L₂) le_sup_right hbL₂)
  -- It suffices to show `R` is nontrivial (automatic) and has no zero divisors.
  -- Apply (B3) to the directed family `S`.
  have hnzd : NoZeroDivisors R := by
    refine directedUnion_subdomain_isDomain R S ?_ ?_ ?_
    · -- Directedness: for `A₁, A₂ ∈ S` (from `L₁, L₂`), use `L₁ ⊔ L₂`.
      rintro A₁ ⟨L₁, hL₁, rfl⟩ A₂ ⟨L₂, hL₂, rfl⟩
      refine ⟨((φ (L₁ ⊔ L₂)).range).restrictScalars ℕ,
        ⟨L₁ ⊔ L₂, IntermediateField.finiteDimensional_sup L₁ L₂, rfl⟩, ?_, ?_⟩
      · exact fun x hx => hmono L₁ (L₁ ⊔ L₂) le_sup_left hx
      · exact fun x hx => hmono L₂ (L₁ ⊔ L₂) le_sup_right hx
    · -- Cover.
      intro x
      obtain ⟨L, hL, hxL⟩ := hcov x
      exact ⟨((φ L).range).restrictScalars ℕ, ⟨L, hL, rfl⟩, hxL⟩
    · -- Each member is an integral domain: `range (φ L) ≃ₐ K ⊗[F] L`, a field (B2).
      rintro A ⟨L, hL, rfl⟩
      have hfield : IsField (K ⊗[F] L) := tensorSep_finite_isField F K hsc L
      let : Field (K ⊗[F] L) := hfield.toField
      have : IsDomain (K ⊗[F] L) := Field.isDomain
      let e : (K ⊗[F] L) ≃ₐ[K] (φ L).range := AlgEquiv.ofInjective (φ L) (hφinj L)
      have : IsDomain ((φ L).range) := e.symm.toMulEquiv.isDomain (K ⊗[F] L)
      exact (inferInstance : IsDomain ((φ L).range))
  exact NoZeroDivisors.to_isDomain R

-- ===========================================================================
-- (A) Stacks 037K all-L topological descent, for the descent statement.  Decomposed into two
-- acyclic sub-lemmas (this AND node):
--   (A-D) `tensorSep_algSep_isDomain`  — separable-algebraic descent of the DOMAIN
--         property: `K ⊗[F] Ls` is a domain for any separable-algebraic `Ls/F`,
--         because `Ls` embeds in `F^sep` and `K ⊗[F] (-)` is left-exact (flatness),
--         so `K ⊗[F] Ls ↪ K ⊗[F] F^sep` (a domain by `hdom`).
--   (A-G) `irreducibleSpace_tensor_of_algSep_domain` — the "geometrically pure"
--         descent: if `K ⊗[F] (separableClosure F L)` is a domain then
--         `Spec(K ⊗[F] L)` is irreducible.  Honest content (informal Steps 4a/4b):
--         `L / separableClosure F L` is transcendental ⊕ purely inseparable; the
--         transcendental part keeps the ring a domain (localized polynomial ring),
--         the purely-inseparable part is a Spec universal homeomorphism (Stacks
--         05K7/0BR8) so irreducibility (NOT integrality) is preserved.
-- The assembly below (verified glue) chains (A-D) then (A-G).
-- ===========================================================================

/-- (A-D) Separable-algebraic descent of the domain property. Proof (informal Lemma D): a
separable-algebraic `Ls/F` embeds `F`-linearly into a separable closure `Ω = SeparableClosure
F` (`IsSepClosed.lift`, since `Ω` is separably closed and `Ls/F` separable); base-change the
embedding along the flat (free) `F`-module `K` to get an injective ring map `K ⊗[F] Ls ↪ K ⊗[F]
Ω` (`Module.Flat.lTensor_preserves_injective_linearMap`). A subring of the domain `K ⊗[F] Ω`
(=`hdom`) is a domain. -/
theorem tensorSep_algSep_isDomain (F K : Type*) [Field F] [Field K] [Algebra F K]
    (hdom : IsDomain (K ⊗[F] (SeparableClosure F)))
    (Ls : Type) [Field Ls] [Algebra F Ls]
    [Algebra.IsSeparable F Ls] [Algebra.IsAlgebraic F Ls] :
    IsDomain (K ⊗[F] Ls) := by
  have : IsDomain (K ⊗[F] (SeparableClosure F)) := hdom
  -- Embed `Ls` into the separably closed field `SeparableClosure F`.
  let ι : Ls →ₐ[F] SeparableClosure F := IsSepClosed.lift
  have hιinj : Function.Injective ι := ι.injective
  -- Base-change `ι` along the flat (free) `F`-module `K`.
  let φ : K ⊗[F] Ls →ₐ[K] K ⊗[F] (SeparableClosure F) :=
    Algebra.TensorProduct.map (AlgHom.id K K) ι
  have hφinj : Function.Injective φ := map_id_injective_of_injective F K ι hιinj
  -- A subring of the domain `K ⊗[F] (SeparableClosure F)` is a domain.
  exact Function.Injective.isDomain φ.toRingHom hφinj
