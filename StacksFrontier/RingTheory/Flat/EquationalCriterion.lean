module
public import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.Topology.Sheaves.Init

/-!
# Flatness via maps from finitely presented modules

Let `M` be a module over a commutative ring `R`. This file gives three characterizations of the
flatness of `M` in terms of finitely presented modules.

The first is a factorization property: `M` is flat if and only if, for every finitely presented
`R`-module `P`, every `R`-linear map `f : P → M` factors as `f = g ∘ h` with `h : P → F` and
`g : F → M` for some free finite `R`-module `F`.

The second is a lifting property: `M` is flat if and only if, for every finitely presented
`R`-module `P` and every surjective `R`-linear map `φ : N → M`, the induced map
`Hom_R(P, N) → Hom_R(P, M)` given by postcomposition with `φ` is surjective. Equivalently, every
`R`-linear map from a finitely presented module to `M` lifts along every surjection onto `M`, so
that `M` is projective relative to the finitely presented modules.

The third is the equational criterion: `M` is flat if and only if every relation
`∑ i, f i • x i = 0` in `M` indexed by a finite type is trivial, that is, the elements `x i` are
`R`-linear combinations `x i = ∑ j, a i j • y j` of finitely many `y j : M` whose coefficients
satisfy `∑ i, f i * a i j = 0` for every `j`.

The third criterion is Mathlib's: `Module.IsTrivialRelation` and
`Module.Flat.iff_forall_isTrivialRelation`.

## Main results

* `Module.Flat.iff_exists_factorization_of_finitePresentation`: `M` is flat if and only if every
  `R`-linear map from a finitely presented `R`-module to `M` factors through a finite free module.
* `Module.Flat.iff_surjective_compRight_of_finitePresentation`: `M` is flat if and only if
  postcomposition `Hom_R(P, N) → Hom_R(P, M)` is surjective for every finitely presented `P` and
  every surjection `N → M`.

## Implementation notes

A free finite `R`-module is spelled `Fin k →₀ R`, as in
`Module.Flat.exists_factorization_of_finitePresentation`, rather than as an existentially
quantified type `F` carrying `[Module.Free R F] [Module.Finite R F]`. Every free finite module is
isomorphic to some `Fin k →₀ R`, so the two forms of the condition are equivalent, and this one
keeps `.mp` interchangeable with the Mathlib lemma and `.mpr` applicable without transporting along
a basis.

In `Module.Flat.iff_exists_factorization_of_finitePresentation` the module `P` ranges over
`Type u`, the universe of `R`, exactly as in `Module.flat_iff` and
`Module.Flat.iff_rTensor_injectiveₛ`; a universe-polymorphic `∀` cannot appear inside a `Prop`, so
some choice is forced here. The right-hand side at `Type u` is all the converse needs: from a
relation `x f = 0` in `M` with `f : Fin l →₀ R` one applies it to
`P = (Fin l →₀ R) ⧸ Submodule.span R {f}`, which is finitely presented and lies in `Type u`. The
condition for a `P` in an arbitrary universe is
`Module.Flat.exists_factorization_of_finitePresentation`, so that lemma and the present iff
together state Stacks 058E with no universe restriction. `P` is strict-implicit, as in
`Module.flat_iff`, so that it is determined by the map `f`.

The hypotheses are `[CommRing R] [AddCommGroup M] [Module R M]`; `Module.Flat` itself is defined
over a `CommSemiring`, but the conditions here are about kernels and quotients of free modules,
which is where the additive inverses are used.

The induced map of Stacks 058F is pinned as `LinearMap.compRight R φ`, postcomposition with `φ`,
whose underlying function is `fun g ↦ φ ∘ₗ g`; the scalar `R` is only the ring over which that map
is recorded as linear.

In `Module.Flat.iff_surjective_compRight_of_finitePresentation` the test modules `P` and `N` range
over a single universe `Type v`, the universe of `M`, and `R` is assumed `Small.{v}`, as in
`Module.Flat.iff_rTensor_exact'`. This is more general than the form with `P` and `N` in
`Type (max u v)`, which is the instance `v := max u v`, because `Small.{v} R` is automatic when
`v = max u v`, and in particular whenever `R` and `M` share a universe; the same relation holds
between `Module.Flat.iff_rTensor_exact` and `Module.Flat.iff_rTensor_exact'`. Smallness of `R`
makes `P : Type v` range over every finitely presented `R`-module up to isomorphism, since such a
module is a quotient of some `Fin n →₀ R` and is therefore `Small.{v}`, and it puts a free module
surjecting onto `M` inside `Type v`, namely a `Type v` copy of `M →₀ R`, which is what the converse
consumes. `N` is strict-implicit, being determined by `φ`, while `P` is explicit.

## References

* [StacksProject 00HK](https://stacks.math.columbia.edu/tag/00HK)
* [StacksProject 058E](https://stacks.math.columbia.edu/tag/058E)
* [StacksProject 058F](https://stacks.math.columbia.edu/tag/058F)

## Tags

flat module, finitely presented module, free module, factorization
-/

section

universe u v

namespace Stacks.Flatness.FactorizationCriterion

/-- The quotient of a module of finite presentation by a finitely generated submodule is again of
finite presentation. -/
private theorem finitePresentation_quotient {R : Type*} {M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [Module.FinitePresentation R M] (N : Submodule R M) (hN : N.FG) :
    Module.FinitePresentation R (M ⧸ N) :=
  Module.finitePresentation_of_surjective N.mkQ N.mkQ_surjective (by rwa [Submodule.ker_mkQ])

/-- Suppose every `R`-linear map into `M` from a finitely presented `R`-module in the universe of
`R` factors through a free finite `R`-module. Then such a factorization of `x : Q →ₗ[R] M` can be
chosen so that its first leg annihilates any finitely generated submodule `N` that `x` already
annihilates. -/
private theorem exists_factorization_of_le_ker {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    (H : ∀ ⦃P : Type u⦄ [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
      (f : P →ₗ[R] M), ∃ (k : ℕ) (h : P →ₗ[R] (Fin k →₀ R)) (g : (Fin k →₀ R) →ₗ[R] M), f = g ∘ₗ h)
    {Q : Type u} [AddCommGroup Q] [Module R Q] [Module.FinitePresentation R Q]
    {N : Submodule R Q} (hN : N.FG) {x : Q →ₗ[R] M} (hx : N ≤ LinearMap.ker x) :
    ∃ (k : ℕ) (a : Q →ₗ[R] (Fin k →₀ R)) (y : (Fin k →₀ R) →ₗ[R] M),
      x = y ∘ₗ a ∧ N ≤ LinearMap.ker a := by
  have := finitePresentation_quotient N hN
  obtain ⟨k, h, g, hgh⟩ := H (N.liftQ x hx)
  exact ⟨k, h ∘ₗ N.mkQ, g, by rw [← LinearMap.comp_assoc, ← hgh, Submodule.liftQ_mkQ],
    (Submodule.ker_mkQ N).ge.trans (LinearMap.ker_le_ker_comp N.mkQ h)⟩

/-- If every `R`-linear map into `M` from a finitely presented `R`-module in the universe of `R`
factors through a free finite `R`-module, then `M` is flat. -/
private theorem flat_of_forall_exists_factorization {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    (H : ∀ ⦃P : Type u⦄ [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
      (f : P →ₗ[R] M), ∃ (k : ℕ) (h : P →ₗ[R] (Fin k →₀ R)) (g : (Fin k →₀ R) →ₗ[R] M),
      f = g ∘ₗ h) :
    Module.Flat R M := by
  rw [Module.Flat.iff_forall_exists_factorization]
  intro l f x hx
  obtain ⟨k, a, y, hxy, ha⟩ := exists_factorization_of_le_ker H (Submodule.fg_span_singleton f)
    (x := x) ((Submodule.span_singleton_le_iff_mem f _).mpr hx)
  exact ⟨k, a, y, hxy, ha (Submodule.mem_span_singleton_self f)⟩

end Stacks.Flatness.FactorizationCriterion

@[expose] public section

open Stacks.Flatness.FactorizationCriterion in
/-- **Stacks 058E.** An `R`-module `M` is flat if and only if every `R`-linear map to `M` from a
finitely presented `R`-module `P` factors through a free finite `R`-module: there are `k : ℕ` and
maps `h : P → (Fin k →₀ R)` and `g : (Fin k →₀ R) → M` with `f = g ∘ h`. -/
@[stacks 058E]
public theorem Module.Flat.iff_exists_factorization_of_finitePresentation {R : Type u} {M : Type v}
    [CommRing R] [AddCommGroup M] [Module R M] :
    Module.Flat R M ↔ ∀ ⦃P : Type u⦄ [AddCommGroup P] [Module R P]
      [Module.FinitePresentation R P] (f : P →ₗ[R] M),
      ∃ (k : ℕ) (h : P →ₗ[R] (Fin k →₀ R)) (g : (Fin k →₀ R) →ₗ[R] M), f = g ∘ₗ h :=
  ⟨fun _ _ _ _ _ f => Module.Flat.exists_factorization_of_finitePresentation f,
    flat_of_forall_exists_factorization⟩
end

end

section

universe u v

namespace Stacks.Flatness.LiftingCriterion

/-- A finitely generated submodule of `α →₀ N` is supported on a finite set of coordinates. -/
private theorem le_supported_of_fg {R : Type*} [Semiring R] {N : Type*} [AddCommMonoid N]
    [Module R N] {α : Type*} {Q : Submodule R (α →₀ N)} (hQ : Q.FG) :
    ∃ s : Finset α, Q ≤ Finsupp.supported N R (s : Set α) := by
  classical
  obtain ⟨t, ht⟩ := hQ
  refine ⟨t.biUnion fun x => x.support, ?_⟩
  rw [← ht, Submodule.span_le]
  intro x hx a ha
  exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨x, hx, by simpa using ha⟩)

/-- A linear map from a finite module to a free module `α →₀ N` factors through a finite free
module `Fin k →₀ N`. -/
private theorem exists_factorization_finsupp_of_finite {R : Type*} [Semiring R] {N : Type*}
    [AddCommMonoid N] [Module R N] {P : Type*} [AddCommMonoid P] [Module R P] [Module.Finite R P]
    {α : Type*} (g : P →ₗ[R] (α →₀ N)) :
    ∃ (k : ℕ) (h : P →ₗ[R] (Fin k →₀ N)) (j : (Fin k →₀ N) →ₗ[R] (α →₀ N)), g = j ∘ₗ h := by
  have hfg : (LinearMap.range g).FG := by
    rw [LinearMap.range_eq_map]
    exact (Module.finite_def.mp ‹_›).map g
  obtain ⟨s, hs⟩ := le_supported_of_fg hfg
  set S : Submodule R (α →₀ N) := Finsupp.supported N R (s : Set α)
  let T : S ≃ₗ[R] (Fin (Fintype.card ((s : Set α) : Type _)) →₀ N) :=
    Finsupp.supportedEquivFinsupp (s : Set α) ≪≫ₗ Finsupp.domLCongr (Fintype.equivFin _)
  let g₀ : P →ₗ[R] S := LinearMap.codRestrict S g fun x => hs ⟨x, rfl⟩
  refine ⟨_, T.toLinearMap ∘ₗ g₀, S.subtype ∘ₗ T.symm.toLinearMap, ?_⟩
  ext x
  simp [g₀]

/-- If postcomposition with every surjection onto `M` is surjective on maps out of finitely
presented `R`-modules in `Type v`, then every map to `M` from a finitely presented `R`-module in
the universe of `R` lifts along the canonical surjection `(M →₀ R) →ₗ[R] M` from the free module on
`M`. -/
private theorem exists_lift_linearCombination {R : Type u} [CommRing R] [Small.{v} R] {M : Type v}
    [AddCommGroup M] [Module R M]
    (H : ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
      ⦃N : Type v⦄ [AddCommGroup N] [Module R N] (φ : N →ₗ[R] M), Function.Surjective φ →
      Function.Surjective (LinearMap.compRight (M := P) R φ))
    {P : Type u} [AddCommGroup P] [Module R P] [Module.FinitePresentation R P] (f : P →ₗ[R] M) :
    ∃ g : P →ₗ[R] (M →₀ R), Finsupp.linearCombination R id ∘ₗ g = f := by
  have : Small.{v} P := Module.Finite.small R P
  let eP : Shrink.{v} P ≃ₗ[R] P := Shrink.linearEquiv R P
  have : Module.FinitePresentation R (Shrink.{v} P) := .of_equiv eP.symm
  let eF : Shrink.{v} (M →₀ R) ≃ₗ[R] (M →₀ R) := Shrink.linearEquiv R (M →₀ R)
  have hψ : Function.Surjective (Finsupp.linearCombination R (id : M → M)) :=
    fun m => ⟨Finsupp.single m 1, by simp⟩
  obtain ⟨g, hg⟩ := H (Shrink.{v} P) (Finsupp.linearCombination R id ∘ₗ eF.toLinearMap)
    (hψ.comp eF.surjective) (f ∘ₗ eP.toLinearMap)
  refine ⟨eF.toLinearMap ∘ₗ g ∘ₗ eP.symm.toLinearMap, ?_⟩
  ext x
  simpa using LinearMap.congr_fun hg (eP.symm x)

end Stacks.Flatness.LiftingCriterion

@[expose] public section

open Stacks.Flatness.LiftingCriterion in
/-- **Stacks 058F.** An `R`-module `M` is flat if and only if for every finitely presented
`R`-module `P` and every surjection `φ : N → M` of `R`-modules the induced map
`Hom_R(P, N) → Hom_R(P, M)`, postcomposition with `φ`, is surjective. -/
@[stacks 058F]
public theorem Module.Flat.iff_surjective_compRight_of_finitePresentation {R : Type u} [CommRing R]
    [Small.{v} R] {M : Type v} [AddCommGroup M] [Module R M] :
    Module.Flat R M ↔
      ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
        ⦃N : Type v⦄ [AddCommGroup N] [Module R N] (φ : N →ₗ[R] M), Function.Surjective φ →
        Function.Surjective (LinearMap.compRight (M := P) R φ) := by
  constructor
  · intro hM P _ _ _ N _ _ φ hφ f
    obtain ⟨k, h₂, h₃, rfl⟩ := Module.Flat.exists_factorization_of_finitePresentation f
    obtain ⟨t, ht⟩ := Module.projective_lifting_property φ h₃ hφ
    exact ⟨t ∘ₗ h₂, by ext x; simp [← ht]⟩
  · intro H
    rw [Module.Flat.iff_exists_factorization_of_finitePresentation]
    intro P _ _ _ f
    obtain ⟨g, hg⟩ := exists_lift_linearCombination H f
    obtain ⟨k, h, j, hj⟩ := exists_factorization_finsupp_of_finite g
    exact ⟨k, h, Finsupp.linearCombination R id ∘ₗ j, by rw [← hg, hj, LinearMap.comp_assoc]⟩
end

end

@[expose] public section

/-! ### Stacks 00HK, the equational criterion for flatness

Stacks 00HK — `M` is flat iff every relation `∑ i, f i • x i = 0` in `M` is trivial, i.e. the
`x i` are `R`-linear combinations `x i = ∑ j, a i j • y j` of finitely many `y j : M` whose
coefficients satisfy `∑ i, f i * a i j = 0` — is Mathlib's `Module.IsTrivialRelation` together
with `Module.Flat.iff_forall_isTrivialRelation`.
-/

end
