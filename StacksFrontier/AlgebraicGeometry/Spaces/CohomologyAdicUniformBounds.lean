module

public import Mathlib.RingTheory.Filtration
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Abelian.InverseSystemModuleCat
public import StacksFrontier.RingTheory.Noetherian.ArtinRees

/-!
# Uniform bounds for the cohomology of the adic quotients of a coherent sheaf

Situation 08AV is the following standing data: a Noetherian ring `A`, an ideal `I ⊆ A`, a
proper morphism `f : X ⟶ Spec A` of algebraic spaces and a coherent `𝒪_X`-module `ℱ`.  Fix
`p ≥ 0` and write

* `M = H ᵖ (X, ℱ)`, an `A`-module;
* `Q n = H ᵖ (X, ℱ / I ⁿ ℱ)`, with transition maps `T m n : Q n ⟶ Q m` for `m ≤ n` and
  restriction maps `π n : M ⟶ Q n`;
* `Λ n = H ᵖ (X, I ⁿ ℱ)` with its maps `ι n : Λ n ⟶ M`, and
  `L n = H ᵖ⁺¹ (X, I ⁿ ℱ)` with its maps `U m n : L n ⟶ L m` for `m ≤ n`;
* `δ n : Q n ⟶ L n` for the connecting map of
  `0 ⟶ I ⁿ ℱ ⟶ ℱ ⟶ ℱ / I ⁿ ℱ ⟶ 0`.

[Stacks, Tag 08AY] has **three** clauses:

1. there is a `c ≥ 0` with `ker (π n) ⊆ I ^ (n - c) M` for all `n ≥ c`;
2. the inverse system `n ↦ Q n` satisfies the Mittag-Leffler condition of
   [Stacks, Tag 02N0];
3. for every `n` there is a `c₂ n ≥ n` with `im (T n k) = im (π n)` for all `k ≥ c₂ n`.

All three are proved below, from the inputs listed next.  The source deduces (2) from (3) in
one sentence, and that deduction is carried out here in the vocabulary of
[Stacks, Tag 02N0] itself.

## What is carried

The results here are about abstract towers of `A`-modules, so they take as hypotheses the facts
the source's proof uses about the situation, and prove the rest:

* `hexactM` and `hexact`: the two exactness assertions of the long exact sequence that the
  source invokes — `ker (π n) ⊆ im (ι n)` (exactness at `H ᵖ (X, ℱ)`) and
  `ker (δ n) ⊆ im (π n)` (exactness at `H ᵖ (X, ℱ / I ⁿ ℱ)`);
* `h08AX` and `h08AXconnecting`: clause (2) of [Stacks, Tag 08AX] for `H ᵖ` with `n = 0`, that
  `im (ι n) ⊆ I ^ (n - c) M` for `n ≥ c`, and for `H ᵖ⁺¹`, that
  `im (U n k) ⊆ I ^ (k - n - c) L n` for `k ≥ n + c`.  The single `c` is the source's
  `c₁ = max {c_p, c_{p+1}}`;
* `hfin`: finiteness of `L n` over `A` ([Stacks, Tag 08AS] together with the Noetherian
  hypothesis);
* `hann`: that `I ⁿ` annihilates `Q n`, which holds because `ℱ / I ⁿ ℱ` is a module over
  `𝒪_X / I ⁿ 𝒪_X`.

All of these inputs are proved for the cohomology of a coherent module on an algebraic space
proper over `Spec A` in the file `CohomologyAdicUniformBoundsSpace.lean` of
`StacksFrontier/AlgebraicGeometry/Spaces/GrothendieckExistence/HomBijection/`, which deduces
[Stacks, Tag 08AY] itself, unconditionally, from the results of this file.  The registrations
of 08AY are the declarations
`AlgebraicGeometry.Space.exists_ker_cohomologyIdealQuotientProj_le`,
`AlgebraicGeometry.Space.isMittagLefflerCategorical_cohomologyIdealQuotientTower` and
`AlgebraicGeometry.Space.exists_range_cohomologyIdealQuotientTr_eq` of
`StacksFrontier/AlgebraicGeometry/Spaces/CohomologyAdicUniformBoundsSpace.lean`.

Here the Artin–Rees step is
`Ideal.exists_pow_inf_eq_pow_smul` fed into `range_inf_smul_top_le_map_smul_top`, the
map form of [Stacks, Tag 00IO], and the Mittag-Leffler step is the subobject-to-range
dictionary `isMittagLefflerCategorical_of_range_eq_submodule`.

## Main results

* `Stacks.AdicCohomologyBound.ker_le_pow_smul_top` — the tower form of clause (1).
* `Stacks.AdicCohomologyBound.exists_range_transition_eq_range_proj` — the tower form of clause (3);
  this is the Artin–Rees argument of the source and the only substantial proof in the file.
* `Stacks.AdicCohomologyBound.exists_range_transition_stable` — clause (2) in its elementary
  form, the stabilization of the images of the transition maps, deduced from clause (3).
* `Stacks.AdicCohomologyBound.isMittagLefflerCategorical_of_exists_range_eq_range_proj` —
  clause (2) in the form of [Stacks, Tag 02N0]'s own definition
  `IsMittagLefflerCategorical`, for a tower presented as a functor `ℕᵒᵖ ⥤ ModuleCat A`,
  deduced from clause (3).

## Implementation notes

**The threshold in clause (3) grows with `n`, and cannot be made uniform.**  The source's
constant is `c₂ n = c₃ n + c₁ + n`, where `c₃ n` is the Artin–Rees constant of the submodule
`im (δ n) ⊆ L n`; the proof below produces `c₂ n = 2 * n + c + c₃ n`.  Two separate reasons
forbid replacing the per-`n` existential by a single shift `c` with threshold `n + c`: the
Artin–Rees constant `c₃ n` is attached to a submodule of the varying module `L n` and is not
bounded in `n` by anything 08AY supplies, and even for a constant `c₃` the step "`I ^ (N - c₃)`
annihilates `Q n`" needs `N - c₃ ≥ n`, which costs a second `n`.  So clause (3) is stated with
the existential, exactly as the source states it.

**Why the cohomology groups are data.**  `Q`, `Λ` and `L` are arbitrary families of
`A`-modules rather than the cohomology of the adic quotients of a coherent module, so that the
algebra of the source's argument is separated from the geometry that supplies its inputs; the
geometric inputs are supplied in `CohomologyAdicUniformBoundsSpace.lean`.

**The clause (2) statement is over `ModuleCat`.**  `IsMittagLefflerCategorical` is a statement
about the subobject lattices of an inverse system in an abelian category, so its subject is a
functor `ℕᵒᵖ ⥤ ModuleCat A`; the translation to `LinearMap.range` is
`subobjectModule_transitionImage`.  The elementary form
`exists_range_transition_stable` is stated for a bare tower so that it can be used without
packaging the tower as a functor.

## References

* [Stacks Project, Tag 08AY](https://stacks.math.columbia.edu/tag/08AY)
* [Stacks Project, Tag 08AV](https://stacks.math.columbia.edu/tag/08AV)
* [Stacks Project, Tag 08AX](https://stacks.math.columbia.edu/tag/08AX)
* [Stacks Project, Tag 08AS](https://stacks.math.columbia.edu/tag/08AS)
* [Stacks Project, Tag 02N0](https://stacks.math.columbia.edu/tag/02N0)
* [Stacks Project, Tag 00IO](https://stacks.math.columbia.edu/tag/00IO)
* [Stacks Project, Tag 08AZ](https://stacks.math.columbia.edu/tag/08AZ)
-/

@[expose] public section

open CategoryTheory Opposite

universe u v w

namespace Stacks.AdicCohomologyBound

section Tower

variable {A : Type*} [CommRing A] (I : Ideal A) {M : Type*} [AddCommGroup M] [Module A M]

/-- **The abstract-tower form of clause (1) of [Stacks, Tag 08AY].**  For the statement itself,
unconditional, see `AlgebraicGeometry.Space.exists_ker_cohomologyIdealQuotientProj_le`.

In Situation 08AV, for a fixed `p` there is a `c` with
`ker (H ᵖ (X, ℱ) ⟶ H ᵖ (X, ℱ / I ⁿ ℱ)) ⊆ I ^ (n - c) H ᵖ (X, ℱ)` for all `n ≥ c`.

The source's proof is two steps.  The long exact sequence of
`0 ⟶ I ⁿ ℱ ⟶ ℱ ⟶ ℱ / I ⁿ ℱ ⟶ 0` identifies that kernel with the image of
`H ᵖ (X, I ⁿ ℱ) ⟶ H ᵖ (X, ℱ)`, which is the hypothesis `hexactM` here; and clause (2) of
[Stacks, Tag 08AX], taken at `n = 0`, bounds that image by `I ^ (n - c) H ᵖ (X, ℱ)`, which is
the hypothesis `h08AX`.  Only the containment `ker (π n) ⊆ im (ι n)` is needed, not the
equality the source writes. -/
theorem ker_le_pow_smul_top {Λ : ℕ → Type*} [∀ n, AddCommGroup (Λ n)] [∀ n, Module A (Λ n)]
    {Q : ℕ → Type*} [∀ n, AddCommGroup (Q n)] [∀ n, Module A (Q n)]
    (ι : ∀ n, Λ n →ₗ[A] M) (π : ∀ n, M →ₗ[A] Q n) (c : ℕ)
    (hexactM : ∀ n, LinearMap.ker (π n) ≤ LinearMap.range (ι n))
    (h08AX : ∀ n, c ≤ n → LinearMap.range (ι n) ≤ I ^ (n - c) • (⊤ : Submodule A M)) :
    ∀ n, c ≤ n → LinearMap.ker (π n) ≤ I ^ (n - c) • (⊤ : Submodule A M) :=
  fun n hn => (hexactM n).trans (h08AX n hn)

/-- **The abstract-tower form of clause (3) of [Stacks, Tag 08AY].**  For the statement itself,
unconditional, see `AlgebraicGeometry.Space.exists_range_cohomologyIdealQuotientTr_eq`.

In Situation 08AV, for a fixed `p` and a fixed `n` there is a `c₂ ≥ n` with
`im (H ᵖ (X, ℱ / I ᵏ ℱ) ⟶ H ᵖ (X, ℱ / I ⁿ ℱ)) = im (H ᵖ (X, ℱ) ⟶ H ᵖ (X, ℱ / I ⁿ ℱ))`
for all `k ≥ c₂`.

The containment of the image of `π n` in the image of `T n k` is the compatibility `hπ` of the
restriction maps with the transitions.  For the other containment, the source's argument runs
as follows.  Let `x = T n k y`.  The ladder of long exact sequences gives
`δ n x = U n k (δ k y)`, so `δ n x` lies in the image of `U n k`, which clause (2) of
[Stacks, Tag 08AX] for `H ᵖ⁺¹` bounds by `I ^ N L n` with `N = k - n - c`.  Artin–Rees for the
submodule `im (δ n) ⊆ L n` produces a constant `c₃` with
`im (δ n) ⊓ I ^ N L n ⊆ δ n (I ^ (N - c₃) Q n)` for `N ≥ c₃`; and `I ⁿ` annihilates `Q n`, so
once `N - c₃ ≥ n` that target submodule is zero.  Hence `δ n x = 0`, and exactness at
`H ᵖ (X, ℱ / I ⁿ ℱ)` puts `x` in the image of `π n`.  The threshold produced is
`c₂ = 2 * n + c + c₃`; see this file's implementation notes for why it cannot be brought down
to `n + c` for a single `c`. -/
theorem exists_range_transition_eq_range_proj [IsNoetherianRing A]
    {Q : ℕ → Type*} [∀ n, AddCommGroup (Q n)] [∀ n, Module A (Q n)]
    {L : ℕ → Type*} [∀ n, AddCommGroup (L n)] [∀ n, Module A (L n)]
    (π : ∀ n, M →ₗ[A] Q n) (T : ∀ m n : ℕ, m ≤ n → Q n →ₗ[A] Q m)
    (δ : ∀ n, Q n →ₗ[A] L n) (U : ∀ m n : ℕ, m ≤ n → L n →ₗ[A] L m) (c : ℕ)
    (hfin : ∀ n, Module.Finite A (L n))
    (hπ : ∀ (m n : ℕ) (h : m ≤ n), (T m n h).comp (π n) = π m)
    (hladder : ∀ (m n : ℕ) (h : m ≤ n), (δ m).comp (T m n h) = (U m n h).comp (δ n))
    (hexact : ∀ n, LinearMap.ker (δ n) ≤ LinearMap.range (π n))
    (hann : ∀ n, I ^ n • (⊤ : Submodule A (Q n)) = ⊥)
    (h08AXconnecting : ∀ (n k : ℕ) (h : n ≤ k), n + c ≤ k →
      LinearMap.range (U n k h) ≤ I ^ (k - n - c) • (⊤ : Submodule A (L n)))
    (n : ℕ) :
    ∃ c₂ : ℕ, n ≤ c₂ ∧ ∀ (k : ℕ) (h : n ≤ k), c₂ ≤ k →
      LinearMap.range (T n k h) = LinearMap.range (π n) := by
  have := hfin n
  obtain ⟨c₃, hc₃⟩ := Ideal.exists_pow_inf_eq_pow_smul (M := L n) I (LinearMap.range (δ n))
  refine ⟨2 * n + c + c₃, by omega, fun k h hk => le_antisymm ?_ ?_⟩
  · rintro x ⟨y, rfl⟩
    have hcomm : (δ n) ((T n k h) y) = (U n k h) ((δ k) y) := by
      simpa using LinearMap.congr_fun (hladder n k h) y
    have hmem : (δ n) ((T n k h) y) ∈
        LinearMap.range (δ n) ⊓ I ^ (k - n - c) • (⊤ : Submodule A (L n)) := by
      refine Submodule.mem_inf.2 ⟨⟨_, rfl⟩, ?_⟩
      rw [hcomm]
      exact h08AXconnecting n k h (by omega) ⟨_, rfl⟩
    have hbot : I ^ (k - n - c - c₃) • (⊤ : Submodule A (Q n)) = ⊥ :=
      le_antisymm (le_trans (Submodule.smul_mono (Ideal.pow_le_pow_right (by omega)) le_rfl)
        (hann n).le) bot_le
    have hzero : (δ n) ((T n k h) y) = 0 := by
      have hmap := range_inf_smul_top_le_map_smul_top (δ n) I c₃ (k - n - c)
        (hc₃ (k - n - c) (by omega)) hmem
      rwa [hbot, Submodule.map_bot, Submodule.mem_bot] at hmap
    exact hexact n (LinearMap.mem_ker.2 hzero)
  · rintro x ⟨z, rfl⟩
    exact ⟨(π k) z, by simpa using LinearMap.congr_fun (hπ n k h) z⟩

/-- **Clause (2) of [Stacks, Tag 08AY], in elementary form, for an abstract tower.**

"Part (3) implies part (2) by definition of the Mittag-Leffler condition": once the image of
`T n k` equals the image of `π n` for all `k ≥ c₂`, those images are in particular all equal
to one another, which is the stabilization asserted by [Stacks, Tag 02N0].  The hypothesis
here is precisely the conclusion of `exists_range_transition_eq_range_proj`. -/
theorem exists_range_transition_stable {Q : ℕ → Type*} [∀ n, AddCommGroup (Q n)]
    [∀ n, Module A (Q n)] (π : ∀ n, M →ₗ[A] Q n) (T : ∀ m n : ℕ, m ≤ n → Q n →ₗ[A] Q m)
    (h : ∀ n : ℕ, ∃ c₂ : ℕ, n ≤ c₂ ∧ ∀ (k : ℕ) (hnk : n ≤ k), c₂ ≤ k →
      LinearMap.range (T n k hnk) = LinearMap.range (π n))
    (n : ℕ) :
    ∃ c₂ : ℕ, ∃ hnc₂ : n ≤ c₂, ∀ (k : ℕ) (hnk : n ≤ k), c₂ ≤ k →
      LinearMap.range (T n k hnk) = LinearMap.range (T n c₂ hnc₂) := by
  obtain ⟨c₂, hnc₂, hr⟩ := h n
  exact ⟨c₂, hnc₂, fun k hnk hk => (hr k hnk hk).trans (hr c₂ hnc₂ le_rfl).symm⟩

end Tower

section Categorical

/-- **Clause (2) of [Stacks, Tag 08AY] for an abstract tower, in the vocabulary of
[Stacks, Tag 02N0].**  For the statement itself, unconditional, see
`AlgebraicGeometry.Space.isMittagLefflerCategorical_cohomologyIdealQuotientTower`.

For the tower `n ↦ H ᵖ (X, ℱ / I ⁿ ℱ)` presented as an inverse system of `A`-modules, that is
a functor `F : ℕᵒᵖ ⥤ ModuleCat A`, clause (3) of [Stacks, Tag 08AY] says that the images of
the transition maps into `F.obj (op n)` are eventually the image of `π n`; so they stabilize,
which is the Mittag-Leffler condition `IsMittagLefflerCategorical` of [Stacks, Tag 02N0].  The
passage from ranges of linear maps to the transition subobjects that the definition speaks of
is the dictionary `isMittagLefflerCategorical_of_range_eq_submodule`. -/
theorem isMittagLefflerCategorical_of_exists_range_eq_range_proj {A : Type u} [Ring A]
    {M : Type w} [AddCommGroup M] [Module A M] (F : ℕᵒᵖ ⥤ ModuleCat.{v} A)
    (π : ∀ n : ℕ, M →ₗ[A] F.obj (op n))
    (h : ∀ n : ℕ, ∃ c₂ : ℕ, n ≤ c₂ ∧ ∀ (k : ℕ) (hnk : n ≤ k), c₂ ≤ k →
      LinearMap.range (F.map (homOfLE hnk).op).hom = LinearMap.range (π n)) :
    IsMittagLefflerCategorical F := by
  choose b hb hbr using h
  exact isMittagLefflerCategorical_of_range_eq_submodule F b hb
    (fun n => LinearMap.range (π n)) fun i k hbk hik => hbr i k hik hbk

end Categorical

end Stacks.AdicCohomologyBound

end
