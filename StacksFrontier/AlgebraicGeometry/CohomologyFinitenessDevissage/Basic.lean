module

public import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.Symmetry
public import StacksFrontier.AlgebraicGeometry.EulerCharVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs

/-!
# The finiteness floor of [Stacks, Tag 02O6], propagated and reduced to two sheaves

[Stacks, Tag 02O6] over a field is the statement that `Hⁿ(X, ℱ)` is a finite-dimensional
`k`-vector space for `X` proper over `k` and `ℱ` coherent. It is not in the library, and the
Euler-characteristic development of `StacksDraft/AlgebraicGeometry/F3b/` carries it as an
explicit hypothesis. This file does three things to that hypothesis, none of which needs an
input the library lacks.

**The bound is free above the vanishing degree.** `exists_isZero_cohomologyOverField_of_isProper`
produces, for `X` proper over `k`, a single degree `N` beyond which the cohomology of every
quasi-coherent module vanishes, and a vanishing vector space is finite-dimensional. So for a
proper `f` the hypothesis `∀ n, FiniteDimensional k (Hⁿ(X, ℱ))` and the hypothesis
`∀ n < N, FiniteDimensional k (Hⁿ(X, ℱ))` are *the same hypothesis*: the floor bites only in
the finitely many degrees below the affine-cover bound, and the degrees at or above it are
proved here outright.

**The property propagates in all three positions of a short exact sequence.**
`AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_shortExact` already propagates it
from the two outer terms to the middle one. The long exact sequence of
`AlgebraicGeometry.exists_cohomologyOverField_longExactSequence` propagates it in the other two
positions as well — `Hⁿ(X, ℱ₃)` sits between `Hⁿ(X, ℱ₂)` and `Hⁿ⁺¹(X, ℱ₁)`, and `Hⁿ⁺¹(X, ℱ₁)`
between `Hⁿ(X, ℱ₃)` and `Hⁿ⁺¹(X, ℱ₂)`, with `H⁰(X, ℱ₁) ↪ H⁰(X, ℱ₂)` closing the base degree.
All three are unconditional: no hypothesis on `f`, on the modules, or on coherence.

**Hence the floor is a statement about two sheaves, not about all coherent sheaves.** The
three-way propagation is exactly the two-out-of-three obligation that the dévissage of
[Stacks, Tag 01YH] imposes on a property of coherent modules, in the shape
`AlgebraicGeometry.exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add`
carries it. Discharging that obligation leaves the dévissage's two base cases, so
[Stacks, Tag 02O6] for *every* coherent module on `X` — and in particular for the finite locally
free module `ℰ` at which the Euler-characteristic development needs it — follows from
[Stacks, Tag 02O6] at the structure sheaf `𝒪_X` together with [Stacks, Tag 02O6] at the coherent
modules whose support is a proper closed subset.

## Main results

* `AlgebraicGeometry.exists_forall_finiteDimensional_cohomologyOverField_of_le_of_isProper`:
  **unconditional.** For `X` proper over `k` there is a degree `N` such that `Hⁿ(X, ℱ)` is
  finite-dimensional for every quasi-coherent `ℱ` and every `n ≥ N`.
* `AlgebraicGeometry.exists_forall_finiteDimensional_cohomologyOverField_of_forall_lt_of_isProper`
  : the same, read as a bridge — below `N` the hypothesis is the whole of [Stacks, Tag 02O6],
  at or above `N` there is nothing left to assume.
* `AlgebraicGeometry.finiteDimensional_cohomologyOverField_three_of_shortExact`: `Hⁿ(X, ℱ₃)` is
  finite-dimensional as soon as `Hⁿ(X, ℱ₂)` and `Hⁿ⁺¹(X, ℱ₁)` are.
* `AlgebraicGeometry.finiteDimensional_cohomologyOverField_one_of_shortExact_zero` and
  `…_one_of_shortExact_succ`: `Hⁿ(X, ℱ₁)` is finite-dimensional as soon as `Hⁿ(X, ℱ₂)` and
  `Hⁿ⁻¹(X, ℱ₃)` are, the degree `0` case using the injectivity of `H⁰(X, ℱ₁) ⟶ H⁰(X, ℱ₂)`.
* `AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_twoOutOfThree`: the three
  together, in the two-out-of-three shape a dévissage consumes. **Unconditional.**
* `AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_devissage`:
  [Stacks, Tag 02O6] for every coherent module, from the dévissage of [Stacks, Tag 01YH] and its
  two base cases.
* `…forall_finiteDimensional_cohomologyOverField_of_isFiniteLocallyFreeOfRank_of_devissage`:
  the same conclusion at a finite locally free module on a curve, which is the form the
  dévissage statements of `StacksDraft/AlgebraicGeometry/F3b/CurveTensorEuler/` need. The
  elided prefix is `AlgebraicGeometry`, as in the bullets above.

## Implementation notes

**No `@[stacks 02O6]` attribute is attached to anything here, and this file does not prove
[Stacks, Tag 02O6].** The tag asserts finite dimensionality with no hypothesis beyond properness
of `f`, Noetherianness of the base and coherence of `ℱ`. What is proved unconditionally below is
the propagation of that property and its triviality above the vanishing bound; the two theorems
that reach the tag's conclusion carry the dévissage of [Stacks, Tag 01YH] and the property at
the two base sheaves as explicit hypotheses. By the covering-set rule the tag belongs on none of
them.

**What remains, precisely.** After this file the floor under the Euler-characteristic
development is two statements and the dévissage, instead of one statement quantified over all
coherent modules:

* `∀ n, FiniteDimensional k (Hⁿ(X, 𝒪_X))` — the structure sheaf;
* `∀ n, FiniteDimensional k (Hⁿ(X, 𝒢))` for `𝒢` coherent with `supp 𝒢` a proper closed subset.

On a curve the second is a statement about a module with zero-dimensional support
(`AlgebraicGeometry.topologicalKrullDim_le_zero_of_isClosed_of_ne_univ`), and the natural route
to it — the closed subscheme carrying the support is finite over `k`, and
`AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_isFinite` then applies — needs the
comparison `Hⁿ(X, i_* 𝒢) ≅ Hⁿ(Z, 𝒢)` along a closed immersion, which this repository does not
have: `StacksDraft/AlgebraicGeometry/F3b/ClosedPushforward/` proves that the pushforward is
fully faithful and preserves coherence, and says nothing about cohomology.

**Why the two new propagation lemmas are stated pointwise and in shifted degrees.** The long
exact sequence relates `Hⁿ` of one term to `Hⁿ⁺¹` of another, so the hypotheses cannot be taken
in a single degree; stating them pointwise with the shift explicit keeps them usable where only
a range of degrees is known, and the quantified two-out-of-three form is assembled from them.

**The two linear-algebra inputs are the ones already in
`StacksFrontier/AlgebraicGeometry/EulerCharAdditivity/TwoOutOfThree.lean`**, made public there
rather than restated here, so that the four propagation statements share one proof of
"finite-dimensional across an exact sequence" and one proof of "a vanishing space is
finite-dimensional".

## References

* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 01YH](https://stacks.math.columbia.edu/tag/01YH)
* [Stacks Project, Tag 01XI](https://stacks.math.columbia.edu/tag/01XI)
* [Stacks Project, Tag 08AA](https://stacks.math.columbia.edu/tag/08AA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

universe u

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-! ### Above the vanishing bound there is nothing to assume -/

/-- **Finite dimensionality of cohomology in high degrees, unconditionally.** For `X` proper
over a field `k` there is a single degree `N` beyond which `Hⁿ(X, ℱ)` is a finite-dimensional
`k`-vector space for *every* quasi-coherent `ℱ`, because beyond that degree it vanishes.

The bound is the one produced by `exists_isZero_cohomologyOverField_of_isProper`, namely the
size of an affine open cover of `X`, and like it does not depend on the module. -/
theorem exists_forall_finiteDimensional_cohomologyOverField_of_le_of_isProper [IsProper f] :
    ∃ N : ℕ, ∀ G : X.Modules, G.IsQuasicoherent →
      ∀ n : ℕ, N ≤ n → FiniteDimensional k (cohomologyOverField k f G n) := by
  obtain ⟨N, hN⟩ := exists_isZero_cohomologyOverField_of_isProper k f
  exact ⟨N, fun G hG n hn => finiteDimensional_of_isZero k (hN G hG n hn)⟩

/-- **The [Stacks, Tag 02O6] hypothesis is a hypothesis about finitely many degrees.** For `X`
proper over a field there is a degree `N` such that assuming finite dimensionality of `Hⁿ(X, ℱ)`
for `n < N` gives it in every degree. So the restricted form of the hypothesis carried by
`AlgebraicGeometry.eulerCharacteristic_add_of_shortExact_of_outer` is not a weakening of the
unrestricted one: for a proper morphism the two are equivalent. -/
theorem exists_forall_finiteDimensional_cohomologyOverField_of_forall_lt_of_isProper
    [IsProper f] :
    ∃ N : ℕ, ∀ G : X.Modules, G.IsQuasicoherent →
      (∀ n < N, FiniteDimensional k (cohomologyOverField k f G n)) →
        ∀ n : ℕ, FiniteDimensional k (cohomologyOverField k f G n) := by
  obtain ⟨N, hN⟩ := exists_forall_finiteDimensional_cohomologyOverField_of_le_of_isProper k f
  refine ⟨N, fun G hG h n => ?_⟩
  by_cases hn : n < N
  · exact h n hn
  · exact hN G hG n (by omega)

/-! ### Propagation across a short exact sequence, in the two remaining positions -/

variable {S : ShortComplex X.Modules}

/-- **Finite dimensionality of the right-hand cohomology of a short exact sequence.** `Hⁿ(X, ℱ₃)`
is finite-dimensional as soon as `Hⁿ(X, ℱ₂)` and `Hⁿ⁺¹(X, ℱ₁)` are: the long exact sequence of
`AlgebraicGeometry.exists_cohomologyOverField_longExactSequence` is exact at `Hⁿ(X, ℱ₃)` between
the map out of `Hⁿ(X, ℱ₂)` and the connecting map into `Hⁿ⁺¹(X, ℱ₁)`. There is no hypothesis on
`f` or on the modules. -/
theorem finiteDimensional_cohomologyOverField_three_of_shortExact (hS : S.ShortExact) (n : ℕ)
    (h₂ : FiniteDimensional k (cohomologyOverField k f S.X₂ n))
    (h₁ : FiniteDimensional k (cohomologyOverField k f S.X₁ (n + 1))) :
    FiniteDimensional k (cohomologyOverField k f S.X₃ n) := by
  obtain ⟨d, -, -, hgd, -⟩ := exists_cohomologyOverField_longExactSequence k f hS
  have := h₂
  have := h₁
  exact Module.finiteDimensional_of_exact (cohomologyOverFieldMap k f S.g n).hom (d n).hom (hgd n)

/-- **Finite dimensionality of the left-hand cohomology in degree zero.** `H⁰(X, ℱ₁)` is
finite-dimensional as soon as `H⁰(X, ℱ₂)` is, because `H⁰(X, ℱ₁) ⟶ H⁰(X, ℱ₂)` is injective.
There is no hypothesis on `f` or on the modules. -/
theorem finiteDimensional_cohomologyOverField_one_of_shortExact_zero (hS : S.ShortExact)
    (h₂ : FiniteDimensional k (cohomologyOverField k f S.X₂ 0)) :
    FiniteDimensional k (cohomologyOverField k f S.X₁ 0) := by
  obtain ⟨-, hinj, -, -, -⟩ := exists_cohomologyOverField_longExactSequence k f hS
  have := h₂
  exact FiniteDimensional.of_injective (cohomologyOverFieldMap k f S.f 0).hom hinj

/-- **Finite dimensionality of the left-hand cohomology in a positive degree.** `Hⁿ⁺¹(X, ℱ₁)` is
finite-dimensional as soon as `Hⁿ(X, ℱ₃)` and `Hⁿ⁺¹(X, ℱ₂)` are: the long exact sequence is
exact at `Hⁿ⁺¹(X, ℱ₁)` between the connecting map out of `Hⁿ(X, ℱ₃)` and the map into
`Hⁿ⁺¹(X, ℱ₂)`. There is no hypothesis on `f` or on the modules. -/
theorem finiteDimensional_cohomologyOverField_one_of_shortExact_succ (hS : S.ShortExact) (n : ℕ)
    (h₃ : FiniteDimensional k (cohomologyOverField k f S.X₃ n))
    (h₂ : FiniteDimensional k (cohomologyOverField k f S.X₂ (n + 1))) :
    FiniteDimensional k (cohomologyOverField k f S.X₁ (n + 1)) := by
  obtain ⟨d, -, -, -, hdf⟩ := exists_cohomologyOverField_longExactSequence k f hS
  have := h₃
  have := h₂
  exact Module.finiteDimensional_of_exact (d n).hom
    (cohomologyOverFieldMap k f S.f (n + 1)).hom (hdf n)

/-- **The two-out-of-three property of [Stacks, Tag 02O6], unconditionally.** For a short exact
sequence `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of modules on a scheme over a field, finite dimensionality of
all the cohomology of any two of the three terms gives it for the third.

This is exactly the two-out-of-three obligation that the dévissage of [Stacks, Tag 01YH] imposes
on a property of coherent modules, in the shape
`AlgebraicGeometry.exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add`
carries it. There is no hypothesis on `f`, on the modules or on coherence: the three
implications are read off the long exact sequence. -/
theorem forall_finiteDimensional_cohomologyOverField_twoOutOfThree (hS : S.ShortExact) :
    (((∀ n, FiniteDimensional k (cohomologyOverField k f S.X₁ n)) ∧
        ∀ n, FiniteDimensional k (cohomologyOverField k f S.X₂ n)) →
          ∀ n, FiniteDimensional k (cohomologyOverField k f S.X₃ n)) ∧
      (((∀ n, FiniteDimensional k (cohomologyOverField k f S.X₁ n)) ∧
          ∀ n, FiniteDimensional k (cohomologyOverField k f S.X₃ n)) →
            ∀ n, FiniteDimensional k (cohomologyOverField k f S.X₂ n)) ∧
        (((∀ n, FiniteDimensional k (cohomologyOverField k f S.X₂ n)) ∧
            ∀ n, FiniteDimensional k (cohomologyOverField k f S.X₃ n)) →
              ∀ n, FiniteDimensional k (cohomologyOverField k f S.X₁ n)) := by
  refine ⟨fun ⟨h₁, h₂⟩ n => ?_, fun ⟨h₁, h₃⟩ n => ?_, fun ⟨h₂, h₃⟩ n => ?_⟩
  · exact finiteDimensional_cohomologyOverField_three_of_shortExact k f hS n (h₂ n) (h₁ (n + 1))
  · exact finiteDimensional_cohomologyOverField_of_shortExact k f hS n (h₁ n) (h₃ n)
  · cases n with
    | zero => exact finiteDimensional_cohomologyOverField_one_of_shortExact_zero k f hS (h₂ 0)
    | succ m =>
      exact finiteDimensional_cohomologyOverField_one_of_shortExact_succ k f hS m (h₃ m)
        (h₂ (m + 1))

/-! ### The floor reduced to the two base cases of the dévissage -/

/-- **[Stacks, Tag 02O6] over a field for every coherent module, from the dévissage of
[Stacks, Tag 01YH] and its two base cases.** The two-out-of-three obligation of the dévissage is
discharged by `forall_finiteDimensional_cohomologyOverField_twoOutOfThree`, so what is left of
the hypothesis carried across the Euler-characteristic development is finite dimensionality of
the cohomology of the structure sheaf and of the coherent modules supported in a proper closed
subset — two sheaves, not all of them.

The dévissage hypothesis is stated in exactly the form
`AlgebraicGeometry.exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add`
carries it, so the two can be fed the same term. -/
theorem forall_finiteDimensional_cohomologyOverField_of_devissage
    (hdev : ∀ P : X.Modules → Prop,
      (∀ T : ShortComplex X.Modules, T.ShortExact → SheafOfModules.IsCoherent T.X₁ →
        SheafOfModules.IsCoherent T.X₂ → SheafOfModules.IsCoherent T.X₃ →
        ((P T.X₁ ∧ P T.X₂ → P T.X₃) ∧ (P T.X₁ ∧ P T.X₃ → P T.X₂) ∧
          (P T.X₂ ∧ P T.X₃ → P T.X₁))) →
      (∀ (G : X.Modules) (Z : Set X), IsClosed Z → Z ≠ Set.univ →
        _root_.SheafOfModules.supp G ⊆ Z → P G) →
      P (SheafOfModules.unit X.ringCatSheaf) →
      ∀ G : X.Modules, SheafOfModules.IsCoherent G → P G)
    (hclosed : ∀ (G : X.Modules) (Z : Set X), IsClosed Z → Z ≠ Set.univ →
      _root_.SheafOfModules.supp G ⊆ Z → SheafOfModules.IsCoherent G →
        ∀ n, FiniteDimensional k (cohomologyOverField k f G n))
    (hunit : ∀ n,
      FiniteDimensional k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n)) :
    ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ n, FiniteDimensional k (cohomologyOverField k f G n) :=
  fun G hG =>
    hdev (fun G => SheafOfModules.IsCoherent G →
        ∀ n, FiniteDimensional k (cohomologyOverField k f G n))
      (fun _ hT t₁ t₂ t₃ =>
        have H := forall_finiteDimensional_cohomologyOverField_twoOutOfThree k f hT
        ⟨fun h _ => H.1 ⟨h.1 t₁, h.2 t₂⟩, fun h _ => H.2.1 ⟨h.1 t₁, h.2 t₃⟩,
          fun h _ => H.2.2 ⟨h.1 t₂, h.2 t₃⟩⟩)
      hclosed (fun _ => hunit) G hG hG

/-- **[Stacks, Tag 02O6] at a finite locally free module on a curve, from the dévissage and its
two base cases.** This is the single statement the Euler-characteristic development of
`StacksDraft/AlgebraicGeometry/F3b/CurveTensorEuler/` needs about `ℰ` itself: a finite locally
free module of constant rank on a curve over a field is coherent
(`AlgebraicGeometry.SheafOfModules.isCoherent_of_isFiniteLocallyFreeOfRank_of_isCurve`), so it is
an instance of `forall_finiteDimensional_cohomologyOverField_of_devissage`. -/
theorem forall_finiteDimensional_cohomologyOverField_of_isFiniteLocallyFreeOfRank_of_devissage
    [IsCurve k f] (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (hdev : ∀ P : X.Modules → Prop,
      (∀ T : ShortComplex X.Modules, T.ShortExact → SheafOfModules.IsCoherent T.X₁ →
        SheafOfModules.IsCoherent T.X₂ → SheafOfModules.IsCoherent T.X₃ →
        ((P T.X₁ ∧ P T.X₂ → P T.X₃) ∧ (P T.X₁ ∧ P T.X₃ → P T.X₂) ∧
          (P T.X₂ ∧ P T.X₃ → P T.X₁))) →
      (∀ (G : X.Modules) (Z : Set X), IsClosed Z → Z ≠ Set.univ →
        _root_.SheafOfModules.supp G ⊆ Z → P G) →
      P (SheafOfModules.unit X.ringCatSheaf) →
      ∀ G : X.Modules, SheafOfModules.IsCoherent G → P G)
    (hclosed : ∀ (G : X.Modules) (Z : Set X), IsClosed Z → Z ≠ Set.univ →
      _root_.SheafOfModules.supp G ⊆ Z → SheafOfModules.IsCoherent G →
        ∀ n, FiniteDimensional k (cohomologyOverField k f G n))
    (hunit : ∀ n,
      FiniteDimensional k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n)) :
    ∀ n, FiniteDimensional k (cohomologyOverField k f E n) :=
  forall_finiteDimensional_cohomologyOverField_of_devissage k f hdev hclosed hunit E
    (SheafOfModules.isCoherent_of_isFiniteLocallyFreeOfRank_of_isCurve k f E r)

end AlgebraicGeometry

end
