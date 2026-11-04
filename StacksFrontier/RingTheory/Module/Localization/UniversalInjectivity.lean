module

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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
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
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Localization and universal injectivity of module maps

Let `φ : A → B` be a ring map, let `S ⊆ A` and `S' ⊆ B` be multiplicative subsets, let
`f : M → M'` be a map of `B`-modules and let `fₛ : N → N'` be its localization at `S'`, pinned by
the square `fₛ ∘ₗ g = g' ∘ₗ f` for localization maps `g : M → N` and `g' : M' → N'`. Let `Q` be an
`A`-module with localization `q : Q → Qₛ` at `S`. This file proves Stacks 05CM: (1) if `f ⊗_A id_Q`
is injective then so is `fₛ ⊗_A id_Q`, and (2) `fₛ ⊗_A id_Q` is injective if and only if the
`S⁻¹A`-linear avatar of `fₛ` is injective after `- ⊗_{S⁻¹A} Qₛ`. Quantified over the test module,
(1) says that a universally injective map of `A`-modules stays universally injective after
localizing at `S'`, and (2) says that for a map between `S⁻¹A`-modules universal injectivity over
`A` and over `S⁻¹A` are the same condition.

Item (1) is the source's argument: localization at `S'` is exact and `(S')⁻¹M ⊗_A Q` is a
localization of `M ⊗_A Q` at `S'` (`IsLocalizedModule.rTensor`), so `fₛ ⊗_A id_Q` *is* the
localization of `f ⊗_A id_Q` and `IsLocalizedModule.map_injective` applies.

Item (2) is the source's two facts (a) and (b). Both are instances of `Q ⊗_A N = Q ⊗_{S⁻¹A} S⁻¹N`
for `N` an `S⁻¹A`-module, which is used here in two steps: first `id_N ⊗ q : N ⊗_A Q → N ⊗_A Qₛ` is
bijective, being a localization at `S` whose source is already `S`-local; then
`IsLocalization.moduleTensorEquiv` identifies `N ⊗_{S⁻¹A} Qₛ` with `N ⊗_A Qₛ`. Both steps are
squares commuting with `fₛ` — the first because both of its composites are `fₛ ⊗ q` — and
injectivity transfers across such a square.

## Main results

* `Stacks.Localization.UniversalInjectivity.solution`: Stacks 05CM, items (1) and (2) for one test
  module `Q`.

## Implementation notes

Four auxiliary lemmas are proved here because Mathlib has no form of them.

`Stacks.Localization.UniversalInjectivity.map_rTensor` is the `f ⊗ id_Q` sibling of
`IsLocalizedModule.map_lTensor`, which covers `id_M ⊗ f` only: it says that `fₛ ⊗ id_Q` is the
localization of `f ⊗ id_Q` at `S'`. It is the whole content of item (1), and it is proved the way
its sibling is, by uniqueness of a map out of a localization.

`Stacks.Localization.UniversalInjectivity.bijective_of_isLocalizedModule_id_left` says that a
localization map at `S` whose *source* is already `S`-local is bijective. It is the "`S⁻¹N = N` for
an `S⁻¹A`-module `N`" of the source, and it is a general fact about `IsLocalizedModule` that
belongs next to `IsLocalizedModule.linearEquiv`, from which it follows in one step.

`Stacks.Localization.UniversalInjectivity.bijective_lTensor_of_isLocalizedModule` is that fact
applied to the test module: for an `S⁻¹A`-module `N`, the map `id_N ⊗ q : N ⊗_A Q → N ⊗_A Qₛ` is
bijective, being a localization at `S` (`IsLocalization.instIsLocalizedModuleTensorProductMap`)
whose source is already `S`-local. It carries the first step of item (2), where it is used once for
`N` and once for `N'`.

`Stacks.Localization.UniversalInjectivity.injective_iff_injective_of_comm` is the transfer of
injectivity across a commuting square whose horizontal maps are respectively bijective and
injective. It is stated for bare functions rather than for linear maps: the two squares it is
applied to live over different base rings, `A` for the first and `S⁻¹A` for the second, and the
conclusion identifies maps that differ only by `LinearMap.restrictScalars` or
`LinearMap.extendScalarsOfIsLocalization`, which change the linearity but not the underlying
function.

## References

* [StacksProject 05CM](https://stacks.math.columbia.edu/tag/05CM)
-/

@[expose] public section

namespace Stacks.Localization.UniversalInjectivity

open TensorProduct

/-- A localization map at `S` whose source is already `S`-local is bijective: if
`l : P →ₗ[R] P'` exhibits `P'` as the localization of `P` at `S`, and the identity of `P` does the
same, then `l` is bijective.

This is the source's "if `N` is an `S⁻¹A`-module then `S⁻¹N = N`". -/
@[ega "0 6.3.1" "more general"]
private lemma bijective_of_isLocalizedModule_id_left {R : Type*} [CommSemiring R] (S : Submonoid R)
    {P P' : Type*} [AddCommMonoid P] [Module R P] [AddCommMonoid P'] [Module R P']
    (l : P →ₗ[R] P') [IsLocalizedModule S l]
    [IsLocalizedModule S (LinearMap.id : P →ₗ[R] P)] : Function.Bijective l := by
  have h : ⇑(IsLocalizedModule.linearEquiv S (LinearMap.id : P →ₗ[R] P) l) = ⇑l :=
    funext (IsLocalizedModule.linearEquiv_apply S _ l)
  exact h ▸ (IsLocalizedModule.linearEquiv S (LinearMap.id : P →ₗ[R] P) l).bijective

/-- Tensoring an `S⁻¹A`-module with a localization map at `S` gives a bijection: if `N` is an
`S⁻¹A`-module and `q : Q →ₗ[A] Qₛ` exhibits `Qₛ` as the localization of `Q` at `S`, then
`id_N ⊗ q : N ⊗[A] Q → N ⊗[A] Qₛ` is bijective.

Indeed `id_N ⊗ q` is again a localization map at `S`, and its source `N ⊗[A] Q` is already
`S`-local because `N` is. This is the source's `N ⊗_A Q = N ⊗_A S⁻¹Q`. -/
private lemma bijective_lTensor_of_isLocalizedModule {A : Type*} [CommRing A] (S : Submonoid A)
    (Aₛ : Type*) [CommRing Aₛ] [Algebra A Aₛ] [IsLocalization S Aₛ] (N : Type*)
    [AddCommGroup N] [Module A N] [Module Aₛ N] [IsScalarTower A Aₛ N] {Q Qₛ : Type*}
    [AddCommGroup Q] [Module A Q] [AddCommGroup Qₛ] [Module A Qₛ]
    (q : Q →ₗ[A] Qₛ) [IsLocalizedModule S q] : Function.Bijective (q.lTensor N) :=
  have := isLocalizedModule_id S N Aₛ
  have := isLocalizedModule_id S (N ⊗[A] Q) Aₛ
  bijective_of_isLocalizedModule_id_left S (TensorProduct.map .id q)

/-- Injectivity transfers across a commuting square `r ∘ u = v ∘ l` whose left edge `l` is
bijective and whose right edge `r` is injective: `u` is injective if and only if `v` is. -/
private lemma injective_iff_injective_of_comm {α β γ δ : Type*} {u : α → γ} {v : β → δ}
    {l : α → β} {r : γ → δ} (hl : Function.Bijective l) (hr : Function.Injective r)
    (hcomm : ∀ a, r (u a) = v (l a)) : Function.Injective u ↔ Function.Injective v := by
  have h : r ∘ u = v ∘ l := funext hcomm
  rw [← hr.of_comp_iff u, h]
  exact ⟨fun hv => hv.of_comp_right hl.surjective, (·.comp hl.injective)⟩

/-- Tensoring by an `A`-module commutes with localization at `S'`: if `fₛ` is the localization of
`f` at `S'`, pinned by the square `fₛ ∘ₗ g = g' ∘ₗ f`, then `fₛ ⊗ id_Q` is the localization of
`f ⊗ id_Q` at `S'`.

This is the `f ⊗ id_Q` case of `IsLocalizedModule.map_lTensor`, which covers `id_M ⊗ f`. -/
private lemma map_rTensor {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (S' : Submonoid B) {M M' N N' Q : Type*}
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [AddCommGroup M'] [Module A M'] [Module B M'] [IsScalarTower A B M']
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    [AddCommGroup N'] [Module A N'] [Module B N'] [IsScalarTower A B N']
    [AddCommGroup Q] [Module A Q]
    (g : M →ₗ[B] N) (g' : M' →ₗ[B] N') [IsLocalizedModule S' g] [IsLocalizedModule S' g']
    (f : M →ₗ[B] M') (fₛ : N →ₗ[B] N') (hf : fₛ ∘ₗ g = g' ∘ₗ f) :
    IsLocalizedModule.map S' (AlgebraTensorModule.rTensor A Q g)
        (AlgebraTensorModule.rTensor A Q g') (AlgebraTensorModule.rTensor A Q f) =
      AlgebraTensorModule.rTensor A Q fₛ := by
  refine IsLocalizedModule.linearMap_ext S' (AlgebraTensorModule.rTensor A Q g)
    (AlgebraTensorModule.rTensor A Q g') ?_
  rw [IsLocalizedModule.map_comp, ← AlgebraTensorModule.rTensor_comp,
    ← AlgebraTensorModule.rTensor_comp, hf]

/-- **Stacks 05CM, item (1).** If `f ⊗_A id_Q` is injective, then so is its localization
`fₛ ⊗_A id_Q` at a multiplicative subset `S' ⊆ B`.

Localization at `S'` is exact and `fₛ ⊗_A id_Q` is the localization of `f ⊗_A id_Q`. -/
private lemma rTensor_injective_of_rTensor_injective {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (S' : Submonoid B) {M M' N N' Q : Type*}
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [AddCommGroup M'] [Module A M'] [Module B M'] [IsScalarTower A B M']
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    [AddCommGroup N'] [Module A N'] [Module B N'] [IsScalarTower A B N']
    [AddCommGroup Q] [Module A Q]
    (g : M →ₗ[B] N) (g' : M' →ₗ[B] N') [IsLocalizedModule S' g] [IsLocalizedModule S' g']
    (f : M →ₗ[B] M') (fₛ : N →ₗ[B] N') (hf : fₛ ∘ₗ g = g' ∘ₗ f)
    (h : Function.Injective ((f.restrictScalars A).rTensor Q)) :
    Function.Injective ((fₛ.restrictScalars A).rTensor Q) := by
  have := IsLocalizedModule.map_injective S' (AlgebraTensorModule.rTensor A Q g)
    (AlgebraTensorModule.rTensor A Q g') (AlgebraTensorModule.rTensor A Q f) h
  rwa [map_rTensor S' g g' f fₛ hf] at this

/-- **Stacks 05CM, item (2).** For an `A`-linear map `fₛ` between two `S⁻¹A`-modules and an
`A`-module `Q` with localization `q : Q → Qₛ` at `S`, the map `fₛ ⊗_A id_Q` is injective if and
only if the `S⁻¹A`-linear avatar of `fₛ` is injective after `- ⊗_{S⁻¹A} Qₛ`. -/
private lemma rTensor_injective_iff_extendScalarsOfIsLocalization {A : Type*} [CommRing A]
    (S : Submonoid A) (Aₛ : Type*) [CommRing Aₛ] [Algebra A Aₛ] [IsLocalization S Aₛ]
    {N N' Q Qₛ : Type*}
    [AddCommGroup N] [Module A N] [Module Aₛ N] [IsScalarTower A Aₛ N]
    [AddCommGroup N'] [Module A N'] [Module Aₛ N'] [IsScalarTower A Aₛ N']
    [AddCommGroup Q] [Module A Q] [AddCommGroup Qₛ] [Module A Qₛ] [Module Aₛ Qₛ]
    [IsScalarTower A Aₛ Qₛ] (q : Q →ₗ[A] Qₛ) [IsLocalizedModule S q] (fₛ : N →ₗ[A] N') :
    Function.Injective (fₛ.rTensor Q) ↔
      Function.Injective ((LinearMap.extendScalarsOfIsLocalization S Aₛ fₛ).rTensor Qₛ) := by
  -- Localizing the test module: `id_N ⊗ q` is bijective and natural in `N`, both composites
  -- around its square being `fₛ ⊗ q`.
  have sq₁ : q.lTensor N' ∘ₗ fₛ.rTensor Q = fₛ.rTensor Qₛ ∘ₗ q.lTensor N :=
    (LinearMap.lTensor_comp_rTensor _ _ _).trans (LinearMap.rTensor_comp_lTensor _ _ _).symm
  have step₁ : Function.Injective (fₛ.rTensor Q) ↔ Function.Injective (fₛ.rTensor Qₛ) :=
    injective_iff_injective_of_comm (bijective_lTensor_of_isLocalizedModule S Aₛ N q)
      (bijective_lTensor_of_isLocalizedModule S Aₛ N' q).injective (LinearMap.congr_fun sq₁)
  -- Changing the base ring: `N ⊗[Aₛ] Qₛ = N ⊗[A] Qₛ`, naturally in `N`.
  have sq₂ : (IsLocalization.moduleTensorEquiv S Aₛ N' Qₛ).toLinearMap ∘ₗ
      (LinearMap.extendScalarsOfIsLocalization S Aₛ fₛ).rTensor Qₛ =
      LinearMap.extendScalarsOfIsLocalization S Aₛ (fₛ.rTensor Qₛ) ∘ₗ
        (IsLocalization.moduleTensorEquiv S Aₛ N Qₛ).toLinearMap :=
    TensorProduct.ext' fun _ _ => rfl
  have step₂ : Function.Injective ((LinearMap.extendScalarsOfIsLocalization S Aₛ fₛ).rTensor Qₛ) ↔
      Function.Injective (fₛ.rTensor Qₛ) :=
    injective_iff_injective_of_comm (IsLocalization.moduleTensorEquiv S Aₛ N Qₛ).bijective
      (IsLocalization.moduleTensorEquiv S Aₛ N' Qₛ).injective (LinearMap.congr_fun sq₂)
  exact step₁.trans step₂.symm

/-- **Stacks 05CM.** Let `A → B` be a ring map, let `S ⊆ A` and `S' ⊆ B` be multiplicative
subsets, let `f : M → M'` be a map of `B`-modules and let `fₛ : N → N'` be its localization at
`S'`, pinned by the square `fₛ ∘ₗ g = g' ∘ₗ f`. Let `Q` be an `A`-module with localization `S⁻¹Q`
at `S`. Then:

1. if `f ⊗ id_Q` is injective, so is `fₛ ⊗ id_Q`, both tensor products taken over `A`;
2. `fₛ ⊗_A id_Q` is injective if and only if `fₛ ⊗_{S⁻¹A} id_{S⁻¹Q}` is injective. -/
public theorem solution
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (S : Submonoid A) (S' : Submonoid B)
    (Aₛ : Type*) [CommRing Aₛ] [Algebra A Aₛ] [IsLocalization S Aₛ] {M M' N N' Q Qₛ : Type*}
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [AddCommGroup M'] [Module A M'] [Module B M'] [IsScalarTower A B M']
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    [Module Aₛ N] [IsScalarTower A Aₛ N]
    [AddCommGroup N'] [Module A N'] [Module B N'] [IsScalarTower A B N']
    [Module Aₛ N'] [IsScalarTower A Aₛ N']
    [AddCommGroup Q] [Module A Q] [AddCommGroup Qₛ] [Module A Qₛ] [Module Aₛ Qₛ]
    [IsScalarTower A Aₛ Qₛ] (g : M →ₗ[B] N) (g' : M' →ₗ[B] N') [IsLocalizedModule S' g]
    [IsLocalizedModule S' g'] (q : Q →ₗ[A] Qₛ) [IsLocalizedModule S q] (f : M →ₗ[B] M')
    (fₛ : N →ₗ[B] N') (hf : fₛ ∘ₗ g = g' ∘ₗ f) :
    (Function.Injective ((f.restrictScalars A).rTensor Q) →
        Function.Injective ((fₛ.restrictScalars A).rTensor Q)) ∧
      (Function.Injective ((fₛ.restrictScalars A).rTensor Q) ↔
        Function.Injective ((LinearMap.extendScalarsOfIsLocalization S Aₛ
          (fₛ.restrictScalars A)).rTensor Qₛ)) :=
  ⟨rTensor_injective_of_rTensor_injective S' g g' f fₛ hf,
    rTensor_injective_iff_extendScalarsOfIsLocalization S Aₛ q (fₛ.restrictScalars A)⟩

end Stacks.Localization.UniversalInjectivity

end

/-!
# Localization and universal injectivity of module maps

Let `φ : A → B` be a ring map, let `S ⊆ A` and `S' ⊆ B` be multiplicative subsets with
`φ(S) ⊆ S'`, and let `f : M → M'` be a map of `B`-modules. Following Lazard, a map of
`A`-modules is *universally injective* when it remains injective after `- ⊗_A Q` for every
`A`-module `Q` (Stacks 058I). This file states Stacks 05CM: (1) if `f` is universally injective
as a map of `A`-modules, then its localization `(S')⁻¹M → (S')⁻¹M'` is universally injective both
as a map of `A`-modules and as a map of `S⁻¹A`-modules; (2) between `(S')⁻¹B`-modules the two
notions agree, that is, a map of such modules is universally injective as a map of `A`-modules if
and only if it is universally injective as a map of `S⁻¹A`-modules.

Two identifications carry the lemma. Localization at `S'` is exact and commutes with `- ⊗_A Q`,
so `(S')⁻¹(M ⊗_A Q) = ((S')⁻¹M) ⊗_A Q`; this gives (1). And a module `N` on which the elements
of `S` act invertibly is an `S⁻¹A`-module with `N ⊗_A Q = N ⊗_{S⁻¹A} S⁻¹Q`, naturally in `N`;
this gives (2).

## Main results

* `IsLocalizedModule.rTensor_injective_of_rTensor_injective`: item (1), for one test module `Q`.
  Localization at `S'` preserves injectivity after `- ⊗_A Q`; no localization of `A` occurs.
* `LinearMap.rTensor_injective_iff_extendScalarsOfIsLocalization`: item (2), for one test module
  `Q` together with one localization `S⁻¹Q` of it. For a map of `A`-modules between two
  `S⁻¹A`-modules, injectivity after `- ⊗_A Q` and after `- ⊗_{S⁻¹A} S⁻¹Q` agree; no `B` occurs.
* `IsLocalizedModule.rTensor_injective_of_rTensor_injective_and_iff_extendScalars`: the two items
  in the single form the source states them, about one localized map `fₛ`. The two results above
  are its projections; they are what a user cites, since each item is a statement about only its
  own data, and quantifies over data the other does not mention.

## Implementation notes

Both items are stated for a fixed test module, as in Stacks 05CJ, rather than for
all test modules at once: that is the form the argument proves, it is stronger, and it frees the
statement of any universe hypothesis on the test modules (`Mathlib` has no predicate for universal
injectivity of a module map, so `f ⊗ id_Q` is spelled `f.rTensor Q`, as in Stacks 058K and
058M). The source's form is the closure over the test module. Closing item (1) over `Q` gives
universal injectivity of the localized map as a map of `A`-modules; for an `S⁻¹A`-module `P` one
may take `Q := P` and `S⁻¹Q := P` with `q := .id` (`isLocalizedModule_id`), and item (2) turns that
into universal injectivity as a map of `S⁻¹A`-modules, which is all of (1). Item (2) closed over
`Q` and read in both directions — the `←` direction with `S⁻¹Q` any localization of `Q`, for
instance `LocalizedModule S Q` — is the source's second sentence, for `A`-linear maps between
`S⁻¹A`-modules rather than only for `B`-linear maps between `(S')⁻¹B`-modules; a map of the latter
kind is one of the former by restriction of scalars, so this is a generalization of it. So the two
items are the two results, and the second half of (1) is their composite rather than a third
statement.

The two items are logically independent — neither follows from the other, as the degenerate cases
`S = ⊥` and `S' = ⊥` show, where each becomes a tautology while the other retains its content — so
each is stated over its own data alone: item (1) mentions no localization of `A` and item (2) no
`B`. Their conjunction about a single localized map is the source's own sentence and is stated as
well; the two items are recovered from it at `S = ⊥` and at `S' = ⊥` respectively, and it is those
recoveries, not the conjunction, that a use site should cite.

The ring map `φ` is `[Algebra A B]` and restriction of scalars along it is `[Module A M]` with
`[IsScalarTower A B M]`. Localizations are abstract throughout, `[IsLocalization S Aₛ]` and
`[IsLocalizedModule S' g]`, in place of `Localization S` and `LocalizedModule S' M`, so that the
statements apply to whichever model of the localization a user has. The localized map is not
`IsLocalizedModule.map S' g g' f` but a map `fₛ` pinned by the source's square `fₛ ∘ₗ g = g' ∘ₗ f`,
which determines it: two `B`-linear maps out of a localization that agree after `g` are equal, by
`IsLocalizedModule.ext`. The `S⁻¹A`-linear avatar of an `A`-linear map between `S⁻¹A`-modules is
`LinearMap.extendScalarsOfIsLocalization S Aₛ` of it, an `S⁻¹A`-linear map with the same underlying
function; an `A`-linear map between `S⁻¹A`-modules is `S⁻¹A`-linear for free, so this is a change
of view and not a further hypothesis. Where the map at hand is `B`-linear one applies it to
`fₛ.restrictScalars A`.

The hypothesis `φ(S) ⊆ S'` of the source does not appear. What (2) uses, and all it uses, is that
the two modules involved are `S⁻¹A`-modules compatibly with their `A`-module structures, which is
exactly what `φ(S) ⊆ S'` provides for `(S')⁻¹M` and `(S')⁻¹M'`; that structure is unique when it
exists, so nothing is lost by assuming it as `[Module Aₛ N]` with `[IsScalarTower A Aₛ N]`, and no
relation between `S` and `S'` is then needed anywhere. Item (1) is genuinely an implication and not
an equivalence: for `A = B = ℤ`, `S = {1}`, `S'` the powers of `2`, `M = M' = ℤ` and `f`
multiplication by `2`, the localized map is an isomorphism, so its tensored maps are all injective,
while `f ⊗ id_Q` fails to be injective for `Q = ℤ/2ℤ`.

Faithfulness. (1) No hypothesis is dead. `f`, `g`, `g'`, `hf`, `B` and `S'` are what item (1) runs
on, and `IsLocalizedModule S' g` is live there: without it, `g = 0`, `g' = 0`, `f = .id : ℤ → ℤ`
and `fₛ = 0` satisfy `hf` with `f ⊗ id_Q` injective and `fₛ ⊗ id_Q` not. The localization datum `q`
is live in item (2): with `S⁻¹Q := 0` and `q := 0` the right-hand side holds for `fₛ = 0 : ℤ → 0`
over `Aₛ = A = ℤ` and `S = {1}`, while the left-hand side fails at `Q = ℤ`. The `S⁻¹A`-module
structures are what its right-hand side is stated with. (2) The scalars and the base are the
source's: in item (1) `f` and `fₛ` are `B`-linear and universal injectivity as a map of `A`-modules
is tested by `restrictScalars A` against `⊗[A] Q`; in item (2) universal injectivity as a map of
`S⁻¹A`-modules is tested by `⊗[Aₛ] S⁻¹Q` against the `S⁻¹A`-linear avatar of `fₛ`; neither side is
silently read over the other ring. (3) Every canonical map is pinned: `fₛ` by the square
`fₛ ∘ₗ g = g' ∘ₗ f` rather than by its existence, its `S⁻¹A`-linear form by
`LinearMap.extendScalarsOfIsLocalization`, `S⁻¹Q` by `IsLocalizedModule S q` for the given `q`, and
the tensored maps by `rTensor` applied to `f` and `fₛ` themselves. (4) The instantiation is not
degenerate: for `A = B = ℤ` with `S = S'` the powers of `2`, `Aₛ = ℤ[1/2]`, `M = ℤ`, `M' = ℤ × ℤ`,
`f = LinearMap.inl`, `N = ℤ[1/2]`, `N' = ℤ[1/2] × ℤ[1/2]`, `fₛ = LinearMap.inl`, `Q = ℤ` and
`S⁻¹Q = ℤ[1/2]`, the hypothesis of item (1) holds (`f` is split, hence universally injective) and
both items say something true and non-vacuous, while for `f` multiplication by `3` on `M = M' = ℤ`
the hypothesis fails at `Q = ℤ/3ℤ` and so does the conclusion.

## References

* [StacksProject 05CM](https://stacks.math.columbia.edu/tag/05CM)
-/

@[expose] public section

/-- A ring is its own localization at the trivial submonoid. -/
private instance isLocalization_bot (A : Type*) [CommRing A] : IsLocalization (⊥ : Submonoid A) A :=
  IsLocalization.self bot_le

/-- Localizing at the trivial submonoid is the identity. -/
private instance isLocalizedModule_bot_id (A : Type*) [CommRing A] (P : Type*) [AddCommGroup P]
    [Module A P] : IsLocalizedModule (⊥ : Submonoid A) (LinearMap.id : P →ₗ[A] P) :=
  isLocalizedModule_id _ _ A

/-- **Stacks 05CM.** Let `A → B` be a ring map, let `S ⊆ A` and `S' ⊆ B` be multiplicative
subsets, let `f : M → M'` be a map of `B`-modules and let `fₛ : N → N'` be its localization at
`S'`, pinned by the square `fₛ ∘ₗ g = g' ∘ₗ f`. Let `Q` be an `A`-module with localization
`S⁻¹Q` at `S`. Then:

1. if `f ⊗ id_Q` is injective, so is `fₛ ⊗ id_Q`, both tensor products taken over `A`;
2. `fₛ ⊗_A id_Q` is injective if and only if `fₛ ⊗_{S⁻¹A} id_{S⁻¹Q}` is injective.

This is the source's own sentence, about one localized map. The two items are independent of each
other and each is stated separately, over its own data alone, as
`IsLocalizedModule.rTensor_injective_of_rTensor_injective` and
`LinearMap.rTensor_injective_iff_extendScalarsOfIsLocalization`; those are the forms to cite. -/
@[stacks 05CM "Items (1) and (2) together, for one test module `Q`; the source's form is the
closure over `Q`."]
public theorem IsLocalizedModule.rTensor_injective_of_rTensor_injective_and_iff_extendScalars
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (S : Submonoid A) (S' : Submonoid B)
    (Aₛ : Type*) [CommRing Aₛ] [Algebra A Aₛ] [IsLocalization S Aₛ] {M M' N N' Q Qₛ : Type*}
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [AddCommGroup M'] [Module A M'] [Module B M'] [IsScalarTower A B M']
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    [Module Aₛ N] [IsScalarTower A Aₛ N]
    [AddCommGroup N'] [Module A N'] [Module B N'] [IsScalarTower A B N']
    [Module Aₛ N'] [IsScalarTower A Aₛ N']
    [AddCommGroup Q] [Module A Q] [AddCommGroup Qₛ] [Module A Qₛ] [Module Aₛ Qₛ]
    [IsScalarTower A Aₛ Qₛ] (g : M →ₗ[B] N) (g' : M' →ₗ[B] N') [IsLocalizedModule S' g]
    [IsLocalizedModule S' g'] (q : Q →ₗ[A] Qₛ) [IsLocalizedModule S q] (f : M →ₗ[B] M')
    (fₛ : N →ₗ[B] N') (hf : fₛ ∘ₗ g = g' ∘ₗ f) :
    (Function.Injective ((f.restrictScalars A).rTensor Q) →
        Function.Injective ((fₛ.restrictScalars A).rTensor Q)) ∧
      (Function.Injective ((fₛ.restrictScalars A).rTensor Q) ↔
        Function.Injective ((LinearMap.extendScalarsOfIsLocalization S Aₛ
          (fₛ.restrictScalars A)).rTensor Qₛ)) :=
  Stacks.Localization.UniversalInjectivity.solution S S' Aₛ g g' q f fₛ hf

/-- **Stacks 05CM, item (1).** Let `A → B` be a ring map, let `S' ⊆ B` be a multiplicative subset,
let `f : M → M'` be a map of `B`-modules and let `fₛ : N → N'` be its localization at `S'`, pinned
by the square `fₛ ∘ₗ g = g' ∘ₗ f`. Let `Q` be an `A`-module. If `f ⊗ id_Q` is injective, so is
`fₛ ⊗ id_Q`, both tensor products taken over `A`.

Quantifying over `Q`: if `f` is universally injective as a map of `A`-modules, then so is its
localization at `S'`. Composed with
`LinearMap.rTensor_injective_iff_extendScalarsOfIsLocalization` this gives the universal
injectivity of the localization as a map of `S⁻¹A`-modules as well, for any `S ⊆ A` with
`φ(S) ⊆ S'`. -/
@[stacks 05CM "Item (1), for one test module `Q`; the source's form is the closure over `Q`."]
public theorem IsLocalizedModule.rTensor_injective_of_rTensor_injective
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (S' : Submonoid B)
    {M M' N N' : Type*}
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [AddCommGroup M'] [Module A M'] [Module B M'] [IsScalarTower A B M']
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    [AddCommGroup N'] [Module A N'] [Module B N'] [IsScalarTower A B N']
    (g : M →ₗ[B] N) (g' : M' →ₗ[B] N') [IsLocalizedModule S' g] [IsLocalizedModule S' g']
    (f : M →ₗ[B] M') (fₛ : N →ₗ[B] N') (hf : fₛ ∘ₗ g = g' ∘ₗ f) (Q : Type*) [AddCommGroup Q]
    [Module A Q] (h : Function.Injective ((f.restrictScalars A).rTensor Q)) :
    Function.Injective ((fₛ.restrictScalars A).rTensor Q) :=
  (IsLocalizedModule.rTensor_injective_of_rTensor_injective_and_iff_extendScalars
    ⊥ S' A g g' .id f fₛ hf).1 h

/-- **Stacks 05CM, item (2).** Let `S ⊆ A` be a multiplicative subset, let `fₛ : N → N'` be a map
of `A`-modules between two `S⁻¹A`-modules and let `Q` be an `A`-module with localization `S⁻¹Q` at
`S`. Then `fₛ ⊗_A id_Q` is injective if and only if `fₛ ⊗_{S⁻¹A} id_{S⁻¹Q}` is injective.

Quantifying over `Q`: for a map between `S⁻¹A`-modules — in particular between `(S')⁻¹B`-modules,
for a multiplicative `S' ⊆ B` with `φ(S) ⊆ S'`, which is the case the source states — universal
injectivity as a map of `A`-modules and universal injectivity as a map of `S⁻¹A`-modules are the
same condition. -/
@[stacks 05CM "Item (2), for one test module `Q` and one localization `S⁻¹Q` of it; stated for an
`A`-linear map between `S⁻¹A`-modules, of which the source's `B`-linear map between
`(S')⁻¹B`-modules is a case."]
public theorem LinearMap.rTensor_injective_iff_extendScalarsOfIsLocalization
    {A : Type*} [CommRing A] (S : Submonoid A) (Aₛ : Type*) [CommRing Aₛ] [Algebra A Aₛ]
    [IsLocalization S Aₛ] {N N' Q Qₛ : Type*}
    [AddCommGroup N] [Module A N] [Module Aₛ N] [IsScalarTower A Aₛ N]
    [AddCommGroup N'] [Module A N'] [Module Aₛ N'] [IsScalarTower A Aₛ N']
    [AddCommGroup Q] [Module A Q] [AddCommGroup Qₛ] [Module A Qₛ] [Module Aₛ Qₛ]
    [IsScalarTower A Aₛ Qₛ] (q : Q →ₗ[A] Qₛ) [IsLocalizedModule S q] (fₛ : N →ₗ[A] N') :
    Function.Injective (fₛ.rTensor Q) ↔
      Function.Injective ((LinearMap.extendScalarsOfIsLocalization S Aₛ fₛ).rTensor Qₛ) :=
  (IsLocalizedModule.rTensor_injective_of_rTensor_injective_and_iff_extendScalars
    S ⊥ Aₛ .id .id q fₛ fₛ rfl).2

end
