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
public import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

universe u v

/-!
# A direct sum is Mittag-Leffler if and only if each summand is

Let `R` be a commutative ring and `(M i)` a family of `R`-modules indexed by a type `ι`. This
file proves Stacks 059P: `⨁ i, M i` is Mittag-Leffler if and only if every `M i` is. Being
Mittag-Leffler is the intrinsic condition 059E (1): every map `f : P → M` from a finitely
presented module dominates and is dominated by a map `g : P → Q` into a finitely presented
module, domination meaning `Ker(f ⊗ id_N) = Ker(g ⊗ id_N)` for every `R`-module `N`.

The two directions rest on two facts about a direct sum, one for each. First, the inclusion
`DirectSum.lof R ι M i : M i → ⨁ i, M i` is split by the projection
`DirectSum.component R ι M i`, hence stays injective after tensoring with any `N`, so composing
a map with it does not change the kernel of `f ⊗ id_N`. This settles the "only if" direction
outright: the pair `(Q, g)` that the direct sum provides for `lof i ∘ f` serves `f` itself.

Second, tensoring commutes with direct sums, so an element of `(⨁ i, Q i) ⊗ N` vanishes as soon
as all of its components do, and therefore `Ker (f ⊗ id_N) = ⨅ i, Ker ((π i ∘ f) ⊗ id_N)` for
every `f : P → ⨁ i, Q i`. Read from right to left this says that a *finite* family of maps
`g i : P → Q i` out of one module is jointly dominated by a single map into `⨁ i, Q i`, which is
again finitely presented as soon as the `Q i` are; read from left to right it says that a map into
a direct sum is dominated by anything dominating all of its components. The "if" direction is the
two readings back to back: a finitely presented `P` is in particular finitely generated, so all
components of `f : P → ⨁ i, M i` outside a finite set `s` vanish, and their kernels contribute
nothing to the intersection; for `i ∈ s` choose a finitely presented `Q i` and a map
`g i : P → Q i` dominating and dominated by the `i`-th component of `f`.

## Main results

* `Stacks.MittagLeffler.DirectSumCriterion.solution`: Stacks 059P, the statement of
  `Module.mittagLeffler_directSum_iff`.

## Implementation notes

The source's main route — the "only if" direction from Lemma 059N (1) applied to the split exact
sequence with sub-object `M i`, the finite case of the converse from 059N (2), and the passage
to a general index set through Proposition 059E (1) or Lemma 0AS7 — is unavailable as those
three results stand: each assumes `Small.{v} R`, which 059P deliberately does not, both of its
directions staying inside `Type v`. What is formalized is the direct argument the source gives
after "but we can also argue it directly as follows", with the finite case treated in one step
instead of by induction on the size of `s` through 059N (2).

Two facts used here are missing from `Mathlib`. The formula
`Ker (f ⊗ id_N) = ⨅ i, Ker ((π i ∘ f) ⊗ id_N)` for a map into a direct sum is proved as
`ker_rTensor_eq_iInf_ker_component_comp_rTensor`, from the element-level naturality of
`TensorProduct.directSumLeft`, which `Mathlib` has only on pure tensors
(`TensorProduct.directSumLeft_tmul`). Reindexing an infimum along a map whose range carries all
the non-`⊤` values of the family is `iInf_comp_eq_iInf`; `Mathlib` has the special case
`iInf_ne_top_subtype`, where the reindexing map is the inclusion of `{i | A i ≠ ⊤}`.

## References

* [StacksProject 059P](https://stacks.math.columbia.edu/tag/059P)
-/



namespace Stacks.MittagLeffler.DirectSumCriterion

open DirectSum TensorProduct

section Helpers

variable {R : Type u} [CommRing R]

/-- Reindexing an infimum along `u` does not change it, as soon as the family is `⊤` off the range
of `u`. -/
private lemma iInf_comp_eq_iInf {α : Type*} [CompleteLattice α] {ι κ : Type*} {A : ι → α}
    (u : κ → ι) (h : ∀ i ∉ Set.range u, A i = ⊤) : ⨅ j, A (u j) = ⨅ i, A i := by
  refine le_antisymm (le_iInf fun i => ?_) (le_iInf fun j => iInf_le _ _)
  by_cases hi : i ∈ Set.range u
  · obtain ⟨j, rfl⟩ := hi
    exact iInf_le _ j
  · simp [h i hi]

/-- The equivalence `(⨁ i, M i) ⊗[R] N ≃ ⨁ i, M i ⊗[R] N` reads off the `i`-th component of an
element of `(⨁ i, M i) ⊗[R] N` by tensoring the `i`-th projection with `N`. This is
`TensorProduct.directSumLeft_tmul` for an arbitrary element in place of a pure tensor. -/
private lemma directSumLeft_apply_eq_component_rTensor {ι : Type v} [DecidableEq ι]
    (M : ι → Type v) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (N : Type v)
    [AddCommGroup N] [Module R N] (x : (⨁ i, M i) ⊗[R] N) (i : ι) :
    TensorProduct.directSumLeft R R M N x i = (DirectSum.component R ι M i).rTensor N x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => rw [TensorProduct.directSumLeft_tmul, LinearMap.rTensor_tmul,
      ← DirectSum.apply_eq_component]
  | add x y hx hy => simp [hx, hy]

/-- Tensoring a map into a direct sum with a module `N` has as kernel the intersection of the
kernels of its components tensored with `N`. -/
private lemma ker_rTensor_eq_iInf_ker_component_comp_rTensor {ι : Type v} (M : ι → Type v)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] {P : Type v} [AddCommGroup P] [Module R P]
    (f : P →ₗ[R] ⨁ i, M i) (N : Type v) [AddCommGroup N] [Module R N] :
    LinearMap.ker (f.rTensor N) =
      ⨅ i, LinearMap.ker ((DirectSum.component R ι M i ∘ₗ f).rTensor N) := by
  classical
  refine le_antisymm (le_iInf fun i x hx => ?_) fun x hx => ?_
  · simp only [LinearMap.mem_ker] at hx ⊢
    rw [LinearMap.rTensor_comp, LinearMap.comp_apply, hx, map_zero]
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.rTensor_comp,
      LinearMap.comp_apply] at hx ⊢
    have h0 : TensorProduct.directSumLeft R R M N (f.rTensor N x) = 0 :=
      DirectSum.ext fun i => by
        rw [directSumLeft_apply_eq_component_rTensor]; simpa using hx i
    simpa using h0

/-- Composing with a split injection `h` does not change the kernel of `f ⊗ id_N`: a left inverse
of `h` survives tensoring, so `h ⊗ id_N` is injective. -/
private lemma ker_rTensor_comp_of_leftInverse {A B P : Type v} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup P] [Module R P] {h : A →ₗ[R] B} {r : B →ₗ[R] A}
    (hr : r ∘ₗ h = LinearMap.id) (f : P →ₗ[R] A) (N : Type v) [AddCommGroup N] [Module R N] :
    LinearMap.ker ((h ∘ₗ f).rTensor N) = LinearMap.ker (f.rTensor N) := by
  have hinj : Function.Injective (h.rTensor N) :=
    Function.LeftInverse.injective (g := r.rTensor N) fun x => by
      simp [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hr]
  rw [LinearMap.rTensor_comp, LinearMap.ker_comp, LinearMap.ker_eq_bot.mpr hinj,
    Submodule.comap_bot]

/-- A map from a finitely generated module into a direct sum has all but finitely many
components zero. -/
private lemma exists_finset_forall_component_comp_eq_zero {ι : Type v} (M : ι → Type v)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] {P : Type v} [AddCommGroup P] [Module R P]
    [Module.Finite R P] (f : P →ₗ[R] ⨁ i, M i) :
    ∃ s : Finset ι, ∀ i ∉ s, DirectSum.component R ι M i ∘ₗ f = 0 := by
  classical
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := R) (M := P)
  refine ⟨t.biUnion fun p => (f p).support, fun i hi =>
    LinearMap.ker_eq_top.mp (top_le_iff.mp ?_)⟩
  rw [← ht, Submodule.span_le]
  intro p hp
  simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply,
    ← DirectSum.apply_eq_component]
  exact DFinsupp.notMem_support_iff.mp fun h => hi (Finset.mem_biUnion.mpr ⟨p, hp, h⟩)

/-- Over a finite index type a family of maps out of `P` is the family of components of a single
map into the direct sum. -/
private lemma exists_component_comp_eq {κ : Type v} [Finite κ] (Q : κ → Type v)
    [∀ j, AddCommGroup (Q j)] [∀ j, Module R (Q j)] {P : Type v} [AddCommGroup P] [Module R P]
    (g : ∀ j, P →ₗ[R] Q j) :
    ∃ G : P →ₗ[R] ⨁ j, Q j, ∀ j, DirectSum.component R κ Q j ∘ₗ G = g j := by
  classical
  let := Fintype.ofFinite κ
  exact ⟨(DirectSum.linearEquivFunOnFintype R κ Q).symm.toLinearMap ∘ₗ LinearMap.pi g,
    fun j => by ext p; rfl⟩

/-- A finite family of maps `g j : P →ₗ[R] Q j` into finitely presented modules is jointly
dominated by a single map into a finitely presented module: the direct sum `⨁ j, Q j` and the map
with components the `g j` have as kernel after tensoring with `N` the intersection of the kernels
of the `g j ⊗ id_N`. -/
private lemma exists_finitePresentation_ker_rTensor_eq_iInf {κ : Type v} [Finite κ]
    (Q : κ → Type v) [∀ j, AddCommGroup (Q j)] [∀ j, Module R (Q j)]
    [∀ j, Module.FinitePresentation R (Q j)] {P : Type v} [AddCommGroup P] [Module R P]
    (g : ∀ j, P →ₗ[R] Q j) :
    ∃ (T : Type v) (_ : AddCommGroup T) (_ : Module R T) (_ : Module.FinitePresentation R T)
      (G : P →ₗ[R] T), ∀ (N : Type v) [AddCommGroup N] [Module R N],
        LinearMap.ker (G.rTensor N) = ⨅ j, LinearMap.ker ((g j).rTensor N) := by
  classical
  let := Fintype.ofFinite κ
  obtain ⟨G, hG⟩ := exists_component_comp_eq Q g
  refine ⟨⨁ j, Q j, inferInstance, inferInstance,
    Module.FinitePresentation.of_equiv (DirectSum.linearEquivFunOnFintype R κ Q).symm, G,
    fun N _ _ => ?_⟩
  rw [ker_rTensor_eq_iInf_ker_component_comp_rTensor Q G N]
  exact iInf_congr fun j => by rw [hG j]

end Helpers

/-- Stacks 059P: the direct sum `⨁ i, M i` satisfies the Mittag-Leffler condition, in the
intrinsic form 059E (1), if and only if every summand `M i` does. This is the statement of
`Module.mittagLeffler_directSum_iff`. -/
public theorem solution (R : Type u) [CommRing R] {ι : Type v}
    (M : ι → Type v) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] :
    (∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
        (f : P →ₗ[R] (⨁ i, M i)), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
          (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
            [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) ↔
      ∀ i, ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
        (f : P →ₗ[R] M i), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
          (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
            [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N) := by
  classical
  refine ⟨fun hML i P _ _ _ f => ?_, fun hML P _ _ _ f => ?_⟩
  · obtain ⟨Q, hQ₁, hQ₂, hQ₃, g, hg⟩ := hML P (DirectSum.lof R ι M i ∘ₗ f)
    refine ⟨Q, hQ₁, hQ₂, hQ₃, g, fun N _ _ => Eq.trans ?_ (hg N)⟩
    exact (ker_rTensor_comp_of_leftInverse
      (DirectSum.component_comp_lof_same (M := M) R i) f N).symm
  · obtain ⟨s, hs⟩ := exists_finset_forall_component_comp_eq_zero M f
    choose Q hQ₁ hQ₂ hQ₃ g hg using fun i => hML i P (DirectSum.component R ι M i ∘ₗ f)
    let _ : ∀ i, AddCommGroup (Q i) := hQ₁
    let _ : ∀ i, Module R (Q i) := hQ₂
    let _ : ∀ i, Module.FinitePresentation R (Q i) := hQ₃
    obtain ⟨T, hT₁, hT₂, hT₃, G, hG⟩ :=
      exists_finitePresentation_ker_rTensor_eq_iInf (fun j : ↥s => Q j.1) fun j => g j.1
    refine ⟨T, hT₁, hT₂, hT₃, G, fun N _ _ => ?_⟩
    refine ((ker_rTensor_eq_iInf_ker_component_comp_rTensor M f N).trans ?_).trans (hG N).symm
    refine (iInf_comp_eq_iInf (Subtype.val : ↥s → ι) fun i hi => ?_).symm.trans
      (iInf_congr fun j => hg j.1 N)
    rw [hs i fun h => hi ⟨⟨i, h⟩, rfl⟩]
    simp

end Stacks.MittagLeffler.DirectSumCriterion

/-!
# A direct sum is Mittag-Leffler if and only if each summand is

Let `R` be a commutative ring. An `R`-module `M` is *Mittag-Leffler* when every map `f : P → M`
from a finitely presented `R`-module dominates and is dominated by a map `g : P → Q` into a
finitely presented `R`-module, domination meaning `Ker(f ⊗ id_N) = Ker(g ⊗ id_N)` for every
`R`-module `N` (Definition 059B); this is condition (1) of Proposition 059E, the one of the five
conditions there that mentions only `M`, and it is Definition 059F.

This file states that the property is detected summand by summand: `⨁ i, M i` is Mittag-Leffler if
and only if every `M i` is. In one direction each inclusion `M i → ⨁ i, M i` is split, hence
universally injective, so a map `f : P → M i` and its composite with the inclusion have the same
kernel after tensoring with any `N`, and a `g` dominating the composite dominates `f`; this is
Lemma 059N (1) for the split exact sequence with sub-object `M i`. In the other direction a map
`f : P → ⨁ i, M i` out of a finitely presented — indeed any finitely generated — module has image
in a finite subsum `⨁ i ∈ s, M i`, and the inclusion of that subsum is split again, so it suffices
to dominate the induced map into the subsum; there `Ker(f ⊗ id_N)` is the intersection over `i ∈ s`
of the kernels of the components `f i ⊗ id_N`, because tensoring commutes with direct sums, so the
direct sum `⨁ i ∈ s, Q i` of the modules provided by the hypothesis, which is again finitely
presented, dominates and is dominated by `f`.

## Main results

* `Module.mittagLeffler_directSum_iff`: a direct sum of `R`-modules is Mittag-Leffler if and only
  if each summand is.

## Implementation notes

Departures from the source's form, none of them weakening it.

*The Mittag-Leffler property is spelled out.* The condition is written inline in the intrinsic
form 059E (1), which is the spelling of Propositions 059M and 05CQ and of Lemma 059N, and the same
text appears twice, once for the direct sum and once for a summand;
`CategoryTheory.Functor.IsMittagLeffler` is the condition on an inverse system, that is
condition (4) of 059E for the dual systems, and does not apply to a module on its own.

*The module is the direct sum itself.* The source writes "`M = ⨁ i ∈ I, M i`" for a module `M`
together with a decomposition; here the module is `Mathlib`'s `DirectSum ι M`, as in the sibling
`Module.Flat.directSum_iff`, whose name this one mutates. Nothing is lost: the condition is
invariant under a linear equivalence `e : M ≃ₗ[R] N`, since `(e ∘ₗ f).rTensor N' = e.rTensor N' ∘ₗ
f.rTensor N'` and `e.rTensor N'` is injective, so a module with an internal direct sum
decomposition is covered by composing with `DirectSum.coeLinearMap` for the decomposition, which
is a linear equivalence exactly when the decomposition is internal (`DirectSum.IsInternal`).

*No smallness of `R` is assumed.* The siblings 059E, 059M, 059N and 05CQ carry `Small.{v} R`,
which is what makes their quantifiers over the modules of `Type v` the source's quantifiers over
all modules (Lemma 059C). It is deliberately absent here, because neither direction of the
equivalence uses it: both arguments sketched above keep every module they build — the composite
with a split inclusion, the finite subsum, the direct sum `⨁ i ∈ s, Q i` — inside `Type v`, and
they apply the hypothesis to the very module `P` they are given. Dropping an unused hypothesis
strengthens the statement and does not make it a universe-restricted variant of the source's: for
an `R : Type u` and modules in `Type v` the source's Mittag-Leffler property is the displayed
condition at `v := max u v`, applied to the `ULift`s of the summands to that universe; there
`Small.{max u v} R` holds by `small_lift`, so this statement contains 059P as an instance.

*Universes.* The index type `ι`, the summands `M i`, the modules `P` and `Q` and the test module
`N` all live in `Type v`, which is what puts `⨁ i, M i` in `Type v` too, so that both sides of the
equivalence are conditions on modules of one universe. For an index type in a larger universe `w`
the direct sum lands in `Type (max w v)` and the statement is applied there, to the `ULift`s of the
summands, which are linearly equivalent to them.

Faithfulness. (1) No hypothesis is dead: the data are `R`, `ι` and the family `M`, and each is used
by both sides — `R` as the base of every module, tensor product and finiteness condition, and `ι`
and `M` through `⨁ i, M i` on the left and through the quantifier over `i` on the right; nothing
is assumed of them, in particular no finiteness of `ι`, which is the whole point of the lemma.
(2) The scalars and the base are the source's: one commutative ring `R` throughout, the summands
and all test modules are `R`-modules, `f` and `g` are `R`-linear, finite presentation is over `R`,
and every tensor product is `⊗[R]`; nothing is localized or base changed. (3) The maps of the
Mittag-Leffler condition are pinned, not merely asserted to exist: `f ⊗ id_N` is `f.rTensor N`,
built from `f` itself, and likewise `g.rTensor N`, and only the finitely presented module `Q` and
the map `g` are existentially quantified, as they are in 059E (1); the source names no map in the
statement, the direct sum being pinned as `DirectSum ι M`, with its canonical inclusions
`DirectSum.lof` available for the proof. (4) The instantiation is not degenerate, and neither side
is vacuous: for `R = ℤ`, any `ι` and `M i = ℤ` both sides hold, the direct sum being free
(Example 059R (2)), while for `R = ℤ`, `ι = Unit` and `M _ = ℚ` both sides fail, since `ℚ` is not a
Mittag-Leffler `ℤ`-module (Example 059I). Both directions have content: the left side is a
condition on maps into a module that is not a summand of any `M i`, and the right side is not a
finite conjunction.

## References

* [StacksProject 059P](https://stacks.math.columbia.edu/tag/059P)
-/

open DirectSum

@[expose] public section

/-- **Stacks 059P.** Let `R` be a commutative ring and `(M i)` a family of `R`-modules indexed by a
type `ι`. Then the direct sum `⨁ i, M i` is Mittag-Leffler if and only if each `M i` is. Being
Mittag-Leffler is spelled out in the intrinsic form 059E (1): every map `f : P → M` from a finitely
presented module dominates and is dominated by a map `g : P → Q` into a finitely presented module,
domination meaning `Ker(f ⊗ id_N) = Ker(g ⊗ id_N)` for every `R`-module `N`. -/
@[stacks 059P "Mittag-Leffler is spelled out inline as condition (1) of 059E, as in 059M, 059N and
05CQ; the module is `Mathlib`'s `DirectSum`, as in `Module.Flat.directSum_iff`. No smallness of `R`
is assumed, neither direction using it. See the module docstring."]
public theorem Module.mittagLeffler_directSum_iff (R : Type u) [CommRing R] {ι : Type v}
    (M : ι → Type v) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] :
    (∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
        (f : P →ₗ[R] (⨁ i, M i)), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
          (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
            [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) ↔
      ∀ i, ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
        (f : P →ₗ[R] M i), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
          (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
            [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N) :=
  Stacks.MittagLeffler.DirectSumCriterion.solution R M

end
