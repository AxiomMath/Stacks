module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Mon
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
public import StacksFrontier.CategoryTheory.Sites.Pretopology.EquivalenceComparison
public import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Coverings with a bounded index set (towards Stacks 000X)

Fix a category `C` together with a class `IsCov : Covering C → Prop` of *coverings* of `C`, a
covering being a family of morphisms `{φᵢ : Uᵢ ⟶ U}_{i ∈ I}` with a common target. For a
suitable cardinal `κ`, the coverings in `IsCov` whose index set has cardinality at most `κ` again
satisfy the site axioms, they contain any prescribed small set of coverings, and every covering
in `IsCov` is combinatorially equivalent to one of them. This is the cardinality half of
Stacks 000X; the class it produces is in general *not* set-sized. Stacks 000X itself, with the
`V_α` truncation that makes the class a set, is `exists_covTrunc_isSite` in
`StacksFrontier.CategoryTheory.Sites.Pretopology.SmallSubsiteTruncated`.

## Main definitions

* `Covering C`: an object of `C` together with a family of morphisms into it, i.e. a term of
  `(U : C) × PreZeroHypercover.{w} U`, with an independent index universe `w`.
* `IsoCond`, `CompositionCond`, `BaseChangeCond`: the three site axioms for a class of
  coverings, conjoined in `IsSite`.
* `CovBounded IsCov κ`: the coverings in `IsCov` whose index set has cardinality at most `κ`.

## Main results

* `exists_covBounded_isSite`: the cardinality-bounded coverings form a site representing every
  covering.

## Combinatorial equivalence is Stacks 00VU (1), not a `HEq` of morphisms

A covering is a family of morphisms with fixed target, which is Mathlib's
`CategoryTheory.PreZeroHypercover`; the object is bundled with it here only because `IsCov` and
`Cov₀` must range over the coverings of *all* objects at once. Combinatorial equivalence is
then the canonical `PreZeroHypercover.CombinatoriallyEquivalent` of Stacks 00VU (1), with the
equality of targets carried by the `Σ`.

The relation stated as `HEq (𝒰.hom i) (𝒱.hom (a i))` would be **strictly weaker** than
00VU (1). The source asks for `φᵢ = ψ_{a i}`, which presupposes an equality of *source objects*
and transports along it; `HEq` asks only that the two hom-*types* be equal, and type equality
of hom-sets does not recover object equality. In the indiscrete category on `Bool`, where every
hom-type is `PUnit`, the one-element covering of `true` with source `true` and the one with
source `false` satisfy the `HEq` relation while no index map makes their sources agree. Since
the relation occurs in the *conclusion* of clause (3) below, that would make 000X weaker than
the source.

`combEquiv_of_arrowSet_eq` derives the relation from an equality of the *sets of
`(source, morphism)` pairs*, and such an equality of `Σ`-pairs carries the source equality along
with the morphism equality.

## Implementation notes

Stacks 000X also bounds a covering by asking that it lie in a stage `V_α` of the von Neumann
cumulative hierarchy, and that is what makes `Cov(C)_{κ, α}` a set. `CovBounded` omits this
truncation: the class `CovBounded IsCov κ` lives in `Type (max u v + 1)` and is in general not
`Small.{max u v}` (one-element index types alone already form a proper class). The ordinal `α`
of `exists_covBounded_isSite` is unconstrained and the proof takes `α = ω`. The truncated,
set-sized form is `CovTrunc` and `exists_covTrunc_isSite`. "`Cov₀` is a set rather than a proper
class" reads as `Small.{max u v} Cov₀`.

The covering families and site axioms have an independent index universe `w`. The cardinal
bounds below specialize to `w = max u v`, so that both index sets and the type of
combinatorial invariants can be compared in one `Cardinal` type.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u v w

/-- A *covering family* in `C`: an object together with a family of morphisms into it, indexed
by a type in an independent universe `Type w`. The object is bundled so that a class of
coverings of arbitrary objects is a single predicate `Covering C → Prop`. -/
abbrev Covering (C : Type u) [Category.{v} C] : Type (max u v (w + 1)) :=
  (U : C) × PreZeroHypercover.{w} U

variable {C : Type u} [Category.{v} C]

namespace Covering

/-- Two coverings are *combinatorially equivalent* (Stacks 00VU (1)) if their targets agree and,
after transporting along that equality, the two families are combinatorially equivalent in the
canonical sense: index maps in both directions matching the morphisms on the nose, sources
included. -/
def CombEquiv (𝒰 𝒱 : Covering.{u, v, w} C) : Prop :=
  ∃ h : 𝒰.1 = 𝒱.1, PreZeroHypercover.CombinatoriallyEquivalent (h ▸ 𝒰.2) 𝒱.2

/-- Combinatorial equivalence is reflexive. -/
lemma CombEquiv.refl (𝒰 : Covering.{u, v, w} C) : CombEquiv 𝒰 𝒰 :=
  ⟨rfl, PreZeroHypercover.combinatoriallyEquivalent_refl _⟩

/-- Combinatorial equivalence is symmetric: once the targets are identified, this is symmetry of
the canonical relation, which is the swap of the two halves of its definition. -/
lemma CombEquiv.symm {𝒰 𝒱 : Covering.{u, v, w} C} (h : CombEquiv 𝒰 𝒱) : CombEquiv 𝒱 𝒰 := by
  obtain ⟨U, E⟩ := 𝒰
  obtain ⟨W, F⟩ := 𝒱
  obtain ⟨h, hE⟩ := h
  obtain rfl : U = W := h
  exact ⟨rfl, hE.symm⟩

end Covering

/-! ### The site axioms -/

/-- **Isomorphism axiom.** For every isomorphism `f : V ⟶ U` the one-element family `{f}` is a
covering. That family is Mathlib's `PreZeroHypercover.singleton`. -/
@[sga "3 IV 4.2.5"]
def IsoCond (IsCov : Covering.{u, v, w} C → Prop) : Prop :=
  ∀ {U V : C} (f : V ⟶ U) [IsIso f], IsCov ⟨U, PreZeroHypercover.singleton.{w} f⟩

/-- **Composition axiom.** A covering `{Uᵢ ⟶ U}_{i ∈ I}` refined by coverings
`{Vᵢⱼ ⟶ Uᵢ}_{j ∈ Jᵢ}` composes to a covering `{Vᵢⱼ ⟶ U}_{(i, j) ∈ Σ i, Jᵢ}`. The composite is
Mathlib's `PreZeroHypercover.bind`, each `𝒱 i` first being pushed forward along the identification
of its target with `Uᵢ`. -/
@[sga "3 IV 4.2.5", sga "4 VI 8.3.7"]
def CompositionCond (IsCov : Covering.{u, v, w} C → Prop) : Prop :=
  ∀ 𝒰 : Covering C, IsCov 𝒰 →
  ∀ 𝒱 : 𝒰.2.I₀ → Covering C, (∀ i, IsCov (𝒱 i)) →
  ∀ h : ∀ i, (𝒱 i).1 = 𝒰.2.X i,
    IsCov ⟨𝒰.1, 𝒰.2.bind fun i => (𝒱 i).2.pushforward (eqToHom (h i))⟩

/-- **Base change axiom.** For a covering `{Uᵢ ⟶ U}_{i ∈ I}` and any `g : V ⟶ 𝒰.target` the
fibre products `Uᵢ ×_U V` exist and `{Uᵢ ×_U V ⟶ V}_{i ∈ I}` is a covering. Their existence is
expressed by exhibiting the objects and the projections together with `IsPullback`, so that no
`HasPullback` instance is assumed. -/
@[sga "3 IV 4.2.5", sga "4 II 1.3"]
def BaseChangeCond (IsCov : Covering.{u, v, w} C → Prop) : Prop :=
  ∀ 𝒰 : Covering C, IsCov 𝒰 →
  ∀ (V : C) (g : V ⟶ 𝒰.1),
    ∃ (P : 𝒰.2.I₀ → C) (π₁ : ∀ i, P i ⟶ 𝒰.2.X i) (π₂ : ∀ i, P i ⟶ V),
      (∀ i, IsPullback (π₁ i) (π₂ i) (𝒰.2.f i) g) ∧ IsCov ⟨V, ⟨𝒰.2.I₀, P, π₂⟩⟩

/-- A class of coverings is a *site* if it satisfies the isomorphism, composition and base
change axioms: these are axioms (1), (2) and (3) of Stacks 00VH, as `IsoCond`, `CompositionCond`
and `BaseChangeCond`. The set `Cov(𝒞)` is the predicate `IsCov`. The coverings are families of
morphisms with fixed target, indexed by a type (Stacks 0396), not presieves, so a family may
repeat a morphism. Following the clarification after 00VH, axiom (3) asks for the fibre products
`Uᵢ ×_U V` of the members of a covering only, and for the covering property of *some* choice of
them; no other fibre products are assumed to exist.

Mathlib's `CategoryTheory.Pretopology`, which also carries Stacks 00VH, is the special case of a
category with all pullbacks, with coverings recorded as presieves and base change taken along
the chosen pullbacks; `IsSite.pretopologyBigFppfPretopology` produces it from a site when `C` has
pullbacks. Conversely `CategoryTheory.Precoverage.isSite_presieve₀_mem` produces a site from a
Mathlib precoverage with `HasIsos`, `IsStableUnderComposition`, `IsStableUnderBaseChange` and
`HasPullbacks`. -/
@[sga "4 II 1.3", sga "3 IV 4.2.5",
  stacks 00VH "Stacks' definition of a site: no fibre products beyond those of axiom (3)."]
def IsSite (IsCov : Covering.{u, v, w} C → Prop) : Prop :=
  IsoCond IsCov ∧ CompositionCond IsCov ∧ BaseChangeCond IsCov

/-! ### Coverings with a bounded index set -/

/-- `CovBounded IsCov κ 𝒰` says that `𝒰` is a covering in `IsCov` whose index set has
cardinality at most `κ`. This is the class `Cov(C)_{κ, α}` of Stacks 000X *without* the `V_α`
truncation, so it is not set-sized in general; the truncated class is `CovTrunc`. -/
def CovBounded (IsCov : Covering.{u, v, w} C → Prop) (κ : Cardinal.{w}) (𝒰 : Covering C) : Prop :=
  IsCov 𝒰 ∧ #𝒰.2.I₀ ≤ κ

/-! ### Cardinal bounds -/

/-- A small set of coverings admits a cardinal bounding all of its index sets. -/
private lemma sup_cov0_card (Cov₀ : Set (Covering C)) [Small.{max u v} Cov₀] :
    ∃ κ₀ : Cardinal.{max u v}, ∀ 𝒰 ∈ Cov₀, #𝒰.2.I₀ ≤ κ₀ := by
  -- `le_sum` must be elaborated before the rewrite, or the summand is still a metavariable
  -- and `simp` has nothing to work on.
  refine ⟨sum fun s : Shrink Cov₀ => #((equivShrink Cov₀).symm s).val.2.I₀, fun 𝒰 h𝒰 => ?_⟩
  have h := le_sum (fun s : Shrink Cov₀ => #((equivShrink Cov₀).symm s).val.2.I₀)
    (equivShrink Cov₀ ⟨𝒰, h𝒰⟩)
  -- `equivShrink` is not `@[expose]`, so `simp` cannot see through it; rewrite by name.
  rwa [Equiv.symm_apply_apply] at h

/-- For an infinite cardinal `κ`, a `Σ`-type whose index set and whose fibres all have
cardinality at most `κ` again has cardinality at most `κ`. -/
private lemma sigma_card_le_of_le {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) {I : Type u} (hI : #I ≤ κ)
    {J : I → Type u} (hJ : ∀ i, #(J i) ≤ κ) : #(Σ i, J i) ≤ κ :=
  calc #(Σ i, J i) = sum fun i => #(J i) := mk_sigma J
    _ ≤ #I * κ := (sum_le_sum _ _ hJ).trans (by simp [sum_const])
    _ ≤ κ * κ := mul_le_mul' hI le_rfl
    _ = κ := mul_eq_self hκ

/-- Bounding the index set by an infinite cardinal preserves the isomorphism axiom, the
one-element index set being finite. -/
private lemma covBounded_isoCond {IsCov : Covering C → Prop} (hIso : IsoCond IsCov)
    {κ : Cardinal.{max u v}} (hκ : ℵ₀ ≤ κ) : IsoCond (CovBounded IsCov κ) :=
  fun f _ => ⟨hIso f, mk_punit.trans_le (one_le_aleph0.trans hκ)⟩

/-- Bounding the index set by an infinite cardinal preserves the composition axiom, the
composed family being indexed by a `Σ`-type all of whose parts are bounded by `κ`. -/
private lemma covBounded_compositionCond {IsCov : Covering C → Prop}
    (hComp : CompositionCond IsCov) {κ : Cardinal.{max u v}} (hκ : ℵ₀ ≤ κ) :
    CompositionCond (CovBounded IsCov κ) := by
  intro 𝒰 ⟨h𝒰_cov, h𝒰_card⟩ 𝒱 h𝒱 htargets
  choose h𝒱_cov h𝒱_card using h𝒱
  exact ⟨hComp 𝒰 h𝒰_cov 𝒱 h𝒱_cov htargets, sigma_card_le_of_le hκ h𝒰_card h𝒱_card⟩

/-- Bounding the index set preserves the base change axiom: base change leaves the index set
unchanged. -/
private lemma covBounded_baseChangeCond {IsCov : Covering C → Prop}
    (hBC : BaseChangeCond IsCov) {κ : Cardinal.{max u v}} :
    BaseChangeCond (CovBounded IsCov κ) := by
  intro 𝒰 ⟨h𝒰_cov, h𝒰_card⟩ V g
  obtain ⟨P, π₁, π₂, hpb, hcov⟩ := hBC 𝒰 h𝒰_cov V g
  exact ⟨P, π₁, π₂, hpb, hcov, h𝒰_card⟩

/-- Weakening the bound on a system of combinatorial representatives: if every covering in
`IsCov` is combinatorially equivalent to one whose index set has cardinality at most
`κ_rep ≤ κ`, then it is combinatorially equivalent to a member of `CovBounded IsCov κ`. -/
private lemma exists_bounded_combequiv_rep {IsCov : Covering C → Prop}
    {κ_rep κ : Cardinal.{max u v}} (hle : κ_rep ≤ κ)
    (hκ_rep : ∀ 𝒰 : Covering C, IsCov 𝒰 →
      ∃ 𝒰' : Covering C, IsCov 𝒰' ∧ #𝒰'.2.I₀ ≤ κ_rep ∧ Covering.CombEquiv 𝒰 𝒰')
    (𝒰 : Covering C) (h𝒰 : IsCov 𝒰) :
    ∃ 𝒰' : Covering C, CovBounded IsCov κ 𝒰' ∧ Covering.CombEquiv 𝒰 𝒰' := by
  obtain ⟨𝒰', hcov, hcard, hequiv⟩ := hκ_rep 𝒰 h𝒰
  exact ⟨𝒰', ⟨hcov, hcard.trans hle⟩, hequiv⟩

/-! ### Combinatorial representatives -/

/-- The combinatorial invariant of a covering: its target together with the *set* of its
`(source, morphism)` pairs. -/
private def arrowSet (𝒰 : Covering C) : Σ U : C, Set (Σ V : C, V ⟶ U) :=
  ⟨𝒰.1, Set.range fun i => (⟨𝒰.2.X i, 𝒰.2.f i⟩ : Σ V : C, V ⟶ 𝒰.1)⟩

/-- An equality of `Σ`-pairs in `Σ V : C, V ⟶ U` yields the equality of the two sources
*together with* the morphism equality transported along it. -/
private lemma sigma_hom_eq {U x y : C} {p : x ⟶ U} {q : y ⟶ U}
    (h : (⟨x, p⟩ : Σ V : C, V ⟶ U) = ⟨y, q⟩) : ∃ e : x = y, p = eqToHom e ≫ q := by
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp h
  exact ⟨rfl, by simpa using eq_of_heq h2⟩

/-- Two coverings with the same `arrowSet` are combinatorially equivalent in the sense of
Stacks 00VU (1). Membership of `𝒰`'s pairs in the range of `𝒱`'s gives, for each index, an
equality of `Σ`-pairs, hence both an equality of sources and the morphism equality over it. -/
private lemma combEquiv_of_arrowSet_eq (𝒰 𝒱 : Covering C) (heq : arrowSet 𝒰 = arrowSet 𝒱) :
    Covering.CombEquiv 𝒰 𝒱 := by
  obtain ⟨U, E⟩ := 𝒰
  obtain ⟨W, F⟩ := 𝒱
  simp only [arrowSet] at heq
  obtain rfl : U = W := congr_arg Sigma.fst heq
  simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at heq
  refine ⟨rfl, ?_, ?_⟩
  · choose a ha using fun i => heq.subset ⟨i, rfl⟩
    choose hsrc hhom using fun i => sigma_hom_eq (ha i).symm
    exact ⟨a, hsrc, hhom⟩
  · choose b hb using fun j => heq.symm.subset ⟨j, rfl⟩
    choose hsrc hhom using fun j => sigma_hom_eq (hb j).symm
    exact ⟨b, hsrc, hhom⟩

/-- Every covering in `IsCov` is combinatorially equivalent to one in `IsCov` whose index set
has cardinality at most some fixed `κ_rep`. Indeed a covering is determined up to combinatorial
equivalence by its `arrowSet`, and those range over the set-sized type
`Σ U : C, Set (Σ V : C, V ⟶ U)`, so summing the sizes of one chosen representative per value
gives a bound. -/
private lemma exists_rep_bound (IsCov : Covering C → Prop) :
    ∃ κ_rep : Cardinal.{max u v}, ∀ 𝒰 : Covering C, IsCov 𝒰 →
      ∃ 𝒰' : Covering C, IsCov 𝒰' ∧ #𝒰'.2.I₀ ≤ κ_rep ∧ Covering.CombEquiv 𝒰 𝒰' := by
  classical
  let repSize : (Σ U : C, Set (Σ V : C, V ⟶ U)) → Cardinal.{max u v} := fun c =>
    if h : ∃ 𝒰 : Covering C, IsCov 𝒰 ∧ arrowSet 𝒰 = c then #(Classical.choose h).2.I₀ else 0
  refine ⟨sum repSize, fun 𝒰 h𝒰 => ?_⟩
  have hclass : ∃ 𝒱 : Covering C, IsCov 𝒱 ∧ arrowSet 𝒱 = arrowSet 𝒰 := ⟨𝒰, h𝒰, rfl⟩
  obtain ⟨hcov, hclass_eq⟩ := Classical.choose_spec hclass
  exact ⟨Classical.choose hclass, hcov, (dite_eq_left hclass).symm.trans_le (le_sum repSize _),
    (combEquiv_of_arrowSet_eq (Classical.choose hclass) 𝒰 hclass_eq).symm⟩

/-! ### The main theorem -/

/-- The cardinality half of Stacks 000X. Let `IsCov` be a site on `C` and let `Cov₀` be a
set-sized family of coverings in it. Then there are a cardinal `κ` and a limit ordinal `α` such
that the coverings
in `IsCov` whose index set has cardinality at most `κ` again form a site, contain `Cov₀`, and
every covering in `IsCov` is combinatorially equivalent to one of them. One may take
`κ = ℵ₀ ⊔ κ₀ ⊔ κ_rep`, with `κ₀` bounding the index sets of `Cov₀` and `κ_rep` bounding those
of a system of combinatorial representatives, and `α = ω`.

The ordinal `α` is unconstrained, and the class `CovBounded IsCov κ` is not shown to be a set:
the `V_α` truncation of the source is missing. Stacks 000X with that truncation, the class being
proved `Small`, is `exists_covTrunc_isSite`. -/
theorem exists_covBounded_isSite
    {C : Type u} [Category.{v} C]
    (IsCov : Covering.{u, v, max u v} C → Prop)
    (hSite : IsSite IsCov)
    (Cov₀ : Set (Covering.{u, v, max u v} C))
    [hSmall : Small.{max u v} Cov₀]
    (hCov₀ : ∀ 𝒰 ∈ Cov₀, IsCov 𝒰) :
    ∃ (κ : Cardinal.{max u v}) (α : Ordinal.{max u v}),
      Order.IsSuccLimit α ∧
      (∀ 𝒰 ∈ Cov₀, CovBounded IsCov κ 𝒰) ∧
      IsSite (CovBounded IsCov κ) ∧
      (∀ 𝒰 : Covering C, IsCov 𝒰 →
        ∃ 𝒰' : Covering C,
          CovBounded IsCov κ 𝒰' ∧ Covering.CombEquiv 𝒰 𝒰') := by
  obtain ⟨κ₀, hκ₀⟩ := sup_cov0_card Cov₀
  obtain ⟨κ_rep, hκ_rep⟩ := exists_rep_bound IsCov
  obtain ⟨hIso, hComp, hBC⟩ := hSite
  have hκ : ℵ₀ ≤ ℵ₀ ⊔ κ₀ ⊔ κ_rep := le_sup_left.trans le_sup_left
  exact ⟨ℵ₀ ⊔ κ₀ ⊔ κ_rep, Ordinal.omega0, Ordinal.isSuccLimit_omega0,
    fun 𝒰 h𝒰 => ⟨hCov₀ 𝒰 h𝒰, (hκ₀ 𝒰 h𝒰).trans (le_sup_of_le_left le_sup_right)⟩,
    ⟨covBounded_isoCond hIso hκ, covBounded_compositionCond hComp hκ,
      covBounded_baseChangeCond hBC⟩,
    exists_bounded_combequiv_rep le_sup_right hκ_rep⟩
