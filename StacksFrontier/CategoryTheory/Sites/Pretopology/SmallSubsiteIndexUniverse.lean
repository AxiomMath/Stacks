module

public import StacksFrontier.CategoryTheory.Sites.Pretopology.SmallSubsite
import all StacksFrontier.CategoryTheory.Sites.Pretopology.SmallSubsite

/-!
# Small subsites with index sets in a larger universe

The cardinality half of Stacks 000X for coverings whose index sets lie in any universe
`Type (max u v w)` at least as large as that of the objects and morphisms of `C`:
`exists_covBounded_isSite_of_univ`. The case `w = 0` is `exists_covBounded_isSite`. As there, the
class `CovBounded IsCov κ` is not shown to be a set; Stacks 000X with the `V_α` truncation is
`exists_covTrunc_isSite`.

## References

* [Stacks Project, Tag 000X](https://stacks.math.columbia.edu/tag/000X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u v w

variable {C : Type u} [Category.{v} C]

/-! ### Cardinal bounds -/

/-- A small set of coverings admits a cardinal bounding all of its index sets. -/
private lemma sup_cov0_card_univ (Cov₀ : Set (Covering C)) [Small.{max u v w} Cov₀] :
    ∃ κ₀ : Cardinal.{max u v w}, ∀ 𝒰 ∈ Cov₀, #𝒰.2.I₀ ≤ κ₀ := by
  -- `le_sum` must be elaborated before the rewrite, or the summand is still a metavariable
  -- and `simp` has nothing to work on.
  refine ⟨sum fun s : Shrink Cov₀ => #((equivShrink Cov₀).symm s).val.2.I₀, fun 𝒰 h𝒰 => ?_⟩
  have h := le_sum (fun s : Shrink Cov₀ => #((equivShrink Cov₀).symm s).val.2.I₀)
    (equivShrink Cov₀ ⟨𝒰, h𝒰⟩)
  -- `equivShrink` is not `@[expose]`, so `simp` cannot see through it; rewrite by name.
  rwa [Equiv.symm_apply_apply] at h

/-- Bounding the index set by an infinite cardinal preserves the isomorphism axiom, the
one-element index set being finite. -/
private lemma covBounded_isoCond_univ {IsCov : Covering C → Prop} (hIso : IsoCond IsCov)
    {κ : Cardinal.{max u v w}} (hκ : ℵ₀ ≤ κ) : IsoCond (CovBounded IsCov κ) := by
  intro U V f _
  exact ⟨hIso f, mk_punit.trans_le (one_le_aleph0.trans hκ)⟩

/-- Bounding the index set by an infinite cardinal preserves the composition axiom, the
composed family being indexed by a `Σ`-type all of whose parts are bounded by `κ`. -/
private lemma covBounded_compositionCond_univ {IsCov : Covering C → Prop}
    (hComp : CompositionCond IsCov) {κ : Cardinal.{max u v w}} (hκ : ℵ₀ ≤ κ) :
    CompositionCond (CovBounded IsCov κ) := by
  intro 𝒰 ⟨h𝒰_cov, h𝒰_card⟩ 𝒱 h𝒱 htargets
  choose h𝒱_cov h𝒱_card using h𝒱
  exact ⟨hComp 𝒰 h𝒰_cov 𝒱 h𝒱_cov htargets, sigma_card_le_of_le hκ h𝒰_card h𝒱_card⟩

/-- Bounding the index set preserves the base change axiom: base change leaves the index set
unchanged. -/
private lemma covBounded_baseChangeCond_univ {IsCov : Covering C → Prop}
    (hBC : BaseChangeCond IsCov) {κ : Cardinal.{max u v w}} :
    BaseChangeCond (CovBounded IsCov κ) := by
  intro 𝒰 ⟨h𝒰_cov, h𝒰_card⟩ V g
  obtain ⟨P, π₁, π₂, hpb, hcov⟩ := hBC 𝒰 h𝒰_cov V g
  exact ⟨P, π₁, π₂, hpb, hcov, h𝒰_card⟩

/-- Weakening the bound on a system of combinatorial representatives: if every covering in
`IsCov` is combinatorially equivalent to one whose index set has cardinality at most
`κ_rep ≤ κ`, then it is combinatorially equivalent to a member of `CovBounded IsCov κ`. -/
private lemma exists_bounded_combequiv_rep_univ {IsCov : Covering C → Prop}
    {κ_rep κ : Cardinal.{max u v w}} (hle : κ_rep ≤ κ)
    (hκ_rep : ∀ 𝒰 : Covering C, IsCov 𝒰 →
      ∃ 𝒰' : Covering C, IsCov 𝒰' ∧ #𝒰'.2.I₀ ≤ κ_rep ∧ Covering.CombEquiv 𝒰 𝒰')
    (𝒰 : Covering C) (h𝒰 : IsCov 𝒰) :
    ∃ 𝒰' : Covering C, CovBounded IsCov κ 𝒰' ∧ Covering.CombEquiv 𝒰 𝒰' := by
  obtain ⟨𝒰', hcov, hcard, hequiv⟩ := hκ_rep 𝒰 h𝒰
  exact ⟨𝒰', ⟨hcov, hcard.trans hle⟩, hequiv⟩

/-! ### Combinatorial representatives -/

/-- Every covering in `IsCov` is combinatorially equivalent to one in `IsCov` whose index set
has cardinality at most some fixed `κ_rep`. Indeed a covering is determined up to combinatorial
equivalence by its `arrowSet`, and those range over the set-sized type
`Σ U : C, Set (Σ V : C, V ⟶ U)`, so summing the sizes of one chosen representative per value
gives a bound. -/
private lemma exists_rep_bound_univ (IsCov : Covering C → Prop) :
    ∃ κ_rep : Cardinal.{max u v w}, ∀ 𝒰 : Covering C, IsCov 𝒰 →
      ∃ 𝒰' : Covering C, IsCov 𝒰' ∧ #𝒰'.2.I₀ ≤ κ_rep ∧ Covering.CombEquiv 𝒰 𝒰' := by
  classical
  let ClassIdx := Σ U : C, Set (Σ V : C, V ⟶ U)
  let repSize : ClassIdx → Cardinal.{max u v w} := fun c =>
    if h : ∃ 𝒰 : Covering C, IsCov 𝒰 ∧ arrowSet 𝒰 = c then #(Classical.choose h).2.I₀ else 0
  refine ⟨sum repSize, fun 𝒰 h𝒰 => ?_⟩
  have hclass : ∃ 𝒱 : Covering C, IsCov 𝒱 ∧ arrowSet 𝒱 = arrowSet 𝒰 := ⟨𝒰, h𝒰, rfl⟩
  obtain ⟨hcov, hclass_eq⟩ := Classical.choose_spec hclass
  refine ⟨Classical.choose hclass, hcov, ?_,
    (combEquiv_of_arrowSet_eq (Classical.choose hclass) 𝒰 hclass_eq).symm⟩
  calc #(Classical.choose hclass).2.I₀ = repSize (arrowSet 𝒰) := by
        simp only [repSize]
        rw [dite_eq_left hclass]
    _ ≤ sum repSize := le_sum repSize (arrowSet 𝒰)

/-! ### The main theorem -/

/-- The cardinality half of Stacks 000X. Let `IsCov` be a site on `C` and let `Cov₀` be a
set-sized family of coverings in it. Then there are a cardinal `κ` and a limit ordinal `α` such
that the coverings
in `IsCov` whose index set has cardinality at most `κ` again form a site, contain `Cov₀`, and
every covering in `IsCov` is combinatorially equivalent to one of them. One may take
`κ = ℵ₀ ⊔ κ₀ ⊔ κ_rep`, with `κ₀` bounding the index sets of `Cov₀` and `κ_rep` bounding those
of a system of combinatorial representatives, and `α = ω`.

This is the form with index sets in any universe `Type (max u v w)` at least as large as the
universe of the objects and morphisms of `C`; `exists_covBounded_isSite` is its case `w = 0`.
The ordinal `α` is unconstrained and the class is not shown to be a set; the truncated form is
`exists_covTrunc_isSite`. -/
theorem exists_covBounded_isSite_of_univ
    {C : Type u} [Category.{v} C]
    (IsCov : Covering.{u, v, max u v w} C → Prop)
    (hSite : IsSite IsCov)
    (Cov₀ : Set (Covering.{u, v, max u v w} C))
    [hSmall : Small.{max u v w} Cov₀]
    (hCov₀ : ∀ 𝒰 ∈ Cov₀, IsCov 𝒰) :
    ∃ (κ : Cardinal.{max u v w}) (α : Ordinal.{max u v w}),
      Order.IsSuccLimit α ∧
      (∀ 𝒰 ∈ Cov₀, CovBounded IsCov κ 𝒰) ∧
      IsSite (CovBounded IsCov κ) ∧
      (∀ 𝒰 : Covering C, IsCov 𝒰 →
        ∃ 𝒰' : Covering C,
          CovBounded IsCov κ 𝒰' ∧ Covering.CombEquiv 𝒰 𝒰') := by
  obtain ⟨κ₀, hκ₀⟩ := sup_cov0_card_univ Cov₀
  obtain ⟨κ_rep, hκ_rep⟩ := exists_rep_bound_univ IsCov
  obtain ⟨hIso, hComp, hBC⟩ := hSite
  have hκ : ℵ₀ ≤ ℵ₀ ⊔ κ₀ ⊔ κ_rep := le_sup_left.trans le_sup_left
  exact ⟨ℵ₀ ⊔ κ₀ ⊔ κ_rep, Ordinal.omega0, Ordinal.isSuccLimit_omega0,
    fun 𝒰 h𝒰 => ⟨hCov₀ 𝒰 h𝒰, (hκ₀ 𝒰 h𝒰).trans (le_sup_of_le_left le_sup_right)⟩,
    ⟨covBounded_isoCond_univ hIso hκ, covBounded_compositionCond_univ hComp hκ,
      covBounded_baseChangeCond_univ hBC⟩,
    exists_bounded_combequiv_rep_univ le_sup_right hκ_rep⟩
