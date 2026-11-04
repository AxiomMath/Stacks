module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoproduct
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
public import Mathlib.SetTheory.Cardinal.Aleph

/-!
# The cutoff axioms and the cofinality hypothesis of a coproduct index

`AlgebraicGeometry.BigFppfSite.AdmitsCoproductIndex` bounds an index type by the *cofinality*
of the size cutoff, which is stronger than bounding it by the cutoff itself. This file measures
the gap between the two in the only terms the axioms of
`AlgebraicGeometry.BigFppfSite` provide.

Two facts, in opposite directions.

* If the cutoff is a *regular* cardinal then the two bounds coincide, so the cofinality
  hypothesis is implied by `#I < B.cutoff` and can be dropped:
  `AlgebraicGeometry.BigFppfSite.admitsCoproductIndex_of_isRegular_cutoff`. But regularity is
  not a free assumption: a regular cutoff is an *inaccessible* cardinal, by
  `AlgebraicGeometry.BigFppfSite.isInaccessible_cutoff_of_isRegular`, since the cutoff is
  already uncountable and a strong prelimit. No inaccessible cardinal is provable to exist in
  `Type u`, whereas `AlgebraicGeometry.BigFppfSite.exists_containing` constructs a big fppf
  site containing any prescribed small set of schemes outright.

* The axioms do not imply regularity: `AlgebraicGeometry.exists_cutoff_isSingular` exhibits a
  cardinal satisfying all three cardinal axioms of a big fppf site — uncountable, a strong
  prelimit, of uncountable cofinality — which is nevertheless singular, namely the beth number
  `ℶ_{ω₁}`, whose cofinality is `ℵ₁`. For such a cutoff
  `AlgebraicGeometry.exists_cutoff_not_lt_cof` produces an index type of cardinality below the
  cutoff which is *not* below its cofinality, so the hypothesis genuinely cuts: it is not an
  artefact of the proof but a restriction on the index type that the cutoff axioms permit to
  bite.

## Main results

* `AlgebraicGeometry.BigFppfSite.admitsCoproductIndex_of_isRegular_cutoff`
* `AlgebraicGeometry.BigFppfSite.isInaccessible_cutoff_of_isRegular`
* `AlgebraicGeometry.exists_cutoff_isSingular`
* `AlgebraicGeometry.exists_cutoff_not_lt_cof`

## References

* [Stacks Project, Tag 000J](https://stacks.math.columbia.edu/tag/000J)
* [Stacks Project, Tag 021R](https://stacks.math.columbia.edu/tag/021R)
* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
-/

@[expose] public section

open Cardinal Ordinal

universe u v

namespace AlgebraicGeometry

/-- **A regular cutoff makes the cofinality hypothesis vacuous.** If the size cutoff of a big
fppf site is a regular cardinal then it equals its own cofinality, so an index type of
cardinality below the cutoff is admissible as a coproduct index. -/
public theorem BigFppfSite.admitsCoproductIndex_of_isRegular_cutoff (B : BigFppfSite.{u})
    (hreg : B.cutoff.IsRegular) (I : Type v) [Small.{u} I]
    (hI : #(Shrink.{u} I) < B.cutoff) : B.AdmitsCoproductIndex I :=
  ⟨by rwa [hreg.cof_ord]⟩

/-- **A regular cutoff is an inaccessible cardinal.** The cutoff of a big fppf site is
uncountable and a strong prelimit by `AlgebraicGeometry.BigFppfSite.aleph0_lt_cutoff` and
`AlgebraicGeometry.BigFppfSite.cutoff_isStrongPrelimit`, so adding regularity to the axioms
amounts to postulating an inaccessible cardinal in `Type u`. -/
public theorem BigFppfSite.isInaccessible_cutoff_of_isRegular (B : BigFppfSite.{u})
    (hreg : B.cutoff.IsRegular) : Cardinal.IsInaccessible B.cutoff :=
  ⟨B.aleph0_lt_cutoff, hreg.le_cof_ord, B.cutoff_isStrongPrelimit⟩

/-- **A singular cardinal satisfying every cardinal axiom of a big fppf site**, namely the beth
number `ℶ_{ω₁}`: uncountable, a strong prelimit, and of cofinality `ℵ₁`, which is below it. -/
public noncomputable def singularCutoff : Cardinal.{u} :=
  Cardinal.preBeth (ω₁ : Ordinal.{u})

/-- `ω₁` is a limit ordinal, hence a successor prelimit. -/
private theorem isSuccPrelimit_omega_one : Order.IsSuccPrelimit (ω₁ : Ordinal.{u}) :=
  (isSuccLimit_omega 1).isSuccPrelimit

/-- `ℶ_{ω₁}` is the supremum of the beth numbers `ℶ_a` for `a < ω₁`. -/
private theorem singularCutoff_eq_iSup : singularCutoff.{u} =
    ⨆ a : Set.Iio (ω₁ : Ordinal.{u}), Cardinal.preBeth (a : Ordinal.{u}) := by
  rw [singularCutoff, Cardinal.preBeth_limit isSuccPrelimit_omega_one]

/-- `ℶ_{ω₁}` is uncountable. -/
public theorem aleph0_lt_singularCutoff : ℵ₀ < singularCutoff.{u} := by
  rw [singularCutoff, ← Cardinal.preBeth_omega]
  exact Cardinal.preBeth_strictMono omega0_lt_omega_one

/-- `ℶ_{ω₁}` is a strong prelimit, `ω₁` being a limit ordinal. -/
public theorem isStrongPrelimit_singularCutoff :
    Cardinal.IsStrongPrelimit singularCutoff.{u} :=
  Cardinal.isStrongPrelimit_preBeth.2 isSuccPrelimit_omega_one

/-- `ℶ_{ω₁}` is the supremum of the beth numbers below it, read on ordinals. -/
public theorem ord_singularCutoff :
    singularCutoff.{u}.ord =
      ⨆ a : Set.Iio (ω₁ : Ordinal.{u}), (Cardinal.preBeth (a : Ordinal.{u})).ord := by
  rw [singularCutoff_eq_iSup, Ordinal.iSup_ord]

/-- The cofinality of `ℶ_{ω₁}` is `ℵ₁`: the beth function is normal, so it carries the
cofinality of `ω₁` to its value there. -/
public theorem cof_ord_singularCutoff :
    singularCutoff.{u}.ord.cof = ℵ₁ := by
  rw [ord_singularCutoff, cof_iSup_Iio
    (f := fun a : Set.Iio (ω₁ : Ordinal.{u}) => (Cardinal.preBeth (a : Ordinal.{u})).ord)
    (fun a b hab => Cardinal.ord_lt_ord.2 (Cardinal.preBeth_strictMono hab))
    isSuccPrelimit_omega_one]
  exact Cardinal.isRegular_aleph_one.cof_omega_eq

/-- `ℵ₁` is below `ℶ_{ω₁}`, which is therefore singular: `ℵ₁ ≤ 2 ^ ℵ₀` and the cutoff is a
strong prelimit above `ℵ₀`. -/
public theorem aleph_one_lt_singularCutoff : ℵ₁ < singularCutoff.{u} := by
  refine lt_of_le_of_lt ?_ (isStrongPrelimit_singularCutoff.{u}
    aleph0_lt_singularCutoff)
  rw [← Cardinal.succ_aleph0]
  exact Order.succ_le_of_lt (Cardinal.cantor ℵ₀)

/-- **The beth numbers below `ℶ_{ω₁}` are cofinal in it.** Every cardinal below the witness is
below `ℶ_a` for some `a < ω₁`; this is what makes a family indexed by `ω₁` able to exhaust the
cutoff. -/
public theorem exists_lt_preBeth_of_lt_singularCutoff {κ : Cardinal.{u}}
    (hκ : κ < singularCutoff.{u}) :
    ∃ a : Set.Iio (ω₁ : Ordinal.{u}), κ < Cardinal.preBeth (a : Ordinal.{u}) := by
  rw [singularCutoff_eq_iSup] at hκ
  exact exists_lt_of_lt_ciSup' hκ

/-- **The canonical `u`-small copy of `ω₁` has cardinality `ℵ₁`.** The index type of the
cofinal family of `AlgebraicGeometry.exists_lt_preBeth_of_lt_singularCutoff` lives in
`Type (u+1)`; this reads its cardinality on the `u`-small copy that
`AlgebraicGeometry.BigFppfSite.AdmitsCoproductIndex` and
`AlgebraicGeometry.BigFppfSite.contains_sigma` use. -/
public theorem mk_shrink_Iio_omega_one :
    #(Shrink.{u} (Set.Iio (ω₁ : Ordinal.{u}))) = ℵ₁ := by
  have h : Cardinal.lift.{u + 1} #(Shrink.{u} (Set.Iio (ω₁ : Ordinal.{u}))) =
      Cardinal.lift.{u + 1} (ℵ₁ : Cardinal.{u}) := by
    rw [Cardinal.lift_mk_shrink'', Cardinal.mk_Iio_ordinal, Ordinal.card_omega]
  exact Cardinal.lift_inj.mp h

/-- **The cardinal axioms of a big fppf site permit a singular cutoff.** There is a cardinal
which is uncountable, a strong prelimit and of uncountable cofinality — the three conditions
`AlgebraicGeometry.BigFppfSite` imposes on its cutoff — and whose cofinality is nevertheless
strictly below it, namely `ℶ_{ω₁}`, of cofinality `ℵ₁`.

So the axioms do not imply that the cutoff is regular, and the cofinality bound of
`AlgebraicGeometry.BigFppfSite.AdmitsCoproductIndex` is not a consequence of `#I < B.cutoff`
for a general big fppf site. -/
public theorem exists_cutoff_isSingular :
    ∃ κ : Cardinal.{u}, ℵ₀ < κ ∧ Cardinal.IsStrongPrelimit κ ∧ ℵ₀ < κ.ord.cof ∧
      κ.ord.cof < κ :=
  ⟨singularCutoff.{u}, aleph0_lt_singularCutoff,
    isStrongPrelimit_singularCutoff,
    cof_ord_singularCutoff.{u} ▸ Cardinal.aleph0_lt_aleph_one,
    cof_ord_singularCutoff.{u} ▸ aleph_one_lt_singularCutoff⟩

/-- **An index type below a permitted cutoff need not be below its cofinality.** For the
cutoff of `AlgebraicGeometry.exists_cutoff_isSingular` the type of cardinality equal to the
cofinality has cardinality below the cutoff and is not admissible as a coproduct index.

This is the exact gap between the hypothesis `#I < B.cutoff`, which both sides of Stacks 0ADK
need in order to be formed at all, and the hypothesis
`AlgebraicGeometry.BigFppfSite.AdmitsCoproductIndex`, which the construction of the coproduct
consumes. -/
public theorem exists_cutoff_not_lt_cof :
    ∃ (κ : Cardinal.{u}) (I : Type u), ℵ₀ < κ ∧ Cardinal.IsStrongPrelimit κ ∧
      ℵ₀ < κ.ord.cof ∧ #I < κ ∧ ¬ #I < κ.ord.cof := by
  obtain ⟨κ, h₀, h₁, h₂, h₃⟩ := exists_cutoff_isSingular.{u}
  refine ⟨κ, κ.ord.cof.out, h₀, h₁, h₂, ?_, ?_⟩
  · rwa [Cardinal.mk_out]
  · rw [Cardinal.mk_out]
    exact lt_irrefl _

end AlgebraicGeometry

end
