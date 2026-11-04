module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfSpaceSiteOfBigEtale

/-!
# Big fppf sites of algebraic spaces exist over every big fppf site of schemes

For every big fppf site of schemes `B` containing a scheme `S` there is a big fppf site of
algebraic spaces over `S` (Stacks 0DBV) whose chosen big fppf site of schemes is `B`: take no
initial coverings and the covering bound that Stacks 000X supplies for the fppf covering families
of algebraic spaces, which satisfy the site axioms by
`AlgebraicGeometry.Space.isSite_isFppfCoveringFamily`.

## Main definitions

* `AlgebraicGeometry.BigFppfSpaceSite.ofSchemeSite`: the big fppf site of algebraic spaces over
  `S` built on a prescribed big fppf site of schemes `B` containing `S`.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.schemeSite_ofSchemeSite`,
  `AlgebraicGeometry.BigFppfSpaceSite.scheme_mem_ofSchemeSite`: its scheme site is `B`, and the
  membership proof is the given one, both by `rfl`.
* `AlgebraicGeometry.BigFppfSpaceSite.exists_schemeSite_eq`: the existence statement.
* `AlgebraicGeometry.BigFppfSpaceSite.of_forall`: a statement about the scheme site of every big
  fppf site of algebraic spaces over `S` holds for every big fppf site of schemes containing `S`.

## References

* [Stacks Project, Tag 000X](https://stacks.math.columbia.edu/tag/000X)
* [Stacks Project, Tag 0DBV](https://stacks.math.columbia.edu/tag/0DBV)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.BigFppfSpaceSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Stacks 000X for the fppf covering families of the algebraic spaces over `S` presented by a
big fppf site of schemes `B`, with no initial coverings and index sets in the universe used by
big fppf sites of algebraic spaces. -/
theorem exists_covBounded_isSite_isFppfCoveringFamily_of_schemeSite :
    ∃ (κ : Cardinal.{u + 2}) (α : Ordinal.{u + 2}), Order.IsSuccLimit α ∧
      (∀ 𝒰 ∈ (∅ : Set (Covering.{_, _, u + 2} (AlgebraicSpaces B S hS))),
        CovBounded (Space.IsFppfCoveringFamily B S hS) κ 𝒰) ∧
      IsSite (CovBounded (Space.IsFppfCoveringFamily B S hS) κ) ∧
      (∀ 𝒰 : Covering (AlgebraicSpaces B S hS), Space.IsFppfCoveringFamily B S hS 𝒰 →
        ∃ 𝒰', CovBounded (Space.IsFppfCoveringFamily B S hS) κ 𝒰' ∧
          Covering.CombEquiv 𝒰 𝒰') :=
  exists_covBounded_isSite_of_univ.{_, _, u + 2} (Space.IsFppfCoveringFamily B S hS)
    (Space.isSite_isFppfCoveringFamily B S hS) ∅ (by intro U hU; cases hU)

/-- **A big fppf site of algebraic spaces over `S` on a prescribed big fppf site of schemes `B`
containing `S`**, with no initial coverings and the covering bound of Stacks 000X. -/
noncomputable def ofSchemeSite : BigFppfSpaceSite S :=
  let h := exists_covBounded_isSite_isFppfCoveringFamily_of_schemeSite B S hS
  { schemeSite := B
    scheme_mem := hS
    initialCoverings := ∅
    initialCoverings_small := inferInstance
    initialCoverings_fppf := by simp
    coveringBound := h.choose
    coveringOrdinal := h.choose_spec.choose
    coveringOrdinal_isSuccLimit := h.choose_spec.choose_spec.1
    initialCoverings_bounded := by simp
    coverings_isSite := h.choose_spec.choose_spec.2.2.1
    covering_representative := h.choose_spec.choose_spec.2.2.2 }

/-- The big fppf site of schemes of `ofSchemeSite B S hS` is `B`. -/
@[simp]
theorem schemeSite_ofSchemeSite : (ofSchemeSite B S hS).schemeSite = B :=
  rfl

/-- The membership proof of `ofSchemeSite B S hS` is `hS`. -/
theorem scheme_mem_ofSchemeSite : (ofSchemeSite B S hS).scheme_mem = hS :=
  rfl

/-- **Every big fppf site of schemes containing `S` is the scheme site of a big fppf site of
algebraic spaces over `S`**, with the given membership proof. -/
theorem exists_schemeSite_eq :
    ∃ T : BigFppfSpaceSite S, T.schemeSite = B ∧ HEq T.scheme_mem hS :=
  ⟨ofSchemeSite B S hS, rfl, HEq.rfl⟩

/-- A property of a big fppf site of schemes containing `S` and of the membership proof that
holds for the scheme site of every big fppf site of algebraic spaces over `S` holds for every big
fppf site of schemes containing `S`. -/
theorem of_forall {P : ∀ B : BigFppfSite.{u}, B.Contains S → Prop}
    (h : ∀ T : BigFppfSpaceSite S, P T.schemeSite T.scheme_mem) : P B hS :=
  h (ofSchemeSite B S hS)

end AlgebraicGeometry.BigFppfSpaceSite

end
