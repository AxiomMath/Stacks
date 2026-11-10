module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.SmoothCapFundamentalProduct
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TotalClassPieces
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TotalClassRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFundamentalClass
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.FundamentalClass
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.GysinAtInfinityRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.ModificationComparison
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.RegularImmersionDeformationTop

/-!
# The map `c ↦ c ∩ [X]_d` on a decomposition into open and closed pieces

Let `X` be locally of finite type over the base of chapter 42 of the Stacks Project and let
`X = ∐_i X_i` be a decomposition into open and closed subschemes. Stacks 0FDZ identifies
`A^p(X)` with `∏_i A^p(X_i)` (the components being the restriction maps of Stacks 0B7F), and the
Chow groups decompose likewise, `CH_k(X) = ∏_i CH_k(X_i)`. This file shows that the operational
action `β ↦ c ∩ β` of `A^p(X)` on `CH_*(X)`, and with it the map

  `Θ : A^p(X) ⟶ CH_{d-p}(X)`,   `c ↦ c ∩ [X]_d`,

of Stacks 0FC2 and Stacks 0FCB, are compatible with these decompositions, and deduces that `Θ` is
bijective as soon as it is bijective on every piece.

## Main results

* `Stacks.Chow.chowGroupRestrict_chowCohomologyCap_eq_restriction` — `(c ∩ β)|_U = c|_U ∩ β|_U`
  for an open subscheme `U ⊆ X`.
* `Stacks.Chow.chowGroupRestrict_chowCohomologyCapFundamentalClass` —
  `Θ_X(c)|_U = Θ_U(c|_U)` when `dim_δ X ≤ d`.
* `Stacks.Chow.chowCohomologyComponent_eq_of_restriction_eq`,
  `Stacks.Chow.exists_chowCohomologyComponent_restriction_eq` — Stacks 0FDZ for the identity of
  `X`, in one degree, read through the restriction maps of Stacks 0B7F.
* `Stacks.Chow.chowCohomologyCapFundamentalClass_bijective_of_isClopenDecomposition` — `Θ_X` is
  bijective when every `Θ_{X_i}` is.

## References

* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0B7F](https://stacks.math.columbia.edu/tag/0B7F)
* [Stacks Project, Tag 0FCB](https://stacks.math.columbia.edu/tag/0FCB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-! ### The cap action under restriction to an open subscheme -/

section Restrict

variable (U : X.Opens) (p : ℤ)

/-- **The cap action of `A^p(X)` commutes with restriction to an open subscheme.** For
`c ∈ A^p(X)`, an open `U ⊆ X` and `β ∈ CH_k(X)`,

  `(c ∩ β)|_U = c|_U ∩ β|_U`   in   `CH_{k-p}(U)`,

where `c|_U` is the restriction of Stacks 0B7F. -/
theorem chowGroupRestrict_chowCohomologyCap_eq_restriction
    (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p) (k : ℤ)
    (β : chowGroup C sX k) :
    chowGroupRestrict C sX (U.ι ≫ sX) U.ι rfl (k - p)
        (chowCohomologyCap C (gysinSystemOfInvertible C) sX p c k β) =
      chowCohomologyCap C (gysinSystemOfInvertible C) (U.ι ≫ sX) p
        (chowCohomologyRestrictionOfInvertible C sX U.ι p c) k
        (chowGroupRestrict C sX (U.ι ≫ sX) U.ι rfl k β) := by
  set β' := chowGroupCongr C (Category.id_comp sX).symm k β
  have hL : chowGroupRestrict C sX (U.ι ≫ sX) U.ι rfl (k - p)
        (chowCohomologyCap C (gysinSystemOfInvertible C) sX p c k β) ≍
      c.idRule C sX (gysinSystemOfInvertible C) U.ι k
        (chowGroupRestrict C (𝟙 X ≫ sX) (U.ι ≫ sX) U.ι (by rw [Category.id_comp]) k β') :=
    (chowGroupRestrict_heq_of_eq C U.ι U.ι (Category.id_comp sX).symm rfl rfl _ _ rfl _ _
      (chowCohomologyCap_heq_idRule_ofGysinSystem C (gysinSystemOfInvertible C) sX p c k β)).trans
      (heq_of_eq (c.idRule_chowGroupRestrict (𝟙 X) U.ι U.ι (Category.comp_id _) k β'))
  have hR : chowCohomologyCap C (gysinSystemOfInvertible C) (U.ι ≫ sX) p
        (chowCohomologyRestrictionOfInvertible C sX U.ι p c) k
        (chowGroupRestrict C sX (U.ι ≫ sX) U.ι rfl k β) ≍
      c.idRule C sX (gysinSystemOfInvertible C) U.ι k
        (chowGroupRestrict C (𝟙 X ≫ sX) (U.ι ≫ sX) U.ι (by rw [Category.id_comp]) k β') := by
    refine (chowCohomologyCap_heq_idRule_ofGysinSystem C (gysinSystemOfInvertible C) (U.ι ≫ sX) p
      _ k _).trans ?_
    refine (BivariantClass.idRule_chowCohomologyRestriction_heq U.ι c (𝟙 _) k _
      (chowGroupCongr C (Category.assoc (𝟙 _) U.ι sX).symm k
        (chowGroupCongr C (Category.id_comp (U.ι ≫ sX)).symm k
          (chowGroupRestrict C sX (U.ι ≫ sX) U.ι rfl k β)))
      (chowGroupCongr_heq C _ k _).symm).trans ?_
    refine BivariantClass.idRule_heq_congr c (Category.id_comp U.ι) k _ _ ?_
    refine ((chowGroupCongr_heq C _ k _).trans (chowGroupCongr_heq C _ k _)).trans ?_
    exact chowGroupRestrict_heq_of_eq C U.ι U.ι (Category.id_comp sX).symm rfl rfl _ _ rfl _ _
      (chowGroupCongr_heq C _ k β).symm
  exact eq_of_heq (hL.trans hR.symm)

/-- **The map `c ↦ c ∩ [X]_d` commutes with restriction to an open subscheme.** If
`dim_δ X ≤ d`, then `[X]_d|_U = [U]_d`, and so `Θ_X(c)|_U = Θ_U(c|_U)` for `c ∈ A^p(X)`. -/
theorem chowGroupRestrict_chowCohomologyCapFundamentalClass (d : ℤ)
    (hdim : schemeDeltaDimension C sX ≤ (d : EInt))
    (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p) :
    chowGroupRestrict C sX (U.ι ≫ sX) U.ι rfl (d - p)
        (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX d p c) =
      chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) (U.ι ≫ sX) d p
        (chowCohomologyRestrictionOfInvertible C sX U.ι p c) := by
  rw [← chowCohomologyCap_fundamentalChowClass, ← chowCohomologyCap_fundamentalChowClass,
    chowGroupRestrict_chowCohomologyCap_eq_restriction,
    chowGroupRestrict_fundamentalChowClass C sX (U.ι ≫ sX) U.ι rfl d hdim]

end Restrict

/-! ### Stacks 0FDZ for the identity, in one degree -/

section Pieces

variable {C sX} {I : Type u} {U : I → X.Opens} (hU : IsClopenDecomposition U) (p : ℤ)

include hU in
/-- **A class of `A^p(X)` is determined by its restrictions to the pieces** of a decomposition of
`X` into open and closed subschemes: Stacks 0FDZ for the identity of `X`, read through the
restriction maps of Stacks 0B7F. -/
theorem chowCohomologyComponent_eq_of_restriction_eq
    {c d : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p}
    (h : ∀ i, chowCohomologyRestrictionOfInvertible C sX (U i).ι p c =
      chowCohomologyRestrictionOfInvertible C sX (U i).ι p d) : c = d := by
  refine (bivariantPieceEquivOfInvertible C sX sX (𝟙 X) (Category.id_comp sX) p U U id
    (opens_le_preimage_id U) hU).injective (funext fun i ↦ ?_)
  refine (pieceIdentityCongr C (gysinSystemOfInvertible C) sX U (opens_le_preimage_id U) p
    i _).injective ?_
  simp only [bivariantPieceEquivOfInvertible_apply]
  rw [← chowCohomologyRestriction_eq_pieceIdentityCongr,
    ← chowCohomologyRestriction_eq_pieceIdentityCongr]
  exact h i

include hU in
/-- **Classes on the pieces glue** to a class of `A^p(X)` with the given restrictions, for a
decomposition of `X` into open and closed subschemes: Stacks 0FDZ for the identity of `X`. -/
theorem exists_chowCohomologyComponent_restriction_eq
    (e : ∀ i, chowCohomologyComponent C (gysinSystemOfInvertible C) ((U i).ι ≫ sX) p) :
    ∃ c : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p,
      ∀ i, chowCohomologyRestrictionOfInvertible C sX (U i).ι p c = e i := by
  refine ⟨(bivariantPieceEquivOfInvertible C sX sX (𝟙 X) (Category.id_comp sX) p U U id
    (opens_le_preimage_id U) hU).symm fun i ↦
      (pieceIdentityCongr C (gysinSystemOfInvertible C) sX U (opens_le_preimage_id U) p i
        _).symm (e i), fun i ↦ ?_⟩
  change chowCohomologyRestriction C (gysinSystemOfInvertible C) sX (U i).ι p
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) _ = _
  rw [chowCohomologyRestriction_eq_pieceIdentityCongr,
    ← bivariantPieceEquivOfInvertible_apply C sX sX (𝟙 X) (Category.id_comp sX) p U U id
      (opens_le_preimage_id U) hU, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

include hU in
/-- **`Θ` is bijective when it is bijective on the pieces.** Let `X = ∐_i X_i` be a decomposition
into open and closed subschemes with `dim_δ X ≤ d`. If `c ↦ c ∩ [X_i]_d` is bijective on
`A^p(X_i)` for every `i`, then `c ↦ c ∩ [X]_d` is bijective on `A^p(X)`. -/
theorem chowCohomologyCapFundamentalClass_bijective_of_isClopenDecomposition (d : ℤ)
    (hdim : schemeDeltaDimension C sX ≤ (d : EInt))
    (h : ∀ i, Function.Bijective
      (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) ((U i).ι ≫ sX) d p)) :
    Function.Bijective
      (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX d p) := by
  have hdec : IsClopenDecomposition fun i ↦ (U i).ι.opensRange := by
    simpa only [Scheme.Opens.opensRange_ι] using hU
  set R := chowGroupClopenRestrictEquiv C sX (fun i ↦ (U i).ι ≫ sX) (fun i ↦ (U i).ι)
    (fun _ ↦ rfl) hdec (d - p)
  have hR : ∀ (α : chowGroup C sX (d - p)) i,
      R α i = chowGroupRestrict C sX ((U i).ι ≫ sX) (U i).ι rfl (d - p) α :=
    fun α i ↦ chowGroupClopenRestrictEquiv_apply C sX _ _ _ hdec (d - p) α i
  refine ⟨fun c c' hcc' ↦ ?_, fun α ↦ ?_⟩
  · refine chowCohomologyComponent_eq_of_restriction_eq hU p fun i ↦ (h i).1 ?_
    rw [← chowGroupRestrict_chowCohomologyCapFundamentalClass C sX (U i) p d hdim,
      ← chowGroupRestrict_chowCohomologyCapFundamentalClass C sX (U i) p d hdim, hcc']
  · choose e he using fun i ↦ (h i).2 (chowGroupRestrict C sX ((U i).ι ≫ sX) (U i).ι rfl
      (d - p) α)
    obtain ⟨c, hc⟩ := exists_chowCohomologyComponent_restriction_eq hU p e
    refine ⟨c, R.injective (funext fun i ↦ ?_)⟩
    rw [hR, hR, chowGroupRestrict_chowCohomologyCapFundamentalClass C sX (U i) p d hdim, hc i,
      he i]

end Pieces

end Stacks.Chow

end
