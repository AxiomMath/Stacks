module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfFormalSpacesAdmissible

/-!
# Stacks 0GVN for an index with an admissible cofinal family

Let `(X_λ, f_{λμ})` be a directed system of formal algebraic spaces over `S` whose transition
morphisms are closed immersions inducing isomorphisms on reductions (equivalently, by the remark
opening Section 0GVL, representable thickenings). **Stacks 0GVN** says that the colimit is a
formal algebraic space. As printed this is false: being a formal algebraic space includes the
set-theoretic condition of Remark 0AIS, which fails for the colimit of a system indexed by a set
as large as the site
(`AlgebraicGeometry.FormalSpace.not_forall_isFormalAlgebraicSpace_colimit_closedImmersions`).

This module proves the tag, under the source's hypotheses, for every directed index having a
cofinal family whose index admits coproducts in the site
(`AlgebraicGeometry.BigFppfSite.AdmitsCoproductIndex`, which every countable index does). That is
the proviso of Remark 0AIS (1): the coproduct of (a cofinal family of) the stages is dominated by
an object of the site. The set-theoretic condition is derived, not assumed.

## Main results

* `AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_colimit_of_cofinal`: Remark 0AIS
  for such a colimit.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_colimit_closedImmersions_of_cofinal`:
  **Stacks 0GVN** in that form.

## References

* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0GVN](https://stacks.math.columbia.edu/tag/0GVN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe v u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0AIS for a directed colimit of formal algebraic spaces along representable
thickenings, with an admissible cofinal family of stages.** If `ι : K → Λ` is cofinal and `K`
admits coproducts in the site, the stages `E_{ι k}` cover the colimit, each satisfies the
set-theoretic condition, and the kernel-pair pieces over them are represented by
`AlgebraicGeometry.FormalSpace.exists_epi_pullback_pullback_snd_colimitι`. -/
theorem satisfiesSetTheoreticCondition_colimit_of_cofinal {Λ : Type (u + 1)} [Preorder Λ]
    [Nonempty Λ] [IsDirected Λ (· ≤ ·)] (E : Λ ⥤ FppfSheaf B S hS)
    (hform : ∀ i : Λ, IsFormalAlgebraicSpace B S hS (E.obj i))
    (hthick : ∀ ⦃i j : Λ⦄ (g : i ⟶ j),
      Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom)
    {K : Type v} [Small.{u} K] [B.AdmitsCoproductIndex K] (ι : K → Λ)
    (hι : ∀ i, ∃ k, i ≤ ι k) :
    SatisfiesSetTheoreticCondition B S hS (colimit E) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  -- Replace `K` by a copy in `Type (u + 1)`.
  let K' : Type (u + 1) := ULift.{u + 1} (Shrink.{u} K)
  let : B.AdmitsCoproductIndex K' :=
    ⟨(Cardinal.mk_congr ((equivShrink.{u} K').symm.trans Equiv.ulift)).trans_lt
      (BigFppfSite.AdmitsCoproductIndex.mk_shrink_lt_cutoff_cof (B := B) (I := K))⟩
  let ι' : K' → Λ := fun k ↦ ι ((equivShrink.{u} K).symm k.down)
  have hι' : ∀ i, ∃ k, i ≤ ι' k := fun i ↦ by
    obtain ⟨k, hk⟩ := hι i
    exact ⟨⟨equivShrink.{u} K k⟩, by simpa [ι'] using hk⟩
  refine satisfiesSetTheoreticCondition_of_admissible_cover B S hS (colimit E)
    (fun k ↦ E.obj (ι' k)) (fun k ↦ colimit.ι E (ι' k)) (fun k ↦ (hform (ι' k)).1) ?_
    (fun U t k ↦ exists_epi_pullback_pullback_snd_colimitι B S hS E hform hthick U t (ι' k))
  rw [Sheaf.isLocallySurjective_iff_epi]
  refine ⟨fun {T} a b hab ↦ colimit.hom_ext fun i ↦ ?_⟩
  obtain ⟨k, hk⟩ := hι' i
  rw [← colimit.w E (homOfLE hk), Category.assoc, Category.assoc]
  congr 1
  simpa using congrArg (fun m ↦ Sigma.ι (fun k ↦ E.obj (ι' k)) k ≫ m) hab

/-- **Stacks 0GVN, corrected.** Let `E` be a directed system of formal algebraic spaces over `S`
whose transition morphisms are representable thickenings (equivalently, by the remark opening
Section 0GVL, closed immersions inducing isomorphisms on reductions). Suppose the index has a
cofinal family `ι : K → Λ` whose index `K` admits coproducts in the site; every countable `K`
does, and so does `K = Λ` for a countable `Λ`. Then a sheaf isomorphic to the colimit of `E` is
a formal algebraic space over `S`.

The printed statement, with no condition on `Λ`, is false
(`AlgebraicGeometry.FormalSpace.not_forall_isFormalAlgebraicSpace_colimit_closedImmersions`): the
colimit can fail the set-theoretic condition of Remark 0AIS that Definition 0AIM includes. The
cofinal family is the proviso of Remark 0AIS (1); under it the set-theoretic condition is
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_colimit_of_cofinal`, and the atlas
is the chart system the source's proof constructs, from an atlas of one stage by the étale
lifting of Stacks 0DEE, with affine stages by Stacks 0DE8 (`AlgebraicGeometry.FormalSpace.`
`isFormalAlgebraicSpace_of_colimit_closedImmersions_of_satisfiesSetTheoreticCondition`). -/
@[stacks 0GVN "corrected form: the printed statement is false for an index set as large as the \
site, the colimit then failing the set-theoretic condition of Stacks 0AIS that Definition 0AIM \
includes \
(AlgebraicGeometry.FormalSpace.not_forall_isFormalAlgebraicSpace_colimit_closedImmersions, the \
square-zero system of the 0AIU/0GVM erratum, errata.md 2026-10-27). Stated under the \
source's hypotheses, transition maps being representable thickenings as the remark opening \
Section 0GVL reformulates them, for an index with a cofinal family whose index admits coproducts \
in the site (any countable index), the proviso of Stacks 0AIS observation (1); the set-theoretic \
condition is derived, not assumed, and the conclusion is the whole of Definition 0AIM"]
theorem isFormalAlgebraicSpace_of_colimit_closedImmersions_of_cofinal
    (Λ : Type (u + 1)) [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (E : Λ ⥤ FppfSheaf B S hS)
    (hform : ∀ i : Λ, IsFormalAlgebraicSpace B S hS (E.obj i))
    (hthick : ∀ ⦃i j : Λ⦄ (g : i ⟶ j),
      Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom)
    {K : Type v} [Small.{u} K] [B.AdmitsCoproductIndex K] (ι : K → Λ)
    (hι : ∀ i, ∃ k, i ≤ ι k)
    (Z : FppfSheaf B S hS) (hZ : Nonempty (Z ≅ colimit E)) :
    IsFormalAlgebraicSpace B S hS Z := by
  obtain ⟨eZ⟩ := hZ
  exact isFormalAlgebraicSpace_of_colimit_closedImmersions_of_satisfiesSetTheoreticCondition
    B S hS Λ E hform hthick Z (satisfiesSetTheoreticCondition_of_iso B S hS eZ.symm
      (satisfiesSetTheoreticCondition_colimit_of_cofinal B S hS E hform hthick ι hι)) ⟨eZ⟩

end AlgebraicGeometry.FormalSpace

end
