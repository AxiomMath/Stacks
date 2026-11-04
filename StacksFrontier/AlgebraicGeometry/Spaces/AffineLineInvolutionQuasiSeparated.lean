module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedAbsolute

/-!
# The quotient of the affine line by the punctured graph of negation is quasi-separated

Stacks 02Z1 asserts of the algebraic space `X = 𝔸¹_k/R`, where `R = Δ ⨿ Γ` is the diagonal
together with the graph of negation on the punctured line, that it is quasi-separated but
not locally separated.  This file proves the quasi-separatedness assertion: the chart
`𝔸¹_k ⟶ X` is a surjective étale atlas whose source is an affine, hence quasi-separated,
scheme, and the kernel pair of the chart is a base change of the target map `R ⟶ 𝔸¹_k`,
which is affine and hence quasi-compact.  Stacks 07S4 then applies.

## Main results

* `AlgebraicGeometry.AffineLineInvolution.quasiCompact_target`: the target map of the
  involution relation is quasi-compact, being affine.
* `AlgebraicGeometry.AffineLineInvolution.isAbsolutelyQuasiSeparated_involutionQuotient`:
  the quotient is quasi-separated.

## Implementation notes

The kernel pair of the chart is read off from
`AlgebraicGeometry.Space.exists_isPullback_quotientChart` at the point `𝟙 U`: that theorem
describes the base change of the chart along an arbitrary *lifted* point of the quotient,
and the lifted point `𝟙 U` makes the base change the kernel pair.  It also records the
representing object as a base change of the target map of the relation, which is where
quasi-compactness comes from; no separate identification of the kernel pair with `R` is
needed.

Like `AlgebraicGeometry.AffineLineInvolution.isAlgebraicSpace_involutionQuotient`, on which
this rests, the effective-descent hypothesis of
`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf` is discharged unconditionally: the
chart `affineLineChart` is affine, so
`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft` supplies
effective descent at the monomorphisms locally of finite type, and the diagonal's
representability this gives is enough to get surjectivity and étaleness of the chart as well, by
`AlgebraicGeometry.Space.presheaf_surjective_quotientChart_of_relativelyRepresentable_diag` and its
étale companion.

## References

* [Stacks Project, Tag 02Z1](https://stacks.math.columbia.edu/tag/02Z1)
* [Stacks Project, Tag 07S4](https://stacks.math.columbia.edu/tag/07S4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry.AffineLineInvolution

variable (k : Type u) [Field k]

/-- **Stacks 02Z1.** The first projection `R ⟶ U` of the involution relation is
quasi-compact, being affine.  This is the counterpart for the target map of
`AlgebraicGeometry.AffineLineInvolution.quasiCompact_source`. -/
theorem quasiCompact_target : QuasiCompact (involutionRelation k).target.left :=
  have := isAffineHom_target k
  inferInstance

variable (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k)))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)]

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)] in
/-- The affine line, as an object of the big fppf site, is quasi-separated over `Spec ℤ`:
it is an affine scheme. -/
theorem quasiSeparated_affineLineChart :
    QuasiSeparated (B.inclusion.map (affineLineChart k B hS).hom ≫
      terminal.from (Spec (.of k))) := by
  have h := (quasiSeparatedSpace_iff_quasiSeparated
    ((BigFppfOver.toScheme B (Spec (.of k)) hS).obj (affineLineChart k B hS))).mp
      (inferInstance)
  rwa [terminal.hom_ext
    (terminal.from ((BigFppfOver.toScheme B (Spec (.of k)) hS).obj (affineLineChart k B hS)))
    (B.inclusion.map (affineLineChart k B hS).hom ≫ terminal.from (Spec (.of k)))] at h

/-- The kernel pair of the chart `𝔸¹_k ⟶ X` of the involution quotient is represented by an
object of the site whose second projection is quasi-compact.

The object is the base change of the relation along the target map, which is affine; the
square is `AlgebraicGeometry.Space.exists_isPullback_quotientChart` at the lifted point
`𝟙 U`. -/
theorem exists_isPullback_quotientChart_involutionRelation [NeZero (2 : k)] :
    ∃ (d : BigFppfOver B (Spec (.of k)) hS)
      (p₁ p₂ : d ⟶ affineLineChart k B hS),
      IsPullback (yoneda.map p₁) (yoneda.map p₂)
        (quotientChart (BigFppfOver.topology B (Spec (.of k)) hS) (Over.post B.inclusion)
          (affineLineChart k B hS) (involutionRelation k))
        (quotientChart (BigFppfOver.topology B (Spec (.of k)) hS) (Over.post B.inclusion)
          (affineLineChart k B hS) (involutionRelation k)) ∧
      QuasiCompact ((BigFppfOver.toScheme B (Spec (.of k)) hS).map p₂) := by
  have : IsEtaleEquivalenceRelation
      (R := relationScheme k)
      (U := (Over.post B.inclusion).obj (affineLineChart k B hS))
      (involutionRelation k) := isEtaleEquivalenceRelation k
  obtain ⟨d, p₁, p₂, hpb, ⟨w, hw⟩, -⟩ :=
    Space.exists_isPullback_quotientChart B (Spec (.of k)) hS (affineLineChart k B hS)
      (involutionRelation k) (affineLineChart k B hS) (𝟙 _)
  have hid : yoneda.map (𝟙 (affineLineChart k B hS)) ≫
      quotientChart (BigFppfOver.topology B (Spec (.of k)) hS) (Over.post B.inclusion)
        (affineLineChart k B hS) (involutionRelation k) =
      quotientChart (BigFppfOver.topology B (Spec (.of k)) hS) (Over.post B.inclusion)
        (affineLineChart k B hS) (involutionRelation k) := by
    rw [CategoryTheory.Functor.map_id]
    exact Category.id_comp _
  rw [hid] at hpb
  exact ⟨d, p₁, p₂, hpb,
    MorphismProperty.of_isPullback (P := @QuasiCompact.{u}) hw (quasiCompact_target k)⟩

/-- **Stacks 02Z1, quasi-separatedness.** Away from characteristic two, the quotient of the
affine line by the punctured graph of negation is a quasi-separated algebraic space.

The chart `𝔸¹_k ⟶ X` is surjective and étale by Stacks 0265, its source is affine and hence
quasi-separated, and the second projection of its kernel pair is a base change of the target
map of the relation, which is affine; Stacks 07S4 concludes.

Representability of the diagonal of `X`, from which surjectivity and étaleness of the chart
both follow, is supplied unconditionally by
`AlgebraicGeometry.Space.relativelyRepresentable_diag_quotientSheaf` together with
`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft`. -/
@[stacks 02Z1 "quasi_separated"]
theorem isAbsolutelyQuasiSeparated_involutionQuotient (hchar : (2 : k) ≠ 0)
    (hZ : B.Contains (⊤_ Scheme.{u})) :
    Space.IsAbsolutelyQuasiSeparated B (Spec (.of k)) hS hZ
      (involutionQuotient k B hS).obj := by
  have : NeZero (2 : k) := ⟨hchar⟩
  have : IsEtaleEquivalenceRelation
      (R := relationScheme k)
      (U := (Over.post B.inclusion).obj (affineLineChart k B hS))
      (involutionRelation k) := isEtaleEquivalenceRelation k
  obtain ⟨d, p₁, p₂, hpb, hqc⟩ :=
    exists_isPullback_quotientChart_involutionRelation k B hS
  have hdiagRep := Space.relativelyRepresentable_diag_quotientSheaf B (Spec (.of k)) hS
    (affineLineChart k B hS) (involutionRelation k)
    (Space.isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft B (Spec (.of k)) hS)
  exact Space.isAbsolutelyQuasiSeparated_of_etaleAtlas_quasiCompact_projection
    B (Spec (.of k)) hS hZ (isAlgebraicSpace_involutionQuotient k hchar B hS)
    (Space.presheaf_surjective_quotientChart_of_relativelyRepresentable_diag B (Spec (.of k)) hS
      (affineLineChart k B hS) (involutionRelation k) hdiagRep)
    (Space.presheaf_etale_quotientChart_of_relativelyRepresentable_diag B (Spec (.of k)) hS
      (affineLineChart k B hS) (involutionRelation k) hdiagRep)
    (quasiSeparated_affineLineChart k B hS) hpb hqc

end AlgebraicGeometry.AffineLineInvolution

end
