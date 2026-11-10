module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedAbsolute

/-!
# The involution quotient of the affine line is Noetherian

Over a field in which two is invertible, the algebraic space
`AlgebraicGeometry.AffineLineInvolution.involutionQuotient` obtained by identifying each
nonzero point of the affine line with its negative is a Noetherian algebraic space: it is
quasi-compact, quasi-separated and locally Noetherian.

## Main results

* `AlgebraicGeometry.AffineLineInvolution.isLocallyNoetherian_affineLine`: the affine line is
  locally Noetherian.
* `AlgebraicGeometry.AffineLineInvolution.isNoetherian_involutionQuotient`: the quotient is a
  Noetherian algebraic space.

## Implementation notes

All three components are read off the same chart. The affine line is an affine scheme of
finite type over the ground field, so it is quasi-compact, quasi-separated and locally
Noetherian, and the chart of the quotient sheaf is a surjective étale morphism from it by
Stacks 0265. Quasi-separatedness of the quotient is
`AlgebraicGeometry.AffineLineInvolution.isAbsolutelyQuasiSeparated_involutionQuotient`
(Stacks 02Z1).

## References

* [Stacks Project, Tag 02Z1](https://stacks.math.columbia.edu/tag/02Z1)
* [Stacks Project, Tag 03EA](https://stacks.math.columbia.edu/tag/03EA)
* [Stacks Project, Tag 07S4](https://stacks.math.columbia.edu/tag/07S4)
* [Stacks Project, Tag 0ENT](https://stacks.math.columbia.edu/tag/0ENT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace AffineLineInvolution

variable (k : Type u) [Field k]

/-- The affine line is locally Noetherian, being of finite type over a field. -/
theorem isLocallyNoetherian_affineLine : IsLocallyNoetherian (affineLine k).left := by
  have _ : Finite PUnit.{u + 1} := inferInstance
  have _ : LocallyOfFinitePresentation (affineLine k).hom := by
    change LocallyOfFinitePresentation
      (AffineSpace PUnit.{u + 1} (Spec (.of k)) ↘ Spec (.of k))
    infer_instance
  have _ : IsLocallyNoetherian (Spec (.of k)) := inferInstance
  have _ : LocallyOfFiniteType (affineLine k).hom :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mp ‹_›
  exact LocallyOfFiniteType.isLocallyNoetherian (affineLine k).hom

/-- Away from characteristic two, the quotient of the affine line by the punctured graph of
negation is a Noetherian algebraic space over the ground field: it is quasi-compact,
quasi-separated and locally Noetherian. -/
@[stacks 0ENT "the Noetherian property"]
theorem isNoetherian_involutionQuotient (hchar : (2 : k) ≠ 0) (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (.of k))) (hZ : B.Contains (⊤_ Scheme.{u}))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)] :
    Space.IsNoetherian B (Spec (.of k)) hS hZ (involutionQuotient k B hS).obj := by
  have : NeZero (2 : k) := ⟨hchar⟩
  have : Stacks.Groupoids.IsEtaleEquivalenceRelation
      (R := relationScheme k)
      (U := (Over.post B.inclusion).obj (affineLineChart k B hS))
      (involutionRelation k) := isEtaleEquivalenceRelation k
  have hdiagRep := Space.relativelyRepresentable_diag_quotientSheaf B (Spec (.of k)) hS
    (affineLineChart k B hS) (involutionRelation k)
    (Space.isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft B (Spec (.of k)) hS)
  have hsurj := Space.presheaf_surjective_quotientChart_of_relativelyRepresentable_diag
    B (Spec (.of k)) hS (affineLineChart k B hS) (involutionRelation k) hdiagRep
  have hetale := Space.presheaf_etale_quotientChart_of_relativelyRepresentable_diag
    B (Spec (.of k)) hS (affineLineChart k B hS) (involutionRelation k) hdiagRep
  refine ⟨⟨affineLineChart k B hS, _, ?_, hsurj,
    (Space.isEtale_iff_presheaf_of_yoneda B (Spec (.of k)) hS _).2 hetale⟩,
    isAbsolutelyQuasiSeparated_involutionQuotient k B hS hchar hZ,
    ⟨affineLineChart k B hS, _, hsurj, hetale, ?_⟩⟩
  · change CompactSpace (affineLine k).left
    infer_instance
  · exact isLocallyNoetherian_affineLine k

end AffineLineInvolution

end AlgebraicGeometry

end
