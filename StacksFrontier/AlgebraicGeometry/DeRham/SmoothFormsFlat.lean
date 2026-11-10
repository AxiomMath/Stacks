module

public import StacksFrontier.AlgebraicGeometry.DeRham.ProperSmoothFormsPerfectBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.ScalarRestrictionFlatOver
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatTransport

/-!
# The terms of the relative de Rham complex of a smooth morphism are flat over the base

Let `f : X ⟶ S` be a smooth morphism of schemes. Each term `Ω^p_{X/S}` of the relative de Rham
complex is finite locally free over `𝒪_X`, and `𝒪_X` is flat over `𝒪_S` because a smooth
morphism is flat; so `Ω^p_{X/S}` is flat over `𝒪_S` in the stalkwise sense of
[Stacks, Tag 08KT]. Read as a sheaf of `f^{-1}𝒪_S`-modules — which is how it sits in the de Rham
complex — it is therefore a **flat** sheaf of modules on the ringed space `(X, f^{-1}𝒪_S)`.

This is the hypothesis `hflat` of the projection formula
`relativeComplexOrdinaryProjectionFormulaIsoOfIsLocallyBoundedOfIsQuasicoherent`
([Stacks, Tag 0FML] conclusion (4)) at the complex `Ω^•_{X/S}`, which is the shape in which
[Stacks, Tag 0FMM] uses that conclusion; the companion hypothesis `hF` is
`Stacks.DeRhamDirectImage.isLocallyBounded_deRhamCochainComplex`.

## Main results

* `Stacks.DeRhamDirectImage.isFlat_deRhamCochainComplex_X`: every term of the `ℤ`-indexed
  relative de Rham complex of a smooth morphism is a flat `f^{-1}𝒪_S`-module.

## Implementation notes

Nothing here is a flatness argument: the two steps of the chain are already in the tree and are
only joined.

* `AlgebraicGeometry.ProperSmoothDeRham.isFlatOver_relativeDifferentialForms` is flatness of
  `Ω^p_{X/S}` over `S` at the stalkwise spelling `AlgebraicGeometry.IsFlatOver` of Tag 08KT.
* `AlgebraicGeometry.Scheme.Hom.isFlat_scalarRestriction_of_isFlatOver` carries that to flatness
  of the restriction of scalars along `f^{-1}𝒪_S ⟶ 𝒪_X` as a sheaf of modules on
  `(X, f^{-1}𝒪_S)`, through the comparison `(f^{-1}𝒪_S)_x ≅ 𝒪_{S, f(x)}` of
  `Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso` and the stalkwise criterion for
  flatness of Tag 05NE.

What is left is the degree bookkeeping between the `ℕ`-indexed de Rham complex and the
`ℤ`-indexed one the derived category uses: the negative degrees are zero objects, flat by
`AlgebraicGeometry.SheafOfModules.IsFlat.of_isZero`, and the nonnegative ones are the
`ℕ`-indexed terms along `HomologicalComplex.extendXIso`, flatness transporting by
`AlgebraicGeometry.SheafOfModules.IsFlat.of_iso`. This is the same bookkeeping as in
`Stacks.DeRhamDirectImage.isLocallyBounded_deRhamCochainComplex`.

## References

* [Stacks Project, Tag 08KT](https://stacks.math.columbia.edu/tag/08KT)
* [Stacks Project, Tag 05NE](https://stacks.math.columbia.edu/tag/05NE)
* [Stacks Project, Tag 02N3](https://stacks.math.columbia.edu/tag/02N3)
* [Stacks Project, Tag 0FML](https://stacks.math.columbia.edu/tag/0FML)
* [Stacks Project, Tag 0FMM](https://stacks.math.columbia.edu/tag/0FMM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.DeRhamDirectImage

open _root_.AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **Every term of the relative de Rham complex of a smooth morphism is flat over
`f^{-1}𝒪_S`.** For `f : X ⟶ S` smooth the sheaf `Ω^p_{X/S}` is flat over `S` in the stalkwise
sense of [Stacks, Tag 08KT], hence flat as a sheaf of `f^{-1}𝒪_S`-modules; the terms of the
`ℤ`-indexed complex in negative degrees are zero, and zero is flat.

This is the hypothesis `hflat` of conclusion (4) of [Stacks, Tag 0FML] at the complex
`Ω^•_{X/S}`. -/
theorem isFlat_deRhamCochainComplex_X [Smooth f] (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (inverseImageBase f).sheaf) ((deRhamCochainComplex f).X i) := by
  rcases lt_or_ge i 0 with hneg | hpos
  · exact AlgebraicGeometry.SheafOfModules.IsFlat.of_isZero _
      (HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat i
        (fun n => by simpa using (hneg.trans_le (Int.natCast_nonneg n)).ne'))
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = (n : ℤ) := ⟨i.toNat, by omega⟩
    refine AlgebraicGeometry.SheafOfModules.IsFlat.of_iso _
      (HomologicalComplex.extendXIso
        (show CochainComplex (Modules (inverseImageBase f)) ℕ from Scheme.Hom.deRhamComplex f)
        ComplexShape.embeddingUpNat (i := n) rfl).symm ?_
    rw [Scheme.Hom.deRhamComplex_X]
    exact Scheme.Hom.isFlat_scalarRestriction_of_isFlatOver f _
      (AlgebraicGeometry.ProperSmoothDeRham.isFlatOver_relativeDifferentialForms f n)

end Stacks.DeRhamDirectImage

end
