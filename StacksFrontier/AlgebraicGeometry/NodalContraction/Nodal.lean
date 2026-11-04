module

public import StacksFrontier.AlgebraicGeometry.NodalContraction.FiniteType
public import StacksFrontier.AlgebraicGeometry.NodalContraction.Glue
public import StacksFrontier.AlgebraicGeometry.NodalContraction.SmoothCentre

/-!
# Contracting an exceptional curve in a nodal relative curve over a discrete valuation ring

Let `R` be a discrete valuation ring, let `f : X ⟶ Spec R` be at-worst-nodal of relative
dimension one, let `E ⊆ X` be an exceptional curve of the first kind, presented by its ideal
sheaf `D` together with an isomorphism `e : 𝐏¹_κ ≅ E`, and let `b : X ⟶ X'` be a contraction of
`E`. Then `X'` carries a unique morphism to `Spec R` compatible with `f`, and that morphism is
again at-worst-nodal of relative dimension one.

## Main results

* `AlgebraicGeometry.isAtWorstNodalOfRelativeDimensionOne_of_isContractionOfExceptionalCurve` —
  **Stacks Project, Tag 0CDF.**

## References

* [Stacks Project, Tag 0CDF](https://stacks.math.columbia.edu/tag/0CDF)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace IsLocalRing

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0CDF.** Let `R` be a discrete valuation ring and let
`f : X ⟶ Spec R` be at-worst-nodal of relative dimension one. Let `b : X ⟶ X'` be the
contraction of an exceptional curve `E ⊆ X` of the first kind, presented by its ideal sheaf `D`
and an isomorphism `e : 𝐏¹_κ ≅ E`. Then `X'` is at-worst-nodal of relative dimension one over
`R`: there is a morphism `f' : X' ⟶ Spec R` with `b ≫ f' = f`, and it is at-worst-nodal of
relative dimension one.

Away from the contracted point `b` is an isomorphism, so the only issue is a neighbourhood of
that point. The closed fibre of `f` is reduced, so the uniformizer of `R` vanishes to order one
along `E` and therefore lies in the maximal ideal at the contracted point but not in its square.
The local ring there being regular of dimension two, the local ring of the closed fibre is
regular of dimension one; its residue field is geometrically reduced over the residue field of
`R` because the closed fibre of `f` is. Hence the closed fibre of `f'` is smooth at the
contracted point, and with flatness so is `f'`; a morphism smooth of relative dimension one is
at-worst-nodal of relative dimension one. -/
@[stacks 0CDF]
public theorem isAtWorstNodalOfRelativeDimensionOne_of_isContractionOfExceptionalCurve
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X X' : Scheme.{u}} (D : X.IdealSheafData) (κ : Type u) [Field κ]
    (e : projectiveLineProj κ ≅ D.subscheme)
    (hE : D.IsExceptionalCurveOfFirstKind κ e)
    (b : X ⟶ X') (hb : IsContractionOfExceptionalCurve D b)
    (f : X ⟶ Spec (CommRingCat.of R))
    (hf : IsAtWorstNodalOfRelativeDimensionOne f) :
    ∃ f' : X' ⟶ Spec (CommRingCat.of R),
      b ≫ f' = f ∧ IsAtWorstNodalOfRelativeDimensionOne f' := by
  obtain ⟨f', hbase, -⟩ := exists_factor_of_contraction D κ e b hb f
  refine ⟨f', hbase, ?_⟩
  have hF : IsAtWorstNodalOfRelativeDimensionOne (b ≫ f') := hbase ▸ hf
  have hflat : Flat f' := flat_of_isContractionOfExceptionalCurve D κ e b hb f' hF
  have : LocallyOfFinitePresentation f' :=
    locallyOfFinitePresentation_of_isContractionOfExceptionalCurve D κ e b hb f' hF
  obtain ⟨z, hz, hreg, hdim, hDz, ε, hε⟩ := hb.exists_blowUp_iso
  have := isIntegral_subscheme_of_iso_projectiveLineProj D κ e
  obtain ⟨x₀⟩ : Nonempty D.subscheme := inferInstance
  have hs : f' z = closedPoint R :=
    eq_closedPoint_of_isEffectiveCartierDivisor D hE.1 b z hz hDz f hf f' hbase x₀
      (topologicalKrullDimAt_subscheme_eq_one_of_iso_projectiveLineProj D κ e x₀)
  obtain ⟨x, hx⟩ :=
    exists_isField_stalk_fiber_of_isContractionOfExceptionalCurve D κ e b z hz hDz
  obtain ⟨V, hzV, hV⟩ := exists_smoothOfRelativeDimension_nbhd_centre D b hb f' hflat hF z hz
    hreg hdim hDz hs x hx
  exact isAtWorstNodalOfRelativeDimensionOne_of_compl_and_nbhd f' z hz
    (nodal_on_compl_centre D b z hz ε hε f' hF) V hzV hV

end AlgebraicGeometry

end
