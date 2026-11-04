module

public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReasonableDenseSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyBoundedFibresComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyBoundedFibresDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat

/-!
# The schematic locus of an algebraic space with a finite étale atlas

An algebraic space over a scheme `S` admitting a finite étale surjective morphism from a
scheme is reasonable, hence has a dense open subspace which is a scheme: **Stacks 06NG**.

## Main results

* `AlgebraicGeometry.Space.isReasonableSpace_of_finite_surjective_chart`: an algebraic space
  receiving a finite surjective morphism from a scheme over `S` is reasonable.
* `AlgebraicGeometry.Space.exists_denseRange_isRepresentable_isOpenSubspace_of_finite_etale_cover`:
  **Stacks 06NG**.

## Implementation notes

Reasonableness is taken in the form of condition (2) of Stacks 03JT, which
`AlgebraicGeometry.Space.IsReasonableSpace` spells out: every étale chart of `X` by an affine
scheme has universally bounded fibres. Given such a chart `φ : h_W ⟶ X`, finiteness of the
atlas `f : h_U ⟶ X` represents the base change of `f` along `φ` by an affine scheme `V`, and
the other projection `i : h_V ⟶ h_U` is a base change of `φ`, hence étale. An étale morphism
of schemes is locally quasi-finite and locally of finite type, and `V` is affine, so Stacks
03JA bounds the fibres of `i`. Surjectivity of `f` puts the points of `h_W` inside the image
of `h_U`, so Stacks 03JO carries that bound back to `φ`.

Étaleness of the atlas is therefore not used: finite and surjective suffice, which is what
`AlgebraicGeometry.Space.isReasonableSpace_of_finite_surjective_chart` records. The source's
first proof instead stratifies `X` by the degree of `f` and bounds the fibres of each affine
open of `U` over `X` by that degree; the route here replaces the stratification by the
descent statement of Stacks 03JO.

## References

* [Stacks Project, Tag 06NG](https://stacks.math.columbia.edu/tag/06NG)
* [Stacks Project, Tag 03JI](https://stacks.math.columbia.edu/tag/03JI)
* [Stacks Project, Tag 03JO](https://stacks.math.columbia.edu/tag/03JO)
* [Stacks Project, Tag 03JA](https://stacks.math.columbia.edu/tag/03JA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An algebraic space over `S` admitting a finite surjective morphism from a scheme over `S`
is reasonable.

An étale chart `φ : h_W ⟶ X` by an affine scheme has an affine representable base change
`i : h_V ⟶ h_U` along the atlas, again étale, whose fibres Stacks 03JA bounds; surjectivity
of the atlas and Stacks 03JO return that bound to `φ`. -/
theorem isReasonableSpace_of_finite_surjective_chart
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {U : BigFppfOver B S hS} (f : yoneda.obj U ⟶ X)
    (hfin : IsFinite B S hS f) (hsurj : IsSurjective B S hS f) :
    IsReasonableSpace B S hS X := by
  intro W hW φ hφ
  obtain ⟨V, p, i, hVaff, -, hcart⟩ := hfin W hW φ
  -- The chart `i` of the atlas is a base change of the chart `φ`, hence étale.
  have hbc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hi : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf i :=
    hbc.of_isPullback hcart.flip hφ
  let : AlgebraicGeometry.Etale
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage i)) :=
    prop_preimage_of_presheaf B S hS
      AlgebraicGeometry.Etale.etale_isStableUnderBaseChange i hi
  let : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map (yoneda.preimage i)) :=
    (AlgebraicGeometry.locallyQuasiFinite_of_etale _).1
  let : LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map (yoneda.preimage i)) :=
    (AlgebraicGeometry.locallyQuasiFinite_of_etale _).2
  let : IsAffine ((BigFppfOver.toScheme B S hS).obj V) := hVaff
  -- Stacks 03JA: an étale morphism out of an affine scheme has universally bounded fibres.
  have hbnd : HasUniversallyBoundedFibers B S hS V i := by
    have h := (hasUniversallyBoundedFibers_yoneda_map_iff B S hS (yoneda.preimage i)).2
      (hasUniversallyBoundedFibers_of_locallyQuasiFinite_of_compactSpace _)
    rwa [yoneda.map_preimage] at h
  -- Stacks 03JO: the bound descends to `φ`, whose points lie in the image of the atlas.
  exact hasUniversallyBoundedFibers_of_baseChange_of_range_subset B S hS hX
    (isAlgebraicSpace_yoneda B S hS U) f φ
    (by rw [Set.range_eq_univ.mpr hsurj]; exact Set.subset_univ _) hcart.flip hbnd

/-- **Stacks 06NG.** An algebraic space over `S` admitting a finite étale surjective morphism
from a scheme over `S` has a representable open subspace whose point set is dense: such a
space is reasonable, so Stacks 03JI applies. -/
@[stacks 06NG]
theorem exists_denseRange_isRepresentable_isOpenSubspace_of_finite_etale_cover
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {U : BigFppfOver B S hS} (f : yoneda.obj U ⟶ X)
    (hfin : IsFinite B S hS f) (_hetale : IsEtale B S hS f)
    (hsurj : IsSurjective B S hS f) :
    ∃ G : Subfunctor X, IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable ∧
      DenseRange (pointsMap B S hS G.toFunctor G.ι) :=
  exists_denseRange_isRepresentable_isOpenSubspace_of_isReasonableSpace B S hS hX
    (isReasonableSpace_of_finite_surjective_chart B S hS hX f hfin hsurj)

end AlgebraicGeometry.Space

end
