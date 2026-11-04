module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfSmallEtaleTriples

/-!
# The essential image of `a_X⁻¹` under base change

Let `T` be a big fppf site of algebraic spaces over a scheme `S` and `E` a big étale site of
algebraic spaces over the same big fppf site of schemes. For an algebraic space `X` of `T`
write `a_X` for the morphism from the big fppf topos of `X` to its small étale topos (Stacks
0DGI). This file records how the essential image of `a_X⁻¹` behaves under the inverse image
along a morphism of the big fppf topoi, the step of the proof of Stacks 0DGL that lets one
replace a morphism by its precomposition with an étale atlas.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.fppfToSmallEtale_essImage_bigFppfInverseImage`: if `H`
  is in the essential image of `a_Y⁻¹`, then `f_{big,fppf}⁻¹H` is in that of `a_X⁻¹`.

## References

* [Stacks Project, Tag 0DGI](https://stacks.math.columbia.edu/tag/0DGI)
* [Stacks Project, Tag 0DGL](https://stacks.math.columbia.edu/tag/0DGL)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : T.schemeSite = E.fppfSite)

/-- **The essential image of `a⁻¹` is stable under `f_{big,fppf}⁻¹`.** If `H ≅ a_Y⁻¹F`, then
`f_{big,fppf}⁻¹H ≅ f_{big,fppf}⁻¹a_Y⁻¹F ≅ a_X⁻¹f_small⁻¹F` by the canonical isomorphism of the
square of Stacks 0DGI. -/
theorem fppfToSmallEtale_essImage_bigFppfInverseImage {X Y : T.Spaces} (f : X ⟶ Y)
    {H : Sheaf (BigFppfSpaceOver.topology T Y) (Type (u + 1))}
    (hH : (fppfToSmallEtaleMorphism T E h Y).inverseImage.essImage H) :
    (fppfToSmallEtaleMorphism T E h X).inverseImage.essImage
      ((bigFppfMorphism T f).inverseImage.obj H) := by
  obtain ⟨F, ⟨e⟩⟩ := hH
  exact ⟨(E.smallEtaleMorphism (etaleMap T E h f)).inverseImage.obj F,
    ⟨(fppfSmallEtaleInverseImageCommIso T E h f).app F ≪≫
      (bigFppfMorphism T f).inverseImage.mapIso e⟩⟩

/-- **The essential image of `a⁻¹` along a composite.** If `f_{big,fppf}⁻¹H` is in the
essential image of `a_X⁻¹`, so is `(s ≫ f)_{big,fppf}⁻¹H` in that of `a_{X'}⁻¹`, for every
`s : X' ⟶ X`. -/
theorem fppfToSmallEtale_essImage_bigFppfInverseImage_comp {X' X Y : T.Spaces} (s : X' ⟶ X)
    (f : X ⟶ Y) {H : Sheaf (BigFppfSpaceOver.topology T Y) (Type (u + 1))}
    (hH : (fppfToSmallEtaleMorphism T E h X).inverseImage.essImage
      ((bigFppfMorphism T f).inverseImage.obj H)) :
    (fppfToSmallEtaleMorphism T E h X').inverseImage.essImage
      ((bigFppfMorphism T s).inverseImage.obj ((bigFppfMorphism T f).inverseImage.obj H)) :=
  fppfToSmallEtale_essImage_bigFppfInverseImage T E h s hH

end AlgebraicGeometry.BigFppfSpaceSite

end
