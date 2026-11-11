module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyResidueFieldFirstHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGrc1InH01
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGrc1OpenSubstack
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.FibreBettiZeroGlobalFunctions

/-!
# `Curves^{grc,1} ⊂ Curves^{h0,1}` as open substacks of `Curves`

This file proves Stacks 0E6L up to the form of its base change clause. Both `Curves^{grc,1}`
(families of curves whose geometric fibres are reduced, connected and of dimension `1`) and
`Curves^{h0,1}` (families of curves with `f_*𝒪_X = 𝒪_S`, this holding after arbitrary base
change, and fibres of dimension `1`) are open substacks of `Curves`, the first is contained in
the second, and for a family in `Curves^{grc,1}` the module `R¹f_*𝒪_X` is finite locally free
and isomorphic, along every base change, to the pullback of `R¹f_*𝒪_X`.

## Main results

* `AlgebraicGeometry.curvesGrc1_le_curvesH01_isOpenSubstack_and_firstHigherDirectImage`:
  `Curves^{grc,1}` and `Curves^{h0,1}` are open substacks of `Curves`, the first contained in the
  second, and on `Curves^{grc,1}` the module `R¹f_*𝒪_X` is finite locally free and, along every
  base change, isomorphic to some pullback. Stacks 0E6L itself, with the canonical base change
  map an isomorphism, is in `Quot/CurvesGrc1H01OpenSubstacksBaseChange.lean`.

## References

* [Stacks Project, Tag 0E6L](https://stacks.math.columbia.edu/tag/0E6L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- `Curves^{grc,1}` and `Curves^{h0,1}` are open substacks of `Curves` (each is closed under
isomorphisms, and its inclusion into `Curves` is representable by algebraic spaces and an open
immersion), and `Curves^{grc,1} ⊂ Curves^{h0,1}`; for a family of curves `f : X → S` whose
geometric fibres are reduced, connected and of dimension `1`, `R¹f_*𝒪_X` is a finite locally
free `𝒪_S`-module and, for every morphism `h : S' → S` of base schemes, there is some
isomorphism `h^*(R¹f_*𝒪_X) ≅ R¹f'_*𝒪_{X'}` where `f' : X' → S'` is the base change.

The last clause asserts only an abstract isomorphism, weaker than the base change statement of
Stacks 0E6L; the full statement, with the canonical base change map an isomorphism, is
`AlgebraicGeometry.curvesGrc1_le_curvesH01_isOpenSubstack_and_firstDirectImageBaseChangeMapIsIso`.

The conclusions are stated for the defining properties of the substacks:
`IsGrc1CurveFamily` and `IsH01CurveFamily`, the strictly full subcategories of `Curves` they
cut out, and `curvesSubstackInclusion` their inclusions. -/
theorem curvesGrc1_le_curvesH01_isOpenSubstack_and_firstHigherDirectImage :
    (ObjectProperty.IsClosedUnderIsomorphisms (IsGrc1CurveFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ (IsGrc1CurveFamily B hZ)
          isOpenCurvesLocus_isGrc1CurveFamily.prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsGrc1CurveFamily B hZ)
          isOpenCurvesLocus_isGrc1CurveFamily.prop_of_hom)) ∧
    (ObjectProperty.IsClosedUnderIsomorphisms (IsH01CurveFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ (IsH01CurveFamily B hZ)
          CurveFamily.isOpenCurvesLocus_isH01CurveFamily.prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsH01CurveFamily B hZ)
          CurveFamily.isOpenCurvesLocus_isH01CurveFamily.prop_of_hom)) ∧
    IsGrc1CurveFamily B hZ ≤ IsH01CurveFamily B hZ ∧
    ∀ X : CurveFamily B hZ, IsGrc1CurveFamily B hZ X →
      X.HasFiniteLocallyFreeFirstHigherDirectImage ∧
        X.FirstHigherDirectImageCommutesWithBaseChange :=
  ⟨curvesGrc1_isOpenSubstack B hZ,
    isOpenImmersion_curvesSubstackInclusion CurveFamily.isOpenCurvesLocus_isH01CurveFamily,
    isGrc1CurveFamily_le_isH01CurveFamily,
    fun _ hX =>
      have h := CurveFamily.hasResidueFieldGlobalFunctions_of_hasUniversallyBijectiveGlobalFunctions
        (CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_isGrc1CurveFamily hX)
      ⟨CurveFamily.hasFiniteLocallyFreeFirstHigherDirectImage_of_hasResidueFieldGlobalFunctions h,
        CurveFamily.firstHigherDirectImageCommutesWithBaseChange_of_hasResidueFieldGlobalFunctions
          h⟩⟩

end AlgebraicGeometry

end
