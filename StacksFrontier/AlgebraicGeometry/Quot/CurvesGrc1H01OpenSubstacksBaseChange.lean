module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFirstHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGrc1H01OpenSubstacks

/-!
# Stacks 0E6L, with base change through the canonical map

`Curves^{grc,1}` and `Curves^{h0,1}` are open substacks of `Curves`, the first is contained in
the second, and for a family `f : X → S` in `Curves^{grc,1}` the module `R¹f_*𝒪_X` is finite
locally free and its formation commutes with arbitrary base change: for every `h : S' → S`, with
`f' : X' → S'` the base change, the canonical base change map `h^*(R¹f_*𝒪_X) ⟶ R¹f'_*𝒪_{X'}` is
an isomorphism.

## Main definitions

* `AlgebraicGeometry.CurveFamily.FirstDirectImageBaseChangeMapIsIso`: the canonical base change
  map `h^*(R¹f_*𝒪_X) ⟶ R¹f'_*𝒪_{X'}` is an isomorphism for every morphism of families into `X`.

## Main results

* `AlgebraicGeometry.curvesGrc1_le_curvesH01_isOpenSubstack_and_firstDirectImageBaseChangeMapIsIso`:
  **Stacks 0E6L.**

## References

* [Stacks Project, Tag 0E6L](https://stacks.math.columbia.edu/tag/0E6L)
* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

namespace CurveFamily

variable {B hZ}

/-- **The formation of `R¹f_*𝒪_X` commutes with arbitrary base change.** For a family of curves
`f : X → S` and every morphism `h : S' → S` of base schemes, with `f' : X' → S'` the base change
— that is, for every morphism of families of curves `a : X' ⟶ X`, whose square is cartesian, over
`h = a.baseMap` — the canonical base change map `h^*(R¹f_*𝒪_X) ⟶ R¹f'_*𝒪_{X'}`
(`AlgebraicGeometry.CurveFamily.firstDirectImageBaseChangeMap`) is an isomorphism. -/
def FirstDirectImageBaseChangeMapIsIso (X : CurveFamily B hZ) : Prop :=
  ∀ (F : CurveFamily B hZ) (a : F ⟶ X), IsIso (firstDirectImageBaseChangeMap a)

end CurveFamily

/-- `Curves^{grc,1}` and `Curves^{h0,1}` are open substacks of `Curves` (each is closed under
isomorphisms, and its inclusion into `Curves` is representable by algebraic spaces and an open
immersion), and `Curves^{grc,1} ⊂ Curves^{h0,1}`. In particular, for a family of curves `f : X → S`
whose geometric fibres are reduced, connected and of dimension `1`, `R¹f_*𝒪_X` is a finite locally
free `𝒪_S`-module whose formation commutes with arbitrary base change: for every morphism
`h : S' → S` of base schemes, with `f' : X' → S'` the base change, the canonical base change map
`h^*(R¹f_*𝒪_X) ⟶ R¹f'_*𝒪_{X'}` is an isomorphism.

The conclusions are stated for the defining properties of the substacks:
`IsGrc1CurveFamily` and `IsH01CurveFamily`, the strictly full subcategories of `Curves` they
cut out, and `curvesSubstackInclusion` their inclusions; the base changes `h` are the morphisms
of families of curves into `X`. -/
@[stacks 0E6L "Base change is the canonical map `h^*(R¹f_*𝒪_X) ⟶ R¹f'_*𝒪_{X'}` being an
isomorphism, for every morphism of families of curves `X' ⟶ X` over `h : S' → S`."]
theorem curvesGrc1_le_curvesH01_isOpenSubstack_and_firstDirectImageBaseChangeMapIsIso :
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
      X.HasFiniteLocallyFreeFirstHigherDirectImage ∧ X.FirstDirectImageBaseChangeMapIsIso :=
  ⟨curvesGrc1_isOpenSubstack B hZ,
    isOpenImmersion_curvesSubstackInclusion CurveFamily.isOpenCurvesLocus_isH01CurveFamily,
    isGrc1CurveFamily_le_isH01CurveFamily,
    fun X hX =>
      have h := CurveFamily.hasResidueFieldGlobalFunctions_of_hasUniversallyBijectiveGlobalFunctions
        (CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_isGrc1CurveFamily hX)
      ⟨CurveFamily.hasFiniteLocallyFreeFirstHigherDirectImage_of_hasResidueFieldGlobalFunctions h,
        X.isIso_firstDirectImageBaseChangeMap_of_residueField h⟩⟩

end AlgebraicGeometry

end
