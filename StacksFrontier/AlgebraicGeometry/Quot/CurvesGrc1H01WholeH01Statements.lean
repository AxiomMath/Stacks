module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGrc1H01Whole
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01OpenSubstackH01Statements

/-!
# Stacks 0E6L over the statements of the cohomological inputs of Stacks 0E6I

`AlgebraicGeometry.curvesGrc1_le_curvesH01_isOpenSubstack_and_firstHigherDirectImage_of` proves
Stacks 0E6L from five inputs, two of which are the cohomological inputs of Stacks 0E6I in
curve-family form. This file restates it over those two in the shape in which Stacks 0E0R (at
`i = 0`, for `𝓕 = 𝒪_X`) and Stacks 0E6B part (a) are stated for algebraic spaces — the `hbetti`
and `hstruct` of `StacksFrontier.AlgebraicGeometry.Quot.CurvesH01Inputs`. The conclusion is
unchanged; only the inputs are.

## Main results

* `curvesGrc1_le_curvesH01_isOpenSubstack_and_firstHigherDirectImage_of_h01Statements`:
  Stacks 0E6L, the whole statement.

## References

* [Stacks Project, Tag 0E6L](https://stacks.math.columbia.edu/tag/0E6L)
* [Stacks Project, Tag 0E6I](https://stacks.math.columbia.edu/tag/0E6I)
* [Stacks Project, Tag 0E1I](https://stacks.math.columbia.edu/tag/0E1I)
* [Stacks Project, Tag 0E0R](https://stacks.math.columbia.edu/tag/0E0R)
* [Stacks Project, Tag 0E6B](https://stacks.math.columbia.edu/tag/0E6B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **Stacks 0E6L, the whole statement, over the statements of Stacks 0E0R (at `i = 0`) and 0E6B
(a).** The strictly full subcategories `Curves^{grc,1}` of families of curves whose geometric
fibres are reduced, connected and of dimension `1` and `Curves^{h0,1}` of families with
`f_*𝒪_X = 𝒪_S` universally and fibres of dimension `1` are open substacks of `Curves` — each is
closed under isomorphisms and its inclusion is representable by algebraic spaces and an open
immersion — the first is contained in the second, and for every family of curves in the first the
module `R¹f_*𝒪_X` is a finite locally free `𝒪_S`-module whose formation commutes with arbitrary
base change.

This is `AlgebraicGeometry.curvesGrc1_le_curvesH01_isOpenSubstack_and_firstHigherDirectImage_of`
with its two Stacks 0E6I inputs replaced by `hbetti` (Stacks 0E0R at `i = 0`, for `𝓕 = 𝒪_X`) and
`hstruct` (Stacks 0E6B, part (a)). The other inputs are unchanged: `hconst`, the statement of
Stacks 0DMY part (7) for algebraic spaces, and `hR1`, `hR1bc`, parts (2) and (3) of Stacks 0E1J. -/
theorem curvesGrc1_le_curvesH01_isOpenSubstack_and_firstHigherDirectImage_of_h01Statements
    (hconst : ∀ (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
      (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
      (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
      (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk)))), Space.IsProper B (Spec (.of k)) hk f →
        Space.IsGeometricallyReduced k B hk X hX → Space.IsGeometricallyConnected B k hk X →
        Function.Bijective (algebraMap k (Space.globalFunctions B (Spec (.of k)) hk X)))
    (hbetti : ∀ {U : BigFppfOver B integerBase hZ} {X : AlgebraicSpaces B integerBase hZ}
      (f : X ⟶ schemeSpace U), Space.IsProper B integerBase hZ f.hom →
      Space.IsFlat B integerBase hZ f.hom → Space.IsFinitePresentation B integerBase hZ f.hom →
      ∃ b : (BigFppfOver.toScheme B integerBase hZ).obj U → ℕ∞, UpperSemicontinuous b ∧
        ∀ p : Space.FieldValuedPoint B integerBase hZ (yoneda.obj U),
          Space.h0FibreRank B integerBase hZ f p = b (Space.schemePoint B integerBase hZ U p))
    (hstruct : ∀ {X Y : AlgebraicSpaces B integerBase hZ} (f : X ⟶ Y),
      Space.IsProper B integerBase hZ f.hom → Space.IsFlat B integerBase hZ f.hom →
      Space.IsFinitePresentation B integerBase hZ f.hom →
      (∀ p : Space.FieldValuedPoint B integerBase hZ Y.1, Function.Bijective
        (algebraMap p.carrier (Space.globalFunctions B (Spec (.of p.carrier)) p.contained
          (Space.fibreOverFieldValuedPoint B integerBase hZ f.hom p)))) →
      IsIso (Space.structureSharp B integerBase hZ f) ∧
        ∀ (Y' : AlgebraicSpaces B integerBase hZ) (g : Y' ⟶ Y),
          IsIso (Space.structureSharp B integerBase hZ (pullback.snd f g)))
    (hR1 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.HasFiniteLocallyFreeFirstHigherDirectImage)
    (hR1bc : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.FirstHigherDirectImageCommutesWithBaseChange) :
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
          (CurveFamily.isOpenCurvesLocus_isH01CurveFamily_of_h0FibreRank hbetti
            hstruct).prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsH01CurveFamily B hZ)
          (CurveFamily.isOpenCurvesLocus_isH01CurveFamily_of_h0FibreRank hbetti
            hstruct).prop_of_hom)) ∧
    IsGrc1CurveFamily B hZ ≤ IsH01CurveFamily B hZ ∧
    ∀ X : CurveFamily B hZ, IsGrc1CurveFamily B hZ X →
      X.HasFiniteLocallyFreeFirstHigherDirectImage ∧
        X.FirstHigherDirectImageCommutesWithBaseChange :=
  have hpush : ∀ X : CurveFamily B hZ,
      CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ X →
      HasUniversallyBijectiveGlobalFunctions B hZ X := fun _ hX =>
    CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_hasBijectiveGlobalFunctionsOnFieldFibres
      hstruct hX
  ⟨(curvesGrc1_isOpenSubstack_and_factors_iff B hZ).1,
    (curvesH01_isOpenSubstack_and_factors_iff_of_h01Statements hbetti hstruct).1,
    isGrc1CurveFamily_le_isH01CurveFamily_of hconst hpush,
    fun _ hX =>
      CurveFamily.firstHigherDirectImage_of_isGrc1CurveFamily_of hconst hpush hR1 hR1bc hX⟩

end AlgebraicGeometry

end
