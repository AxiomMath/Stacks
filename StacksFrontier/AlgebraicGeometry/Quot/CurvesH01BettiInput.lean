module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01Inputs
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStructureSheafPushforward

/-!
# Stacks 0E6I over the Betti input alone

`AlgebraicGeometry.CurveFamily.isOpenCurvesLocus_isH01CurveFamily_of_h0FibreRank` and
`AlgebraicGeometry.curvesH01_isOpenSubstack_and_factors_iff_and_over_field_iff_of_statements`
prove condition (o) of Stacks 0E0E for `Curves^{h0,1}`, and Stacks 0E6I itself, from two inputs:
`hbetti`, the statement of Stacks 0E0R at `i = 0` for `𝓕 = 𝒪_X`, and `hstruct`, the statement of
Stacks 0E6B part (a). This file removes the second input: `hstruct` is the type of
`AlgebraicGeometry.Space.isIso_structureSharp_and_baseChange_of_bijective_algebraMap_fibre`
specialized to the base `Spec(ℤ)`, so it is supplied by that declaration and need not be assumed.
The conclusions are unchanged; only the hypotheses are fewer.

## Main results

* `AlgebraicGeometry.CurveFamily.isOpenCurvesLocus_isH01CurveFamily_of_betti`: condition (o) of
  Stacks 0E0E for `Curves^{h0,1}`, from the statement of Stacks 0E0R at `i = 0` alone.
* `AlgebraicGeometry.curvesH01_isOpenSubstack_and_factors_iff_and_over_field_iff_of_betti`:
  Stacks 0E6I, parts (1) and (2), from the statement of Stacks 0E0R at `i = 0` alone.

## The withheld registration

Neither declaration of this file carries a `stacks` attribute for tag **0E6I**, because one input
remains.

* `hstruct` — **Stacks 0E6B, part (a)** — is *discharged* here. This library already carries that
  statement, untagged, as
  `AlgebraicGeometry.Space.isIso_structureSharp_and_baseChange_of_bijective_algebraMap_fibre`
  (`StacksFrontier/AlgebraicGeometry/Spaces/ProperFlatStructureSheafPushforward.lean`), and the
  binder is filled by the bare application
  `AlgebraicGeometry.Space.isIso_structureSharp_and_baseChange_of_bijective_algebraMap_fibre B
  integerBase hZ`.
  The tag 0E6B is not yet proved here, which registers it on
  exactly that declaration; so the tag is not claimed here, only the mathematics is used.
* `hbetti` — **Stacks 0E0R at `i = 0`** (for `𝓕 = 𝒪_X`), stated for algebraic spaces over
  `Spec(ℤ)` — is the one remaining input, and it is likewise not yet proved here. It is not
  discharged here: the Stacks statement is phrased
  in terms of a `ℕ`-valued fibre Betti number that exists in no form in this library, so the
  binder cannot even be put in their words, and the route from the Stacks 0CTM and 0E0S machinery
  this library does carry is not taken here. The comparison its discharge still needs is
  recorded in the withheld-registration note of
  `StacksFrontier.AlgebraicGeometry.Quot.CurvesH01Inputs`.

Because `hbetti` is open, the 0E6I registration stays withheld, exactly as it is on the two-input
forms of `StacksFrontier.AlgebraicGeometry.Quot.CurvesH01Inputs`.

## References

* [Stacks Project, Tag 0E6I](https://stacks.math.columbia.edu/tag/0E6I)
* [Stacks Project, Tag 0E6B](https://stacks.math.columbia.edu/tag/0E6B)
* [Stacks Project, Tag 0E0R](https://stacks.math.columbia.edu/tag/0E0R)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace CurveFamily

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **Condition (o) of Stacks 0E0E for `Curves^{h0,1}`, from the statement of Stacks 0E0R at
`i = 0`.** The hypothesis `hbetti` is parts (1) and (2) of Stacks 0E0R for `i = 0` and
`𝓕 = 𝒪_X`, with `dim_k H⁰(X_k, 𝒪)` read as `AlgebraicGeometry.Space.h0FibreRank`. The second
input of `AlgebraicGeometry.CurveFamily.isOpenCurvesLocus_isH01CurveFamily_of_h0FibreRank`,
Stacks 0E6B part (a), is supplied by
`AlgebraicGeometry.Space.isIso_structureSharp_and_baseChange_of_bijective_algebraMap_fibre`. -/
theorem isOpenCurvesLocus_isH01CurveFamily_of_betti
    (hbetti : ∀ {U : BigFppfOver B integerBase hZ} {X : AlgebraicSpaces B integerBase hZ}
      (f : X ⟶ schemeSpace U), Space.IsProper B integerBase hZ f.hom →
      Space.IsFlat B integerBase hZ f.hom → Space.IsFinitePresentation B integerBase hZ f.hom →
      ∃ b : (BigFppfOver.toScheme B integerBase hZ).obj U → ℕ∞, UpperSemicontinuous b ∧
        ∀ p : Space.FieldValuedPoint B integerBase hZ (yoneda.obj U),
          Space.h0FibreRank B integerBase hZ f p = b (Space.schemePoint B integerBase hZ U p)) :
    IsOpenCurvesLocus B hZ (IsH01CurveFamily B hZ) :=
  isOpenCurvesLocus_isH01CurveFamily_of_h0FibreRank hbetti
    (Space.isIso_structureSharp_and_baseChange_of_bijective_algebraMap_fibre B integerBase hZ)

end CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **Stacks 0E6I, parts (1) and (2), from the statement of Stacks 0E0R at `i = 0`.** The
hypothesis `hbetti` is parts (1) and (2) of Stacks 0E0R for `i = 0` and `𝓕 = 𝒪_X`, with `H⁰` read
as global functions. Then `Curves^{h0,1} ⊂ Curves` is an open substack such that
1. the classifying morphism of a family of curves `f : X → S` factors through it exactly when
   `f_*𝒪_X = 𝒪_S`, universally, and the fibres of `f` have dimension `1`;
2. for a proper scheme `X = T` of dimension at most one over a field `k = W`, the classifying
   morphism `Spec k → Curves` of `X` factors through it exactly when `H⁰(X, 𝒪_X) = k` and
   `dim(X) = 1`.

This is
`AlgebraicGeometry.curvesH01_isOpenSubstack_and_factors_iff_and_over_field_iff_of_statements`
with its second input, Stacks 0E6B part (a), supplied by
`AlgebraicGeometry.Space.isIso_structureSharp_and_baseChange_of_bijective_algebraMap_fibre`. -/
theorem curvesH01_isOpenSubstack_and_factors_iff_and_over_field_iff_of_betti
    (hbetti : ∀ {U : BigFppfOver B integerBase hZ} {X : AlgebraicSpaces B integerBase hZ}
      (f : X ⟶ schemeSpace U), Space.IsProper B integerBase hZ f.hom →
      Space.IsFlat B integerBase hZ f.hom → Space.IsFinitePresentation B integerBase hZ f.hom →
      ∃ b : (BigFppfOver.toScheme B integerBase hZ).obj U → ℕ∞, UpperSemicontinuous b ∧
        ∀ p : Space.FieldValuedPoint B integerBase hZ (yoneda.obj U),
          Space.h0FibreRank B integerBase hZ f p = b (Space.schemePoint B integerBase hZ U p)) :
    (ObjectProperty.IsClosedUnderIsomorphisms (IsH01CurveFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ (IsH01CurveFamily B hZ)
          (CurveFamily.isOpenCurvesLocus_isH01CurveFamily_of_betti hbetti).prop_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsH01CurveFamily B hZ)
          (CurveFamily.isOpenCurvesLocus_isH01CurveFamily_of_betti hbetti).prop_of_hom)) ∧
    (∀ (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsH01CurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsH01CurveFamily B hZ) = y) ↔
        IsH01CurveFamily B hZ (y.obj (Over.mk (𝟙 U.left))))) ∧
    (∀ {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W) (k : Type u) [Field k]
      (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
      (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
      (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
      (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
      (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
      (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
      (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
      (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
      (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      (y.obj (Over.mk (𝟙 U.left)) ≅
        curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsH01CurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsH01CurveFamily B hZ) = y) ↔
        Function.Bijective ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW).appTop ∧
          topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1)) :=
  curvesH01_isOpenSubstack_and_factors_iff_and_over_field_iff_of_statements hbetti
    (Space.isIso_structureSharp_and_baseChange_of_bijective_algebraMap_fibre B integerBase hZ)

end AlgebraicGeometry

end
