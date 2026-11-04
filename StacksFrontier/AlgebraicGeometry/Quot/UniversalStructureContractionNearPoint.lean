module

public import StacksFrontier.AlgebraicGeometry.Quot.UniversalStructureContractionOpenOfCharts
public import StacksFrontier.AlgebraicGeometry.Quot.PrestableStabilization

/-!
# Universal structure contractions near a point of the base

Let `c : X ⟶ Y` be a morphism over `S` of families of curves (Stacks 0D4Z) and `s ∈ S`. The
conclusion of Stacks 0E88 is that, after replacing `S` by an open neighbourhood `W` of `s`, we
have `𝒪_Y = c_*𝒪_X` and `R¹c_*𝒪_X = 0`, and this remains true after any base change `T ⟶ W`.
This file names that conclusion in the vocabulary of condition (1) of Stacks 0E8A
(`AlgebraicGeometry.CurveFamily.IsUniversalStructureContraction`):

* `AlgebraicGeometry.CurveFamily.IsUniversalStructureContractionOver X Y hb c W`: condition (1)
  of Stacks 0E8A for all base changes along schemes `T ⟶ S` landing in the open `W`;
* `AlgebraicGeometry.CurveFamily.HasUniversalStructureContractionNear X Y hb c s`: this holds for
  some open neighbourhood `W` of `s`.

Over `W = S` the first is condition (1) of Stacks 0E8A itself. Stacks 0E88 says that the second
holds as soon as `c_s` is a structure contraction (`c_{s,*}𝒪_{X_s} = 𝒪_{Y_s}` and
`R¹c_{s,*}𝒪_{X_s} = 0`); this file proves that implication when both families have étale scheme
charts at `s` (the pointwise conclusion of Stacks 0E6F), from
`AlgebraicGeometry.CurveFamily.exists_isOpen_isStructureContraction_of_hasEtaleSchemeChartAt`.

## Main definitions

* `AlgebraicGeometry.CurveFamily.IsUniversalStructureContractionOver`
* `AlgebraicGeometry.CurveFamily.HasUniversalStructureContractionNear`

## Main results

* `CurveFamily.IsUniversalStructureContractionOver.isUniversalStructureContraction`:
  over the whole base, condition (1) of Stacks 0E8A.
* `AlgebraicGeometry.CurveFamily.hasUniversalStructureContractionNear_of_hasEtaleSchemeChartAt`:
  Stacks 0E88 at a point where both families have étale scheme charts.

## References

* [Stacks Project, Tag 0E88](https://stacks.math.columbia.edu/tag/0E88)
* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- **Condition (1) of Stacks 0E8A over an open of the base.** For a morphism `c : X ⟶ Y` over
the common base `S` of two families of curves and an open `W ⊆ S`: for every scheme `T` of the
site with a morphism `h : T ⟶ S` landing in `W`, whenever `X'` and `Y'` are the fibre products
`X ×_S T` and `Y ×_S T` and `c' : X' ⟶ Y'` is the morphism induced by `c`, the structure map
`𝒪_{Y'} ⟶ c'_*𝒪_{X'}` is an isomorphism and `R¹c'_*𝒪_{X'} = 0`. -/
def IsUniversalStructureContractionOver (X Y : CurveFamily B hZ) (hb : Y.base = X.base)
    (c : X.total ⟶ Y.total) (W : X.base.left.1.Opens) : Prop :=
  ∀ (T : BigFppfOver B integerBase hZ) (h : T ⟶ X.base),
    (∀ t, ((𝒯).map h).base t ∈ W) →
    ∀ (X' Y' : AlgebraicSpaces B integerBase hZ) (pX' : X' ⟶ X.total)
      (fX' : X' ⟶ schemeSpace T) (pY' : Y' ⟶ Y.total) (fY' : Y' ⟶ schemeSpace T)
      (c' : X' ⟶ Y'),
      IsPullback pX' fX' X.toBase (schemeSpaceMap h) →
      IsPullback pY' fY' (Y.toBase ≫ eqToHom (congrArg schemeSpace hb)) (schemeSpaceMap h) →
      c' ≫ pY' = pX' ≫ c → c' ≫ fY' = fX' →
      Space.IsStructureContraction B integerBase hZ c'

/-- **The conclusion of Stacks 0E88 at a point.** There is an open neighbourhood `W` of `s` in
the base over which `c` satisfies condition (1) of Stacks 0E8A
(`AlgebraicGeometry.CurveFamily.IsUniversalStructureContractionOver`). -/
def HasUniversalStructureContractionNear (X Y : CurveFamily B hZ) (hb : Y.base = X.base)
    (c : X.total ⟶ Y.total) (s : X.base.left.1) : Prop :=
  ∃ W : X.base.left.1.Opens, s ∈ W ∧ IsUniversalStructureContractionOver X Y hb c W

/-- Over the whole base, `AlgebraicGeometry.CurveFamily.IsUniversalStructureContractionOver` is
condition (1) of Stacks 0E8A. -/
theorem IsUniversalStructureContractionOver.isUniversalStructureContraction
    {X Y : CurveFamily B hZ} {hb : Y.base = X.base} {c : X.total ⟶ Y.total}
    (h : IsUniversalStructureContractionOver X Y hb c ⊤) :
    IsUniversalStructureContraction B hZ X Y hb c :=
  fun T g X' Y' pX' fX' pY' fY' c' h₁ h₂ h₃ h₄ =>
    h T g (fun _ => trivial) X' Y' pX' fX' pY' fY' c' h₁ h₂ h₃ h₄

/-- Condition (1) of Stacks 0E8A gives it over every open of the base. -/
theorem IsUniversalStructureContraction.isUniversalStructureContractionOver
    {X Y : CurveFamily B hZ} {hb : Y.base = X.base} {c : X.total ⟶ Y.total}
    (h : IsUniversalStructureContraction B hZ X Y hb c) (W : X.base.left.1.Opens) :
    IsUniversalStructureContractionOver X Y hb c W :=
  fun T g _ X' Y' pX' fX' pY' fY' c' h₁ h₂ h₃ h₄ => h T g X' Y' pX' fX' pY' fY' c' h₁ h₂ h₃ h₄

open Stacks.AlgebraicGeometry.TopDegreeBaseChange Space in
/-- **Stacks 0E88 at a point with étale scheme charts.** Let `c : X ⟶ Y` be a morphism over `S`
of families of curves and `s ∈ S` a point at which both families have étale scheme charts (the
pointwise conclusion of Stacks 0E6F). If `c_{s,*}𝒪_{X_s} = 𝒪_{Y_s}` and `R¹c_{s,*}𝒪_{X_s} = 0`,
then `c` is a universal structure contraction over an open neighbourhood of `s`. -/
theorem hasUniversalStructureContractionNear_of_hasEtaleSchemeChartAt
    (X Y : CurveFamily B hZ) (hb : Y.base = X.base) (c : X.total ⟶ Y.total)
    (hc : c ≫ Y.toBase ≫ eqToHom (congrArg schemeSpace hb) = X.toBase) (s : X.base.left.1)
    (hXs : X.HasEtaleSchemeChartAt s) (hYs : Y.HasEtaleSchemeChartAt (cast (by rw [hb]; rfl) s))
    (hs : Space.IsStructureContraction B integerBase hZ
      (Space.structureContractionBaseChange B integerBase hZ c hc
        (schemeSpaceMap (Space.residueFieldMap B integerBase hZ X.base s
          (B.residueField_spec_contains X.base.left.property s))))) :
    HasUniversalStructureContractionNear X Y hb c s :=
  exists_isOpen_isStructureContraction_of_hasEtaleSchemeChartAt X Y hb c hc s hXs hYs hs

end CurveFamily

end AlgebraicGeometry

end
