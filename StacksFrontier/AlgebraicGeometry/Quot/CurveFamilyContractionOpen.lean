module

public import StacksFrontier.AlgebraicGeometry.Quot.UniversalStructureContractionOpenOfCharts
public import StacksFrontier.AlgebraicGeometry.Quot.EtaleLocallyProjectiveCurvesAmpleFibre

/-!
# Morphisms of families of curves contracting the structure sheaf near a fibre (Stacks 0E88)

Let `S` be a scheme, `s ∈ S`, and let `f : X → S` and `g : Y → S` be families of curves
(Stacks 0D4Z) with a morphism `c : X → Y` over `S`. Stacks 0E88 says: if
`c_{s,*}𝒪_{X_s} = 𝒪_{Y_s}` and `R¹c_{s,*}𝒪_{X_s} = 0`, then after replacing `S` by an open
neighbourhood of `s` we have `𝒪_Y = c_*𝒪_X` and `R¹c_*𝒪_X = 0`, and this remains true after
base change by any morphism `S' → S`.

## Main results

* `AlgebraicGeometry.CurveFamily.exists_isOpen_forall_isStructureContraction_baseChange`:
  Stacks 0E88.

## Implementation notes

The conclusion is stated in the vocabulary of `AlgebraicGeometry.Space.IsStructureContraction`, as
in `AlgebraicGeometry.CurveFamily.exists_isOpen_isStructureContraction_of_hasEtaleSchemeChartAt`:
an open `W ∋ s` of the base such that for every scheme `T` of the site over `S` landing in `W`
and every base change `c' : X_T ⟶ Y_T` of `c`, `𝒪_{Y_T} = c'_*𝒪_{X_T}` and
`R¹c'_*𝒪_{X_T} = 0`. Taking `T = W` gives the statement over `W`; the quantification over `T` is
the persistence under base change.

## References

* [Stacks Project, Tag 0E88](https://stacks.math.columbia.edu/tag/0E88)
* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
* [Stacks Project, Tag 0E7L](https://stacks.math.columbia.edu/tag/0E7L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- Let `S` be a scheme, `s ∈ S`, and `c : X ⟶ Y` a morphism over `S` of families of curves. If
`c_{s,*}𝒪_{X_s} = 𝒪_{Y_s}` and `R¹c_{s,*}𝒪_{X_s} = 0`, there is an open neighbourhood `W` of `s`
such that for every scheme `T ⟶ S` landing in `W` and every base change `c' : X_T ⟶ Y_T` of `c`,
`𝒪_{Y_T} = c'_*𝒪_{X_T}` and `R¹c'_*𝒪_{X_T} = 0`. Taking `T = W` gives the statement over `W`,
and the quantification over `T` is the persistence under base change. -/
@[stacks 0E88]
theorem exists_isOpen_forall_isStructureContraction_baseChange
    (X Y : CurveFamily B hZ) (hb : Y.base = X.base) (c : X.total ⟶ Y.total)
    (hc : c ≫ Y.toBase ≫ eqToHom (congrArg schemeSpace hb) = X.toBase) (s : X.base.left.1)
    (hs : Space.IsStructureContraction B integerBase hZ
      (Space.structureContractionBaseChange B integerBase hZ c hc
        (schemeSpaceMap (Space.residueFieldMap B integerBase hZ X.base s
          (B.residueField_spec_contains X.base.left.property s))))) :
    ∃ W : X.base.left.1.Opens, s ∈ W ∧
      ∀ (T : BigFppfOver B integerBase hZ) (h : T ⟶ X.base),
        (∀ t, ((𝒯).map h).base t ∈ W) →
        ∀ (X' Y' : AlgebraicSpaces B integerBase hZ) (pX' : X' ⟶ X.total)
          (fX' : X' ⟶ schemeSpace T) (pY' : Y' ⟶ Y.total) (fY' : Y' ⟶ schemeSpace T)
          (c' : X' ⟶ Y'),
          IsPullback pX' fX' X.toBase (schemeSpaceMap h) →
          IsPullback pY' fY' (Y.toBase ≫ eqToHom (congrArg schemeSpace hb)) (schemeSpaceMap h) →
          c' ≫ pY' = pX' ≫ c → c' ≫ fY' = fX' →
          Space.IsStructureContraction B integerBase hZ c' :=
  exists_isOpen_isStructureContraction_of_hasEtaleSchemeChartAt X Y hb c hc s
    (X.hasEtaleSchemeChartAt s) (Y.hasEtaleSchemeChartAt _) hs

end CurveFamily

end AlgebraicGeometry

end
