module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyContraction
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyIsSmoothLocallyPolarized
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedHigherDirectImageAssociatedModule

/-!
# Structure contractions of families of curves, from Picard charts

Assuming the Picard-chart hypothesis `hchart` (Stacks 0D04 with Stacks 09DS, and Stacks 0DPJ),
the conclusion of Stacks 0E88 holds: for a morphism `c : X ⟶ Y` over `S` of families of curves
and `s ∈ S` with `c_{s,*}𝒪_{X_s} = 𝒪_{Y_s}` and `R¹c_{s,*}𝒪_{X_s} = 0`, there is an open
neighbourhood of `s` over which `𝒪_Y = c_*𝒪_X` and `R¹c_*𝒪_X = 0`, and this persists after any
base change.

## Main results

* `AlgebraicGeometry.CurveFamily.exists_isOpen_isStructureContraction_of_picardCharts`: Stacks
  0E88, given `hchart`.

## References

* [Stacks Project, Tag 0E88](https://stacks.math.columbia.edu/tag/0E88)
* [Stacks Project, Tag 0DQ0](https://stacks.math.columbia.edu/tag/0DQ0)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
* [Stacks Project, Tag 0D04](https://stacks.math.columbia.edu/tag/0D04)
* [Stacks Project, Tag 09DS](https://stacks.math.columbia.edu/tag/09DS)
* [Stacks Project, Tag 0DPJ](https://stacks.math.columbia.edu/tag/0DPJ)
* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- **Stacks 0E88, given the Picard-chart hypothesis `hchart`.** Let `S` be a scheme, `s ∈ S`,
and `c : X ⟶ Y` a morphism over `S` of families of curves. If `c_{s,*}𝒪_{X_s} = 𝒪_{Y_s}` and
`R¹c_{s,*}𝒪_{X_s} = 0`, there is an open neighbourhood `W` of `s` such that for every scheme
`T ⟶ S` landing in `W` and every base change `c' : X_T ⟶ Y_T` of `c`, `𝒪_{Y_T} = c'_*𝒪_{X_T}`
and `R¹c'_*𝒪_{X_T} = 0`. -/
theorem exists_isOpen_isStructureContraction_of_picardCharts
    (hchart : ∀ (X : CurveFamily B hZ) (K : Type u) (_ : Field K)
      (hK : B.Contains (Spec (.of K)))
      (x : (schemeOverIntegers B).obj (B.obj hK) ⟶ X.base)
      (A₀ : Space.PicardObject X.picardSituation), A₀.T = X.picardTestScheme x →
        A₀.IsInAmpleLocus →
        ∃ (T' : BigFppfOver B integerBase hZ) (π : T' ⟶ X.base),
          Smooth ((BigFppfOver.toScheme B integerBase hZ).map π) ∧
          ∃ (A : Space.PicardObject X.picardSituation) (hA : A.T = X.picardTestScheme π)
            (K' : Type u) (_ : Field K') (hK' : B.Contains (Spec (.of K')))
            (y : (schemeOverIntegers B).obj (B.obj hK') ⟶ T')
            (e : (schemeOverIntegers B).obj (B.obj hK') ⟶ (schemeOverIntegers B).obj (B.obj hK)),
            y ≫ π = e ≫ x ∧
            (Space.PicardSituation.pullbackObject A
              (X.picardTestSchemeMap y π ≫ eqToHom hA.symm)).IsInAmpleLocus)
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
  exists_isOpen_isStructureContraction_of_isSmoothLocallyPolarized
    (isSmoothLocallyPolarized hchart)
    (fun g' hqc' hsep' F hF j =>
      Space.nonempty_rightDerived_modulePushforward_representedAssociatedModule_of_isSeparated
        B integerBase hZ g' hqc' hsep' F hF j)
    X Y hb c hc s hs

end CurveFamily

end AlgebraicGeometry

end
