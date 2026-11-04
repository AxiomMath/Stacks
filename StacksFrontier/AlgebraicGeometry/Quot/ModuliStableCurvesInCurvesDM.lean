module

public import StacksFrontier.AlgebraicGeometry.Curves.VectorFieldsGenus
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGenusH01Statements
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallIsom
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStable
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStableOpen
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesDeligneMumford
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesOfGenusOpen
public import StacksFrontier.AlgebraicGeometry.Quot.StableCurveFamilyOverFieldConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStructureSheafPushforward

/-!
# `𝓜̄` and `𝓜̄_g` inside `Curves^{DM}`, at the open substacks of stable families (towards 0E7A)

Stacks 0E7A: the moduli stacks `𝓜̄` of stable curves and `𝓜̄_g` of stable curves of genus `g` are
open substacks of `Curves^{DM}`; in particular they are DM (Stacks 050D) and Deligne–Mumford
stacks (Stacks 03YO).

`AlgebraicGeometry.curvesSmall.exists_curvesDM_and_le_and_isDeligneMumfordStack_of_stable` proves
this from its inputs. This file discharges three of them and fixes the open substacks:

* `hIsomSep`, the separation step of Stacks 0DSQ, is
  `AlgebraicGeometry.curvesSmall.isSeparated_relocalizeToYoneda_isomSpace`;
* `hvan`, Stacks 0E69, is `Stacks.Curves.SheafDerivation.eq_zero_of_hasAtWorstNodalSingularities`;
* `hU`, the implication (a) ⇒ (b) of part (2) of Stacks 0E76 at the points of the open substack
  of stable families, is
  `AlgebraicGeometry.curvesSmall.stableConditions_of_curvesSmallOpenSubstack_curveFieldPoint`;
* `𝓜̄` is the open substack `AlgebraicGeometry.curvesSmallOpenSubstack` of the small model of
  `Curves` cut out by `AlgebraicGeometry.IsStableCurveFamily` (Stacks 0E75), and `𝓜̄_g` the one
  cut out by `AlgebraicGeometry.IsStableCurveFamilyOfGenus` (condition (1)(b) of Stacks 0E78);
  the inclusion `𝓜̄_g ⊆ 𝓜̄` is the first conjunct of the latter.

## Main results

* `exists_curvesDM_and_le_and_isDeligneMumfordStack_of_isOpenCurvesLocus` (namespace
  `AlgebraicGeometry.curvesSmall`):
  Stacks 0E7A on the algebraicity of `Curves` (`h`, Stacks 0D5A) and the openness of the stable
  locus and of the stable locus of genus `g` (`hst`, `hstg`: Stacks 0E76, 0E78).
* `AlgebraicGeometry.isOpenCurvesLocus_isStableCurveFamily_of_h0FibreRank`: `hst`, from the
  semicontinuity of `h⁰` of the fibres (`hbetti`, Stacks 0E0R at `i = 0`) and the relative
  openness of stable fibres on prestable families (`hrel`, Stacks 0E74 with Stacks 0D3D); Stacks
  0E6B (a) is
  `AlgebraicGeometry.Space.isIso_structureSharp_and_baseChange_of_bijective_algebraMap_fibre`.
* `AlgebraicGeometry.isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_h0FibreRank`: `hstg`, from
  the same inputs and the local freeness of `R¹f_*𝒪_X` and its formation commuting with base
  change on families with `H⁰` of the fibres the residue fields (`h2`, `h3`, Stacks 0E6B (b) and
  0E1J).

## References

* [Stacks Project, Tag 0E7A](https://stacks.math.columbia.edu/tag/0E7A)
* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0E78](https://stacks.math.columbia.edu/tag/0E78)
* [Stacks Project, Tag 0E69](https://stacks.math.columbia.edu/tag/0E69)
* [Stacks Project, Tag 0DSQ](https://stacks.math.columbia.edu/tag/0DSQ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe w u

namespace AlgebraicGeometry.curvesSmall

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}
  (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)

/-- **Stacks 0E7A at the open substacks of stable families, from the remaining inputs.** Let
`Curves` be algebraic (`h`, Stacks 0D5A), let the stable families and the stable families of
genus `g` satisfy condition (o) of Stacks 0E0E (`hst`, `hstg`: the openness of Stacks 0E76 and
0E78). Then there is an open substack `Curves^{DM}` of `Curves` cutting out the
Deligne–Mumford locus and DM (Stacks 0DSW (1)), and `𝓜̄` and `𝓜̄_g` are open substacks of it, DM
(Stacks 050D) and Deligne–Mumford stacks (Stacks 03YO). -/
theorem exists_curvesDM_and_le_and_isDeligneMumfordStack_of_isOpenCurvesLocus (g : ℕ)
    (hst : IsOpenCurvesLocus B hZ (IsStableCurveFamily B hZ))
    (hstg : IsOpenCurvesLocus B hZ (IsStableCurveFamilyOfGenus B hZ g)) :
    ∃ W : Stack.OpenSubstack (curvesAlgebraicStack B hZ h),
      W.property =
        Stack.dmLocus B integerBase hZ B.contains_terminal (curvesAlgebraicStack B hZ h) ∧
      Stack.AlgebraicStacks.IsAbsolutelyDM B integerBase hZ B.contains_terminal
        W.toAlgebraicStack ∧
      ((curvesSmallOpenSubstack B hZ h hst).property ≤ W.property ∧
        Stack.AlgebraicStacks.IsAbsolutelyDM B integerBase hZ B.contains_terminal
          (curvesSmallOpenSubstack B hZ h hst).toAlgebraicStack ∧
        Stack.IsDeligneMumfordStack.{u, w} B integerBase hZ
          (curvesSmallOpenSubstack B hZ h hst).toAlgebraicStack.val.val) ∧
      ((curvesSmallOpenSubstack B hZ h hstg).property ≤ W.property ∧
        Stack.AlgebraicStacks.IsAbsolutelyDM B integerBase hZ B.contains_terminal
          (curvesSmallOpenSubstack B hZ h hstg).toAlgebraicStack ∧
        Stack.IsDeligneMumfordStack.{u, w} B integerBase hZ
          (curvesSmallOpenSubstack B hZ h hstg).toAlgebraicStack.val.val) :=
  exists_curvesDM_and_le_and_isDeligneMumfordStack_of_stable h
    (fun y₁ y₂ => isSeparated_relocalizeToYoneda_isomSpace y₁ y₂)
    (fun k _ _ X _ _ _ hdim hnodal hg htail hbridge =>
      ⟨fun D₁ D₂ =>
        (Stacks.Curves.SheafDerivation.eq_zero_of_hasAtWorstNodalSingularities k X hdim hnodal hg
          htail hbridge D₁).trans
        (Stacks.Curves.SheafDerivation.eq_zero_of_hasAtWorstNodalSingularities k X hdim hnodal hg
          htail hbridge D₂).symm⟩)
    _ _ (curvesOpenSubstackOfIsOpenCurvesLocus_mono B hZ hstg hst (fun _ hF => hF.1) _ _ _)
    (fun _ _ _ X _ hk hdim hX =>
      stableConditions_of_curvesSmallOpenSubstack_curveFieldPoint h hst X hk hdim hX)

end AlgebraicGeometry.curvesSmall

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **The stable families satisfy condition (o)** (the openness of Stacks 0E76), from the
semicontinuity of `h⁰` of the fibres of a proper flat family over a scheme (`hbetti`, Stacks
0E0R at `i = 0`) and the relative openness of stable fibres on prestable families (`hrel`, Stacks
0E74 with Stacks 0D3D). Stacks 0E6B (a) is supplied by
`AlgebraicGeometry.Space.isIso_structureSharp_and_baseChange_of_bijective_algebraMap_fibre`. -/
theorem isOpenCurvesLocus_isStableCurveFamily_of_h0FibreRank
    (hbetti : ∀ {U : BigFppfOver B integerBase hZ} {X : AlgebraicSpaces B integerBase hZ}
      (f : X ⟶ schemeSpace U), Space.IsProper B integerBase hZ f.hom →
      Space.IsFlat B integerBase hZ f.hom → Space.IsFinitePresentation B integerBase hZ f.hom →
      ∃ b : (BigFppfOver.toScheme B integerBase hZ).obj U → ℕ∞, UpperSemicontinuous b ∧
        ∀ p : Space.FieldValuedPoint B integerBase hZ (yoneda.obj U),
          Space.h0FibreRank B integerBase hZ f p = b (Space.schemePoint B integerBase hZ U p))
    (hrel : IsOpenCurvesLocusWithin B hZ (IsPrestableCurveFamily B hZ)
      (CurveFamily.HasStableFibres B hZ)) :
    IsOpenCurvesLocus B hZ (IsStableCurveFamily B hZ) :=
  isOpenCurvesLocus_isStableCurveFamily_of_prestable
    (isOpenCurvesLocus_isPrestableCurveFamily_of
      (CurveFamily.isOpenCurvesLocus_isH01CurveFamily_of_h0FibreRank hbetti
        (fun f hf hfl hfp h =>
          Space.isIso_structureSharp_and_baseChange_of_bijective_algebraMap_fibre B integerBase hZ
            f hf hfl hfp h))) hrel

/-- **The stable families of genus `g` satisfy condition (o)** (the openness of Stacks 0E78),
from the inputs of `AlgebraicGeometry.isOpenCurvesLocus_isStableCurveFamily_of_h0FibreRank` and
the local freeness of `R¹f_*𝒪_X` and its formation commuting with base change on families whose
fibres have `H⁰` the residue fields (`h2`, `h3`): a stable family is in `Curves^{h0,1}`, so it has
genus `g` in the sense of Stacks 0E78 exactly when it lies in the open locus `Curves_g` of
`AlgebraicGeometry.isOpenCurvesLocus_isGenusCurveFamily_of_h01Statements`. -/
theorem isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_h0FibreRank (g : ℕ)
    (hbetti : ∀ {U : BigFppfOver B integerBase hZ} {X : AlgebraicSpaces B integerBase hZ}
      (f : X ⟶ schemeSpace U), Space.IsProper B integerBase hZ f.hom →
      Space.IsFlat B integerBase hZ f.hom → Space.IsFinitePresentation B integerBase hZ f.hom →
      ∃ b : (BigFppfOver.toScheme B integerBase hZ).obj U → ℕ∞, UpperSemicontinuous b ∧
        ∀ p : Space.FieldValuedPoint B integerBase hZ (yoneda.obj U),
          Space.h0FibreRank B integerBase hZ f p = b (Space.schemePoint B integerBase hZ U p))
    (hrel : IsOpenCurvesLocusWithin B hZ (IsPrestableCurveFamily B hZ)
      (CurveFamily.HasStableFibres B hZ))
    (h2 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.HasFiniteLocallyFreeFirstHigherDirectImage)
    (h3 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.FirstHigherDirectImageCommutesWithBaseChange) :
    IsOpenCurvesLocus B hZ (IsStableCurveFamilyOfGenus B hZ g) :=
  IsOpenCurvesLocus.of_iff (IsOpenCurvesLocus.and
      (isOpenCurvesLocus_isStableCurveFamily_of_h0FibreRank hbetti hrel)
      (isOpenCurvesLocus_isGenusCurveFamily_of_h01Statements hbetti
        (fun f hf hfl hfp h =>
          Space.isIso_structureSharp_and_baseChange_of_bijective_algebraMap_fibre B integerBase hZ
            f hf hfl hfp h) h2 h3 g))
    fun _ => ⟨fun h => ⟨h.1, h.2.2⟩,
      fun h => ⟨h.1, isH01CurveFamily_of_isPrestableCurveFamily h.1.1, h.2⟩⟩

end AlgebraicGeometry

end
