module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGenusDecomposition
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesGenusDecomposition
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesInCurvesDM
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesOfGenus

/-!
# `𝓜̄` and `𝓜̄_g` inside `Curves^{DM}`, granted the relative openness of stable fibres

Granted that `Curves` is algebraic and that stable fibres are relatively open on prestable
families, the moduli stacks `𝓜̄` of stable curves and `𝓜̄_g` of stable curves of genus `g` are open
substacks of `Curves^{DM}` and are Deligne–Mumford stacks.

## Main results

* `exists_curvesDM_moduliStableCurves_le_and_isDeligneMumfordStack_of_hasStableFibres`
  (namespace `AlgebraicGeometry.curvesSmall`): granted the algebraicity of `Curves` (`h`) and the
  relative openness of stable fibres on prestable families (`hrel`), there are open substacks of
  `Curves^{DM}` whose objects are the stable families and the stable families of fibre genus `g`,
  and both are Deligne–Mumford stacks.
* `AlgebraicGeometry.isOpenCurvesLocus_isStableCurveFamily_of_hasStableFibres`,
  `AlgebraicGeometry.isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_hasStableFibres`,
  `AlgebraicGeometry.isOpenCurvesLocus_isStableCurveFamilyOfFibreGenus_of_hasStableFibres`:
  condition (o) for the stable families, for the stable families with `R¹f_*𝒪_X` locally free of
  rank `g`, and for the stable families whose fibres have genus `g`, granted `hrel`.

## References

* [Stacks Project, Tag 0E7A](https://stacks.math.columbia.edu/tag/0E7A)
-/

@[expose] public noncomputable section

open CategoryTheory

universe w u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- The stable families of curves satisfy condition (o), granted the relative openness `hrel` of
stable fibres on prestable families. -/
theorem isOpenCurvesLocus_isStableCurveFamily_of_hasStableFibres
    (hrel : IsOpenCurvesLocusWithin B hZ (IsPrestableCurveFamily B hZ)
      (CurveFamily.HasStableFibres B hZ)) :
    IsOpenCurvesLocus B hZ (IsStableCurveFamily B hZ) :=
  isOpenCurvesLocus_isStableCurveFamily_of_prestable
    (isOpenCurvesLocus_isPrestableCurveFamily_of CurveFamily.isOpenCurvesLocus_isH01CurveFamily)
    hrel

open CurveFamily in
/-- The stable families of curves with `R¹f_*𝒪_X` locally free of rank `g` satisfy condition (o),
granted the relative openness `hrel` of stable fibres on prestable families. -/
theorem isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_hasStableFibres (g : ℕ)
    (hrel : IsOpenCurvesLocusWithin B hZ (IsPrestableCurveFamily B hZ)
      (CurveFamily.HasStableFibres B hZ)) :
    IsOpenCurvesLocus B hZ (IsStableCurveFamilyOfGenus B hZ g) :=
  IsOpenCurvesLocus.of_iff (IsOpenCurvesLocus.and
      (isOpenCurvesLocus_isStableCurveFamily_of_hasStableFibres hrel)
      (isOpenCurvesLocus_isGenusCurveFamily_of
        CurveFamily.isOpenCurvesLocus_hasBijectiveGlobalFunctionsOnFieldFibres
        CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_fieldFibres
        (fun _ => hasFiniteLocallyFreeFirstHigherDirectImage_of_hasResidueFieldGlobalFunctions)
        (fun _ => firstHigherDirectImageCommutesWithBaseChange_of_hasResidueFieldGlobalFunctions)
        g))
    fun _ => ⟨fun h => ⟨h.1, h.2.2⟩,
      fun h => ⟨h.1, isH01CurveFamily_of_isPrestableCurveFamily h.1.1, h.2⟩⟩

/-- The stable families of curves whose fibres all have genus `g`
(`AlgebraicGeometry.IsStableCurveFamilyOfFibreGenus`) satisfy condition (o), granted the relative
openness `hrel` of stable fibres on prestable families. -/
theorem isOpenCurvesLocus_isStableCurveFamilyOfFibreGenus_of_hasStableFibres (g : ℕ)
    (hrel : IsOpenCurvesLocusWithin B hZ (IsPrestableCurveFamily B hZ)
      (CurveFamily.HasStableFibres B hZ)) :
    IsOpenCurvesLocus B hZ (IsStableCurveFamilyOfFibreGenus B hZ g) :=
  IsOpenCurvesLocus.of_iff (isOpenCurvesLocus_isStableCurveFamilyOfGenus_of_hasStableFibres g hrel)
    fun _ => and_congr_right fun h =>
      (CurveFamily.hasFieldPointFibreGenus_iff_hasGenus_of_hasUniversallyBijectiveGlobalFunctions
        h.1.2 g).symm

end AlgebraicGeometry

namespace AlgebraicGeometry.curvesSmall

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}
  (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)

/-- Let `Curves` be algebraic (`h`) and let stable fibres be relatively open on prestable families
(`hrel`). Then there are open substacks `W`, `M`, `M_g` of (the small model of) `Curves` such that
`W` is the Deligne–Mumford locus `Curves^{DM}` and is DM; the objects of `M` are exactly the stable
families of curves, and those of `M_g` exactly the stable families whose fibres all have genus `g`;
and `M` and `M_g` are open substacks of `W`, DM, and Deligne–Mumford stacks. -/
theorem exists_curvesDM_moduliStableCurves_le_and_isDeligneMumfordStack_of_hasStableFibres
    (g : ℕ) (hrel : IsOpenCurvesLocusWithin B hZ (IsPrestableCurveFamily B hZ)
      (CurveFamily.HasStableFibres B hZ)) :
    ∃ W M Mg : Stack.OpenSubstack (curvesAlgebraicStack B hZ h),
      (W.property =
          Stack.dmLocus B integerBase hZ B.contains_terminal (curvesAlgebraicStack B hZ h) ∧
        Stack.AlgebraicStacks.IsAbsolutelyDM B integerBase hZ B.contains_terminal
          W.toAlgebraicStack) ∧
      ((∀ F : CurveFamily B hZ,
          M.property ((curvesSmallEquivalence B hZ h).functor.obj F) ↔ IsStableCurveFamily B hZ F) ∧
        M.property ≤ W.property ∧
        Stack.AlgebraicStacks.IsAbsolutelyDM B integerBase hZ B.contains_terminal
          M.toAlgebraicStack ∧
        Stack.IsDeligneMumfordStack.{u, w} B integerBase hZ M.toAlgebraicStack.val.val) ∧
      ((∀ F : CurveFamily B hZ,
          Mg.property ((curvesSmallEquivalence B hZ h).functor.obj F) ↔
            IsStableCurveFamilyOfFibreGenus B hZ g F) ∧
        Mg.property ≤ W.property ∧
        Stack.AlgebraicStacks.IsAbsolutelyDM B integerBase hZ B.contains_terminal
          Mg.toAlgebraicStack ∧
        Stack.IsDeligneMumfordStack.{u, w} B integerBase hZ Mg.toAlgebraicStack.val.val) := by
  have hst := isOpenCurvesLocus_isStableCurveFamily_of_hasStableFibres hrel
  have hstg := isOpenCurvesLocus_isStableCurveFamilyOfFibreGenus_of_hasStableFibres g hrel
  obtain ⟨W, hW, hWDM, ⟨hM, hMDM, hMD⟩, ⟨hMg, hMgDM, hMgD⟩⟩ :=
    exists_curvesDM_and_le_and_isDeligneMumfordStack_of_stable h
      (fun y₁ y₂ => isSeparated_relocalizeToYoneda_isomSpace y₁ y₂)
      (fun k _ _ X _ _ _ hdim hnodal hg htail hbridge =>
        ⟨fun D₁ D₂ => by
          have e := Stacks.Curves.SheafDerivation.eq_zero_of_hasAtWorstNodalSingularities k X hdim
            hnodal hg htail hbridge
          exact (e D₁).trans (e D₂).symm⟩)
      _ _ (curvesOpenSubstackOfIsOpenCurvesLocus_mono B hZ hstg hst (fun _ hF => hF.1) _ _ _)
      (fun _ _ _ X _ hk hdim hX =>
        stableConditions_of_curvesSmallOpenSubstack_curveFieldPoint h hst X hk hdim hX)
  exact ⟨W, _, _, ⟨hW, hWDM⟩,
    ⟨curvesSmallOpenSubstack_property_iff B hZ h hst, hM, hMDM, hMD⟩,
    ⟨curvesSmallOpenSubstack_property_iff B hZ h hstg, hMg, hMgDM, hMgD⟩⟩

end AlgebraicGeometry.curvesSmall

end
