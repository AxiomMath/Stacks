module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFirstCohomology
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmoothH0
public import StacksFrontier.AlgebraicGeometry.Quot.StableCurveFamilies
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordStack
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackDenseTestProper

/-!
# The moduli stack of stable curves of genus `g` (towards Stacks 0E9C)

Inside the small model `curvesAlgebraicStack B hZ h` of the stack of curves, this file names the
loci `𝓜̄_g` and `𝓜_g` of Stacks 0E78 and Stacks 0E83, and proves the assembly of **Stacks 0E9C**
from the results its proof cites: for `g ≥ 2`, `𝓜̄_g` is a Deligne–Mumford stack, proper and
smooth over `Spec(ℤ)`, and `𝓜_g` is a dense open substack of it.

## Main definitions

* `AlgebraicGeometry.IsStableGenusCurveFamily`: condition (1)(b) of Stacks 0E78 — the family is
  stable (Stacks 0E75) and `R¹f_*𝒪_X` is a finite locally free `𝒪_S`-module of rank `g`.
* `AlgebraicGeometry.IsSmoothGenusCurveFamily`: condition (1)(b) of Stacks 0E83 — `f` is smooth,
  `f_*𝒪_X = 𝒪_S` after every base change (`AlgebraicGeometry.IsSmoothH0CurveFamily`), and
  `R¹f_*𝒪_X` is a finite locally free `𝒪_S`-module of rank `g`.

## Main results

* `AlgebraicGeometry.moduliStableCurves_isDeligneMumford_proper_smooth_of`: the statement of
  Stacks 0E9C, from the inputs listed below.

## Implementation notes

The open substacks `𝓜̄_g`, `𝓜_g` of the small model are
`AlgebraicGeometry.curvesSmallOpenSubstack` of the two loci, given condition (o) of Section 0E0E
for them (the open-substack halves of Stacks 0E78 and 0E83). Properness is **not** an input: it is
proved by Stacks 0CQM applied to `𝓜_g ⟶ 𝓜̄_g ⟶ Spec(ℤ)`
(`isProper_inclusion_comp_structureMorphism_of_denseTestExistence` in
`AlgebraicGeometry.Stack.AlgebraicStacks`), from separation (Stacks 0E9A), quasi-compactness
(Stacks 0E9B), the local finite presentation of `Curves ⟶ Spec(ℤ)` (Stacks 0DSS), density
(Stacks 0E87), and the existence of dotted arrows along `𝓜_g ⟶ 𝓜̄_g` over discrete valuation
rings; the morphism of 2-categories `𝓜_g ⟶ 𝓜̄_g` is the factorization of the inclusion given by
the containment of point sets of Stacks 0E87, through Stacks 06FJ. The inputs, each an explicit
hypothesis, are

* `h`: the stack of curves is algebraic (Stacks 0D5A), the argument of `curvesAlgebraicStack`;
* `hP`, `hQ`: condition (o) for `𝓜̄_g` and `𝓜_g` (Stacks 0E78 and 0E83);
* `hcurves`: `Curves ⟶ Spec(ℤ)` is quasi-separated and locally of finite presentation
  (Stacks 0DSS);
* `hDM`: `𝓜̄_g` is a Deligne–Mumford stack (Stacks 0E7A);
* `hsmooth`: `𝓜̄_g ⟶ Spec(ℤ)` is smooth (Stacks 0E79);
* `hopen`: `|𝓜_g| ⊆ |𝓜̄_g|` is a dense subset (Stacks 0E87), read in `|Curves|`;
* `hsep`, `hqc`: `𝓜̄_g` is separated (Stacks 0E9A) and quasi-compact (Stacks 0E9B);
* `hchow`: Chow's lemma for algebraic stacks (Stacks 0CQ8), as Stacks 0CQM takes it;
* `hlift`: the hypothesis of Stacks 0CQM for `𝓜_g ⟶ 𝓜̄_g ⟶ Spec(ℤ)`, which the source obtains
  from the stable reduction theorem (Stacks 0E98) through the moduli interpretation of `𝓜_g` and
  `𝓜̄_g`.

## References

* [Stacks Project, Tag 0E9C](https://stacks.math.columbia.edu/tag/0E9C)
* [Stacks Project, Tag 0E78](https://stacks.math.columbia.edu/tag/0E78)
* [Stacks Project, Tag 0E83](https://stacks.math.columbia.edu/tag/0E83)
* [Stacks Project, Tag 0CQM](https://stacks.math.columbia.edu/tag/0CQM)
* [Stacks Project, Tag 0E98](https://stacks.math.columbia.edu/tag/0E98)
-/

@[expose] public section

open CategoryTheory Topology

universe u w

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **The families of `𝓜̄_g`** (condition (1)(b) of Stacks 0E78): the family of curves
`f : X → S` is stable and `R¹f_*𝒪_X` is a finite locally free `𝒪_S`-module of rank `g`. -/
abbrev IsStableGenusCurveFamily (g : ℕ) (X : CurveFamily B hZ) : Prop :=
  IsStableCurveFamily B hZ X ∧
    RingedSite.IsFiniteLocallyFreeOfRank
      (Space.smallEtaleRingedSite B integerBase hZ (schemeSpace X.base).1 (schemeSpace X.base).2)
      (X.firstDirectImage B hZ) g

/-- **The families of `𝓜_g`** (condition (1)(b) of Stacks 0E83): the family of curves
`f : X → S` is smooth, `f_*𝒪_X = 𝒪_S` holds after every base change, and `R¹f_*𝒪_X` is a finite
locally free `𝒪_S`-module of rank `g`. -/
abbrev IsSmoothGenusCurveFamily (g : ℕ) (X : CurveFamily B hZ) : Prop :=
  IsSmoothH0CurveFamily B hZ X ∧
    RingedSite.IsFiniteLocallyFreeOfRank
      (Space.smallEtaleRingedSite B integerBase hZ (schemeSpace X.base).1 (schemeSpace X.base).2)
      (X.firstDirectImage B hZ) g

variable (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)

/-- **The assembly of Stacks 0E9C.** Let `g ≥ 2`, and let `𝓜̄_g` and `𝓜_g` be the open substacks
of the small model of the stack of curves cut out by `IsStableGenusCurveFamily g` and
`IsSmoothGenusCurveFamily g`. Then `𝓜̄_g` is a Deligne–Mumford stack, proper and smooth over
`Spec(ℤ)`, and `𝓜_g` is an open substack of `𝓜̄_g` whose points are dense in `|𝓜̄_g|`.

The inputs are the results the source cites (see the module documentation): `hP`, `hQ`
(Stacks 0E78, 0E83), `hcurves` (Stacks 0DSS), `hDM` (Stacks 0E7A), `hsmooth` (Stacks 0E79),
`hopen` (Stacks 0E87), `hsep` (Stacks 0E9A), `hqc` (Stacks 0E9B), `hchow` (Stacks 0CQ8, as
Stacks 0CQM takes it), and `hlift`, the hypothesis of Stacks 0CQM for `𝓜_g ⟶ 𝓜̄_g ⟶ Spec(ℤ)`,
which the source reads off the stable reduction theorem (Stacks 0E98). Properness is proved from
them by Stacks 0CQM. -/
theorem moduliStableCurves_isDeligneMumford_proper_smooth_of (g : ℕ) (hg : 2 ≤ g)
    (hP : IsOpenCurvesLocus B hZ (IsStableGenusCurveFamily B hZ g))
    (hQ : IsOpenCurvesLocus B hZ (IsSmoothGenusCurveFamily B hZ g))
    (hcurves : Stack.AlgebraicStacks.IsQuasiSeparated B integerBase hZ
        (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) ∧
      Stack.AlgebraicStacks.IsLocallyOfFinitePresentation B integerBase hZ
        (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)))
    (hDM : Stack.IsDeligneMumfordStack.{u, w} B integerBase hZ
      (curvesSmallOpenSubstack B hZ h hP).toAlgebraicStack.val.val)
    (hsmooth : IsSmoothOverIntegers B hZ h hP)
    (hopen : (curvesSmallOpenSubstack B hZ h hQ).pointSet ⊆
        (curvesSmallOpenSubstack B hZ h hP).pointSet ∧
      (curvesSmallOpenSubstack B hZ h hP).pointSet ⊆
        @closure _ (Stack.pointTopology B integerBase hZ (curvesAlgebraicStack B hZ h).val)
          (curvesSmallOpenSubstack B hZ h hQ).pointSet)
    (hsep : Stack.AlgebraicStacks.IsSeparated B integerBase hZ
      ((curvesSmallOpenSubstack B hZ h hP).inclusion ≫
        Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)))
    (hqc : Stack.IsQuasiCompactStack.{u, w} B integerBase hZ
      (curvesSmallOpenSubstack B hZ h hP).toAlgebraicStack.val
      (curvesSmallOpenSubstack B hZ h hP).toAlgebraicStack.property)
    (hchow : ∀ (hT : B.Contains (⊤_ Scheme.{u}))
      {𝒳' : Stack.AlgebraicStacks.{u, w} B integerBase hZ}
      {Y : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B integerBase hZ Y),
      Space.IsQuasiCompactSpace B integerBase hZ Y →
      Space.IsAbsolutelyQuasiSeparated B integerBase hZ hT Y →
      ∀ (f' : 𝒳' ⟶ Stack.algebraicSpaceStack.{u, w} B integerBase hZ Y hY),
        Stack.AlgebraicStacks.IsSeparated B integerBase hZ f' →
        Stack.AlgebraicStacks.IsFiniteType B integerBase hZ f' →
        ∃ (X Xbar : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u)
          (hX : IsAlgebraicSpace B integerBase hZ X)
          (_ : IsAlgebraicSpace B integerBase hZ Xbar)
          (a : Stack.algebraicSpaceStack.{u, w} B integerBase hZ X hX ⟶ 𝒳')
          (i : X ⟶ Xbar) (g : Xbar ⟶ Y),
          Stack.AlgebraicStacks.IsProper B integerBase hZ a ∧
          Stack.IsSurjective B integerBase hZ a ∧
          Space.IsOpenImmersion B integerBase hZ i ∧ Space.IsProper B integerBase hZ g ∧
          Nonempty (a ≫ f' ≅
            Stack.algebraicSpaceStackMap.{u, w} B integerBase hZ hX hY (i ≫ g)))
    (hlift : Stack.ValuativeCriterion.DenseTestExistence B integerBase hZ
      (Stack.OpenSubstack.homOfLE B integerBase hZ (curvesSmallOpenSubstack B hZ h hQ)
        (curvesSmallOpenSubstack B hZ h hP)
        (Stack.OpenSubstack.property_le_of_pointSet_subset B integerBase hZ hopen.1))
      ((curvesSmallOpenSubstack B hZ h hP).inclusion ≫
        Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h))) :
    Stack.IsDeligneMumfordStack.{u, w} B integerBase hZ
        (curvesSmallOpenSubstack B hZ h hP).toAlgebraicStack.val.val ∧
      Stack.AlgebraicStacks.IsProper B integerBase hZ
        ((curvesSmallOpenSubstack B hZ h hP).inclusion ≫
          Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) ∧
      IsSmoothOverIntegers B hZ h hP ∧
      ∃ hle : (curvesSmallOpenSubstack B hZ h hQ).property ≤
          (curvesSmallOpenSubstack B hZ h hP).property,
        @Dense _ (Stack.pointTopology B integerBase hZ
            (curvesSmallOpenSubstack B hZ h hP).toAlgebraicStack.val)
          (Set.range (Stack.AlgebraicStacks.pointsMap B integerBase hZ
            (Stack.OpenSubstack.homOfLE B integerBase hZ (curvesSmallOpenSubstack B hZ h hQ)
              (curvesSmallOpenSubstack B hZ h hP) hle))) := by
  have : IsNoetherianRing (ULift.{u} ℤ) := isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have hle := Stack.OpenSubstack.property_le_of_pointSet_subset B integerBase hZ hopen.1
  exact ⟨hDM, Stack.AlgebraicStacks.isProper_inclusion_comp_structureMorphism_of_denseTestExistence
      B integerBase hZ _ _ hle
      (Stack.AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B integerBase
        hZ hcurves.2) hsep hqc hopen.2 hlift hchow, hsmooth, hle,
    Stack.AlgebraicStacks.dense_range_pointsMap_of_pointSet_subset_closure B integerBase hZ
      _ _ hopen.2⟩

end AlgebraicGeometry

end
