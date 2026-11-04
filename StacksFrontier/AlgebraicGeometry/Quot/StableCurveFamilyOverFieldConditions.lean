module

public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.DualizingAmple
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.DualizingSheafDegree
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.TerminalBaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.NodalSpecialFibre
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyCriterion
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.AmpleNoRationalBridge
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.TricanonicalVeryAmple
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkEquivalence.FieldFiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.OverAField
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.UniversalDirectImage
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyAutomorphismGroupScheme
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesStable
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesOfGenusOverField
public import StacksFrontier.Deformation.Examples.Geometric.CurvesDeformationComparison
public import StacksFrontier.Topology.Dimension.Krull

/-!
# A stable family over a field is a stable curve (the implication (a) ⇒ (b) of 0E76 (2))

Let `X` be a proper scheme of dimension at most one over a field `k`, and suppose that the family
of curves `X → Spec k` (`AlgebraicGeometry.curveFamilyOfScheme`) is stable (Stacks 0E75). Then
`X` has at-worst-nodal singularities, `dim(X) = 1`, `k = H⁰(X, 𝒪_X)`, the genus of `X` is at
least two and `X` has no rational tails and no rational bridges: condition (b) of part (2) of
Stacks 0E76. In particular, the point `Spec k → Curves` classifying `X` lies in the open substack
of the small model of `Curves` cut out by the stable families only if `X` satisfies (b).

## Main results

* `AlgebraicGeometry.stableConditions_of_isStableCurveFamily_curveFamilyOfScheme`: the
  implication.
* `AlgebraicGeometry.curvesSmall.stableConditions_of_curvesSmallOpenSubstack_curveFieldPoint`:
  the same at the point `Spec k → Curves` and the open substack of stable families.

## References

* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0E75](https://stacks.math.columbia.edu/tag/0E75)
* [Stacks Project, Tag 0C59](https://stacks.math.columbia.edu/tag/0C59)
* [Stacks Project, Tag 0E32](https://stacks.math.columbia.edu/tag/0E32)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-! ### The family of a stable curve over a field -/

/-- A proper scheme over a field `k` contained in the site is itself contained in the site. -/
private theorem contains_left_of_isProper {k : Type u} [Field k]
    (hk : B.Contains (Spec (.of k))) (X : Over (Spec (.of k))) [IsProper X.hom] :
    B.Contains X.left :=
  Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hk

/-- The field-valued point of the base of the family of curves of `X` given by `Spec k`. -/
private abbrev fieldPointOfFamily {k : Type u} [Field k] (hk : B.Contains (Spec (.of k)))
    (X : Over (Spec (.of k))) [IsProper X.hom] (hdim : topologicalKrullDim X.left ≤ 1) :
    Space.FieldValuedPoint B integerBase hZ
      (schemeSpace (curveFamilyOfScheme X B hZ hk hdim).base).obj :=
  ⟨k, hk, specULiftZIsTerminal.from _, 𝟙 _⟩

/-- `k = H⁰(X, 𝒪_X)` when the family of curves of `X` has `f_*𝒪_X = 𝒪_S` universally. -/
private theorem isIso_globalSections_of_hasUniversallyBijectiveGlobalFunctions {k : Type u}
    [Field k] (hk : B.Contains (Spec (.of k))) (X : Over (Spec (.of k))) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1)
    (hF : HasUniversallyBijectiveGlobalFunctions B hZ (curveFamilyOfScheme X B hZ hk hdim)) :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) := by
  have hX := contains_left_of_isProper hk X
  let p₀ := fieldPointOfFamily (hZ := hZ) hk X hdim
  have h1 : schemeSpaceMap (𝟙 (integerSiteObject B hZ hk)) = 𝟙 _ :=
    (schemeSpaceFunctor B integerBase hZ).map_id _
  have hsq : IsPullback (𝟙 _) (schemeSpaceMap (integerSiteMap B hZ hX hk X.hom))
      (curveFamilyOfScheme X B hZ hk hdim).toBase (schemeSpaceMap p₀.value) := by
    show IsPullback (𝟙 _) (schemeSpaceMap (integerSiteMap B hZ hX hk X.hom))
      (schemeSpaceMap (integerSiteMap B hZ hX hk X.hom))
      (schemeSpaceMap (𝟙 (integerSiteObject B hZ hk)))
    rw [h1]
    exact IsPullback.id_horiz _
  exact CurveFamily.isIso_appTop_of_isPullback_fieldValuedPoint (p := p₀)
    (V := integerSiteObject B hZ hX) (v := integerSiteMap B hZ hX hk X.hom) (q := 𝟙 _) hF hsq

/-- If the family of curves of `X` over `k` is prestable, then `X` is at-worst-nodal, of dimension
one, with `k = H⁰(X, 𝒪_X)`. -/
private theorem prestableConditions_of_isPrestableCurveFamily_curveFamilyOfScheme {k : Type u}
    [Field k] (hk : B.Contains (Spec (.of k))) (X : Over (Spec (.of k))) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1)
    (hpre : IsPrestableCurveFamily B hZ (curveFamilyOfScheme X B hZ hk hdim)) :
    (letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩;
      Stacks.Curves.HasAtWorstNodalSingularities k X.left) ∧
      topologicalKrullDim X.left = 1 ∧ IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) := by
  have hX := contains_left_of_isProper hk X
  have hnod : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ
      (curveFamilyOfScheme X B hZ hk hdim).toBase.hom ↔
        IsAtWorstNodalOfRelativeDimensionOne X.hom :=
    Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
      isAtWorstNodalOfRelativeDimensionOne_isEtaleLocalOnSourceAndTarget
      (integerSiteMap B hZ hX hk X.hom)
  have : LocallyOfFinitePresentation X.hom := inferInstance
  obtain ⟨hn, hF⟩ := hpre
  have hH0 := isIso_globalSections_of_hasUniversallyBijectiveGlobalFunctions hk X hdim hF
  have : Nonempty X.left := by
    by_contra hempty
    rw [not_nonempty_iff] at hempty
    have : Subsingleton Γ(X.left, ⊤) := inferInstance
    have hinj := (ConcreteCategory.bijective_of_isIso
      ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop)).1
    exact zero_ne_one (hinj (Subsingleton.elim _ _) : (0 : k) = 1)
  obtain ⟨-, hdim1, hnodal⟩ :=
    (isAtWorstNodalOfRelativeDimensionOne_iff_of_field k X.hom).1 (hnod.1 hn)
  exact ⟨hnodal, hdim1, hH0⟩

/-- A stable family over a field is a stable curve: let `X` be a proper scheme of dimension at
most one over a field `k` whose family of curves `X → Spec k` is stable (Stacks 0E75); then `X`
has at-worst-nodal singularities, `dim(X) = 1`, `k = H⁰(X, 𝒪_X)`, genus at least two, and no
rational tails or bridges: the implication (a) ⇒ (b) of part (2) of Stacks 0E76. -/
theorem stableConditions_of_isStableCurveFamily_curveFamilyOfScheme {k : Type u} [Field k]
    (hk : B.Contains (Spec (.of k))) (X : Over (Spec (.of k))) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1)
    (hst : IsStableCurveFamily B hZ (curveFamilyOfScheme X B hZ hk hdim)) :
    (letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩;
      Stacks.Curves.HasAtWorstNodalSingularities k X.left) ∧
      topologicalKrullDim X.left = 1 ∧
      IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) ∧
      HasGenusTwoNoRationalTailNoRationalBridge k X.hom := by
  have hX := contains_left_of_isProper hk X
  have hid : Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (Spec (.of k)) := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  obtain ⟨hpre, hst⟩ := hst
  obtain ⟨hnodal, hdim1, hH0⟩ :=
    prestableConditions_of_isPrestableCurveFamily_curveFamilyOfScheme hk X hdim hpre
  have := hH0
  have hequi : TopologicalSpace.Equidimensional X.left :=
    equidimensional_of_isIso_globalSections_of_dimension_one k X.hom hdim1
  let p₀ := fieldPointOfFamily (hZ := hZ) hk X hdim
  have hp₀ : (BigFppfOver.toScheme B integerBase hZ).map p₀.value =
      Spec.map (CommRingCat.ofHom (algebraMap k k)) := by
    rw [hid]
    exact (BigFppfOver.toScheme B integerBase hZ).map_id _
  obtain ⟨V', v', q', hq', hV'⟩ := hst p₀
  have hval : yonedaEquiv.symm p₀.value = yoneda.map p₀.value :=
    yonedaEquiv.symm_apply_eq.2 (yonedaEquiv_yoneda_map _).symm
  rw [hval] at hq'
  obtain ⟨a', ha'⟩ : ∃ a' : (BigFppfOver.toScheme B integerBase hZ).obj V' ⟶ X.left,
      @IsPullback Scheme.{u} _ _ _ (Spec (.of p₀.carrier)) (Spec (.of k)) a'
        ((BigFppfOver.toScheme B integerBase hZ).map v') X.hom
        ((BigFppfOver.toScheme B integerBase hZ).map p₀.value) :=
    ⟨_, isPullback_toScheme_of_isPullback_yoneda (c := integerSiteMap B hZ hX hk X.hom) hq'⟩
  rw [hp₀] at ha'
  have ha'' : @IsPullback Scheme.{u} _ _ _ (Spec (.of k)) (Spec (.of k)) a'
      ((BigFppfOver.toScheme B integerBase hZ).map v') X.hom (𝟙 (Spec (.of k))) := by
    rwa [hid] at ha'
  have : IsIso a' := ha''.isIso_fst_of_isIso
  have hinv : @IsPullback Scheme.{u} _ _ _ (Spec (.of k)) (Spec (.of k)) (inv a') X.hom
      ((BigFppfOver.toScheme B integerBase hZ).map v')
      (Spec.map (CommRingCat.ofHom (algebraMap k k))) := by
    rw [hid]
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [Category.comp_id, IsIso.inv_comp_eq, ha''.w, Category.comp_id]
  have : IsProper ((BigFppfOver.toScheme B integerBase hZ).map v') :=
    isProper_of_isPullback_specMapAlgebraMap k k a' _ X.hom ha'
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫
      ((BigFppfOver.toScheme B integerBase hZ).map v').appTop) :=
    isIso_globalSections_baseChange k k a' _ X.hom ha'
  have hXst := HasGenusTwoNoRationalTailNoRationalBridge.of_isPullback k k hinv
    ((topologicalKrullDim_baseChange k k a' _ X.hom ha').trans hdim1)
    (hasAtWorstNodalSingularities_of_isPullback k k ha' hequi hdim1 hnodal) hV'
  exact ⟨hnodal, hdim1, hH0, hXst⟩

end AlgebraicGeometry

namespace AlgebraicGeometry.curvesSmall

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- The points of the open substack of stable families are stable curves: let `Curves` be
algebraic (`h`), let the stable families satisfy condition (o) of Stacks 0E0E (`hst`), and let
`X` be a proper scheme of dimension at most one over a field `k`. If the point `Spec k → Curves`
classifying `X` lies in the open substack of stable families, then `X` satisfies condition (b)
of part (2) of Stacks 0E76. -/
theorem stableConditions_of_curvesSmallOpenSubstack_curveFieldPoint.{w}
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)
    (hst : IsOpenCurvesLocus B hZ (IsStableCurveFamily B hZ))
    {k : Type u} [Field k] (X : Over (Spec (.of k))) [IsProper X.hom]
    (hk : B.Contains (Spec (.of k))) (hdim : topologicalKrullDim X.left ≤ 1)
    (hX : (curvesSmallOpenSubstack B hZ h hst).property (curveFieldPoint X hk hdim h).obj) :
    (letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩;
      Stacks.Curves.HasAtWorstNodalSingularities k X.left) ∧
      topologicalKrullDim X.left = 1 ∧
      IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) ∧
      HasGenusTwoNoRationalTailNoRationalBridge k X.hom :=
  stableConditions_of_isStableCurveFamily_curveFamilyOfScheme hk X hdim
    ((curvesSmallOpenSubstack_property_iff B hZ h hst (curveFamilyOfScheme X B hZ hk hdim)).1 hX)

end AlgebraicGeometry.curvesSmall

end
