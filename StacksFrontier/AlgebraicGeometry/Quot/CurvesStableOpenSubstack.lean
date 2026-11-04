module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableLocusOpenUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStable
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesOfGenusOverField
public import StacksFrontier.AlgebraicGeometry.Quot.StableLocusOpenFibreAmple

/-!
# The open substack of stable curves (Stacks 0E76)

Stacks 0E76 produces an open substack `Curves^{stable} ⊂ Curves` such that

1. the classifying morphism of a family of curves `X → S` factors through it exactly when
   `X → S` is a stable family of curves (Stacks 0E75), and
2. for a scheme `X` proper over a field `k` with `dim(X) ≤ 1`, the following are equivalent:
   (a) the classifying morphism `Spec(k) → Curves` factors through it; (b) the singularities of
   `X` are at-worst-nodal, `dim(X) = 1`, `k = H⁰(X, 𝒪_X)`, the genus of `X` is at least two and
   `X` has no rational tails or bridges; (c) the singularities of `X` are at-worst-nodal,
   `dim(X) = 1`, `k = H⁰(X, 𝒪_X)` and `ω_X` is ample.

`Curves^{stable}` is the strictly full subcategory of stable families,
`AlgebraicGeometry.curvesSubstack` at `AlgebraicGeometry.IsStableCurveFamily`; stability passes
along morphisms of families (`AlgebraicGeometry.CurveFamily.isStableCurveFamily_of_hom`).

## Main results

* `AlgebraicGeometry.isStableCurveFamily_curveFamilyOfScheme_iff`: the family of a proper scheme
  of dimension at most one over a field is stable exactly when condition (b) of part (2) holds.
* `AlgebraicGeometry.curvesStable_isOpenSubstack_and_factors_iff`: `Curves^{stable}` is an open
  substack of `Curves`, and parts (1) and (2) hold.

## Implementation notes

The openness of the stable locus, together with its compatibility with base change (condition (o)
of Section 0E0E), is `AlgebraicGeometry.C1590Private.isOpenCurvesLocus_isStableCurveFamily`. Part
(2) is part (1) at the family `AlgebraicGeometry.curveFamilyOfScheme` of `X`, whose fibres are the
base changes of `X` along field extensions `K/k`; the equivalence of (b) and (c) is
`AlgebraicGeometry.hasGenusTwoNoRationalTailNoRationalBridge_iff_isAmple_dualizingSheafOverField`.

As in Stacks 0E78, `k = H⁰(X, 𝒪_X)` is the bijectivity of `k ≅ Γ(Spec k, 𝒪) ⟶ Γ(X, 𝒪_X)`, read
as an isomorphism of rings; in condition (c) the invertibility of `ω_X`, which the ampleness
predicate takes as an instance, is supplied by
`AlgebraicGeometry.isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities` from the
other three conditions. The source's `ω_{X_s}` in (c) is `ω_X`.

## References

* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0E75](https://stacks.math.columbia.edu/tag/0E75)
* [Stacks Project, Tag 0E74](https://stacks.math.columbia.edu/tag/0E74)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 0E3L](https://stacks.math.columbia.edu/tag/0E3L)
* [Stacks Project, Tag 0E3Q](https://stacks.math.columbia.edu/tag/0E3Q)
* [Stacks Project, Tag 0D2P](https://stacks.math.columbia.edu/tag/0D2P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- The family of a proper scheme `X` of dimension at most one over a field `k` is stable exactly
when `X` is at-worst-nodal, of dimension one, with `k = H⁰(X, 𝒪_X)`, of genus at least two, and
without rational tails and rational bridges: condition (b) of part (2) of Stacks 0E76. -/
theorem isStableCurveFamily_curveFamilyOfScheme_iff {k : Type u} [Field k]
    (hk : B.Contains (Spec (.of k))) (X : Over (Spec (.of k))) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    IsStableCurveFamily B hZ (curveFamilyOfScheme X B hZ hk hdim) ↔
      letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
      haveI : IsProper (X.left ↘ Spec (.of k)) := inferInstanceAs (IsProper X.hom)
      Stacks.Curves.HasAtWorstNodalSingularities k X.left ∧ topologicalKrullDim X.left = 1 ∧
        IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) ∧ 2 ≤ genus X.hom ∧
        (∀ C : X.left.IdealSheafData, ¬ IsRationalTail k X.left C) ∧
        ∀ C : X.left.IdealSheafData, ¬ IsRationalBridge k X.left C := by
  have hX : B.Contains X.left :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hk
  have hid : Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (Spec (.of k)) := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have hfibsq : ∀ (p : Space.FieldValuedPoint B integerBase hZ
      (schemeSpace (curveFamilyOfScheme X B hZ hk hdim).base).obj)
      (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject)
      (q : yoneda.obj V ⟶ (curveFamilyOfScheme X B hZ hk hdim).total.obj),
      IsPullback q (yoneda.map v) (curveFamilyOfScheme X B hZ hk hdim).toBase.hom
        (yonedaEquiv.symm p.value) →
      ∃ a : (BigFppfOver.toScheme B integerBase hZ).obj V ⟶ X.left,
        @IsPullback Scheme.{u} _ _ _ (Spec (.of p.carrier)) (Spec (.of k)) a
          ((BigFppfOver.toScheme B integerBase hZ).map v) X.hom
          ((BigFppfOver.toScheme B integerBase hZ).map p.value) := by
    intro p V v q hq
    have hval : yonedaEquiv.symm p.value = yoneda.map p.value :=
      yonedaEquiv.symm_apply_eq.2 (yonedaEquiv_yoneda_map _).symm
    rw [hval] at hq
    exact ⟨_, isPullback_toScheme_of_isPullback_yoneda (c := integerSiteMap B hZ hX hk X.hom) hq⟩
  constructor
  · rintro ⟨hpre, hst⟩
    obtain ⟨hnodal, hdim1, hH0⟩ :=
      (isPrestableCurveFamily_curveFamilyOfScheme_iff hk X hdim).1 hpre
    have hequi : TopologicalSpace.Equidimensional X.left :=
      equidimensional_of_isIso_globalSections_of_dimension_one k X.hom hdim1
    let p₀ : Space.FieldValuedPoint B integerBase hZ
        (schemeSpace (curveFamilyOfScheme X B hZ hk hdim).base).obj :=
      ⟨k, hk, specULiftZIsTerminal.from _, 𝟙 _⟩
    have hp₀ : (BigFppfOver.toScheme B integerBase hZ).map p₀.value =
        Spec.map (CommRingCat.ofHom (algebraMap k k)) := by
      rw [hid]
      exact (BigFppfOver.toScheme B integerBase hZ).map_id _
    obtain ⟨V', v', q', hq', hV'⟩ := hst p₀
    obtain ⟨a', ha'⟩ := hfibsq p₀ V' v' q' hq'
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
    obtain ⟨hg, htail, _, hbridge⟩ := hXst
    exact ⟨hnodal, hdim1, hH0, hg, htail, hbridge⟩
  · rintro ⟨hnodal, hdim1, hH0, hg, htail, hbridge⟩
    have hpre : IsPrestableCurveFamily B hZ (curveFamilyOfScheme X B hZ hk hdim) :=
      (isPrestableCurveFamily_curveFamilyOfScheme_iff hk X hdim).2 ⟨hnodal, hdim1, hH0⟩
    have hXst : HasGenusTwoNoRationalTailNoRationalBridge k X.hom :=
      ⟨hg, htail, inferInstanceAs (IsProper X.hom), hbridge⟩
    refine ⟨hpre, fun p => ?_⟩
    obtain ⟨V, v, q, hsq⟩ := CurveFamily.exists_isPullback_fieldValuedPoint B hZ
      (curveFamilyOfScheme X B hZ hk hdim) p
    have hsq' : IsPullback q.hom (yoneda.map v)
        (curveFamilyOfScheme X B hZ hk hdim).toBase.hom (yonedaEquiv.symm p.value) :=
      AlgebraicSpaces.isPullback_hom B integerBase hZ hsq
    obtain ⟨a, ha⟩ := hfibsq p V v q.hom hsq'
    set φ := (BigFppfOver.toScheme B integerBase hZ).map p.value
    let : Algebra k p.carrier := (Spec.preimage φ).hom.toAlgebra
    have hφ : Spec.map (CommRingCat.ofHom (algebraMap k p.carrier)) = φ := Spec.map_preimage φ
    rw [← hφ] at ha
    exact ⟨V, v, q.hom, hsq',
      HasGenusTwoNoRationalTailNoRationalBridge.of_isPullback k p.carrier ha hdim1 hnodal hXst⟩

/-- The genus and rational tail/bridge conditions are equivalent to ampleness of `ω_X`, with the
global sections hypothesis given as an isomorphism `k ≅ Γ(X, 𝒪_X)`. -/
private theorem hasGenusTwoNoRationalTailNoRationalBridge_iff_isAmple_of_isIso
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hH0 : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop))
    (hdim : topologicalKrullDim X = 1)
    (hnodal : letI : X.Over (Spec (.of k)) := ⟨f⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X) :
    HasGenusTwoNoRationalTailNoRationalBridge k f ↔
      ∃ _ : SheafOfModules.IsInvertible X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property
          (Stacks.Duality.dualizingSheafOverField f),
        Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField f) := by
  have : IsIso f.appTop := IsIso.of_isIso_comp_left (Scheme.ΓSpecIso _).inv _
  exact hasGenusTwoNoRationalTailNoRationalBridge_iff_isAmple_dualizingSheafOverField k f hdim
    (ConcreteCategory.bijective_of_isIso f.appTop) hnodal

variable (B hZ)

/-- There is an open substack `Curves^{stable} ⊂ Curves` — the strictly full
subcategory of stable families of curves (Stacks 0E75), invariant under isomorphism, whose
inclusion into `Curves` is representable by algebraic spaces and an open immersion — such that

1. given a family of curves `f : X → U`, the classifying morphism `U → Curves` factors through
   `Curves^{stable}` if and only if `X → U` is a stable family of curves: a scheme-valued point
   `y` of `Curves` over `U` lifts to `Curves^{stable}` exactly when the family `y(U)` it
   classifies is stable;
2. given a scheme `X` proper over a field `k` with `dim(X) ≤ 1`, the following are equivalent:
   * (a) the classifying morphism `Spec(k) → Curves` of `X` factors through `Curves^{stable}`
     (every scheme-valued point `y` with `y(U) ≅ X` lifts);
   * (b) the singularities of `X` are at-worst-nodal, `dim(X) = 1`, `k = H⁰(X, 𝒪_X)`, the genus
     of `X` is at least two, and `X` has no rational tails and no rational bridges;
   * (c) the singularities of `X` are at-worst-nodal, `dim(X) = 1`, `k = H⁰(X, 𝒪_X)`, and the
     dualizing sheaf `ω_X` is ample. -/
@[stacks 0E76]
theorem curvesStable_isOpenSubstack_and_factors_iff :
    (ObjectProperty.IsClosedUnderIsomorphisms (IsStableCurveFamily B hZ) ∧
      Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
        (curvesSubstackInclusion B hZ (IsStableCurveFamily B hZ)
          CurveFamily.isStableCurveFamily_of_hom).hom ∧
      Stack.IsOpenImmersion B integerBase hZ
        (curvesSubstackInclusion B hZ (IsStableCurveFamily B hZ)
          CurveFamily.isStableCurveFamily_of_hom)) ∧
    (∀ (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsStableCurveFamily B hZ),
          z ⋙ ObjectProperty.ι (IsStableCurveFamily B hZ) = y) ↔
        IsStableCurveFamily B hZ (y.obj (Over.mk (𝟙 U.left))))) ∧
    ∀ {k : Type u} [Field k] (hk : B.Contains (Spec (.of k)))
      (X : Over (Spec (.of k))) [IsProper X.hom] (hdim : topologicalKrullDim X.left ≤ 1),
      (∀ (U : BigFppfOver B integerBase hZ)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
        y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
        (y.obj (Over.mk (𝟙 U.left)) ≅ curveFamilyOfScheme X B hZ hk hdim) →
        ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
            ObjectProperty.FullSubcategory (IsStableCurveFamily B hZ),
            z ⋙ ObjectProperty.ι (IsStableCurveFamily B hZ) = y) ↔
          letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
          haveI : IsProper (X.left ↘ Spec (.of k)) := inferInstanceAs (IsProper X.hom)
          Stacks.Curves.HasAtWorstNodalSingularities k X.left ∧ topologicalKrullDim X.left = 1 ∧
            IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) ∧ 2 ≤ genus X.hom ∧
            (∀ C : X.left.IdealSheafData, ¬ IsRationalTail k X.left C) ∧
            ∀ C : X.left.IdealSheafData, ¬ IsRationalBridge k X.left C)) ∧
      ((letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
        haveI : IsProper (X.left ↘ Spec (.of k)) := inferInstanceAs (IsProper X.hom)
        Stacks.Curves.HasAtWorstNodalSingularities k X.left ∧ topologicalKrullDim X.left = 1 ∧
          IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) ∧ 2 ≤ genus X.hom ∧
          (∀ C : X.left.IdealSheafData, ¬ IsRationalTail k X.left C) ∧
          ∀ C : X.left.IdealSheafData, ¬ IsRationalBridge k X.left C) ↔
        letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
        haveI : IsProper (X.left ↘ Spec (.of k)) := inferInstanceAs (IsProper X.hom)
        ∃ (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X.left)
          (hdim1 : topologicalKrullDim X.left = 1)
          (hH0 : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X.left ↘ Spec (.of k)).appTop)),
            haveI := hH0
            haveI := connectedSpace_of_isIso_globalSections k (X.left ↘ Spec (.of k))
            letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X.left
              hdim1 hnodal
            Scheme.Modules.IsAmple X.left
              (Stacks.Duality.dualizingSheafOverField (X.left ↘ Spec (.of k)))) := by
  have hP := C1590Private.isOpenCurvesLocus_isStableCurveFamily B hZ
  refine ⟨isOpenImmersion_curvesSubstackInclusion hP,
    fun U y hy => factors_curvesSubstack_iff hP U y hy,
    @fun k _ hk X _ hdim => ⟨fun U y hy e => ?_, ?_⟩⟩
  · exact (factors_curvesSubstack_iff_of_iso hP U y hy _ e).trans
      (isStableCurveFamily_curveFamilyOfScheme_iff hk X hdim)
  · let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
    have : IsProper (X.left ↘ Spec (.of k)) := inferInstanceAs (IsProper X.hom)
    constructor
    · rintro ⟨hnodal, hdim1, hH0, hg, htail, hbridge⟩
      obtain ⟨_, hω⟩ :=
        (hasGenusTwoNoRationalTailNoRationalBridge_iff_isAmple_of_isIso
          k X.hom hH0 hdim1 hnodal).1
          ⟨hg, htail, inferInstanceAs (IsProper X.hom), hbridge⟩
      exact ⟨hnodal, hdim1, hH0, hω⟩
    · rintro ⟨hnodal, hdim1, hH0, hω⟩
      have := connectedSpace_of_isIso_globalSections k (X.left ↘ Spec (.of k))
      obtain ⟨hg, htail, _, hbridge⟩ :=
        (hasGenusTwoNoRationalTailNoRationalBridge_iff_isAmple_of_isIso
          k X.hom hH0 hdim1 hnodal).2
          ⟨isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X.left hdim1
            hnodal, hω⟩
      exact ⟨hnodal, hdim1, hH0, hg, htail, hbridge⟩

end AlgebraicGeometry

end
