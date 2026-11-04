module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafDuality
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDualizingComplexAffinePerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedRightAdjointHomologyReading
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackTopDegree

/-!
# The relative dualizing complex of a family of curves over an affine base, on a fibre

Let `f : X → S` be a family of curves with `S` affine, and let `ω^•_{X/S} = a(𝒪_S)`, where `a` is
the right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_S)` (Stacks 0E55). By the discussion after
Stacks 0E5X, `(a(𝒪_S), Tr)` is a relative dualizing complex (Stacks 0E5V (1) and 0E5I). Let
`Spec K → S` be a field-valued point and `V` a scheme presenting the fibre `X_K`. Section 0E6N:
"for any base change of `X` which is a scheme, the relative dualizing complex agrees with the
relative dualizing complex of Duality for Schemes"; in particular the derived pullback of
`ω^•_{X/S}` to `V` has, in every degree `n`, the cohomology sheaf `H^n(ω_V^•)` of the dualizing
complex `ω_V^• = f_V^×(𝒪_{Spec K})` of Algebraic Curves, Lemma 0BS2.

## Main definitions

* `AlgebraicGeometry.CurveFamily.affineDualizingComplex`: `ω^•_{X/S} = a(𝒪_S)` for `S` affine.

## Main results

* `AlgebraicGeometry.CurveFamily.nonempty_homology_derivedPullback_affineDualizingComplex_iso`:
  the restriction to the Zariski site of `V` of `H^n(Lq^* ω^•_{X/S})` is
  `H^n(dualizingComplexOverField (V → Spec K))`.

## Implementation notes

The proof: the base change property of the relative dualizing complex identifies
`Lq^* ω^•_{X/S}` with `a_V(𝒪_{Spec K})`, the right adjoint for the represented morphism
`V → Spec K` (Stacks 0E5X); Stacks 0E6E identifies that with the image of `f_V^×(𝒪_{Spec K})`
under the equivalence of Stacks 071Q, read on cohomology sheaves by
`AlgebraicGeometry.Space.representedRightAdjointHomologyRestrictIso`.

## References

* [Stacks Project, Tag 0E5X](https://stacks.math.columbia.edu/tag/0E5X)
* [Stacks Project, Tag 0E6E](https://stacks.math.columbia.edu/tag/0E6E)
* [Stacks Project, Tag 0E6N](https://stacks.math.columbia.edu/tag/0E6N)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.CurveFamily

-- No global `HasDerivedCategory` instance applies to modules on small étale sites, which are not
-- `SmallCategory`; at low priority the standard model chooses nothing where a global one exists.
attribute [local instance low] HasDerivedCategory.standard

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- The base of a family of curves with affine underlying scheme is an affine algebraic space. -/
theorem isAffineSpace_schemeSpace_base (G : CurveFamily B hZ)
    (hA : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj G.base)) :
    Space.IsAffineSpace B integerBase hZ (schemeSpace G.base).1 :=
  Space.isAffineSpace_yoneda B integerBase hZ _ hA

/-- **The relative dualizing complex `ω^•_{X/S} = a(𝒪_S)` of a family of curves over an affine
base** (the discussion after Stacks 0E5X): the value at `𝒪_S` of the right adjoint `a` of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_S)`. -/
def affineDualizingComplex (G : CurveFamily B hZ)
    (hA : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj G.base)) :
    Space.QuasicoherentDerivedCategory.{u, u} B integerBase hZ G.total.1 G.total.2 :=
  (Space.affineRightAdjoint B.contains_terminal G.toBase G.finitePresentation
    (isAffineSpace_schemeSpace_base G hA)).obj
      (Space.derivedStructureSheaf B integerBase hZ _ (schemeSpace G.base).2)

/-- `(a(𝒪_S), Tr)` is a relative dualizing complex of the family (Stacks 0E5X). -/
def affineRelativeDualizingComplex (G : CurveFamily B hZ)
    (hA : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj G.base)) :
    Space.RelativeDualizingComplex B.contains_terminal G.toBase G.proper G.flat
      G.finitePresentation :=
  Space.RelativeDualizingComplex.ofIsAffine B.contains_terminal G.toBase G.proper G.flat
    G.finitePresentation (isAffineSpace_schemeSpace_base G hA)

/-- A presentation of a fibre over a field-valued point is a cartesian square of algebraic
spaces. -/
theorem isPullback_fieldPointPresentation {G : CurveFamily B hZ}
    {p : Space.FieldValuedPoint B integerBase hZ (schemeSpace G.base).obj}
    {V : BigFppfOver B integerBase hZ} {v : V ⟶ p.siteObject} {q : yoneda.obj V ⟶ G.total.obj}
    (h : IsPullback q (yoneda.map v) G.toBase.hom (yonedaEquiv.symm p.value)) :
    IsPullback (ObjectProperty.homMk q : schemeSpace V ⟶ G.total) (schemeSpaceMap v) G.toBase
      (ObjectProperty.homMk (yonedaEquiv.symm p.value) :
        schemeSpace p.siteObject ⟶ schemeSpace G.base) :=
  Space.isPullback_homMk B integerBase hZ G.total.property
    (isAlgebraicSpace_yoneda B integerBase hZ _) (isAlgebraicSpace_yoneda B integerBase hZ _)
    (isAlgebraicSpace_yoneda B integerBase hZ _) h

/-- The point `Spec K` of a field-valued point is an affine algebraic space. -/
theorem isAffineSpace_fieldPoint {G : CurveFamily B hZ}
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace G.base).obj) :
    Space.IsAffineSpace B integerBase hZ (schemeSpace p.siteObject).1 :=
  Space.isAffineSpace_yoneda B integerBase hZ _ (inferInstanceAs (IsAffine (Spec _)))

/-- **The relative dualizing complex on a fibre** (Section 0E6N). Let `f : X → S` be a family of
curves over an affine `S`, `Spec K → S` a field-valued point and `V` a scheme presenting the fibre
`X_K` through `q : V → X`. For every `n`, the restriction to the Zariski site of `V` of
`H^n(Lq^* ω^•_{X/S})` is the cohomology sheaf `H^n(ω_V^•)` of the dualizing complex
`ω_V^• = f_V^×(𝒪_{Spec K})` of Algebraic Curves, Lemma 0BS2. -/
theorem nonempty_homology_derivedPullback_affineDualizingComplex_iso (G : CurveFamily B hZ)
    (hA : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj G.base))
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace G.base).obj)
    (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject) (q : yoneda.obj V ⟶ G.total.obj)
    [IsProper ((BigFppfOver.toScheme B integerBase hZ).map v)]
    (h : IsPullback q (yoneda.map v) G.toBase.hom (yonedaEquiv.symm p.value)) (n : ℤ) :
    Nonempty (Space.restrictToChartScheme B integerBase hZ (yoneda.obj V)
        (isAlgebraicSpace_yoneda B integerBase hZ V)
        ((DerivedCategory.homologyFunctor
          (Space.Modules.{u, u} B integerBase hZ (schemeSpace V).1 (schemeSpace V).2) n).obj
          ((Space.smallEtaleDerivedModulePullback B integerBase hZ
            (ObjectProperty.homMk q : schemeSpace V ⟶ G.total)).obj
              (affineDualizingComplex G hA).obj))
        (Space.idEtaleChart B integerBase hZ V) ≅
      (DerivedCategory.homologyFunctor ((BigFppfOver.toScheme B integerBase hZ).obj V).Modules
        n).obj (Stacks.Duality.dualizingComplexOverField
          ((BigFppfOver.toScheme B integerBase hZ).map v)).obj) := by
  have sq := isPullback_fieldPointPresentation h
  have hP := isAffineSpace_fieldPoint (G := G) p
  have hZ' := B.contains_terminal
  obtain ⟨e, -⟩ := (affineRelativeDualizingComplex G hA).isAffineBaseChangePair
    (schemeSpaceMap v) _ _ sq hP
  have hfqc := Space.isQuasiCompact_of_isPullback_of_isFinitePresentation sq G.finitePresentation
  have hfqs := Space.isQuasiSeparated_of_isPullback_of_isFinitePresentation sq G.finitePresentation
  have hXqc := Space.isQuasiCompactSpace_of_isQuasiCompact_hom_of_isAffineSpace B integerBase hZ
    (schemeSpaceMap v) hfqc hP
  have hXqs := Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated_hom_of_isAffineSpace B
    integerBase hZ hZ' (schemeSpaceMap v) hfqs hP
  have hYqs := Space.isAbsolutelyQuasiSeparated_of_isAffineSpace B integerBase hZ hZ' hP
  have e₀ := Space.representedRightAdjointHomologyRestrictIso hZ' v hXqc hXqs
    hP.isQuasiCompactSpace hYqs
    (Stacks.Duality.DerivedPushforward.derivedStructureSheaf
      ((BigFppfOver.toScheme B integerBase hZ).obj p.siteObject)) n
  refine ⟨(Space.restrictToChartSchemeFunctor B integerBase hZ (yoneda.obj V)
      (isAlgebraicSpace_yoneda B integerBase hZ V) (Space.idEtaleChart B integerBase hZ V)).mapIso
      ((DerivedCategory.homologyFunctor
        (Space.Modules.{u, u} B integerBase hZ (schemeSpace V).1 (schemeSpace V).2) n).mapIso
        (e ≪≫ (ObjectProperty.ι _).mapIso
        ((Space.affineBaseChangeRightAdjoint hZ' sq G.finitePresentation hP).mapIso
          (Space.representedEquivalenceStructureSheafIso B integerBase hZ p.siteObject).symm))) ≪≫
    e₀⟩

/-- **The sheaf `H^{-1}(ω^•_{X/S})` on a fibre** (Section 0E6N, Definition 0E6Q). If the relative
dualizing complex `ω^•_{X/S} = a(𝒪_S)` of a family of curves over an affine base has no
cohomology above degree `-1`, then the pullback of `ω_{X/S} = H^{-1}(ω^•_{X/S})` to a scheme `V`
presenting the fibre over a field-valued point `Spec K → S` is the dualizing sheaf
`ω_V = H^{-1}(f_V^×(𝒪_{Spec K}))` of Algebraic Curves, Lemma 0BS2: the derived pullback computes
the underived one in the top degree, and the derived pullback of `ω^•_{X/S}` is read on `V` by
`AlgebraicGeometry.CurveFamily.nonempty_homology_derivedPullback_affineDualizingComplex_iso`. -/
theorem nonempty_baseChangeModule_homology_affineDualizingComplex_iso (G : CurveFamily B hZ)
    (hA : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj G.base))
    (hle : (affineDualizingComplex G hA).obj.IsLE (-1))
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace G.base).obj)
    (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject) (q : yoneda.obj V ⟶ G.total.obj)
    [IsProper ((BigFppfOver.toScheme B integerBase hZ).map v)]
    (h : IsPullback q (yoneda.map v) G.toBase.hom (yonedaEquiv.symm p.value)) :
    Nonempty (Space.baseChangeModule B integerBase hZ
      ((DerivedCategory.homologyFunctor
        (Space.Modules.{u, u} B integerBase hZ G.total.1 G.total.2) (-1)).obj
          (affineDualizingComplex G hA).obj) V q ≅
      Stacks.Duality.dualizingSheafOverField ((BigFppfOver.toScheme B integerBase hZ).map v)) := by
  obtain ⟨e⟩ := Space.nonempty_homology_smallEtaleDerivedModulePullback_iso_of_isLE
    (ObjectProperty.homMk q : schemeSpace V ⟶ G.total) _ (-1) hle
  obtain ⟨e'⟩ := nonempty_homology_derivedPullback_affineDualizingComplex_iso G hA p V v q h (-1)
  exact ⟨(Space.restrictToChartSchemeFunctor B integerBase hZ (yoneda.obj V)
    (isAlgebraicSpace_yoneda B integerBase hZ V) (Space.idEtaleChart B integerBase hZ V)).mapIso
      e.symm ≪≫ e'⟩

end AlgebraicGeometry.CurveFamily

end
