module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFibreGenusRank
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesOfGenusOverField

/-!
# The decomposition of `𝓜̄` by the genus (Stacks 0E78)

Stacks 0E78 decomposes the moduli stack of stable curves `𝓜̄ = Curves^{stable}`
(`AlgebraicGeometry.moduliStableCurves`) into the open and closed substacks `𝓜̄_g`, `g ≥ 2`
(`AlgebraicGeometry.moduliStableCurvesOfGenus`), and characterizes `𝓜̄_g`

1. by its families: the classifying morphism `S → Curves` of a family of curves `f : X → S`
   factors through `𝓜̄_g` exactly when `X → S` is stable and `R¹f_*𝒪_X` is a locally free
   `𝒪_S`-module of rank `g`;
2. by its points: the classifying morphism `Spec(k) → Curves` of a proper scheme `X` of dimension
   at most one over a field `k` factors through `𝓜̄_g` exactly when `X` is at-worst-nodal of
   dimension one with `k = H⁰(X, 𝒪_X)`, of genus `g`, without rational tails or bridges, exactly
   when moreover the last condition is replaced by the ampleness of `ω_X`.

## Main results

* `AlgebraicGeometry.isStableCurveFamilyOfFibreGenus_iff_range_subset_fibreGenusLocus`: over the
  base of a stable family `G`, a family mapping to `G` lies in `𝓜̄_g` exactly when its base lands
  in the locus of points with fibres of genus `g`.
* `AlgebraicGeometry.factors_moduliStableCurvesOfGenus_iff_isStableCurveFamily_and_hasGenus`:
  part (1).
* `AlgebraicGeometry.moduliStableCurves_decomposition_moduliStableCurvesOfGenus`: the whole of
  Stacks 0E78.

## Implementation notes

The decomposition is read on the scheme-valued points of `𝓜̄`, as in
`AlgebraicGeometry.IsOpenCurvesLocus.openClosedDecomposition_of_baseLoci`: a scheme-valued point
of `𝓜̄` over `S` is a stable family `G` over `S`, and the objects of `𝓜̄` over it are the families
`F` with a morphism `F ⟶ G` (a cartesian square). Over `S` the loci
`AlgebraicGeometry.CurveFamily.fibreGenusLocus` of the points with fibres of genus `g`, `g ≥ 2`,
are open and closed, pairwise disjoint and cover `S`, and `F` lies in `𝓜̄_g` exactly when its base
lands in the locus of `g`. So `𝓜̄_g ×_{𝓜̄} S` is the open and closed subscheme of `S` with that
locus of points, and `𝓜̄ = ∐_{g ≥ 2} 𝓜̄_g`. The genus loci are clopen and compatible with base
change because `R¹f_*𝒪_X` of a family with `k = H⁰(X_k, 𝒪_{X_k})` on the fibres is finite locally
free, commutes with base change, and has rank the genus of the fibre
(`AlgebraicGeometry.CurveFamily.isClopen_fibreGenusLocus_and_pairwise_disjoint_and_iUnion_eq_univ`,
`AlgebraicGeometry.CurveFamily.preimage_fibreGenusLocus`); the genus of a fibre of a stable family
is at least two by definition (Stacks 0E75), so the loci of `g < 2` are empty.

## References

* [Stacks Project, Tag 0E78](https://stacks.math.columbia.edu/tag/0E78)
* [Stacks Project, Tag 0E77](https://stacks.math.columbia.edu/tag/0E77)
* [Stacks Project, Tag 0E75](https://stacks.math.columbia.edu/tag/0E75)
* [Stacks Project, Tag 0E6V](https://stacks.math.columbia.edu/tag/0E6V)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **The genus loci of a stable family.** Over the base of a stable family of curves `G`, a
family `F` mapping to `G` is stable with every fibre of genus `g` exactly when its base lands in
the locus of points of the base of `G` whose fibre has genus `g`. -/
theorem isStableCurveFamilyOfFibreGenus_iff_range_subset_fibreGenusLocus {G : CurveFamily B hZ}
    (hG : IsStableCurveFamily B hZ G) (g : ℕ) {F : CurveFamily B hZ} (a : F ⟶ G) :
    IsStableCurveFamilyOfFibreGenus B hZ g F ↔
      Set.range (Space.pointsMap B integerBase hZ (schemeSpace F.base).obj
        (schemeSpaceMap a.baseMap).hom) ⊆ CurveFamily.fibreGenusLocus B hZ G g := by
  have hF : IsStableCurveFamily B hZ F := CurveFamily.isStableCurveFamily_of_hom a hG
  have hkF := CurveFamily.bijective_algebraMap_fibre_of_hasUniversallyBijectiveGlobalFunctions
    hF.1.2
  rw [IsStableCurveFamilyOfFibreGenus, and_iff_right hF,
    F.hasFieldPointFibreGenus_iff_fibreGenusLocus_eq_univ hkF g,
    ← G.preimage_fibreGenusLocus
      (CurveFamily.bijective_algebraMap_fibre_of_hasUniversallyBijectiveGlobalFunctions hG.1.2)
      a hkF g,
    Set.preimage_eq_univ_iff]

/-- **Stacks 0E78, part (1).** The classifying morphism of a family of curves `f : X → U` factors
through `𝓜̄_g` (`AlgebraicGeometry.moduliStableCurvesOfGenus`) exactly when `X → U` is a stable
family of curves and `R¹f_*𝒪_X` is a locally free `𝒪_U`-module of rank `g`: a scheme-valued point
`y` of `Curves` over `U` lifts to the full subcategory of stable families with every fibre of
genus `g` exactly when the family `y(U)` it classifies is stable of genus `g`. -/
theorem factors_moduliStableCurvesOfGenus_iff_isStableCurveFamily_and_hasGenus (g : ℕ)
    (U : BigFppfOver B integerBase hZ) (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ)
    (_hy : y ⋙ curvesProjectionOver B hZ = Over.map U.hom) :
    (∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
        ObjectProperty.FullSubcategory (IsStableCurveFamilyOfFibreGenus B hZ g),
        z ⋙ ObjectProperty.ι (IsStableCurveFamilyOfFibreGenus B hZ g) = y) ↔
      IsStableCurveFamily B hZ (y.obj (Over.mk (𝟙 U.left))) ∧
        CurveFamily.HasGenus B hZ (y.obj (Over.mk (𝟙 U.left))) g := by
  have key : ∀ X : CurveFamily B hZ, IsStableCurveFamilyOfFibreGenus B hZ g X ↔
      IsStableCurveFamily B hZ X ∧ CurveFamily.HasGenus B hZ X g := fun X =>
    and_congr_right fun hX => X.hasFieldPointFibreGenus_iff_hasGenus_of_bijective_algebraMap_fibre
      (CurveFamily.bijective_algebraMap_fibre_of_hasUniversallyBijectiveGlobalFunctions hX.1.2) g
  rw [← key]
  refine ⟨?_, fun h => ⟨ObjectProperty.lift _ y fun T =>
    CurveFamily.isStableCurveFamilyOfFibreGenus_of_hom B hZ (y.map (Over.homMk T.hom (by simp))) h,
    rfl⟩⟩
  rintro ⟨z, rfl⟩
  exact (z.obj _).property

/-- **The decomposition of `𝓜̄` by the genus.** The moduli stack of stable curves decomposes into
open and closed substacks `𝓜̄ = ∐_{g ≥ 2} 𝓜̄_g` (`AlgebraicGeometry.moduliStableCurves`,
`AlgebraicGeometry.moduliStableCurvesOfGenus`), and:

* **Decomposition.** For every scheme-valued point of `𝓜̄`, that is every stable family of curves
  `G` over a scheme `S`, the loci `fibreGenusLocus G g` of the points of `S` whose fibre has genus
  `g` are open and closed in `S`; for `g ≥ 2` they are pairwise disjoint and cover `S`; and an
  object `F ⟶ G` of `𝓜̄` over `S` lies in `𝓜̄_g` exactly when its base lands in the locus of `g`.
  So `𝓜̄_g ×_{𝓜̄} S` is the open and closed subscheme of `S` on that locus.
* **(1)** Given a family of curves `f : X → U`, its classifying morphism `U → Curves` factors
  through `𝓜̄_g` if and only if `X → U` is a stable family of curves and `R¹f_*𝒪_X` is a locally
  free `𝒪_U`-module of rank `g`.
* **(2)** Given a proper scheme `X` over a field `k` with `dim(X) ≤ 1`, the following are
  equivalent: (a) the classifying morphism `Spec(k) → Curves` factors through `𝓜̄_g`; (b) the
  singularities of `X` are at-worst-nodal, `dim(X) = 1`, `k = H⁰(X, 𝒪_X)`, the genus of `X` is
  `g`, and `X` has no rational tails or bridges; (c) the singularities of `X` are at-worst-nodal,
  `dim(X) = 1`, `k = H⁰(X, 𝒪_X)`, the genus of `X` is `g`, and `ω_X` is ample. -/
@[stacks 0E78 "the decomposition of the moduli stack of stable curves into the open and closed \
substacks of stable curves of genus g >= 2, read on the scheme-valued points of the moduli stack, \
together with parts (1) and (2)", sga "7 I 5.1" "(2), special case"]
theorem moduliStableCurves_decomposition_moduliStableCurvesOfGenus :
    (∀ G : CurveFamily B hZ, IsStableCurveFamily B hZ G →
      (∀ g : ℕ, IsClopen (CurveFamily.fibreGenusLocus B hZ G g)) ∧
        Pairwise (Function.onFun Disjoint
          fun g : {g : ℕ // 2 ≤ g} => CurveFamily.fibreGenusLocus B hZ G g) ∧
        ⋃ g : {g : ℕ // 2 ≤ g}, CurveFamily.fibreGenusLocus B hZ G g = Set.univ ∧
        ∀ (g : ℕ) (F : CurveFamily B hZ) (a : F ⟶ G),
          (IsStableCurveFamilyOfFibreGenus B hZ g F ↔
            Set.range (Space.pointsMap B integerBase hZ (schemeSpace F.base).obj
              (schemeSpaceMap a.baseMap).hom) ⊆ CurveFamily.fibreGenusLocus B hZ G g)) ∧
    (∀ (g : ℕ) (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsStableCurveFamilyOfFibreGenus B hZ g),
          z ⋙ ObjectProperty.ι (IsStableCurveFamilyOfFibreGenus B hZ g) = y) ↔
        IsStableCurveFamily B hZ (y.obj (Over.mk (𝟙 U.left))) ∧
          CurveFamily.HasGenus B hZ (y.obj (Over.mk (𝟙 U.left))) g)) ∧
    ∀ {g : ℕ} (_hg : 2 ≤ g) {k : Type u} [Field k] (hk : B.Contains (Spec (.of k)))
      (X : Over (Spec (.of k))) [IsProper X.hom] (hdim : topologicalKrullDim X.left ≤ 1),
      (∀ (U : BigFppfOver B integerBase hZ)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
        y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
        (y.obj (Over.mk (𝟙 U.left)) ≅ curveFamilyOfScheme X B hZ hk hdim) →
        ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
            ObjectProperty.FullSubcategory (IsStableCurveFamilyOfFibreGenus B hZ g),
            z ⋙ ObjectProperty.ι (IsStableCurveFamilyOfFibreGenus B hZ g) = y) ↔
          letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
          haveI : IsProper (X.left ↘ Spec (.of k)) := inferInstanceAs (IsProper X.hom)
          Stacks.Curves.HasAtWorstNodalSingularities k X.left ∧ topologicalKrullDim X.left = 1 ∧
            IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) ∧ genus X.hom = g ∧
            (∀ C : X.left.IdealSheafData, ¬ IsRationalTail k X.left C) ∧
            ∀ C : X.left.IdealSheafData, ¬ IsRationalBridge k X.left C)) ∧
      ((letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
        haveI : IsProper (X.left ↘ Spec (.of k)) := inferInstanceAs (IsProper X.hom)
        Stacks.Curves.HasAtWorstNodalSingularities k X.left ∧ topologicalKrullDim X.left = 1 ∧
          IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) ∧ genus X.hom = g ∧
          (∀ C : X.left.IdealSheafData, ¬ IsRationalTail k X.left C) ∧
          ∀ C : X.left.IdealSheafData, ¬ IsRationalBridge k X.left C) ↔
        letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
        haveI : IsProper (X.left ↘ Spec (.of k)) := inferInstanceAs (IsProper X.hom)
        ∃ (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X.left)
          (hdim1 : topologicalKrullDim X.left = 1)
          (hH0 : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X.left ↘ Spec (.of k)).appTop)),
          genus X.hom = g ∧
            haveI := hH0
            haveI := connectedSpace_of_isIso_globalSections k (X.left ↘ Spec (.of k))
            letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X.left
              hdim1 hnodal
            Scheme.Modules.IsAmple X.left
              (Stacks.Duality.dualizingSheafOverField (X.left ↘ Spec (.of k)))) := by
  refine ⟨fun G hG => ?_, factors_moduliStableCurvesOfGenus_iff_isStableCurveFamily_and_hasGenus,
    fun hg _ _ hk X _ hdim => factors_moduliStableCurvesOfGenus_over_field_iff hg hk X hdim⟩
  have hkG := CurveFamily.bijective_algebraMap_fibre_of_hasUniversallyBijectiveGlobalFunctions
    hG.1.2
  obtain ⟨hclopen, hdisj, -⟩ :=
    G.isClopen_fibreGenusLocus_and_pairwise_disjoint_and_iUnion_eq_univ hkG
  refine ⟨hclopen, fun g g' hne => hdisj (Subtype.coe_ne_coe.mpr hne), ?_,
    fun g F a => isStableCurveFamilyOfFibreGenus_iff_range_subset_fibreGenusLocus hG g a⟩
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨p, rfl⟩ := Quot.exists_rep x
  obtain ⟨V, v, q, hq, hV⟩ := hG.2 p
  exact Set.mem_iUnion.mpr ⟨⟨_, hV.1⟩, p, rfl, V, v, q, hq, rfl⟩

end AlgebraicGeometry

end
