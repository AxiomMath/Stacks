module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGenusH01Statements
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGenusOverField
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesPrestableGenus

/-!
# `Curves^{prestable}_g` over the statements of the cohomological inputs of Stacks 0E6I

The results of `StacksFrontier.AlgebraicGeometry.Quot.CurvesPrestableGenus` about the substacks
`Curves^{prestable}_g` take two inputs in curve-family form: the openness and base-change
compatibility of the fibrewise condition `k = H⁰(X_k, 𝒪_{X_k})`, and the implication from that
fibrewise condition to `f_*𝒪_X = 𝒪_S` universally. This file restates each of them over the two
inputs in the shape in which Stacks 0E0R (at `i = 0`, for `𝓕 = 𝒪_X`) and Stacks 0E6B part (a)
are stated for algebraic spaces — the `hbetti` and `hstruct` of
`StacksFrontier.AlgebraicGeometry.Quot.CurvesH01Inputs`. The conclusions are unchanged; only the
inputs are.

## Main results

All names are in the namespace `AlgebraicGeometry`.

* `isOpenCurvesLocus_isPrestableGenusCurveFamily_of_h01Statements`: condition (o) of Stacks 0E0E
  for `Curves^{prestable}_g`.
* `curvesPrestableGenus_decomposition_of_h01Statements`: the decomposition
  `Curves^{prestable} = ∐_g Curves^{prestable}_g` read on a scheme-valued point.
* `curvesPrestableGenus_isOpenSubstack_and_factors_iff_and_decomposition_of_h01Statements`:
  Stacks 0E6V, the decomposition and part (1).

Writing `P` for the prefix
`curvesPrestableGenus_isOpenSubstack_factors_decomp_overField_`:

* `P` followed by `of_h01Statements`: Stacks 0E6V, the whole statement, with the rank over a
  field as an input `hrk`.
* `P` followed by `of_h01Statements_rightDerived`: the same with `hrk` replaced by the
  comparison of étale and Zariski higher direct images.
* `P` followed by `of_h01Statements_genusRank`: the same with `hrk` discharged.

## References

* [Stacks Project, Tag 0E6V](https://stacks.math.columbia.edu/tag/0E6V)
* [Stacks Project, Tag 0E6I](https://stacks.math.columbia.edu/tag/0E6I)
* [Stacks Project, Tag 0E6K](https://stacks.math.columbia.edu/tag/0E6K)
* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
* [Stacks Project, Tag 0E0R](https://stacks.math.columbia.edu/tag/0E0R)
* [Stacks Project, Tag 0E6B](https://stacks.math.columbia.edu/tag/0E6B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **Condition (o) of Stacks 0E0E for `Curves^{prestable}_g`, over the statements of Stacks 0E0R
(at `i = 0`), 0E6B (a) and 0E1J.** It is the intersection of condition (o) for
`Curves^{prestable}` (Stacks 0E6U) with condition (o) for `Curves_g` (Stacks 0E6K). -/
theorem isOpenCurvesLocus_isPrestableGenusCurveFamily_of_h01Statements
    (hbetti : ∀ {U : BigFppfOver B integerBase hZ} {X : AlgebraicSpaces B integerBase hZ}
      (f : X ⟶ schemeSpace U), Space.IsProper B integerBase hZ f.hom →
      Space.IsFlat B integerBase hZ f.hom → Space.IsFinitePresentation B integerBase hZ f.hom →
      ∃ b : (BigFppfOver.toScheme B integerBase hZ).obj U → ℕ∞, UpperSemicontinuous b ∧
        ∀ p : Space.FieldValuedPoint B integerBase hZ (yoneda.obj U),
          Space.h0FibreRank B integerBase hZ f p = b (Space.schemePoint B integerBase hZ U p))
    (hstruct : ∀ {X Y : AlgebraicSpaces B integerBase hZ} (f : X ⟶ Y),
      Space.IsProper B integerBase hZ f.hom → Space.IsFlat B integerBase hZ f.hom →
      Space.IsFinitePresentation B integerBase hZ f.hom →
      (∀ p : Space.FieldValuedPoint B integerBase hZ Y.1, Function.Bijective
        (algebraMap p.carrier (Space.globalFunctions B (Spec (.of p.carrier)) p.contained
          (Space.fibreOverFieldValuedPoint B integerBase hZ f.hom p)))) →
      IsIso (Space.structureSharp B integerBase hZ f) ∧
        ∀ (Y' : AlgebraicSpaces B integerBase hZ) (g : Y' ⟶ Y),
          IsIso (Space.structureSharp B integerBase hZ (pullback.snd f g)))
    (h2 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.HasFiniteLocallyFreeFirstHigherDirectImage)
    (h3 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.FirstHigherDirectImageCommutesWithBaseChange)
    (g : ℕ) :
    IsOpenCurvesLocus B hZ (IsPrestableGenusCurveFamily B hZ g) :=
  (isOpenCurvesLocus_isPrestableCurveFamily_of
    (CurveFamily.isOpenCurvesLocus_isH01CurveFamily_of_h0FibreRank hbetti hstruct)).and
      (isOpenCurvesLocus_isGenusCurveFamily_of_h01Statements hbetti hstruct h2 h3 g)

/-- **The decomposition `Curves^{prestable} = ∐_g Curves^{prestable}_g` into open and closed
substacks, read on a scheme-valued point of `Curves^{prestable}`, over the statements of Stacks
0E0R (at `i = 0`), 0E6B (a) and 0E1J.** For every prestable family `G` over a scheme `S` there
are subsets `Ω_g` of the points of `S`, open and closed, pairwise disjoint and covering `S`, such
that a family mapping to `G` is in `Curves^{prestable}_g` exactly when its base maps into `Ω_g`.
-/
theorem curvesPrestableGenus_decomposition_of_h01Statements
    (hbetti : ∀ {U : BigFppfOver B integerBase hZ} {X : AlgebraicSpaces B integerBase hZ}
      (f : X ⟶ schemeSpace U), Space.IsProper B integerBase hZ f.hom →
      Space.IsFlat B integerBase hZ f.hom → Space.IsFinitePresentation B integerBase hZ f.hom →
      ∃ b : (BigFppfOver.toScheme B integerBase hZ).obj U → ℕ∞, UpperSemicontinuous b ∧
        ∀ p : Space.FieldValuedPoint B integerBase hZ (yoneda.obj U),
          Space.h0FibreRank B integerBase hZ f p = b (Space.schemePoint B integerBase hZ U p))
    (hstruct : ∀ {X Y : AlgebraicSpaces B integerBase hZ} (f : X ⟶ Y),
      Space.IsProper B integerBase hZ f.hom → Space.IsFlat B integerBase hZ f.hom →
      Space.IsFinitePresentation B integerBase hZ f.hom →
      (∀ p : Space.FieldValuedPoint B integerBase hZ Y.1, Function.Bijective
        (algebraMap p.carrier (Space.globalFunctions B (Spec (.of p.carrier)) p.contained
          (Space.fibreOverFieldValuedPoint B integerBase hZ f.hom p)))) →
      IsIso (Space.structureSharp B integerBase hZ f) ∧
        ∀ (Y' : AlgebraicSpaces B integerBase hZ) (g : Y' ⟶ Y),
          IsIso (Space.structureSharp B integerBase hZ (pullback.snd f g)))
    (h2 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.HasFiniteLocallyFreeFirstHigherDirectImage)
    (h3 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.FirstHigherDirectImageCommutesWithBaseChange)
    (G : CurveFamily B hZ)
    (hG : IsPrestableCurveFamily B hZ G) :
    ∃ Ω : ℕ → Set (Space.points B integerBase hZ (schemeSpace G.base).obj),
      (∀ g, IsOpen (Ω g) ∧ IsClosed (Ω g)) ∧ Pairwise (fun g g' => Disjoint (Ω g) (Ω g')) ∧
        (⋃ g, Ω g) = Set.univ ∧
        ∀ (g : ℕ) (F : CurveFamily B hZ) (a : F ⟶ G),
          IsPrestableGenusCurveFamily B hZ g F ↔
            Set.range (Space.pointsMap B integerBase hZ (schemeSpace F.base).obj
              (schemeSpaceMap a.baseMap).hom) ⊆ Ω g := by
  obtain ⟨Ω, hclopen, hdisj, hcov, hchar⟩ :=
    curvesGenus_decomposition_of_h01Statements hbetti hstruct h2 h3 G
      (isH01CurveFamily_of_isPrestableCurveFamily hG)
  refine ⟨Ω, hclopen, hdisj, hcov, fun g F a => ?_⟩
  have hF : IsPrestableCurveFamily B hZ F :=
    (isOpenCurvesLocus_isPrestableCurveFamily_of
      (CurveFamily.isOpenCurvesLocus_isH01CurveFamily_of_h0FibreRank hbetti
        hstruct)).prop_of_hom a hG
  exact (and_iff_right hF).trans (hchar g F a)

/-- **Stacks 0E6V, the decomposition and part (1), over the statements of Stacks 0E0R (at
`i = 0`), 0E6B (a) and 0E1J.** For every `g ≥ 0`
* `Curves^{prestable}_g` is an open substack of `Curves`, contained in `Curves^{prestable}`;
* the classifying morphism of a family of curves `f : X → S` factors through
  `Curves^{prestable}_g` exactly when `f` is a prestable family of curves and `R¹f_*𝒪_X` is a
  locally free `𝒪_S`-module of rank `g` (part (1));
* over every prestable family, with base `S`, the loci of the `Curves^{prestable}_g` are open and
  closed subsets of `S` which are pairwise disjoint and cover `S`:
  `Curves^{prestable} = ∐_g Curves^{prestable}_g` as open and closed substacks. -/
theorem curvesPrestableGenus_isOpenSubstack_and_factors_iff_and_decomposition_of_h01Statements
    (hbetti : ∀ {U : BigFppfOver B integerBase hZ} {X : AlgebraicSpaces B integerBase hZ}
      (f : X ⟶ schemeSpace U), Space.IsProper B integerBase hZ f.hom →
      Space.IsFlat B integerBase hZ f.hom → Space.IsFinitePresentation B integerBase hZ f.hom →
      ∃ b : (BigFppfOver.toScheme B integerBase hZ).obj U → ℕ∞, UpperSemicontinuous b ∧
        ∀ p : Space.FieldValuedPoint B integerBase hZ (yoneda.obj U),
          Space.h0FibreRank B integerBase hZ f p = b (Space.schemePoint B integerBase hZ U p))
    (hstruct : ∀ {X Y : AlgebraicSpaces B integerBase hZ} (f : X ⟶ Y),
      Space.IsProper B integerBase hZ f.hom → Space.IsFlat B integerBase hZ f.hom →
      Space.IsFinitePresentation B integerBase hZ f.hom →
      (∀ p : Space.FieldValuedPoint B integerBase hZ Y.1, Function.Bijective
        (algebraMap p.carrier (Space.globalFunctions B (Spec (.of p.carrier)) p.contained
          (Space.fibreOverFieldValuedPoint B integerBase hZ f.hom p)))) →
      IsIso (Space.structureSharp B integerBase hZ f) ∧
        ∀ (Y' : AlgebraicSpaces B integerBase hZ) (g : Y' ⟶ Y),
          IsIso (Space.structureSharp B integerBase hZ (pullback.snd f g)))
    (h2 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.HasFiniteLocallyFreeFirstHigherDirectImage)
    (h3 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.FirstHigherDirectImageCommutesWithBaseChange)
    :
    (∀ g : ℕ,
      (ObjectProperty.IsClosedUnderIsomorphisms (IsPrestableGenusCurveFamily B hZ g) ∧
        Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
          (curvesSubstackInclusion B hZ (IsPrestableGenusCurveFamily B hZ g)
            (isOpenCurvesLocus_isPrestableGenusCurveFamily_of_h01Statements hbetti hstruct h2 h3
              g).prop_of_hom).hom ∧
        Stack.IsOpenImmersion B integerBase hZ
          (curvesSubstackInclusion B hZ (IsPrestableGenusCurveFamily B hZ g)
            (isOpenCurvesLocus_isPrestableGenusCurveFamily_of_h01Statements hbetti hstruct h2 h3
              g).prop_of_hom)) ∧
      (∀ X : CurveFamily B hZ, IsPrestableGenusCurveFamily B hZ g X →
        IsPrestableCurveFamily B hZ X) ∧
      ∀ (U : BigFppfOver B integerBase hZ)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
        y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
        ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
            ObjectProperty.FullSubcategory (IsPrestableGenusCurveFamily B hZ g),
            z ⋙ ObjectProperty.ι (IsPrestableGenusCurveFamily B hZ g) = y) ↔
          IsPrestableCurveFamily B hZ (y.obj (Over.mk (𝟙 U.left))) ∧
            RingedSite.IsFiniteLocallyFreeOfRank
              (Space.smallEtaleRingedSite B integerBase hZ
                (schemeSpace (y.obj (Over.mk (𝟙 U.left))).base).1
                (schemeSpace (y.obj (Over.mk (𝟙 U.left))).base).2)
              ((y.obj (Over.mk (𝟙 U.left))).firstDirectImage B hZ) g)) ∧
    ∀ G : CurveFamily B hZ, IsPrestableCurveFamily B hZ G →
      ∃ Ω : ℕ → Set (Space.points B integerBase hZ (schemeSpace G.base).obj),
        (∀ g, IsOpen (Ω g) ∧ IsClosed (Ω g)) ∧ Pairwise (fun g g' => Disjoint (Ω g) (Ω g')) ∧
          (⋃ g, Ω g) = Set.univ ∧
          ∀ (g : ℕ) (F : CurveFamily B hZ) (a : F ⟶ G),
            IsPrestableGenusCurveFamily B hZ g F ↔
              Set.range (Space.pointsMap B integerBase hZ (schemeSpace F.base).obj
                (schemeSpaceMap a.baseMap).hom) ⊆ Ω g :=
  ⟨fun g => ⟨isOpenImmersion_curvesSubstackInclusion
      (isOpenCurvesLocus_isPrestableGenusCurveFamily_of_h01Statements hbetti hstruct h2 h3 g),
    fun _ h => h.1,
    fun U y hy => (factors_curvesSubstack_iff
      (isOpenCurvesLocus_isPrestableGenusCurveFamily_of_h01Statements hbetti hstruct h2 h3 g) U y
        hy).trans (isPrestableGenusCurveFamily_iff g _)⟩,
    curvesPrestableGenus_decomposition_of_h01Statements hbetti hstruct h2 h3⟩

/-- **Stacks 0E6V, over the statements of Stacks 0E0R (at `i = 0`) and 0E6B (a).** There is a
decomposition `Curves^{prestable} = ∐_{g ≥ 0} Curves^{prestable}_g` into open and closed
substacks, where
1. the classifying morphism of a family of curves `f : X → S` factors through
   `Curves^{prestable}_g` exactly when `f` is a prestable family of curves and `R¹f_*𝒪_X` is a
   locally free `𝒪_S`-module of rank `g`;
2. for a scheme `X` proper over a field `k` with `dim(X) ≤ 1` (a proper morphism `p : T ⟶ W` of
   the site with `W = Spec k`), the classifying morphism `Spec k → Curves` of `X` factors through
   `Curves^{prestable}_g` exactly when the singularities of `X` are at-worst-nodal, `dim(X) = 1`,
   `k = H⁰(X, 𝒪_X)` and the genus of `X` is `g`.

Each `Curves^{prestable}_g` is an open substack of `Curves` contained in `Curves^{prestable}`, and
over every scheme-valued point of `Curves^{prestable}` the loci of the `Curves^{prestable}_g` are
open and closed, pairwise disjoint, and cover the base.

The inputs are `hbetti` (Stacks 0E0R at `i = 0`, for `𝓕 = 𝒪_X`), `hstruct` (Stacks 0E6B part
(a)), parts (2) and (3) of Stacks 0E1J (`h2`, `h3`), the at-worst-nodal criterion over a field
(`hsch`), and the input of part (2) of Stacks 0E6K that `R¹f_*𝒪_X` over a field has rank the
genus (`hrk`). -/
theorem curvesPrestableGenus_isOpenSubstack_factors_decomp_overField_of_h01Statements
    (hbetti : ∀ {U : BigFppfOver B integerBase hZ} {X : AlgebraicSpaces B integerBase hZ}
      (f : X ⟶ schemeSpace U), Space.IsProper B integerBase hZ f.hom →
      Space.IsFlat B integerBase hZ f.hom → Space.IsFinitePresentation B integerBase hZ f.hom →
      ∃ b : (BigFppfOver.toScheme B integerBase hZ).obj U → ℕ∞, UpperSemicontinuous b ∧
        ∀ p : Space.FieldValuedPoint B integerBase hZ (yoneda.obj U),
          Space.h0FibreRank B integerBase hZ f p = b (Space.schemePoint B integerBase hZ U p))
    (hstruct : ∀ {X Y : AlgebraicSpaces B integerBase hZ} (f : X ⟶ Y),
      Space.IsProper B integerBase hZ f.hom → Space.IsFlat B integerBase hZ f.hom →
      Space.IsFinitePresentation B integerBase hZ f.hom →
      (∀ p : Space.FieldValuedPoint B integerBase hZ Y.1, Function.Bijective
        (algebraMap p.carrier (Space.globalFunctions B (Spec (.of p.carrier)) p.contained
          (Space.fibreOverFieldValuedPoint B integerBase hZ f.hom p)))) →
      IsIso (Space.structureSharp B integerBase hZ f) ∧
        ∀ (Y' : AlgebraicSpaces B integerBase hZ) (g : Y' ⟶ Y),
          IsIso (Space.structureSharp B integerBase hZ (pullback.snd f g)))
    (h2 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.HasFiniteLocallyFreeFirstHigherDirectImage)
    (h3 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.FirstHigherDirectImageCommutesWithBaseChange)
    (hsch : ∀ (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [LocallyOfFiniteType (X ↘ Spec (.of k))],
      IsAtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k)) ↔
        (Stacks.Curves.HasAtWorstNodalSingularities k X ∧ TopologicalSpace.Equidimensional X ∧
          ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = (1 : WithBot ℕ∞)))
    (hrk : ∀ (k : Type u) [Field k] {T W : BigFppfOver B integerBase hZ} (p : T ⟶ W)
      (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
      (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map p))
      (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1),
      IsH01CurveFamily B hZ (curveFamilyOverFieldOfProper B hZ p k hW hproper hdim) →
      RingedSite.IsFiniteLocallyFreeOfRank
        (Space.smallEtaleRingedSite B integerBase hZ
          (schemeSpace (curveFamilyOverFieldOfProper B hZ p k hW hproper hdim).base).1
          (schemeSpace (curveFamilyOverFieldOfProper B hZ p k hW hproper hdim).base).2)
        ((curveFamilyOverFieldOfProper B hZ p k hW hproper hdim).firstDirectImage B hZ)
        (genus ((BigFppfOver.toScheme B integerBase hZ).map p ≫ eqToHom hW))) :
    (∀ g : ℕ,
      (ObjectProperty.IsClosedUnderIsomorphisms (IsPrestableGenusCurveFamily B hZ g) ∧
        Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
          (curvesSubstackInclusion B hZ (IsPrestableGenusCurveFamily B hZ g)
            (isOpenCurvesLocus_isPrestableGenusCurveFamily_of_h01Statements hbetti hstruct h2 h3
              g).prop_of_hom).hom ∧
        Stack.IsOpenImmersion B integerBase hZ
          (curvesSubstackInclusion B hZ (IsPrestableGenusCurveFamily B hZ g)
            (isOpenCurvesLocus_isPrestableGenusCurveFamily_of_h01Statements hbetti hstruct h2 h3
              g).prop_of_hom)) ∧
      (∀ X : CurveFamily B hZ, IsPrestableGenusCurveFamily B hZ g X →
        IsPrestableCurveFamily B hZ X) ∧
      ∀ (U : BigFppfOver B integerBase hZ)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
        y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
        ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
            ObjectProperty.FullSubcategory (IsPrestableGenusCurveFamily B hZ g),
            z ⋙ ObjectProperty.ι (IsPrestableGenusCurveFamily B hZ g) = y) ↔
          IsPrestableCurveFamily B hZ (y.obj (Over.mk (𝟙 U.left))) ∧
            RingedSite.IsFiniteLocallyFreeOfRank
              (Space.smallEtaleRingedSite B integerBase hZ
                (schemeSpace (y.obj (Over.mk (𝟙 U.left))).base).1
                (schemeSpace (y.obj (Over.mk (𝟙 U.left))).base).2)
              ((y.obj (Over.mk (𝟙 U.left))).firstDirectImage B hZ) g)) ∧
    (∀ G : CurveFamily B hZ, IsPrestableCurveFamily B hZ G →
      ∃ Ω : ℕ → Set (Space.points B integerBase hZ (schemeSpace G.base).obj),
        (∀ g, IsOpen (Ω g) ∧ IsClosed (Ω g)) ∧ Pairwise (fun g g' => Disjoint (Ω g) (Ω g')) ∧
          (⋃ g, Ω g) = Set.univ ∧
          ∀ (g : ℕ) (F : CurveFamily B hZ) (a : F ⟶ G),
            IsPrestableGenusCurveFamily B hZ g F ↔
              Set.range (Space.pointsMap B integerBase hZ (schemeSpace F.base).obj
                (schemeSpaceMap a.baseMap).hom) ⊆ Ω g) ∧
    (∀ (g : ℕ) (k : Type u) [Field k] {T W : BigFppfOver B integerBase hZ} (p : T ⟶ W)
      (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
      (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map p))
      (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
      (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      (y.obj (Over.mk (𝟙 U.left)) ≅ curveFamilyOverFieldOfProper B hZ p k hW hproper hdim) →
      letI : ((BigFppfOver.toScheme B integerBase hZ).obj T).Over (Spec (.of k)) :=
        ⟨(BigFppfOver.toScheme B integerBase hZ).map p ≫ eqToHom hW⟩
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsPrestableGenusCurveFamily B hZ g),
          z ⋙ ObjectProperty.ι (IsPrestableGenusCurveFamily B hZ g) = y) ↔
        (Stacks.Curves.HasAtWorstNodalSingularities k
            ((BigFppfOver.toScheme B integerBase hZ).obj T) ∧
          topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1 ∧
          Function.Bijective
            ((BigFppfOver.toScheme B integerBase hZ).map p ≫ eqToHom hW).appTop ∧
          genus ((BigFppfOver.toScheme B integerBase hZ).map p ≫ eqToHom hW) = g))) := by
  have hpush : ∀ X : CurveFamily B hZ,
      CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ X →
      HasUniversallyBijectiveGlobalFunctions B hZ X := fun _ hX =>
    CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_hasBijectiveGlobalFunctionsOnFieldFibres
      hstruct hX
  obtain ⟨h1, hdec⟩ :=
    curvesPrestableGenus_isOpenSubstack_and_factors_iff_and_decomposition_of_h01Statements hbetti
      hstruct h2 h3
  refine ⟨h1, hdec, ?_⟩
  intro g k _ T W p hW hproper hdim U y hy e
  rw [factors_curvesSubstack_iff_of_iso
    (isOpenCurvesLocus_isPrestableGenusCurveFamily_of_h01Statements hbetti hstruct h2 h3 g) U y hy
    _ e]
  exact isPrestableGenusCurveFamily_curveFamilyOverFieldOfProper_iff_of hpush hsch hrk g k p hW
    hproper hdim

/-- **Stacks 0E6V, over the statements of Stacks 0E0R (at `i = 0`) and 0E6B (a), with `hrk`
discharged.** The whole statement of the theorem of the same name without the suffix `_genusRank`,
with its input `hrk` — the rank of `R¹f_*𝒪_X` over a field, part (2) of Stacks 0E6K — discharged by
`isFiniteLocallyFreeOfRank_firstDirectImage_curveFamilyOverFieldOfProper_genus`. The inputs that
remain are `hbetti` (Stacks 0E0R at `i = 0`, for `𝓕 = 𝒪_X`), `hstruct` (Stacks 0E6B part (a)),
parts (2) and (3) of Stacks 0E1J (`h2`, `h3`), and the at-worst-nodal criterion over a field
(`hsch`, the scheme-level content of part (2) of Stacks 0DSY). -/
theorem curvesPrestableGenus_isOpenSubstack_factors_decomp_overField_of_h01Statements_genusRank
    (hbetti : ∀ {U : BigFppfOver B integerBase hZ} {X : AlgebraicSpaces B integerBase hZ}
      (f : X ⟶ schemeSpace U), Space.IsProper B integerBase hZ f.hom →
      Space.IsFlat B integerBase hZ f.hom → Space.IsFinitePresentation B integerBase hZ f.hom →
      ∃ b : (BigFppfOver.toScheme B integerBase hZ).obj U → ℕ∞, UpperSemicontinuous b ∧
        ∀ p : Space.FieldValuedPoint B integerBase hZ (yoneda.obj U),
          Space.h0FibreRank B integerBase hZ f p = b (Space.schemePoint B integerBase hZ U p))
    (hstruct : ∀ {X Y : AlgebraicSpaces B integerBase hZ} (f : X ⟶ Y),
      Space.IsProper B integerBase hZ f.hom → Space.IsFlat B integerBase hZ f.hom →
      Space.IsFinitePresentation B integerBase hZ f.hom →
      (∀ p : Space.FieldValuedPoint B integerBase hZ Y.1, Function.Bijective
        (algebraMap p.carrier (Space.globalFunctions B (Spec (.of p.carrier)) p.contained
          (Space.fibreOverFieldValuedPoint B integerBase hZ f.hom p)))) →
      IsIso (Space.structureSharp B integerBase hZ f) ∧
        ∀ (Y' : AlgebraicSpaces B integerBase hZ) (g : Y' ⟶ Y),
          IsIso (Space.structureSharp B integerBase hZ (pullback.snd f g)))
    (h2 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.HasFiniteLocallyFreeFirstHigherDirectImage)
    (h3 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.FirstHigherDirectImageCommutesWithBaseChange)
    (hsch : ∀ (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [LocallyOfFiniteType (X ↘ Spec (.of k))],
      IsAtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k)) ↔
        (Stacks.Curves.HasAtWorstNodalSingularities k X ∧ TopologicalSpace.Equidimensional X ∧
          ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = (1 : WithBot ℕ∞))) :
    (∀ g : ℕ,
      (ObjectProperty.IsClosedUnderIsomorphisms (IsPrestableGenusCurveFamily B hZ g) ∧
        Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
          (curvesSubstackInclusion B hZ (IsPrestableGenusCurveFamily B hZ g)
            (isOpenCurvesLocus_isPrestableGenusCurveFamily_of_h01Statements hbetti hstruct h2 h3
              g).prop_of_hom).hom ∧
        Stack.IsOpenImmersion B integerBase hZ
          (curvesSubstackInclusion B hZ (IsPrestableGenusCurveFamily B hZ g)
            (isOpenCurvesLocus_isPrestableGenusCurveFamily_of_h01Statements hbetti hstruct h2 h3
              g).prop_of_hom)) ∧
      (∀ X : CurveFamily B hZ, IsPrestableGenusCurveFamily B hZ g X →
        IsPrestableCurveFamily B hZ X) ∧
      ∀ (U : BigFppfOver B integerBase hZ)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
        y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
        ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
            ObjectProperty.FullSubcategory (IsPrestableGenusCurveFamily B hZ g),
            z ⋙ ObjectProperty.ι (IsPrestableGenusCurveFamily B hZ g) = y) ↔
          IsPrestableCurveFamily B hZ (y.obj (Over.mk (𝟙 U.left))) ∧
            RingedSite.IsFiniteLocallyFreeOfRank
              (Space.smallEtaleRingedSite B integerBase hZ
                (schemeSpace (y.obj (Over.mk (𝟙 U.left))).base).1
                (schemeSpace (y.obj (Over.mk (𝟙 U.left))).base).2)
              ((y.obj (Over.mk (𝟙 U.left))).firstDirectImage B hZ) g)) ∧
    (∀ G : CurveFamily B hZ, IsPrestableCurveFamily B hZ G →
      ∃ Ω : ℕ → Set (Space.points B integerBase hZ (schemeSpace G.base).obj),
        (∀ g, IsOpen (Ω g) ∧ IsClosed (Ω g)) ∧ Pairwise (fun g g' => Disjoint (Ω g) (Ω g')) ∧
          (⋃ g, Ω g) = Set.univ ∧
          ∀ (g : ℕ) (F : CurveFamily B hZ) (a : F ⟶ G),
            IsPrestableGenusCurveFamily B hZ g F ↔
              Set.range (Space.pointsMap B integerBase hZ (schemeSpace F.base).obj
                (schemeSpaceMap a.baseMap).hom) ⊆ Ω g) ∧
    (∀ (g : ℕ) (k : Type u) [Field k] {T W : BigFppfOver B integerBase hZ} (p : T ⟶ W)
      (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
      (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map p))
      (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
      (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      (y.obj (Over.mk (𝟙 U.left)) ≅ curveFamilyOverFieldOfProper B hZ p k hW hproper hdim) →
      letI : ((BigFppfOver.toScheme B integerBase hZ).obj T).Over (Spec (.of k)) :=
        ⟨(BigFppfOver.toScheme B integerBase hZ).map p ≫ eqToHom hW⟩
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsPrestableGenusCurveFamily B hZ g),
          z ⋙ ObjectProperty.ι (IsPrestableGenusCurveFamily B hZ g) = y) ↔
        (Stacks.Curves.HasAtWorstNodalSingularities k
            ((BigFppfOver.toScheme B integerBase hZ).obj T) ∧
          topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1 ∧
          Function.Bijective
            ((BigFppfOver.toScheme B integerBase hZ).map p ≫ eqToHom hW).appTop ∧
          genus ((BigFppfOver.toScheme B integerBase hZ).map p ≫ eqToHom hW) = g))) :=
  curvesPrestableGenus_isOpenSubstack_factors_decomp_overField_of_h01Statements
    hbetti hstruct h2 h3 hsch fun k _ _ _ p hW hproper hdim _ =>
      isFiniteLocallyFreeOfRank_firstDirectImage_curveFamilyOverFieldOfProper_genus k p hW hproper
        hdim

section RightDerivedComparison

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/-- **Stacks 0E6V, over the statements of Stacks 0E0R (at `i = 0`) and 0E6B (a), with `hrk` from
Stacks 071N.** The whole statement of the theorem of the same name without the suffix
`_rightDerived`, with the rank of `R¹f_*𝒪_X` over a field supplied by
`isFiniteLocallyFreeOfRank_firstHigherDirectImage_curveFamilyOfSchemeMorphism_genus_of`:
the only input replacing `hrk` is the comparison of the étale higher direct images of a
quasi-compact separated morphism of schemes with the Zariski ones (`h071N`, Stacks 071N). -/
theorem curvesPrestableGenus_isOpenSubstack_factors_decomp_overField_of_h01Statements_rightDerived
    (hbetti : ∀ {U : BigFppfOver B integerBase hZ} {X : AlgebraicSpaces B integerBase hZ}
      (f : X ⟶ schemeSpace U), Space.IsProper B integerBase hZ f.hom →
      Space.IsFlat B integerBase hZ f.hom → Space.IsFinitePresentation B integerBase hZ f.hom →
      ∃ b : (BigFppfOver.toScheme B integerBase hZ).obj U → ℕ∞, UpperSemicontinuous b ∧
        ∀ p : Space.FieldValuedPoint B integerBase hZ (yoneda.obj U),
          Space.h0FibreRank B integerBase hZ f p = b (Space.schemePoint B integerBase hZ U p))
    (hstruct : ∀ {X Y : AlgebraicSpaces B integerBase hZ} (f : X ⟶ Y),
      Space.IsProper B integerBase hZ f.hom → Space.IsFlat B integerBase hZ f.hom →
      Space.IsFinitePresentation B integerBase hZ f.hom →
      (∀ p : Space.FieldValuedPoint B integerBase hZ Y.1, Function.Bijective
        (algebraMap p.carrier (Space.globalFunctions B (Spec (.of p.carrier)) p.contained
          (Space.fibreOverFieldValuedPoint B integerBase hZ f.hom p)))) →
      IsIso (Space.structureSharp B integerBase hZ f) ∧
        ∀ (Y' : AlgebraicSpaces B integerBase hZ) (g : Y' ⟶ Y),
          IsIso (Space.structureSharp B integerBase hZ (pullback.snd f g)))
    (h2 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.HasFiniteLocallyFreeFirstHigherDirectImage)
    (h3 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.FirstHigherDirectImageCommutesWithBaseChange)
    (hsch : ∀ (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [LocallyOfFiniteType (X ↘ Spec (.of k))],
      IsAtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k)) ↔
        (Stacks.Curves.HasAtWorstNodalSingularities k X ∧ TopologicalSpace.Equidimensional X ∧
          ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = (1 : WithBot ℕ∞)))
    (h071N : ∀ {T' T : BigFppfOver B integerBase hZ} (g : T' ⟶ T)
      (_hqc : QuasiCompact ((BigFppfOver.toScheme B integerBase hZ).map g))
      (_hsep : IsSeparated ((BigFppfOver.toScheme B integerBase hZ).map g))
      (F : ((BigFppfOver.toScheme B integerBase hZ).obj T').Modules) (_hF : F.IsQuasicoherent)
      (k : ℕ),
      have := Space.hasInjectiveResolutions_modules B integerBase hZ (yoneda.obj T')
        (isAlgebraicSpace_yoneda B integerBase hZ T')
      have := Space.modulePushforward_additive B integerBase hZ
        (Space.representedSpaceMap B integerBase hZ g)
      Nonempty (((Space.modulePushforward B integerBase hZ
          (Space.representedSpaceMap B integerBase hZ g)).rightDerived k).obj
          ((Space.representedAssociatedModule B integerBase hZ T'
            (isAlgebraicSpace_yoneda B integerBase hZ T')).obj F) ≅
        (Space.representedAssociatedModule B integerBase hZ T
            (isAlgebraicSpace_yoneda B integerBase hZ T)).obj
          (((Scheme.Modules.pushforward
            ((BigFppfOver.toScheme B integerBase hZ).map g)).rightDerived k).obj F))) :
    (∀ g : ℕ,
      (ObjectProperty.IsClosedUnderIsomorphisms (IsPrestableGenusCurveFamily B hZ g) ∧
        Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
          (curvesSubstackInclusion B hZ (IsPrestableGenusCurveFamily B hZ g)
            (isOpenCurvesLocus_isPrestableGenusCurveFamily_of_h01Statements hbetti hstruct h2 h3
              g).prop_of_hom).hom ∧
        Stack.IsOpenImmersion B integerBase hZ
          (curvesSubstackInclusion B hZ (IsPrestableGenusCurveFamily B hZ g)
            (isOpenCurvesLocus_isPrestableGenusCurveFamily_of_h01Statements hbetti hstruct h2 h3
              g).prop_of_hom)) ∧
      (∀ X : CurveFamily B hZ, IsPrestableGenusCurveFamily B hZ g X →
        IsPrestableCurveFamily B hZ X) ∧
      ∀ (U : BigFppfOver B integerBase hZ)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
        y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
        ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
            ObjectProperty.FullSubcategory (IsPrestableGenusCurveFamily B hZ g),
            z ⋙ ObjectProperty.ι (IsPrestableGenusCurveFamily B hZ g) = y) ↔
          IsPrestableCurveFamily B hZ (y.obj (Over.mk (𝟙 U.left))) ∧
            RingedSite.IsFiniteLocallyFreeOfRank
              (Space.smallEtaleRingedSite B integerBase hZ
                (schemeSpace (y.obj (Over.mk (𝟙 U.left))).base).1
                (schemeSpace (y.obj (Over.mk (𝟙 U.left))).base).2)
              ((y.obj (Over.mk (𝟙 U.left))).firstDirectImage B hZ) g)) ∧
    (∀ G : CurveFamily B hZ, IsPrestableCurveFamily B hZ G →
      ∃ Ω : ℕ → Set (Space.points B integerBase hZ (schemeSpace G.base).obj),
        (∀ g, IsOpen (Ω g) ∧ IsClosed (Ω g)) ∧ Pairwise (fun g g' => Disjoint (Ω g) (Ω g')) ∧
          (⋃ g, Ω g) = Set.univ ∧
          ∀ (g : ℕ) (F : CurveFamily B hZ) (a : F ⟶ G),
            IsPrestableGenusCurveFamily B hZ g F ↔
              Set.range (Space.pointsMap B integerBase hZ (schemeSpace F.base).obj
                (schemeSpaceMap a.baseMap).hom) ⊆ Ω g) ∧
    (∀ (g : ℕ) (k : Type u) [Field k] {T W : BigFppfOver B integerBase hZ} (p : T ⟶ W)
      (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
      (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map p))
      (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)
      (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      (y.obj (Over.mk (𝟙 U.left)) ≅ curveFamilyOverFieldOfProper B hZ p k hW hproper hdim) →
      letI : ((BigFppfOver.toScheme B integerBase hZ).obj T).Over (Spec (.of k)) :=
        ⟨(BigFppfOver.toScheme B integerBase hZ).map p ≫ eqToHom hW⟩
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsPrestableGenusCurveFamily B hZ g),
          z ⋙ ObjectProperty.ι (IsPrestableGenusCurveFamily B hZ g) = y) ↔
        (Stacks.Curves.HasAtWorstNodalSingularities k
            ((BigFppfOver.toScheme B integerBase hZ).obj T) ∧
          topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1 ∧
          Function.Bijective
            ((BigFppfOver.toScheme B integerBase hZ).map p ≫ eqToHom hW).appTop ∧
          genus ((BigFppfOver.toScheme B integerBase hZ).map p ≫ eqToHom hW) = g))) :=
  curvesPrestableGenus_isOpenSubstack_factors_decomp_overField_of_h01Statements
    hbetti hstruct h2 h3 hsch fun k _ _ _ p hW hproper hdim _ =>
      isFiniteLocallyFreeOfRank_firstHigherDirectImage_curveFamilyOfSchemeMorphism_genus_of h071N p
        _ hproper _ _ _ _ hdim k hW

end RightDerivedComparison

end AlgebraicGeometry

end
