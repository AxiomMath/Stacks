module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGenus
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGenusDecomposition
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01Inputs

/-!
# `Curves_g` over the statements of the cohomological inputs of Stacks 0E6I

The results of `StacksFrontier.AlgebraicGeometry.Quot.CurvesGenus` about the substack `Curves_g`
take two inputs in curve-family form: the openness and base-change compatibility of the fibrewise
condition `k = H⁰(X_k, 𝒪_{X_k})` on families of curves, and the implication from that fibrewise
condition to `f_*𝒪_X = 𝒪_S` universally. This file restates each of them over the two inputs in
the shape in which Stacks 0E0R (at `i = 0`, for `𝓕 = 𝒪_X`) and Stacks 0E6B part (a) are stated
for algebraic spaces, namely the `hbetti` and `hstruct` of
`StacksFrontier.AlgebraicGeometry.Quot.CurvesH01Inputs`. The conclusions are unchanged; only the
inputs are.

## Main results

* `AlgebraicGeometry.isGenusCurveFamily_iff_of_h01Statements`: a family over a family in
  `Curves^{h0,1}` is in `Curves_g` exactly when its base maps into the rank locus of `g`.
* `AlgebraicGeometry.isOpenCurvesLocus_isGenusCurveFamily_of_h01Statements`: condition (o) of
  Stacks 0E0E for `Curves_g`.
* `AlgebraicGeometry.curvesGenus_decomposition_of_h01Statements`: the decomposition
  `Curves^{h0,1} = ∐_g Curves_g` read on a scheme-valued point.
* `curvesGenus_isOpenSubstack_and_factors_iff_and_decomposition_of_h01Statements`: Stacks 0E6K,
  the decomposition and part (1).

## References

* [Stacks Project, Tag 0E6K](https://stacks.math.columbia.edu/tag/0E6K)
* [Stacks Project, Tag 0E6I](https://stacks.math.columbia.edu/tag/0E6I)
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

/-- **The genus of a family over a family in `Curves^{h0,1}`, over the statements of Stacks 0E0R
(at `i = 0`) and 0E6B (a).** Let `G` be a family in `Curves^{h0,1}` and suppose `R¹f_*𝒪_G` finite
locally free with formation commuting with base change (Stacks 0E1J, parts (2) and (3)). Then a
family `F` mapping to `G` is in `Curves_g` exactly when its base maps into the rank locus of `g`
of `R¹f_*𝒪_G`. -/
theorem isGenusCurveFamily_iff_of_h01Statements
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
    (h3 : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.FirstHigherDirectImageCommutesWithBaseChange)
    (g : ℕ) {G : CurveFamily B hZ}
    (hG : IsH01CurveFamily B hZ G)
    (hR : SheafOfModules.IsFiniteLocallyFreeOnSite (G.firstDirectImage B hZ))
    (F : CurveFamily B hZ) (a : F ⟶ G) :
    IsGenusCurveFamily B hZ g F ↔
      Set.range (Space.pointsMap B integerBase hZ (schemeSpace F.base).obj
        (schemeSpaceMap a.baseMap).hom) ⊆ Space.rankLocus (G.firstDirectImage B hZ) g := by
  have hF : IsH01CurveFamily B hZ F :=
    (CurveFamily.isOpenCurvesLocus_isH01CurveFamily_of_h0FibreRank hbetti
      hstruct).prop_of_hom a hG
  obtain ⟨e⟩ := h3 G
    (CurveFamily.hasResidueFieldGlobalFunctions_of_hasUniversallyBijectiveGlobalFunctions hG.1)
    F a
  rw [← Space.isFiniteLocallyFreeOfRank_modulePullback_iff (schemeSpaceMap a.baseMap) hR g]
  exact ⟨fun h => RingedSite.IsFiniteLocallyFreeOfRank.of_iso _ _ e.symm h.2,
    fun h => ⟨hF, RingedSite.IsFiniteLocallyFreeOfRank.of_iso _ _ e h⟩⟩

/-- **Condition (o) of Stacks 0E0E for `Curves_g`, over the statements of Stacks 0E0R (at
`i = 0`), 0E6B (a) and 0E1J.** The locus is cut out, over a family in `Curves^{h0,1}`, by the
open rank locus of `g` of `R¹f_*𝒪`, and `Curves^{h0,1}` is open by Stacks 0E6I. -/
theorem isOpenCurvesLocus_isGenusCurveFamily_of_h01Statements
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
    IsOpenCurvesLocus B hZ (IsGenusCurveFamily B hZ g) :=
  IsOpenCurvesLocus.of_points_of_isOpenCurvesLocus
    (CurveFamily.isOpenCurvesLocus_isH01CurveFamily_of_h0FibreRank hbetti hstruct)
    (fun _ h => h.1) fun G hG =>
      ⟨Space.rankLocus (G.firstDirectImage B hZ) g, Space.isOpen_rankLocus _ g,
        isGenusCurveFamily_iff_of_h01Statements hbetti hstruct h3 g hG
          (isFiniteLocallyFreeOnSite_firstHigherDirectImage_of h2 hG)⟩

/-- **The decomposition `Curves^{h0,1} = ∐_g Curves_g` into open and closed substacks, read on a
scheme-valued point of `Curves^{h0,1}`, over the statements of Stacks 0E0R (at `i = 0`), 0E6B (a)
and 0E1J.** For every family `G` over a scheme `S` in `Curves^{h0,1}` there are subsets `Ω_g` of
the points of `S`, open and closed, pairwise disjoint and covering `S`, such that a family
mapping to `G` is in `Curves_g` exactly when its base maps into `Ω_g`. -/
theorem curvesGenus_decomposition_of_h01Statements
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
    (hG : IsH01CurveFamily B hZ G) :
    ∃ Ω : ℕ → Set (Space.points B integerBase hZ (schemeSpace G.base).obj),
      (∀ g, IsOpen (Ω g) ∧ IsClosed (Ω g)) ∧ Pairwise (fun g g' => Disjoint (Ω g) (Ω g')) ∧
        (⋃ g, Ω g) = Set.univ ∧
        ∀ (g : ℕ) (F : CurveFamily B hZ) (a : F ⟶ G),
          IsGenusCurveFamily B hZ g F ↔
            Set.range (Space.pointsMap B integerBase hZ (schemeSpace F.base).obj
              (schemeSpaceMap a.baseMap).hom) ⊆ Ω g := by
  have hR := isFiniteLocallyFreeOnSite_firstHigherDirectImage_of h2 hG
  let Ω : ℕ → Set (Space.points B integerBase hZ (schemeSpace G.base).obj) :=
    fun g => Space.rankLocus (G.firstDirectImage B hZ) g
  have hdisj : Pairwise (fun g g' => Disjoint (Ω g) (Ω g')) := fun g g' hne =>
    Set.disjoint_left.mpr fun s hs hs' => hne (Space.eq_of_mem_rankLocus_of_mem_rankLocus hs hs')
  have hcov : (⋃ g, Ω g) = Set.univ :=
    Set.eq_univ_of_forall fun s => Set.mem_iUnion.mpr (Space.exists_mem_rankLocus hR s)
  refine ⟨Ω, fun g => ⟨Space.isOpen_rankLocus _ g, ?_⟩, hdisj, hcov,
    fun g => isGenusCurveFamily_iff_of_h01Statements hbetti hstruct h3 g hG hR⟩
  have hcompl : (Ω g)ᶜ = ⋃ g' ∈ {g' | g' ≠ g}, Ω g' := by
    ext s
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    refine ⟨fun hs => ?_, fun ⟨g', hne, hs'⟩ hs =>
      hne (Space.eq_of_mem_rankLocus_of_mem_rankLocus hs' hs)⟩
    obtain ⟨g', hg'⟩ := Set.mem_iUnion.mp (hcov.symm ▸ Set.mem_univ s : s ∈ ⋃ g, Ω g)
    exact ⟨g', fun h => hs (h ▸ hg'), hg'⟩
  exact isOpen_compl_iff.mp (hcompl ▸ isOpen_biUnion fun g' _ => Space.isOpen_rankLocus _ g')

/-- **Stacks 0E6K, the decomposition and part (1), over the statements of Stacks 0E0R (at
`i = 0`), 0E6B (a) and 0E1J.** For every `g ≥ 0`
* `Curves_g` is an open substack of `Curves`, contained in `Curves^{h0,1}`;
* the classifying morphism of a family of curves `f : X → S` factors through `Curves_g` exactly
  when `f_*𝒪_X = 𝒪_S` universally, the fibres of `f` have dimension `1`, and `R¹f_*𝒪_X` is
  locally free of rank `g` (part (1));
* over every family in `Curves^{h0,1}`, with base `S`, the loci of the `Curves_g` are open and
  closed subsets of `S` which are pairwise disjoint and cover `S`: `Curves^{h0,1} = ∐_g Curves_g`
  as open and closed substacks. -/
theorem curvesGenus_isOpenSubstack_and_factors_iff_and_decomposition_of_h01Statements
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
      (ObjectProperty.IsClosedUnderIsomorphisms (IsGenusCurveFamily B hZ g) ∧
        Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
          (curvesSubstackInclusion B hZ (IsGenusCurveFamily B hZ g)
            (isOpenCurvesLocus_isGenusCurveFamily_of_h01Statements hbetti hstruct h2 h3
              g).prop_of_hom).hom ∧
        Stack.IsOpenImmersion B integerBase hZ
          (curvesSubstackInclusion B hZ (IsGenusCurveFamily B hZ g)
            (isOpenCurvesLocus_isGenusCurveFamily_of_h01Statements hbetti hstruct h2 h3
              g).prop_of_hom)) ∧
      (∀ X : CurveFamily B hZ, IsGenusCurveFamily B hZ g X → IsH01CurveFamily B hZ X) ∧
      ∀ (U : BigFppfOver B integerBase hZ)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
        y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
        ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
            ObjectProperty.FullSubcategory (IsGenusCurveFamily B hZ g),
            z ⋙ ObjectProperty.ι (IsGenusCurveFamily B hZ g) = y) ↔
          IsGenusCurveFamily B hZ g (y.obj (Over.mk (𝟙 U.left))))) ∧
    ∀ G : CurveFamily B hZ, IsH01CurveFamily B hZ G →
      ∃ Ω : ℕ → Set (Space.points B integerBase hZ (schemeSpace G.base).obj),
        (∀ g, IsOpen (Ω g) ∧ IsClosed (Ω g)) ∧ Pairwise (fun g g' => Disjoint (Ω g) (Ω g')) ∧
          (⋃ g, Ω g) = Set.univ ∧
          ∀ (g : ℕ) (F : CurveFamily B hZ) (a : F ⟶ G),
            IsGenusCurveFamily B hZ g F ↔
              Set.range (Space.pointsMap B integerBase hZ (schemeSpace F.base).obj
                (schemeSpaceMap a.baseMap).hom) ⊆ Ω g :=
  ⟨fun g => ⟨isOpenImmersion_curvesSubstackInclusion
      (isOpenCurvesLocus_isGenusCurveFamily_of_h01Statements hbetti hstruct h2 h3 g),
    fun _ h => h.1,
    fun U y hy => factors_curvesSubstack_iff
      (isOpenCurvesLocus_isGenusCurveFamily_of_h01Statements hbetti hstruct h2 h3 g) U y hy⟩,
    curvesGenus_decomposition_of_h01Statements hbetti hstruct h2 h3⟩

end AlgebraicGeometry

end
