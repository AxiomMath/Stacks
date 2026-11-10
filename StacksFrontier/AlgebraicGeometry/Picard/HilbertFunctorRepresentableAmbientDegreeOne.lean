module

public import StacksFrontier.AlgebraicGeometry.NonAffineMorphism.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorOpenAmbient
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorRepresentableAmbientCharts
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorRepresentableAmbientRankOne
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertPointAddition

/-!
# Degree-one Hilbert families of the doubled affine line

Let `k` be a field, let `S = Spec k[y]` be the affine line and let `X` be the affine line with
its origin doubled, viewed as a scheme over `S` through the coordinate morphism. This file
computes the degree-one Hilbert functor of `X ⟶ S` on points: a degree-one family over a base
`T ⟶ S` exists exactly when the preimage in `T` of the punctured base is *clopen*, and in that
case there are the two families cut out by the graphs of the two charts.

## Main definitions

* `Stacks.Hilbert.doubledChartOver` — a chart of the doubled origin, as a morphism over `S`
  out of the terminal object `Over.mk (𝟙 S)` of `Over S`.
* `Stacks.Hilbert.doubledChartPoint` — the relative point of `X` over `T` given by a chart.
* `Stacks.Hilbert.doubledChartFamilyOpen` — the open of `X ×_S T` lying over a chart.
* `Stacks.Hilbert.doubledChartFamily` — the degree-one family cut out by the graph of a chart
  point, available once the preimage of the punctured base in `T` is empty.

## Main results

* `Stacks.Hilbert.isClosed_preimage_basicOpen_of_hilbertFamily` — if a degree-one Hilbert family
  of the doubled affine line exists over `T`, then the preimage in `T` of the punctured base is
  closed, hence clopen.
* `Stacks.Hilbert.isClosedImmersion_pointGraph_doubledChartPoint` — conversely, when that is
  empty the graph of a chart point is a closed immersion, so
  `Stacks.Hilbert.doubledChartFamily` is a degree-one Hilbert family.

## References

* [Stacks Project, Tag 0B9A](https://stacks.math.columbia.edu/tag/0B9A)
* [Stacks Project, Tag 01JD](https://stacks.math.columbia.edu/tag/01JD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Hilbert

/-! ### Generalities -/

/-- The structure morphism of `S ×_S T`, the base change of `𝟙 S` along `T ⟶ S`, is an
isomorphism. -/
instance isIso_structureMorphism_mkId {S : Scheme.{u}} (T : Over S) :
    IsIso ((Over.pullback T.hom).obj (Over.mk (𝟙 S))).hom :=
  (MorphismProperty.isomorphisms.iff _).mp
    (MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms Scheme)
      (IsPullback.of_hasPullback (𝟙 S) T.hom) (MorphismProperty.isomorphisms.infer_property _))

/-- An open set disjoint from a second open set and covering with it is that second one's
complement, hence closed. -/
private theorem isClosed_coe_of_inf_eq_bot_of_sup_eq_top {α : Type*} [TopologicalSpace α]
    (U V : Opens α) (hinf : U ⊓ V = ⊥) (hsup : U ⊔ V = ⊤) : IsClosed (U : Set α) := by
  have hinter : (U : Set α) ∩ (V : Set α) = ∅ := by rw [← Opens.coe_inf, hinf, Opens.coe_bot]
  have hunion : (U : Set α) ∪ (V : Set α) = Set.univ := by
    rw [← Opens.coe_sup, hsup, Opens.coe_top]
  have h : (U : Set α) = (V : Set α)ᶜ := by
    refine Set.Subset.antisymm (fun a ha hb ↦ ?_) fun a ha ↦ ?_
    · exact (Set.eq_empty_iff_forall_notMem.mp hinter a) ⟨ha, hb⟩
    · exact ((Set.mem_union a _ _).mp (hunion ▸ Set.mem_univ a)).resolve_right ha
  exact h ▸ V.isOpen.isClosed_compl

/-- The preimage of the punctured base is the preimage of the standard open of the coordinate. -/
private theorem preimage_puncturedAffineSpace_eq_preimage_basicOpen (k : Type u) [Field k]
    (T : Over (Spec (.of (MvPolynomial (Fin 1) k)))) :
    T.hom ⁻¹ᵁ puncturedAffineSpace k 1 =
      T.hom ⁻¹ᵁ PrimeSpectrum.basicOpen (MvPolynomial.X (0 : Fin 1)) := by
  rw [puncturedAffineSpace_one]

/-! ### The charts of the doubled origin as relative points -/

/-- The two charts of the doubled origin, as morphisms of schemes over the base. -/
def doubledChartOver (k : Type u) [Field k] (i : Fin 2) :
    Over.mk (𝟙 (Spec (.of (MvPolynomial (Fin 1) k)))) ⟶ Over.mk (coordinateMorphism k 1) :=
  Over.homMk (chartInclusion k 1 i) (by simpa using (coordinateMorphismData k 1).property i)

/-- The morphism of schemes underlying a chart viewed over the base is that chart. -/
@[simp]
theorem doubledChartOver_left (k : Type u) [Field k] (i : Fin 2) :
    (doubledChartOver k i).left = chartInclusion k 1 i :=
  rfl

/-- A chart of the doubled origin is an open immersion. -/
instance isOpenImmersion_doubledChartOver_left (k : Type u) [Field k] (i : Fin 2) :
    IsOpenImmersion (doubledChartOver k i).left :=
  inferInstanceAs (IsOpenImmersion (chartInclusion k 1 i))

/-- The relative point of the doubled origin given by a chart: the unique morphism to the
terminal object `Over.mk (𝟙 S)` of `Over S`, followed by that chart. -/
def doubledChartPoint (k : Type u) [Field k] (T : Over (Spec (.of (MvPolynomial (Fin 1) k))))
    (i : Fin 2) : T ⟶ Over.mk (coordinateMorphism k 1) :=
  Over.homMk T.hom ≫ doubledChartOver k i

/-- The morphism of schemes underlying a chart point is the structure morphism followed by the
chart. -/
@[simp]
theorem doubledChartPoint_left (k : Type u) [Field k]
    (T : Over (Spec (.of (MvPolynomial (Fin 1) k)))) (i : Fin 2) :
    (doubledChartPoint k T i).left = T.hom ≫ chartInclusion k 1 i :=
  rfl

/-- The open of `X ×_S T` lying over the `i`-th chart of the doubled origin. -/
def doubledChartFamilyOpen (k : Type u) [Field k] (T : Over (Spec (.of (MvPolynomial (Fin 1) k))))
    (i : Fin 2) :
    ((Over.pullback T.hom).obj (Over.mk (coordinateMorphism k 1))).left.Opens :=
  familyProjection (Over.mk (coordinateMorphism k 1)) T ⁻¹ᵁ (chartInclusion k 1 i).opensRange

/-- The image of `S ×_S T ⟶ X ×_S T` induced by a chart is the open lying over that chart. -/
theorem range_familyAmbientMap_doubledChartOver (k : Type u) [Field k]
    (T : Over (Spec (.of (MvPolynomial (Fin 1) k)))) (i : Fin 2) :
    Set.range (familyAmbientMap (doubledChartOver k i) T) =
      (doubledChartFamilyOpen k T i : Set _) :=
  range_familyAmbientMap (doubledChartOver k i) T

/-- The two opens lying over the two charts meet in the preimage of the punctured base. -/
theorem doubledChartFamilyOpen_inf (k : Type u) [Field k]
    (T : Over (Spec (.of (MvPolynomial (Fin 1) k)))) :
    doubledChartFamilyOpen k T 0 ⊓ doubledChartFamilyOpen k T 1 =
      ((Over.pullback T.hom).obj (Over.mk (coordinateMorphism k 1))).hom ⁻¹ᵁ
        (T.hom ⁻¹ᵁ puncturedAffineSpace k 1) := by
  have hfp := congrArg
    (fun f : ((Over.pullback T.hom).obj (Over.mk (coordinateMorphism k 1))).left ⟶
        Spec (.of (MvPolynomial (Fin 1) k)) => f ⁻¹ᵁ puncturedAffineSpace k 1)
    (familyProjection_comp (Over.mk (coordinateMorphism k 1)) T)
  simp only [Scheme.Hom.comp_preimage] at hfp
  have h : doubledChartFamilyOpen k T 0 ⊓ doubledChartFamilyOpen k T 1 =
      familyProjection (Over.mk (coordinateMorphism k 1)) T ⁻¹ᵁ
        ((chartInclusion k 1 0).opensRange ⊓ (chartInclusion k 1 1).opensRange) := rfl
  rw [h, ← preimage_puncturedAffineSpace_coordinateMorphism]
  exact hfp

/-- The two opens lying over the two charts cover `X ×_S T`. -/
theorem doubledChartFamilyOpen_sup (k : Type u) [Field k]
    (T : Over (Spec (.of (MvPolynomial (Fin 1) k)))) :
    doubledChartFamilyOpen k T 0 ⊔ doubledChartFamilyOpen k T 1 = ⊤ := by
  refine top_le_iff.mp fun x _ ↦ ?_
  have hx : familyProjection (Over.mk (coordinateMorphism k 1)) T x ∈
      ⨆ i : Fin 2, (chartInclusion k 1 i).opensRange := by
    rw [iSup_opensRange_chartInclusion]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · exact Or.inl hi
  · exact Or.inr hi

/-! ### A degree-one family forces the punctured locus to be clopen -/

/-- **A degree-one Hilbert family of the doubled affine line forces the preimage of the
punctured base to be clopen.** The preimage in `T` of the punctured base is always open; if a
degree-one Hilbert family of the doubled origin exists over `T`, it is also closed. -/
theorem isClosed_preimage_puncturedAffineSpace_of_hilbertFamily (k : Type u) [Field k]
    (T : Over (Spec (.of (MvPolynomial (Fin 1) k))))
    (Z : HilbertFamily (Over.mk (coordinateMorphism k 1)) T 1) :
    IsClosed ((T.hom ⁻¹ᵁ puncturedAffineSpace k 1 : T.left.Opens) : Set T.left) := by
  have hiso : IsIso Z.structural :=
    Stacks.Morphisms.isIso_of_isFiniteLocallyFreeOfRank_one Z.structural
      Z.isFiniteLocallyFreeOfRank_structural
  have hstr : ∀ z : Z.ideal.subscheme,
      ((Over.pullback T.hom).obj (Over.mk (coordinateMorphism k 1))).hom
        (Z.ideal.subschemeι z) = Z.structural z := fun z ↦
    (Scheme.Hom.comp_apply _ _ z).symm
  have hmq : ∀ (i : Fin 2) (w : ((Over.pullback T.hom).obj
      (Over.mk (𝟙 (Spec (.of (MvPolynomial (Fin 1) k)))))).left),
      ((Over.pullback T.hom).obj (Over.mk (coordinateMorphism k 1))).hom
        (familyAmbientMap (doubledChartOver k i) T w) =
      ((Over.pullback T.hom).obj
        (Over.mk (𝟙 (Spec (.of (MvPolynomial (Fin 1) k)))))).hom w := fun i w ↦ by
    have h := congrArg (fun g : ((Over.pullback T.hom).obj
        (Over.mk (𝟙 (Spec (.of (MvPolynomial (Fin 1) k)))))).left ⟶ T.left => g w)
      (familyAmbientMap_comp_hom (doubledChartOver k i) T)
    simpa [Scheme.Hom.comp_apply] using h
  have hcoord : ∀ w : ((Over.pullback T.hom).obj (Over.mk (coordinateMorphism k 1))).left,
      coordinateMorphism k 1 (familyProjection (Over.mk (coordinateMorphism k 1)) T w) =
        T.hom (((Over.pullback T.hom).obj (Over.mk (coordinateMorphism k 1))).hom w) := fun w ↦ by
    have h := congrArg (fun g : ((Over.pullback T.hom).obj
        (Over.mk (coordinateMorphism k 1))).left ⟶ Spec (.of (MvPolynomial (Fin 1) k)) => g w)
      (familyProjection_comp (Over.mk (coordinateMorphism k 1)) T)
    simpa [Scheme.Hom.comp_apply] using h
  have hclosed : ∀ i : Fin 2, IsClosed (Z.structural ''
      (Z.ideal.subschemeι ⁻¹' (doubledChartFamilyOpen k T i : Set _))) := by
    intro i
    have hrange := range_familyAmbientMap_doubledChartOver k T i
    have himage : Z.structural '' (Z.ideal.subschemeι ⁻¹' (doubledChartFamilyOpen k T i : Set _)) =
        ((Over.pullback T.hom).obj
          (Over.mk (𝟙 (Spec (.of (MvPolynomial (Fin 1) k)))))).hom ''
          (familyAmbientMap (doubledChartOver k i) T ⁻¹' Set.range Z.ideal.subschemeι) := by
      refine Set.Subset.antisymm ?_ ?_
      · rintro _ ⟨z, hz, rfl⟩
        have hz' : Z.ideal.subschemeι z ∈
            Set.range (familyAmbientMap (doubledChartOver k i) T) := by rw [hrange]; exact hz
        obtain ⟨w, hw⟩ := hz'
        exact ⟨w, ⟨z, hw.symm⟩, by rw [← hmq i w, hw, hstr z]⟩
      · rintro _ ⟨w, ⟨z, hz⟩, rfl⟩
        refine ⟨z, ?_, ?_⟩
        · rw [← hrange]; exact ⟨w, hz.symm⟩
        · rw [← hstr z, hz, hmq i w]
    rw [himage]
    have hζ : IsClosed (Set.range Z.ideal.subschemeι) :=
      Z.ideal.range_subschemeι ▸ Z.ideal.support.isClosed
    exact ((Over.pullback T.hom).obj
      (Over.mk (𝟙 (Spec (.of (MvPolynomial (Fin 1) k)))))).hom.homeomorph.isClosedMap _
      (hζ.preimage (familyAmbientMap (doubledChartOver k i) T).continuous)
  have hkey : ((T.hom ⁻¹ᵁ puncturedAffineSpace k 1 : T.left.Opens) : Set T.left) =
      (Z.structural '' (Z.ideal.subschemeι ⁻¹' (doubledChartFamilyOpen k T 0 : Set _))) ∩
        (Z.structural '' (Z.ideal.subschemeι ⁻¹' (doubledChartFamilyOpen k T 1 : Set _))) := by
    refine Set.Subset.antisymm (fun t ht ↦ ?_) ?_
    · obtain ⟨z, rfl⟩ := Z.structural.homeomorph.surjective t
      have hbase : T.hom (Z.structural z) ∈ puncturedAffineSpace k 1 := ht
      have hmem : familyProjection (Over.mk (coordinateMorphism k 1)) T
          (Z.ideal.subschemeι z) ∈
          coordinateMorphism k 1 ⁻¹ᵁ puncturedAffineSpace k 1 := by
        change coordinateMorphism k 1 (familyProjection (Over.mk (coordinateMorphism k 1)) T
          (Z.ideal.subschemeι z)) ∈ puncturedAffineSpace k 1
        rw [hcoord (Z.ideal.subschemeι z), hstr z]
        exact hbase
      rw [preimage_puncturedAffineSpace_coordinateMorphism] at hmem
      exact ⟨⟨z, hmem.1, rfl⟩, ⟨z, hmem.2, rfl⟩⟩
    · rintro t ⟨⟨z₀, hz₀, hz₀'⟩, ⟨z₁, hz₁, hz₁'⟩⟩
      have hzz : z₀ = z₁ := Z.structural.homeomorph.injective (hz₀'.trans hz₁'.symm)
      rw [← hzz] at hz₁
      have hmem : familyProjection (Over.mk (coordinateMorphism k 1)) T
          (Z.ideal.subschemeι z₀) ∈
          (chartInclusion k 1 0).opensRange ⊓ (chartInclusion k 1 1).opensRange := ⟨hz₀, hz₁⟩
      rw [← preimage_puncturedAffineSpace_coordinateMorphism] at hmem
      change T.hom t ∈ puncturedAffineSpace k 1
      rw [← hz₀', ← hstr z₀, ← hcoord (Z.ideal.subschemeι z₀)]
      exact hmem
  rw [hkey]
  exact (hclosed 0).inter (hclosed 1)

/-- **A degree-one Hilbert family of the doubled affine line forces the preimage of the standard
open of the coordinate to be clopen.** If a degree-one Hilbert family of the doubled origin exists
over `T`, the preimage in `T` of the standard open of the single coordinate is closed. -/
theorem isClosed_preimage_basicOpen_of_hilbertFamily (k : Type u) [Field k]
    (T : Over (Spec (.of (MvPolynomial (Fin 1) k))))
    (Z : HilbertFamily (Over.mk (coordinateMorphism k 1)) T 1) :
    IsClosed ((T.hom ⁻¹ᵁ PrimeSpectrum.basicOpen (MvPolynomial.X (0 : Fin 1)) : T.left.Opens) :
      Set T.left) := by
  rw [← preimage_puncturedAffineSpace_eq_preimage_basicOpen]
  exact isClosed_preimage_puncturedAffineSpace_of_hilbertFamily k T Z

/-! ### The two chart families over a base with empty punctured locus -/

/-- When the preimage of the punctured base is empty, the image of the comparison morphism of a
chart is closed. -/
theorem isClosed_range_familyAmbientMap_doubledChartOver (k : Type u) [Field k]
    (T : Over (Spec (.of (MvPolynomial (Fin 1) k))))
    (hT : (T.hom ⁻¹ᵁ PrimeSpectrum.basicOpen (MvPolynomial.X (0 : Fin 1)) : T.left.Opens) = ⊥)
    (i : Fin 2) : IsClosed (Set.range (familyAmbientMap (doubledChartOver k i) T)) := by
  have hT' := (preimage_puncturedAffineSpace_eq_preimage_basicOpen k T).trans hT
  have hinf : doubledChartFamilyOpen k T 0 ⊓ doubledChartFamilyOpen k T 1 = ⊥ := by
    rw [doubledChartFamilyOpen_inf, hT']
    exact Opens.ext (by simp)
  rw [range_familyAmbientMap_doubledChartOver]
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · exact isClosed_coe_of_inf_eq_bot_of_sup_eq_top _ (doubledChartFamilyOpen k T 1) hinf
      (doubledChartFamilyOpen_sup k T)
  · exact isClosed_coe_of_inf_eq_bot_of_sup_eq_top _ (doubledChartFamilyOpen k T 0)
      (by rw [inf_comm]; exact hinf) (by rw [sup_comm]; exact doubledChartFamilyOpen_sup k T)

/-- When the preimage of the punctured base is empty, the comparison morphism
`S ×_S T ⟶ X ×_S T` of a chart is a closed immersion. -/
theorem isClosedImmersion_familyAmbientMap_doubledChartOver (k : Type u) [Field k]
    (T : Over (Spec (.of (MvPolynomial (Fin 1) k))))
    (hT : (T.hom ⁻¹ᵁ PrimeSpectrum.basicOpen (MvPolynomial.X (0 : Fin 1)) : T.left.Opens) = ⊥)
    (i : Fin 2) : IsClosedImmersion (familyAmbientMap (doubledChartOver k i) T) :=
  IsClosedImmersion.of_isPreimmersion _ (isClosed_range_familyAmbientMap_doubledChartOver k T hT i)

/-- The comparison morphism of a chart is the structure morphism of `S ×_S T` followed by the
graph of the chart point. -/
theorem familyAmbientMap_doubledChartOver_eq (k : Type u) [Field k]
    (T : Over (Spec (.of (MvPolynomial (Fin 1) k)))) (i : Fin 2) :
    familyAmbientMap (doubledChartOver k i) T =
      ((Over.pullback T.hom).obj (Over.mk (𝟙 (Spec (.of (MvPolynomial (Fin 1) k)))))).hom ≫
        pointGraph (Over.mk (coordinateMorphism k 1)) T (doubledChartPoint k T i) := by
  have hcond : familyProjection (Over.mk (𝟙 (Spec (.of (MvPolynomial (Fin 1) k))))) T =
      ((Over.pullback T.hom).obj (Over.mk (𝟙 (Spec (.of (MvPolynomial (Fin 1) k)))))).hom ≫
        T.hom :=
    (Category.comp_id _).symm.trans
      (familyProjection_comp (Over.mk (𝟙 (Spec (.of (MvPolynomial (Fin 1) k))))) T)
  have hmfst : familyAmbientMap (doubledChartOver k i) T ≫
      pullback.fst (Over.mk (coordinateMorphism k 1)).hom T.hom =
      ((Over.pullback T.hom).obj (Over.mk (𝟙 (Spec (.of (MvPolynomial (Fin 1) k)))))).hom ≫
        T.hom ≫ chartInclusion k 1 i := by
    have h1 : familyAmbientMap (doubledChartOver k i) T ≫
        pullback.fst (Over.mk (coordinateMorphism k 1)).hom T.hom =
        familyProjection (Over.mk (𝟙 (Spec (.of (MvPolynomial (Fin 1) k))))) T ≫
          chartInclusion k 1 i :=
      familyAmbientMap_comp_fst (doubledChartOver k i) T
    rw [h1, hcond, Category.assoc]
  have hmsnd : familyAmbientMap (doubledChartOver k i) T ≫
      pullback.snd (Over.mk (coordinateMorphism k 1)).hom T.hom =
      ((Over.pullback T.hom).obj (Over.mk (𝟙 (Spec (.of (MvPolynomial (Fin 1) k)))))).hom :=
    familyAmbientMap_comp_hom (doubledChartOver k i) T
  refine pullback.hom_ext ?_ ?_
  · rw [hmfst, Category.assoc, pointGraph_comp_fst, doubledChartPoint_left]
  · rw [hmsnd, Category.assoc, pointGraph_comp_snd, Category.comp_id]

/-- **The graph of a chart point is a closed immersion** when the preimage of the punctured base
in `T` is empty. -/
theorem isClosedImmersion_pointGraph_doubledChartPoint (k : Type u) [Field k]
    (T : Over (Spec (.of (MvPolynomial (Fin 1) k))))
    (hT : (T.hom ⁻¹ᵁ PrimeSpectrum.basicOpen (MvPolynomial.X (0 : Fin 1)) : T.left.Opens) = ⊥)
    (i : Fin 2) :
    IsClosedImmersion
      (pointGraph (Over.mk (coordinateMorphism k 1)) T (doubledChartPoint k T i)) := by
  have := isClosedImmersion_familyAmbientMap_doubledChartOver k T hT i
  have h : inv ((Over.pullback T.hom).obj
          (Over.mk (𝟙 (Spec (.of (MvPolynomial (Fin 1) k)))))).hom ≫
        familyAmbientMap (doubledChartOver k i) T =
      pointGraph (Over.mk (coordinateMorphism k 1)) T (doubledChartPoint k T i) := by
    rw [IsIso.inv_comp_eq]
    exact familyAmbientMap_doubledChartOver_eq k T i
  rw [← h]
  infer_instance

/-- **The two degree-one Hilbert families of the doubled affine line** over a base whose
preimage of the punctured base is empty: the graphs of the two chart points. -/
def doubledChartFamily (k : Type u) [Field k] (T : Over (Spec (.of (MvPolynomial (Fin 1) k))))
    (hT : (T.hom ⁻¹ᵁ PrimeSpectrum.basicOpen (MvPolynomial.X (0 : Fin 1)) : T.left.Opens) = ⊥)
    (i : Fin 2) : HilbertFamily (Over.mk (coordinateMorphism k 1)) T 1 where
  ideal := pointIdeal (Over.mk (coordinateMorphism k 1)) T (doubledChartPoint k T i)
  isFiniteLocallyFreeOfRank :=
    haveI := isClosedImmersion_pointGraph_doubledChartPoint k T hT i
    isFiniteLocallyFreeOfRank_pointIdeal (Over.mk (coordinateMorphism k 1)) T
      (doubledChartPoint k T i)

end Stacks.Hilbert

end
