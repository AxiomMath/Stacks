module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FibreDimension.AffineComponents
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Support
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ExtendedIntegers
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralGoodSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.InverseImageDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.TrivialRestrictionGysin
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionZeroPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionZeroCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Specializations
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.LocalRingDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback

/-!
# The δ-dimension of a flat inverse image

In Situation 0EDT let `X/B` and `Y/B` be good and let `f : X ⟶ Y` be a morphism over the base
which is flat of relative dimension `r`. Along such an `f` the δ-dimension of a closed set of
points grows by exactly `r`, and each irreducible component of the inverse image of an integral
closed subspace `Z ⊆ Y` dominates `Z` and has δ-dimension `dim_δ(Z) + r`. This is Stacks 0EP5;
Stacks 0EPB gives the inequality `≤`.

## Main results

* `deltaDimensionClosed_eq_biSup`: the δ-dimension of a closed set of points is the supremum of
  the induced dimension function over all of its points.
* `IntegralClosedSubspace.isGenericPoint_pointsMap_of_isGenericPoint_of_isFlat`: along a flat
  morphism a generic point of a component of the inverse image of an integral closed subspace is
  carried to the generic point of the set of points of that subspace.
* `IntegralClosedSubspace.closure_image_subspacePointSet_preimageComponent_of_isFlat`: such a
  component dominates the subspace (Stacks 0EP5).
* `IntegralClosedSubspace.deltaDimension_preimageComponent_of_isFlat`: the δ-dimension of such a
  component is `dim_δ(Z) + r` (Stacks 0EP5).
* `deltaDimensionClosed_preimage_eq_iSup_add`: the δ-dimension of the inverse image of a closed
  set of points `T` is `r` more than the supremum of the δ-dimensions of the irreducible
  components of `T` which `f` meets (Stacks 0EP5).

## Implementation notes

The components of `f^{-1}(Z)` are indexed as in Stacks 0EE5, by `irreducibleComponents` of its
set of points, and taken as integral closed subspaces of `X` through
`AlgebraicGeometry.Space.IntegralClosedSubspace.preimageComponent`.

## References

* [Stacks Project, Tag 0EP5](https://stacks.math.columbia.edu/tag/0EP5)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDN](https://stacks.math.columbia.edu/tag/0EDN)
* [Stacks Project, Tag 0EDX](https://stacks.math.columbia.edu/tag/0EDX)
* [Stacks Project, Tag 0ENF](https://stacks.math.columbia.edu/tag/0ENF)
* [Stacks Project, Tag 0EPB](https://stacks.math.columbia.edu/tag/0EPB)
* [Stacks Project, Tag 0EPY](https://stacks.math.columbia.edu/tag/0EPY)
* [Stacks Project, Tag 04NQ](https://stacks.math.columbia.edu/tag/04NQ)
* [Stacks Project, Tag 04NR](https://stacks.math.columbia.edu/tag/04NR)
* [Stacks Project, Tag 04NS](https://stacks.math.columbia.edu/tag/04NS)
* [Stacks Project, Tag 0ABV](https://stacks.math.columbia.edu/tag/0ABV)
* [Stacks Project, Tag 0B7W](https://stacks.math.columbia.edu/tag/0B7W)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The local ring of a fibre at a point where the local ring of the source has Krull dimension
zero has Krull dimension zero. -/
private theorem ringKrullDim_fiber_stalk_eq_zero_of_source_eq_zero
    {Z W : Scheme.{u}} (h : Z ⟶ W) (z : Z)
    (hzero : ringKrullDim (Z.presheaf.stalk z) = 0) :
    ringKrullDim ((h.fiber (h z)).presheaf.stalk (h.asFiber z)) = 0 := by
  let w := h.asFiber z
  have hz : (h.fiberι (h z)) w = z := Scheme.Hom.fiberι_asFiber h z
  let c : Z.presheaf.stalk z ⟶ Z.presheaf.stalk ((h.fiberι (h z)) w) :=
    (Z.presheaf.stalkCongr (.of_eq hz.symm)).hom
  let i := ((h.fiberι (h z)).stalkMap w).hom.comp c.hom
  have hi : Function.Surjective i :=
    ((h.fiberι (h z)).stalkMap_surjective w).comp
      (ConcreteCategory.bijective_of_isIso c).2
  exact le_antisymm ((ringKrullDim_le_of_surjective i hi).trans (le_of_eq hzero))
    ringKrullDim_nonneg_of_nontrivial

namespace Space

attribute [local instance] pointTopology

/-! ### Generic points of the components of a closed subset -/

/-- A point of a closed subset of a space which is generic for the image of a closed subset of
the subspace is, as a point of the subspace, generic for that subset. -/
private theorem isGenericPoint_subtype_of_isGenericPoint_image {α : Type*}
    [TopologicalSpace α] {A : Set α} {C : Set A} (hC : IsClosed C) {x : α} (hxA : x ∈ A)
    (hx : IsGenericPoint x (Subtype.val '' C)) : IsGenericPoint (⟨x, hxA⟩ : A) C := by
  have hmem : (⟨x, hxA⟩ : A) ∈ C := by
    obtain ⟨c, hc, hcx⟩ : x ∈ Subtype.val '' C := hx ▸ subset_closure rfl
    exact (Subtype.ext hcx : c = (⟨x, hxA⟩ : A)) ▸ hc
  refine Set.Subset.antisymm (hC.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hmem)) ?_
  intro c hc
  rw [closure_subtype]
  have hcx : (c : α) ∈ Subtype.val '' C := ⟨c, hc, rfl⟩
  rw [← hx] at hcx
  simpa using hcx

/-- An irreducible component of a closed subset of a space is closed in the space. -/
private theorem isClosed_image_val_of_mem_irreducibleComponents {α : Type*}
    [TopologicalSpace α] {A : Set α} (hA : IsClosed A) {C : Set A}
    (hC : C ∈ irreducibleComponents A) : IsClosed (Subtype.val '' C) :=
  hA.isClosedEmbedding_subtypeVal.isClosedMap _ (isClosed_of_mem_irreducibleComponents _ hC)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- At a generic point of an irreducible component of the space of points of a decent algebraic
space the local ring of the fibre of any morphism out of it has dimension zero. -/
theorem hasFiberLocalRingDimension_zero_of_mem_genericPoints
    (hP : IsAlgebraicSpace B S hS P) (hQ : IsAlgebraicSpace B S hS Q)
    (hPdec : IsDecentSpace B S hS P) (p : P ⟶ Q) (w : points B S hS P)
    (hw : w ∈ genericPoints (points B S hS P)) :
    HasFiberLocalRingDimension 0 B S hS hP hQ p w := by
  have hdim : localRingDimension B S hS w = 0 :=
    (mem_genericPoints_iff_localRingDimension_eq_zero B S hS hP hPdec w).mp hw
  have hall := (localRingDimension_eq_zero_iff_all_etale_genericPoints B S hS hP w).mp hdim
  intro c
  let U := (BigFppfOver.toScheme B S hS).obj c.U
  let V := (BigFppfOver.toScheme B S hS).obj c.V
  let u := c.sourcePoint B S hS
  let h := (BigFppfOver.toScheme B S hS).map c.h
  have hchartpoint : ChartPoint B S hS c.U c.a u w :=
    ⟨c.representative, congrArg ((BigFppfOver.toScheme B S hS).map c.representative.value)
      (Subsingleton.elim _ c.point), c.maps_to⟩
  have hu : u ∈ genericPoints U :=
    hall c.U c.a u ((isEtale_iff_presheaf_of_yoneda B S hS c.a).mpr c.a_etale) hchartpoint
  have hzero : ringKrullDim (U.presheaf.stalk u) = 0 :=
    (ringKrullDim_stalk_eq_zero_iff_mem_genericPoints U u).2 hu
  let z : (⊤ : U.Opens).toScheme := ⟨u, by simp⟩
  have hzero' : ringKrullDim (((⊤ : U.Opens).toScheme).presheaf.stalk z) = 0 :=
    (AlgebraicGeometry.ringKrullDim_stalk_eq_of_etale U.topIso.hom z).trans hzero
  have hfiber := ringKrullDim_fiber_stalk_eq_zero_of_source_eq_zero
    (U.topIso.hom ≫ h) z hzero'
  change ∃ g : AlgebraicGeometry.MorphismOfGerms.Representative ⟨U, u⟩ ⟨V, h u⟩,
    AlgebraicGeometry.MorphismOfGerms.mk g =
      AlgebraicGeometry.MorphismOfGerms.ofSchemeHom h u ∧
    ringKrullDim ((g.hom.fiber (g.hom ⟨u, g.mem_source⟩)).presheaf.stalk
      (g.hom.asFiber ⟨u, g.mem_source⟩)) = 0
  let rep : AlgebraicGeometry.MorphismOfGerms.Representative ⟨U, u⟩ ⟨V, h u⟩ :=
    { source := ⊤
      mem_source := by simp
      hom := U.topIso.hom ≫ h
      map_point := by rfl }
  exact ⟨rep, rfl, hfiber⟩

end Space

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-! ### Dominance of the components of a flat inverse image -/

/-- Let `f : X ⟶ Y` be a flat morphism of good algebraic spaces over the base and let `Z ⊆ Y` be
an integral closed subspace. A generic point of an irreducible component of the inverse image of
`Z` is carried by `f` to the generic point of the set of points of `Z`. -/
theorem IntegralClosedSubspace.isGenericPoint_pointsMap_of_isGenericPoint_of_isFlat
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) {f : X ⟶ Y}
    (hf : IsFlat D.site D.base D.base_mem f)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (C : irreducibleComponents (Z.preimagePointSet D.site D.base D.base_mem f))
    (x : points D.site D.base D.base_mem X)
    (hx : IsGenericPoint x (subspacePointSet D.site D.base D.base_mem X
      (Z.preimageComponent D.site D.base D.base_mem f hX.1
        (D.isDecentSpace_of_isGood sX hX) hY.1 C).subspace)) :
    IsGenericPoint (pointsMap D.site D.base D.base_mem X f x)
      (subspacePointSet D.site D.base D.base_mem Y Z.subspace) := by
  have hT0 : T0Space (points D.site D.base D.base_mem X) :=
    t0Space_points_of_isDecentSpace D.site D.base D.base_mem hX.1
      (D.isDecentSpace_of_isGood sX hX)
  rw [Z.subspacePointSet_preimageComponent D.site D.base D.base_mem f hX.1
    (D.isDecentSpace_of_isGood sX hX) hY.1 C] at hx
  have hxA : x ∈ Z.preimagePointSet D.site D.base D.base_mem f := by
    exact Subtype.coe_image_subset _ _ hx.mem
  have hη := isGenericPoint_pointsMap_genericPoint D.site D.base D.base_mem hY.1 Z
  have hspec : pointsMap D.site D.base D.base_mem Z.subspace.toFunctor Z.subspace.ι
      (Z.genericPoint D.site D.base D.base_mem) ⤳ pointsMap D.site D.base D.base_mem X f x :=
    hη.specializes hxA
  obtain ⟨x', hx'spec, hx'map⟩ := exists_specializes_pointsMap_eq_of_isFlat
    D.site D.base D.base_mem hX.1 hY.1 f hf hspec
    (fun V hV ψ hψ => hasFiniteChartFibersAtEveryPoint_of_isDecentSpace D.site D.base D.base_mem
      (D.isDecentSpace_of_isGood sY hY) _ V hV ψ hψ) x rfl
  have hx'A : x' ∈ Z.preimagePointSet D.site D.base D.base_mem f := by
    change pointsMap D.site D.base D.base_mem X f x' ∈
      subspacePointSet D.site D.base D.base_mem Y Z.subspace
    rw [hx'map]
    exact ⟨Z.genericPoint D.site D.base D.base_mem, rfl⟩
  rwa [← Stacks.Chow.eq_of_specializes_of_isGenericPoint_component C.2 hx hx'A hx'spec, hx'map]

/-! ### The δ-dimension of a closed set as a supremum over its points -/

/-- The δ-dimension of a closed set of points of a good algebraic space is the supremum of the
induced dimension function over all of its points, not only over the generic points of its
irreducible components. -/
theorem deltaDimensionClosed_eq_biSup (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (T : Set (points D.site D.base D.base_mem X)) (hT : IsClosed T) :
    deltaDimensionClosed D sX hX T hT =
      ⨆ t ∈ T, ((inducedDimensionValue D.site D.base D.base_mem D.delta sX t : ℤ) : EInt) := by
  have _hsober : QuasiSober (points D.site D.base D.base_mem X) :=
    quasiSober_points_of_isGood D sX hX
  have _hTsober : QuasiSober T := hT.isClosedEmbedding_subtypeVal.quasiSober
  have hval : deltaDimensionClosed D sX hX T hT =
      ⨆ Z : irreducibleComponents T,
        (inducedDimensionValue D.site D.base D.base_mem D.delta sX Z.2.1.genericPoint.1 :
          EInt) := rfl
  have hanti : ∀ ⦃x y : points D.site D.base D.base_mem X⦄, x ⤳ y → x ≠ y →
      inducedDimensionValue D.site D.base D.base_mem D.delta sX y <
        inducedDimensionValue D.site D.base D.base_mem D.delta sX x :=
    lt_inducedDimensionValue_of_specializes D.site D.base D.base_mem hX.1
      (D.isDecentSpace_of_isGood sX hX) D.isAlgebraicSpace
      (isDecentSpace_of_isAbsolutelyQuasiSeparated D.site D.base D.base_mem D.space
        D.isAlgebraicSpace D.quasiSeparated)
      D.locallyNoetherian D.universallyCatenary D.delta sX hX.2.2
  rw [hval]
  refine le_antisymm (iSup_le fun Z => ?_) (iSup_le fun t => iSup_le fun ht => ?_)
  · exact le_iSup₂_of_le Z.2.1.genericPoint.1 Z.2.1.genericPoint.2 le_rfl
  · obtain ⟨W, hW, hsub⟩ :=
      exists_mem_irreducibleComponents_subset_of_isIrreducible
        (closure ({(⟨t, ht⟩ : T)} : Set T))
        (isIrreducible_iff_closure.mpr isIrreducible_singleton)
    have hη : IsGenericPoint hW.1.genericPoint W := by
      simpa [isClosed_of_mem_irreducibleComponents W hW] using
        hW.1.isGenericPoint_genericPoint_closure
    refine le_iSup_of_le (⟨W, hW⟩ : irreducibleComponents T) ?_
    by_cases hηt : hW.1.genericPoint = (⟨t, ht⟩ : T)
    · rw [show t = (hW.1.genericPoint : T).1 from by rw [hηt]]
    · have hlt : inducedDimensionValue D.site D.base D.base_mem D.delta sX t <
          inducedDimensionValue D.site D.base D.base_mem D.delta sX hW.1.genericPoint.1 :=
        hanti ((hη.specializes (hsub (subset_closure rfl))).map continuous_subtype_val)
          (fun h => hηt (Subtype.ext h))
      exact WithBotTop.coe_le_coe.mpr hlt.le

/-- The δ-dimension of a closed set depends only on the set. -/
theorem deltaDimensionClosed_congr (sX : X ⟶ D.space) (hX : D.IsGood sX)
    {T U : Set (points D.site D.base D.base_mem X)} (h : T = U) (hT : IsClosed T)
    (hU : IsClosed U) :
    deltaDimensionClosed D sX hX T hT = deltaDimensionClosed D sX hX U hU := by
  subst h
  rfl

/-- The δ-dimension of a closed set covered by a family of closed sets is the supremum of their
δ-dimensions. -/
theorem deltaDimensionClosed_eq_iSup_of_iUnion {ι : Type*} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (T : Set (points D.site D.base D.base_mem X)) (hT : IsClosed T)
    (S : ι → Set (points D.site D.base D.base_mem X)) (hS : ∀ i, IsClosed (S i))
    (hcover : T = ⋃ i, S i) :
    deltaDimensionClosed D sX hX T hT = ⨆ i, deltaDimensionClosed D sX hX (S i) (hS i) := by
  rw [deltaDimensionClosed_eq_biSup D sX hX T hT]
  simp only [deltaDimensionClosed_eq_biSup D sX hX _ (hS _)]
  rw [hcover, iSup_iUnion]

/-! ### Dominance -/

/-- Let `f : X ⟶ Y` be a flat morphism of good algebraic spaces over the base and let `Z ⊆ Y` be
an integral closed subspace. An irreducible component `Z'` of `f^{-1}(Z)` dominates `Z`: the
closure of the image of `|Z'|` is `|Z|`. -/
@[stacks 0EP5 "a component of the inverse image of an integral closed subspace dominates it"]
theorem IntegralClosedSubspace.closure_image_subspacePointSet_preimageComponent_of_isFlat
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) {f : X ⟶ Y}
    (hflat : IsFlat D.site D.base D.base_mem f)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (C : irreducibleComponents (Z.preimagePointSet D.site D.base D.base_mem f)) :
    closure (pointsMap D.site D.base D.base_mem X f ''
        subspacePointSet D.site D.base D.base_mem X
          (Z.preimageComponent D.site D.base D.base_mem f hX.1
            (D.isDecentSpace_of_isGood sX hX) hY.1 C).subspace) =
      subspacePointSet D.site D.base D.base_mem Y Z.subspace := by
  have hgenξ := isGenericPoint_pointsMap_genericPoint D.site D.base D.base_mem hX.1
    (Z.preimageComponent D.site D.base D.base_mem f hX.1
      (D.isDecentSpace_of_isGood sX hX) hY.1 C)
  have hdom := Z.isGenericPoint_pointsMap_of_isGenericPoint_of_isFlat D sX hX sY hY hflat C _
    hgenξ
  refine Set.Subset.antisymm (closure_minimal ?_
    (isClosed_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem hY.1 Z)) ?_
  · rintro y ⟨x, hxW, rfl⟩
    rw [Z.subspacePointSet_preimageComponent D.site D.base D.base_mem f hX.1
      (D.isDecentSpace_of_isGood sX hX) hY.1 C] at hxW
    obtain ⟨c, -, hc⟩ := hxW
    exact hc ▸ c.2
  · rw [← hdom]
    exact closure_mono (Set.singleton_subset_iff.mpr
      ⟨_, ⟨(Z.preimageComponent D.site D.base D.base_mem f hX.1
        (D.isDecentSpace_of_isGood sX hX) hY.1 C).genericPoint D.site D.base D.base_mem, rfl⟩,
        rfl⟩)

/-! ### The dimension of the local ring of the fibre at such a generic point -/

/-- The local ring of the fibre of `f : X ⟶ Y` has dimension zero at a generic point of an
irreducible component of the inverse image of an integral closed subspace `Z ⊆ Y`. -/
private theorem hasFiberLocalRingDimension_zero_of_isGenericPoint_preimageComponent
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) {f : X ⟶ Y}
    (hfft : IsLocallyOfFiniteType D.site D.base D.base_mem f)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (C : irreducibleComponents (Z.preimagePointSet D.site D.base D.base_mem f))
    (x : points D.site D.base D.base_mem X)
    (hx : IsGenericPoint x
      (Subtype.val '' (C : Set (Z.preimagePointSet D.site D.base D.base_mem f)))) :
    HasFiberLocalRingDimension 0 D.site D.base D.base_mem hX.1 hY.1 f x := by
  have hPclosed : IsClosedSubspace D.site D.base D.base_mem (Z.subspace.preimage f) :=
    IntegralClosedSubspace.isClosedSubspace_preimage D.site D.base D.base_mem f hX.1 hY.1 Z
  have hrange : Set.range (pointsMap D.site D.base D.base_mem
      (Z.subspace.preimage f).toFunctor (Z.subspace.preimage f).ι) =
      Z.preimagePointSet D.site D.base D.base_mem f :=
    subspacePointSet_preimage D.site D.base D.base_mem f Z.subspace
  have hxA : x ∈ Z.preimagePointSet D.site D.base D.base_mem f := by
    exact Subtype.coe_image_subset _ _ hx.mem
  obtain ⟨w, hw⟩ : x ∈ Set.range (pointsMap D.site D.base D.base_mem
      (Z.subspace.preimage f).toFunctor (Z.subspace.preimage f).ι) := hrange ▸ hxA
  have hemb : Topology.IsEmbedding (pointsMap D.site D.base D.base_mem
      (Z.subspace.preimage f).toFunctor (Z.subspace.preimage f).ι) :=
    isEmbedding_pointsMap_of_isImmersion D.site D.base D.base_mem hX.1
      (Z.subspace.preimage f).ι
      (isImmersion_of_isClosedImmersion D.site D.base D.base_mem hPclosed.2)
  let e : points D.site D.base D.base_mem (Z.subspace.preimage f).toFunctor ≃ₜ
      Z.preimagePointSet D.site D.base D.base_mem f :=
    hemb.toHomeomorph.trans (Homeomorph.setCongr hrange)
  have hew : e w = (⟨x, hxA⟩ : Z.preimagePointSet D.site D.base D.base_mem f) := Subtype.ext hw
  have hgenA : IsGenericPoint (⟨x, hxA⟩ : Z.preimagePointSet D.site D.base D.base_mem f)
      (C : Set (Z.preimagePointSet D.site D.base D.base_mem f)) :=
    isGenericPoint_subtype_of_isGenericPoint_image
      (isClosed_of_mem_irreducibleComponents _ C.2) hxA hx
  have hWP : e.symm '' (C : Set (Z.preimagePointSet D.site D.base D.base_mem f)) ∈
      irreducibleComponents (points D.site D.base D.base_mem
        (Z.subspace.preimage f).toFunctor) :=
    Homeomorph.image_mem_irreducibleComponents e.symm C.2
  have hgenw : IsGenericPoint w
      (e.symm '' (C : Set (Z.preimagePointSet D.site D.base D.base_mem f))) := by
    have h := hgenA.image e.symm.continuous
    rwa [← hew, Homeomorph.symm_apply_apply,
      (isClosed_of_mem_irreducibleComponents _ hWP).closure_eq] at h
  have hwgen : w ∈ genericPoints (points D.site D.base D.base_mem
      (Z.subspace.preimage f).toFunctor) := by
    change closure {w} ∈ irreducibleComponents _
    rw [hgenw.def]
    exact hWP
  have hPdec : IsDecentSpace D.site D.base D.base_mem (Z.subspace.preimage f).toFunctor :=
    D.isDecentSpace_of_isGood ((Z.subspace.preimage f).ι ≫ sX)
      (isGood_closedSubspace (D := D) (p := sX) (hp := hX)
        (E := ⟨Z.subspace.preimage f, hPclosed⟩))
  have hfib0 := hasFiberLocalRingDimension_zero_of_mem_genericPoints D.site D.base D.base_mem
    hPclosed.1 Z.isClosedSubspace.1 hPdec (Z.subspace.fromPreimage f) w hwgen
  have hsq := (Subfunctor.isPullback_preimage f Z.subspace).flip
  have hxy : pointsMap D.site D.base D.base_mem X f x =
      pointsMap D.site D.base D.base_mem Z.subspace.toFunctor Z.subspace.ι
        (pointsMap D.site D.base D.base_mem (Z.subspace.preimage f).toFunctor
          (Z.subspace.fromPreimage f) w) := by
    rw [← hw, ← pointsMap_comp_apply, ← pointsMap_comp_apply, hsq.w]
  obtain ⟨w', hw'1, -, hdimiff, -⟩ := exists_point_preserving_fiberLocalRingDimension_and_trdeg
    D.site D.base D.base_mem hsq hPclosed.1 hX.1 Z.isClosedSubspace.1 hY.1 hfft x
    (pointsMap D.site D.base D.base_mem (Z.subspace.preimage f).toFunctor
      (Z.subspace.fromPreimage f) w) hxy
  have hw'w : w' = w := hemb.injective (hw'1.trans hw.symm)
  exact (hdimiff 0).mpr (hw'w ▸ hfib0)

/-! ### The δ-dimension of a component of a flat inverse image -/

/-- Let `f : X ⟶ Y` be a morphism of good algebraic spaces over the base which is flat of
relative dimension `r`, and let `Z ⊆ Y` be an integral closed subspace. An irreducible component
`Z'` of `f^{-1}(Z)` satisfies `dim_δ(Z') = dim_δ(Z) + r`. -/
@[stacks 0EP5 "the δ-dimension of a component of the inverse image of an integral closed \
subspace"]
theorem IntegralClosedSubspace.deltaDimension_preimageComponent_of_isFlat
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) {f : X ⟶ Y}
    (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (C : irreducibleComponents (Z.preimagePointSet D.site D.base D.base_mem f)) :
    deltaDimension D sX (Z.preimageComponent D.site D.base D.base_mem f hX.1
        (D.isDecentSpace_of_isGood sX hX) hY.1 C) = deltaDimension D sY Z + r := by
  have hfft : IsLocallyOfFiniteType D.site D.base D.base_mem f :=
    isLocallyOfFiniteType_of_comp D.site D.base D.base_mem hX.1 hY.1 D.isAlgebraicSpace f sY
      (by rw [hbase]; exact hX.2.2)
  set W := Z.preimageComponent D.site D.base D.base_mem f hX.1
    (D.isDecentSpace_of_isGood sX hX) hY.1 C with hWdef
  set ξ := pointsMap D.site D.base D.base_mem W.subspace.toFunctor W.subspace.ι
    (W.genericPoint D.site D.base D.base_mem) with hξdef
  have hgenξ : IsGenericPoint ξ (subspacePointSet D.site D.base D.base_mem X W.subspace) :=
    isGenericPoint_pointsMap_genericPoint D.site D.base D.base_mem hX.1 W
  have hdom : IsGenericPoint (pointsMap D.site D.base D.base_mem X f ξ)
      (subspacePointSet D.site D.base D.base_mem Y Z.subspace) :=
    Z.isGenericPoint_pointsMap_of_isGenericPoint_of_isFlat D sX hX sY hY hflat C ξ hgenξ
  have hgenC : IsGenericPoint ξ
      (Subtype.val '' (C : Set (Z.preimagePointSet D.site D.base D.base_mem f))) := by
    rwa [hWdef, Z.subspacePointSet_preimageComponent D.site D.base D.base_mem f hX.1
      (D.isDecentSpace_of_isGood sX hX) hY.1 C] at hgenξ
  have hfib0 := hasFiberLocalRingDimension_zero_of_isGenericPoint_preimageComponent D sX hX
    sY hY hfft Z C ξ hgenC
  obtain ⟨a, ha⟩ := exists_finite_transcendenceDegreeAt D.site D.base D.base_mem f hfft ξ
  have hsum := relativeDimensionAt_eq_fiberLocalRingDimension_add_transcendenceDegreeAt
    D.site D.base D.base_mem hX.1 hY.1 f ξ hfft (r : ℕ∞) 0 (a : ℕ∞) (hr ξ) hfib0 ha
  have har : a = r := by
    have hra : ((r : ℕ) : ℕ∞) = ((a : ℕ) : ℕ∞) := by simpa using hsum
    exact_mod_cast hra.symm
  obtain ⟨b, hb⟩ := exists_finite_transcendenceDegreeAt D.site D.base D.base_mem sY hY.2.2
    (pointsMap D.site D.base D.base_mem X f ξ)
  have hcomp : HasTranscendenceDegreeAt D.site D.base D.base_mem sX ξ ((a + b : ℕ) : ℕ∞) := by
    rw [← hbase]
    simpa only [Nat.cast_add] using hasTranscendenceDegreeAt_comp D.site D.base D.base_mem
      hX.1 hY.1 D.isAlgebraicSpace f sY ξ (a : ℕ∞) (b : ℕ∞) ha hb
  have hXval := inducedDimensionValue_eq D.site D.base D.base_mem hX.1 D.isAlgebraicSpace
    D.delta.toFun sX hX.2.2 ξ ((a + b : ℕ) : ℕ∞) hcomp
  have hYval := inducedDimensionValue_eq D.site D.base D.base_mem hY.1 D.isAlgebraicSpace
    D.delta.toFun sY hY.2.2 (pointsMap D.site D.base D.base_mem X f ξ) (b : ℕ∞) hb
  have himg : pointsMap D.site D.base D.base_mem X sX ξ =
      pointsMap D.site D.base D.base_mem Y sY
        (pointsMap D.site D.base D.base_mem X f ξ) := by
    rw [← hbase, pointsMap_comp_apply]
  rw [deltaDimension_eq_of_isGenericPoint D sX hX.1 W ξ hgenξ,
    deltaDimension_eq_of_isGenericPoint D sY hY.1 Z _ hdom]
  change inducedDimensionValue D.site D.base D.base_mem D.delta.toFun sX ξ =
    inducedDimensionValue D.site D.base D.base_mem D.delta.toFun sY
      (pointsMap D.site D.base D.base_mem X f ξ) + (r : ℤ)
  rw [hXval, hYval, himg, ← har]
  simp only [ENat.toNat_natCast]
  lia

/-! ### The δ-dimension of a flat inverse image -/

/-- Every irreducible closed subset of the space of points of a good algebraic space is the set
of points of an integral closed subspace. -/
private theorem exists_integralClosedSubspace_subspacePointSet_eq (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (C : IrreducibleCloseds (points D.site D.base D.base_mem Y)) :
    ∃ Z : IntegralClosedSubspace D.site D.base D.base_mem Y,
      subspacePointSet D.site D.base D.base_mem Y Z.subspace =
        (C : Set (points D.site D.base D.base_mem Y)) := by
  obtain ⟨Z, hZ⟩ := (bijective_integralClosedSubspaceSupport D.site D.base D.base_mem hY.1
    (D.isDecentSpace_of_isGood sY hY)).2 C
  exact ⟨Z, congrArg IrreducibleCloseds.carrier hZ⟩

/-- The δ-dimension of an integral closed subspace, as the δ-dimension of its set of points. -/
private theorem deltaDimensionClosed_subspacePointSet_eq (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    deltaDimensionClosed D sY hY (subspacePointSet D.site D.base D.base_mem Y Z.subspace)
        (isClosed_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem hY.1 Z) =
      (deltaDimension D sY Z : EInt) := by
  let hirr : IrreducibleCloseds (points D.site D.base D.base_mem Y) :=
    ⟨subspacePointSet D.site D.base D.base_mem Y Z.subspace,
      isIrreducible_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem Z,
      isClosed_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem hY.1 Z⟩
  have h1 : deltaDimensionClosed D sY hY
      (subspacePointSet D.site D.base D.base_mem Y Z.subspace)
      (isClosed_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem hY.1 Z) =
      (deltaDimensionIrreducible D sY hY hirr : EInt) :=
    deltaDimensionClosed_eq_deltaDimensionIrreducible D sY hY hirr
  rw [h1, deltaDimensionIrreducible_eq_of_isGenericPoint D sY hY hirr
    (isGenericPoint_pointsMap_genericPoint D.site D.base D.base_mem hY.1 Z)]
  rfl

/-- The δ-dimension of a nonempty inverse image of an integral closed subspace along a flat
morphism of relative dimension `r` is the δ-dimension of the subspace plus `r`. -/
theorem IntegralClosedSubspace.deltaDimensionClosed_preimagePointSet_eq (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) {f : X ⟶ Y}
    (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (hne : (Z.preimagePointSet D.site D.base D.base_mem f).Nonempty) :
    deltaDimensionClosed D sX hX (Z.preimagePointSet D.site D.base D.base_mem f)
        (Z.isClosed_preimagePointSet D.site D.base D.base_mem f hY.1) =
      ((deltaDimension D sY Z + (r : ℤ) : ℤ) : EInt) := by
  have hAclosed := Z.isClosed_preimagePointSet D.site D.base D.base_mem f hY.1
  have _hsober : QuasiSober (points D.site D.base D.base_mem X) :=
    quasiSober_points_of_isGood D sX hX
  have _hAsober : QuasiSober (Z.preimagePointSet D.site D.base D.base_mem f) :=
    hAclosed.isClosedEmbedding_subtypeVal.quasiSober
  have hval : deltaDimensionClosed D sX hX (Z.preimagePointSet D.site D.base D.base_mem f)
      hAclosed = ⨆ C : irreducibleComponents (Z.preimagePointSet D.site D.base D.base_mem f),
        (inducedDimensionValue D.site D.base D.base_mem D.delta sX C.2.1.genericPoint.1 :
          EInt) := rfl
  have hcomp : ∀ C : irreducibleComponents (Z.preimagePointSet D.site D.base D.base_mem f),
      (inducedDimensionValue D.site D.base D.base_mem D.delta sX C.2.1.genericPoint.1 : EInt) =
        ((deltaDimension D sY Z + (r : ℤ) : ℤ) : EInt) := by
    intro C
    have hCclosed := isClosed_image_val_of_mem_irreducibleComponents hAclosed C.2
    have hgen : IsGenericPoint (C.2.1.genericPoint : Z.preimagePointSet D.site D.base
        D.base_mem f).1
        (Subtype.val '' (C : Set (Z.preimagePointSet D.site D.base D.base_mem f))) := by
      simpa [hCclosed.closure_eq] using
        (C.2.1.isGenericPoint_genericPoint
          (isClosed_of_mem_irreducibleComponents _ C.2)).image continuous_subtype_val
    have hgen' : IsGenericPoint (C.2.1.genericPoint : Z.preimagePointSet D.site D.base
        D.base_mem f).1
        (subspacePointSet D.site D.base D.base_mem X
          (Z.preimageComponent D.site D.base D.base_mem f hX.1
            (D.isDecentSpace_of_isGood sX hX) hY.1 C).subspace) := by
      rwa [Z.subspacePointSet_preimageComponent D.site D.base D.base_mem f hX.1
        (D.isDecentSpace_of_isGood sX hX) hY.1 C]
    have hdim := Z.deltaDimension_preimageComponent_of_isFlat D sX hX sY hY hbase r hflat hr C
    rw [deltaDimension_eq_of_isGenericPoint D sX hX.1 _ _ hgen'] at hdim
    exact congrArg (fun n : ℤ => (n : EInt)) hdim
  obtain ⟨x, hx⟩ := hne
  have _hne : Nonempty (irreducibleComponents (Z.preimagePointSet D.site D.base D.base_mem f)) :=
    ⟨⟨_, irreducibleComponent_mem_irreducibleComponents ⟨x, hx⟩⟩⟩
  rw [hval, iSup_congr hcomp, iSup_const]

/-- Let `f : X ⟶ Y` be a morphism of good algebraic spaces over the base which is flat of
relative dimension `r`, and let `T ⊆ |Y|` be a closed set of points whose inverse image is
nonempty. Then `dim_δ(f^{-1}(T))` is `r` more than the supremum of the δ-dimensions of the
irreducible components of `T` which `f` meets.

When `f` meets every component of `T`, in particular when `f` is surjective, the supremum is
`dim_δ(T)` and the formula reads `dim_δ(f^{-1}(T)) = dim_δ(T) + r`. -/
@[stacks 0EP5 "the δ-dimension of the inverse image of a closed set of points"]
theorem deltaDimensionClosed_preimage_eq_iSup_add (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) {f : X ⟶ Y} (hbase : f ≫ sY = sX) (r : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (T : Set (points D.site D.base D.base_mem Y)) (hT : IsClosed T)
    (_hne : (pointsMap D.site D.base D.base_mem X f ⁻¹' T).Nonempty) :
    deltaDimensionClosed D sX hX (pointsMap D.site D.base D.base_mem X f ⁻¹' T)
        (isClosed_preimage_pointsMap D.site D.base D.base_mem hX.1 hY.1 f hT) =
      (⨆ C : irreducibleComponents T,
        ⨆ _ : (pointsMap D.site D.base D.base_mem X f ⁻¹'
            (Subtype.val '' (C : Set T))).Nonempty,
          deltaDimensionClosed D sY hY (closure (Subtype.val '' (C : Set T)))
            isClosed_closure) + ((r : ℤ) : EInt) := by
  have hScl : ∀ C : irreducibleComponents T, IsClosed (Subtype.val '' (C : Set T)) :=
    fun C => isClosed_image_val_of_mem_irreducibleComponents hT C.2
  have hprecl : ∀ C : irreducibleComponents T,
      IsClosed (pointsMap D.site D.base D.base_mem X f ⁻¹' (Subtype.val '' (C : Set T))) :=
    fun C => isClosed_preimage_pointsMap D.site D.base D.base_mem hX.1 hY.1 f (hScl C)
  have hcover : pointsMap D.site D.base D.base_mem X f ⁻¹' T =
      ⋃ C : irreducibleComponents T,
        pointsMap D.site D.base D.base_mem X f ⁻¹' (Subtype.val '' (C : Set T)) := by
    rw [← Set.preimage_iUnion]
    congr 1
    refine Set.Subset.antisymm (fun y hy => ?_) ?_
    · exact Set.mem_iUnion.mpr ⟨⟨_, irreducibleComponent_mem_irreducibleComponents ⟨y, hy⟩⟩,
        ⟨y, hy⟩, mem_irreducibleComponent, rfl⟩
    · exact Set.iUnion_subset fun C => fun y hy => by
        obtain ⟨z, -, rfl⟩ := hy; exact z.2
  rw [deltaDimensionClosed_eq_iSup_of_iUnion D sX hX _ _ _ hprecl hcover,
    Stacks.Chow.iSup_add_coe]
  refine iSup_congr fun C => ?_
  by_cases hC : (pointsMap D.site D.base D.base_mem X f ⁻¹'
      (Subtype.val '' (C : Set T))).Nonempty
  · rw [iSup_pos hC]
    obtain ⟨Z, hZ⟩ := exists_integralClosedSubspace_subspacePointSet_eq D sY hY
      ⟨Subtype.val '' (C : Set T), C.2.1.image _ continuous_subtype_val.continuousOn, hScl C⟩
    have hZset : subspacePointSet D.site D.base D.base_mem Y Z.subspace =
        Subtype.val '' (C : Set T) := hZ
    have hpre : Z.preimagePointSet D.site D.base D.base_mem f =
        pointsMap D.site D.base D.base_mem X f ⁻¹' (Subtype.val '' (C : Set T)) := by
      rw [← hZset]
    have hdim := Z.deltaDimensionClosed_preimagePointSet_eq D sX hX sY hY hbase r hflat hr
      (hpre ▸ hC)
    have h1 : deltaDimensionClosed D sX hX (pointsMap D.site D.base D.base_mem X f ⁻¹'
        (Subtype.val '' (C : Set T))) (hprecl C) =
        deltaDimensionClosed D sX hX (Z.preimagePointSet D.site D.base D.base_mem f)
          (Z.isClosed_preimagePointSet D.site D.base D.base_mem f hY.1) :=
      deltaDimensionClosed_congr D sX hX hpre.symm _ _
    have h2 : deltaDimensionClosed D sY hY (closure (Subtype.val '' (C : Set T)))
        isClosed_closure =
        deltaDimensionClosed D sY hY
          (subspacePointSet D.site D.base D.base_mem Y Z.subspace)
          (isClosed_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem hY.1 Z) :=
      deltaDimensionClosed_congr D sY hY (((hScl C).closure_eq).trans hZset.symm) _ _
    rw [h1, hdim, h2, deltaDimensionClosed_subspacePointSet_eq D sY hY Z,
      Stacks.Chow.coe_add_coe_eq_coe_add]
  · rw [iSup_neg hC, WithBot.bot_add,
      deltaDimensionClosed_eq_biSup D sX hX _ (hprecl C),
      Set.not_nonempty_iff_eq_empty.mp hC]
    simp

end AlgebraicGeometry.Space

end
