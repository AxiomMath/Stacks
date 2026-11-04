module

public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyLocus
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFppfLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.FullSubcategoryBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopologyRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsWithinOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedStackClosedSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityComp
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocus
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap
public import StacksFrontier.CategoryTheory.TwoFibreProduct.TripleProductRecognition
public import StacksFrontier.CategoryTheory.TwoFibreProduct.TripleProductRecognitionSnd

/-!
# The locus of a relative property, from its hypotheses on algebraic spaces (Stacks 06M3)

Let `P`, `Q`, `R` be properties of morphisms of algebraic spaces over `S`, fppf local on the
target and stable under base change, such that smoothness implies `R`
(`AlgebraicGeometry.Stack.SmoothImplies`), every morphism with `Q` has a greatest open subspace
of its source on which it has `P` (`AlgebraicGeometry.Stack.HasRelativePropertyLocusOnSpaces`),
and that greatest open subspace is compatible with base change along a morphism with `R`
(`AlgebraicGeometry.Stack.RelativePropertyLocusBaseChange`). For a 1-morphism `f` of algebraic
stacks over `S` representable by algebraic spaces and having `Q`, this file constructs the locus
`W(P, f)` of **Stacks 06M3**, in the sense of `AlgebraicGeometry.Stack.IsRelativePropertyLocus`,
from a smooth scheme chart of the target, and proves the maximality half of assertion (B).

## Main results

* `AlgebraicGeometry.Stack.exists_isRelativePropertyLocus_of_hasRelativePropertyLocusOnSpaces`:
  assertion (A) of Stacks 06M3 from its hypotheses on algebraic spaces.
* `AlgebraicGeometry.Stack.isRelativePropertyLocus_baseChange_apply_symm` and
  `AlgebraicGeometry.Stack.pointSet_subset_preimage_of_hasRelativeProperty`: the maximality half of
  assertion (B).

## References

* [Stacks Project, Tag 06M3](https://stacks.math.columbia.edu/tag/06M3)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The hypotheses of Stacks 06M3 -/

/-- The set of open subspaces of `X` on which a morphism `f : X ⟶ Y` of algebraic spaces over `S`
has the property `P`. The `W(P, f)` of **Stacks 06M3** is the greatest element of this set. -/
def relativePropertyOpens (P : MorphismProperty (AlgebraicSpaces B S hS))
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    Set {V : Subfunctor X // Space.IsOpenSubspace B S hS V} :=
  {V | P (ObjectProperty.homMk (V.1.ι ≫ f) :
    (⟨V.1.toFunctor, V.2.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)}

/-- **Hypothesis (3) of Stacks 06M3.** Every morphism `f : X ⟶ Y` of algebraic spaces over `S`
with the property `Q` has a greatest open subspace `W(P, f)` of `X` on which it has `P`. -/
def HasRelativePropertyLocusOnSpaces (P Q : MorphismProperty (AlgebraicSpaces B S hS)) : Prop :=
  ∀ (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
      (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y),
    Q (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩) →
      ∃ W, IsGreatest (relativePropertyOpens B S hS P hY f) W

/-- **Hypothesis (4) of Stacks 06M3.** For a morphism `f : X ⟶ Y` of algebraic spaces over `S`
with the property `Q` and a morphism `g : Y' ⟶ Y` with the property `R`, the greatest open
subspace of the source of the base change `f'` on which `f'` has `P` is the inverse image of the
greatest open subspace of `X` on which `f` has `P`: the identity
`Y' ×_Y W(P, f) = W(P, f')`. Both greatest open subspaces are quantified over rather than
chosen. -/
def RelativePropertyLocusBaseChange (P Q R : MorphismProperty (AlgebraicSpaces B S hS)) : Prop :=
  ∀ (X' X Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (_hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
      (hY' : IsAlgebraicSpace B S hS Y') (hY : IsAlgebraicSpace B S hS Y)
      (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (_sq : IsPullback g' f' f g),
    Q (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩) →
      R (ObjectProperty.homMk g : (⟨Y', hY'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩) →
        ∀ W, IsGreatest (relativePropertyOpens B S hS P hY f) W →
          ∀ W', IsGreatest (relativePropertyOpens B S hS P hY' f') W' →
            W'.1 = W.1.preimage g'

/-- **Hypothesis (2) of Stacks 06M3.** Smoothness implies `R`. -/
def SmoothImplies (R : MorphismProperty (AlgebraicSpaces B S hS)) : Prop :=
  ∀ (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
      (hY : IsAlgebraicSpace B S hS Y) (g : X ⟶ Y),
    Space.IsSmooth B S hS g →
      R (ObjectProperty.homMk g : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)

/-! ### Two set-theoretic steps -/

/-- **Stacks 04XH, set-theoretically.** In a 2-fibre product square of categories fibred in
groupoids over the big fppf site of `S`, the image under one projection of the preimage of a set
of points under the other is the preimage of its image. -/
theorem image_preimage_pointsMap_of_isTwoFibreProduct
    {𝒳 𝒬 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {g : 𝒳 ⟶ 𝒴} {f : 𝒬 ⟶ 𝒴}
    (D : Bicategory.TwoCommSq g f) (hD : Bicategory.IsTwoFibreProduct D)
    (T : Set (points B S hS 𝒳.val 𝒳.property)) :
    pointsMap B S hS D.pt.val D.pt.property 𝒬.property D.snd.hom ''
        (pointsMap B S hS D.pt.val D.pt.property 𝒳.property D.fst.hom ⁻¹' T) =
      pointsMap B S hS 𝒬.val 𝒬.property 𝒴.property f.hom ⁻¹'
        (pointsMap B S hS 𝒳.val 𝒳.property 𝒴.property g.hom '' T) := by
  have hcomm : ∀ r, pointsMap B S hS 𝒳.val 𝒳.property 𝒴.property g.hom
        (pointsMap B S hS D.pt.val D.pt.property 𝒳.property D.fst.hom r) =
      pointsMap B S hS 𝒬.val 𝒬.property 𝒴.property f.hom
        (pointsMap B S hS D.pt.val D.pt.property 𝒬.property D.snd.hom r) := by
    intro r
    rw [pointsMap_comp, pointsMap_comp]
    exact congrFun (pointsMap_eq_of_basedNatTrans B S hS D.pt.val D.pt.property 𝒴.property
      D.iso.hom.hom) r
  ext z
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨_, hr, hcomm r⟩
  · rintro ⟨x, hx, hxz⟩
    obtain ⟨r, hr₁, hr₂⟩ := exists_point_of_isTwoFibreProduct B S hS D hD x z hxz
    exact ⟨r, by simpa [hr₁] using hx, hr₂⟩

/-- The point set of the inverse image of a subfunctor along a morphism of presheaves on the big
fppf site of `S` is the preimage of its point set. -/
theorem range_pointsMap_preimage_eq
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Y ⟶ X) (Z : Subfunctor X) :
    Set.range (Space.pointsMap B S hS (Z.preimage g).toFunctor (Z.preimage g).ι) =
      Space.pointsMap B S hS Y g ⁻¹' Set.range (Space.pointsMap B S hS Z.toFunctor Z.ι) := by
  rw [← Set.image_univ, ← Set.image_univ (f := Space.pointsMap B S hS Z.toFunctor Z.ι),
    Space.preimage_image_pointsMap_of_isPullback B S hS
      (Subfunctor.isPullback_preimage g Z) Set.univ,
    Set.preimage_univ, Set.image_univ]

/-- **The morphism of representing presheaves induced by the first leg of a pasted rectangle.**
It is the composite of those induced by the two inner first legs. -/
theorem representingMap_paste_fst
    {𝒱 𝒴 𝒳 𝒲 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {b : 𝒱 ⟶ 𝒴} {fm : 𝒳 ⟶ 𝒴} (D : Bicategory.TwoCommSq b fm) {k : 𝒲 ⟶ 𝒳}
    (E : Bicategory.TwoCommSq D.snd k)
    (F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver E.pt.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver D.pt.val.p
      (presheafOfCategories (G ⋙ typeToCat)).p)
    (eH : StacksRepresentableCFG.EquivalenceOver 𝒱.val.p
      (presheafOfCategories (H ⋙ typeToCat)).p) :
    representingMap B S hS (D.paste E).pt 𝒱 F H eF eH (D.paste E).fst =
      representingMap B S hS E.pt D.pt F G eF eG E.fst ≫
        representingMap B S hS D.pt 𝒱 G H eG eH D.fst :=
  representingMap_comp B S hS F G H eF eG eH E.fst D.fst

/-- In a 2-fibre product square over `(g, f)`, the range on points of the second projection is the
preimage under `f` of the range of `g`. -/
private theorem range_pointsMap_snd_eq_preimage_range
    {𝒳 𝒬 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {g : 𝒳 ⟶ 𝒴} {f : 𝒬 ⟶ 𝒴} (D : Bicategory.TwoCommSq g f) (hD : Bicategory.IsTwoFibreProduct D) :
    Set.range (pointsMap B S hS D.pt.val D.pt.property 𝒬.property D.snd.hom) =
      pointsMap B S hS 𝒬.val 𝒬.property 𝒴.property f.hom ⁻¹'
        Set.range (pointsMap B S hS 𝒳.val 𝒳.property 𝒴.property g.hom) := by
  simpa only [Set.preimage_univ, Set.image_univ] using
    image_preimage_pointsMap_of_isTwoFibreProduct B S hS D hD Set.univ

/-- A 2-fibre product square over `(g, f)` has surjective second projection when `g` is
surjective on points. -/
private theorem surjective_pointsMap_snd_of_surjective
    {𝒳 𝒬 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {g : 𝒳 ⟶ 𝒴} {f : 𝒬 ⟶ 𝒴} (D : Bicategory.TwoCommSq g f) (hD : Bicategory.IsTwoFibreProduct D)
    (hg : Function.Surjective (pointsMap B S hS 𝒳.val 𝒳.property 𝒴.property g.hom)) :
    Function.Surjective (pointsMap B S hS D.pt.val D.pt.property 𝒬.property D.snd.hom) := by
  rw [← Set.range_eq_univ, range_pointsMap_snd_eq_preimage_range B S hS D hD,
    Set.range_eq_univ.2 hg, Set.preimage_univ]

/-- An open immersion `j` followed by `f'` has `P` if and only if the inclusion of the range of `j`
followed by `f'` has `P`. -/
private theorem property_comp_iff_property_range_ι_comp
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.RespectsIso]
    {V U X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
    (hX : IsAlgebraicSpace B S hS X) {j : V ⟶ U} (hj : Space.IsOpenImmersion B S hS j)
    (f' : U ⟶ X) :
    P (ObjectProperty.homMk (X := (⟨V, hV⟩ : AlgebraicSpaces B S hS))
        (Y := (⟨X, hX⟩ : AlgebraicSpaces B S hS)) (j ≫ f')) ↔
      P (ObjectProperty.homMk (X := (⟨(Subfunctor.range j).toFunctor,
          (Space.isOpenSubspace_subfunctorRange B S hS hV hj).1⟩ : AlgebraicSpaces B S hS))
        (Y := (⟨X, hX⟩ : AlgebraicSpaces B S hS)) ((Subfunctor.range j).ι ≫ f')) := by
  have := Space.mono_of_isOpenImmersion B S hS j hj
  have : IsIso (ObjectProperty.homMk (X := (⟨V, hV⟩ : AlgebraicSpaces B S hS))
      (Y := (⟨(Subfunctor.range j).toFunctor,
        (Space.isOpenSubspace_subfunctorRange B S hS hV hj).1⟩ : AlgebraicSpaces B S hS))
      (Subfunctor.toRange j)) :=
    ⟨⟨ObjectProperty.homMk (inv (Subfunctor.toRange j)), by
      apply ObjectProperty.hom_ext; simp, by apply ObjectProperty.hom_ext; simp⟩⟩
  rw [← P.cancel_left_of_respectsIso (ObjectProperty.homMk (X := (⟨V, hV⟩ : AlgebraicSpaces B S hS))
    (Y := (⟨(Subfunctor.range j).toFunctor,
      (Space.isOpenSubspace_subfunctorRange B S hS hV hj).1⟩ : AlgebraicSpaces B S hS))
    (Subfunctor.toRange j))]
  rfl

/-- If `j ≫ f'` has `P` for an open immersion `j`, then the points of its source lie in the
greatest open subspace on which `f'` has `P`. -/
private theorem range_pointsMap_subset_of_property_comp
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.RespectsIso]
    {V U X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
    (hX : IsAlgebraicSpace B S hS X) {j : V ⟶ U} (hj : Space.IsOpenImmersion B S hS j)
    {f' : U ⟶ X} {W : {V : Subfunctor U // Space.IsOpenSubspace B S hS V}}
    (hW : IsGreatest (relativePropertyOpens B S hS P hX f') W)
    (h : P (ObjectProperty.homMk (X := (⟨V, hV⟩ : AlgebraicSpaces B S hS))
      (Y := (⟨X, hX⟩ : AlgebraicSpaces B S hS)) (j ≫ f'))) :
    Set.range (Space.pointsMap B S hS V j) ⊆
      Set.range (Space.pointsMap B S hS W.1.toFunctor W.1.ι) := by
  have hle : Subfunctor.range j ≤ W.1 :=
    hW.2 (show (⟨Subfunctor.range j, Space.isOpenSubspace_subfunctorRange B S hS hV hj⟩ :
      {V : Subfunctor U // Space.IsOpenSubspace B S hS V}) ∈ relativePropertyOpens B S hS P hX f'
      from (property_comp_iff_property_range_ι_comp B S hS P hV hX hj f').1 h)
  have := Space.mono_of_isOpenImmersion B S hS j hj
  rw [← Space.range_pointsMap_ι_range B S hS j]
  rintro _ ⟨z, rfl⟩
  refine ⟨Space.pointsMap B S hS (Subfunctor.range j).toFunctor (Subfunctor.homOfLe hle) z, ?_⟩
  rw [← Function.comp_apply (f := Space.pointsMap B S hS W.1.toFunctor W.1.ι),
    ← Space.pointsMap_comp, Subfunctor.homOfLe_ι]

/-! ### The chart construction -/

section Chart

variable (P Q R : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    [Q.IsStableUnderBaseChange]
    [Q.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    [R.IsStableUnderBaseChange]
    [R.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]

omit [R.IsStableUnderBaseChange] [R.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)] in
/-- **Stacks 06M3, assertion (A), run at a given chart of the target.** The chart is a scheme
`Vo` of the site together with a 1-morphism `c` to `𝒴` representable by algebraic spaces whose
represented base changes are surjective and smooth — the scheme presentation that
`AlgebraicGeometry.Stack.IsAlgebraicStack` carries.

Besides the locus itself the statement returns the chart data the construction ran on: the
algebraic space `U` representing the chart base change, the greatest open subspace `W` of `U` on
which the morphism of representing presheaves has `P`, and the identification of the point set of
the locus — its inverse image on `U` is exactly the point set of `W`. -/
private theorem exists_isRelativePropertyLocus_of_chart (hsmR : SmoothImplies B S hS R)
    (h3 : HasRelativePropertyLocusOnSpaces B S hS P Q)
    (h4 : RelativePropertyLocusBaseChange B S hS P Q R)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hQf : HasRelativeProperty.{u, u, u + 1, u} B S hS Q f.hom hf)
    (Vo : BigFppfOver B S hS)
    (c : schemeFibredCategory B S hS Vo ⟶ 𝒴.val)
    (hcrep : IsRepresentableByAlgebraicSpaces B S hS c.hom)
    (hcsurj : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) c hcrep)
    (hcsm : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.smoothMorphismProperty B S hS) c hcrep) :
    ∃ (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS U)
      (eU : StacksRepresentableCFG.EquivalenceOver
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} c f.hom).pt.val.p
        (presheafOfCategories (U ⋙ typeToCat)).p)
      (W : {V : Subfunctor U // Space.IsOpenSubspace B S hS V}) (𝒲 : OpenSubstack 𝒳),
      IsGreatest (relativePropertyOpens B S hS P (isAlgebraicSpace_yoneda B S hS Vo)
        (representingMap B S hS
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} c f.hom).pt
          (schemeFibredCategory B S hS Vo) U (yoneda.obj Vo) eU
          (PresheafOfCategories.sliceElementsEquivalenceOver.{u} Vo)
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} c f.hom).fst)) W ∧
      IsRelativePropertyLocus B S hS P f hf 𝒲 ∧
      spacePointMap B S hS U 𝒳.val
          ((Bicategory.InducedBicategory.mkHom (representationMap B S hS U
              (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} c f.hom).pt eU) ≫
            (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} c f.hom).snd).hom)
            ⁻¹' (𝒲.pointSet B S hS) =
        Set.range (Space.pointsMap B S hS W.1.toFunctor W.1.ι) ∧
      𝒲.property = pointsWithin 𝒳 (𝒲.pointSet B S hS) := by
  classical
  have : (Space.openImmersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.openImmersion_isLocalAtTarget_fppf.{u, u} B S hS
  have hVp : IsAlgebraicSpace B S hS (yoneda.obj Vo) := isAlgebraicSpace_yoneda B S hS Vo
  have h𝒱rep : IsRepresentableByAlgebraicSpace B S hS (schemeFibredCategory B S hS Vo) :=
    ⟨yoneda.obj Vo, hVp, ⟨PresheafOfCategories.sliceElementsEquivalenceOver.{u} Vo⟩⟩
  have h𝒱alg : IsAlgebraicStack.{u, w} B S hS (schemeFibredCategory B S hS Vo).val :=
    isAlgebraicStack_schemeFibredCategory.{u, w} B S hS Vo
  have hdiagY := SelfIntersection.hasRepresentableDiagonal_of_isAlgebraicStack.{u, w}
    B S hS 𝒴.val 𝒴.property
  have hdiagV := SelfIntersection.hasRepresentableDiagonal_of_isAlgebraicStack.{u, w}
    B S hS (schemeFibredCategory B S hS Vo) h𝒱alg
  set eV := PresheafOfCategories.sliceElementsEquivalenceOver.{u} Vo with heV
  set Q₁ := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} c f.hom with hQ₁def
  have hQ₁ : Bicategory.IsTwoFibreProduct Q₁ :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} c f.hom
  obtain ⟨U, hU, ⟨eU⟩⟩ : IsRepresentableByAlgebraicSpace B S hS Q₁.pt :=
    isRepresentableByAlgebraicSpace_twoFibreProduct.{u, u, u + 1, u, u + 1, u, u + 1}
      B S hS 𝒴.val (schemeFibredCategory B S hS Vo) 𝒳.val c.hom f.hom.hom hf h𝒱rep
  have h𝒰rep : IsRepresentableByAlgebraicSpace B S hS Q₁.pt := ⟨U, hU, ⟨eU⟩⟩
  set kk : fibredCategory B S hS U ⟶ Q₁.pt :=
    Bicategory.InducedBicategory.mkHom (representationMap B S hS U Q₁.pt eU) with hkkdef
  set QR := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} c c with hQRdef
  have hQR : Bicategory.IsTwoFibreProduct QR :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} c c
  obtain ⟨Rs, hRs, ⟨eR⟩⟩ : IsRepresentableByAlgebraicSpace B S hS QR.pt :=
    hasAlgebraicSpaceProducts_of_hasRepresentableDiagonal.{u, u, u + 1, u, u, u, u}
      B S hS 𝒴.val hdiagY (schemeFibredCategory B S hS Vo) (schemeFibredCategory B S hS Vo)
      h𝒱rep h𝒱rep c.hom c.hom
  set Hsq := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Q₁.fst QR.fst
    with hHsqdef
  have hHsq : Bicategory.IsTwoFibreProduct Hsq :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      Q₁.fst QR.fst
  obtain ⟨Hs, hHs, ⟨eH⟩⟩ : IsRepresentableByAlgebraicSpace B S hS Hsq.pt :=
    hasAlgebraicSpaceProducts_of_hasRepresentableDiagonal.{u, u, u + 1, u, u, u, u}
      B S hS (schemeFibredCategory B S hS Vo) hdiagV Q₁.pt QR.pt h𝒰rep ⟨Rs, hRs, ⟨eR⟩⟩
      Q₁.fst.hom QR.fst.hom
  obtain ⟨Cs, hCs, ⟨eC⟩⟩ : IsRepresentableByAlgebraicSpace B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} QR.snd Q₁.fst).pt :=
    hasAlgebraicSpaceProducts_of_hasRepresentableDiagonal.{u, u, u + 1, u, u, u, u}
      B S hS (schemeFibredCategory B S hS Vo) hdiagV QR.pt Q₁.pt ⟨Rs, hRs, ⟨eR⟩⟩ h𝒰rep
      QR.snd.hom Q₁.fst.hom
  set f' := representingMap B S hS Q₁.pt (schemeFibredCategory B S hS Vo) U (yoneda.obj Vo)
    eU eV Q₁.fst with hf'def
  set pr₁ := representingMap B S hS QR.pt (schemeFibredCategory B S hS Vo) Rs (yoneda.obj Vo)
    eR eV QR.fst with hpr₁def
  set pr₂ := representingMap B S hS QR.pt (schemeFibredCategory B S hS Vo) Rs (yoneda.obj Vo)
    eR eV QR.snd with hpr₂def
  set av := representingMap B S hS Hsq.pt Q₁.pt Hs U eH eU Hsq.fst with havdef
  set fH := representingMap B S hS Hsq.pt QR.pt Hs Rs eH eR Hsq.snd with hfHdef
  set bv := representingMap B S hS Hsq.pt Q₁.pt Hs U eH eU
    (CatFiberedInGroupoids.triplePairingMor.{u, u, u + 1, u + 1} c f.hom c) with hbvdef
  have sq1 : IsPullback av fH f' pr₁ :=
    isPullback_representingMap_of_isTwoFibreProduct B S hS hHsq U Rs (yoneda.obj Vo) Hs Hs
      eU eR eV eH eH
  have sq2 : IsPullback fH bv pr₂ f' :=
    isPullback_representingMap_of_isTwoFibreProduct B S hS
      (CatFiberedInGroupoids.isTwoFibreProduct_tripleProductSndSquare.{u, u, u + 1, u + 1}
        c f.hom c)
      Rs U (yoneda.obj Vo) Hs Cs eR eU eV eH eC
  have hQf' : Q (ObjectProperty.homMk f' :
      (⟨U, hU⟩ : AlgebraicSpaces B S hS) ⟶ ⟨yoneda.obj Vo, hVp⟩) :=
    (hasRelativeProperty_iff_forall_space_baseChange.{u, u} B S hS Q f.hom hf).mp hQf
      (schemeFibredCategory B S hS Vo) h𝒱rep c Q₁ hQ₁ U (yoneda.obj Vo) hU hVp eU eV
  have hQ₁fst := hasRelativeProperty_baseChange.{u, u, u + 1} B S hS Q 𝒳.val 𝒴.val
    (schemeFibredCategory B S hS Vo) f.hom c Q₁ hQ₁ hf hQf
  have hQfH : Q (ObjectProperty.homMk fH :
      (⟨Hs, hHs⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Rs, hRs⟩) :=
    (hasRelativeProperty_iff_forall_space_baseChange.{u, u} B S hS Q Q₁.fst _).mp hQ₁fst
      QR.pt ⟨Rs, hRs, ⟨eR⟩⟩ QR.fst Hsq.swap (Bicategory.isTwoFibreProduct_swap hHsq)
      Hs Rs hHs hRs eH eR
  have hsm₁ : Space.IsSmooth B S hS pr₁ :=
    (hasRelativeProperty_iff_forall_space_baseChange.{u, u} B S hS
      (Space.smoothMorphismProperty B S hS) c hcrep).mp hcsm
      (schemeFibredCategory B S hS Vo) h𝒱rep c QR hQR Rs (yoneda.obj Vo) hRs hVp eR eV
  have hsm₂ : Space.IsSmooth B S hS pr₂ :=
    (hasRelativeProperty_iff_forall_space_baseChange.{u, u} B S hS
      (Space.smoothMorphismProperty B S hS) c hcrep).mp hcsm
      (schemeFibredCategory B S hS Vo) h𝒱rep c QR.swap (Bicategory.isTwoFibreProduct_swap hQR)
      Rs (yoneda.obj Vo) hRs hVp eR eV
  obtain ⟨W, hW⟩ := h3 U (yoneda.obj Vo) hU hVp f' hQf'
  obtain ⟨W'', hW''⟩ := h3 Hs Rs hHs hRs fH hQfH
  have inv₁ : W''.1 = W.1.preimage av :=
    h4 Hs U Rs (yoneda.obj Vo) hHs hU hRs hVp av fH f' pr₁ sq1 hQf'
      (hsmR Rs (yoneda.obj Vo) hRs hVp pr₁ hsm₁) W hW W'' hW''
  have inv₂ : W''.1 = W.1.preimage bv :=
    h4 Hs U Rs (yoneda.obj Vo) hHs hU hRs hVp bv fH f' pr₂ sq2.flip hQf'
      (hsmR Rs (yoneda.obj Vo) hRs hVp pr₂ hsm₂) W hW W'' hW''
  have hinv : W.1.preimage av = W.1.preimage bv := inv₁ ▸ inv₂
  have hrUbij : Function.Bijective (spacePointMap B S hS U Q₁.pt
      (representationMap B S hS U Q₁.pt eU)) :=
    bijective_spacePointMap_representing B S hS U Q₁.pt eU
  have hrHbij : Function.Bijective (spacePointMap B S hS Hs Hsq.pt
      (representationMap B S hS Hs Hsq.pt eH)) :=
    bijective_spacePointMap_representing B S hS Hs Hsq.pt eH
  set rU := spacePointMap B S hS U Q₁.pt (representationMap B S hS U Q₁.pt eU) with hrUdef
  set rH := spacePointMap B S hS Hs Hsq.pt (representationMap B S hS Hs Hsq.pt eH) with hrHdef
  have hcmp : spacePointMap B S hS U 𝒳.val (kk ≫ Q₁.snd).hom =
      pointsMap B S hS Q₁.pt.val Q₁.pt.property 𝒳.val.property Q₁.snd.hom ∘ rU :=
    spacePointMap_comp B S hS U Q₁.pt 𝒳.val (representationMap B S hS U Q₁.pt eU) Q₁.snd.hom
  set Wpts := Set.range (Space.pointsMap B S hS W.1.toFunctor W.1.ι) with hWptsdef
  set Ω := spacePointMap B S hS U 𝒳.val (kk ≫ Q₁.snd).hom '' Wpts with hΩdef
  have hQsq := CatFiberedInGroupoids.isTwoFibreProduct_tripleProductSquare.{u, u, u + 1, u + 1}
    c f.hom c
  have hA : ∀ z, rU (Space.pointsMap B S hS Hs av z) =
      pointsMap B S hS Hsq.pt.val Hsq.pt.property Q₁.pt.property Hsq.fst.hom (rH z) :=
    fun z => representationMap_naturality B S hS Hs U Hsq.pt Q₁.pt eH eU Hsq.fst z
  have hBb : ∀ z, rU (Space.pointsMap B S hS Hs bv z) =
      pointsMap B S hS Hsq.pt.val Hsq.pt.property Q₁.pt.property
        (CatFiberedInGroupoids.triplePairingMor.{u, u, u + 1, u + 1} c f.hom c).hom (rH z) :=
    fun z => representationMap_naturality B S hS Hs U Hsq.pt Q₁.pt eH eU
      (CatFiberedInGroupoids.triplePairingMor.{u, u, u + 1, u + 1} c f.hom c) z
  have hinvpts : Space.pointsMap B S hS Hs av ⁻¹' Wpts =
      Space.pointsMap B S hS Hs bv ⁻¹' Wpts := by
    rw [← range_pointsMap_preimage_eq B S hS av W.1, ← range_pointsMap_preimage_eq B S hS bv W.1,
      hinv]
  have key : spacePointMap B S hS U 𝒳.val (kk ≫ Q₁.snd).hom ⁻¹' Ω = Wpts := by
    refine subset_antisymm ?_ (Set.subset_preimage_image _ _)
    rintro z ⟨x, hx, hxz⟩
    rw [hcmp] at hxz
    obtain ⟨r, hr₁, hr₂⟩ := exists_point_of_isTwoFibreProduct B S hS
      (CatFiberedInGroupoids.tripleProductSquare.{u, u, u + 1, u + 1} c f.hom c) hQsq
      (rU x) (rU z) hxz
    obtain ⟨q, hq⟩ := hrHbij.surjective r
    have hax : Space.pointsMap B S hS Hs av q = x := by
      refine hrUbij.injective ?_
      rw [hA q, hq]
      exact hr₁
    have hbz : Space.pointsMap B S hS Hs bv q = z := by
      refine hrUbij.injective ?_
      rw [hBb q, hq]
      exact hr₂
    have hmem : q ∈ Space.pointsMap B S hS Hs av ⁻¹' Wpts := by simpa [hax] using hx
    rw [hinvpts] at hmem
    simpa [hbz] using hmem
  have hsmQ₁snd : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.smoothMorphismProperty B S hS) Q₁.swap.fst _ :=
    hasRelativeProperty_baseChange.{u, u, u + 1} B S hS
      (Space.smoothMorphismProperty B S hS) (schemeFibredCategory B S hS Vo) 𝒴.val 𝒳.val
      c f.hom Q₁.swap (Bicategory.isTwoFibreProduct_swap hQ₁) hcrep hcsm
  have haeq : Functor.IsEquivalence (representationMap B S hS U Q₁.pt eU).toFunctor :=
    eU.symm.toEquivalence.isEquivalence_functor
  have hbeq : Functor.IsEquivalence (BasedFunctor.id 𝒳.val.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒳.val.val.obj))
  have hbase := relativeProperty_of_equivalences B S hS
    (fun _ _ k => Space.IsFlat B S hS k.hom ∧
      Space.IsLocallyOfFinitePresentation B S hS k.hom)
    (kk ≫ Q₁.snd).hom Q₁.snd.hom (representationMap B S hS U Q₁.pt eU)
    (BasedFunctor.id 𝒳.val.val) (Iso.refl _)
    (fun V y hy G hG he => ⟨Space.isFlat_of_isSmooth B S hS _ (hsmQ₁snd V y hy G hG he),
      Space.isLocallyOfFinitePresentation_of_isSmooth B S hS (hsmQ₁snd V y hy G hG he)⟩)
  have hWptsopen : @IsOpen _ (Space.pointTopology B S hS U) Wpts :=
    Space.isOpen_range_pointsMap_of_isOpenImmersion B S hS W.1.ι W.2.2
  have hΩopen : @IsOpen _ (pointTopology B S hS 𝒳.val) Ω :=
    isOpenMap_spacePointMap B S hS U hU 𝒳.val 𝒳.property (kk ≫ Q₁.snd).hom hbase Wpts hWptsopen
  clear_value Ω
  clear hA hBb hinvpts inv₁ inv₂ hinv sq1 sq2 hQsq hrHbij hsm₁ hsm₂ hQfH hW''
  set 𝒲 := pointsWithinOpenSubstack B S hS 𝒳 Ω hΩopen with h𝒲def
  set incl := fullSubcategoryFiberedInclusion 𝒳 (fun e => pointsWithin_of_hom 𝒳 Ω e)
    with hincldef
  set iD : (kk ≫ Q₁.fst) ≫ c ≅ (kk ≫ Q₁.snd) ≫ f.hom :=
    Bicategory.associator kk Q₁.fst c ≪≫ Bicategory.whiskerLeftIso kk Q₁.iso ≪≫
      (Bicategory.associator kk Q₁.snd f.hom).symm with hiD
  have hD : Bicategory.IsTwoFibreProduct
      ({ pt := fibredCategory B S hS U, fst := kk ≫ Q₁.fst, snd := kk ≫ Q₁.snd, iso := iD } :
        Bicategory.TwoCommSq c f.hom) := by
    refine Bicategory.isTwoFibreProduct_of_isEquivalence_to hQ₁
      { hom := kk, isoFst := Iso.refl _, isoSnd := Iso.refl _, compat := ?_ } haeq
    have h1 : Bicategory.whiskerRight (𝟙 (kk ≫ Q₁.snd)) f.hom = 𝟙 _ :=
      Bicategory.id_whiskerRight _ _
    have h2 : Bicategory.whiskerRight (𝟙 (kk ≫ Q₁.fst)) c = 𝟙 _ :=
      Bicategory.id_whiskerRight _ _
    rw [hiD]
    simp only [Iso.refl_hom, Iso.trans_hom, Iso.symm_hom, Bicategory.whiskerLeftIso_hom, h1, h2,
      Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  set Qin := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Q₁.snd incl
    with hQindef
  have hQin : Bicategory.IsTwoFibreProduct Qin :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} Q₁.snd incl
  have hQout : Bicategory.IsTwoFibreProduct (Q₁.paste Qin) :=
    Bicategory.isTwoFibreProduct_pasteSnd Q₁ hQ₁ Qin hQin
  obtain ⟨eQ⟩ := nonempty_equivalenceOver_chartBaseChange_comp_pointsWithin
    (𝒳 := 𝒳) (U := U) Ω f.hom c (kk ≫ Q₁.fst) (kk ≫ Q₁.snd) iD hD (Q₁.paste Qin) hQout
  set Vops := Space.openSubspaceOfPoints B S hS U
    (spacePointMap B S hS U 𝒳.val (kk ≫ Q₁.snd).hom ⁻¹' Ω) with hVopsdef
  have hVopsrange : Set.range (Space.pointsMap B S hS Vops.toFunctor Vops.ι) = Wpts := by
    rw [hVopsdef, Space.range_pointsMap_ι_openSubspaceOfPoints, key]
  have hVopsopen : Space.IsOpenSubspace B S hS Vops := by
    rw [hVopsdef, key]
    exact Space.isOpenSubspace_openSubspaceOfPoints B S hS hU Wpts hWptsopen
  have hVopsW : Vops = W.1 :=
    le_antisymm
      (Space.le_of_range_pointsMap_ι_subset B S hS W.2 (by rw [hVopsrange]))
      (Space.le_of_range_pointsMap_ι_subset B S hS hVopsopen (by rw [hVopsrange]))
  set i0 := representingMap B S hS Qin.pt Q₁.pt Vops.toFunctor U eQ eU Qin.fst with hi0def
  have hi0oi : Space.IsOpenImmersion B S hS i0 :=
    (hasRelativeProperty_iff_forall_space_baseChange.{u, u} B S hS
      (Space.openImmersionProperty B S hS) incl
      (isRepresentableByAlgebraicSpaces_fullSubcategoryBasedInclusion_pointsWithin
        B S hS 𝒳 Ω hΩopen)).mp
      (isOpenImmersion_fullSubcategoryInclusion_pointsWithin B S hS 𝒳 Ω hΩopen).2
      Q₁.pt h𝒰rep Q₁.snd Qin hQin Vops.toFunctor U hVopsopen.1 hU eQ eU
  have hrVbij : Function.Bijective (spacePointMap B S hS Vops.toFunctor Qin.pt
      (representationMap B S hS Vops.toFunctor Qin.pt eQ)) :=
    bijective_spacePointMap_representing B S hS Vops.toFunctor Qin.pt eQ
  have hi0nat : ∀ x, rU (Space.pointsMap B S hS Vops.toFunctor i0 x) =
      pointsMap B S hS Qin.pt.val Qin.pt.property Q₁.pt.property Qin.fst.hom
        (spacePointMap B S hS Vops.toFunctor Qin.pt
          (representationMap B S hS Vops.toFunctor Qin.pt eQ) x) :=
    fun x => representationMap_naturality B S hS Vops.toFunctor U Qin.pt Q₁.pt eQ eU Qin.fst x
  have hinclrange : Set.range (pointsMap B S hS (fullSubcategoryFibered 𝒳 (fun e =>
    pointsWithin_of_hom 𝒳 Ω e)).val
      (fullSubcategoryFibered 𝒳 (fun e => pointsWithin_of_hom 𝒳 Ω e)).property 𝒳.val.property
        incl.hom) = Ω :=
    pointSet_pointsWithinOpenSubstack B S hS 𝒳 Ω hΩopen
  have hQinrange : Set.range (pointsMap B S hS Qin.pt.val Qin.pt.property Q₁.pt.property
      Qin.fst.hom) =
      pointsMap B S hS Q₁.pt.val Q₁.pt.property 𝒳.val.property Q₁.snd.hom ⁻¹' Ω := by
    have h := range_pointsMap_snd_eq_preimage_range B S hS Qin.swap
      (Bicategory.isTwoFibreProduct_swap hQin)
    rw [hinclrange] at h
    exact h
  have hi0range : Set.range (Space.pointsMap B S hS Vops.toFunctor i0) = Wpts := by
    rw [← key, hcmp, Set.preimage_comp, ← hQinrange]
    refine subset_antisymm ?_ ?_
    · rintro _ ⟨x, rfl⟩
      rw [Set.mem_preimage, hi0nat x]
      exact ⟨_, rfl⟩
    · intro z hz
      rw [Set.mem_preimage] at hz
      obtain ⟨r, hr⟩ := hz
      obtain ⟨x, hx⟩ := hrVbij.surjective r
      exact ⟨x, hrUbij.injective (by rw [hi0nat x, hx, hr])⟩
  have hmonoi0 : Mono i0 := Space.mono_of_isOpenImmersion B S hS i0 hi0oi
  have hi0rng : Subfunctor.range i0 = W.1 := by
    refine le_antisymm (Space.le_of_range_pointsMap_ι_subset B S hS W.2 ?_)
      (Space.le_of_range_pointsMap_ι_subset B S hS
        (Space.isOpenSubspace_subfunctorRange B S hS hVopsopen.1 hi0oi) ?_)
    · rw [Space.range_pointsMap_ι_range, hi0range]
    · rw [Space.range_pointsMap_ι_range, hi0range]
  have hsurjc : Function.Surjective (pointsMap B S hS
      (schemeFibredCategory B S hS Vo).val (schemeFibredCategory B S hS Vo).property
      𝒴.val.property c.hom) :=
    (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS
      (𝒳 := (⟨schemeFibredCategory B S hS Vo, h𝒱alg⟩ : AlgebraicStacks.{u, w} B S hS))
      (𝒴 := 𝒴) (Bicategory.InducedBicategory.mkHom c) hcrep).2 hcsurj
  have hQ₁sndsurj : Function.Surjective (pointsMap B S hS Q₁.pt.val Q₁.pt.property
      𝒳.val.property Q₁.snd.hom) := by
    exact surjective_pointsMap_snd_of_surjective B S hS Q₁ hQ₁ hsurjc
  refine ⟨U, hU, eU, W, 𝒲, hW, ⟨?_, ?_⟩,
    by rw [h𝒲def, pointSet_pointsWithinOpenSubstack, ← hkkdef, ← hWptsdef]; exact key,
    by rw [h𝒲def, pointSet_pointsWithinOpenSubstack]
       exact pointsWithinOpenSubstack_property B S hS 𝒳 Ω hΩopen⟩
  · refine (hasRelativeProperty_iff_prop_representingMap_of_fppf.{u, u} B S hS P
      (fullSubcategoryAlgebraicStack 𝒳 𝒲.property 𝒲.isAlgebraic).val 𝒴.val
      (schemeFibredCategory B S hS Vo)
      (fullSubcategoryInclusion 𝒳 𝒲.property 𝒲.isAlgebraic ≫ f).hom c _ hcrep
      (fun V y hy G hG he => ⟨hcsurj V y hy G hG he,
        Space.isFlat_of_isSmooth B S hS _ (hcsm V y hy G hG he),
        Space.isLocallyOfFinitePresentation_of_isSmooth B S hS (hcsm V y hy G hG he)⟩)
      (Q₁.paste Qin) hQout Vops.toFunctor (yoneda.obj Vo) hVopsopen.1 hVp eQ eV).mpr ?_
    rw [representingMap_paste_fst B S hS Q₁ Qin Vops.toFunctor U (yoneda.obj Vo) eQ eU eV,
      ← hi0def, ← hf'def, property_comp_iff_property_range_ι_comp B S hS P hVopsopen.1 hVp hi0oi]
    have htr : ∀ (Z : Subfunctor U) (hZ : Space.IsOpenSubspace B S hS Z), Z = W.1 →
        P (ObjectProperty.homMk (X := (⟨Z.toFunctor, hZ.1⟩ : AlgebraicSpaces B S hS))
          (Y := (⟨yoneda.obj Vo, hVp⟩ : AlgebraicSpaces B S hS)) (Z.ι ≫ f')) := by
      rintro Z hZ rfl
      exact hW.1
    exact htr _ (Space.isOpenSubspace_subfunctorRange B S hS hVopsopen.1 hi0oi) hi0rng
  · intro V hV
    obtain ⟨VV, hVV, ⟨eVV⟩⟩ : IsRepresentableByAlgebraicSpace B S hS
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Q₁.snd
          (fullSubcategoryInclusion 𝒳 V.property V.isAlgebraic).hom).pt :=
      isRepresentableByAlgebraicSpace_twoFibreProduct.{u, u, u + 1, u, u + 1, u, u + 1}
        B S hS 𝒳.val Q₁.pt (fullSubcategoryAlgebraicStack 𝒳 V.property V.isAlgebraic).val
        Q₁.snd.hom (fullSubcategoryInclusion 𝒳 V.property V.isAlgebraic).hom.hom
        V.isOpenImmersion.1 h𝒰rep
    set QinV := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Q₁.snd
      (fullSubcategoryInclusion 𝒳 V.property V.isAlgebraic).hom with hQinVdef
    have hQinV : Bicategory.IsTwoFibreProduct QinV :=
      CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        Q₁.snd (fullSubcategoryInclusion 𝒳 V.property V.isAlgebraic).hom
    have hQoutV : Bicategory.IsTwoFibreProduct (Q₁.paste QinV) :=
      Bicategory.isTwoFibreProduct_pasteSnd Q₁ hQ₁ QinV hQinV
    set jV := representingMap B S hS QinV.pt Q₁.pt VV U eVV eU QinV.fst with hjVdef
    have hjVoi : Space.IsOpenImmersion B S hS jV :=
      (hasRelativeProperty_iff_forall_space_baseChange.{u, u} B S hS
        (Space.openImmersionProperty B S hS)
        (fullSubcategoryInclusion 𝒳 V.property V.isAlgebraic).hom
        V.isOpenImmersion.1).mp V.isOpenImmersion.2
        Q₁.pt h𝒰rep Q₁.snd QinV hQinV VV U hVV hU eVV eU
    have hPjV : P (ObjectProperty.homMk (X := (⟨VV, hVV⟩ : AlgebraicSpaces B S hS))
        (Y := (⟨yoneda.obj Vo, hVp⟩ : AlgebraicSpaces B S hS)) (jV ≫ f')) := by
      have h := (hasRelativeProperty_iff_forall_space_baseChange.{u, u} B S hS P
        (fullSubcategoryInclusion 𝒳 V.property V.isAlgebraic ≫ f).hom _).mp hV
        (schemeFibredCategory B S hS Vo) h𝒱rep c (Q₁.paste QinV) hQoutV VV (yoneda.obj Vo)
        hVV hVp eVV eV
      rwa [representingMap_paste_fst B S hS Q₁ QinV VV U (yoneda.obj Vo) eVV eU eV] at h
    have hjVptsle := range_pointsMap_subset_of_property_comp B S hS P hVV hVp hjVoi hW hPjV
    have hrVVbij : Function.Bijective (spacePointMap B S hS VV QinV.pt
        (representationMap B S hS VV QinV.pt eVV)) :=
      bijective_spacePointMap_representing B S hS VV QinV.pt eVV
    have hjVnat : ∀ x, rU (Space.pointsMap B S hS VV jV x) =
        pointsMap B S hS QinV.pt.val QinV.pt.property Q₁.pt.property QinV.fst.hom
          (spacePointMap B S hS VV QinV.pt (representationMap B S hS VV QinV.pt eVV) x) :=
      fun x => representationMap_naturality B S hS VV U QinV.pt Q₁.pt eVV eU QinV.fst x
    have hQinVrange : Set.range (pointsMap B S hS QinV.pt.val QinV.pt.property Q₁.pt.property
        QinV.fst.hom) =
        pointsMap B S hS Q₁.pt.val Q₁.pt.property 𝒳.val.property Q₁.snd.hom ⁻¹'
          Set.range (pointsMap B S hS
            (fullSubcategoryAlgebraicStack 𝒳 V.property V.isAlgebraic).val.val
            (fullSubcategoryAlgebraicStack 𝒳 V.property V.isAlgebraic).val.property
            𝒳.val.property (fullSubcategoryInclusion 𝒳 V.property V.isAlgebraic).hom.hom) := by
      exact range_pointsMap_snd_eq_preimage_range B S hS QinV.swap
        (Bicategory.isTwoFibreProduct_swap hQinV)
    have hVΩ : Set.range (pointsMap B S hS
        (fullSubcategoryAlgebraicStack 𝒳 V.property V.isAlgebraic).val.val
        (fullSubcategoryAlgebraicStack 𝒳 V.property V.isAlgebraic).val.property
        𝒳.val.property (fullSubcategoryInclusion 𝒳 V.property V.isAlgebraic).hom.hom) ⊆ Ω := by
      intro ξ hξ
      obtain ⟨u, hu⟩ := hQ₁sndsurj ξ
      obtain ⟨z, hz⟩ := hrUbij.surjective u
      have humem : u ∈ Set.range (pointsMap B S hS QinV.pt.val QinV.pt.property
          Q₁.pt.property QinV.fst.hom) := by
        rw [hQinVrange, Set.mem_preimage, hu]
        exact hξ
      obtain ⟨r, hr⟩ := humem
      obtain ⟨x, hx⟩ := hrVVbij.surjective r
      have hzx : Space.pointsMap B S hS VV jV x = z :=
        hrUbij.injective (by rw [hjVnat x, hx, hr, hz])
      have hzW : z ∈ Wpts := hjVptsle ⟨x, hzx⟩
      rw [hΩdef]
      refine ⟨z, hzW, ?_⟩
      rw [hcmp]
      simpa [hz] using hu
    intro x hx q φ
    have := V.strictlyFull
    exact hVΩ ((OpenSubstack.mem_pointSet_iff B S hS V _).2
      ⟨q, prop_of_isHomLift B S hS V.isAlgebraic (𝒳.val.val.p.map φ) φ
        inferInstance hx, rfl⟩)

/-- **The existence of the maximal open substack on which a relative property holds.** Let `P`,
`Q`, `R` be properties of morphisms of algebraic spaces over `S` which are fppf local on the target
and stable under arbitrary base change, with smoothness implying `R`, with every morphism of
algebraic spaces having `Q` carrying a greatest open subspace of its source on which it has `P`,
and with that greatest open subspace compatible with base change along a morphism with `R`. Then
a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` representable by algebraic spaces and
having `Q` has an open substack of `𝒳` on which it restricts to a 1-morphism with the relative
property `P` of **Stacks 03YK** and which contains every open substack with that property. -/
@[stacks 06M3 "assertion (A), the existence of the largest open substack of the source on which \
a 1-morphism representable by algebraic spaces and having Q has P, from the four hypotheses of \
the source on P, Q and R, by the chart construction of the source"]
theorem exists_isRelativePropertyLocus_of_hasRelativePropertyLocusOnSpaces
    (P Q R : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    [Q.IsStableUnderBaseChange]
    [Q.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    [R.IsStableUnderBaseChange]
    [R.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    (hsmR : SmoothImplies B S hS R)
    (h3 : HasRelativePropertyLocusOnSpaces B S hS P Q)
    (h4 : RelativePropertyLocusBaseChange B S hS P Q R)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hQf : HasRelativeProperty.{u, u, u + 1, u} B S hS Q f.hom hf) :
    ∃ W : OpenSubstack 𝒳, IsRelativePropertyLocus B S hS P f hf W := by
  obtain ⟨hfib, -, -, Vo, cV, hcVrep, hcVatlas⟩ := 𝒴.property
  obtain ⟨-, -, -, -, 𝒲, -, h𝒲, -, -⟩ :=
    exists_isRelativePropertyLocus_of_chart B S hS P Q R hsmR h3 h4 f hf hQf Vo
      (Bicategory.InducedBicategory.mkHom cV) hcVrep
      (fun V y hy G hG he => (hcVatlas V y hy G hG he).1)
      (fun V y hy G hG he => (hcVatlas V y hy G hG he).2)
  exact ⟨𝒲, h𝒲⟩

end Chart

/-! ### The maximality half of assertion (B) -/

section BaseChangeMaximality

variable (P Q R : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    [Q.IsStableUnderBaseChange]
    [Q.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    [R.IsStableUnderBaseChange]
    [R.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]

/-- **The maximality half of assertion (B) of Stacks 06M3, for every open substack with `P`.**
Let `P`, `Q`, `R` satisfy the hypotheses of Stacks 06M3, let `f : 𝒳 ⟶ 𝒴` be
representable by algebraic spaces and have `Q`, let `g : 𝒵 ⟶ 𝒴` be representable by algebraic
spaces and have `R`, let `D` be a 2-fibre product square over the cospan `(g, f)` and let `W` be
the `P`-locus of `f`. Then **every** open substack `V` of the apex on which the base change
`D.fst` has the relative property `P` is carried by the other projection into `W`. -/
theorem property_baseChange_of_hasRelativeProperty
    (hsmR : SmoothImplies B S hS R)
    (h3 : HasRelativePropertyLocusOnSpaces B S hS P Q)
    (h4 : RelativePropertyLocusBaseChange B S hS P Q R)
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴} {g : 𝒵 ⟶ 𝒴}
    {hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom}
    {hg : IsRepresentableByAlgebraicSpaces B S hS g.hom.hom}
    (hQf : HasRelativeProperty.{u, u, u + 1, u} B S hS Q f.hom hf)
    (hRg : HasRelativeProperty.{u, u, u + 1, u} B S hS R g.hom hg)
    (D : Bicategory.TwoCommSq g f) (hD : Bicategory.IsTwoFibreProduct D)
    {hfst : IsRepresentableByAlgebraicSpaces B S hS D.fst.hom.hom}
    {W : OpenSubstack 𝒳} (hW : IsRelativePropertyLocus B S hS P f hf W)
    (V : OpenSubstack D.pt)
    (hV : HasRelativeProperty B S hS P
      (fullSubcategoryInclusion D.pt V.property V.isAlgebraic ≫ D.fst).hom
      (isRepresentableByAlgebraicSpaces_fullSubcategoryInclusion_comp B S hS D.fst hfst V))
    {x : D.pt.val.val.obj} (hx : V.property x) :
    W.property (D.snd.hom.hom.toFunctor.obj x) := by
  classical
  have : (Space.openImmersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.openImmersion_isLocalAtTarget_fppf.{u, u} B S hS
  obtain ⟨hfib, -, -, Vo, cV, hcrep, hcatlas⟩ := 𝒴.property
  set c : schemeFibredCategory B S hS Vo ⟶ 𝒴.val :=
    Bicategory.InducedBicategory.mkHom cV with hcdef
  have hVp : IsAlgebraicSpace B S hS (yoneda.obj Vo) := isAlgebraicSpace_yoneda B S hS Vo
  have h𝒱rep : IsRepresentableByAlgebraicSpace B S hS (schemeFibredCategory B S hS Vo) :=
    ⟨yoneda.obj Vo, hVp, ⟨PresheafOfCategories.sliceElementsEquivalenceOver.{u} Vo⟩⟩
  have h𝒱alg : IsAlgebraicStack.{u, w} B S hS (schemeFibredCategory B S hS Vo).val :=
    isAlgebraicStack_schemeFibredCategory.{u, w} B S hS Vo
  have hcsurj : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) c hcrep :=
    fun V y hy G hG he => (hcatlas V y hy G hG he).1
  have hcsm : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.smoothMorphismProperty B S hS) c hcrep :=
    fun V y hy G hG he => (hcatlas V y hy G hG he).2
  obtain ⟨U, hU, eU, WU, 𝒲, hWU, h𝒲, hkey, hpts⟩ :=
    exists_isRelativePropertyLocus_of_chart B S hS P Q R hsmR h3 h4 f hf hQf Vo c hcrep
      hcsurj hcsm
  rw [eq_of_isRelativePropertyLocus B S hS P hW h𝒲]
  have hQ₁ : Bicategory.IsTwoFibreProduct
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} c f.hom) :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} c f.hom
  have h𝒰rep : IsRepresentableByAlgebraicSpace B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} c f.hom).pt :=
    ⟨U, hU, ⟨eU⟩⟩
  have hK : Bicategory.IsTwoFibreProduct
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} c g.hom) :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} c g.hom
  obtain ⟨Ts, hTs, ⟨eT⟩⟩ : IsRepresentableByAlgebraicSpace B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} c g.hom).pt :=
    isRepresentableByAlgebraicSpace_twoFibreProduct.{u, u, u + 1, u, u + 1, u, u + 1}
      B S hS 𝒴.val (schemeFibredCategory B S hS Vo) 𝒵.val c.hom g.hom.hom hg h𝒱rep
  have h𝒯rep : IsRepresentableByAlgebraicSpace B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} c g.hom).pt :=
    ⟨Ts, hTs, ⟨eT⟩⟩
  revert eU hWU hkey hQ₁ h𝒰rep eT h𝒯rep hK
  set Q₁ := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} c f.hom with hQ₁def
  set KK := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} c g.hom with hKKdef
  intro eU hWU hkey hQ₁ h𝒰rep hK eT h𝒯rep
  have hKfstrep : IsRepresentableByAlgebraicSpaces B S hS KK.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _ g.hom c KK hK hg
  have hRt : R (ObjectProperty.homMk (representingMap B S hS KK.pt
      (schemeFibredCategory B S hS Vo) Ts (yoneda.obj Vo) eT
      (PresheafOfCategories.sliceElementsEquivalenceOver.{u} Vo) KK.fst) :
      (⟨Ts, hTs⟩ : AlgebraicSpaces B S hS) ⟶ ⟨yoneda.obj Vo, hVp⟩) :=
    (hasRelativeProperty_iff_forall_space_baseChange.{u, u} B S hS R g.hom hg).mp hRg
      (schemeFibredCategory B S hS Vo) h𝒱rep c KK hK Ts (yoneda.obj Vo) hTs hVp eT
      (PresheafOfCategories.sliceElementsEquivalenceOver.{u} Vo)
  have hQf' : Q (ObjectProperty.homMk (representingMap B S hS Q₁.pt
      (schemeFibredCategory B S hS Vo) U (yoneda.obj Vo) eU
      (PresheafOfCategories.sliceElementsEquivalenceOver.{u} Vo) Q₁.fst) :
      (⟨U, hU⟩ : AlgebraicSpaces B S hS) ⟶ ⟨yoneda.obj Vo, hVp⟩) :=
    (hasRelativeProperty_iff_forall_space_baseChange.{u, u} B S hS Q f.hom hf).mp hQf
      (schemeFibredCategory B S hS Vo) h𝒱rep c Q₁ hQ₁ U (yoneda.obj Vo) hU hVp eU
      (PresheafOfCategories.sliceElementsEquivalenceOver.{u} Vo)
  have hDc : Bicategory.IsTwoFibreProduct D.underlying :=
    Bicategory.isTwoFibreProduct_underlying (twoFibreProductSquareAlgebraicStacks B S hS g f) hD
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        g.hom f.hom)
  have hQDc : HasRelativeProperty.{u, u, u + 1, u} B S hS Q D.fst.hom hfst :=
    hasRelativeProperty_baseChange.{u, u, u + 1} B S hS Q 𝒳.val 𝒴.val 𝒵.val f.hom g.hom
      D.underlying hDc hf hQf
  have hΛ : Bicategory.IsTwoFibreProduct
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd) :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _
  obtain ⟨As, hAs, ⟨eA⟩⟩ : IsRepresentableByAlgebraicSpace B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).pt :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS _ _ _
      D.fst.hom KK.snd
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).swap
      (Bicategory.isTwoFibreProduct_swap hΛ) hfst h𝒯rep
  have hΛrep : IsRepresentableByAlgebraicSpace B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).pt :=
    ⟨As, hAs, ⟨eA⟩⟩
  have hQfA : Q (ObjectProperty.homMk (representingMap B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).pt
      KK.pt As Ts eA eT
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).snd) :
      (⟨As, hAs⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Ts, hTs⟩) :=
    (hasRelativeProperty_iff_forall_space_baseChange.{u, u} B S hS Q D.fst.hom hfst).mp
      hQDc KK.pt h𝒯rep KK.snd
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).swap
      (Bicategory.isTwoFibreProduct_swap hΛ) As Ts hAs hTs eA eT
  obtain ⟨WA, hWA⟩ := h3 As Ts hAs hTs _ hQfA
  have hcmpD : (CatFiberedInGroupoids.canonicalPreHom.{u, u, u + 1, u + 1} f.hom g.hom
      D.underlying.swap).hom.hom.toFunctor.IsEquivalence :=
    Bicategory.isEquivalence_of_isTwoFibreProduct (Bicategory.isTwoFibreProduct_swap hDc)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        f.hom g.hom)
      (CatFiberedInGroupoids.canonicalPreHom.{u, u, u + 1, u + 1} f.hom g.hom D.underlying.swap)
  have hcmpQ : (CatFiberedInGroupoids.canonicalPreHom.{u, u, u + 1, u + 1} f.hom c
      Q₁.swap).hom.hom.toFunctor.IsEquivalence :=
    Bicategory.isEquivalence_of_isTwoFibreProduct (Bicategory.isTwoFibreProduct_swap hQ₁)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom c)
      (CatFiberedInGroupoids.canonicalPreHom.{u, u, u + 1, u + 1} f.hom c Q₁.swap)
  have hAsq := CatFiberedInGroupoids.isTwoFibreProduct_cancelSndEquivSquare.{u, u, u + 1, u + 1}
    f.hom g.hom
    (CatFiberedInGroupoids.canonicalPreHom.{u, u, u + 1, u + 1} f.hom g.hom D.underlying.swap).hom
    KK.snd (KK.fst ≫ c) KK.iso.symm hcmpD
  have hBsq := CatFiberedInGroupoids.isTwoFibreProduct_cancelSndEquivSquare.{u, u, u + 1, u + 1}
    f.hom c
    (CatFiberedInGroupoids.canonicalPreHom.{u, u, u + 1, u + 1} f.hom c Q₁.swap).hom
    KK.fst (KK.fst ≫ c) (Iso.refl _) hcmpQ
  set cmp3 := (hBsq.from (CatFiberedInGroupoids.cancelSndEquivSquare.{u, u, u + 1, u + 1} f.hom
    g.hom
    (CatFiberedInGroupoids.canonicalPreHom.{u, u, u + 1, u + 1} f.hom g.hom D.underlying.swap).hom
    KK.snd (KK.fst ≫ c) KK.iso.symm)).out with hcmp3def
  have hcmp3eq : cmp3.hom.hom.toFunctor.IsEquivalence :=
    Bicategory.isEquivalence_of_isTwoFibreProduct hAsq hBsq cmp3
  have p3iso : (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        D.fst.hom KK.snd).snd ≅
      cmp3.hom ≫ (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        Q₁.fst KK.fst).snd :=
    cmp3.isoSnd
  have p3isoFst : (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        D.fst.hom KK.snd).fst ≫ D.snd.hom ≅
      cmp3.hom ≫ ((CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        Q₁.fst KK.fst).fst ≫ Q₁.snd) :=
    cmp3.isoFst
  have hR3 : Bicategory.IsTwoFibreProduct
      ((CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        Q₁.fst KK.fst).precompose cmp3.hom) :=
    Bicategory.isTwoFibreProduct_of_isEquivalence_to
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        Q₁.fst KK.fst)
      (Bicategory.TwoCommSq.PreHom.ofPrecompose
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Q₁.fst KK.fst)
        cmp3.hom) hcmp3eq
  obtain ⟨Xs, hXs, ⟨eC⟩⟩ : IsRepresentableByAlgebraicSpace B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Q₁.fst KK.fst).pt :=
    isRepresentableByAlgebraicSpace_twoFibreProduct.{u, u, u + 1, u, u + 1, u, u + 1}
      B S hS (schemeFibredCategory B S hS Vo) Q₁.pt KK.pt Q₁.fst.hom KK.fst.hom hKfstrep h𝒰rep
  have hsq := isPullback_representingMap_of_isTwoFibreProduct B S hS hR3 U Ts (yoneda.obj Vo)
    As Xs eU eT (PresheafOfCategories.sliceElementsEquivalenceOver.{u} Vo) eA eC
  rw [representingMap_congr_twoIso B S hS As Ts eA eT p3iso] at hQfA
  obtain ⟨WA, hWA⟩ := h3 As Ts hAs hTs _ hQfA
  have hWAeq := h4 As U Ts (yoneda.obj Vo) hAs hU hTs hVp _ _ _ _ hsq hQf' hRt WU hWU WA hWA
  have hWAeq' : WA.1 = WU.1.preimage (representingMap B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).pt
      Q₁.pt As U eA eU
      (cmp3.hom ≫ (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        Q₁.fst KK.fst).fst)) := hWAeq
  have hQinV : Bicategory.IsTwoFibreProduct
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).fst
        (fullSubcategoryInclusion D.pt V.property V.isAlgebraic).hom) :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _
  obtain ⟨VV, hVV, ⟨eVV⟩⟩ : IsRepresentableByAlgebraicSpace B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).fst
        (fullSubcategoryInclusion D.pt V.property V.isAlgebraic).hom).pt :=
    isRepresentableByAlgebraicSpace_twoFibreProduct.{u, u, u + 1, u, u + 1, u, u + 1}
      B S hS D.pt.val
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).pt
      (fullSubcategoryAlgebraicStack D.pt V.property V.isAlgebraic).val
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).fst.hom
      (fullSubcategoryInclusion D.pt V.property V.isAlgebraic).hom.hom
      V.isOpenImmersion.1 hΛrep
  have hQoutV : Bicategory.IsTwoFibreProduct
      ((CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          D.fst.hom KK.snd).swap.paste
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).fst
          (fullSubcategoryInclusion D.pt V.property V.isAlgebraic).hom)) :=
    Bicategory.isTwoFibreProduct_pasteSnd _ (Bicategory.isTwoFibreProduct_swap hΛ) _ hQinV
  have hswapfst : (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      D.fst.hom KK.snd).swap.fst =
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).snd :=
    rfl
  have hcongrswap := representingMap_congr_twoIso B S hS
    (𝒜 := (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      D.fst.hom KK.snd).swap.pt) As Ts eA eT p3iso
  have hPjV := (hasRelativeProperty_iff_forall_space_baseChange.{u, u} B S hS P
      (fullSubcategoryInclusion D.pt V.property V.isAlgebraic ≫ D.fst).hom
      (isRepresentableByAlgebraicSpaces_fullSubcategoryInclusion_comp B S hS D.fst hfst V)).mp hV
      KK.pt h𝒯rep KK.snd _ hQoutV VV Ts hVV hTs eVV eT
  rw [representingMap_paste_fst B S hS
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).swap
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).fst
      (fullSubcategoryInclusion D.pt V.property V.isAlgebraic).hom) VV As Ts eVV eA eT,
    hswapfst, hcongrswap] at hPjV
  set fA := (representingMap B S hS (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u +
    1} D.fst.hom KK.snd).pt KK.pt As Ts eA eT (cmp3.hom ≫
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Q₁.fst KK.fst).snd)) with
    hfAdef
  set aU := (representingMap B S hS (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u +
    1} D.fst.hom KK.snd).pt Q₁.pt As U eA eU (cmp3.hom ≫
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Q₁.fst KK.fst).fst)) with
    haUdef
  set jV := (representingMap B S hS (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u +
    1} (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).fst
        (fullSubcategoryInclusion D.pt V.property V.isAlgebraic).hom).pt
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).pt VV
          As eVV eA (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).fst
        (fullSubcategoryInclusion D.pt V.property V.isAlgebraic).hom).fst) with hjVdef
  have hjVoi : Space.IsOpenImmersion B S hS jV :=
    (hasRelativeProperty_iff_forall_space_baseChange.{u, u} B S hS
      (Space.openImmersionProperty B S hS)
      (fullSubcategoryInclusion D.pt V.property V.isAlgebraic).hom
      V.isOpenImmersion.1).mp V.isOpenImmersion.2 (CatFiberedInGroupoids.twoFibreProductSquare.{u,
        u, u + 1, u + 1} D.fst.hom KK.snd).pt hΛrep
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).fst
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).fst
        (fullSubcategoryInclusion D.pt V.property V.isAlgebraic).hom) hQinV VV As
      hVV hAs eVV eA
  have hjVptsle := range_pointsMap_subset_of_property_comp B S hS P hVV hTs hjVoi hWA hPjV
  have hWApts : Set.range (Space.pointsMap B S hS WA.1.toFunctor WA.1.ι) =
      Space.pointsMap B S hS As aU ⁻¹'
        Set.range (Space.pointsMap B S hS WU.1.toFunctor WU.1.ι) := by
    rw [hWAeq', range_pointsMap_preimage_eq]
  have hrAbij : Function.Bijective (spacePointMap B S hS As
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).pt
      (representationMap B S hS As (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u +
        1} D.fst.hom KK.snd).pt eA)) :=
    bijective_spacePointMap_representing B S hS As (CatFiberedInGroupoids.twoFibreProductSquare.{u,
      u, u + 1, u + 1} D.fst.hom KK.snd).pt eA
  have hrVVbij : Function.Bijective (spacePointMap B S hS VV
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).fst
        (fullSubcategoryInclusion D.pt V.property V.isAlgebraic).hom).pt
      (representationMap B S hS VV (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u +
        1} (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).fst
        (fullSubcategoryInclusion D.pt V.property V.isAlgebraic).hom).pt eVV)) :=
    bijective_spacePointMap_representing B S hS VV (CatFiberedInGroupoids.twoFibreProductSquare.{u,
      u, u + 1, u + 1} (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom
      KK.snd).fst
        (fullSubcategoryInclusion D.pt V.property V.isAlgebraic).hom).pt eVV
  have hjVnat : ∀ y, spacePointMap B S hS As (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u
    + 1, u + 1} D.fst.hom KK.snd).pt (representationMap B S hS As
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).pt eA)
      (Space.pointsMap B S hS VV jV y) =
      pointsMap B S hS (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).fst
        (fullSubcategoryInclusion D.pt V.property V.isAlgebraic).hom).pt.val
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).fst
        (fullSubcategoryInclusion D.pt V.property V.isAlgebraic).hom).pt.property
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom
          KK.snd).pt.property (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).fst
        (fullSubcategoryInclusion D.pt V.property V.isAlgebraic).hom).fst.hom
        (spacePointMap B S hS VV (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).fst
        (fullSubcategoryInclusion D.pt V.property V.isAlgebraic).hom).pt (representationMap B S hS
          VV (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).fst
        (fullSubcategoryInclusion D.pt V.property V.isAlgebraic).hom).pt eVV) y) :=
    fun y => representationMap_naturality B S hS VV As
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).fst
        (fullSubcategoryInclusion D.pt V.property V.isAlgebraic).hom).pt
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).pt
          eVV eA (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).fst
        (fullSubcategoryInclusion D.pt V.property V.isAlgebraic).hom).fst y
  have hQinVrange : Set.range (pointsMap B S hS (CatFiberedInGroupoids.twoFibreProductSquare.{u, u,
    u + 1, u + 1} (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom
    KK.snd).fst
        (fullSubcategoryInclusion D.pt V.property V.isAlgebraic).hom).pt.val
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).fst
        (fullSubcategoryInclusion D.pt V.property V.isAlgebraic).hom).pt.property
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom
        KK.snd).pt.property (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).fst
        (fullSubcategoryInclusion D.pt V.property V.isAlgebraic).hom).fst.hom) =
      pointsMap B S hS (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom
        KK.snd).pt.val (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom
        KK.snd).pt.property D.pt.val.property (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u
        + 1, u + 1} D.fst.hom KK.snd).fst.hom ⁻¹'
        (V.pointSet B S hS) := by
    exact range_pointsMap_snd_eq_preimage_range B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).fst
        (fullSubcategoryInclusion D.pt V.property V.isAlgebraic).hom).swap
      (Bicategory.isTwoFibreProduct_swap hQinV)
  have hcsurjpts : Function.Surjective (pointsMap B S hS
      (schemeFibredCategory B S hS Vo).val (schemeFibredCategory B S hS Vo).property
      𝒴.val.property c.hom) :=
    (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS
      (𝒳 := (⟨schemeFibredCategory B S hS Vo, h𝒱alg⟩ : AlgebraicStacks.{u, w} B S hS))
      (𝒴 := 𝒴) (Bicategory.InducedBicategory.mkHom c) hcrep).2 hcsurj
  have hKsndsurjpts : Function.Surjective (pointsMap B S hS KK.pt.val KK.pt.property
      𝒵.val.property KK.snd.hom) := by
    exact surjective_pointsMap_snd_of_surjective B S hS KK hK hcsurjpts
  have hΛfstsurj : Function.Surjective (pointsMap B S hS
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).pt.val
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).pt.property
      D.pt.val.property (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom
        KK.snd).fst.hom) := by
    exact surjective_pointsMap_snd_of_surjective B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).swap
      (Bicategory.isTwoFibreProduct_swap hΛ) hKsndsurjpts
  have hpointset : ∀ ζ ∈ V.pointSet B S hS,
      pointsMap B S hS D.pt.val.val D.pt.val.property 𝒳.val.property D.snd.hom.hom ζ ∈
        𝒲.pointSet B S hS := by
    intro ζ hζ
    obtain ⟨α, hα⟩ := hΛfstsurj ζ
    obtain ⟨z, hz⟩ := hrAbij.surjective α
    have hαmem : α ∈ Set.range (pointsMap B S hS (CatFiberedInGroupoids.twoFibreProductSquare.{u,
      u, u + 1, u + 1} (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom
      KK.snd).fst
        (fullSubcategoryInclusion D.pt V.property V.isAlgebraic).hom).pt.val
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).fst
        (fullSubcategoryInclusion D.pt V.property V.isAlgebraic).hom).pt.property
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom
          KK.snd).pt.property (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).fst
        (fullSubcategoryInclusion D.pt V.property V.isAlgebraic).hom).fst.hom) := by
      rw [hQinVrange, Set.mem_preimage, hα]
      exact hζ
    obtain ⟨ρ, hρ⟩ := hαmem
    obtain ⟨y, hy⟩ := hrVVbij.surjective ρ
    have hzy : Space.pointsMap B S hS VV jV y = z :=
      hrAbij.injective (by rw [hjVnat y, hy, hρ, hz])
    have hzWA : z ∈ Space.pointsMap B S hS As aU ⁻¹'
        Set.range (Space.pointsMap B S hS WU.1.toFunctor WU.1.ι) := by
      rw [← hWApts]
      exact hjVptsle ⟨y, hzy⟩
    have hcmpU : spacePointMap B S hS U 𝒳.val
        (Bicategory.InducedBicategory.mkHom (representationMap B S hS U Q₁.pt eU) ≫
          Q₁.snd).hom =
        pointsMap B S hS Q₁.pt.val Q₁.pt.property 𝒳.val.property Q₁.snd.hom ∘
          spacePointMap B S hS U Q₁.pt (representationMap B S hS U Q₁.pt eU) :=
      spacePointMap_comp B S hS U Q₁.pt 𝒳.val (representationMap B S hS U Q₁.pt eU) Q₁.snd.hom
    rw [Set.mem_preimage, ← hkey, Set.mem_preimage, hcmpU, Function.comp_apply,
      representationMap_naturality B S hS As U (CatFiberedInGroupoids.twoFibreProductSquare.{u, u,
        u + 1, u + 1} D.fst.hom KK.snd).pt Q₁.pt eA eU
        (cmp3.hom ≫ (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Q₁.fst
          KK.fst).fst) z, hz, pointsMap_comp] at hzWA
    have hiso := congrFun (pointsMap_eq_of_basedNatTrans B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom KK.snd).pt.val
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom
        KK.snd).pt.property 𝒳.val.property p3isoFst.hom.hom) α
    have heq : pointsMap B S hS D.pt.val.val D.pt.val.property 𝒳.val.property D.snd.hom.hom
        (pointsMap B S hS (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          D.fst.hom KK.snd).pt.val (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u +
          1} D.fst.hom KK.snd).pt.property D.pt.val.property
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} D.fst.hom
          KK.snd).fst.hom α) =
        pointsMap B S hS (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          D.fst.hom KK.snd).pt.val (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u +
          1} D.fst.hom KK.snd).pt.property 𝒳.val.property
          (BasedFunctor.comp (cmp3.hom ≫ (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1,
            u + 1} Q₁.fst KK.fst).fst).hom Q₁.snd.hom) α := by
      rw [pointsMap_comp]
      exact hiso
    rw [← hα, heq]
    exact hzWA
  rw [hpts]
  refine pointsWithin_obj_of_pointsWithin_preimage B S hS (𝒜 := D.pt) D.snd.hom.hom
    (𝒲.pointSet B S hS) ?_
  intro r ρ
  have := V.strictlyFull
  exact hpointset _ ((OpenSubstack.mem_pointSet_iff B S hS V _).2
    ⟨r, prop_of_isHomLift B S hS V.isAlgebraic (D.pt.val.val.p.map ρ) ρ inferInstance hx, rfl⟩)

/-- **The locus of a base change is carried into the locus.** Let `P`, `Q`, `R` be properties of
morphisms of algebraic spaces over `S` satisfying the hypotheses of Stacks 06M3, let
`f : 𝒳 ⟶ 𝒴` be a 1-morphism representable by algebraic spaces having `Q`, let `g : 𝒵 ⟶ 𝒴` be
representable by algebraic spaces having `R` and let `D` be a 2-fibre product square over the
cospan `(g, f)`. If `W` is the `P`-locus of `f` and `W'` the `P`-locus of the base change
`D.fst`, then every object of the apex lying in `W'` is carried by `D.snd` into `W`: that is,
`W(P, f') ⊆ 𝒵 ×_𝒴 W(P, f)`. -/
@[stacks 06M3 "assertion (B), the maximality half: the locus of the base change is carried into \
the locus of the 1-morphism, so that together with the containment proved above the base change \
of the locus is the locus of the base change. From the four hypotheses of the source on P, Q and \
R, with Q for the 1-morphism and R for the base change as the source has them, by the source's \
chart construction run at one more base change"]
theorem isRelativePropertyLocus_baseChange_apply_symm
    (hsmR : SmoothImplies B S hS R)
    (h3 : HasRelativePropertyLocusOnSpaces B S hS P Q)
    (h4 : RelativePropertyLocusBaseChange B S hS P Q R)
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴} {g : 𝒵 ⟶ 𝒴}
    {hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom}
    {hg : IsRepresentableByAlgebraicSpaces B S hS g.hom.hom}
    (hQf : HasRelativeProperty.{u, u, u + 1, u} B S hS Q f.hom hf)
    (hRg : HasRelativeProperty.{u, u, u + 1, u} B S hS R g.hom hg)
    (D : Bicategory.TwoCommSq g f) (hD : Bicategory.IsTwoFibreProduct D)
    {hfst : IsRepresentableByAlgebraicSpaces B S hS D.fst.hom.hom}
    {W : OpenSubstack 𝒳} {W' : OpenSubstack D.pt}
    (hW : IsRelativePropertyLocus B S hS P f hf W)
    (hW' : IsRelativePropertyLocus B S hS P D.fst hfst W')
    {x : D.pt.val.val.obj} (hx : W'.property x) :
    W.property (D.snd.hom.hom.toFunctor.obj x) :=
  property_baseChange_of_hasRelativeProperty B S hS P Q R hsmR h3 h4 hQf hRg D hD
    (hfst := hfst) hW W' hW'.1 hx

/-- **The maximality half of assertion (B) of Stacks 06M3, read on points.** The point set of an
open substack of the apex on which the base change has the relative property `P` is contained in
the inverse image of the point set of the `P`-locus of `f`. -/
theorem pointSet_subset_preimage_of_hasRelativeProperty
    (hsmR : SmoothImplies B S hS R)
    (h3 : HasRelativePropertyLocusOnSpaces B S hS P Q)
    (h4 : RelativePropertyLocusBaseChange B S hS P Q R)
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴} {g : 𝒵 ⟶ 𝒴}
    {hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom}
    {hg : IsRepresentableByAlgebraicSpaces B S hS g.hom.hom}
    (hQf : HasRelativeProperty.{u, u, u + 1, u} B S hS Q f.hom hf)
    (hRg : HasRelativeProperty.{u, u, u + 1, u} B S hS R g.hom hg)
    (D : Bicategory.TwoCommSq g f) (hD : Bicategory.IsTwoFibreProduct D)
    {hfst : IsRepresentableByAlgebraicSpaces B S hS D.fst.hom.hom}
    {W : OpenSubstack 𝒳} (hW : IsRelativePropertyLocus B S hS P f hf W)
    (V : OpenSubstack D.pt)
    (hV : HasRelativeProperty B S hS P
      (fullSubcategoryInclusion D.pt V.property V.isAlgebraic ≫ D.fst).hom
      (isRepresentableByAlgebraicSpaces_fullSubcategoryInclusion_comp B S hS D.fst hfst V)) :
    V.pointSet B S hS ⊆
      AlgebraicStacks.pointsMap B S hS D.snd ⁻¹' W.pointSet B S hS := by
  intro ζ hζ
  obtain ⟨r, hr, rfl⟩ := (OpenSubstack.mem_pointSet_iff B S hS V ζ).1 hζ
  exact (OpenSubstack.mem_pointSet_iff B S hS W _).2
    ⟨fieldValuedPointMap B S hS D.pt.val.val D.snd.hom.hom r,
      property_baseChange_of_hasRelativeProperty B S hS P Q R hsmR h3 h4 hQf hRg D hD
        (hfst := hfst) hW V hV hr,
      rfl⟩

end BaseChangeMaximality

end AlgebraicGeometry.Stack

end
