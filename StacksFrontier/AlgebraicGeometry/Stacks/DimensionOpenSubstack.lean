module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartShrinkingQuasiFiniteEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionZeroOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubsetSeparationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenImageSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackCoverScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.Substack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtalePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocus

/-!
# The dimension of an algebraic stack along an open immersion

Let `j : 𝒱 ⟶ 𝒳` be an open immersion of locally Noetherian algebraic stacks over `S`. The
dimension of Stacks 0AFN is *local*: for `v ∈ |𝒱|` the dimension of `𝒳` at the image of `v` is
the dimension of `𝒱` at `v`. This is the step the statement of **Stacks 0DS1** needs in order to
compare `dim_{x₀}(𝒳)` with `dim_x(𝒱)` for an open substack `𝒱 ⊆ 𝒳`.

## Main results

* `AlgebraicGeometry.Stack.relativeStackDimensionAt_eq_zero_of_isOpenImmersion`: the relative
  dimension of Stacks 0DRL of an open immersion is `0`.
* `AlgebraicGeometry.Stack.dimensionAtPoint_pointsMap_eq_of_isOpenImmersion`: the dimension of
  Stacks 0AFN is unchanged by an open immersion.
* `AlgebraicGeometry.Stack.relativeStackDimensionAt_pointsMap_eq_of_isOpenImmersion`: the
  relative dimension of Stacks 0DRL is unchanged by precomposition with an open immersion.
* `AlgebraicGeometry.Stack.isLocallyNoetherianStack_toAlgebraicStack`: an open substack of a
  locally Noetherian algebraic stack is locally Noetherian.

## Implementation notes

The relative dimension of Stacks 0DRL of `j` at `v` is read off the fibre `𝒱 ×_𝒳 Spec k` over a
field-valued point of `𝒳` representing the image of `v`, by **Stacks 0DRM**. That fibre is
representable by an algebraic space, because `j` is representable by algebraic spaces, and its
projection to `Spec k` is an open immersion of algebraic spaces, being a base change of `j`; so
the fibre is étale over `Spec k` and has the dimension of `Spec k`, which is `0`.

The locality of the dimension then follows from the chart formula of **Stacks 0DRJ**: a smooth
chart `a : T ⟶ 𝒱` by an algebraic space is also a smooth chart of `𝒳`, an open immersion being
smooth (**Stacks 0CIP** and Stacks 075V), and the chart formula of **Stacks 0DRN** for the
relative dimension of `j` says that the two relative dimensions of `a` and of `a ≫ j` differ by
the relative dimension of `j`, which is `0`. Both dimensions are therefore the dimension of `T`
at the chart point minus one and the same natural number. The same comparison of the two charts
`a` and `a ≫ j` gives the relative statement: for a further 1-morphism `f : 𝒳 ⟶ 𝒴` locally of
finite type the relative dimensions of Stacks 0DRL of `f` at the image of `v` and of `j ≫ f` at
`v` are read off the one relative dimension of `a ≫ j ≫ f`, with the same subtrahend.

The universe `u` is that of the base scheme and of its relative big fppf site, while `w` is the
descent universe at which algebraicity is tested; the two are independent.

## References

* [Stacks Project, Tag 02IL](https://stacks.math.columbia.edu/tag/02IL)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
* [Stacks Project, Tag 0CIP](https://stacks.math.columbia.edu/tag/0CIP)
* [Stacks Project, Tag 0CPM](https://stacks.math.columbia.edu/tag/0CPM)
* [Stacks Project, Tag 0DRJ](https://stacks.math.columbia.edu/tag/0DRJ)
* [Stacks Project, Tag 0DRL](https://stacks.math.columbia.edu/tag/0DRL)
* [Stacks Project, Tag 0DRM](https://stacks.math.columbia.edu/tag/0DRM)
* [Stacks Project, Tag 0DRN](https://stacks.math.columbia.edu/tag/0DRN)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {𝒱 𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- **An open immersion of algebraic stacks is locally of finite type.** It is locally of finite
presentation by **Stacks 06Q7**. -/
theorem AlgebraicStacks.isLocallyOfFiniteType_of_isOpenImmersion (j : 𝒱 ⟶ 𝒳)
    (hj : AlgebraicStacks.IsOpenImmersion B S hS j) :
    AlgebraicStacks.IsLocallyOfFiniteType B S hS j :=
  AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
    (AlgebraicStacks.isLocallyOfFinitePresentation_of_isOpenImmersion B S hS j hj)

/-- **Stacks 0CPM at an open substack.** The source of an open immersion into a locally
Noetherian algebraic stack is locally Noetherian: an open immersion is an immersion. -/
theorem isLocallyNoetherianStack_of_isOpenImmersion (j : 𝒱 ⟶ 𝒳)
    (hj : AlgebraicStacks.IsOpenImmersion B S hS j)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳) :
    IsLocallyNoetherianStack.{u, w} B S hS 𝒱 :=
  AlgebraicStacks.isLocallyNoetherian_of_isImmersion B S hS j
    ⟨hj.1, fun U y hy F hF he =>
      Space.isImmersion_of_isOpenImmersion B S hS (hj.2 U y hy F hF he)⟩ h𝒳

/-- **An open substack of a locally Noetherian algebraic stack is locally Noetherian.** -/
theorem isLocallyNoetherianStack_toAlgebraicStack (𝒲 : OpenSubstack 𝒳)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳) :
    IsLocallyNoetherianStack.{u, w} B S hS
      (fullSubcategoryAlgebraicStack 𝒳 𝒲.property 𝒲.isAlgebraic) :=
  isLocallyNoetherianStack_of_isOpenImmersion B S hS 𝒲.inclusion 𝒲.isOpenImmersion h𝒳

/-- **The relative dimension of Stacks 0DRL of an open immersion is zero.** The fibre of `j` over
a field-valued point of `𝒳` is representable by an algebraic space which is étale over the field
spectrum, because the fibre's projection to the field spectrum is a base change of `j` and so an
open immersion; the dimension of the spectrum of a field being `0`, so is the dimension of the
fibre, and by **Stacks 0DRM** that value is the relative dimension. -/
theorem relativeStackDimensionAt_eq_zero_of_isOpenImmersion (j : 𝒱 ⟶ 𝒳)
    (hj : AlgebraicStacks.IsOpenImmersion B S hS j)
    (hjft : AlgebraicStacks.IsLocallyOfFiniteType B S hS j)
    (h𝒱 : IsLocallyNoetherianStack.{u, w} B S hS 𝒱)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (v : points B S hS 𝒱.val.val 𝒱.val.property) :
    relativeStackDimensionAt.{u, w} B S hS j hjft h𝒱 h𝒳 v = 0 := by
  classical
  obtain ⟨p, q, hp, hq⟩ := exists_admissible_fieldFibreStackDimensionAt B S hS j v
  rw [relativeStackDimensionAt_eq_fieldFibreStackDimensionAt.{u, w} B S hS j hjft h𝒱 h𝒳 v p q
    hp hq]
  have hsqc : Bicategory.IsTwoFibreProduct (fieldFibreStackSquare B S hS j p).underlying :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 p).hom j.hom
  have hZrep : IsRepresentableByAlgebraicSpace B S hS
      (fieldFibreStackSquare B S hS j p).pt.val :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
      𝒱.val 𝒳.val (schemeFibredCategory B S hS p.base) j.hom
      (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 p).hom _ hsqc hj.1
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS p.base)
  obtain ⟨W, hW, ⟨eW⟩⟩ := id hZrep
  obtain ⟨x, hx⟩ := (bijective_spacePointMap_representing B S hS W
    (fieldFibreStackSquare B S hS j p).pt.val eW).surjective q
  have hunfold : fieldFibreStackDimensionAt.{u, w} B S hS j hjft p q =
      dimensionAtPoint B S hS (fieldFibreStackSquare B S hS j p).pt
        (isLocallyNoetherianStack_fieldFibreStackSquare.{u, w} B S hS j hjft p) q := rfl
  rw [hunfold, dimensionAtPoint_eq_dimensionSubNat_zero_of_representing.{u, w} B S hS
    (fieldFibreStackSquare B S hS j p).pt
    (isLocallyNoetherianStack_fieldFibreStackSquare.{u, w} B S hS j hjft p) W hW eW x q hx]
  -- the fibre's projection to the field spectrum is an open immersion of algebraic spaces
  have hopenimm : Space.IsOpenImmersion B S hS
      (representingMap B S hS (fieldFibreStackSquare B S hS j p).pt.val
        (schemeFibredCategory B S hS p.base) W (yoneda.obj p.base) eW
        (PresheafOfCategories.sliceElementsEquivalenceOver p.base)
        (fieldFibreStackSquare B S hS j p).fst.hom) :=
    isOpenImmersion_representingMap B S hS (fieldFibreStackSquare B S hS j p).fst.hom
      (isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS
        𝒱.val 𝒳.val (schemeFibredCategory B S hS p.base) j.hom
        (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 p).hom _ hsqc hj.1)
      (isOpenImmersion_baseChange.{u, u, u + 1} B S hS
        𝒱.val 𝒳.val (schemeFibredCategory B S hS p.base) j.hom
        (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 p).hom _ hsqc hj.2)
      W (yoneda.obj p.base) hW (isAlgebraicSpace_yoneda B S hS p.base) eW
      (PresheafOfCategories.sliceElementsEquivalenceOver p.base)
  -- so the fibre has dimension zero at `x`
  have hdim : Space.dimensionAtPoint B S hS W hW x = 0 := by
    rw [Space.dimensionAtPoint_eq_of_isEtale B S hS hW (isAlgebraicSpace_yoneda B S hS p.base) _
      (Space.isEtale_of_isOpenImmersion B S hS hopenimm) x]
    have hsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj p.base) :=
      p.isSpec.hom.homeomorph.toEquiv.subsingleton
    have hne : Nonempty ((BigFppfOver.toScheme B S hS).obj p.base) :=
      ⟨p.isSpec.inv (IsLocalRing.closedPoint p.carrier)⟩
    refine le_antisymm ?_ (Space.zero_le_dimensionAtPoint B S hS
      (isAlgebraicSpace_yoneda B S hS p.base) _)
    refine le_trans (le_iSup (fun y => Space.dimensionAtPoint B S hS (yoneda.obj p.base)
      (isAlgebraicSpace_yoneda B S hS p.base) y) _) ?_
    exact le_of_eq ((Space.dimension_yoneda_eq_topologicalKrullDim B S hS p.base).trans
      topologicalKrullDim_eq_zero_of_discreteTopology_nonempty)
  rw [hdim]
  rfl

/-- A smooth chart `a` of `𝒱` above `v` composes with an open immersion `j` to a smooth chart of
`𝒳`, and the relative dimensions of `a` and `a ≫ j` at the chart point are the same natural
number `m`. -/
private theorem exists_chart_comp_isOpenImmersion (j : 𝒱 ⟶ 𝒳)
    (hj : AlgebraicStacks.IsOpenImmersion B S hS j)
    (h𝒱 : IsLocallyNoetherianStack.{u, w} B S hS 𝒱)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (v : points B S hS 𝒱.val.val 𝒱.val.property) :
    ∃ (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hT : IsAlgebraicSpace B S hS T)
      (a : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒱) (u : Space.points B S hS T) (m : ℕ)
      (_ : AlgebraicStacks.IsSmooth B S hS a)
      (ha : AlgebraicStacks.IsLocallyOfFiniteType B S hS a)
      (_ : AlgebraicStacks.IsSmooth B S hS (a ≫ j))
      (hbft : AlgebraicStacks.IsLocallyOfFiniteType B S hS (a ≫ j)),
      pointsMap B S hS (fibredCategory B S hS T).val (fibredCategory B S hS T).property
        𝒱.val.property a.hom.hom (stackPointOfSpacePoint B S hS T u) = v ∧
      pointsMap B S hS (fibredCategory B S hS T).val (fibredCategory B S hS T).property
        𝒳.val.property (a ≫ j).hom.hom (stackPointOfSpacePoint B S hS T u) =
        pointsMap B S hS 𝒱.val.val 𝒱.val.property 𝒳.val.property j.hom.hom v ∧
      relativeDimensionAt.{u, w} B S hS T hT 𝒱 a ha u = (m : WithBot ℕ∞) ∧
      relativeDimensionAt.{u, w} B S hS T hT 𝒳 (a ≫ j) hbft u = (m : WithBot ℕ∞) := by
  classical
  have hjsm := AlgebraicStacks.isSmooth_of_isOpenImmersion B S hS j hj
  have hjft := AlgebraicStacks.isLocallyOfFiniteType_of_isOpenImmersion B S hS j hj
  obtain ⟨T, hT, a, hasm, u, hu⟩ :=
    exists_isSmooth_algebraicSpaceStack_hom_pointsMap_eq.{u, w} B S hS 𝒱 v
  have ha := AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS a hasm
  have hbft := AlgebraicStacks.isLocallyOfFiniteType_comp B S hS a j ha hjft
  obtain ⟨m, hm⟩ := exists_relativeDimensionAt_eq_natCast B S hS T hT 𝒱 a ha u
  obtain ⟨n, hn⟩ := exists_relativeDimensionAt_eq_natCast B S hS T hT 𝒳 (a ≫ j) hbft u
  have hrel := relativeStackDimensionAt_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS j hjft h𝒱
    h𝒳 v hT a hasm ha hbft u hu m hm
  rw [relativeStackDimensionAt_eq_zero_of_isOpenImmersion B S hS j hj hjft h𝒱 h𝒳 v, hn] at hrel
  have hnm : n = m := by
    have h0 : WithBotTop.coe (0 : ℤ) = (((n : ℤ) - (m : ℤ) : ℤ) : EInt) := hrel
    have hz : (0 : ℤ) = (n : ℤ) - (m : ℤ) := WithBotTop.coe_injective h0
    omega
  refine ⟨T, hT, a, u, m, hasm, ha, AlgebraicStacks.isSmooth_comp B S hS a j hasm hjsm, hbft, hu,
    ?_, hm, hnm ▸ hn⟩
  exact (pointsMap_comp B S hS (fibredCategory B S hS T).val (fibredCategory B S hS T).property
    𝒱.val.property 𝒳.val.property a.hom.hom j.hom.hom
    (stackPointOfSpacePoint B S hS T u)).symm.trans
    (congrArg (pointsMap B S hS 𝒱.val.val 𝒱.val.property 𝒳.val.property j.hom.hom) hu)

/-- **The dimension of Stacks 0AFN is unchanged by an open immersion.** For an open immersion
`j : 𝒱 ⟶ 𝒳` of locally Noetherian algebraic stacks and `v ∈ |𝒱|`, the dimension of `𝒳` at the
image of `v` is the dimension of `𝒱` at `v`.

A smooth chart `a : T ⟶ 𝒱` by an algebraic space above `v` is also a smooth chart of `𝒳` after
composing with `j`, and the chart formula of **Stacks 0DRN** exhibits the relative dimension of
`j` at `v` as the difference of the relative dimensions of `a ≫ j` and of `a` at the chart point.
That difference is `0` by
`AlgebraicGeometry.Stack.relativeStackDimensionAt_eq_zero_of_isOpenImmersion`, so the two
relative dimensions agree, and the dimension formula of **Stacks 0DRJ** reads both dimensions off
the same chart with the same subtrahend. -/
theorem dimensionAtPoint_pointsMap_eq_of_isOpenImmersion (j : 𝒱 ⟶ 𝒳)
    (hj : AlgebraicStacks.IsOpenImmersion B S hS j)
    (h𝒱 : IsLocallyNoetherianStack.{u, w} B S hS 𝒱)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (v : points B S hS 𝒱.val.val 𝒱.val.property) :
    dimensionAtPoint B S hS 𝒳 h𝒳
        (pointsMap B S hS 𝒱.val.val 𝒱.val.property 𝒳.val.property j.hom.hom v) =
      dimensionAtPoint B S hS 𝒱 h𝒱 v := by
  obtain ⟨T, hT, a, u, m, hasm, ha, hbsm, hbft, hu, hbu, hm, hn⟩ :=
    exists_chart_comp_isOpenImmersion B S hS j hj h𝒱 h𝒳 v
  rw [dimensionAtPoint_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS 𝒳 h𝒳 _ hT (a ≫ j) hbsm hbft
      u hbu m hn,
    dimensionAtPoint_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS 𝒱 h𝒱 v hT a hasm ha u hu m hm]

/-- **The relative dimension of Stacks 0DRL is unchanged by precomposition with an open
immersion.** For an open immersion `j : 𝒱 ⟶ 𝒳`, a 1-morphism `f : 𝒳 ⟶ 𝒴` locally of finite type
of locally Noetherian algebraic stacks and `v ∈ |𝒱|`, the relative dimension of `f` at the image
of `v` is the relative dimension of `j ≫ f` at `v`.

A smooth chart `a : T ⟶ 𝒱` by an algebraic space above `v` is a chart of `𝒱` above `v` and, after
composing with `j`, a chart of `𝒳` above the image of `v`; the chart formula of **Stacks 0DRN**
reads both relative dimensions off the same relative dimension of `a ≫ (j ≫ f) = (a ≫ j) ≫ f`,
with subtrahends the relative dimensions of `a` and of `a ≫ j`. Those two agree because their
difference is the relative dimension of `j` at `v`, which is `0` by
`AlgebraicGeometry.Stack.relativeStackDimensionAt_eq_zero_of_isOpenImmersion`. -/
theorem relativeStackDimensionAt_pointsMap_eq_of_isOpenImmersion
    {𝒴 : AlgebraicStacks.{u, w} B S hS} (j : 𝒱 ⟶ 𝒳) (f : 𝒳 ⟶ 𝒴)
    (hj : AlgebraicStacks.IsOpenImmersion B S hS j)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (hjf : AlgebraicStacks.IsLocallyOfFiniteType B S hS (j ≫ f))
    (h𝒱 : IsLocallyNoetherianStack.{u, w} B S hS 𝒱)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (h𝒴 : IsLocallyNoetherianStack.{u, w} B S hS 𝒴)
    (v : points B S hS 𝒱.val.val 𝒱.val.property) :
    relativeStackDimensionAt.{u, w} B S hS f hf h𝒳 h𝒴
        (pointsMap B S hS 𝒱.val.val 𝒱.val.property 𝒳.val.property j.hom.hom v) =
      relativeStackDimensionAt.{u, w} B S hS (j ≫ f) hjf h𝒱 h𝒴 v := by
  obtain ⟨T, hT, a, u, m, hasm, ha, hbsm, hbft, hu, hbu, hm, hn⟩ :=
    exists_chart_comp_isOpenImmersion B S hS j hj h𝒱 h𝒳 v
  have hcft := AlgebraicStacks.isLocallyOfFiniteType_comp B S hS a (j ≫ f) ha hjf
  have hcft' := AlgebraicStacks.isLocallyOfFiniteType_comp B S hS (a ≫ j) f hbft hf
  rw [relativeStackDimensionAt_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS f hf h𝒳 h𝒴 _ hT
      (a ≫ j) hbsm hbft hcft' u hbu m hn,
    relativeStackDimensionAt_eq_dimensionSubNat_of_isSmooth.{u, w} B S hS (j ≫ f) hjf h𝒱 h𝒴 v
      hT a hasm ha hcft u hu m hm]
  rfl

end AlgebraicGeometry.Stack

end
