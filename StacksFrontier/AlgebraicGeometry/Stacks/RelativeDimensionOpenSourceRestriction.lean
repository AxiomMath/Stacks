module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.CancelTwoFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionsStableUnderBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSmoothObject
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubspaceOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionZeroLocusStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeOpenChartThickening
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedSmoothLocal
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial

/-!
# Restricting the source of a 1-morphism to an open subspace does not change its relative dimension

Let `f : U ⟶ 𝒳` be a 1-morphism, locally of finite type, from the algebraic stack of an algebraic
space `U` to an algebraic stack `𝒳` over `S`, and let `ι : W ⟶ U` be an open immersion of
algebraic spaces. The relative dimension of **Stacks 0DRG** of the restriction `W ⟶ 𝒳` at a point
`w ∈ |W|` is the relative dimension of `f` at the image of `w`. Consequently the restriction of `f`
to the open subspace where the relative dimension vanishes is locally quasi-finite (**Stacks 04NW**
at an algebraic stack target), and, when the source is the algebraic space represented by a scheme
of the site, that open subspace is an open of the scheme.

The last statement also holds for a source given as `AlgebraicGeometry.Stack.schemeStack`, the
slice of the site over an object, with the vanishing of the relative dimension given on any chart
of the target that sees the point.

## Main definitions

* `AlgebraicGeometry.Stack.relativeDimensionZeroLocusStack`: the locus in `|U|` where the
  relative dimension of **Stacks 0DRG** of `f` vanishes, as a subfunctor of `U`.

## Main results

* `AlgebraicGeometry.Stack.relativeDimensionAt_eq_iff_hasRelativeDimensionAt_baseChange`: the
  relative dimension of **Stacks 0DRG** is read on an arbitrary 2-fibre product square of a chart
  and the 1-morphism.
* `AlgebraicGeometry.Stack.relativeDimensionAt_comp_algebraicSpaceStackMap_of_isOpenImmersion`:
  the relative dimension is unchanged by restricting the source to an open subspace.
* `AlgebraicGeometry.Stack`
  `.isLocallyQuasiFinite_openChart_comp_of_forall_relativeDimensionAt_eq_zero` and
  `AlgebraicGeometry.Stack.exists_opens_isLocallyQuasiFinite_of_relativeDimensionAt_eq_zero`:
  for a source represented by a scheme of the site, an open of that scheme on which the
  1-morphism is locally quasi-finite in the sense of **Stacks 04XB**.
* `AlgebraicGeometry.Stack.isOpenSubspace_relativeDimensionZeroLocusStack` and
  `AlgebraicGeometry.Stack.isLocallyQuasiFinite_relativeDimensionZeroLocusStack`:
  **Stacks 04NW** for a 1-morphism from an algebraic space to an algebraic stack.
* `AlgebraicGeometry.Stack.exists_fieldFibreDimensionAt_eq_natCast`,
  `AlgebraicGeometry.Stack.hasRelativeDimensionAt_chartBaseChange_of_pointsMap_eq` and
  `AlgebraicGeometry.Stack.eq_of_hasRelativeDimensionAt_chartBaseChange_of_pointsMap_eq`:
  finiteness and well-definedness of the formula of **Stacks 0DRG** for a source that is merely
  *representable* by an algebraic space, so has no
  `AlgebraicGeometry.Stack.relativeDimensionAt`: the relative dimension of the base change along a
  chart depends only on the image point, and not on the chart.
* `AlgebraicGeometry.Stack.isLocallyQuasiFinite_iff_forall_hasRelativeDimensionAt_zero_baseChange`:
  the quasi-finiteness criterion of **Stacks 04NV** at an arbitrary 2-fibre product square of the
  chart and the 1-morphism.
* `AlgebraicGeometry.Stack`
  `.isLocallyQuasiFinite_openChart_comp_of_forall_exists_hasRelativeDimensionAt_zero` and
  `AlgebraicGeometry.Stack`
  `.exists_opens_isLocallyQuasiFinite_schemeStack_of_hasRelativeDimensionAt_zero`:
  the open of the scheme on which the 1-morphism is locally quasi-finite, for a source given as
  the slice of the site over an object of it.

## References

* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
* [Stacks Project, Tag 04NS](https://stacks.math.columbia.edu/tag/04NS)
* [Stacks Project, Tag 04NT](https://stacks.math.columbia.edu/tag/04NT)
* [Stacks Project, Tag 04NV](https://stacks.math.columbia.edu/tag/04NV)
* [Stacks Project, Tag 04NW](https://stacks.math.columbia.edu/tag/04NW)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 042S](https://stacks.math.columbia.edu/tag/042S)
* [Stacks Project, Tag 0501](https://stacks.math.columbia.edu/tag/0501)
* [Stacks Project, Tag 06ME](https://stacks.math.columbia.edu/tag/06ME)
* [Stacks Project, Tag 0CPP](https://stacks.math.columbia.edu/tag/0CPP)
* [Stacks Project, Tag 0DRG](https://stacks.math.columbia.edu/tag/0DRG)
* [Stacks Project, Tag 0DRH](https://stacks.math.columbia.edu/tag/0DRH)
* [Stacks Project, Tag 0DRQ](https://stacks.math.columbia.edu/tag/0DRQ)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The projection to a chart, on the representing algebraic spaces, of the base change of a
1-morphism locally of finite type is locally of finite type. -/
private theorem isLocallyOfFiniteType_representingMap_fst_of_isLocallyOfFiniteType
    (𝒳 𝒯 : AlgebraicStacks.{u, w} B S hS) (c : 𝒯 ⟶ 𝒳)
    (hc : AlgebraicStacks.IsLocallyOfFiniteType B S hS c)
    (V₀ : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS V₀ ⟶ 𝒳)
    {Sq : Bicategory.TwoCommSq a c} (hSq : Bicategory.IsTwoFibreProduct Sq)
    (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hP : IsAlgebraicSpace B S hS P)
    (eP : StacksRepresentableCFG.EquivalenceOver Sq.pt.val.val.p
      (presheafOfCategories (P ⋙ typeToCat)).p) :
    Space.IsLocallyOfFiniteType B S hS
      (representingMap B S hS Sq.pt.val (schemeStack.{u, w} B S hS V₀).val P (yoneda.obj V₀) eP
        (PresheafOfCategories.sliceElementsEquivalenceOver V₀) Sq.fst.hom) :=
  isLocallyOfFiniteType_representingMap B S hS
    (𝒳 := Sq.pt) (𝒴 := schemeStack.{u, w} B S hS V₀) P (yoneda.obj V₀) hP
    (isAlgebraicSpace_yoneda B S hS V₀) eP
    (PresheafOfCategories.sliceElementsEquivalenceOver V₀) _
    (AlgebraicStacks.isLocallyOfFiniteType_baseChange B S hS c a Sq hSq hc)

/-! ### The chart bridge at an arbitrary 2-fibre product square -/

section Bridge

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)

/-- Let `Sq` be an arbitrary 2-fibre product square of a chart `a : V ⟶ 𝒳` and of `f`. For a
point `z` of an algebraic space `P` representing the apex of `Sq`, the relative dimension of
**Stacks 0DRG** of `f` at the image of `z` in `|U|` is `d` exactly when the projection `P ⟶ V` has
relative dimension `d` at `z` in the sense of **Stacks 04NM**. -/
theorem relativeDimensionAt_eq_iff_hasRelativeDimensionAt_baseChange
    (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (V₀ : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS V₀ ⟶ 𝒳)
    {Sq : Bicategory.TwoCommSq a f} (hSq : Bicategory.IsTwoFibreProduct Sq)
    (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hP : IsAlgebraicSpace B S hS P)
    (eP : StacksRepresentableCFG.EquivalenceOver Sq.pt.val.val.p
      (presheafOfCategories (P ⋙ typeToCat)).p)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (z : Space.points B S hS P) (d : ℕ∞) :
    relativeDimensionAt.{u, w} B S hS U hU 𝒳 f hf
        (Space.pointsMap B S hS P (representingMap B S hS Sq.pt.val
          (algebraicSpaceStack.{u, w} B S hS U hU).val P U eP
          (StacksRepresentableCFG.EquivalenceOver.refl _) Sq.snd.hom) z) = (d : WithBot ℕ∞) ↔
      Space.HasRelativeDimensionAt d B S hS
        (representingMap B S hS Sq.pt.val (schemeStack.{u, w} B S hS V₀).val P (yoneda.obj V₀) eP
          (PresheafOfCategories.sliceElementsEquivalenceOver V₀) Sq.fst.hom) z := by
  have hprFT := isLocallyOfFiniteType_representingMap_fst_of_isLocallyOfFiniteType.{u, w}
    B S hS 𝒳 _ f hf V₀ a hSq P hP eP
  have hforward : ∀ e : ℕ∞, relativeDimensionAt.{u, w} B S hS U hU 𝒳 f hf
      (Space.pointsMap B S hS P (representingMap B S hS Sq.pt.val
        (algebraicSpaceStack.{u, w} B S hS U hU).val P U eP
        (StacksRepresentableCFG.EquivalenceOver.refl _) Sq.snd.hom) z) = (e : WithBot ℕ∞) →
      Space.HasRelativeDimensionAt e B S hS
        (representingMap B S hS Sq.pt.val (schemeStack.{u, w} B S hS V₀).val P (yoneda.obj V₀) eP
          (PresheafOfCategories.sliceElementsEquivalenceOver V₀) Sq.fst.hom) z := by
    intro e he
    obtain ⟨p, q, hp, hq, hval⟩ := exists_eq_fieldFibreDimensionAt B S hS U hU 𝒳 f hf _
    refine hasRelativeDimensionAt_representingMap_fst_of_fieldFibreDimensionAt B S hS a f
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS U hU) hf
      (Bicategory.isTwoFibreProduct_underlying (P := Sq)
        (twoFibreProductSquareAlgebraicStacks B S hS a f) hSq
        (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
          a.hom f.hom))
      ⟨P, hP, ⟨eP⟩⟩ (yoneda.obj V₀) P (isAlgebraicSpace_yoneda B S hS V₀) hP
      (PresheafOfCategories.sliceElementsEquivalenceOver V₀) eP hprFT rfl
      _ z rfl p q ?_ e (by rw [← hval]; exact he)
    rw [hq]
    exact spacePointMap_representing_naturality B S hS P U Sq.pt.val
      (algebraicSpaceStack.{u, w} B S hS U hU).val eP
      (StacksRepresentableCFG.EquivalenceOver.refl _) Sq.snd.hom z
  refine ⟨hforward d, fun hdz => ?_⟩
  obtain ⟨d₀, hd₀⟩ := exists_relativeDimensionAt_eq_natCast B S hS U hU 𝒳 f hf _
  have hkz := hforward (d₀ : ℕ∞) (by exact_mod_cast hd₀)
  have heq : (d₀ : ℕ∞) = d :=
    eq_of_hasRelativeDimensionAt B S hS hP (isAlgebraicSpace_yoneda B S hS V₀) _ z hkz hdz
  rw [hd₀]
  exact_mod_cast heq

end Bridge

/-! ### Restricting the source to an open subspace -/

section Restriction

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (U W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hU : IsAlgebraicSpace B S hS U) (hW : IsAlgebraicSpace B S hS W)
  (ι : W ⟶ U)
  (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
  (𝒲 : AlgebraicStacks.{u, w} B S hS) (a : 𝒲 ⟶ 𝒳)

/-- The inner square: the base change of the restriction `W ⟶ U` along the projection
`U ×_𝒳 V ⟶ U` of the base change of `f` along the chart `a`. -/
def restrictionInnerSquare : Bicategory.TwoCommSq
    (twoFibreProductSquareAlgebraicStacks B S hS a f).snd
    (algebraicSpaceStackMap.{u, w} B S hS hW hU ι) :=
  twoFibreProductSquareAlgebraicStacks B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS a f).snd
    (algebraicSpaceStackMap.{u, w} B S hS hW hU ι)

/-- The square which exhibits the apex of
`AlgebraicGeometry.Stack.restrictionInnerSquare` as a base change of the restriction of `f` to
`W` along the chart `a`: **Stacks 02XD** in the 2-category of algebraic stacks. -/
def restrictionSquare : Bicategory.TwoCommSq a
    (algebraicSpaceStackMap.{u, w} B S hS hW hU ι ≫ f) :=
  cancelSndSquareAlgebraicStacks B S hS a f (algebraicSpaceStackMap.{u, w} B S hS hW hU ι)
    (algebraicSpaceStackMap.{u, w} B S hS hW hU ι ≫ f) (Iso.refl _)

/-- `AlgebraicGeometry.Stack.restrictionSquare` is a 2-fibre product square. -/
def isTwoFibreProduct_restrictionSquare :
    Bicategory.IsTwoFibreProduct (restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 a) :=
  isTwoFibreProduct_cancelSndSquareAlgebraicStacks B S hS a f
    (algebraicSpaceStackMap.{u, w} B S hS hW hU ι)
    (algebraicSpaceStackMap.{u, w} B S hS hW hU ι ≫ f) (Iso.refl _)

/-- The inner projection is an open immersion. -/
theorem isOpenImmersion_restrictionInnerSquare_fst
    (hι : Space.IsOpenImmersion B S hS ι) :
    AlgebraicStacks.IsOpenImmersion B S hS
      (restrictionInnerSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 a).fst :=
  AlgebraicStacks.isOpenImmersion_baseChange_snd B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS a f).snd
      (algebraicSpaceStackMap.{u, w} B S hS hW hU ι)).swap
    (Bicategory.isTwoFibreProduct_swap
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS a f).snd
        (algebraicSpaceStackMap.{u, w} B S hS hW hU ι)))
    (isOpenImmersion_algebraicSpaceStackMap_of_isOpenImmersion B S hS hW hU hι)

variable (P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hP : IsAlgebraicSpace B S hS P) (hQ : IsAlgebraicSpace B S hS Q)
  (eP : StacksRepresentableCFG.EquivalenceOver
    (twoFibreProductSquareAlgebraicStacks B S hS a f).pt.val.val.p
    (presheafOfCategories (P ⋙ typeToCat)).p)

/-- The projection of the restricted base change onto the chart is the morphism of representing
algebraic spaces induced by the inner projection, followed by the projection of the base change
of `f` onto the chart. -/
theorem representingMap_restrictionSquare_fst
    (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eV : StacksRepresentableCFG.EquivalenceOver 𝒲.val.val.p
      (presheafOfCategories (V ⋙ typeToCat)).p)
    (eQ : StacksRepresentableCFG.EquivalenceOver
      (restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 a).pt.val.val.p
      (presheafOfCategories (Q ⋙ typeToCat)).p) :
    representingMap B S hS (restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 a).pt.val
        𝒲.val Q V eQ eV
        (restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 a).fst.hom =
      representingMap B S hS (restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 a).pt.val
          (twoFibreProductSquareAlgebraicStacks B S hS a f).pt.val Q P eQ eP
          (restrictionInnerSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 a).fst.hom ≫
        representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a f).pt.val
          𝒲.val P V eP eV
          (twoFibreProductSquareAlgebraicStacks B S hS a f).fst.hom :=
  representingMap_comp
    (𝒜 := (restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 a).pt.val)
    (ℬ := (twoFibreProductSquareAlgebraicStacks B S hS a f).pt.val)
    (𝒞 := 𝒲.val)
    B S hS Q P V eQ eP eV
    (restrictionInnerSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 a).fst.hom
    (twoFibreProductSquareAlgebraicStacks B S hS a f).fst.hom

/-- The inner projection commutes with the restriction on the representing algebraic spaces. -/
theorem representingMap_restrictionSquare_snd
    (eQ : StacksRepresentableCFG.EquivalenceOver
      (restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 a).pt.val.val.p
      (presheafOfCategories (Q ⋙ typeToCat)).p) :
    representingMap B S hS (restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 a).pt.val
          (twoFibreProductSquareAlgebraicStacks B S hS a f).pt.val Q P eQ eP
          (restrictionInnerSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 a).fst.hom ≫
        representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a f).pt.val
          (algebraicSpaceStack.{u, w} B S hS U hU).val P U eP
          (StacksRepresentableCFG.EquivalenceOver.refl _)
          (twoFibreProductSquareAlgebraicStacks B S hS a f).snd.hom =
      representingMap B S hS (restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 a).pt.val
          (algebraicSpaceStack.{u, w} B S hS W hW).val Q W eQ
          (StacksRepresentableCFG.EquivalenceOver.refl _)
          (restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 a).snd.hom ≫ ι := by
  have h₁ := representingMap_comp
    (𝒜 := (restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 a).pt.val)
    (ℬ := (twoFibreProductSquareAlgebraicStacks B S hS a f).pt.val)
    (𝒞 := (algebraicSpaceStack.{u, w} B S hS U hU).val)
    B S hS Q P U eQ eP (StacksRepresentableCFG.EquivalenceOver.refl _)
    (restrictionInnerSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 a).fst.hom
    (twoFibreProductSquareAlgebraicStacks B S hS a f).snd.hom
  have h₂ := representingMap_comp
    (𝒜 := (restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 a).pt.val)
    (ℬ := (algebraicSpaceStack.{u, w} B S hS W hW).val)
    (𝒞 := (algebraicSpaceStack.{u, w} B S hS U hU).val)
    B S hS Q W U eQ (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 a).snd.hom
    (algebraicSpaceStackMap.{u, w} B S hS hW hU ι).hom
  rw [representingMap_associatedMap B S hS W U ι] at h₂
  rw [← h₁, ← h₂]
  exact representingMap_congr_twoIso
    (𝒜 := (restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 a).pt.val)
    (𝒞 := (algebraicSpaceStack.{u, w} B S hS U hU).val)
    B S hS Q U eQ (StacksRepresentableCFG.EquivalenceOver.refl _)
    (Bicategory.InducedBicategory.isoHom
      (restrictionInnerSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 a).iso)

include hP hQ in
/-- The morphism of representing algebraic spaces induced by the inner projection is an open
immersion. -/
theorem isOpenImmersion_representingMap_restrictionInnerSquare_fst
    (hι : Space.IsOpenImmersion B S hS ι)
    (eQ : StacksRepresentableCFG.EquivalenceOver
      (restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 a).pt.val.val.p
      (presheafOfCategories (Q ⋙ typeToCat)).p) :
    Space.IsOpenImmersion B S hS
      (representingMap B S hS (restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 a).pt.val
        (twoFibreProductSquareAlgebraicStacks B S hS a f).pt.val Q P eQ eP
        (restrictionInnerSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 a).fst.hom) := by
  have : (Space.openImmersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.openImmersion_isLocalAtTarget_fppf.{u, u} B S hS
  exact (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
    (Space.openImmersionProperty B S hS)
    (𝒜 := (restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 a).pt.val)
    (𝒞 := (twoFibreProductSquareAlgebraicStacks B S hS a f).pt.val)
    (restrictionInnerSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 a).fst.hom
    (isOpenImmersion_restrictionInnerSquare_fst.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 a hι).1
    Q P hQ hP eQ eP).mp
    (isOpenImmersion_restrictionInnerSquare_fst.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 a hι).2

/-- The projection of the restricted base change onto `W` is surjective on points, as soon as
the chart is surjective. -/
theorem surjective_representingMap_restrictionInnerSquare_snd
    (haSurj : IsSurjective B S hS a)
    (eQ : StacksRepresentableCFG.EquivalenceOver
      (restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 a).pt.val.val.p
      (presheafOfCategories (Q ⋙ typeToCat)).p) :
    Function.Surjective (Space.pointsMap B S hS Q
      (representingMap B S hS (restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 a).pt.val
        (algebraicSpaceStack.{u, w} B S hS W hW).val Q W eQ
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 a).snd.hom)) :=
  isSurjective_representingMap_of_isSurjective B S hS
    (𝒳 := (restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 a).pt)
    (𝒴 := algebraicSpaceStack.{u, w} B S hS W hW) Q W eQ
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (restrictionInnerSquare.{u, w} B S hS 𝒳 U W hU hW ι f 𝒲 a).snd
    (isSurjective_of_isTwoFibreProduct B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS a f).snd
        (algebraicSpaceStackMap.{u, w} B S hS hW hU ι))
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS a f).snd
        (algebraicSpaceStackMap.{u, w} B S hS hW hU ι))
      (isSurjective_of_isTwoFibreProduct B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS a f)
        (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a f) haSurj))

end Restriction

/-- The restriction of a 1-morphism locally of finite type to an open subspace of its source is
locally of finite type. -/
private theorem isLocallyOfFiniteType_algebraicSpaceStackMap_comp_of_isOpenImmersion
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (U W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hU : IsAlgebraicSpace B S hS U) (hW : IsAlgebraicSpace B S hS W)
    (ι : W ⟶ U) (hι : Space.IsOpenImmersion B S hS ι)
    (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f) :
    AlgebraicStacks.IsLocallyOfFiniteType B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hW hU ι ≫ f) :=
  AlgebraicStacks.isLocallyOfFiniteType_comp B S hS _ f
    ((isLocallyOfFiniteType_algebraicSpaceStackMap_iff.{u, w} B S hS hW hU ι).mpr
      (Space.isLocallyOfFiniteType_of_isEtale B S hS hU
        (Space.isEtale_of_isOpenImmersion B S hS hι))) hf

/-- A point of an algebraic space at which the relative dimension of a 1-morphism locally of finite
type from its algebraic stack is at most zero has relative dimension zero. -/
private theorem relativeDimensionAt_eq_zero_of_le_zero
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hU : IsAlgebraicSpace B S hS U) (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f) (t : Space.points B S hS U)
    (ht : relativeDimensionAt.{u, w} B S hS U hU 𝒳 f hf t ≤ (((0 : ℕ) : ℕ∞) : WithBot ℕ∞)) :
    relativeDimensionAt.{u, w} B S hS U hU 𝒳 f hf t = (0 : WithBot ℕ∞) := by
  obtain ⟨d, hd⟩ := exists_relativeDimensionAt_eq_natCast B S hS U hU 𝒳 f hf t
  have hd0 : d = 0 := Nat.le_zero.mp (by exact_mod_cast hd ▸ ht)
  rw [hd, hd0]
  norm_num

/-- Let `f : U ⟶ 𝒳` be a 1-morphism locally of finite type from the algebraic stack of an
algebraic space `U` to an algebraic stack, and let `ι : W ⟶ U` be an open immersion of algebraic
spaces. Then the relative dimension of **Stacks 0DRG** of the restriction `W ⟶ 𝒳` at a point
`w ∈ |W|` is the relative dimension of `f` at the image of `w`. -/
theorem relativeDimensionAt_comp_algebraicSpaceStackMap_of_isOpenImmersion
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (U W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hU : IsAlgebraicSpace B S hS U) (hW : IsAlgebraicSpace B S hS W)
    (ι : W ⟶ U) (hι : Space.IsOpenImmersion B S hS ι)
    (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (hj : AlgebraicStacks.IsLocallyOfFiniteType B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hW hU ι ≫ f))
    (w : Space.points B S hS W) :
    relativeDimensionAt.{u, w} B S hS W hW 𝒳
        (algebraicSpaceStackMap.{u, w} B S hS hW hU ι ≫ f) hj w =
      relativeDimensionAt.{u, w} B S hS U hU 𝒳 f hf (Space.pointsMap B S hS W ι w) := by
  obtain ⟨V₀, a, haSm, haSurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒳
  have hPtrep : IsRepresentableByAlgebraicSpace B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS a f).pt.val :=
    isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒳.val
      (schemeStack.{u, w} B S hS V₀).val (algebraicSpaceStack.{u, w} B S hS U hU).val
      a.hom.hom f.hom.hom
      (isRepresentableByAlgebraicSpaces_of_algebraicSpaceStack_source.{u, w} B S hS 𝒳 U hU f)
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS V₀)
  obtain ⟨P, hP, ⟨eP⟩⟩ := id hPtrep
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ : IsRepresentableByAlgebraicSpace B S hS
      (restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f
        (schemeStack.{u, w} B S hS V₀) a).pt.val :=
    isRepresentableByAlgebraicSpace_twoFibreProduct B S hS
      (algebraicSpaceStack.{u, w} B S hS U hU).val
      (twoFibreProductSquareAlgebraicStacks B S hS a f).pt.val
      (algebraicSpaceStack.{u, w} B S hS W hW).val
      (twoFibreProductSquareAlgebraicStacks B S hS a f).snd.hom.hom
      (algebraicSpaceStackMap.{u, w} B S hS hW hU ι).hom.hom
      (isOpenImmersion_algebraicSpaceStackMap_of_isOpenImmersion.{u, w} B S hS hW hU hι).1
      hPtrep
  obtain ⟨y, hy⟩ := surjective_representingMap_restrictionInnerSquare_snd.{u, w}
    B S hS 𝒳 U W hU hW ι f (schemeStack.{u, w} B S hS V₀) a Q haSurj eQ w
  obtain ⟨d₀, hd₀⟩ := exists_relativeDimensionAt_eq_natCast B S hS W hW 𝒳
    (algebraicSpaceStackMap.{u, w} B S hS hW hU ι ≫ f) hj w
  have h₁ := (relativeDimensionAt_eq_iff_hasRelativeDimensionAt_baseChange B S hS 𝒳 W hW
    (algebraicSpaceStackMap.{u, w} B S hS hW hU ι ≫ f) V₀ a
    (isTwoFibreProduct_restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f
      (schemeStack.{u, w} B S hS V₀) a)
    Q hQ eQ hj y (d₀ : ℕ∞)).mp (by rw [hy]; exact_mod_cast hd₀)
  rw [representingMap_restrictionSquare_fst.{u, w} B S hS 𝒳 U W hU hW ι f
    (schemeStack.{u, w} B S hS V₀) a P Q eP (yoneda.obj V₀)
    (PresheafOfCategories.sliceElementsEquivalenceOver V₀) eQ] at h₁
  have h₂ := (Space.hasRelativeDimensionAt_comp_iff B S hS (d₀ : ℕ∞) _ _
    (Space.presheaf_etale_of_isOpenImmersion B S hS
      (isOpenImmersion_representingMap_restrictionInnerSquare_fst.{u, w}
        B S hS 𝒳 U W hU hW ι f (schemeStack.{u, w} B S hS V₀) a P Q hP hQ eP hι eQ))
    hQ (isAlgebraicSpace_yoneda B S hS V₀) y).mp h₁
  have h₃ := (relativeDimensionAt_eq_iff_hasRelativeDimensionAt_baseChange B S hS 𝒳 U hU f V₀ a
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a f) P hP eP hf _
    (d₀ : ℕ∞)).mpr h₂
  have hpt : Space.pointsMap B S hS P
      (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a f).pt.val
        (algebraicSpaceStack.{u, w} B S hS U hU).val P U eP
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (twoFibreProductSquareAlgebraicStacks B S hS a f).snd.hom)
      (Space.pointsMap B S hS Q
        (representingMap B S hS (restrictionSquare.{u, w} B S hS 𝒳 U W hU hW ι f
            (schemeStack.{u, w} B S hS V₀) a).pt.val
          (twoFibreProductSquareAlgebraicStacks B S hS a f).pt.val Q P eQ eP
          (restrictionInnerSquare.{u, w} B S hS 𝒳 U W hU hW ι f
            (schemeStack.{u, w} B S hS V₀) a).fst.hom) y) =
      Space.pointsMap B S hS W ι w := by
    rw [← Space.pointsMap_comp_apply,
      representingMap_restrictionSquare_snd.{u, w} B S hS 𝒳 U W hU hW ι f
        (schemeStack.{u, w} B S hS V₀) a P Q eP eQ,
      Space.pointsMap_comp_apply, hy]
  rw [hd₀, ← hpt, h₃]
  norm_cast

/-! ### The open on which a 1-morphism from a scheme of the site is locally quasi-finite -/

section SchemeSource

variable (𝒴₀ : AlgebraicStacks.{u, w} B S hS) (Z : BigFppfOver B S hS)
  (f : algebraicSpaceStack.{u, w} B S hS (yoneda.obj Z)
    (isAlgebraicSpace_yoneda B S hS Z) ⟶ 𝒴₀)
  (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
  (V : ((BigFppfOver.toScheme B S hS).obj Z).Opens)

/-- The restriction of a 1-morphism to an open of the scheme on which its relative dimension
vanishes is locally quasi-finite. -/
theorem isLocallyQuasiFinite_openChart_comp_of_forall_relativeDimensionAt_eq_zero
    (hV : ∀ t : Space.points B S hS (yoneda.obj Z), Space.pointsToScheme B S hS Z t ∈ V →
      relativeDimensionAt.{u, w} B S hS (yoneda.obj Z) (isAlgebraicSpace_yoneda B S hS Z) 𝒴₀
        f hf t = (0 : WithBot ℕ∞)) :
    IsLocallyQuasiFinite B S hS
      (algebraicSpaceStackMap.{u, w} B S hS
          (isAlgebraicSpace_yoneda B S hS (AlgebraicStacks.openChart B S hS Z V))
          (isAlgebraicSpace_yoneda B S hS Z)
          (yoneda.map (AlgebraicStacks.openChartHom B S hS Z V)) ≫ f).hom := by
  have hιOI : Space.IsOpenImmersion B S hS
      (yoneda.map (AlgebraicStacks.openChartHom B S hS Z V)) :=
    (Space.presheaf_yoneda_map_iff B S hS (P := @AlgebraicGeometry.IsOpenImmersion.{u})
      inferInstance (AlgebraicStacks.openChartHom B S hS Z V)).2
      (AlgebraicStacks.isOpenImmersion_openChartHom B S hS Z V)
  have hjlft := isLocallyOfFiniteType_algebraicSpaceStackMap_comp_of_isOpenImmersion.{u, w}
    B S hS 𝒴₀ _ _ (isAlgebraicSpace_yoneda B S hS Z)
    (isAlgebraicSpace_yoneda B S hS (AlgebraicStacks.openChart B S hS Z V)) _ hιOI f hf
  refine (isLocallyQuasiFinite_iff_forall_relativeDimensionAt_eq_zero.{u, w} B S hS 𝒴₀
    (yoneda.obj (AlgebraicStacks.openChart B S hS Z V))
    (isAlgebraicSpace_yoneda B S hS (AlgebraicStacks.openChart B S hS Z V)) _ hjlft).mpr
    (fun x => ?_)
  rw [relativeDimensionAt_comp_algebraicSpaceStackMap_of_isOpenImmersion B S hS 𝒴₀
    (yoneda.obj Z) (yoneda.obj (AlgebraicStacks.openChart B S hS Z V))
    (isAlgebraicSpace_yoneda B S hS Z)
    (isAlgebraicSpace_yoneda B S hS (AlgebraicStacks.openChart B S hS Z V))
    (yoneda.map (AlgebraicStacks.openChartHom B S hS Z V)) hιOI f hf hjlft x]
  refine hV _ ?_
  rw [Space.pointsToScheme_pointsMap, AlgebraicStacks.openChartHom_toScheme]
  exact (Scheme.Opens.range_ι V).le (Set.mem_range_self _)

/-- Let `f : Z ⟶ 𝒴₀` be a 1-morphism locally of finite type from the algebraic stack of the
algebraic space represented by a scheme `Z` of the site to an algebraic stack, and let `z₀ ∈ |Z|`
be a point at which the relative dimension of **Stacks 0DRG** vanishes. Then some open `V` of the
scheme `Z` contains `z₀` and the restriction of `f` to `V` is locally quasi-finite in the sense of
**Stacks 04XB**. -/
theorem exists_opens_isLocallyQuasiFinite_of_relativeDimensionAt_eq_zero
    (z₀ : Space.points B S hS (yoneda.obj Z))
    (hz₀ : relativeDimensionAt.{u, w} B S hS (yoneda.obj Z)
      (isAlgebraicSpace_yoneda B S hS Z) 𝒴₀ f hf z₀ = (0 : WithBot ℕ∞)) :
    ∃ V : ((BigFppfOver.toScheme B S hS).obj Z).Opens,
      Space.pointsToScheme B S hS Z z₀ ∈ V ∧
        IsLocallyQuasiFinite B S hS
          (algebraicSpaceStackMap.{u, w} B S hS
              (isAlgebraicSpace_yoneda B S hS (AlgebraicStacks.openChart B S hS Z V))
              (isAlgebraicSpace_yoneda B S hS Z)
              (yoneda.map (AlgebraicStacks.openChartHom B S hS Z V)) ≫ f).hom := by
  classical
  refine ⟨⟨Space.pointsToScheme B S hS Z ''
      {t : Space.points B S hS (yoneda.obj Z) |
        relativeDimensionAt.{u, w} B S hS (yoneda.obj Z) (isAlgebraicSpace_yoneda B S hS Z) 𝒴₀
          f hf t ≤ (((0 : ℕ) : ℕ∞) : WithBot ℕ∞)},
    (Space.isOpen_pointTopology_yoneda_iff_isOpen_image B S hS Z _).mp
      (isOpen_setOf_relativeDimensionAt_le_of_algebraicStackTarget.{u, w} B S hS 𝒴₀
        (yoneda.obj Z) (isAlgebraicSpace_yoneda B S hS Z) f hf 0)⟩,
    ⟨z₀, by simp only [Set.mem_ofPred_eq, hz₀]; norm_num, rfl⟩,
    isLocallyQuasiFinite_openChart_comp_of_forall_relativeDimensionAt_eq_zero.{u, w}
      B S hS 𝒴₀ Z f hf _ (fun t htmem => ?_)⟩
  obtain ⟨t', ht'O, ht'eq⟩ := htmem
  have ht : t' = t := (Space.bijective_pointsToScheme B S hS Z).injective ht'eq
  subst ht
  exact relativeDimensionAt_eq_zero_of_le_zero B S hS 𝒴₀ (yoneda.obj Z)
    (isAlgebraicSpace_yoneda B S hS Z) f hf t' ht'O

end SchemeSource

/-! ### Stacks 04NW at an algebraic stack target -/

section ZeroLocus

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
  (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
  (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)

/-- The locus in `|U|` where the relative dimension of **Stacks 0DRG** of `f` vanishes, as a
subfunctor of `U`. -/
def relativeDimensionZeroLocusStack : Subfunctor U :=
  Space.openSubspaceOfPoints B S hS U
    {t : Space.points B S hS U |
      relativeDimensionAt.{u, w} B S hS U hU 𝒳 f hf t ≤ (((0 : ℕ) : ℕ∞) : WithBot ℕ∞)}

/-- For a 1-morphism `f : U ⟶ 𝒳` locally of finite type from the algebraic stack of an algebraic
space to an algebraic stack, the locus where the relative dimension of **Stacks 0DRG** vanishes is
an open subspace of `U` (**Stacks 04NW**). -/
theorem isOpenSubspace_relativeDimensionZeroLocusStack :
    Space.IsOpenSubspace B S hS
      (relativeDimensionZeroLocusStack B S hS 𝒳 U hU f hf) :=
  Space.isOpenSubspace_openSubspaceOfPoints B S hS hU _
    (isOpen_setOf_relativeDimensionAt_le_of_algebraicStackTarget.{u, w} B S hS 𝒳 U hU f hf 0)

/-- The point set of the relative-dimension-zero locus is the set of points at which the
relative dimension of **Stacks 0DRG** vanishes. -/
theorem range_pointsMap_relativeDimensionZeroLocusStack :
    Set.range (Space.pointsMap B S hS
        (relativeDimensionZeroLocusStack B S hS 𝒳 U hU f hf).toFunctor
        (relativeDimensionZeroLocusStack B S hS 𝒳 U hU f hf).ι) =
      {t : Space.points B S hS U |
        relativeDimensionAt.{u, w} B S hS U hU 𝒳 f hf t ≤ (((0 : ℕ) : ℕ∞) : WithBot ℕ∞)} :=
  Space.range_pointsMap_ι_openSubspaceOfPoints B S hS _

/-- The restriction of `f` to the open subspace of its source where the relative dimension of
**Stacks 0DRG** vanishes is locally quasi-finite in the sense of **Stacks 04XB**
(**Stacks 04NW**). -/
theorem isLocallyQuasiFinite_relativeDimensionZeroLocusStack :
    IsLocallyQuasiFinite B S hS
      (algebraicSpaceStackMap.{u, w} B S hS
          (isOpenSubspace_relativeDimensionZeroLocusStack B S hS 𝒳 U hU f hf).1 hU
          (relativeDimensionZeroLocusStack B S hS 𝒳 U hU f hf).ι ≫ f).hom := by
  have hιOI := (isOpenSubspace_relativeDimensionZeroLocusStack B S hS 𝒳 U hU f hf).2
  have hjlft := isLocallyOfFiniteType_algebraicSpaceStackMap_comp_of_isOpenImmersion.{u, w}
    B S hS 𝒳 U _ hU (isOpenSubspace_relativeDimensionZeroLocusStack B S hS 𝒳 U hU f hf).1 _
    hιOI f hf
  refine (isLocallyQuasiFinite_iff_forall_relativeDimensionAt_eq_zero.{u, w} B S hS 𝒳
    (relativeDimensionZeroLocusStack B S hS 𝒳 U hU f hf).toFunctor
    (isOpenSubspace_relativeDimensionZeroLocusStack B S hS 𝒳 U hU f hf).1 _
    hjlft).mpr (fun x => ?_)
  rw [relativeDimensionAt_comp_algebraicSpaceStackMap_of_isOpenImmersion B S hS 𝒳 U
    (relativeDimensionZeroLocusStack B S hS 𝒳 U hU f hf).toFunctor hU
    (isOpenSubspace_relativeDimensionZeroLocusStack B S hS 𝒳 U hU f hf).1
    (relativeDimensionZeroLocusStack B S hS 𝒳 U hU f hf).ι hιOI f hf hjlft x]
  have hmem : Space.pointsMap B S hS
      (relativeDimensionZeroLocusStack B S hS 𝒳 U hU f hf).toFunctor
      (relativeDimensionZeroLocusStack B S hS 𝒳 U hU f hf).ι x ∈
      {t : Space.points B S hS U |
        relativeDimensionAt.{u, w} B S hS U hU 𝒳 f hf t ≤ (((0 : ℕ) : ℕ∞) : WithBot ℕ∞)} := by
    rw [← range_pointsMap_relativeDimensionZeroLocusStack B S hS 𝒳 U hU f hf]
    exact Set.mem_range_self x
  exact relativeDimensionAt_eq_zero_of_le_zero B S hS 𝒳 U hU f hf _ hmem

end ZeroLocus

/-! ### Finiteness of the formula of Stacks 0DRG at a representable source -/

section Saturation

variable (𝒳 𝒯 : AlgebraicStacks.{u, w} B S hS) (c : 𝒯 ⟶ 𝒳)
  (h𝒯 : IsRepresentableByAlgebraicSpace B S hS 𝒯.val)
  (hc : AlgebraicStacks.IsLocallyOfFiniteType B S hS c)

include hc in
/-- For a 1-morphism `c : 𝒯 ⟶ 𝒳` locally of finite type from an algebraic stack representable by
an algebraic space to an algebraic stack, every value of the formula of **Stacks 0DRG** is a
natural number. -/
theorem exists_fieldFibreDimensionAt_eq_natCast
    (p : FieldValuedPoint B S hS 𝒳.val.val)
    (q : points B S hS (fieldFibreSquare B S hS c.hom p).pt.val
      (fieldFibreSquare B S hS c.hom p).pt.property) :
    ∃ d : ℕ, fieldFibreDimensionAt.{u, w} B S hS c.hom 𝒳.property h𝒯 p q = (d : WithBot ℕ∞) := by
  classical
  obtain ⟨W, hW, ⟨eW⟩⟩ :=
    isRepresentableByAlgebraicSpace_fieldFibreSquare.{u, w} B S hS c.hom 𝒳.property h𝒯 p
  obtain ⟨x, hx⟩ := (bijective_spacePointMap_representing B S hS W
    (fieldFibreSquare B S hS c.hom p).pt eW).surjective q
  have hdim : fieldFibreDimensionAt.{u, w} B S hS c.hom 𝒳.property h𝒯 p q =
      Space.dimensionAtPoint B S hS W hW x := by
    rw [← hx]
    exact fieldFibreDimensionAt_eq_dimensionAtPoint.{u, w} B S hS _ _ _ p W hW eW x
  have hgft := isLocallyOfFiniteType_representingMap_fieldFibreSquare_snd.{u, w} B S hS c hc p
    W (yoneda.obj p.base) hW (isAlgebraicSpace_yoneda B S hS p.base) eW
    (PresheafOfCategories.sliceElementsEquivalenceOver p.base)
  obtain ⟨d, hd⟩ := Space.exists_hasRelativeDimensionAt_natCast B S hS hW
    (isAlgebraicSpace_yoneda B S hS p.base) _ hgft x
  refine ⟨d, ?_⟩
  rw [hdim]
  refine (dimensionAtPoint_eq_iff_hasRelativeDimensionAt_of_isPullback B S hS p
    IsPullback.of_id_snd hW hW (isAlgebraicSpace_yoneda B S hS p.base) hgft x d).mpr ?_
  simpa using hd

end Saturation

/-! ### The relative dimension on a chart depends only on the image point -/

section ChartIndependence

/-- Let `c : 𝒯 ⟶ 𝒳` be locally of finite type with `𝒯` representable by an algebraic space, let
`V ⟶ 𝒳` and `V' ⟶ 𝒳` be two charts by schemes of the site, let `P` represent `𝒯 ×_𝒳 V`, let `P'`
represent `𝒯 ×_𝒳 V'`, and let `T` represent `𝒯`. A point of `P` and a point of `P'` with the same
image in `T` have the same relative dimension of **Stacks 04NM**, for the projection `P ⟶ V` and
the projection `P' ⟶ V'` respectively. -/
theorem hasRelativeDimensionAt_chartBaseChange_of_pointsMap_eq
    (𝒳 𝒯 : AlgebraicStacks.{u, w} B S hS) (c : 𝒯 ⟶ 𝒳)
    (h𝒯 : IsRepresentableByAlgebraicSpace B S hS 𝒯.val)
    (hc : AlgebraicStacks.IsLocallyOfFiniteType B S hS c)
    (V₀ V₁ : BigFppfOver B S hS)
    (a : schemeStack.{u, w} B S hS V₀ ⟶ 𝒳) (a' : schemeStack.{u, w} B S hS V₁ ⟶ 𝒳)
    (P P' T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hP : IsAlgebraicSpace B S hS P) (hP' : IsAlgebraicSpace B S hS P')
    (eP : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val.val.p
      (presheafOfCategories (P ⋙ typeToCat)).p)
    (eP' : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductSquareAlgebraicStacks B S hS a' c).pt.val.val.p
      (presheafOfCategories (P' ⋙ typeToCat)).p)
    (eT : StacksRepresentableCFG.EquivalenceOver 𝒯.val.val.p
      (presheafOfCategories (T ⋙ typeToCat)).p)
    (ξ : Space.points B S hS P) (ξ' : Space.points B S hS P')
    (hξ : Space.pointsMap B S hS P
          (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val
            𝒯.val P T eP eT (twoFibreProductSquareAlgebraicStacks B S hS a c).snd.hom) ξ =
        Space.pointsMap B S hS P'
          (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a' c).pt.val
            𝒯.val P' T eP' eT (twoFibreProductSquareAlgebraicStacks B S hS a' c).snd.hom) ξ')
    {d : ℕ∞}
    (hd : Space.HasRelativeDimensionAt d B S hS
      (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val
        (schemeStack.{u, w} B S hS V₀).val P (yoneda.obj V₀) eP
        (PresheafOfCategories.sliceElementsEquivalenceOver V₀)
        (twoFibreProductSquareAlgebraicStacks B S hS a c).fst.hom) ξ) :
    Space.HasRelativeDimensionAt d B S hS
      (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a' c).pt.val
        (schemeStack.{u, w} B S hS V₁).val P' (yoneda.obj V₁) eP'
        (PresheafOfCategories.sliceElementsEquivalenceOver V₁)
        (twoFibreProductSquareAlgebraicStacks B S hS a' c).fst.hom) ξ' := by
  classical
  have hprFT := isLocallyOfFiniteType_representingMap_fst_of_isLocallyOfFiniteType.{u, w}
    B S hS 𝒳 𝒯 c hc V₀ a (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a c)
    P hP eP
  have hprFT' := isLocallyOfFiniteType_representingMap_fst_of_isLocallyOfFiniteType.{u, w}
    B S hS 𝒳 𝒯 c hc V₁ a' (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a' c)
    P' hP' eP'
  have hζ : pointsMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val.val
        (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val.property 𝒯.val.property
        (twoFibreProductSquareAlgebraicStacks B S hS a c).snd.hom.hom
        (spacePointMap B S hS P (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val
          (representingEquivalence B S hS P
            (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val eP).functor ξ) =
      pointsMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a' c).pt.val.val
        (twoFibreProductSquareAlgebraicStacks B S hS a' c).pt.val.property 𝒯.val.property
        (twoFibreProductSquareAlgebraicStacks B S hS a' c).snd.hom.hom
        (spacePointMap B S hS P' (twoFibreProductSquareAlgebraicStacks B S hS a' c).pt.val
          (representingEquivalence B S hS P'
            (twoFibreProductSquareAlgebraicStacks B S hS a' c).pt.val eP').functor ξ') := by
    rw [← spacePointMap_representing_naturality B S hS P T
        (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val 𝒯.val eP eT
        (twoFibreProductSquareAlgebraicStacks B S hS a c).snd.hom ξ,
      ← spacePointMap_representing_naturality B S hS P' T
        (twoFibreProductSquareAlgebraicStacks B S hS a' c).pt.val 𝒯.val eP' eT
        (twoFibreProductSquareAlgebraicStacks B S hS a' c).snd.hom ξ', hξ]
  obtain ⟨q, hq⟩ := exists_point_fieldFibreSquare B S hS c.hom
    (pointsMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val.val
      (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val.property 𝒯.val.property
      (twoFibreProductSquareAlgebraicStacks B S hS a c).snd.hom.hom
      (spacePointMap B S hS P (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val
        (representingEquivalence B S hS P
          (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val eP).functor ξ))
    (Quotient.out (pointsMap B S hS 𝒯.val.val 𝒯.val.property 𝒳.val.property c.hom.hom
      (pointsMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val.val
        (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val.property 𝒯.val.property
        (twoFibreProductSquareAlgebraicStacks B S hS a c).snd.hom.hom
        (spacePointMap B S hS P (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val
          (representingEquivalence B S hS P
            (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val eP).functor ξ))))
    (Quotient.out_eq _)
  obtain ⟨e, he⟩ := exists_fieldFibreDimensionAt_eq_natCast.{u, w} B S hS 𝒳 𝒯 c h𝒯 hc _ q
  have hcan := Bicategory.isTwoFibreProduct_underlying
    (twoFibreProductSquareAlgebraicStacks B S hS a c)
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a c)
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      a.hom c.hom)
  have hcan' := Bicategory.isTwoFibreProduct_underlying
    (twoFibreProductSquareAlgebraicStacks B S hS a' c)
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a' c)
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      a'.hom c.hom)
  have hξval := hasRelativeDimensionAt_representingMap_fst_of_fieldFibreDimensionAt B S hS a c
    h𝒯 hc hcan ⟨P, hP, ⟨eP⟩⟩ (yoneda.obj V₀) P (isAlgebraicSpace_yoneda B S hS V₀) hP
    (PresheafOfCategories.sliceElementsEquivalenceOver V₀) eP hprFT rfl _ ξ rfl _ q hq
    (e : ℕ∞) he
  have hξ'val := hasRelativeDimensionAt_representingMap_fst_of_fieldFibreDimensionAt B S hS a' c
    h𝒯 hc hcan' ⟨P', hP', ⟨eP'⟩⟩ (yoneda.obj V₁) P' (isAlgebraicSpace_yoneda B S hS V₁) hP'
    (PresheafOfCategories.sliceElementsEquivalenceOver V₁) eP' hprFT' rfl _ ξ' rfl _ q
    (hq.trans hζ) (e : ℕ∞) he
  rw [eq_of_hasRelativeDimensionAt B S hS hP (isAlgebraicSpace_yoneda B S hS V₀) _ ξ hd hξval]
  exact hξ'val

/-- Two points of the algebraic space representing `𝒯 ×_𝒳 V` with the same image in the algebraic
space representing `𝒯` have the same relative dimension of **Stacks 04NM** for the projection to
`V`. -/
theorem eq_of_hasRelativeDimensionAt_chartBaseChange_of_pointsMap_eq
    (𝒳 𝒯 : AlgebraicStacks.{u, w} B S hS) (c : 𝒯 ⟶ 𝒳)
    (h𝒯 : IsRepresentableByAlgebraicSpace B S hS 𝒯.val)
    (hc : AlgebraicStacks.IsLocallyOfFiniteType B S hS c)
    (V₀ : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS V₀ ⟶ 𝒳)
    (P T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hP : IsAlgebraicSpace B S hS P)
    (eP : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val.val.p
      (presheafOfCategories (P ⋙ typeToCat)).p)
    (eT : StacksRepresentableCFG.EquivalenceOver 𝒯.val.val.p
      (presheafOfCategories (T ⋙ typeToCat)).p)
    (ξ ξ' : Space.points B S hS P)
    (hξ : Space.pointsMap B S hS P
          (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val
            𝒯.val P T eP eT (twoFibreProductSquareAlgebraicStacks B S hS a c).snd.hom) ξ =
        Space.pointsMap B S hS P
          (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val
            𝒯.val P T eP eT (twoFibreProductSquareAlgebraicStacks B S hS a c).snd.hom) ξ')
    {d d' : ℕ∞}
    (hd : Space.HasRelativeDimensionAt d B S hS
      (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val
        (schemeStack.{u, w} B S hS V₀).val P (yoneda.obj V₀) eP
        (PresheafOfCategories.sliceElementsEquivalenceOver V₀)
        (twoFibreProductSquareAlgebraicStacks B S hS a c).fst.hom) ξ)
    (hd' : Space.HasRelativeDimensionAt d' B S hS
      (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val
        (schemeStack.{u, w} B S hS V₀).val P (yoneda.obj V₀) eP
        (PresheafOfCategories.sliceElementsEquivalenceOver V₀)
        (twoFibreProductSquareAlgebraicStacks B S hS a c).fst.hom) ξ') : d = d' :=
  eq_of_hasRelativeDimensionAt B S hS hP (isAlgebraicSpace_yoneda B S hS V₀) _ ξ'
    (hasRelativeDimensionAt_chartBaseChange_of_pointsMap_eq.{u, w} B S hS 𝒳 𝒯 c h𝒯 hc V₀ V₀ a a
      P P T hP hP eP eP eT ξ ξ' hξ hd) hd'

end ChartIndependence

/-! ### The quasi-finiteness criterion at an arbitrary 2-fibre product square -/

/-- **Stacks 04NV** at a source representable by an algebraic space, read on an arbitrary
2-fibre product square `Sq` of the smooth surjective chart `a` and of `c`. -/
theorem isLocallyQuasiFinite_iff_forall_hasRelativeDimensionAt_zero_baseChange
    (𝒳 𝒯 : AlgebraicStacks.{u, w} B S hS) (c : 𝒯 ⟶ 𝒳)
    (V₀ : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS V₀ ⟶ 𝒳)
    {Sq : Bicategory.TwoCommSq a c} (hSq : Bicategory.IsTwoFibreProduct Sq)
    (h𝒯 : IsRepresentableByAlgebraicSpace B S hS 𝒯.val)
    (hc : AlgebraicStacks.IsLocallyOfFiniteType B S hS c)
    (haSm : AlgebraicStacks.IsSmooth B S hS a) (haSurj : IsSurjective B S hS a)
    (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hP : IsAlgebraicSpace B S hS P)
    (eP : StacksRepresentableCFG.EquivalenceOver Sq.pt.val.val.p
      (presheafOfCategories (P ⋙ typeToCat)).p) :
    IsLocallyQuasiFinite B S hS c.hom ↔
      ∀ ξ : Space.points B S hS P, Space.HasRelativeDimensionAt 0 B S hS
        (representingMap B S hS Sq.pt.val (schemeStack.{u, w} B S hS V₀).val P (yoneda.obj V₀) eP
          (PresheafOfCategories.sliceElementsEquivalenceOver V₀) Sq.fst.hom) ξ := by
  have hcrep := isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property h𝒯 c.hom
  have hprFT := isLocallyOfFiniteType_representingMap_fst_of_isLocallyOfFiniteType.{u, w}
    B S hS 𝒳 𝒯 c hc V₀ a hSq P hP eP
  refine Iff.trans ?_
    (Space.isLocallyQuasiFinite_iff_forall_hasRelativeDimensionAt_zero B S hS _ hprFT)
  refine Iff.trans (hasRelativeProperty_iff_of_fppfCoverStack B S hS
    (Space.locallyQuasiFiniteProperty B S hS) c a hcrep haSurj
    (AlgebraicStacks.isFlat_of_isSmooth B S hS a haSm)
    (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS a haSm) Sq hSq) ?_
  refine ⟨fun h => ?_, fun h => ⟨isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1}
    B S hS _ _ _ c.hom a.hom _
    (Bicategory.isTwoFibreProduct_underlying (P := Sq)
      (twoFibreProductSquareAlgebraicStacks B S hS a c) hSq
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        a.hom c.hom)) hcrep, ?_⟩⟩
  · obtain ⟨hfst, hfstP⟩ := h
    exact (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
      (Space.locallyQuasiFiniteProperty B S hS) Sq.fst.hom hfst P (yoneda.obj V₀) hP
      (isAlgebraicSpace_yoneda B S hS V₀) eP
      (PresheafOfCategories.sliceElementsEquivalenceOver V₀)).mp hfstP
  · exact (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
      (Space.locallyQuasiFiniteProperty B S hS) Sq.fst.hom _ P (yoneda.obj V₀) hP
      (isAlgebraicSpace_yoneda B S hS V₀) eP
      (PresheafOfCategories.sliceElementsEquivalenceOver V₀)).mpr h

/-! ### Restricting the source of a 1-morphism out of a scheme of the site -/

section SliceSource

attribute [local instance] Space.pointTopology

variable (𝒴₀ : AlgebraicStacks.{u, w} B S hS) (Z : BigFppfOver B S hS)
  (c : schemeStack.{u, w} B S hS Z ⟶ 𝒴₀)
  (V : ((BigFppfOver.toScheme B S hS).obj Z).Opens)
  (W₀ : BigFppfOver B S hS) (b : schemeStack.{u, w} B S hS W₀ ⟶ 𝒴₀)

/-- The inner square: the base change of the inclusion of the open `V` of the scheme `Z` along the
projection `Z ×_𝒴₀ W ⟶ Z` of the base change of `c` along the chart `b`. -/
private def sliceInnerSquare : Bicategory.TwoCommSq
    (twoFibreProductSquareAlgebraicStacks B S hS b c).snd
    (schemeStackMap.{u, w} B S hS (AlgebraicStacks.openChartHom B S hS Z V)) :=
  twoFibreProductSquareAlgebraicStacks B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS b c).snd
    (schemeStackMap.{u, w} B S hS (AlgebraicStacks.openChartHom B S hS Z V))

/-- The square which exhibits the apex of `AlgebraicGeometry.Stack.sliceInnerSquare` as a base
change along the chart `b` of the restriction of `c` to the open `V`: **Stacks 02XD** in the
2-category of algebraic stacks. -/
private def sliceRestrictionSquare : Bicategory.TwoCommSq b
    (schemeStackMap.{u, w} B S hS (AlgebraicStacks.openChartHom B S hS Z V) ≫ c) :=
  cancelSndSquareAlgebraicStacks B S hS b c
    (schemeStackMap.{u, w} B S hS (AlgebraicStacks.openChartHom B S hS Z V))
    (schemeStackMap.{u, w} B S hS (AlgebraicStacks.openChartHom B S hS Z V) ≫ c) (Iso.refl _)

/-- `AlgebraicGeometry.Stack.sliceRestrictionSquare` is a 2-fibre product square. -/
private def isTwoFibreProduct_sliceRestrictionSquare :
    Bicategory.IsTwoFibreProduct (sliceRestrictionSquare.{u, w} B S hS 𝒴₀ Z c V W₀ b) :=
  isTwoFibreProduct_cancelSndSquareAlgebraicStacks B S hS b c
    (schemeStackMap.{u, w} B S hS (AlgebraicStacks.openChartHom B S hS Z V))
    (schemeStackMap.{u, w} B S hS (AlgebraicStacks.openChartHom B S hS Z V) ≫ c) (Iso.refl _)

/-- The inner projection is an open immersion. -/
private theorem isOpenImmersion_sliceInnerSquare_fst :
    AlgebraicStacks.IsOpenImmersion B S hS
      (sliceInnerSquare.{u, w} B S hS 𝒴₀ Z c V W₀ b).fst :=
  AlgebraicStacks.isOpenImmersion_baseChange_snd B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS b c).snd
      (schemeStackMap.{u, w} B S hS (AlgebraicStacks.openChartHom B S hS Z V))).swap
    (Bicategory.isTwoFibreProduct_swap
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS b c).snd
        (schemeStackMap.{u, w} B S hS (AlgebraicStacks.openChartHom B S hS Z V))))
    (AlgebraicStacks.isOpenImmersion_schemeStackMap.{u, w} B S hS
      (AlgebraicStacks.openChartHom B S hS Z V)
      (AlgebraicStacks.isOpenImmersion_openChartHom B S hS Z V))

variable (P₁ Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (e₁ : StacksRepresentableCFG.EquivalenceOver
    (twoFibreProductSquareAlgebraicStacks B S hS b c).pt.val.val.p
    (presheafOfCategories (P₁ ⋙ typeToCat)).p)

/-- The projection of the restricted base change onto the chart is the morphism of representing
algebraic spaces induced by the inner projection, followed by the projection of the base change of
`c` onto the chart. -/
private theorem representingMap_sliceRestrictionSquare_fst
    (eQ : StacksRepresentableCFG.EquivalenceOver
      (sliceRestrictionSquare.{u, w} B S hS 𝒴₀ Z c V W₀ b).pt.val.val.p
      (presheafOfCategories (Q ⋙ typeToCat)).p) :
    representingMap B S hS (sliceRestrictionSquare.{u, w} B S hS 𝒴₀ Z c V W₀ b).pt.val
        (schemeStack.{u, w} B S hS W₀).val Q (yoneda.obj W₀) eQ
        (PresheafOfCategories.sliceElementsEquivalenceOver W₀)
        (sliceRestrictionSquare.{u, w} B S hS 𝒴₀ Z c V W₀ b).fst.hom =
      representingMap B S hS (sliceRestrictionSquare.{u, w} B S hS 𝒴₀ Z c V W₀ b).pt.val
          (twoFibreProductSquareAlgebraicStacks B S hS b c).pt.val Q P₁ eQ e₁
          (sliceInnerSquare.{u, w} B S hS 𝒴₀ Z c V W₀ b).fst.hom ≫
        representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS b c).pt.val
          (schemeStack.{u, w} B S hS W₀).val P₁ (yoneda.obj W₀) e₁
          (PresheafOfCategories.sliceElementsEquivalenceOver W₀)
          (twoFibreProductSquareAlgebraicStacks B S hS b c).fst.hom :=
  representingMap_comp
    (𝒜 := (sliceRestrictionSquare.{u, w} B S hS 𝒴₀ Z c V W₀ b).pt.val)
    (ℬ := (twoFibreProductSquareAlgebraicStacks B S hS b c).pt.val)
    (𝒞 := (schemeStack.{u, w} B S hS W₀).val)
    B S hS Q P₁ (yoneda.obj W₀) eQ e₁
    (PresheafOfCategories.sliceElementsEquivalenceOver W₀)
    (sliceInnerSquare.{u, w} B S hS 𝒴₀ Z c V W₀ b).fst.hom
    (twoFibreProductSquareAlgebraicStacks B S hS b c).fst.hom

/-- The inner projection commutes with the inclusion of the open `V` on the representing algebraic
spaces. -/
private theorem representingMap_sliceRestrictionSquare_snd
    (eQ : StacksRepresentableCFG.EquivalenceOver
      (sliceRestrictionSquare.{u, w} B S hS 𝒴₀ Z c V W₀ b).pt.val.val.p
      (presheafOfCategories (Q ⋙ typeToCat)).p) :
    representingMap B S hS (sliceRestrictionSquare.{u, w} B S hS 𝒴₀ Z c V W₀ b).pt.val
          (twoFibreProductSquareAlgebraicStacks B S hS b c).pt.val Q P₁ eQ e₁
          (sliceInnerSquare.{u, w} B S hS 𝒴₀ Z c V W₀ b).fst.hom ≫
        representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS b c).pt.val
          (schemeStack.{u, w} B S hS Z).val P₁ (yoneda.obj Z) e₁
          (PresheafOfCategories.sliceElementsEquivalenceOver Z)
          (twoFibreProductSquareAlgebraicStacks B S hS b c).snd.hom =
      representingMap B S hS (sliceRestrictionSquare.{u, w} B S hS 𝒴₀ Z c V W₀ b).pt.val
          (schemeStack.{u, w} B S hS (AlgebraicStacks.openChart B S hS Z V)).val Q
          (yoneda.obj (AlgebraicStacks.openChart B S hS Z V)) eQ
          (PresheafOfCategories.sliceElementsEquivalenceOver
            (AlgebraicStacks.openChart B S hS Z V))
          (sliceRestrictionSquare.{u, w} B S hS 𝒴₀ Z c V W₀ b).snd.hom ≫
        yoneda.map (AlgebraicStacks.openChartHom B S hS Z V) := by
  have h₁ := representingMap_comp
    (𝒜 := (sliceRestrictionSquare.{u, w} B S hS 𝒴₀ Z c V W₀ b).pt.val)
    (ℬ := (twoFibreProductSquareAlgebraicStacks B S hS b c).pt.val)
    (𝒞 := (schemeStack.{u, w} B S hS Z).val)
    B S hS Q P₁ (yoneda.obj Z) eQ e₁
    (PresheafOfCategories.sliceElementsEquivalenceOver Z)
    (sliceInnerSquare.{u, w} B S hS 𝒴₀ Z c V W₀ b).fst.hom
    (twoFibreProductSquareAlgebraicStacks B S hS b c).snd.hom
  have h₂ := representingMap_comp
    (𝒜 := (sliceRestrictionSquare.{u, w} B S hS 𝒴₀ Z c V W₀ b).pt.val)
    (ℬ := (schemeStack.{u, w} B S hS (AlgebraicStacks.openChart B S hS Z V)).val)
    (𝒞 := (schemeStack.{u, w} B S hS Z).val)
    B S hS Q (yoneda.obj (AlgebraicStacks.openChart B S hS Z V)) (yoneda.obj Z) eQ
    (PresheafOfCategories.sliceElementsEquivalenceOver (AlgebraicStacks.openChart B S hS Z V))
    (PresheafOfCategories.sliceElementsEquivalenceOver Z)
    (sliceRestrictionSquare.{u, w} B S hS 𝒴₀ Z c V W₀ b).snd.hom
    (schemeStackMap.{u, w} B S hS (AlgebraicStacks.openChartHom B S hS Z V)).hom
  have h₃ : representingMap B S hS
      (schemeStack.{u, w} B S hS (AlgebraicStacks.openChart B S hS Z V)).val
      (schemeStack.{u, w} B S hS Z).val (yoneda.obj (AlgebraicStacks.openChart B S hS Z V))
      (yoneda.obj Z)
      (PresheafOfCategories.sliceElementsEquivalenceOver (AlgebraicStacks.openChart B S hS Z V))
      (PresheafOfCategories.sliceElementsEquivalenceOver Z)
      (schemeStackMap.{u, w} B S hS (AlgebraicStacks.openChartHom B S hS Z V)).hom =
        yoneda.map (AlgebraicStacks.openChartHom B S hS Z V) :=
    representingMap_schemeFibredCategoryMap B S hS (AlgebraicStacks.openChartHom B S hS Z V)
  rw [h₃] at h₂
  rw [← h₁, ← h₂]
  exact representingMap_congr_twoIso
    (𝒜 := (sliceRestrictionSquare.{u, w} B S hS 𝒴₀ Z c V W₀ b).pt.val)
    (𝒞 := (schemeStack.{u, w} B S hS Z).val)
    B S hS Q (yoneda.obj Z) eQ (PresheafOfCategories.sliceElementsEquivalenceOver Z)
    (Bicategory.InducedBicategory.isoHom
      (sliceInnerSquare.{u, w} B S hS 𝒴₀ Z c V W₀ b).iso)

/-- The morphism of representing algebraic spaces induced by the inner projection is an open
immersion. -/
private theorem isOpenImmersion_representingMap_sliceInnerSquare_fst
    (hP₁ : IsAlgebraicSpace B S hS P₁) (hQ : IsAlgebraicSpace B S hS Q)
    (eQ : StacksRepresentableCFG.EquivalenceOver
      (sliceRestrictionSquare.{u, w} B S hS 𝒴₀ Z c V W₀ b).pt.val.val.p
      (presheafOfCategories (Q ⋙ typeToCat)).p) :
    Space.IsOpenImmersion B S hS
      (representingMap B S hS (sliceRestrictionSquare.{u, w} B S hS 𝒴₀ Z c V W₀ b).pt.val
        (twoFibreProductSquareAlgebraicStacks B S hS b c).pt.val Q P₁ eQ e₁
        (sliceInnerSquare.{u, w} B S hS 𝒴₀ Z c V W₀ b).fst.hom) := by
  have : (Space.openImmersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.openImmersion_isLocalAtTarget_fppf.{u, u} B S hS
  exact (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
    (Space.openImmersionProperty B S hS)
    (𝒜 := (sliceRestrictionSquare.{u, w} B S hS 𝒴₀ Z c V W₀ b).pt.val)
    (𝒞 := (twoFibreProductSquareAlgebraicStacks B S hS b c).pt.val)
    (sliceInnerSquare.{u, w} B S hS 𝒴₀ Z c V W₀ b).fst.hom
    (isOpenImmersion_sliceInnerSquare_fst.{u, w} B S hS 𝒴₀ Z c V W₀ b).1
    Q P₁ hQ hP₁ eQ e₁).mp
    (isOpenImmersion_sliceInnerSquare_fst.{u, w} B S hS 𝒴₀ Z c V W₀ b).2

/-- Let `c : Z ⟶ 𝒴₀` be locally of finite type, where `Z` is an object of the site read as an
algebraic stack through the slice of the site over it, let `V ⟶ 𝒴₀` be any chart by a scheme of
the site, not assumed surjective, and let `P` represent `Z ×_𝒴₀ V`. If every point of the open
`V` of the scheme `Z` is the image of a point of `P` at which the projection `P ⟶ V` has relative
dimension zero in the sense of **Stacks 04NM**, then the restriction of `c` to that open is locally
quasi-finite in the sense of **Stacks 04XB**. -/
theorem isLocallyQuasiFinite_openChart_comp_of_forall_exists_hasRelativeDimensionAt_zero
    (hc : AlgebraicStacks.IsLocallyOfFiniteType B S hS c)
    (V₀ : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS V₀ ⟶ 𝒴₀)
    (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hP : IsAlgebraicSpace B S hS P)
    (eP : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val.val.p
      (presheafOfCategories (P ⋙ typeToCat)).p)
    (hV : ∀ z : Space.points B S hS (yoneda.obj Z),
      Space.pointsToScheme B S hS Z z ∈ V →
        ∃ ξ : Space.points B S hS P,
          Space.pointsMap B S hS P
              (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val
                (schemeStack.{u, w} B S hS Z).val P (yoneda.obj Z) eP
                (PresheafOfCategories.sliceElementsEquivalenceOver Z)
                (twoFibreProductSquareAlgebraicStacks B S hS a c).snd.hom) ξ = z ∧
            Space.HasRelativeDimensionAt 0 B S hS
              (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val
                (schemeStack.{u, w} B S hS V₀).val P (yoneda.obj V₀) eP
                (PresheafOfCategories.sliceElementsEquivalenceOver V₀)
                (twoFibreProductSquareAlgebraicStacks B S hS a c).fst.hom) ξ) :
    IsLocallyQuasiFinite B S hS
      (schemeStackMap.{u, w} B S hS (AlgebraicStacks.openChartHom B S hS Z V) ≫ c).hom := by
  classical
  obtain ⟨W₀, b, hbSm, hbSurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒴₀
  have hZrep : IsRepresentableByAlgebraicSpace B S hS (schemeStack.{u, w} B S hS Z).val :=
    isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS Z
  have hιOI : AlgebraicStacks.IsOpenImmersion B S hS
      (schemeStackMap.{u, w} B S hS (AlgebraicStacks.openChartHom B S hS Z V)) :=
    AlgebraicStacks.isOpenImmersion_schemeStackMap.{u, w} B S hS
      (AlgebraicStacks.openChartHom B S hS Z V)
      (AlgebraicStacks.isOpenImmersion_openChartHom B S hS Z V)
  have hc' : AlgebraicStacks.IsLocallyOfFiniteType B S hS
      (schemeStackMap.{u, w} B S hS (AlgebraicStacks.openChartHom B S hS Z V) ≫ c) :=
    AlgebraicStacks.isLocallyOfFiniteType_comp B S hS _ c
      (AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
        (AlgebraicStacks.isLocallyOfFinitePresentation_schemeStackMap.{u, w} B S hS
          (AlgebraicStacks.openChartHom B S hS Z V)
          (inferInstanceAs (LocallyOfFinitePresentation V.ι)))) hc
  have hP₁rep : IsRepresentableByAlgebraicSpace B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS b c).pt.val :=
    isRepresentableByAlgebraicSpace_chartBaseChange B S hS 𝒴₀
      (schemeStack.{u, w} B S hS Z) c W₀ b hZrep
  obtain ⟨P₁, hP₁, ⟨e₁⟩⟩ := id hP₁rep
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ : IsRepresentableByAlgebraicSpace B S hS
      (sliceRestrictionSquare.{u, w} B S hS 𝒴₀ Z c V W₀ b).pt.val :=
    isRepresentableByAlgebraicSpace_twoFibreProduct B S hS
      (schemeStack.{u, w} B S hS Z).val
      (twoFibreProductSquareAlgebraicStacks B S hS b c).pt.val
      (schemeStack.{u, w} B S hS (AlgebraicStacks.openChart B S hS Z V)).val
      (twoFibreProductSquareAlgebraicStacks B S hS b c).snd.hom.hom
      (schemeStackMap.{u, w} B S hS (AlgebraicStacks.openChartHom B S hS Z V)).hom.hom
      hιOI.1 hP₁rep
  rw [isLocallyQuasiFinite_iff_forall_hasRelativeDimensionAt_zero_baseChange B S hS 𝒴₀
    (schemeStack.{u, w} B S hS (AlgebraicStacks.openChart B S hS Z V))
    (schemeStackMap.{u, w} B S hS (AlgebraicStacks.openChartHom B S hS Z V) ≫ c) W₀ b
    (isTwoFibreProduct_sliceRestrictionSquare.{u, w} B S hS 𝒴₀ Z c V W₀ b)
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS
      (AlgebraicStacks.openChart B S hS Z V))
    hc' hbSm hbSurj Q hQ eQ]
  intro η
  rw [representingMap_sliceRestrictionSquare_fst.{u, w} B S hS 𝒴₀ Z c V W₀ b P₁ Q e₁ eQ,
    Space.hasRelativeDimensionAt_comp_iff B S hS 0 _ _
      (Space.presheaf_etale_of_isOpenImmersion B S hS
        (isOpenImmersion_representingMap_sliceInnerSquare_fst.{u, w} B S hS 𝒴₀ Z c V W₀ b
          P₁ Q e₁ hP₁ hQ eQ))
      hQ (isAlgebraicSpace_yoneda B S hS W₀) η]
  have hmem : Space.pointsToScheme B S hS Z (Space.pointsMap B S hS P₁
      (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS b c).pt.val
        (schemeStack.{u, w} B S hS Z).val P₁ (yoneda.obj Z) e₁
        (PresheafOfCategories.sliceElementsEquivalenceOver Z)
        (twoFibreProductSquareAlgebraicStacks B S hS b c).snd.hom)
      (Space.pointsMap B S hS Q
        (representingMap B S hS (sliceRestrictionSquare.{u, w} B S hS 𝒴₀ Z c V W₀ b).pt.val
          (twoFibreProductSquareAlgebraicStacks B S hS b c).pt.val Q P₁ eQ e₁
          (sliceInnerSquare.{u, w} B S hS 𝒴₀ Z c V W₀ b).fst.hom) η)) ∈ V := by
    rw [← Space.pointsMap_comp_apply,
      representingMap_sliceRestrictionSquare_snd.{u, w} B S hS 𝒴₀ Z c V W₀ b P₁ Q e₁ eQ,
      Space.pointsMap_comp_apply, Space.pointsToScheme_pointsMap,
      AlgebraicStacks.openChartHom_toScheme]
    exact (Scheme.Opens.range_ι V).le (Set.mem_range_self _)
  obtain ⟨ξ, hξeq, hξ0⟩ := hV _ hmem
  exact hasRelativeDimensionAt_chartBaseChange_of_pointsMap_eq.{u, w} B S hS 𝒴₀
    (schemeStack.{u, w} B S hS Z) c hZrep hc V₀ W₀ a b P P₁ (yoneda.obj Z) hP hP₁ eP e₁
    (PresheafOfCategories.sliceElementsEquivalenceOver Z) ξ _ hξeq hξ0

/-- Let `c : Z ⟶ 𝒴₀` be a 1-morphism locally of finite type from an object `Z` of the site, read
as an algebraic stack through the slice of the site over it, to an algebraic stack; let `V ⟶ 𝒴₀`
be a smooth chart by a scheme of the site, not assumed surjective; let `P` be an algebraic space
representing `Z ×_𝒴₀ V`; and let `ξ₀ ∈ |P|` be a point at which the projection `P ⟶ V` has
relative dimension zero in the sense of **Stacks 04NM**. Then some open `V₁` of the scheme `Z`
contains the image of `ξ₀` in `Z` and the restriction of `c` to `V₁` is locally quasi-finite in
the sense of **Stacks 04XB**. -/
theorem exists_opens_isLocallyQuasiFinite_schemeStack_of_hasRelativeDimensionAt_zero
    (hc : AlgebraicStacks.IsLocallyOfFiniteType B S hS c)
    (V₀ : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS V₀ ⟶ 𝒴₀)
    (haSm : AlgebraicStacks.IsSmooth B S hS a)
    (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hP : IsAlgebraicSpace B S hS P)
    (eP : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val.val.p
      (presheafOfCategories (P ⋙ typeToCat)).p)
    (ξ₀ : Space.points B S hS P)
    (hξ₀ : Space.HasRelativeDimensionAt 0 B S hS
      (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val
        (schemeStack.{u, w} B S hS V₀).val P (yoneda.obj V₀) eP
        (PresheafOfCategories.sliceElementsEquivalenceOver V₀)
        (twoFibreProductSquareAlgebraicStacks B S hS a c).fst.hom) ξ₀) :
    ∃ V₁ : ((BigFppfOver.toScheme B S hS).obj Z).Opens,
      Space.pointsToScheme B S hS Z (Space.pointsMap B S hS P
          (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val
            (schemeStack.{u, w} B S hS Z).val P (yoneda.obj Z) eP
            (PresheafOfCategories.sliceElementsEquivalenceOver Z)
            (twoFibreProductSquareAlgebraicStacks B S hS a c).snd.hom) ξ₀) ∈ V₁ ∧
        IsLocallyQuasiFinite B S hS
          (schemeStackMap.{u, w} B S hS (AlgebraicStacks.openChartHom B S hS Z V₁) ≫ c).hom := by
  classical
  have hsndSm : AlgebraicStacks.IsSmooth B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS a c).snd :=
    AlgebraicStacks.isSmooth_baseChange B S hS a c
      (twoFibreProductSquareAlgebraicStacks B S hS a c).swap
      (Bicategory.isTwoFibreProduct_swap
        (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a c)) haSm
  have hπSm : Space.IsSmooth B S hS
      (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val
        (schemeStack.{u, w} B S hS Z).val P (yoneda.obj Z) eP
        (PresheafOfCategories.sliceElementsEquivalenceOver Z)
        (twoFibreProductSquareAlgebraicStacks B S hS a c).snd.hom) :=
    isSmooth_representingMap_of_isSmooth B S hS
      (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS)
      (𝒳 := (twoFibreProductSquareAlgebraicStacks B S hS a c).pt)
      (𝒴 := schemeStack.{u, w} B S hS Z) P (yoneda.obj Z) hP
      (isAlgebraicSpace_yoneda B S hS Z) eP
      (PresheafOfCategories.sliceElementsEquivalenceOver Z) _ hsndSm
  have hprFT := isLocallyOfFiniteType_representingMap_fst_of_isLocallyOfFiniteType.{u, w}
    B S hS 𝒴₀ _ c hc V₀ a (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS a c)
    P hP eP
  refine ⟨⟨Space.pointsToScheme B S hS Z '' (Space.pointsMap B S hS P
          (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val
            (schemeStack.{u, w} B S hS Z).val P (yoneda.obj Z) eP
            (PresheafOfCategories.sliceElementsEquivalenceOver Z)
            (twoFibreProductSquareAlgebraicStacks B S hS a c).snd.hom) ''
        {ξ : Space.points B S hS P | ∃ d : ℕ∞, d ≤ ((0 : ℕ) : ℕ∞) ∧
          Space.HasRelativeDimensionAt d B S hS
            (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS a c).pt.val
              (schemeStack.{u, w} B S hS V₀).val P (yoneda.obj V₀) eP
              (PresheafOfCategories.sliceElementsEquivalenceOver V₀)
              (twoFibreProductSquareAlgebraicStacks B S hS a c).fst.hom) ξ}),
      (Space.isOpen_pointTopology_yoneda_iff_isOpen_image B S hS Z _).mp
        (Space.isOpenMap_pointsMap_of_isFlat_of_isLocallyOfFinitePresentation B S hS hP
          (isAlgebraicSpace_yoneda B S hS Z) _
          (Space.isFlat_of_isSmooth B S hS _ hπSm)
          (Space.isLocallyOfFinitePresentation_of_isSmooth B S hS hπSm) _
          (Space.isOpen_setOf_hasRelativeDimensionAt_le B S hS hP
            (isAlgebraicSpace_yoneda B S hS V₀) _ hprFT 0))⟩,
    ⟨_, ⟨ξ₀, ⟨0, by simp, hξ₀⟩, rfl⟩, rfl⟩,
    isLocallyQuasiFinite_openChart_comp_of_forall_exists_hasRelativeDimensionAt_zero.{u, w}
      B S hS 𝒴₀ Z c _ hc V₀ a P hP eP (fun z hz => ?_)⟩
  obtain ⟨z', ⟨ξ, ⟨d, hd0, hdξ⟩, hzξ⟩, hz'⟩ := hz
  have hzz : z' = z := (Space.bijective_pointsToScheme B S hS Z).injective hz'
  subst hzz
  refine ⟨ξ, hzξ, ?_⟩
  have hd : d = 0 := le_antisymm (by simpa using hd0) zero_le
  rw [← hd]
  exact hdξ

end SliceSource

end AlgebraicGeometry.Stack

end
