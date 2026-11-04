module

public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningDeformationProperties
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.ProperFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.CancelTwoFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.DescendingStacksAlongLimit
public import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentableUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointsMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperClosedImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedStackFactorization
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationOverBase
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.Substack
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningQuasiDMDeligneMumford
public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffine

/-!
# More of Stacks 0CJC: locally quasi-finite, monomorphism, finite

Consider the commutative diagram of thickenings of algebraic stacks over `S` of **Stacks 0CJC**:
`(𝒳 ⊂ 𝒳') ⟶ (𝒴 ⊂ 𝒴')` over a thickening `iB : ℬ ⟶ ℬ'`, with `𝒴' ⟶ ℬ'` locally of finite type,
`𝒳' ⟶ ℬ'` flat and locally of finite presentation, and the two restricted stacks the base
changes of the ambient ones. `StacksFrontier.AlgebraicGeometry.Stacks.ThickeningDeformationProperties`
proves items (1), (6) and (7). This file proves items (4), (5) and (10): `f` is a monomorphism,
locally quasi-finite, resp. finite, exactly when `f'` is.

None of these properties is smooth local on the source, so none goes through the smooth-diagram
reduction of `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_iff_of_flatDeformation`.

* Local quasi-finiteness is by **Stacks 06PU** three conditions, carried separately: the
  quasi-DM condition is item (8) of **Stacks 0CJ9**; local finite type holds for both
  1-morphisms outright; discreteness of the fibres over field-valued points passes along the
  thickening because a 1-morphism out of a reduced algebraic stack into the ambient stack of a
  thickening factors through it
  (`AlgebraicGeometry.Stack.exists_hom_comp_iso_of_isThickening_of_isReducedStack`, from
  **Stacks 050B**).
* Monomorphisms and finite 1-morphisms are representable by algebraic spaces, which passes by
  item (12) of **Stacks 0CJ9**
  (`AlgebraicGeometry.Stack.AlgebraicStacks.isRepresentableByAlgebraicSpaces_iff_ambient`), and
  the property of the representing morphisms of algebraic spaces passes across the cartesian
  square of thickenings by the point test of **Stacks 0BPJ**, parts (6) and (2)
  (`AlgebraicGeometry.Stack.AlgebraicStacks.hasRelativeProperty_iff_of_pointTest`); neither
  flatness nor any part of Stacks 0CGX is needed.

## Main results

* `AlgebraicGeometry.Stack.exists_hom_comp_iso_of_isThickening_of_isReducedStack`.
* `AlgebraicGeometry.Stack.discreteTopology_points_twoFibreProduct_of_isThickening_lift`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyQuasiFinite_iff_isLocallyQuasiFinite_ambient`:
  **Stacks 0CJC**, locally quasi-finite.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isRepresentableByAlgebraicSpaces_iff_ambient`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.hasRelativeProperty_iff_of_pointTest`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isMonomorphism_iff_isMonomorphism_ambient` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.isFinite_iff_isFinite_ambient`: **Stacks 0CJC**,
  monomorphism and finite.

## References

* [Stacks Project, Tag 050B](https://stacks.math.columbia.edu/tag/050B)
* [Stacks Project, Tag 06PU](https://stacks.math.columbia.edu/tag/06PU)
* [Stacks Project, Tag 0BPJ](https://stacks.math.columbia.edu/tag/0BPJ)
* [Stacks Project, Tag 0CJ9](https://stacks.math.columbia.edu/tag/0CJ9)
* [Stacks Project, Tag 0CJC](https://stacks.math.columbia.edu/tag/0CJC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CatFiberedInGroupoids
open Stacks.Thickenings

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {ℬ ℬ' 𝒴' 𝒳' : AlgebraicStacks.{u, w} B S hS}

/-! ### A 1-morphism out of a reduced algebraic stack lifts along a thickening -/

/-- **A 1-morphism from a reduced algebraic stack into the ambient stack of a thickening factors
through the thickening.** This is **Stacks 050B** at the closed substack cut out by the essential
image of the thickening, together with **Stacks 0506**.

A thickening is a closed immersion, so its essential image cuts out a closed substack
(`AlgebraicGeometry.Stack.AlgebraicStacks.isClosedSubstack_essImage`) which is an algebraic stack
and onto which the thickening restricts to an equivalence
(`AlgebraicGeometry.Stack.AlgebraicStacks.essImageEquivalence`, read in the 2-category of
algebraic stacks by `AlgebraicGeometry.Stack.equivalenceOfBasedEquivalence`). The hypothesis of
Stacks 050B — that the image on points lands in the substack — is free here, because a thickening
is by definition *surjective* on points, so the inclusion of the substack is already surjective on
points. Stacks 050B then factors the 1-morphism through the substack, and composing with the
inverse of the equivalence lands it in the source of the thickening. -/
theorem exists_hom_comp_iso_of_isThickening_of_isReducedStack
    {𝒦 𝒵 𝒵' : AlgebraicStacks.{u, w} B S hS} {j : 𝒵 ⟶ 𝒵'} (hj : IsThickening j)
    (hK : IsReducedStack B S hS 𝒦) (g : 𝒦 ⟶ 𝒵') :
    ∃ g₀ : 𝒦 ⟶ 𝒵, Nonempty (g₀ ≫ j ≅ g) := by
  classical
  have hjimm : AlgebraicStacks.IsImmersion B S hS j :=
    AlgebraicStacks.isImmersion_of_isClosedImmersion B S hS j hj.1
  have hA : IsAlgebraicStack.{u, w} B S hS
      (fullSubcategoryBased 𝒵' (CatFiberedInGroupoids.homFunctor j.hom).essImage) :=
    AlgebraicStacks.isAlgebraicStack_essImage j hjimm
  have hcl : IsClosedSubstack 𝒵' (CatFiberedInGroupoids.homFunctor j.hom).essImage :=
    AlgebraicStacks.isClosedSubstack_essImage j hj.1
  set incl := fullSubcategoryInclusion 𝒵'
    (CatFiberedInGroupoids.homFunctor j.hom).essImage hA
  set e : Bicategory.Equivalence 𝒵 (fullSubcategoryAlgebraicStack 𝒵'
      (CatFiberedInGroupoids.homFunctor j.hom).essImage hA) :=
    equivalenceOfBasedEquivalence.{u, w} B S hS
      (AlgebraicStacks.essImageEquivalence j hjimm)
  have hα : e.hom ≫ incl ≅ j :=
    Bicategory.InducedBicategory.isoMk
      (Bicategory.InducedBicategory.isoMk (AlgebraicStacks.toEssImageBasedSquareIso j))
  have hrange : Set.range (AlgebraicStacks.pointsMap B S hS g) ⊆
      Set.range (AlgebraicStacks.pointsMap B S hS incl) := by
    rintro q -
    obtain ⟨p, rfl⟩ := hj.2 q
    exact ⟨AlgebraicStacks.pointsMap B S hS e.hom p,
      (congrFun (AlgebraicStacks.pointsMap_comp B S hS e.hom incl) p).symm.trans
        (congrFun (AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS hα.hom) p)⟩
  obtain ⟨gb, ⟨β⟩⟩ :=
    (factorsThroughSubstack_iff_range_pointsMap_subset B S hS g hcl hA hK).2 hrange
  set gZ : 𝒦 ⟶ fullSubcategoryAlgebraicStack 𝒵'
      (CatFiberedInGroupoids.homFunctor j.hom).essImage hA :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom gb)
  have hβ : gZ ≫ incl ≅ g :=
    Bicategory.InducedBicategory.isoMk (Bicategory.InducedBicategory.isoMk β)
  refine ⟨gZ ≫ e.inv, ⟨?_⟩⟩
  have hη : e.inv ≫ j ≅ incl :=
    Bicategory.whiskerLeftIso e.inv hα.symm ≪≫ (Bicategory.associator e.inv e.hom incl).symm ≪≫
      Bicategory.whiskerRightIso e.counit incl ≪≫ Bicategory.leftUnitor incl
  exact (Bicategory.associator gZ e.inv j) ≪≫ Bicategory.whiskerLeftIso gZ hη ≪≫ hβ

/-! ### The fibres over field-valued points along a thickening of the target -/

/-- **The fibre of a 1-morphism of algebraic stacks over a field-valued point of the target is the
fibre of its base change along a thickening over any lift of that point.** Let `f'` be a
1-morphism, `jY` a thickening of its target and `R` a 2-fibre product square exhibiting `R.fst` as
the base change of `f'` along `jY`. A 1-morphism `g` out of `𝒦` which lifts through `jY` along
`θ` has its fibre of `f'` 2-equivalent to the fibre of `R.fst` over the lift, so the two have
discrete spaces of points together.

Cancelling the inner square off the iterated product
(`AlgebraicGeometry.Stack.cancelSndEquivSquareAlgebraicStacks`, **Stacks 02XD**) exhibits the
fibre of `R.fst` over the lift as a 2-fibre product of the cospan `(g, f')`, of which the
canonical square of **Stacks 04T2** is another; discreteness on points is a property of the cospan
by `AlgebraicGeometry.Stack.discreteTopology_points_congr`. -/
theorem discreteTopology_points_twoFibreProduct_of_isThickening_lift
    {𝒦 𝒴 𝒴'' 𝒳'' : AlgebraicStacks.{u, w} B S hS} (f' : 𝒳'' ⟶ 𝒴'') (jY : 𝒴 ⟶ 𝒴'')
    (R : Bicategory.TwoCommSq jY f') (hR : Bicategory.IsTwoFibreProduct R)
    {g₀ : 𝒦 ⟶ 𝒴} {g : 𝒦 ⟶ 𝒴''} (θ : g₀ ≫ jY ≅ g)
    (h : @DiscreteTopology
        (points B S hS (twoFibreProductSquareAlgebraicStacks B S hS R.fst g₀).pt.val.val
          (twoFibreProductSquareAlgebraicStacks B S hS R.fst g₀).pt.val.property)
        (pointTopology B S hS (twoFibreProductSquareAlgebraicStacks B S hS R.fst g₀).pt.val)) :
    @DiscreteTopology
      (points B S hS (twoFibreProductSquareAlgebraicStacks B S hS f' g).pt.val.val
        (twoFibreProductSquareAlgebraicStacks B S hS f' g).pt.val.property)
      (pointTopology B S hS (twoFibreProductSquareAlgebraicStacks B S hS f' g).pt.val) := by
  classical
  set cmp := (canonicalPreHomAlgebraicStacks B S hS f' jY R.swap).hom
  have hequiv : cmp.hom.hom.toFunctor.IsEquivalence :=
    isEquivalence_of_isTwoFibreProduct_algebraicStacks B S hS
      (Bicategory.isTwoFibreProduct_swap hR)
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f' jY)
      (canonicalPreHomAlgebraicStacks B S hS f' jY R.swap)
  exact discreteTopology_points_congr B S hS
    (cancelSndEquivSquareAlgebraicStacks B S hS f' jY cmp g₀ g θ).underlying
    (twoFibreProductSquareAlgebraicStacks B S hS f' g).underlying
    (isTwoFibreProduct_underlying_algebraicStacks B S hS _
      (isTwoFibreProduct_cancelSndEquivSquareAlgebraicStacks B S hS f' jY cmp g₀ g θ hequiv))
    (isTwoFibreProduct_underlying_algebraicStacks B S hS _
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f' g))
    h

namespace AlgebraicStacks

/-- The restriction of a thickening to a cartesian square over it is a thickening. -/
private theorem isThickening_fst_of_isTwoFibreProduct {iB : ℬ ⟶ ℬ'} {p : 𝒳' ⟶ ℬ'}
    {P : Bicategory.TwoCommSq p iB} (hiB : Stack.IsThickening iB)
    (hcart : Bicategory.IsTwoFibreProduct P) : Stack.IsThickening P.fst :=
  Stack.isThickening_baseChange B S hS iB p P.swap (Bicategory.isTwoFibreProduct_swap hcart) hiB

/-- A 1-morphism over `pX'` locally of finite presentation is locally of finite type, by
Stacks 0464 and the cancellation Stacks 06U9. -/
private theorem isLocallyOfFiniteType_of_iso_of_isLocallyOfFinitePresentation
    {pX' : 𝒳' ⟶ ℬ'} {pY' : 𝒴' ⟶ ℬ'} {f' : 𝒳' ⟶ 𝒴'} (houter : f' ≫ pY' ≅ pX')
    (hXfp : IsLocallyOfFinitePresentation B S hS pX') : IsLocallyOfFiniteType B S hS f' :=
  isLocallyOfFiniteType_of_comp B S hS f' pY'
    (isLocallyOfFiniteType_of_twoIso B S hS (Bicategory.InducedBicategory.isoHom houter.symm)
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hXfp))

/-- **Stacks 0CJC, locally quasi-finite.** Under the hypotheses of
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_iff_isFlat_ambient`, the restricted 1-morphism
`f` is locally quasi-finite if and only if the ambient 1-morphism `f'` is locally quasi-finite.

Local quasi-finiteness is by **Stacks 06PU** three conditions, and each is carried separately;
none of them goes through the smooth-diagram reduction of
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_iff_of_flatDeformation`, local
quasi-finiteness not being smooth local on the source.

The quasi-DM condition is item (8) of **Stacks 0CJ9**,
`AlgebraicGeometry.Stack.isQuasiDM_inner_iff_outer`, read on the morphism of thickenings whose
ambient 1-morphism is `f'` and whose restricted one is `f` — the two thickenings being the base
changes of `iB`, which are thickenings by **Stacks 0BPR** — and converted to the longhand reading
of Stacks 04YW by `.isQuasiDMWithRepresentableDiagonal_iff_isQuasiDM`, the representability of a
relative diagonal being free (**Stacks 04XS**, part (1)).

Local finite type holds for *both* 1-morphisms outright, with no appeal to the thickening: `pX'`
is locally of finite presentation, hence locally of finite type (**Stacks 0464**), and `houter`
identifies it with `f' ≫ pY'`, so `f'` is locally of finite type by the cancellation
**Stacks 06U9** (`.isLocallyOfFiniteType_of_comp`), which needs nothing of `pY'`. For `f` it is
the base change of that (**Stacks 06FU**), and it is not even needed: it is read off the
hypothesis in the forward direction and supplied by base change in the converse.

The condition on the fibres is where the thickening enters. `Spec` of a field is reduced, so a
field-valued point of the ambient target lifts along the thickening `𝒴 ⟶ 𝒴'` by
`AlgebraicGeometry.Stack.exists_hom_comp_iso_of_isThickening_of_isReducedStack`, and the fibre of
`f'` over it is the fibre of `f` over the lift by
`AlgebraicGeometry.Stack.discreteTopology_points_twoFibreProduct_of_isThickening_lift`; the
reducedness of the field's stack is the scheme case of **Stacks 04YF**.

The converse is base change in one step: **Stacks 06UB**, `.isLocallyQuasiFinite_baseChange`, at
the cartesian square `AlgebraicGeometry.Stack.restrictedSourceSq`. -/
@[stacks 0CJC "locally quasi-finite"]
theorem isLocallyQuasiFinite_iff_isLocallyQuasiFinite_ambient
    {iB : ℬ ⟶ ℬ'} {pX' : 𝒳' ⟶ ℬ'} {pY' : 𝒴' ⟶ ℬ'}
    {PX : Bicategory.TwoCommSq pX' iB} {PY : Bicategory.TwoCommSq pY' iB}
    {f : PX.pt ⟶ PY.pt} {f' : 𝒳' ⟶ 𝒴'}
    (hiB : IsThickening iB)
    (hcartX : Bicategory.IsTwoFibreProduct PX) (hcartY : Bicategory.IsTwoFibreProduct PY)
    (houter : f' ≫ pY' ≅ pX')
    (hrestrict : f ≫ PY.fst ≅ PX.fst ≫ f')
    (hinner : f ≫ PY.snd ≅ PX.snd)
    (hcoh : Bicategory.whiskerLeft f PY.iso.hom ≫ Bicategory.whiskerRight hinner.hom iB =
      Bicategory.whiskerRight hrestrict.hom pY' ≫
        Bicategory.whiskerLeft PX.fst houter.hom ≫ PX.iso.hom)
    (hYft : IsLocallyOfFiniteType B S hS pY')
    (hXflat : IsFlat B S hS pX')
    (hXfp : IsLocallyOfFinitePresentation B S hS pX') :
    IsLocallyQuasiFinite B S hS f ↔ IsLocallyQuasiFinite B S hS f' := by
  classical
  -- the two thickenings of the diagram, as base changes of `iB` (Stacks 0BPR)
  have hiX := isThickening_fst_of_isTwoFibreProduct B S hS hiB hcartX
  have hiY := isThickening_fst_of_isTwoFibreProduct B S hS hiB hcartY
  -- the quasi-DM condition, by item (8) of Stacks 0CJ9
  have hqdm : IsQuasiDMWithRepresentableDiagonal B S hS f ↔
      IsQuasiDMWithRepresentableDiagonal B S hS f' :=
    (isQuasiDMWithRepresentableDiagonal_iff_isQuasiDM B S hS f).trans
      ((Stack.isQuasiDM_inner_iff_outer B S hS
          ({ outer := f', inner := f, comm := hrestrict } :
            Stack.ThickeningMorphism PX.fst PY.fst hiX hiY)).trans
        (isQuasiDMWithRepresentableDiagonal_iff_isQuasiDM B S hS f').symm)
  have hf'ft := isLocallyOfFiniteType_of_iso_of_isLocallyOfFinitePresentation B S hS houter hXfp
  have hcart := Stack.isTwoFibreProduct_restrictedSourceSq B S hS hcartX hcartY houter hrestrict
    hinner hcoh
  refine ⟨fun hf => ⟨hqdm.1 hf.1, hf'ft, ?_⟩, fun hf' => ?_⟩
  · -- the fibre over a field-valued point of the ambient target, by lifting the point
    intro k _ hk toBase g
    have hKred : IsReducedStack B S hS
        (Stack.schemeStack.{u, w} B S hS (Over.mk (⟨toBase⟩ : B.obj hk ⟶ B.obj hS))) :=
      (Stack.exists_scheme_atlas_iff_scheme B S hS (fun V : Scheme.{u} => IsReduced V) _).2
        (by change IsReduced (Spec (.of k)); infer_instance)
    obtain ⟨g₀, ⟨θ⟩⟩ :=
      Stack.exists_hom_comp_iso_of_isThickening_of_isReducedStack B S hS hiY hKred g
    exact Stack.discreteTopology_points_twoFibreProduct_of_isThickening_lift B S hS f' PY.fst
      (Stack.restrictedSourceSq B S hS PX PY hrestrict) hcart θ (hf.2.2 k hk toBase g₀)
  · -- the converse is base change along the thickening of the restricted target (Stacks 06UB)
    exact isLocallyQuasiFinite_baseChange B S hS f' PY.fst
      (Stack.restrictedSourceSq B S hS PX PY hrestrict) hcart hf'

/-! ### The items of Stacks 0CJC that go by the point test of Stacks 0BPJ -/

/-- **Item (12) of Stacks 0CJ9 in the diagram of Stacks 0CJC.**
For a commutative diagram of thickenings of algebraic stacks over `S` whose two restricted stacks
are the base changes of the ambient ones along the thickening `iB` of bases, the restricted
1-morphism `f` is representable by algebraic spaces if and only if the ambient 1-morphism `f'` is.

The two thickenings `𝒳 ⟶ 𝒳'` and `𝒴 ⟶ 𝒴'` are the base changes of `iB`, hence thickenings by
**Stacks 0BPR**, so `(f, f')` is a morphism of thickenings and this is
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_inner_iff_outer` read on it. -/
theorem isRepresentableByAlgebraicSpaces_iff_ambient
    {iB : ℬ ⟶ ℬ'} {pX' : 𝒳' ⟶ ℬ'} {pY' : 𝒴' ⟶ ℬ'}
    {PX : Bicategory.TwoCommSq pX' iB} {PY : Bicategory.TwoCommSq pY' iB}
    {f : PX.pt ⟶ PY.pt} {f' : 𝒳' ⟶ 𝒴'}
    (hiB : Stack.IsThickening iB)
    (hcartX : Bicategory.IsTwoFibreProduct PX) (hcartY : Bicategory.IsTwoFibreProduct PY)
    (hrestrict : f ≫ PY.fst ≅ PX.fst ≫ f') :
    Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom.hom ↔
      Stack.IsRepresentableByAlgebraicSpaces B S hS f'.hom.hom :=
  Stack.isRepresentableByAlgebraicSpaces_inner_iff_outer B S hS
    ({ outer := f', inner := f, comm := hrestrict } :
      Stack.ThickeningMorphism PX.fst PY.fst
        (isThickening_fst_of_isTwoFibreProduct B S hS hiB hcartX)
        (isThickening_fst_of_isTwoFibreProduct B S hS hiB hcartY))

/-- **A condition of Stacks 04XB holds for the restricted 1-morphism of a commutative diagram of
thickenings of algebraic stacks exactly when it holds for the ambient one, given the point test of
Stacks 0BPJ.** Under the hypotheses of
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_iff_isFlat_ambient` that the argument uses —
`𝒳' ⟶ ℬ'` locally of finite presentation and the two restricted stacks the base changes of the
ambient ones along `iB` — and with both 1-morphisms representable by algebraic spaces, a condition
of Stacks 04XB holds for `f` exactly when it holds for `f'`, as soon as `hpointTest` holds: the
condition transfers along a cartesian square of thickenings of algebraic *spaces* over `S` whose
two horizontal morphisms are locally of finite type.

The forward implication is
`AlgebraicGeometry.Stack.hasRelativeProperty_outer_of_inner_of_pointTest` at the cartesian square
`AlgebraicGeometry.Stack.restrictedSourceSq`, whose target leg is the thickening of the restricted
target — a base change of `iB`, hence a thickening by **Stacks 0BPR**. The engine's two
local-finite-type inputs are not hypotheses here: `f'` is locally of finite type by **Stacks
0464** and the cancellation **Stacks 06U9**, exactly as in
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyQuasiFinite_iff_isLocallyQuasiFinite_ambient`,
and `f` by base change (**Stacks 06FU**); both are read in the Section 04XB form by
`AlgebraicGeometry.Stack.hasPropertyOnEverySmoothDiagram_iff_relative`, the **Stacks 06FM**
comparison for a representable 1-morphism. The converse is base change, **Stacks 045C** at the
same square.

Neither flatness of `𝒳' ⟶ ℬ'` nor local finite type of `𝒴' ⟶ ℬ'` enters, and no part of **Stacks
0CGX** does: this is the road the items of 0CJC take that a flat deformation diagram cannot
carry. See the implementation notes of this file for which items those are and why the split is
forced. -/
theorem hasRelativeProperty_iff_of_pointTest
    {iB : ℬ ⟶ ℬ'} {pX' : 𝒳' ⟶ ℬ'} {pY' : 𝒴' ⟶ ℬ'}
    {PX : Bicategory.TwoCommSq pX' iB} {PY : Bicategory.TwoCommSq pY' iB}
    {f : PX.pt ⟶ PY.pt} {f' : 𝒳' ⟶ 𝒴'}
    (hiB : Stack.IsThickening iB)
    (hcartX : Bicategory.IsTwoFibreProduct PX) (hcartY : Bicategory.IsTwoFibreProduct PY)
    (houter : f' ≫ pY' ≅ pX')
    (hrestrict : f ≫ PY.fst ≅ PX.fst ≫ f')
    (hinner : f ≫ PY.snd ≅ PX.snd)
    (hcoh : Bicategory.whiskerLeft f PY.iso.hom ≫ Bicategory.whiskerRight hinner.hom iB =
      Bicategory.whiskerRight hrestrict.hom pY' ≫
        Bicategory.whiskerLeft PX.fst houter.hom ≫ PX.iso.hom)
    (hXfp : IsLocallyOfFinitePresentation B S hS pX')
    (hrepInner : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hrepOuter : Stack.IsRepresentableByAlgebraicSpaces B S hS f'.hom.hom)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    (hpointTest : ∀ {A A' C C' : AlgebraicSpaces B S hS} {a : A ⟶ A'} {b : C ⟶ C'}
      {p : A ⟶ C} {p' : A' ⟶ C'}, Space.IsThickeningHom B S hS a →
      Space.IsThickeningHom B S hS b → IsPullback p a b p' →
      Space.locallyOfFiniteTypeProperty B S hS p →
      Space.locallyOfFiniteTypeProperty B S hS p' → P p → P p') :
    Stack.HasRelativeProperty.{u, u, u + 1, u} B S hS P f.hom hrepInner ↔
      Stack.HasRelativeProperty.{u, u, u + 1, u} B S hS P f'.hom hrepOuter := by
  have : (Stack.spaceProperty B S hS
      (fun _ _ k => Space.IsLocallyOfFiniteType B S hS k)).IsStableUnderBaseChange :=
    Space.isLocallyOfFiniteType_isStableUnderBaseChange B S hS
  have : (Stack.spaceProperty B S hS
      (fun _ _ k => Space.IsLocallyOfFiniteType B S hS k)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  -- the thickening of the restricted target, a base change of `iB` (Stacks 0BPR)
  have hiY := isThickening_fst_of_isTwoFibreProduct B S hS hiB hcartY
  -- the restricted 1-morphism as a base change of the ambient one
  have hcart : Bicategory.IsTwoFibreProduct (Stack.restrictedSourceSq B S hS PX PY hrestrict) :=
    Stack.isTwoFibreProduct_restrictedSourceSq B S hS hcartX hcartY houter hrestrict hinner hcoh
  have hf'ft := isLocallyOfFiniteType_of_iso_of_isLocallyOfFinitePresentation B S hS houter hXfp
  -- and of the restricted one, by base change (Stacks 06FU)
  have hfft : IsLocallyOfFiniteType B S hS f :=
    isLocallyOfFiniteType_baseChange B S hS f' PY.fst
      (Stack.restrictedSourceSq B S hS PX PY hrestrict) hcart hf'ft
  -- both read in the Section 04XB form, by Stacks 06FM for a representable 1-morphism
  have hftInner : Stack.HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.locallyOfFiniteTypeProperty B S hS) f.hom hrepInner :=
    (Stack.hasPropertyOnEverySmoothDiagram_iff_relative.{u, u, w} B S hS
      (fun _ _ g => Space.IsLocallyOfFiniteType B S hS g)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
      PX.pt.property PY.pt.property f.hom hrepInner).1 hfft
  have hftOuter : Stack.HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.locallyOfFiniteTypeProperty B S hS) f'.hom hrepOuter :=
    (Stack.hasPropertyOnEverySmoothDiagram_iff_relative.{u, u, w} B S hS
      (fun _ _ g => Space.IsLocallyOfFiniteType B S hS g)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
      𝒳'.property 𝒴'.property f'.hom hrepOuter).1 hf'ft
  exact ⟨Stack.hasRelativeProperty_outer_of_inner_of_pointTest B S hS
      (Stack.restrictedSourceSq B S hS PX PY hrestrict) hcart hiY hrepInner hrepOuter P
      hpointTest hftInner hftOuter,
    Stack.hasRelativeProperty_baseChange_algebraicStacks B S hS P f' PY.fst
      (Stack.restrictedSourceSq B S hS PX PY hrestrict) hcart hrepOuter hrepInner⟩

/-- **Item (4) of Stacks 0CJC, monomorphism.** Under the
hypotheses of `AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_iff_isFlat_ambient`, the restricted
1-morphism `f` is a monomorphism in the sense of **Stacks 04ZW** if and only if the ambient
1-morphism `f'` is.

Being a monomorphism is representability by algebraic spaces together with a condition of Stacks
04XB at the monomorphisms of algebraic spaces. The first conjunct transfers by item (12) of
**Stacks 0CJ9**, `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_inner_iff_outer`, read
on the morphism of thickenings whose ambient 1-morphism is `f'` and whose restricted one is `f`.
The second is `AlgebraicGeometry.Stack.AlgebraicStacks.hasRelativeProperty_iff_of_pointTest` at
`CategoryTheory.MorphismProperty.monomorphisms`, whose point test is part (6) of **Stacks 0BPJ**,
`AlgebraicGeometry.Space.mono_iff_of_cartesianSquareOfThickeningHoms`, which asks no flatness;
fppf-target-locality of the monomorphisms is **Stacks 042D** and stability under base change an
instance.

Item (12) of Stacks 0CJ9 is unconditional, so nothing beyond the source's own hypotheses is
carried in either direction. -/
@[stacks 0CJC "monomorphism"]
theorem isMonomorphism_iff_isMonomorphism_ambient
    {iB : ℬ ⟶ ℬ'} {pX' : 𝒳' ⟶ ℬ'} {pY' : 𝒴' ⟶ ℬ'}
    {PX : Bicategory.TwoCommSq pX' iB} {PY : Bicategory.TwoCommSq pY' iB}
    {f : PX.pt ⟶ PY.pt} {f' : 𝒳' ⟶ 𝒴'}
    (hiB : Stack.IsThickening iB)
    (hcartX : Bicategory.IsTwoFibreProduct PX) (hcartY : Bicategory.IsTwoFibreProduct PY)
    (houter : f' ≫ pY' ≅ pX')
    (hrestrict : f ≫ PY.fst ≅ PX.fst ≫ f')
    (hinner : f ≫ PY.snd ≅ PX.snd)
    (hcoh : Bicategory.whiskerLeft f PY.iso.hom ≫ Bicategory.whiskerRight hinner.hom iB =
      Bicategory.whiskerRight hrestrict.hom pY' ≫
        Bicategory.whiskerLeft PX.fst houter.hom ≫ PX.iso.hom)
    (_hYft : IsLocallyOfFiniteType B S hS pY')
    (_hXflat : IsFlat B S hS pX')
    (hXfp : IsLocallyOfFinitePresentation B S hS pX') :
    IsMonomorphism B S hS f ↔ IsMonomorphism B S hS f' := by
  have hrepIff := isRepresentableByAlgebraicSpaces_iff_ambient B S hS hiB hcartX hcartY
    hrestrict
  have hiff := fun hrepInner hrepOuter => hasRelativeProperty_iff_of_pointTest B S hS hiB hcartX
    hcartY houter hrestrict hinner hcoh hXfp hrepInner hrepOuter
    (MorphismProperty.monomorphisms (AlgebraicSpaces B S hS))
    fun ha hb hsq hlft hlft' hmono =>
      (Space.mono_iff_of_cartesianSquareOfThickeningHoms B S hS ha hb hsq hlft hlft').1 hmono
  exact ⟨fun hf => ⟨hrepIff.1 hf.1, (hiff hf.1 (hrepIff.1 hf.1)).1 hf.2⟩,
    fun hf' => ⟨hrepIff.2 hf'.1, (hiff (hrepIff.2 hf'.1) hf'.1).2 hf'.2⟩⟩

/-- **Item (10) of Stacks 0CJC, finite.** Under the hypotheses of
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_iff_isFlat_ambient`, the restricted 1-morphism `f`
is finite in the sense of **Stacks 03ZP** read through Stacks 03YK if and only if the ambient
1-morphism `f'` is.

The companion of
`AlgebraicGeometry.Stack.AlgebraicStacks.isMonomorphism_iff_isMonomorphism_ambient` at
`AlgebraicGeometry.Space.finiteMorphismProperty`, whose point test is part (2) of **Stacks
0BPJ**, `AlgebraicGeometry.Space.finiteMorphismProperty_iff_of_cartesianSquareOfThickeningHoms`:
a morphism of algebraic spaces is finite exactly when it is proper and locally quasi-finite
(**Stacks 0A4X**), and both of those transfer across a cartesian square of thickenings with
locally-of-finite-type horizontals, with no flatness. Stability under base change and
fppf-target-locality (**Stacks 0426**) are both instances.

Representability of the two 1-morphisms comes from item (12) of Stacks 0CJ9 as in that theorem,
and is unconditional for the same reason. -/
@[stacks 0CJC "finite"]
theorem isFinite_iff_isFinite_ambient
    {iB : ℬ ⟶ ℬ'} {pX' : 𝒳' ⟶ ℬ'} {pY' : 𝒴' ⟶ ℬ'}
    {PX : Bicategory.TwoCommSq pX' iB} {PY : Bicategory.TwoCommSq pY' iB}
    {f : PX.pt ⟶ PY.pt} {f' : 𝒳' ⟶ 𝒴'}
    (hiB : Stack.IsThickening iB)
    (hcartX : Bicategory.IsTwoFibreProduct PX) (hcartY : Bicategory.IsTwoFibreProduct PY)
    (houter : f' ≫ pY' ≅ pX')
    (hrestrict : f ≫ PY.fst ≅ PX.fst ≫ f')
    (hinner : f ≫ PY.snd ≅ PX.snd)
    (hcoh : Bicategory.whiskerLeft f PY.iso.hom ≫ Bicategory.whiskerRight hinner.hom iB =
      Bicategory.whiskerRight hrestrict.hom pY' ≫
        Bicategory.whiskerLeft PX.fst houter.hom ≫ PX.iso.hom)
    (_hYft : IsLocallyOfFiniteType B S hS pY')
    (_hXflat : IsFlat B S hS pX')
    (hXfp : IsLocallyOfFinitePresentation B S hS pX') :
    IsFinite B S hS f ↔ IsFinite B S hS f' := by
  have hrepIff := isRepresentableByAlgebraicSpaces_iff_ambient B S hS hiB hcartX hcartY
    hrestrict
  have hiff := fun hrepInner hrepOuter => hasRelativeProperty_iff_of_pointTest B S hS hiB hcartX
    hcartY houter hrestrict hinner hcoh hXfp hrepInner hrepOuter
    (Space.finiteMorphismProperty B S hS)
    fun ha hb hsq hlft hlft' =>
      (Space.finiteMorphismProperty_iff_of_cartesianSquareOfThickeningHoms
        B S hS ha hb hsq hlft hlft').1
  exact ⟨fun hf => ⟨hrepIff.1 hf.choose, (hiff hf.choose (hrepIff.1 hf.choose)).1 hf.choose_spec⟩,
    fun hf' => ⟨hrepIff.2 hf'.choose, (hiff (hrepIff.2 hf'.choose) hf'.choose).2 hf'.choose_spec⟩⟩

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
