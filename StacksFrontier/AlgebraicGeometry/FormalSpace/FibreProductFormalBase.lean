module

public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitOfSchemeThickenings
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductRefined
public import StacksFrontier.CategoryTheory.Filtered.ProdPreorder
public import StacksFrontier.CategoryTheory.Limits.RelativeProductOfColimits
public import StacksFrontier.CategoryTheory.Sites.FilteredUniversalColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineFibreProductRefined

/-!
# Fibre products of formal algebraic spaces over a formal algebraic space

Let `S` be a scheme contained in a big fppf site `B`. **Stacks 0AJ3** says that the category of
formal algebraic spaces over `S` has fibre products. The content is that the fibre product
`X ×_Z Y` of two formal algebraic spaces over a formal algebraic space `Z` is again a formal
algebraic space, after which the fibre product in the full subcategory is the fibre product of
the underlying fppf sheaves.

## Main results

* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_of_isAffineFormal_of_isFormal`:
  the affine case, which is the hypothesis `hstage` of
  `FormalSpace.isFormalAlgebraicSpace_pullback_of_affineStages_of_representableProducts`,
  discharged.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_of_isFormalAlgebraicSpace`: the
  fibre product of two formal algebraic spaces over a formal algebraic space is a formal
  algebraic space.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace`:
  the same for the fibre product of a morphism with an affine formal chart of its target, which
  is the shape in which the proofs of Stacks 0ANG, 0ANL, 0ANW, 0GBB, 0GBI and 0GBM use it.
* `AlgebraicGeometry.FormalSpace.FormalAlgebraicSpaces`: the category of formal algebraic spaces
  over `S`, the full subcategory of fppf sheaves cut out by
  `AlgebraicGeometry.IsFormalAlgebraicSpace`.
* `AlgebraicGeometry.FormalSpace.hasPullbacks_formalAlgebraicSpaces`: **Stacks 0AJ3**.

## Implementation notes

*The affine case.* Write `X = colim_λ Spec A_λ` and `Y = colim_μ Spec B_μ` along thickenings,
which is what being an affine formal algebraic space provides (**Stacks 0AI7**). A filtered
colimit of fppf sheaves is a universal colimit
(`CategoryTheory.Limits.sheaf_filteredColimit_isUniversalColimit`), so

`X ×_Z Y = colim_{λ, μ} (Spec A_λ ×_Z Spec B_μ)`

by `CategoryTheory.Limits.isColimit_relativeProductCocone`. Here the hypothesis on `Z` enters
twice. First, `Z` being a formal algebraic space, every morphism to it out of a representable
sheaf is representable **by objects of the site** — the representability assertion of
**Stacks 0AIP**, `…hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace` — so each stage
`Spec A_λ ×_Z Spec B_μ` is represented by an object of the site, and the diagram of stages lifts
to a diagram in the site along the fully faithful sheafified Yoneda embedding
(`CategoryTheory.Functor.essImage.liftFunctor`). Second, each transition of that diagram
factors, through the intermediate stage `Spec A_{λ'} ×_Z Spec B_μ`, as a base change of
`Spec A_λ ⟶ Spec A_{λ'}` followed by a base change of `Spec B_μ ⟶ Spec B_{μ'}`
(`CategoryTheory.Limits.uncurry_relativeProductDiagram_map` with
`CategoryTheory.Limits.isPullback_relativeBaseTransition` and
`CategoryTheory.Limits.equifibered_relativeStageSnd`), and a base change of a thickening is a
thickening (**Stacks 09ZU**), so the transitions of the lifted diagram are thickenings of
schemes. That is exactly the input of
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_colimit_siteThickenings`.

The index of the colimit is the product of the two presentation indices, carrying the product
*preorder* rather than the product category structure: `CategoryTheory.ProdPreorder`, with
`CategoryTheory.prodPreorderEquivalence` comparing the two.

Nothing set-theoretic is assumed: the condition of **Stacks 0AIS** for the fibre product is
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_pullback'`, which asks of each leg
only the condition itself and representable relative products, both of which an affine formal
algebraic space has.

*Why this is not Stacks 0AJ2.* Stacks 0AJ2 concludes the same for a `Z` whose diagonal is
representable only by *algebraic spaces*. That hypothesis is strictly weaker than being a formal
algebraic space, and under it the stages of the colimit above are algebraic spaces rather than
schemes, so neither half of the argument here is available: it needs Stacks 05ZH for
thickenings of algebraic spaces at arbitrary order and Stacks 07VT. No declaration below
carries a 0AJ2 attribute.

## References

* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
* [Stacks Project, Tag 0AJ2](https://stacks.math.columbia.edu/tag/0AJ2)
* [Stacks Project, Tag 0AJ3](https://stacks.math.columbia.edu/tag/0AJ3)
* [Stacks Project, Tag 09ZU](https://stacks.math.columbia.edu/tag/09ZU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Thickenings

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The affine case -/

/-- The property of a morphism of the big fppf site over `S` that its underlying morphism of
schemes is a **thickening**. It is an `abbrev` so that the instances of `MorphismProperty` it
inherits -- stability under composition and under base change -- are found by instance
resolution. -/
private abbrev IsThickeningSite : MorphismProperty (BigFppfOver B S hS) :=
  MorphismProperty.inverseImage (@IsThickening : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)

private instance isStableUnderBaseChange_isThickeningSite :
    (IsThickeningSite B S hS).IsStableUnderBaseChange :=
  BigFppfOver.isStableUnderBaseChange_inverseImage B S hS
    (@IsThickening : MorphismProperty Scheme.{u})

/-- **The fibre product of two affine formal algebraic spaces over a formal algebraic space is a
formal algebraic space.**

This is the hypothesis `hstage` of
`FormalSpace.isFormalAlgebraicSpace_pullback_of_affineStages_of_representableProducts`,
proved for a base which is a formal algebraic space. The fibre product is the colimit of the
fibre products `Spec A_λ ×_Z Spec B_μ` of the stages of the two presentations; those are
schemes, because the diagonal of a formal algebraic space is representable by objects of the
site, and the transitions between them are thickenings, being composites of base changes of the
transitions of the two presentations. So
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_colimit_siteThickenings` applies. -/
theorem isFormalAlgebraicSpace_pullback_of_isAffineFormal_of_isFormal
    {X Y Z : FppfSheaf B S hS} (p : X ⟶ Z) (q : Y ⟶ Z)
    (hZ : IsFormalAlgebraicSpace B S hS Z)
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y) :
    IsFormalAlgebraicSpace B S hS (pullback p q) := by
  classical
  let J := BigFppfOver.topology B S hS
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have : J.Subcanonical := bigFppfOver_subcanonical B S hS
  have : (Sheaf.sheafifiedYoneda J).Full := inferInstance
  have : (Sheaf.sheafifiedYoneda J).Faithful := inferInstance
  have : PreservesLimitsOfShape WalkingCospan (Sheaf.sheafifiedYoneda J) :=
    preservesLimitsOfShape_walkingCospan_sheafifiedYoneda B S hS
  have hZrep := hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace B S hS hZ
  have hset : SatisfiesSetTheoreticCondition B S hS (pullback p q) :=
    satisfiesSetTheoreticCondition_pullback' B S hS p q hZrep hX.1
      (hasRepresentableRelativeProducts_of_isAffineFormalAlgebraicSpace B S hS hX) hY.1
      (hasRepresentableRelativeProducts_of_isAffineFormalAlgebraicSpace B S hS hY)
  obtain ⟨-, I₁, pre₁, hne₁, hdir₁, D₁, hD₁, ⟨eX⟩⟩ := hX
  obtain ⟨-, I₂, pre₂, hne₂, hdir₂, D₂, hD₂, ⟨eY⟩⟩ := hY
  let : Preorder I₁ := pre₁
  let : Nonempty I₁ := hne₁
  let : IsDirected I₁ (· ≤ ·) := hdir₁
  let : Preorder I₂ := pre₂
  let : Nonempty I₂ := hne₂
  let : IsDirected I₂ (· ≤ ·) := hdir₂
  set F₁ : I₁ ⥤ FppfSheaf B S hS :=
    D₁ ⋙ BigAffineFppf.inclusion B S hS ⋙ Sheaf.sheafifiedYoneda J with hF₁
  set F₂ : I₂ ⥤ FppfSheaf B S hS :=
    D₂ ⋙ BigAffineFppf.inclusion B S hS ⋙ Sheaf.sheafifiedYoneda J with hF₂
  set c₁ := colimit.cocone F₁ with hc₁
  set c₂ := colimit.cocone F₂ with hc₂
  set a : c₁.pt ⟶ Z := eX.inv ≫ p with ha
  set b : c₂.pt ⟶ Z := eY.inv ≫ q with hb
  have h₁ : IsUniversalColimit c₁ := sheaf_filteredColimit_isUniversalColimit J F₁
  have h₂ : IsUniversalColimit c₂ := sheaf_filteredColimit_isUniversalColimit J F₂
  -- the two-variable diagram of stages, reindexed by the product preorder
  set Θ := CategoryTheory.prodPreorderEquivalence I₁ I₂ with hΘ
  set Big := Functor.uncurry.obj (relativeProductDiagram c₁ c₂ a b) with hBig
  set E₀ : CategoryTheory.ProdPreorder I₁ I₂ ⥤ FppfSheaf B S hS := Θ.functor ⋙ Big with hE₀
  have hE₀colim : IsColimit ((relativeProductCocone c₁ c₂ a b).whisker Θ.functor) :=
    (isColimit_relativeProductCocone c₁ c₂ a b h₁ h₂).whiskerEquivalence Θ
  -- every stage is represented by an object of the site
  have hess : ∀ l : CategoryTheory.ProdPreorder I₁ I₂,
      (Sheaf.sheafifiedYoneda J).essImage (E₀.obj l) := by
    intro l
    obtain ⟨P, pr, fs, hpb⟩ := hZrep (c₁.ι.app (Θ.functor.obj l).1 ≫ a)
      (c₂.ι.app (Θ.functor.obj l).2 ≫ b)
    exact ⟨P, ⟨hpb.isoPullback⟩⟩
  set Dsite := Functor.essImage.liftFunctor E₀ (Sheaf.sheafifiedYoneda J) hess with hDsite
  have eD : Dsite ⋙ Sheaf.sheafifiedYoneda J ≅ E₀ :=
    Functor.essImage.liftFunctorCompIso E₀ (Sheaf.sheafifiedYoneda J) hess
  -- the transitions of the lifted diagram are thickenings
  have hthick : ∀ ⦃l m : CategoryTheory.ProdPreorder I₁ I₂⦄ (f : l ⟶ m),
      IsThickening ((BigFppfOver.toScheme B S hS).map (Dsite.map f)) := by
    intro l m f
    have : ((IsThickeningSite B S hS).relative
        (Sheaf.sheafifiedYoneda J)).IsStableUnderBaseChange :=
      MorphismProperty.relative_isStableUnderBaseChange (IsThickeningSite B S hS)
    have : (IsThickeningSite B S hS).IsStableUnderComposition :=
      MorphismProperty.IsStableUnderComposition.inverseImage (BigFppfOver.toScheme B S hS)
    have : ((IsThickeningSite B S hS).relative
        (Sheaf.sheafifiedYoneda J)).IsStableUnderComposition :=
      MorphismProperty.relative_isStableUnderComposition (IsThickeningSite B S hS)
    -- the first-variable leg
    have hQ₁ : (IsThickeningSite B S hS).relative (Sheaf.sheafifiedYoneda J)
        (F₁.map (Θ.functor.map f).1) :=
      MorphismProperty.relative_map (hD₁ (Θ.functor.map f).1)
    have hbase : (IsThickeningSite B S hS).relative (Sheaf.sheafifiedYoneda J)
        (relativeBaseTransition c₁ c₂ a b (Θ.functor.map f).1 (Θ.functor.obj l).2) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (isPullback_relativeBaseTransition c₁ c₂ a b
          (Θ.functor.map f).1 (Θ.functor.obj l).2).flip hQ₁
    -- the second-variable leg
    have hQ₂ : (IsThickeningSite B S hS).relative (Sheaf.sheafifiedYoneda J)
        (F₂.map (Θ.functor.map f).2) :=
      MorphismProperty.relative_map (hD₂ (Θ.functor.map f).2)
    have hstage : (IsThickeningSite B S hS).relative (Sheaf.sheafifiedYoneda J)
        (relativeStageTransition c₁ c₂ a b (Θ.functor.obj m).1 (Θ.functor.map f).2) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (equifibered_relativeStageSnd c₁ c₂ a b (Θ.functor.obj m).1
          (Θ.functor.map f).2).flip hQ₂
    have hcomp : (IsThickeningSite B S hS).relative (Sheaf.sheafifiedYoneda J) (E₀.map f) := by
      change (IsThickeningSite B S hS).relative (Sheaf.sheafifiedYoneda J)
        (Big.map (Θ.functor.map f))
      rw [uncurry_relativeProductDiagram_map]
      exact MorphismProperty.comp_mem _ _ _ hbase hstage
    have harr : Arrow.mk ((Dsite ⋙ Sheaf.sheafifiedYoneda J).map f) ≅ Arrow.mk (E₀.map f) :=
      Arrow.isoMk (eD.app l) (eD.app m) (eD.hom.naturality f).symm
    change IsThickeningSite B S hS (Dsite.map f)
    exact MorphismProperty.of_relative_map
      ((MorphismProperty.arrow_mk_iso_iff
        (P := (IsThickeningSite B S hS).relative (Sheaf.sheafifiedYoneda J)) harr).mpr hcomp)
  -- the fibre product is the colimit of the lifted diagram
  refine isFormalAlgebraicSpace_of_colimit_siteThickenings B S hS Dsite hthick
    (pullback p q) hset ⟨?_⟩
  have hsq : IsPullback (pullback.fst a b ≫ eX.inv) (pullback.snd a b ≫ eY.inv) p q := by
    refine (IsPullback.of_hasPullback a b).of_iso (Iso.refl _) eX.symm eY.symm (Iso.refl _)
      ?_ ?_ ?_ ?_
    · simp
    · simp
    · exact (Category.comp_id a).trans rfl
    · exact (Category.comp_id b).trans rfl
  exact hsq.isoPullback.symm ≪≫ hE₀colim.coconePointUniqueUpToIso (colimit.isColimit E₀) ≪≫
    (HasColimit.isoOfNatIso eD).symm

/-! ### Stacks 0AJ3 -/

/-- **The fibre product of two formal algebraic spaces over a formal algebraic space is a formal
algebraic space.** This is the content of **Stacks 0AJ3**, before the fibre product is read in
the category of formal algebraic spaces.

It is `FormalSpace.isFormalAlgebraicSpace_pullback_of_affineStages_of_representableProducts` with
both of its remaining hypotheses discharged for a base which is a formal algebraic space: `hZrep`
by the representability assertion of **Stacks 0AIP** and `hstage` by
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_of_isAffineFormal_of_isFormal`.

NO 0AJ2 ATTRIBUTE IS ATTACHED. Stacks 0AJ2 asks only that the diagonal of `Z` be representable
by algebraic spaces, which is strictly weaker than `Z` being a formal algebraic space; this is
the sub-case of that tag which **Stacks 0AJ3** uses, and the general case needs Stacks 05ZH
at arbitrary order and Stacks 07VT, which are not in this library. -/
theorem isFormalAlgebraicSpace_pullback_of_isFormalAlgebraicSpace
    {X Y Z : FppfSheaf B S hS} (p : X ⟶ Z) (q : Y ⟶ Z)
    (hZ : IsFormalAlgebraicSpace B S hS Z)
    (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y) :
    IsFormalAlgebraicSpace B S hS (pullback p q) :=
  isFormalAlgebraicSpace_pullback_of_affineStages_of_representableProducts B S hS p q
    (hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace B S hS hZ) hX hY
    (fun _X' _Y' p' q' hX' hY' ↦
      isFormalAlgebraicSpace_pullback_of_isAffineFormal_of_isFormal B S hS p' q' hZ hX' hY')

/-- **The fibre product of a morphism of formal algebraic spaces with an affine formal chart of
its target is a formal algebraic space.**

This is the shape in which **Stacks 0AJ3** is used in the proofs of Stacks 0ANG, 0ANL, 0ANW,
0GBB, 0GBI and 0GBM: the chart `V` of the target is an affine formal algebraic space, hence a
formal algebraic space by
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace`, so
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_of_isFormalAlgebraicSpace`
applies to `v` and `f` over `Y`. Nothing is asked of `v` beyond its existence; in the
applications it is a representable étale member of an atlas of `Y`. -/
theorem isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace
    {X Y V : FppfSheaf B S hS} (v : V ⟶ Y) (f : X ⟶ Y)
    (hY : IsFormalAlgebraicSpace B S hS Y)
    (hV : IsAffineFormalAlgebraicSpace B S hS V)
    (hX : IsFormalAlgebraicSpace B S hS X) :
    IsFormalAlgebraicSpace B S hS (pullback v f) :=
  isFormalAlgebraicSpace_pullback_of_isFormalAlgebraicSpace B S hS v f hY
    (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hV) hX

/-- **The category of formal algebraic spaces over `S`**: the full subcategory of fppf sheaves
on the big fppf site of `S` whose objects are the formal algebraic spaces over `S`. Its
morphisms are the morphisms of the underlying sheaves. -/
abbrev FormalAlgebraicSpaces : Type (u + 2) :=
  ObjectProperty.FullSubcategory (IsFormalAlgebraicSpace B S hS)

/-- **Stacks 0AJ3.** The category of formal algebraic spaces over a scheme `S` has fibre
products.

The fibre product is the fibre product of the underlying fppf sheaves: that is again a formal
algebraic space by
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_of_isFormalAlgebraicSpace`, so the
full inclusion into fppf sheaves creates fibre products and the subcategory inherits them. -/
@[stacks 0AJ3]
instance hasPullbacks_formalAlgebraicSpaces : HasPullbacks (FormalAlgebraicSpaces B S hS) := by
  let P : ObjectProperty (FppfSheaf B S hS) := IsFormalAlgebraicSpace B S hS
  let : CreatesLimitsOfShape WalkingCospan P.ι :=
    ⟨fun {F} ↦ by
      letI D := F ⋙ P.ι
      exact createsLimitFullSubcategoryInclusion' F
        ((IsLimit.postcomposeInvEquiv (diagramIsoCospan D) (pullback.cone _ _)).symm
          (limit.isLimit _))
        (isFormalAlgebraicSpace_pullback_of_isFormalAlgebraicSpace B S hS _ _
          (F.obj WalkingCospan.one).property (F.obj WalkingCospan.left).property
          (F.obj WalkingCospan.right).property)⟩
  exact hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape P.ι

end AlgebraicGeometry.FormalSpace

end
