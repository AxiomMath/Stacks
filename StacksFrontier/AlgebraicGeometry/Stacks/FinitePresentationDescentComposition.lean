module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFppfLocality
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationBaseChangeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeFppfDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentIngredients
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveProperties
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# Descent of local finite presentation across a surjective flat first factor (Stacks 06Q9)

**Stacks 06Q9.** Let `𝒳 ⟶ 𝒴 ⟶ 𝒵` be 1-morphisms of algebraic stacks over `S`. If the composite
`𝒳 ⟶ 𝒵` is locally of finite presentation and `𝒳 ⟶ 𝒴` is surjective, flat and locally of finite
presentation, then `𝒴 ⟶ 𝒵` is locally of finite presentation.

The property is descended across the *first* factor of a composite, which is the fppf-descent
direction on the **source**; for morphisms of algebraic spaces this is **Stacks 06EV**, local
finite presentation being local on the source for the fppf topology, consumed at the one-member
covering family cut out by a single surjective flat morphism locally of finite presentation.

The source's proof chooses three presentations by algebraic spaces: `W` smooth and surjective over
`𝒵`, then `V` smooth and surjective over `W ×_𝒵 𝒴`, then one of `V ×_𝒴 𝒳`; it observes that the
third is surjective, flat and locally of finite presentation over `V` and locally of finite
presentation over `W`, and appeals to the statement for algebraic spaces. Here only the third
presentation has to be chosen. Local finite presentation of a 1-morphism of algebraic stacks is
**Stacks 06Q2** part (1), the *universal* smooth-diagram condition of **Stacks 06FM**, so an
arbitrary smooth diagram `(V, W, a, b, h)` over `𝒴 ⟶ 𝒵` is handed to the proof and plays the role
of the source's first two choices. Writing `𝒱`, `𝒲` for the algebraic stacks of those two
algebraic spaces, the algebraic stack whose presentation is chosen is

`𝒱 ×_{𝒲 ×_𝒵 𝒴} ((𝒲 ×_𝒵 𝒴) ×_𝒴 𝒳)`,

where `𝒱` maps to `𝒲 ×_𝒵 𝒴` by the comparison 1-morphism the diagram's own clause makes smooth.
Its first projection to `𝒱` is a base change of a base change of `𝒳 ⟶ 𝒴`, hence surjective by
**Stacks 04ZU**, flat by **Stacks 06PY** and locally of finite presentation by **Stacks 06Q4**;
its second projection is a base change of that comparison, hence smooth by **Stacks 075W** and so
locally of finite presentation by **Stacks 0DNP**. Pasting the two 2-fibre products exhibits
`(𝒲 ×_𝒵 𝒴) ×_𝒴 𝒳` over the cospan `(𝒲 ⟶ 𝒵, 𝒳 ⟶ 𝒵)` (**Stacks 003Q**), so its projection to `𝒲`
is a base change of `𝒳 ⟶ 𝒵` and is locally of finite presentation.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_comp_of_fppf`: **Stacks 06EV**
  consumed at a one-member covering, the statement for morphisms of algebraic spaces.
* `AlgebraicGeometry.Stack.representingMap_comp_eq_of_twoIso`: a 2-isomorphism over a morphism of
  representing presheaves is an equality of induced morphisms.
* `AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_of_representedChart` and
  `AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_of_chart`: the space-level statement read
  on an algebraic stack lying over two algebraic spaces, presented and arbitrary.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_of_comp_of_fppf`:
  **Stacks 06Q9**.

## Implementation notes

The three properties of the presentation are established for 1-morphisms of algebraic stacks and
only then read on morphisms of algebraic spaces, through the third assertion of **Stacks 06FM**
for representable source and target:
`AlgebraicGeometry.Stack.isSurjective_representingMap_of_isSurjective`,
`AlgebraicGeometry.Stack.isFlat_representingMap_of_isFlat` and its companion at local finite
presentation. Doing it in that order keeps the argument inside the permanence lemmas of this
chapter — every step is a base change, a composition or a monotonicity statement about
1-morphisms of algebraic stacks — and the passage to algebraic spaces happens once, in
`AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_of_chart`.

That lemma takes the presentation in two steps, because
`AlgebraicGeometry.Stack.exists_smooth_surjective_schemeStack` presents an algebraic stack by a
*scheme* of the site: the chart is composed with the smooth surjective comparison of
`AlgebraicGeometry.Stack.exists_smooth_surjective_algebraicSpaceStack_hom` between the algebraic
stack of the algebraic space of a scheme and the algebraic stack of the scheme itself, so that
the source of the resulting chart is a category of elements and the comparisons of **Stacks
04SW** may all be taken to be identities.

Unlike the local-finite-type statement **Stacks 06U8**
(`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_of_comp_of_fppf`), neither the
source nor this formalization assumes `𝒳 ⟶ 𝒴` representable by algebraic spaces: Stacks 06U8
takes `V ×_𝒴 𝒳` itself to be an algebraic space, where Stacks 06Q9 only covers it by one, and
covering it is what the chosen presentation does.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04ZU](https://stacks.math.columbia.edu/tag/04ZU)
* [Stacks Project, Tag 06EV](https://stacks.math.columbia.edu/tag/06EV)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06PY](https://stacks.math.columbia.edu/tag/06PY)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
* [Stacks Project, Tag 06Q4](https://stacks.math.columbia.edu/tag/06Q4)
* [Stacks Project, Tag 06Q9](https://stacks.math.columbia.edu/tag/06Q9)
* [Stacks Project, Tag 075W](https://stacks.math.columbia.edu/tag/075W)
* [Stacks Project, Tag 0DNP](https://stacks.math.columbia.edu/tag/0DNP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

universe u w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06EV, consumed at a one-member covering.** If `p : X ⟶ Y` is a surjective flat
morphism of algebraic spaces over `S` locally of finite presentation and `p ≫ q` is locally of
finite presentation, then `q` is locally of finite presentation.

Local finite presentation is local on the source for the fppf topology, which is Stacks 06EV
(`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_isLocalAtSource_fppf`). The smooth
statement would not do: a smooth covering is an fppf covering and not conversely, and such a `p`
is only flat and locally of finite presentation. -/
theorem isLocallyOfFinitePresentation_of_comp_of_fppf
    {X Y Z : AlgebraicSpaces B S hS} (p : X ⟶ Y) (q : Y ⟶ Z)
    (hsurj : IsSurjective B S hS p.hom) (hflat : IsFlat B S hS p.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS p.hom)
    (hpq : IsLocallyOfFinitePresentation B S hS (p.hom ≫ q.hom)) :
    IsLocallyOfFinitePresentation B S hS q.hom :=
  prop_of_comp_of_fppf.{u, u} B S hS
    (fun ⦃F G : AlgebraicSpaces B S hS⦄ (k : F ⟶ G) =>
      IsLocallyOfFinitePresentation B S hS k.hom)
    p q hsurj hflat hlfp hpq

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A 2-isomorphism over a morphism of presheaves is an equality of induced morphisms of
representing presheaves.** Let `k` and `l` be 1-morphisms from a category fibred in groupoids
represented by a presheaf `T` to the categories of elements of presheaves `V` and `W`, and let
`h : V ⟶ W` be such that `k` followed by the 1-morphism attached to `h` by **Stacks 0458** is
2-isomorphic to `l`. Then the morphism `T ⟶ V` induced by `k`, followed by `h`, is the morphism
`T ⟶ W` induced by `l`.

This is functoriality of the identification of **Stacks 04SW** together with its value on the
1-morphism attached to a morphism of presheaves. -/
theorem representingMap_comp_eq_of_twoIso
    {𝒰 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {T V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (eU : StacksRepresentableCFG.EquivalenceOver 𝒰.val.p
      (presheafOfCategories (T ⋙ typeToCat)).p)
    (k : 𝒰 ⟶ fibredCategory B S hS V) (l : 𝒰 ⟶ fibredCategory B S hS W) (h : V ⟶ W)
    (ι : k ≫ (associatedMap B S hS h).1 ≅ l) :
    representingMap B S hS 𝒰 (fibredCategory B S hS V) T V eU
          (StacksRepresentableCFG.EquivalenceOver.refl _) k ≫ h =
      representingMap B S hS 𝒰 (fibredCategory B S hS W) T W eU
        (StacksRepresentableCFG.EquivalenceOver.refl _) l := by
  have e1 : representingMap B S hS 𝒰 (fibredCategory B S hS W) T W eU
        (StacksRepresentableCFG.EquivalenceOver.refl _) (k ≫ (associatedMap B S hS h).1) =
      representingMap B S hS 𝒰 (fibredCategory B S hS V) T V eU
          (StacksRepresentableCFG.EquivalenceOver.refl _) k ≫ h := by
    rw [representingMap_comp (𝒜 := 𝒰) (ℬ := fibredCategory B S hS V)
        (𝒞 := fibredCategory B S hS W) B S hS T V W eU
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _),
      representingMap_associatedMap B S hS V W h]
  refine e1.symm.trans ?_
  exact representingMap_congr_twoIso (𝒜 := 𝒰) (𝒞 := fibredCategory B S hS W) B S hS T W eU
    (StacksRepresentableCFG.EquivalenceOver.refl _) ι

/-- **Local finite presentation passes from a chart by an algebraic space to a morphism of
algebraic spaces it lies over.** Let `h : V ⟶ W` be a morphism of algebraic spaces over `S` and
let `u`, `v` be 1-morphisms from the algebraic stack of an algebraic space `T` to those of `V`
and of `W` such that `u` followed by the 1-morphism attached to `h` is 2-isomorphic to `v`. If
`u` is surjective, flat and locally of finite presentation and `v` is locally of finite
presentation, then `h` is locally of finite presentation.

Source and target of `u` and of `v` are representable by algebraic spaces, so the third assertion
of **Stacks 06FM** reads all four hypotheses on the induced morphisms `T ⟶ V` and `T ⟶ W`, and
the 2-isomorphism makes the second the first followed by `h`
(`AlgebraicGeometry.Stack.representingMap_comp_eq_of_twoIso`). The conclusion is then
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_comp_of_fppf`. -/
theorem isLocallyOfFinitePresentation_of_representedChart
    {T V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B S hS T) (hV : IsAlgebraicSpace B S hS V)
    (hW : IsAlgebraicSpace B S hS W) (h : V ⟶ W)
    (u : algebraicSpaceStack.{u, w} B S hS T hT ⟶ algebraicSpaceStack.{u, w} B S hS V hV)
    (v : algebraicSpaceStack.{u, w} B S hS T hT ⟶ algebraicSpaceStack.{u, w} B S hS W hW)
    (hcomm : u ≫ (Bicategory.InducedBicategory.mkHom (associatedMap B S hS h).1 :
        algebraicSpaceStack.{u, w} B S hS V hV ⟶ algebraicSpaceStack.{u, w} B S hS W hW) ≅ v)
    (husurj : IsSurjective B S hS u)
    (huflat : AlgebraicStacks.IsFlat B S hS u)
    (hulfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS u)
    (hvlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS v) :
    Space.IsLocallyOfFinitePresentation B S hS h := by
  let p := representingMap B S hS
    (algebraicSpaceStack.{u, w} B S hS T hT).val (algebraicSpaceStack.{u, w} B S hS V hV).val
    T V (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) u.hom
  let q := representingMap B S hS
    (algebraicSpaceStack.{u, w} B S hS T hT).val (algebraicSpaceStack.{u, w} B S hS W hW).val
    T W (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) v.hom
  have hpSurjSp : Space.IsSurjective B S hS p :=
    isSurjective_representingMap_of_isSurjective.{u, w} B S hS
      (𝒳 := algebraicSpaceStack.{u, w} B S hS T hT)
      (𝒴 := algebraicSpaceStack.{u, w} B S hS V hV) T V
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) u husurj
  have hpFlatSp : Space.IsFlat B S hS p :=
    isFlat_representingMap_of_isFlat.{u, w} B S hS
      (𝒳 := algebraicSpaceStack.{u, w} B S hS T hT)
      (𝒴 := algebraicSpaceStack.{u, w} B S hS V hV) T V hT hV
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) u huflat
  have hpLfpSp : Space.IsLocallyOfFinitePresentation B S hS p :=
    isLocallyOfFinitePresentation_representingMap_of_isLocallyOfFinitePresentation.{u, w}
      B S hS (𝒳 := algebraicSpaceStack.{u, w} B S hS T hT)
      (𝒴 := algebraicSpaceStack.{u, w} B S hS V hV) T V hT hV
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) u hulfp
  have hqLfpSp : Space.IsLocallyOfFinitePresentation B S hS q :=
    isLocallyOfFinitePresentation_representingMap_of_isLocallyOfFinitePresentation.{u, w}
      B S hS (𝒳 := algebraicSpaceStack.{u, w} B S hS T hT)
      (𝒴 := algebraicSpaceStack.{u, w} B S hS W hW) T W hT hW
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) v hvlfp
  have hmap : p ≫ h = q :=
    representingMap_comp_eq_of_twoIso B S hS
      (𝒰 := (algebraicSpaceStack.{u, w} B S hS T hT).val) (T := T) (V := V) (W := W)
      (StacksRepresentableCFG.EquivalenceOver.refl _) u.hom v.hom h
      (Bicategory.InducedBicategory.isoHom
        (f := u ≫ Bicategory.InducedBicategory.mkHom (associatedMap B S hS h).1) (g := v) hcomm)
  have hpq : Space.IsLocallyOfFinitePresentation B S hS (p ≫ h) := by
    rw [hmap]; exact hqLfpSp
  exact Space.isLocallyOfFinitePresentation_of_comp_of_fppf B S hS
    (X := ⟨T, hT⟩) (Y := ⟨V, hV⟩) (Z := ⟨W, hW⟩)
    (ObjectProperty.homMk p) (ObjectProperty.homMk h) hpSurjSp hpFlatSp hpLfpSp hpq

/-- **Local finite presentation passes from a presented algebraic stack to a morphism of
algebraic spaces it lies over.** Let `h : V ⟶ W` be a morphism of algebraic spaces over `S` and
let `𝒰` be an algebraic stack over `S` with 1-morphisms `u` and `v` to the algebraic stacks of
`V` and of `W` such that `u` followed by the 1-morphism attached to `h` is 2-isomorphic to `v`.
If `u` is surjective, flat and locally of finite presentation and `v` is locally of finite
presentation, then `h` is locally of finite presentation.

A smooth surjective chart of `𝒰` by an algebraic space is surjective, flat and locally of finite
presentation, by **Stacks 04TA** and **Stacks 0DNP**, so composing with it preserves the four
hypotheses — the composition laws **Stacks 04ZT**, **Stacks 06PX** and **Stacks 06Q3** — and
`AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_of_representedChart` applies to the
composites. -/
theorem isLocallyOfFinitePresentation_of_chart
    {V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hV : IsAlgebraicSpace B S hS V) (hW : IsAlgebraicSpace B S hS W) (h : V ⟶ W)
    {𝒰 : AlgebraicStacks.{u, w} B S hS}
    (u : 𝒰 ⟶ algebraicSpaceStack.{u, w} B S hS V hV)
    (v : 𝒰 ⟶ algebraicSpaceStack.{u, w} B S hS W hW)
    (hcomm : u ≫ (Bicategory.InducedBicategory.mkHom (associatedMap B S hS h).1 :
        algebraicSpaceStack.{u, w} B S hS V hV ⟶ algebraicSpaceStack.{u, w} B S hS W hW) ≅ v)
    (husurj : IsSurjective B S hS u)
    (huflat : AlgebraicStacks.IsFlat B S hS u)
    (hulfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS u)
    (hvlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS v) :
    Space.IsLocallyOfFinitePresentation B S hS h := by
  obtain ⟨T, c, hcSmooth, hcSurj⟩ := exists_smooth_surjective_schemeStack B S hS 𝒰
  obtain ⟨e, heSmooth, heSurj⟩ :=
    exists_smooth_surjective_algebraicSpaceStack_hom.{u, w} B S hS T
  have hrSmooth : AlgebraicStacks.IsSmooth B S hS (e ≫ c) :=
    AlgebraicStacks.isSmooth_comp B S hS e c heSmooth hcSmooth
  have hrSurj : IsSurjective B S hS (e ≫ c) := isSurjective_comp B S hS e c heSurj hcSurj
  have hrFlat : AlgebraicStacks.IsFlat B S hS (e ≫ c) :=
    AlgebraicStacks.isFlat_of_isSmooth B S hS (e ≫ c) hrSmooth
  have hrLfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS (e ≫ c) :=
    AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS (e ≫ c) hrSmooth
  exact isLocallyOfFinitePresentation_of_representedChart B S hS
    (isAlgebraicSpace_yoneda B S hS T) hV hW h ((e ≫ c) ≫ u) ((e ≫ c) ≫ v)
    (α_ (e ≫ c) u _ ≪≫ Bicategory.whiskerLeftIso (e ≫ c) hcomm)
    (isSurjective_comp B S hS (e ≫ c) u hrSurj husurj)
    (AlgebraicStacks.isFlat_comp B S hS (e ≫ c) u hrFlat huflat)
    (AlgebraicStacks.isLocallyOfFinitePresentation_comp B S hS (e ≫ c) u hrLfp hulfp)
    (AlgebraicStacks.isLocallyOfFinitePresentation_comp B S hS (e ≫ c) v hrLfp hvlfp)

namespace AlgebraicStacks

/-- **Stacks 06Q9.** Let `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` be 1-morphisms of algebraic stacks over
`S`. If `f ≫ g` is locally of finite presentation and `f` is surjective, flat and locally of
finite presentation, then `g` is locally of finite presentation. -/
@[stacks 06Q9]
theorem isLocallyOfFinitePresentation_of_comp_of_fppf
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hfg : IsLocallyOfFinitePresentation B S hS (f ≫ g))
    (hfsurj : Stack.IsSurjective B S hS f)
    (hfflat : IsFlat B S hS f)
    (hflfp : IsLocallyOfFinitePresentation B S hS f) :
    IsLocallyOfFinitePresentation B S hS g := by
  intro V W hV hW a b h η _ha _hb hcomp
  -- `D` is `𝒲 ×_𝒵 𝒴` and `E` is `(𝒲 ×_𝒵 𝒴) ×_𝒴 𝒳`, for `𝒲` the algebraic stack of `W`
  let bSt : Stack.algebraicSpaceStack.{u, w} B S hS W hW ⟶ 𝒵 :=
    Bicategory.InducedBicategory.mkHom b
  let D := Stack.twoFibreProductSquareAlgebraicStacks B S hS bSt g
  have hD : Bicategory.IsTwoFibreProduct D :=
    Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS bSt g
  let E := Stack.twoFibreProductSquareAlgebraicStacks B S hS D.snd f
  have hE : Bicategory.IsTwoFibreProduct E :=
    Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS D.snd f
  -- the pasted rectangle exhibits `E.pt` over the cospan `(bSt, f ≫ g)`
  have hDEfst : IsLocallyOfFinitePresentation B S hS (D.paste E).fst :=
    isLocallyOfFinitePresentation_baseChange B S hS (f ≫ g) bSt (D.paste E)
      (Bicategory.isTwoFibreProduct_paste hD hE) hfg
  -- `E.fst`, a base change of `f`, inherits its three properties
  have hEsurj : Stack.IsSurjective B S hS E.fst :=
    Stack.isSurjective_of_isTwoFibreProduct B S hS E.swap
      (Bicategory.isTwoFibreProduct_swap hE) hfsurj
  have hEflat : IsFlat B S hS E.fst := isFlat_baseChange B S hS f D.snd E hE hfflat
  have hElfp : IsLocallyOfFinitePresentation B S hS E.fst :=
    isLocallyOfFinitePresentation_baseChange B S hS f D.snd E hE hflfp
  -- the comparison 1-morphism of the given diagram into `𝒲 ×_𝒵 𝒴`, smooth by the diagram's
  -- own clause
  let Q := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b g.hom
  have hQ : Bicategory.IsTwoFibreProduct Q :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} b g.hom
  let k₀ : Bicategory.TwoCommSq.PreHom (Stack.diagramCone B S hS g.hom a b h η) Q :=
    Quotient.out (hQ.from (Stack.diagramCone B S hS g.hom a b h η))
  let kSt : Stack.algebraicSpaceStack.{u, w} B S hS V hV ⟶ D.pt :=
    Bicategory.InducedBicategory.mkHom k₀.hom
  have hkSt : IsSmooth B S hS kSt :=
    Stack.hasPropertyOnSomeSmoothDiagram_of_isRelativelySmooth B S hS _ k₀.hom V hV
      (StacksRepresentableCFG.EquivalenceOver.refl _) (hcomp Q hQ k₀)
      (Space.isSmooth_id B S hS hV)
  -- `R` is `𝒱 ×_{𝒲 ×_𝒵 𝒴} ((𝒲 ×_𝒵 𝒴) ×_𝒴 𝒳)`
  let R := Stack.twoFibreProductSquareAlgebraicStacks B S hS kSt E.fst
  have hR : Bicategory.IsTwoFibreProduct R :=
    Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS kSt E.fst
  let hSt : Stack.algebraicSpaceStack.{u, w} B S hS V hV ⟶
      Stack.algebraicSpaceStack.{u, w} B S hS W hW :=
    Bicategory.InducedBicategory.mkHom (Stack.associatedMap B S hS h).1
  have hKst : hSt ≅ kSt ≫ D.fst :=
    Bicategory.InducedBicategory.isoMk (f := hSt) (g := kSt ≫ D.fst) k₀.isoFst
  refine Stack.isLocallyOfFinitePresentation_of_chart B S hS hV hW h R.fst
    (R.snd ≫ (D.paste E).fst) ?_
    (Stack.isSurjective_of_isTwoFibreProduct B S hS R.swap
      (Bicategory.isTwoFibreProduct_swap hR) hEsurj)
    (isFlat_baseChange B S hS E.fst kSt R hR hEflat)
    (isLocallyOfFinitePresentation_baseChange B S hS E.fst kSt R hR hElfp)
    (isLocallyOfFinitePresentation_comp B S hS R.snd (D.paste E).fst
      (isLocallyOfFinitePresentation_of_isSmooth B S hS R.snd
        (isSmooth_baseChange B S hS kSt E.fst R.swap
          (Bicategory.isTwoFibreProduct_swap hR) hkSt)) hDEfst)
  exact Bicategory.whiskerLeftIso R.fst hKst ≪≫ (α_ R.fst kSt D.fst).symm ≪≫
    Bicategory.whiskerRightIso R.iso D.fst ≪≫ α_ R.snd E.fst D.fst

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
