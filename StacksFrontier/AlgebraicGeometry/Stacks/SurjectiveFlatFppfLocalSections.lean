module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationBaseChangeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySchemeMap
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismComp
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap
public import StacksFrontier.CategoryTheory.TwoYoneda.OverBase

/-!
# Fppf-local sections of a surjective, flat, locally finitely presented morphism (Stacks 06QA)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` which is surjective
(**Stacks 04ZS**), flat (**Stacks 06PW**) and locally of finite presentation
(**Stacks 06Q2**, part (1)). **Stacks 06QA** says that for every scheme `U` of the site and every
object `y` of the fibre of `𝒴` over `U` there is an fppf covering `{U_i → U}` and objects `x_i`
of `𝒳` over `U_i` with `f(x_i) ≅ y|_{U_i}` in the fibre of `𝒴` over `U_i`.

The proof is the source's. Read `y` as a 1-morphism `U ⟶ 𝒴` out of the algebraic stack of `U`
through the 2-Yoneda lemma (**Stacks 004B**) and form the 2-fibre product `𝒳 ×_𝒴 U`
(**Stacks 04T2**). Its projection to `U` is again surjective, flat and locally of finite
presentation, by **Stacks 04ZU**, **Stacks 06PY** and **Stacks 06Q4**. Choose a smooth surjective
presentation `V ⟶ 𝒳 ×_𝒴 U` by a scheme of the site, which is flat and locally of finite
presentation because it is smooth, and compose: `V ⟶ U` is surjective, flat and locally of finite
presentation, by **Stacks 04ZT**, **Stacks 06PX** and **Stacks 06Q3**. Both its source and its
target are represented, so **Stacks 04SW** identifies it, up to a 2-isomorphism, with the
1-morphism attached to a morphism `V ⟶ U` of the site carrying the same three properties; the
one-member family `{V → U}` is then an fppf covering of `U`, and the composite `V ⟶ 𝒳 ×_𝒴 U ⟶ 𝒳`
supplies the object of `𝒳` over `V` together with the required isomorphism.

## Main results

* `AlgebraicGeometry.Stack.exists_fibre_lift_of_twoCell`: an object of a fibre lifts along a
  morphism of the base as soon as a 1-morphism out of the slice over its source fits into a
  2-commutative triangle over that morphism.
* `AlgebraicGeometry.Stack.isHomLift_homMk_left`: a morphism lying over `k : V ⟶ U` lies over the
  same morphism with its source presented as the slice object of its structure morphism.
* `AlgebraicGeometry.Stack.exists_schemeMap_of_isSurjective_isFlat_isLfp`: a surjective, flat,
  locally finitely presented 1-morphism between represented algebraic stacks is 2-isomorphic to
  the one attached to a morphism of the site with the same three properties.
* `AlgebraicGeometry.Stack.exists_scheme_lift_of_isSurjective_isFlat_isLfp`: the single flat,
  locally finitely presented, surjective morphism of the site along which the object lifts, i.e.
  **Stacks 06QA** with a one-member covering.
* `AlgebraicGeometry.Stack.exists_fppfCovering_fibre_lift`: **Stacks 06QA**.

## Implementation notes

The covering of the conclusion is rendered as a covering sieve of the big fppf topology of `S`,
together with a lift of `y` along every arrow of the sieve. This is the shape in which the library
meets fppf-local liftability — it is the conclusion of
`AlgebraicGeometry.Stack.localEssSurj_of_isSurjective_isFlat_isLocallyOfFinitePresentation`, the
local essential surjectivity which the descent lemma **Stacks 045D** consumes — and an arrow
`k : V ⟶ U` of the sieve together with a morphism `f(x) ⟶ y` lying over `k` is exactly a member
`V → U` of the covering, an object `x` of `𝒳` over `V` and an isomorphism `f(x) ≅ y|_V`, since
`𝒴` is fibred in groupoids. The one-member form is stated separately because it is strictly more
informative: the covering it produces has a single member, which no sieve exposes.

Passing from the composite 1-morphism `V ⟶ U` of represented algebraic stacks to a morphism of
the site is the uniqueness half of **Stacks 04SW**: the morphism of representing presheaves is
`yoneda.map` of a unique morphism of the site by full faithfulness of Yoneda, and
`AlgebraicGeometry.Stack.representingMap_schemeFibredCategoryMap` computes the representing map of
the attached 1-morphism as that same `yoneda.map`, so
`AlgebraicGeometry.Stack.nonempty_unique_twoIso_of_representingMap_eq` produces the 2-isomorphism.
The three properties are read off the representing map directly — flatness and local finite
presentation by **Stacks 06FM** for represented source and target followed by
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map_iff`, and surjectivity by
`AlgebraicGeometry.Stack.isSurjective_representingMap_of_isSurjective` — so the 2-isomorphism is
needed only to transport the 2-commutativity datum that carries the lift.

Surjectivity of the base change is **Stacks 04ZU** applied to the exchanged square
`CategoryTheory.Bicategory.TwoCommSq.swap`, because that statement concludes about the second
projection where flatness and local finite presentation conclude about the first; exchanging the
legs of a 2-fibre product again gives a 2-fibre product by
`CategoryTheory.Bicategory.isTwoFibreProduct_swap`.

The smooth presentation of the 2-fibre product is flat and locally of finite presentation by
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_of_isSmooth` and
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth`, which are the
source's **Stacks 04TA** and **Stacks 04AJ** read at 1-morphisms of algebraic stacks.

`CategoryTheory.BasedCategory.ofFunctor`, `CategoryTheory.BasedFunctor.comp` and
`CategoryTheory.BasedFunctor.overMap` are made `implicit_reducible` locally, as in
`StacksFrontier.CategoryTheory.TwoYoneda.OverBase`: the verticality condition carried by a
`CategoryTheory.BasedNatTrans` has to reduce to the `IsHomLift` statement about the underlying
functors for the composite of the triangle's filler with the arrow to `y` to be recognised as a
lift, and the pasting of the two 2-cells has to be read as a 2-cell of based functors with the
bracketing the triangle asks for.

`AlgebraicGeometry.Stack.exists_fibre_lift_of_twoCell` takes the 1-morphism `H` out of the slice
over `U` and the vertical arrow from its value at the unit object to `y` as data rather than
building them from the 2-Yoneda lemma, so that none of its lifting statements mention
`CategoryTheory.Functor.TwoYoneda.liftBased`; the 2-Yoneda choice is substituted for them only
where the triangle is assembled.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 04AJ](https://stacks.math.columbia.edu/tag/04AJ)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04TA](https://stacks.math.columbia.edu/tag/04TA)
* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
* [Stacks Project, Tag 04ZT](https://stacks.math.columbia.edu/tag/04ZT)
* [Stacks Project, Tag 04ZU](https://stacks.math.columbia.edu/tag/04ZU)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06PW](https://stacks.math.columbia.edu/tag/06PW)
* [Stacks Project, Tag 06PX](https://stacks.math.columbia.edu/tag/06PX)
* [Stacks Project, Tag 06PY](https://stacks.math.columbia.edu/tag/06PY)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
* [Stacks Project, Tag 06Q3](https://stacks.math.columbia.edu/tag/06Q3)
* [Stacks Project, Tag 06Q4](https://stacks.math.columbia.edu/tag/06Q4)
* [Stacks Project, Tag 06QA](https://stacks.math.columbia.edu/tag/06QA)
-/

@[expose] public section

open CategoryTheory

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.BasedFunctor.comp CategoryTheory.BasedFunctor.overMap

namespace AlgebraicGeometry.Stack

universe u w v₁ u₁ v₂ u₂ v₃ u₃

/-- **A 2-commutative triangle over a morphism of the base lifts an object of a fibre.** Let
`g : p ⟶ r` be a 1-morphism of categories over `C`, let `y` be an
object of the fibre of `r` over `U`, let `H` be a 1-morphism from the slice `C/U` to `r` whose
value at the unit object admits a vertical morphism `cy` to `y`, let `q : V ⟶ U` and let `a` be a
1-morphism from the slice `C/V` to `p`. A 2-morphism from `a` followed by `g` to the restriction
of `H` along `q` produces an object `x` of the fibre of `p` over `V` and a morphism `g(x) ⟶ y`
lying over `q`.

The object is the value of `a` at the unit object of `C/V`. The morphism is the component of the
filler there, which lies over an identity, followed by the image under `H` of the canonical arrow
`1_V · q ⟶ 1_U`, which lies over `q`, followed by `cy`. -/
theorem exists_fibre_lift_of_twoCell {C : Type u₁} [Category.{v₁} C]
    {X : Type u₂} [Category.{v₂} X] {Y : Type u₃} [Category.{v₃} Y]
    (p : X ⥤ C) (r : Y ⥤ C)
    {U V : C} (y : r.Fiber U) (q : V ⟶ U)
    (g : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor r)
    (a : BasedCategory.slice V ⥤ᵇ BasedCategory.ofFunctor p)
    (H : BasedCategory.slice U ⥤ᵇ BasedCategory.ofFunctor r)
    (cy : H.obj (Over.mk (𝟙 U)) ⟶ y.1) (hcy : r.IsHomLift (𝟙 U) cy)
    (η : BasedFunctor.comp a g ⟶ BasedFunctor.comp (BasedFunctor.overMap q) H) :
    ∃ (x : p.Fiber V) (α : g.obj x.1 ⟶ y.1), r.IsHomLift q α := by
  have hβ : r.IsHomLift (𝟙 V) (η.app (Over.mk (𝟙 V))) := η.isHomLift' (Over.mk (𝟙 V))
  have hκ : r.IsHomLift q (H.map (Over.mkIdTerminal.from (Functor.TwoYoneda.unitOver q))) :=
    Functor.TwoYoneda.isHomLift_map_from_mkIdTerminal_unitOver r q
  have hκχ : r.IsHomLift q
      (H.map (Over.mkIdTerminal.from (Functor.TwoYoneda.unitOver q)) ≫ cy) :=
    IsHomLift.comp_lift_id_right' r q
      (H.map (Over.mkIdTerminal.from (Functor.TwoYoneda.unitOver q))) U cy
  refine ⟨⟨a.obj (Over.mk (𝟙 V)), a.w_obj (Over.mk (𝟙 V))⟩,
    η.app (Over.mk (𝟙 V)) ≫
      H.map (Over.mkIdTerminal.from (Functor.TwoYoneda.unitOver q)) ≫ cy, ?_⟩
  exact IsHomLift.comp_lift_id_left' r V (η.app (Over.mk (𝟙 V))) q
    (H.map (Over.mkIdTerminal.from (Functor.TwoYoneda.unitOver q)) ≫ cy)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A lift along a morphism of the site is a lift along it with its source presented by its
structure morphism.** A morphism `k : V ⟶ U` of the big fppf category of `S` agrees, under the
equality identifying `V` with the slice object of `k.left ≫ U.hom`, with the morphism
`Over.homMk k.left`; so a morphism of a category over the site lying over `k` lies over
`Over.homMk k.left` too.

This is the spelling of a covering family used by
`AlgebraicGeometry.mem_topology_of_family` and by
`AlgebraicGeometry.Stack.localEssSurj_of_exists_scheme_lift`. -/
theorem isHomLift_homMk_left {X : Type u₂} [Category.{v₂} X]
    (p : X ⥤ BigFppfOver B S hS) {V U : BigFppfOver B S hS} (k : V ⟶ U)
    {x z : X} (α : x ⟶ z) (hα : p.IsHomLift k α) :
    p.IsHomLift (Over.homMk k.left rfl :
      (Over.mk (k.left ≫ U.hom) : BigFppfOver B S hS) ⟶ U) α := by
  have hV : (Over.mk (k.left ≫ U.hom) : BigFppfOver B S hS) = V := by
    rw [Over.w k]
    exact (CostructuredArrow.eq_mk V).symm
  have := hα
  refine IsHomLift.of_commsq p _ α ((IsHomLift.domain_eq p k α).trans hV.symm)
    (IsHomLift.codomain_eq p k α) ?_
  have hk : (Over.homMk k.left rfl :
      (Over.mk (k.left ≫ U.hom) : BigFppfOver B S hS) ⟶ U) = eqToHom hV ≫ k :=
    Over.OverMorphism.ext (by simp [Over.eqToHom_left])
  rw [hk, ← Category.assoc, eqToHom_trans]
  exact (IsHomLift.commSq p k α).w

/-- **A surjective, flat, locally finitely presented 1-morphism of represented algebraic stacks
comes from a morphism of the site with those three properties.** By the uniqueness half of
**Stacks 04SW** a 1-morphism `schemeStack V ⟶ schemeStack U` is 2-isomorphic to the one attached
to a morphism `q : V ⟶ U` of the big fppf category of `S`, namely the morphism whose `yoneda.map`
is the induced morphism of representing presheaves; and `q` is then flat, locally of finite
presentation and surjective as a morphism of schemes. -/
theorem exists_schemeMap_of_isSurjective_isFlat_isLfp {V U : BigFppfOver B S hS}
    (h : schemeStack.{u, w} B S hS V ⟶ schemeStack.{u, w} B S hS U)
    (hsurj : IsSurjective B S hS h)
    (hflat : AlgebraicStacks.IsFlat B S hS h)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS h) :
    ∃ q : V ⟶ U,
      Flat ((BigFppfOver.toScheme B S hS).map q) ∧
        LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map q) ∧
          Surjective ((BigFppfOver.toScheme B S hS).map q) ∧
            Nonempty (h.hom ≅ schemeFibredCategoryMap B S hS q) := by
  obtain ⟨q, hq⟩ : ∃ q : V ⟶ U, yoneda.map q =
      representingMap B S hS (schemeFibredCategory B S hS V) (schemeFibredCategory B S hS U)
        (yoneda.obj V) (yoneda.obj U) (representedChart B S hS V) (representedChart B S hS U)
        h.hom :=
    ⟨yoneda.preimage _, yoneda.map_preimage _⟩
  have key : ∀ P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u),
      Space.IsSmoothLocalOnSourceAndTarget B S hS P →
        HasPropertyOnSomeSmoothDiagram B S hS P h.hom → P (yoneda.map q) := fun P hP hh => by
    rw [hq]
    exact (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS P hP
      (schemeStack.{u, w} B S hS V).property (schemeStack.{u, w} B S hS U).property
      (yoneda.obj V) (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS V) (isAlgebraicSpace_yoneda B S hS U)
      (representedChart B S hS V) (representedChart B S hS U) h.hom).1 hh
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · exact (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      Flat.isEtaleLocalOnSourceAndTarget q).1
      (key _ (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) hflat)
  · refine (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget q).1 <|
      key _ (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS) ?_
    exact (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
      (fun _ _ k => Space.IsLocallyOfFinitePresentation B S hS k)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
      (schemeStack.{u, w} B S hS V).property (schemeStack.{u, w} B S hS U).property h.hom).1 hlfp
  · refine (Space.presheaf_yoneda_map_iff B S hS
      (inferInstance : MorphismProperty.IsStableUnderBaseChange
        (@Surjective.{u} : MorphismProperty Scheme.{u})) q).1 ?_
    refine (Space.surjective_yonedaMap_iff_surjective_pointsMap B S hS q).2 ?_
    rw [hq]
    exact isSurjective_representingMap_of_isSurjective B S hS
      (𝒳 := schemeStack.{u, w} B S hS V) (𝒴 := schemeStack.{u, w} B S hS U)
      (yoneda.obj V) (yoneda.obj U)
      (representedChart B S hS V) (representedChart B S hS U) h hsurj
  · obtain ⟨hu⟩ := nonempty_unique_twoIso_of_representingMap_eq B S hS
      (schemeFibredCategory B S hS V) (schemeFibredCategory B S hS U)
      (yoneda.obj V) (yoneda.obj U) (representedChart B S hS V) (representedChart B S hS U)
      (f := h.hom) (g := schemeFibredCategoryMap B S hS q)
      (by rw [representingMap_schemeFibredCategoryMap]; exact hq.symm)
    exact ⟨hu.default⟩

/-- **A single flat, locally finitely presented, surjective morphism of the site along which an
object lifts.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` which is surjective,
flat and locally of finite presentation. Then every object `y` of the fibre of `𝒴` over an object
`U` of the site admits a morphism `m : T ⟶ U.left` of the underlying category of the site, flat,
locally of finite presentation and surjective on the underlying schemes, together with an object
of `𝒳` over its source whose image is isomorphic to the restriction of `y` along `m`.

This is **Stacks 06QA** with the fppf covering produced as a one-member family, which is the
source's own construction: the smooth surjective scheme presentation of the 2-fibre product
`𝒳 ×_𝒴 U`. -/
theorem exists_scheme_lift_of_isSurjective_isFlat_isLfp
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hsurj : IsSurjective B S hS f)
    (hflat : AlgebraicStacks.IsFlat B S hS f)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (U : BigFppfOver B S hS) (y : 𝒴.val.val.p.Fiber U) :
    ∃ (T : B.Schemes) (m : T ⟶ U.left),
      Flat (B.inclusion.map m) ∧ LocallyOfFinitePresentation (B.inclusion.map m) ∧
        Surjective (B.inclusion.map m) ∧
        ∃ (x : 𝒳.val.val.obj) (α : (CatFiberedInGroupoids.homFunctor f.hom).obj x ⟶ y.1),
          𝒴.val.val.p.IsHomLift
            (Over.homMk m rfl : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U) α := by
  classical
  -- The 2-Yoneda 1-morphism of `y`, out of the algebraic stack of `U`.
  let Y : schemeFibredCategory B S hS U ⟶ 𝒴.val :=
    Bicategory.InducedBicategory.mkHom
      (Functor.TwoYoneda.liftBased 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids U y)
  let b : schemeStack.{u, w} B S hS U ⟶ 𝒴 := Bicategory.InducedBicategory.mkHom Y
  -- The 2-fibre product `𝒳 ×_𝒴 U` and its projection to `U`.
  let P : Bicategory.TwoCommSq b f := twoFibreProductSquareAlgebraicStacks B S hS b f
  have hP : Bicategory.IsTwoFibreProduct P :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS b f
  have hPsurj : IsSurjective B S hS P.fst :=
    isSurjective_of_isTwoFibreProduct B S hS P.swap
      (Bicategory.isTwoFibreProduct_swap hP) hsurj
  have hPflat : AlgebraicStacks.IsFlat B S hS P.fst :=
    AlgebraicStacks.isFlat_baseChange B S hS f b P hP hflat
  have hPlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS P.fst :=
    AlgebraicStacks.isLocallyOfFinitePresentation_baseChange B S hS f b P hP hlfp
  -- A smooth surjective scheme presentation of the 2-fibre product, and the composite to `U`.
  obtain ⟨V, c, hcsm, hcsurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS P.pt
  have hwsurj : IsSurjective B S hS (c ≫ P.fst) :=
    isSurjective_comp B S hS c P.fst hcsurj hPsurj
  have hwflat : AlgebraicStacks.IsFlat B S hS (c ≫ P.fst) :=
    AlgebraicStacks.isFlat_comp B S hS c P.fst
      (AlgebraicStacks.isFlat_of_isSmooth B S hS c hcsm) hPflat
  have hwlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS (c ≫ P.fst) :=
    AlgebraicStacks.isLocallyOfFinitePresentation_comp B S hS c P.fst
      (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS c hcsm) hPlfp
  -- The composite is the 1-morphism attached to a morphism `q : V ⟶ U` of the site.
  obtain ⟨q, hqflat, hqlfp, hqsurj, ⟨e⟩⟩ :=
    exists_schemeMap_of_isSurjective_isFlat_isLfp B S hS (c ≫ P.fst) hwsurj hwflat hwlfp
  refine ⟨V.left, q.left, hqflat, hqlfp, hqsurj, ?_⟩
  -- The lift of `y`, read off the filler of the 2-fibre product square.
  obtain ⟨x, α, hα⟩ := exists_fibre_lift_of_twoCell 𝒳.val.val.p 𝒴.val.val.p
    y q f.hom.hom (c ≫ P.snd).hom.hom
    (Functor.TwoYoneda.liftBased 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids U y)
    (Functor.TwoYoneda.chosenLift 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids U y
      (Over.mk (𝟙 U))).φ
    ((Functor.TwoYoneda.chosenLift 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids U y
      (Over.mk (𝟙 U))).isStronglyCartesian.toIsHomLift)
    ((Bicategory.whiskerLeft c P.iso.inv).hom.hom ≫
      (Bicategory.whiskerRight e.hom Y).hom)
  exact ⟨x.1, α, isHomLift_homMk_left B S hS 𝒴.val.val.p q α hα⟩

/-- **Stacks 06QA.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` which is
surjective, flat and locally of finite presentation. Then for every object `U` of the big fppf
site of `S` and every object `y` of the fibre of `𝒴` over `U` there is an fppf covering of `U`
such that over every member of it `y` is isomorphic to the image of an object of `𝒳`.

The covering is a covering sieve of the big fppf topology of `S`, and the isomorphism over a
member `k : V ⟶ U` is a morphism `f(x) ⟶ y` lying over `k`, which in a category fibred in
groupoids is exactly an isomorphism `f(x) ≅ y|_V` of the fibre over `V`. The covering produced is
a one-member one; see
`AlgebraicGeometry.Stack.exists_scheme_lift_of_isSurjective_isFlat_isLfp`. -/
@[stacks 06QA]
theorem exists_fppfCovering_fibre_lift
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hsurj : IsSurjective B S hS f)
    (hflat : AlgebraicStacks.IsFlat B S hS f)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f) :
    ∀ (U : BigFppfOver B S hS) (y : 𝒴.val.val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          ∃ (x : 𝒳.val.val.obj) (α : (CatFiberedInGroupoids.homFunctor f.hom).obj x ⟶ y.1),
            𝒴.val.val.p.IsHomLift k α :=
  localEssSurj_of_exists_scheme_lift B S hS f.hom
    (exists_scheme_lift_of_isSurjective_isFlat_isLfp B S hS f hsurj hflat hlfp)

end AlgebraicGeometry.Stack

end
