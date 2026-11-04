module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveFlatFppfLocalSections
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.CoveringSieves

/-!
# Fppf-local sections of a jointly surjective flat, locally finitely presented family (Stacks 07AN)

Let `f j : 𝒳 j ⟶ 𝒴`, `j ∈ J`, be a family of 1-morphisms of algebraic stacks over `S` which are
each flat (**Stacks 06PW**) and locally of finite presentation (**Stacks 06Q2**, part (1)) and
which are *jointly surjective*, that is `|𝒴| = ⋃ j, |f j|(|𝒳 j|)` for the points of
**Stacks 04XG**. **Stacks 07AN** says that for every scheme `U` of the site and every object `y`
of the fibre of `𝒴` over `U` there is an fppf covering `{U i → U}_{i ∈ I}`, a map `a : I → J`,
and objects `x i` of `𝒳 (a i)` over `U i` with `f (a i) (x i) ≅ y|_{U i}` in the fibre of `𝒴`
over `U i`.

The source deduces this from **Stacks 06QA** applied to the single 1-morphism
`∐ j, 𝒳 j ⟶ 𝒴`, and then splits each member of the resulting covering into the disjoint pieces
on which it lands in one `𝒳 j`; it notes that the coproduct raises a set-theoretic issue which it
passes over. The argument below forms no coproduct. Instead it runs the proof of **Stacks 06QA**
one point of `U` at a time: for a point `x` of `U`, read as a point `z` of the algebraic stack of
`U` through `AlgebraicGeometry.Stack.pointsHomeomorphScheme`, joint surjectivity supplies an index
`j` and a point of `|𝒳 j|` with the same image in `|𝒴|` as `z` has under the 1-morphism
`AlgebraicGeometry.Stack.fibreObjectStackMap` attached to `y` by the 2-Yoneda lemma
(**Stacks 004B**); by **Stacks 04XH** the two lift to a point of the 2-fibre product
`𝒳 j ×_𝒴 U` (**Stacks 04T2**), and a smooth surjective scheme presentation of that 2-fibre
product therefore contains a point above `x`. The presentation composed with the first projection
is flat and locally of finite presentation by **Stacks 06PY**, **Stacks 06Q4**, **Stacks 04TA**,
**Stacks 04AJ**, **Stacks 06PX** and **Stacks 06Q3**, and — both its source and its target being
represented — it is 2-isomorphic to the 1-morphism attached to a morphism of the site with those
two properties, by **Stacks 04SW**. The resulting family of morphisms of the site, indexed by the
points of `U`, is flat, locally of finite presentation and jointly surjective, hence an fppf
covering of `U`, and each member carries a lift of `y`.

## Main definitions

* `AlgebraicGeometry.Stack.fibreObjectStackMap`: the 1-morphism of algebraic stacks out of the
  algebraic stack of `U` attached to an object of the fibre over `U` by the 2-Yoneda lemma.

## Main results

* `AlgebraicGeometry.Stack.exists_schemeMap_of_isFlat_isLfp`: a flat, locally finitely presented
  1-morphism between represented algebraic stacks is 2-isomorphic to the one attached to a
  morphism of the site with the same two properties.
* `AlgebraicGeometry.Stack.exists_scheme_lift_of_isFlat_isLfp_at_point`: a flat, locally finitely
  presented 1-morphism admits, above any point of `U` whose image in `|𝒴|` lies in the image of
  the 1-morphism, a single flat and locally finitely presented morphism of the site hitting that
  point and carrying a lift of `y`.
* `AlgebraicGeometry.Stack.exists_fppfCovering_family_fibre_lift`: **Stacks 07AN**, with the fppf
  covering produced as a family of morphisms of the site together with the index map to `J`.
* `AlgebraicGeometry.Stack.exists_fppfCovering_fibre_lift_of_family`: **Stacks 07AN** with the
  covering presented as a covering sieve of the big fppf topology of `S`.

## Implementation notes

The covering is indexed by the points of the underlying scheme of `U`, lifted to the index
universe `Type (u + 1)` of `AlgebraicGeometry.mem_topology_of_family`; this is where the index map
`a : I → J` of the source's statement acquires content, since the index set `J` of the family is
left in an arbitrary universe. Choosing one member of the covering per point of `U` is what
replaces the source's coproduct, and it is also what frees `J` from any smallness assumption.

`AlgebraicGeometry.Stack.exists_schemeMap_of_isFlat_isLfp` repeats the flatness, local finite
presentation and 2-isomorphism parts of
`AlgebraicGeometry.Stack.exists_schemeMap_of_isSurjective_isFlat_isLfp`, whose statement also
concludes surjectivity of the morphism of the site and therefore assumes surjectivity of the
1-morphism; no member of the covering here is surjective on its own.

The isomorphism `f (a i) (x i) ≅ y|_{U i}` is rendered, as in
`AlgebraicGeometry.Stack.exists_fppfCovering_fibre_lift`, as a morphism
`f (a i) (x i) ⟶ y` lying over the member `U i → U` of the covering: in a category fibred in
groupoids that is exactly an isomorphism in the fibre over `U i`.

The transport of a lift along a factorisation of an arrow of the covering sieve through a member
of the covering is the one used by
`AlgebraicGeometry.Stack.localEssSurj_of_exists_scheme_lift`, whose own hypothesis is a
one-member family and so cannot be applied to a family with a varying index.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 04AJ](https://stacks.math.columbia.edu/tag/04AJ)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04TA](https://stacks.math.columbia.edu/tag/04TA)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
* [Stacks Project, Tag 06PW](https://stacks.math.columbia.edu/tag/06PW)
* [Stacks Project, Tag 06PX](https://stacks.math.columbia.edu/tag/06PX)
* [Stacks Project, Tag 06PY](https://stacks.math.columbia.edu/tag/06PY)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
* [Stacks Project, Tag 06Q3](https://stacks.math.columbia.edu/tag/06Q3)
* [Stacks Project, Tag 06Q4](https://stacks.math.columbia.edu/tag/06Q4)
* [Stacks Project, Tag 06QA](https://stacks.math.columbia.edu/tag/06QA)
* [Stacks Project, Tag 07AN](https://stacks.math.columbia.edu/tag/07AN)
-/

@[expose] public section

open CategoryTheory

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.BasedFunctor.comp CategoryTheory.BasedFunctor.overMap

namespace AlgebraicGeometry.Stack

universe u w v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The 1-morphism named by an object of a fibre.** An object `y` of the fibre of an algebraic
stack `𝒴` over an object `U` of the big fppf site of `S` is, by the 2-Yoneda lemma
(**Stacks 004B**), the same thing as a 1-morphism from the algebraic stack of `U` to `𝒴`; this is
that 1-morphism. -/
noncomputable def fibreObjectStackMap (𝒴 : AlgebraicStacks.{u, w} B S hS)
    (U : BigFppfOver B S hS) (y : 𝒴.val.val.p.Fiber U) :
    schemeStack.{u, w} B S hS U ⟶ 𝒴 :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    (Functor.TwoYoneda.liftBased 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids U y))

/-- **A flat, locally finitely presented 1-morphism of represented algebraic stacks comes from a
morphism of the site with those two properties.** By the uniqueness half of **Stacks 04SW** a
1-morphism `schemeStack V ⟶ schemeStack U` is 2-isomorphic to the one attached to a morphism
`q : V ⟶ U` of the big fppf category of `S`, namely the morphism whose `yoneda.map` is the
induced morphism of representing presheaves; and `q` is then flat and locally of finite
presentation as a morphism of schemes. -/
theorem exists_schemeMap_of_isFlat_isLfp {V U : BigFppfOver B S hS}
    (h : schemeStack.{u, w} B S hS V ⟶ schemeStack.{u, w} B S hS U)
    (hflat : AlgebraicStacks.IsFlat B S hS h)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS h) :
    ∃ q : V ⟶ U,
      Flat ((BigFppfOver.toScheme B S hS).map q) ∧
        LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map q) ∧
          Nonempty (h.hom ≅ schemeFibredCategoryMap B S hS q) := by
  obtain ⟨q, hq⟩ : ∃ q : V ⟶ U, yoneda.map q =
      representingMap B S hS (schemeFibredCategory B S hS V) (schemeFibredCategory B S hS U)
        (yoneda.obj V) (yoneda.obj U) (representedChart B S hS V) (representedChart B S hS U)
        h.hom :=
    ⟨yoneda.preimage _, yoneda.map_preimage _⟩
  refine ⟨q, ?_, ?_, ?_⟩
  · refine (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      Flat.isEtaleLocalOnSourceAndTarget q).1 ?_
    rw [hq]
    exact (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS
      (fun _ _ k => Space.IsFlat B S hS k) (Space.isSmoothLocalOnSourceAndTarget_flat B S hS)
      (schemeStack.{u, w} B S hS V).property (schemeStack.{u, w} B S hS U).property
      (yoneda.obj V) (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS V) (isAlgebraicSpace_yoneda B S hS U)
      (representedChart B S hS V) (representedChart B S hS U) h.hom).1
      ((AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS h).1 hflat)
  · refine (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget q).1 ?_
    rw [hq]
    refine (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS
      (fun _ _ k => Space.IsLocallyOfFinitePresentation B S hS k)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
      (schemeStack.{u, w} B S hS V).property (schemeStack.{u, w} B S hS U).property
      (yoneda.obj V) (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS V) (isAlgebraicSpace_yoneda B S hS U)
      (representedChart B S hS V) (representedChart B S hS U) h.hom).1 ?_
    exact (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
      (fun _ _ k => Space.IsLocallyOfFinitePresentation B S hS k)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
      (schemeStack.{u, w} B S hS V).property (schemeStack.{u, w} B S hS U).property h.hom).1 hlfp
  · obtain ⟨hu⟩ := nonempty_unique_twoIso_of_representingMap_eq B S hS
      (schemeFibredCategory B S hS V) (schemeFibredCategory B S hS U)
      (yoneda.obj V) (yoneda.obj U) (representedChart B S hS V) (representedChart B S hS U)
      (f := h.hom) (g := schemeFibredCategoryMap B S hS q)
      (by rw [representingMap_schemeFibredCategoryMap]; exact hq.symm)
    exact ⟨hu.default⟩

/-- **A flat, locally finitely presented morphism of the site through a prescribed point, along
which an object lifts.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` which is
flat and locally of finite presentation, let `y` be an object of the fibre of `𝒴` over an object
`U` of the site, and let `z` be a point of the algebraic stack of `U` whose image in `|𝒴|` under
the 1-morphism named by `y` lies in the image of `|f|`. Then there is a morphism `m : T ⟶ U.left`
of the underlying category of the site which is flat and locally of finite presentation, whose
image contains the point of `U` corresponding to `z`, together with an object of `𝒳` over its
source whose image is isomorphic to the restriction of `y` along `m`.

This is the argument of **Stacks 06QA** with surjectivity of `f` replaced by the hypothesis at the
single point `z`: that hypothesis is what **Stacks 04XH** turns into a point of the 2-fibre
product `𝒳 ×_𝒴 U` above `z`, which the smooth surjective scheme presentation of that 2-fibre
product then lifts. -/
theorem exists_scheme_lift_of_isFlat_isLfp_at_point
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hflat : AlgebraicStacks.IsFlat B S hS f)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (U : BigFppfOver B S hS) (y : 𝒴.val.val.p.Fiber U)
    (z : AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS U))
    (hz : AlgebraicStacks.pointsMap B S hS (fibreObjectStackMap B S hS 𝒴 U y) z ∈
      Set.range (AlgebraicStacks.pointsMap B S hS f)) :
    ∃ (T : B.Schemes) (m : T ⟶ U.left),
      Flat (B.inclusion.map m) ∧ LocallyOfFinitePresentation (B.inclusion.map m) ∧
        pointsHomeomorphScheme B S hS U z ∈ Set.range (B.inclusion.map m) ∧
        ∃ (x : 𝒳.val.val.obj) (α : (CatFiberedInGroupoids.homFunctor f.hom).obj x ⟶ y.1),
          𝒴.val.val.p.IsHomLift
            (Over.homMk m rfl : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U) α := by
  classical
  -- The 2-Yoneda 1-morphism of `y`, out of the algebraic stack of `U`.
  let b : schemeStack.{u, w} B S hS U ⟶ 𝒴 := fibreObjectStackMap B S hS 𝒴 U y
  let Y : schemeFibredCategory B S hS U ⟶ 𝒴.val := b.hom
  -- The 2-fibre product `𝒳 ×_𝒴 U` and its projection to `U`.
  let P : Bicategory.TwoCommSq b f := twoFibreProductSquareAlgebraicStacks B S hS b f
  have hP : Bicategory.IsTwoFibreProduct P :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS b f
  have hPflat : AlgebraicStacks.IsFlat B S hS P.fst :=
    AlgebraicStacks.isFlat_baseChange B S hS f b P hP hflat
  have hPlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS P.fst :=
    AlgebraicStacks.isLocallyOfFinitePresentation_baseChange B S hS f b P hP hlfp
  -- A smooth surjective scheme presentation of the 2-fibre product, and the composite to `U`.
  obtain ⟨V, c, hcsm, hcsurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS P.pt
  have hwflat : AlgebraicStacks.IsFlat B S hS (c ≫ P.fst) :=
    AlgebraicStacks.isFlat_comp B S hS c P.fst
      (AlgebraicStacks.isFlat_of_isSmooth B S hS c hcsm) hPflat
  have hwlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS (c ≫ P.fst) :=
    AlgebraicStacks.isLocallyOfFinitePresentation_comp B S hS c P.fst
      (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS c hcsm) hPlfp
  -- The composite is the 1-morphism attached to a morphism `q : V ⟶ U` of the site.
  obtain ⟨q, hqflat, hqlfp, ⟨e⟩⟩ :=
    exists_schemeMap_of_isFlat_isLfp B S hS (c ≫ P.fst) hwflat hwlfp
  -- The presentation of the 2-fibre product has a point above `z`.
  obtain ⟨ξ, hξ⟩ := hz
  obtain ⟨p, hp, -⟩ :=
    exists_point_of_isTwoFibreProduct_algebraicStacks B S hS P hP z ξ hξ.symm
  obtain ⟨t, ht⟩ := hcsurj p
  have htz : AlgebraicStacks.pointsMap B S hS (c ≫ P.fst) t = z := by
    rwa [AlgebraicStacks.pointsMap_comp, Function.comp_apply, ht]
  have hpts : AlgebraicStacks.pointsMap B S hS (c ≫ P.fst) =
      pointsMap B S hS (schemeFibredCategory B S hS V).val
        (Classical.choose (schemeStack.{u, w} B S hS V).property)
        (Classical.choose (schemeStack.{u, w} B S hS U).property)
        (schemeFibredCategoryMap B S hS q).hom :=
    pointsMap_eq_of_basedNatTrans B S hS (schemeFibredCategory B S hS V).val _ _ e.hom.hom
  refine ⟨V.left, q.left, hqflat, hqlfp, ⟨pointsHomeomorphScheme B S hS V t, ?_⟩, ?_⟩
  · calc B.inclusion.map q.left (pointsHomeomorphScheme B S hS V t)
        = pointsHomeomorphScheme B S hS U
            (pointsMap B S hS (schemeFibredCategory B S hS V).val
              (schemeFibredCategory B S hS V).property
              (schemeFibredCategory B S hS U).property
              (schemeFibredCategoryMap B S hS q).hom t) :=
          (pointsHomeomorphScheme_naturality B S hS q t).symm
      _ = pointsHomeomorphScheme B S hS U
            (AlgebraicStacks.pointsMap B S hS (c ≫ P.fst) t) :=
          congrArg (pointsHomeomorphScheme B S hS U) (congrFun hpts t).symm
      _ = pointsHomeomorphScheme B S hS U z :=
          congrArg (pointsHomeomorphScheme B S hS U) htz
  · obtain ⟨x, α, hα⟩ := exists_fibre_lift_of_twoCell 𝒳.val.val.p 𝒴.val.val.p
      y q f.hom.hom (c ≫ P.snd).hom.hom
      (Functor.TwoYoneda.liftBased 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids U y)
      (Functor.TwoYoneda.chosenLift 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids U y
        (Over.mk (𝟙 U))).φ
      ((Functor.TwoYoneda.chosenLift 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids U y
        (Over.mk (𝟙 U))).isStronglyCartesian.toIsHomLift)
      ((Bicategory.whiskerLeft c P.iso.inv).hom.hom ≫
        (Bicategory.whiskerRight e.hom Y).hom)
    exact ⟨x.1, α, isHomLift_homMk_left B S hS 𝒴.val.val.p q α hα⟩

/-- **Stacks 07AN.** Let `f j : 𝒳 j ⟶ 𝒴`, `j ∈ J`, be a family of 1-morphisms of algebraic stacks
over `S` which are each flat and locally of finite presentation and which are jointly surjective,
that is `|𝒴| = ⋃ j, |f j|(|𝒳 j|)`. Then for every object `U` of the big fppf site of `S` and every
object `y` of the fibre of `𝒴` over `U` there are an fppf covering `{U i → U}_{i ∈ I}` of `U`, a
map `a : I → J` and, for every `i`, an object of `𝒳 (a i)` over `U i` whose image is isomorphic to
the restriction of `y` to `U i`.

The covering is given as a family of morphisms `m i : W i ⟶ U.left` of the underlying category of
the site which are flat, locally of finite presentation and jointly surjective on the underlying
schemes — which is what an fppf covering of `U` is. The isomorphism over a member is rendered as a
morphism from the image of the object to `y` lying over that member, which in a category fibred in
groupoids is exactly an isomorphism in the fibre. -/
@[stacks 07AN "the covering family and the index map"]
theorem exists_fppfCovering_family_fibre_lift {J : Type v}
    {𝒳 : J → AlgebraicStacks.{u, w} B S hS} {𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : ∀ j, 𝒳 j ⟶ 𝒴)
    (hflat : ∀ j, AlgebraicStacks.IsFlat B S hS (f j))
    (hlfp : ∀ j, AlgebraicStacks.IsLocallyOfFinitePresentation B S hS (f j))
    (hjs : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒴)) =
      ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)))
    (U : BigFppfOver B S hS) (y : 𝒴.val.val.p.Fiber U) :
    ∃ (I : Type (u + 1)) (W : I → B.Schemes) (m : ∀ i, W i ⟶ U.left) (a : I → J),
      (∀ i, Flat (B.inclusion.map (m i))) ∧
        (∀ i, LocallyOfFinitePresentation (B.inclusion.map (m i))) ∧
          (∀ x : (B.inclusion.obj U.left), ∃ i, x ∈ Set.range (B.inclusion.map (m i))) ∧
            ∀ i, ∃ (x : (𝒳 (a i)).val.val.obj)
              (α : (CatFiberedInGroupoids.homFunctor (f (a i)).hom).obj x ⟶ y.1),
              𝒴.val.val.p.IsHomLift
                (Over.homMk (m i) rfl :
                  (Over.mk (m i ≫ U.hom) : BigFppfOver B S hS) ⟶ U) α := by
  classical
  have key : ∀ x : (B.inclusion.obj U.left), ∃ (j : J) (T : B.Schemes) (m : T ⟶ U.left),
      Flat (B.inclusion.map m) ∧ LocallyOfFinitePresentation (B.inclusion.map m) ∧
        x ∈ Set.range (B.inclusion.map m) ∧
        ∃ (x' : (𝒳 j).val.val.obj)
          (α : (CatFiberedInGroupoids.homFunctor (f j).hom).obj x' ⟶ y.1),
          𝒴.val.val.p.IsHomLift
            (Over.homMk m rfl : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U) α := by
    intro x
    let _ := pointTopology B S hS (schemeFibredCategory B S hS U)
    let z : AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS U) :=
      (pointsHomeomorphScheme B S hS U).symm x
    have hmem : AlgebraicStacks.pointsMap B S hS (fibreObjectStackMap B S hS 𝒴 U y) z ∈
        ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)) :=
      hjs.subset (Set.mem_univ _)
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hmem
    obtain ⟨T, m, hm₁, hm₂, hm₃, hlift⟩ := exists_scheme_lift_of_isFlat_isLfp_at_point
      B S hS (f j) (hflat j) (hlfp j) U y z hj
    refine ⟨j, T, m, hm₁, hm₂, ?_, hlift⟩
    rwa [show pointsHomeomorphScheme B S hS U z = x from
      (pointsHomeomorphScheme B S hS U).apply_symm_apply x] at hm₃
  choose jj TT mm hmm using key
  exact ⟨ULift.{u + 1} (B.inclusion.obj U.left), fun i => TT i.down, fun i => mm i.down,
    fun i => jj i.down, fun i => (hmm i.down).1, fun i => (hmm i.down).2.1,
    fun x => ⟨ULift.up x, (hmm x).2.2.1⟩, fun i => (hmm i.down).2.2.2⟩

/-- **Stacks 07AN, with the covering as a covering sieve.** Under the hypotheses of
`AlgebraicGeometry.Stack.exists_fppfCovering_family_fibre_lift` there is a covering sieve of `U`
for the big fppf topology of `S` such that over every arrow of it the object `y` is isomorphic to
the image of an object of `𝒳 j` for some `j`.

The index `j` is produced per arrow of the sieve rather than by a map out of the index set of a
covering family, since a sieve carries no family; see
`AlgebraicGeometry.Stack.exists_fppfCovering_family_fibre_lift` for the family form. -/
@[stacks 07AN "the covering sieve form"]
theorem exists_fppfCovering_fibre_lift_of_family {J : Type v}
    {𝒳 : J → AlgebraicStacks.{u, w} B S hS} {𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : ∀ j, 𝒳 j ⟶ 𝒴)
    (hflat : ∀ j, AlgebraicStacks.IsFlat B S hS (f j))
    (hlfp : ∀ j, AlgebraicStacks.IsLocallyOfFinitePresentation B S hS (f j))
    (hjs : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒴)) =
      ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)))
    (U : BigFppfOver B S hS) (y : 𝒴.val.val.p.Fiber U) :
    ∃ R ∈ BigFppfOver.topology B S hS U,
      ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
        ∃ (j : J) (x : (𝒳 j).val.val.obj)
          (α : (CatFiberedInGroupoids.homFunctor (f j).hom).obj x ⟶ y.1),
          𝒴.val.val.p.IsHomLift k α := by
  obtain ⟨I, W, m, a, hmflat, hmlfp, hmcov, hmlift⟩ :=
    exists_fppfCovering_family_fibre_lift B S hS f hflat hlfp hjs U y
  obtain ⟨R, hR, hfac⟩ := exists_mem_topology_of_family B S hS W m hmflat hmlfp hmcov
  refine ⟨R, hR, ?_⟩
  intro V k hk
  obtain ⟨i, c, hc⟩ := hfac hk
  obtain ⟨x, α, hα⟩ := hmlift i
  have hw : CatFiberedInGroupoids.homFunctor (f (a i)).hom ⋙ 𝒴.val.val.p =
      (𝒳 (a i)).val.val.p := (f (a i)).hom.hom.w
  have hxbase : (𝒳 (a i)).val.val.p.obj x = Over.mk (m i ≫ U.hom) := by
    rw [← hw]
    exact IsHomLift.domain_eq 𝒴.val.val.p
      (Over.homMk (m i) rfl : (Over.mk (m i ≫ U.hom) : BigFppfOver B S hS) ⟶ U) α
  obtain ⟨x', ρ, hρ⟩ := (𝒳 (a i)).val.isFiberedInGroupoids.exists_lift c x hxbase
  refine ⟨a i, x', (CatFiberedInGroupoids.homFunctor (f (a i)).hom).map ρ ≫ α, ?_⟩
  rw [← hc]
  have h₁ : 𝒴.val.val.p.IsHomLift c
      ((CatFiberedInGroupoids.homFunctor (f (a i)).hom).map ρ) :=
    PresheafOfCategories.isHomLift_map_of_comp hw c ρ hρ
  exact IsHomLift.comp 𝒴.val.val.p c
    (Over.homMk (m i) rfl : (Over.mk (m i ≫ U.hom) : BigFppfOver B S hS) ⟶ U)
    ((CatFiberedInGroupoids.homFunctor (f (a i)).hom).map ρ) α

end AlgebraicGeometry.Stack

end
