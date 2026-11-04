module

public import StacksFrontier.AlgebraicGeometry.Stacks.ParasiticLisseEtaleVanishing
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticFlatLocalLifts

/-!
# Lifting a flat object along a jointly surjective family of flat 1-morphisms

Let `f j : 𝒳 j ⟶ 𝒴` be a family of *flat* 1-morphisms of algebraic stacks over `S` which is
jointly surjective on points, and let `y` be a flat object of `𝒴` over `U`.  For every point of
`U` there is a flat morphism of the site `T ⟶ U` through that point together with a lift of the
restriction of `y` to `T` to a flat object of some `𝒳 j`.

This is `AlgebraicGeometry.Stack.exists_flatObject_lift_of_isFlat_isLfp_at_point` (Stacks 0774,
07AN) with the hypothesis that the `f j` are locally of finite presentation dropped and, with it,
the conclusion that `T ⟶ U` is: the argument is the same, through a smooth surjective scheme
presentation of the 2-fibre product `𝒳 j ×_𝒴 U`, whose projection to `U` is flat as soon as
`f j` is.  It is the geometric input of the proof of Stacks 0GQF, where the family is that of the
flat objects `x_i : U_i → 𝒳`, which need not be locally of finite presentation: the source covers
`V ×_𝒳 U_i` by schemes `W_{i,j}` flat over both factors.

## Main results

* `AlgebraicGeometry.Stack.exists_schemeMap_of_isFlat`: a flat 1-morphism between represented
  algebraic stacks is 2-isomorphic to the one attached to a flat morphism of the site.
* `AlgebraicGeometry.Stack.exists_flatObject_lift_of_isFlat_at_point`: the pointwise statement.
* `AlgebraicGeometry.Stack.exists_flatCovering_family_flatObject_lift`: the covering statement,
  with the members flat and jointly surjective.

## References

* [Stacks Project, Tag 0GQF](https://stacks.math.columbia.edu/tag/0GQF)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 06PY](https://stacks.math.columbia.edu/tag/06PY)
-/

@[expose] public section

open CategoryTheory

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.BasedFunctor.comp CategoryTheory.BasedFunctor.overMap

namespace AlgebraicGeometry.Stack

universe u w v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A flat 1-morphism of represented algebraic stacks comes from a flat morphism of the
site.** -/
theorem exists_schemeMap_of_isFlat {V U : BigFppfOver B S hS}
    (h : schemeStack.{u, w} B S hS V ⟶ schemeStack.{u, w} B S hS U)
    (hflat : AlgebraicStacks.IsFlat B S hS h) :
    ∃ q : V ⟶ U,
      Flat ((BigFppfOver.toScheme B S hS).map q) ∧
        Nonempty (h.hom ≅ schemeFibredCategoryMap B S hS q) := by
  obtain ⟨q, hq⟩ : ∃ q : V ⟶ U, yoneda.map q =
      representingMap B S hS (schemeFibredCategory B S hS V) (schemeFibredCategory B S hS U)
        (yoneda.obj V) (yoneda.obj U) (representedChart B S hS V) (representedChart B S hS U)
        h.hom :=
    ⟨yoneda.preimage _, yoneda.map_preimage _⟩
  refine ⟨q, ?_, ?_⟩
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
  · obtain ⟨hu⟩ := nonempty_unique_twoIso_of_representingMap_eq B S hS
      (schemeFibredCategory B S hS V) (schemeFibredCategory B S hS U)
      (yoneda.obj V) (yoneda.obj U) (representedChart B S hS V) (representedChart B S hS U)
      (f := h.hom) (g := schemeFibredCategoryMap B S hS q)
      (by rw [representingMap_schemeFibredCategoryMap]; exact hq.symm)
    exact ⟨hu.default⟩

/-- A point of a represented algebraic stack mapping to `z` along a 1-morphism 2-isomorphic to
the one attached to `q` exhibits the point of the scheme corresponding to `z` in the image of
`q`. -/
theorem mem_range_inclusion_map_of_pointsMap_eq {V W : BigFppfOver B S hS} (q : V ⟶ W)
    (g : schemeStack.{u, w} B S hS V ⟶ schemeStack.{u, w} B S hS W)
    (e : g.hom ≅ schemeFibredCategoryMap B S hS q)
    (t : AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS V))
    (z : AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS W))
    (htz : AlgebraicStacks.pointsMap B S hS g t = z) :
    pointsHomeomorphScheme B S hS W z ∈ Set.range (B.inclusion.map q.left) := by
  subst htz
  have hpts : AlgebraicStacks.pointsMap B S hS g =
      pointsMap B S hS (schemeFibredCategory B S hS V).val
        (Classical.choose (schemeStack.{u, w} B S hS V).property)
        (Classical.choose (schemeStack.{u, w} B S hS W).property)
        (schemeFibredCategoryMap B S hS q).hom :=
    pointsMap_eq_of_basedNatTrans B S hS (schemeFibredCategory B S hS V).val _ _ e.hom.hom
  refine ⟨pointsHomeomorphScheme B S hS V t, ?_⟩
  calc B.inclusion.map q.left (pointsHomeomorphScheme B S hS V t)
      = pointsHomeomorphScheme B S hS W
          (pointsMap B S hS (schemeFibredCategory B S hS V).val
            (schemeFibredCategory B S hS V).property
            (schemeFibredCategory B S hS W).property
            (schemeFibredCategoryMap B S hS q).hom t) :=
        (pointsHomeomorphScheme_naturality B S hS q t).symm
    _ = pointsHomeomorphScheme B S hS W (AlgebraicStacks.pointsMap B S hS g t) :=
        congrArg (pointsHomeomorphScheme B S hS W) (congrFun hpts t).symm

/-- **A flat morphism of the site through a prescribed point, along which a flat object lifts to
a flat object,** for a flat 1-morphism which need not be locally of finite presentation. -/
theorem exists_flatObject_lift_of_isFlat_at_point
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hflat : AlgebraicStacks.IsFlat B S hS f)
    (U : BigFppfOver B S hS) (y : 𝒴.val.val.p.Fiber U)
    (hy : flatObject B S hS 𝒴.val y.1)
    (z : AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS U))
    (hz : AlgebraicStacks.pointsMap B S hS (fibreObjectStackMap B S hS 𝒴 U y) z ∈
      Set.range (AlgebraicStacks.pointsMap B S hS f)) :
    ∃ (T : B.Schemes) (m : T ⟶ U.left),
      Flat (B.inclusion.map m) ∧
        pointsHomeomorphScheme B S hS U z ∈ Set.range (B.inclusion.map m) ∧
        ∃ x : 𝒳.val.val.obj, flatObject B S hS 𝒳.val x ∧
          ∃ α : (CatFiberedInGroupoids.homFunctor f.hom).obj x ⟶ y.1,
            𝒴.val.val.p.IsHomLift
              (Over.homMk m rfl : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U) α := by
  classical
  obtain ⟨y, rfl⟩ := y
  -- The 2-Yoneda 1-morphism of `y`, out of the algebraic stack of `U`; it is flat.
  let b : schemeStack.{u, w} B S hS (𝒴.val.val.p.obj y) ⟶ 𝒴 :=
    fibreObjectStackMap B S hS 𝒴 (𝒴.val.val.p.obj y) (Functor.Fiber.mk rfl)
  let Y : schemeFibredCategory B S hS (𝒴.val.val.p.obj y) ⟶ 𝒴.val := b.hom
  -- The 2-fibre product `𝒳 ×_𝒴 U` and its two projections, both flat.
  let P : Bicategory.TwoCommSq b f := twoFibreProductSquareAlgebraicStacks B S hS b f
  have hP : Bicategory.IsTwoFibreProduct P :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS b f
  -- A smooth surjective scheme presentation of the 2-fibre product, and the two composites.
  obtain ⟨V, c, hcsm, hcsurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS P.pt
  have hc := AlgebraicStacks.isFlat_of_isSmooth B S hS c hcsm
  have hwflat : AlgebraicStacks.IsFlat B S hS (c ≫ P.fst) :=
    AlgebraicStacks.isFlat_comp B S hS c P.fst hc
      (AlgebraicStacks.isFlat_baseChange B S hS f b P hP hflat)
  have hsndflat : AlgebraicStacks.IsFlat B S hS (c ≫ P.snd) :=
    AlgebraicStacks.isFlat_comp B S hS c P.snd hc
      (AlgebraicStacks.isFlat_baseChange B S hS b f P.swap (Bicategory.isTwoFibreProduct_swap hP)
        (isFlat_fibreObjectStackMap B S hS y hy))
  -- The composite with the first projection is the 1-morphism attached to a morphism of the site.
  obtain ⟨q, hqflat, ⟨e⟩⟩ :=
    exists_schemeMap_of_isFlat B S hS (c ≫ P.fst) hwflat
  -- The presentation of the 2-fibre product has a point above `z`.
  obtain ⟨ξ, hξ⟩ := hz
  obtain ⟨pt, hpt, -⟩ :=
    exists_point_of_isTwoFibreProduct_algebraicStacks B S hS P hP z ξ hξ.symm
  obtain ⟨t, ht⟩ := hcsurj pt
  have htz : AlgebraicStacks.pointsMap B S hS (c ≫ P.fst) t = z := by
    rwa [AlgebraicStacks.pointsMap_comp, Function.comp_apply, ht]
  refine ⟨V.left, q.left, hqflat,
    mem_range_inclusion_map_of_pointsMap_eq B S hS q (c ≫ P.fst) e t z htz, ?_⟩
  refine ⟨(c ≫ P.snd).hom.hom.obj (Over.mk (𝟙 V)),
    FlatFppf.flatObject_map B S hS (c ≫ P.snd) hsndflat
      ⟨Over.mk (𝟙 V), flatObject_schemeStack_id.{u, w} B S hS V⟩, ?_⟩
  let L := Functor.TwoYoneda.chosenLift 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
    (𝒴.val.val.p.obj y) (Functor.Fiber.mk rfl) (Over.mk (𝟙 (𝒴.val.val.p.obj y)))
  obtain ⟨α, hα⟩ := exists_isHomLift_twoCellFibreLift 𝒳.val.val.p 𝒴.val.val.p
    (Functor.Fiber.mk (a := y) rfl) q f.hom.hom (c ≫ P.snd).hom.hom
    (Functor.TwoYoneda.liftBased 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
      (𝒴.val.val.p.obj y) (Functor.Fiber.mk rfl))
    L.φ L.isStronglyCartesian.toIsHomLift
    ((Bicategory.whiskerLeft c P.iso.inv).hom.hom ≫
      (Bicategory.whiskerRight e.hom Y).hom)
  exact ⟨α, isHomLift_homMk_left B S hS 𝒴.val.val.p q α hα⟩

/-- **Flat lifts of a flat object along a jointly surjective family of flat 1-morphisms.** The
members `m i` are flat and jointly surjective; they need not be locally of finite presentation. -/
theorem exists_flatCovering_family_flatObject_lift {J : Type v}
    {𝒳 : J → AlgebraicStacks.{u, w} B S hS} {𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : ∀ j, 𝒳 j ⟶ 𝒴)
    (hflat : ∀ j, AlgebraicStacks.IsFlat B S hS (f j))
    (hjs : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒴)) =
      ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)))
    (U : BigFppfOver B S hS) (y : 𝒴.val.val.p.Fiber U)
    (hy : flatObject B S hS 𝒴.val y.1) :
    ∃ (I : Type (u + 1)) (W : I → B.Schemes) (m : ∀ i, W i ⟶ U.left) (a : I → J),
      (∀ i, Flat (B.inclusion.map (m i))) ∧
          (∀ x : (B.inclusion.obj U.left), ∃ i, x ∈ Set.range (B.inclusion.map (m i))) ∧
            ∀ i, ∃ x : (𝒳 (a i)).val.val.obj, flatObject B S hS (𝒳 (a i)).val x ∧
              ∃ α : (CatFiberedInGroupoids.homFunctor (f (a i)).hom).obj x ⟶ y.1,
                𝒴.val.val.p.IsHomLift
                  (Over.homMk (m i) rfl :
                    (Over.mk (m i ≫ U.hom) : BigFppfOver B S hS) ⟶ U) α := by
  classical
  have key : ∀ x : (B.inclusion.obj U.left), ∃ (j : J) (T : B.Schemes) (m : T ⟶ U.left),
      Flat (B.inclusion.map m) ∧
        x ∈ Set.range (B.inclusion.map m) ∧
        ∃ x' : (𝒳 j).val.val.obj, flatObject B S hS (𝒳 j).val x' ∧
          ∃ α : (CatFiberedInGroupoids.homFunctor (f j).hom).obj x' ⟶ y.1,
            𝒴.val.val.p.IsHomLift
              (Over.homMk m rfl : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U) α := by
    intro x
    let _ := pointTopology B S hS (schemeFibredCategory B S hS U)
    let z : AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS U) :=
      (pointsHomeomorphScheme B S hS U).symm x
    have hmem : AlgebraicStacks.pointsMap B S hS (fibreObjectStackMap B S hS 𝒴 U y) z ∈
        ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)) :=
      hjs ▸ Set.mem_univ _
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hmem
    obtain ⟨T, m, hm₁, hm₃, hlift⟩ := exists_flatObject_lift_of_isFlat_at_point
      B S hS (f j) (hflat j) U y hy z hj
    refine ⟨j, T, m, hm₁, ?_, hlift⟩
    rwa [show pointsHomeomorphScheme B S hS U z = x from
      (pointsHomeomorphScheme B S hS U).apply_symm_apply x] at hm₃
  choose jj TT mm hmm using key
  exact ⟨ULift.{u + 1} (B.inclusion.obj U.left), fun i => TT i.down, fun i => mm i.down,
    fun i => jj i.down, fun i => (hmm i.down).1,
    fun x => ⟨ULift.up x, (hmm x).2.1⟩, fun i => (hmm i.down).2.2⟩

end AlgebraicGeometry.Stack

end
