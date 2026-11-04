module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfSiteFunctor
public import StacksFrontier.AlgebraicGeometry.Stacks.JointlySurjectiveFlatFppfLocalSections
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStackTerminalSubsite
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# Lifting a flat object along a jointly surjective flat family (Stacks 0774)

Let `f j : 𝒳 j ⟶ 𝒴` be a family of flat, locally finitely presented 1-morphisms of algebraic
stacks over `S` which is jointly surjective, and let `y` be an object of `𝒴` which is *flat* in
the sense of **Stacks 0787**. **Stacks 07AN**, which this library has as
`AlgebraicGeometry.Stack.exists_fppfCovering_family_fibre_lift`, produces an fppf covering of the
scheme `y` lies over together with a lift of `y` to some `𝒳 j` over each member. This file adds
the conclusion the proof of clause (4) of **Stacks 0774** needs and 07AN does not record: when
`y` is flat, the lifts may be taken to be *flat objects* of the `𝒳 j`.

That is not a formal consequence of 07AN: a lift of a flat object along a flat 1-morphism need
not be flat, and what makes it flat is the construction. The lift of 07AN is the image of the
tautological object under a smooth surjective scheme presentation of the 2-fibre product
`𝒳 j ×_𝒴 U` followed by the projection to `𝒳 j`, and that projection is the base change of the
2-Yoneda 1-morphism of `y`, which is flat exactly because `y` is a flat object. So the composite
is flat, and a flat 1-morphism carries flat objects to flat objects
(`AlgebraicGeometry.Stack.FlatFppf.flatObject_map`), the tautological object being flat by
`AlgebraicGeometry.Stack.flatObject_schemeStack_id`.

## Main results

* `AlgebraicGeometry.Stack.exists_isHomLift_twoCellFibreLift`: the lift produced by a 2-cell,
  with its witness named. This is the witness-level refinement of
  `AlgebraicGeometry.Stack.exists_fibre_lift_of_twoCell`, which states the same lift as an
  existential and so hides which object it is; naming it is what lets its flatness be read off.
* `AlgebraicGeometry.Stack.isFlat_fibreObjectStackMap`: the 2-Yoneda 1-morphism of a flat object
  is a flat 1-morphism — the two notions are the same proposition.
* `AlgebraicGeometry.Stack.exists_flatObject_lift_of_isFlat_isLfp_at_point`: the pointwise
  statement, with the lift flat.
* `AlgebraicGeometry.Stack.exists_fppfCovering_family_flatObject_lift`: the covering-family
  statement, with every lift flat.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 06PY](https://stacks.math.columbia.edu/tag/06PY)
* [Stacks Project, Tag 06QA](https://stacks.math.columbia.edu/tag/06QA)
* [Stacks Project, Tag 0774](https://stacks.math.columbia.edu/tag/0774)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 07AN](https://stacks.math.columbia.edu/tag/07AN)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w v v₁ u₁ v₂ u₂ v₃ u₃

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

/-- **The lift of an object produced by a 2-cell, with its witness named.** In the situation of
`AlgebraicGeometry.Stack.exists_fibre_lift_of_twoCell` the lift of `y` along `q` is the value of
`a` at the tautological object of the slice of `V`, and this records that: only the comparison
morphism is existentially quantified.

The existential form loses which object the lift is, and that is exactly what a consumer needing
a *property* of the lift — here flatness — has to know. -/
theorem exists_isHomLift_twoCellFibreLift {C : Type u₁} [Category.{v₁} C]
    {X : Type u₂} [Category.{v₂} X] {Y : Type u₃} [Category.{v₃} Y]
    (p : X ⥤ C) (r : Y ⥤ C)
    {U V : C} (y : r.Fiber U) (q : V ⟶ U)
    (g : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor r)
    (a : BasedCategory.slice V ⥤ᵇ BasedCategory.ofFunctor p)
    (H : BasedCategory.slice U ⥤ᵇ BasedCategory.ofFunctor r)
    (cy : H.obj (Over.mk (𝟙 U)) ⟶ y.1) (hcy : r.IsHomLift (𝟙 U) cy)
    (η : BasedFunctor.comp a g ⟶ BasedFunctor.comp (BasedFunctor.overMap q) H) :
    ∃ α : g.obj (a.obj (Over.mk (𝟙 V))) ⟶ y.1, r.IsHomLift q α := by
  have : r.IsHomLift (𝟙 V) (η.app (Over.mk (𝟙 V))) := η.isHomLift' (Over.mk (𝟙 V))
  have := Functor.TwoYoneda.isHomLift_map_from_mkIdTerminal_unitOver r q (H := H)
  have : r.IsHomLift q
      (H.map (Over.mkIdTerminal.from (Functor.TwoYoneda.unitOver q)) ≫ cy :
        (BasedFunctor.comp (BasedFunctor.overMap q) H).obj (Over.mk (𝟙 V)) ⟶ y.1) :=
    IsHomLift.comp_lift_id_right' r q
      (H.map (Over.mkIdTerminal.from (Functor.TwoYoneda.unitOver q))) U cy
  exact ⟨_, IsHomLift.comp_lift_id_left' r V (η.app (Over.mk (𝟙 V))) q
    (H.map (Over.mkIdTerminal.from (Functor.TwoYoneda.unitOver q)) ≫ cy)⟩

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The 2-Yoneda 1-morphism of a flat object is a flat 1-morphism.** Flatness of an object
(**Stacks 0787**) is by definition the existential smooth-diagram condition of **Stacks 06FM**
for the 1-morphism the object names under the 2-Yoneda lemma, and flatness of a 1-morphism of
algebraic stacks (**Stacks 06PW**) is that same condition; so the two are the same
proposition. -/
theorem isFlat_fibreObjectStackMap {𝒴 : AlgebraicStacks.{u, w} B S hS} (y : 𝒴.val.val.obj)
    (hy : flatObject B S hS 𝒴.val y) :
    AlgebraicStacks.IsFlat B S hS
      (fibreObjectStackMap B S hS 𝒴 (𝒴.val.val.p.obj y) (Functor.Fiber.mk rfl)) :=
  (AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS _).2 hy

/-- **A flat, locally finitely presented morphism of the site through a prescribed point, along
which a flat object lifts to a flat object.**

This is `AlgebraicGeometry.Stack.exists_scheme_lift_of_isFlat_isLfp_at_point` with the extra
hypothesis that `y` is a flat object of `𝒴` and the extra conclusion that the lift is a flat
object of `𝒳`. That conclusion is not a consequence of the statement without it: the lift is the
image of the tautological object under the composite of a smooth surjective scheme presentation
`c` of the 2-fibre product `𝒳 ×_𝒴 U` with the projection to `𝒳`, and that projection is flat
exactly because the 2-Yoneda 1-morphism of `y` is, i.e. because `y` is a flat object. A flat
1-morphism carries flat objects to flat objects, and the tautological object is flat. -/
theorem exists_flatObject_lift_of_isFlat_isLfp_at_point
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hflat : AlgebraicStacks.IsFlat B S hS f)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (U : BigFppfOver B S hS) (y : 𝒴.val.val.p.Fiber U)
    (hy : flatObject B S hS 𝒴.val y.1)
    (z : AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS U))
    (hz : AlgebraicStacks.pointsMap B S hS (fibreObjectStackMap B S hS 𝒴 U y) z ∈
      Set.range (AlgebraicStacks.pointsMap B S hS f)) :
    ∃ (T : B.Schemes) (m : T ⟶ U.left),
      Flat (B.inclusion.map m) ∧ LocallyOfFinitePresentation (B.inclusion.map m) ∧
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
  have hPflat : AlgebraicStacks.IsFlat B S hS P.fst :=
    AlgebraicStacks.isFlat_baseChange B S hS f b P hP hflat
  have hPlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS P.fst :=
    AlgebraicStacks.isLocallyOfFinitePresentation_baseChange B S hS f b P hP hlfp
  have hPsnd : AlgebraicStacks.IsFlat B S hS P.snd :=
    AlgebraicStacks.isFlat_baseChange B S hS b f P.swap
      (Bicategory.isTwoFibreProduct_swap hP) (isFlat_fibreObjectStackMap B S hS y hy)
  -- A smooth surjective scheme presentation of the 2-fibre product, and the two composites.
  obtain ⟨V, c, hcsm, hcsurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS P.pt
  have hwflat : AlgebraicStacks.IsFlat B S hS (c ≫ P.fst) :=
    AlgebraicStacks.isFlat_comp B S hS c P.fst
      (AlgebraicStacks.isFlat_of_isSmooth B S hS c hcsm) hPflat
  have hwlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS (c ≫ P.fst) :=
    AlgebraicStacks.isLocallyOfFinitePresentation_comp B S hS c P.fst
      (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS c hcsm) hPlfp
  have hsndflat : AlgebraicStacks.IsFlat B S hS (c ≫ P.snd) :=
    AlgebraicStacks.isFlat_comp B S hS c P.snd
      (AlgebraicStacks.isFlat_of_isSmooth B S hS c hcsm) hPsnd
  -- The composite with the first projection is the 1-morphism attached to a morphism of the site.
  obtain ⟨q, hqflat, hqlfp, ⟨e⟩⟩ :=
    exists_schemeMap_of_isFlat_isLfp B S hS (c ≫ P.fst) hwflat hwlfp
  -- The presentation of the 2-fibre product has a point above `z`.
  obtain ⟨ξ, hξ⟩ := hz
  obtain ⟨pt, hpt, -⟩ :=
    exists_point_of_isTwoFibreProduct_algebraicStacks B S hS P hP z ξ hξ.symm
  obtain ⟨t, ht⟩ := hcsurj pt
  have htz : AlgebraicStacks.pointsMap B S hS (c ≫ P.fst) t = z := by
    rwa [AlgebraicStacks.pointsMap_comp, Function.comp_apply, ht]
  have hpts : AlgebraicStacks.pointsMap B S hS (c ≫ P.fst) =
      pointsMap B S hS (schemeFibredCategory B S hS V).val
        (Classical.choose (schemeStack.{u, w} B S hS V).property)
        (Classical.choose (schemeStack.{u, w} B S hS (𝒴.val.val.p.obj y)).property)
        (schemeFibredCategoryMap B S hS q).hom :=
    pointsMap_eq_of_basedNatTrans B S hS (schemeFibredCategory B S hS V).val _ _ e.hom.hom
  refine ⟨V.left, q.left, hqflat, hqlfp, ⟨pointsHomeomorphScheme B S hS V t, ?_⟩, ?_⟩
  · exact (pointsHomeomorphScheme_naturality B S hS q t).symm.trans
      (congrArg (pointsHomeomorphScheme B S hS _) ((congrFun hpts t).symm.trans htz))
  · refine ⟨(c ≫ P.snd).hom.hom.obj (Over.mk (𝟙 V)), ?_, ?_⟩
    · exact FlatFppf.flatObject_map B S hS (c ≫ P.snd) hsndflat
        ⟨Over.mk (𝟙 V), flatObject_schemeStack_id.{u, w} B S hS V⟩
    · obtain ⟨α, hα⟩ := exists_isHomLift_twoCellFibreLift 𝒳.val.val.p 𝒴.val.val.p
        (Functor.Fiber.mk (a := y) rfl) q f.hom.hom (c ≫ P.snd).hom.hom
        (Functor.TwoYoneda.liftBased 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
          (𝒴.val.val.p.obj y) (Functor.Fiber.mk rfl))
        (Functor.TwoYoneda.chosenLift 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
          (𝒴.val.val.p.obj y) (Functor.Fiber.mk rfl)
          (Over.mk (𝟙 (𝒴.val.val.p.obj y)))).φ
        ((Functor.TwoYoneda.chosenLift 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
          (𝒴.val.val.p.obj y) (Functor.Fiber.mk rfl)
          (Over.mk (𝟙 (𝒴.val.val.p.obj y)))).isStronglyCartesian.toIsHomLift)
        ((Bicategory.whiskerLeft c P.iso.inv).hom.hom ≫
          (Bicategory.whiskerRight e.hom Y).hom)
      exact ⟨α, isHomLift_homMk_left B S hS 𝒴.val.val.p q α hα⟩

/-- **Stacks 07AN for a flat object, with flat lifts.** Let `f j : 𝒳 j ⟶ 𝒴` be a jointly
surjective family of flat, locally finitely presented 1-morphisms of algebraic stacks over `S`,
and let `y` be an object of `𝒴` which is flat in the sense of **Stacks 0787**. Then the fppf
covering of **Stacks 07AN** can be chosen so that each lift of `y` is itself a *flat object* of
the corresponding `𝒳 j`.

The covering is given, as in `AlgebraicGeometry.Stack.exists_fppfCovering_family_fibre_lift`, as
a family of morphisms of the underlying category of the site which are flat, locally of finite
presentation and jointly surjective on the underlying schemes. -/
theorem exists_fppfCovering_family_flatObject_lift {J : Type v}
    {𝒳 : J → AlgebraicStacks.{u, w} B S hS} {𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : ∀ j, 𝒳 j ⟶ 𝒴)
    (hflat : ∀ j, AlgebraicStacks.IsFlat B S hS (f j))
    (hlfp : ∀ j, AlgebraicStacks.IsLocallyOfFinitePresentation B S hS (f j))
    (hjs : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒴)) =
      ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)))
    (U : BigFppfOver B S hS) (y : 𝒴.val.val.p.Fiber U)
    (hy : flatObject B S hS 𝒴.val y.1) :
    ∃ (I : Type (u + 1)) (W : I → B.Schemes) (m : ∀ i, W i ⟶ U.left) (a : I → J),
      (∀ i, Flat (B.inclusion.map (m i))) ∧
        (∀ i, LocallyOfFinitePresentation (B.inclusion.map (m i))) ∧
          (∀ x : (B.inclusion.obj U.left), ∃ i, x ∈ Set.range (B.inclusion.map (m i))) ∧
            ∀ i, ∃ x : (𝒳 (a i)).val.val.obj, flatObject B S hS (𝒳 (a i)).val x ∧
              ∃ α : (CatFiberedInGroupoids.homFunctor (f (a i)).hom).obj x ⟶ y.1,
                𝒴.val.val.p.IsHomLift
                  (Over.homMk (m i) rfl :
                    (Over.mk (m i ≫ U.hom) : BigFppfOver B S hS) ⟶ U) α := by
  classical
  have key : ∀ x : (B.inclusion.obj U.left), ∃ (j : J) (T : B.Schemes) (m : T ⟶ U.left),
      Flat (B.inclusion.map m) ∧ LocallyOfFinitePresentation (B.inclusion.map m) ∧
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
    obtain ⟨T, m, hm₁, hm₂, hm₃, hlift⟩ := exists_flatObject_lift_of_isFlat_isLfp_at_point
      B S hS (f j) (hflat j) (hlfp j) U y hy z hj
    refine ⟨j, T, m, hm₁, hm₂, ?_, hlift⟩
    rwa [show pointsHomeomorphScheme B S hS U z = x from
      (pointsHomeomorphScheme B S hS U).apply_symm_apply x] at hm₃
  choose jj TT mm hmm using key
  exact ⟨ULift.{u + 1} (B.inclusion.obj U.left), fun i => TT i.down, fun i => mm i.down,
    fun i => jj i.down, fun i => (hmm i.down).1, fun i => (hmm i.down).2.1,
    fun x => ⟨ULift.up x, (hmm x).2.2.1⟩, fun i => (hmm i.down).2.2.2⟩

end AlgebraicGeometry.Stack

end
