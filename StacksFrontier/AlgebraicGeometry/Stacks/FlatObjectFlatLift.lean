module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfSite
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatObjectFibreLifts
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticFlatLocalLifts
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveFlatFppfLocalSections

/-!
# Fppf-local lifts of a flat object along a presentation, with flat structure morphism

Let `f : 𝒲 ⟶ 𝒳` be a 1-morphism of algebraic stacks over `S` which is surjective, flat and locally
of finite presentation, with `𝒲` the algebraic stack of a scheme `W` over `S`. **Stacks 06QA**
lifts every object `y` of `𝒳` over a scheme `U`, after a flat, locally finitely presented,
surjective base change `T ⟶ U`, to an object `x` of `𝒲`, that is to a morphism `T ⟶ W`. This
file records what the source's own construction gives in addition when `y` is a *flat* object of
`𝒳` (Stacks 0H14): the morphism `T ⟶ W` named by the lift is flat.

This is the geometric input of the source's proof of Stacks 0779 part (1): for `y : V → 𝒳` flat,
the projection `V ×_𝒳 W ⟶ W` is a base change of `y`, hence flat, and the lift is read off a
smooth presentation of the 2-fibre product `V ×_𝒳 W`.

## Main results

* `AlgebraicGeometry.Stack.exists_scheme_lift_flat_of_flatObject`: the lift of Stacks 06QA of a
  flat object along a surjective, flat, locally finitely presented 1-morphism out of the algebraic
  stack of a scheme `W`, with flat structure morphism to `W`.

## Implementation notes

The proof is that of `AlgebraicGeometry.Stack.exists_scheme_lift_of_isSurjective_isFlat_isLfp`,
which is not reused as a black box because its conclusion forgets *which* object of `𝒲` the lift
is. Here the lift is the value at the unit object of the composite `c ≫ P.snd` of a smooth
presentation `c` of the 2-fibre product `P` with its second projection; that composite is flat,
since `P.snd` is the base change of the flat 1-morphism `y : V → 𝒳` along `f` (Stacks 06PY on the
exchanged square), so by Stacks 04SW it is 2-isomorphic to the 1-morphism attached to a flat
morphism `q' : V' ⟶ W` of the site, and the lift is isomorphic over `W` to `q'`.

The flatness of `y` is `AlgebraicGeometry.Stack.flatObject`, which is the existential
smooth-diagram criterion for the 2-Yoneda 1-morphism `AlgebraicGeometry.Stack.objectMorphism` of
`y`; that 1-morphism is, by definition, the one the proof of Stacks 06QA forms the 2-fibre product
with, so no comparison is needed.

## References

* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 06PY](https://stacks.math.columbia.edu/tag/06PY)
* [Stacks Project, Tag 06QA](https://stacks.math.columbia.edu/tag/06QA)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 0H14](https://stacks.math.columbia.edu/tag/0H14)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.BasedFunctor.comp CategoryTheory.BasedFunctor.overMap

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The value at the unit object of a 1-morphism of represented categories coming from a flat
morphism of the site has flat structure morphism.** If `a : schemeFibredCategory V ⟶
schemeFibredCategory W` is 2-isomorphic to the 1-morphism attached to `q : V ⟶ W` with `q` flat,
then the object `a(1_V)` of the slice over `W` has flat structure morphism: the component of the
2-isomorphism at `1_V` is an isomorphism over `W` from `a(1_V)` to `1_V · q`. -/
theorem flat_obj_unit_of_iso_schemeFibredCategoryMap {V W : BigFppfOver B S hS}
    (a : schemeFibredCategory B S hS V ⟶ schemeFibredCategory B S hS W) (q : V ⟶ W)
    (e : a ≅ schemeFibredCategoryMap B S hS q)
    (hq : Flat ((BigFppfOver.toScheme B S hS).map q)) :
    Flat (B.inclusion.map (a.hom.toFunctor.obj (Over.mk (𝟙 V))).hom.left) := by
  let k : a.hom.toFunctor.obj (Over.mk (𝟙 V)) ⟶
      (schemeFibredCategoryMap B S hS q).hom.toFunctor.obj (Over.mk (𝟙 V)) :=
    e.hom.hom.toNatTrans.app (Over.mk (𝟙 V))
  let k' : (schemeFibredCategoryMap B S hS q).hom.toFunctor.obj (Over.mk (𝟙 V)) ⟶
      a.hom.toFunctor.obj (Over.mk (𝟙 V)) :=
    e.inv.hom.toNatTrans.app (Over.mk (𝟙 V))
  have hkk' : k ≫ k' = 𝟙 _ :=
    congrArg (fun t => t.hom.toNatTrans.app (Over.mk (𝟙 V))) e.hom_inv_id
  have hk'k : k' ≫ k = 𝟙 _ :=
    congrArg (fun t => t.hom.toNatTrans.app (Over.mk (𝟙 V))) e.inv_hom_id
  have : IsIso k := ⟨⟨k', hkk', hk'k⟩⟩
  have : IsIso k.left := inferInstanceAs (IsIso ((Over.forget W).map k))
  have : IsIso k.left.left := inferInstanceAs (IsIso ((Over.forget (B.obj hS)).map k.left))
  have hw : (a.hom.toFunctor.obj (Over.mk (𝟙 V))).hom.left =
      k.left.left ≫ (𝟙 V ≫ q).left :=
    (congrArg CommaMorphism.left (Over.w k)).symm
  have key : ∀ {X Y Z : B.Schemes} (g : X ⟶ Y) (g' : Y ⟶ Z) [IsIso g],
      Flat (B.inclusion.map g') → Flat (B.inclusion.map (g ≫ g')) := by
    intro X Y Z g g' _ hg'
    rw [Functor.map_comp]
    infer_instance
  rw [hw]
  refine key _ _ ?_
  rw [Category.id_comp]
  exact hq

/-- **The lift of Stacks 06QA of a flat object has flat structure morphism.** Let
`f : schemeStack W ⟶ 𝒳` be a surjective, flat, locally finitely presented 1-morphism out of the
algebraic stack of a scheme `W` over `S`, and let `y` be a flat object of `𝒳`, lying over `U`.
Then there are a flat, locally finitely presented, surjective morphism `m : T ⟶ U` of the
underlying category of the site, an object `x` of the slice over `W` whose structure morphism
`x ⟶ W` is flat, and a morphism `f(x) ⟶ y` lying over `m`.

This is the source's construction of Stacks 06QA at the 2-fibre product `P = U ×_𝒳 W`: the second
projection `P ⟶ W` is the base change of the flat 1-morphism `y : U → 𝒳` along `f`, hence flat
(Stacks 06PY), so its composite with a smooth presentation of `P` is flat, and the lift, which is
the value of that composite at the unit object, has flat structure morphism. -/
theorem exists_scheme_lift_flat_of_flatObject
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {W : BigFppfOver B S hS}
    (f : schemeStack.{u, w} B S hS W ⟶ 𝒳)
    (hsurj : IsSurjective B S hS f)
    (hflat : AlgebraicStacks.IsFlat B S hS f)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (y : 𝒳.val.val.obj) (hy : flatObject B S hS 𝒳.val y) :
    ∃ (T : B.Schemes) (m : T ⟶ (𝒳.val.val.p.obj y).left),
      Flat (B.inclusion.map m) ∧ LocallyOfFinitePresentation (B.inclusion.map m) ∧
        Surjective (B.inclusion.map m) ∧
        ∃ (x : Over W) (α : (CatFiberedInGroupoids.homFunctor f.hom).obj x ⟶ y),
          Flat (B.inclusion.map x.hom.left) ∧
          𝒳.val.val.p.IsHomLift
            (Over.homMk m rfl : (Over.mk (m ≫ (𝒳.val.val.p.obj y).hom) : BigFppfOver B S hS) ⟶
              𝒳.val.val.p.obj y) α := by
  classical
  -- The 2-Yoneda 1-morphism of `y`, out of the algebraic stack of the scheme below it; it is flat.
  let U := 𝒳.val.val.p.obj y
  let yU : 𝒳.val.val.p.Fiber U := Functor.Fiber.mk (a := y) rfl
  let Y : schemeFibredCategory B S hS U ⟶ 𝒳.val := objectMorphism B S hS 𝒳.val yU
  let b : schemeStack.{u, w} B S hS U ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom Y
  have hb : AlgebraicStacks.IsFlat B S hS b := hy
  -- The 2-fibre product `U ×_𝒳 W` and its two projections.
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
  have hPsnd : AlgebraicStacks.IsFlat B S hS P.snd :=
    AlgebraicStacks.isFlat_baseChange B S hS b f P.swap (Bicategory.isTwoFibreProduct_swap hP) hb
  -- A smooth surjective scheme presentation of the 2-fibre product, and the composite to `U`.
  obtain ⟨V, c, hcsm, hcsurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS P.pt
  have hcflat : AlgebraicStacks.IsFlat B S hS c := AlgebraicStacks.isFlat_of_isSmooth B S hS c hcsm
  have hwsurj : IsSurjective B S hS (c ≫ P.fst) :=
    isSurjective_comp B S hS c P.fst hcsurj hPsurj
  have hwflat : AlgebraicStacks.IsFlat B S hS (c ≫ P.fst) :=
    AlgebraicStacks.isFlat_comp B S hS c P.fst hcflat hPflat
  have hwlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS (c ≫ P.fst) :=
    AlgebraicStacks.isLocallyOfFinitePresentation_comp B S hS c P.fst
      (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS c hcsm) hPlfp
  obtain ⟨q, hqflat, hqlfp, hqsurj, ⟨e⟩⟩ :=
    exists_schemeMap_of_isSurjective_isFlat_isLfp B S hS (c ≫ P.fst) hwsurj hwflat hwlfp
  -- The composite to `W` is flat, hence comes from a flat morphism of the site.
  obtain ⟨q', hq', ⟨e'⟩⟩ := exists_schemeMap_of_isFlat B S hS (c ≫ P.snd)
    (AlgebraicStacks.isFlat_comp B S hS c P.snd hcflat hPsnd)
  refine ⟨V.left, q.left, hqflat, hqlfp, hqsurj, ?_⟩
  -- The lift of `y`, read off the filler of the 2-fibre product square.
  obtain ⟨α, hα⟩ := exists_isHomLift_twoCellFibreLift
    (schemeStack.{u, w} B S hS W).val.val.p 𝒳.val.val.p
    yU q f.hom.hom (c ≫ P.snd).hom.hom
    (Functor.TwoYoneda.liftBased 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids U yU)
    (Functor.TwoYoneda.chosenLift 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids U yU
      (Over.mk (𝟙 U))).φ
    ((Functor.TwoYoneda.chosenLift 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids U yU
      (Over.mk (𝟙 U))).isStronglyCartesian.toIsHomLift)
    ((Bicategory.whiskerLeft c P.iso.inv).hom.hom ≫
      (Bicategory.whiskerRight e.hom Y).hom)
  exact ⟨_, α, flat_obj_unit_of_iso_schemeFibredCategoryMap B S hS (c ≫ P.snd).hom q' e' hq',
    isHomLift_homMk_left B S hS 𝒳.val.val.p q α hα⟩

end AlgebraicGeometry.Stack

end
