module

public import StacksFrontier.AlgebraicGeometry.Duality.Compactification.ShriekPseudofunctor.DiagramChase

/-!
# Exceptional inverse image is a pseudofunctor (Tag 0ATY): the triple of compactifications

The data of the proof of [Stacks, Tag 0ATY]: for a `Stacks.Duality.CompositionData` `E` for `g`
and `h` and a compactification `t` of `X` over `Ȳ`, the choices
`Stacks.Duality.CompositionData.tripleLeft`, `tripleRight` and `tripleInner` for `(f, h ∘ g)`,
`(g ∘ f, h)` and `(f, g)`, the squares `A`, `B`, `C` and their base change maps, and the diagram
chase for the triple, `Stacks.Duality.CompositionData.tripleNat`, using [Stacks, Tag 0ATR] and
[Stacks, Tag 0ATQ].

## References

* [Stacks Project, Tag 0ATY](https://stacks.math.columbia.edu/tag/0ATY)
* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
* [Stacks Project, Tag 0AA0](https://stacks.math.columbia.edu/tag/0AA0)
* [Stacks Project, Tag 0ATQ](https://stacks.math.columbia.edu/tag/0ATQ)
* [Stacks Project, Tag 0ATR](https://stacks.math.columbia.edu/tag/0ATR)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe u

namespace Stacks.Duality

/-! ### The data of the proof: three compactifications stacked over each other -/

/-- Compactifications given by factorizations with equal proper parts are equal. -/
theorem _root_.AlgebraicGeometry.CompactificationOf.ofFactorization_congr {X B : Scheme.{u}}
    {h : X ⟶ B} (P : Scheme.{u}) (ι : X ⟶ P) {π π' : P ⟶ B} [IsOpenImmersion ι] [IsProper π]
    [IsProper π'] (w : ι ≫ π = h) (w' : ι ≫ π' = h) (e : π = π') :
    CompactificationOf.ofFactorization P ι π w = CompactificationOf.ofFactorization P ι π' w' := by
  subst e
  rfl

variable {S : Scheme.{u}} [IsNoetherian S]

/-- **The comparison of [Stacks, Tag 0AA0] between two compactifications given by factorizations
with equal proper parts** is the transport along the equality of the proper parts. -/
theorem compactificationUpperShriekIso_ofFactorization {Xf Yf : FTS S} (h : Xf ⟶ Yf)
    (P : Scheme.{u}) [IsNoetherian P] (ι : Xf.left ⟶ P) {π π' : P ⟶ Yf.left} [IsOpenImmersion ι]
    [IsProper π] [IsProper π'] (w : ι ≫ π = h.left) (w' : ι ≫ π' = h.left) (e : π = π') :
    (compactificationUpperShriekIso h (CompactificationOf.ofFactorization P ι π w)
        (CompactificationOf.ofFactorization P ι π' w')).hom =
      (whiskerLeft (ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel Yf.left))
        (whiskerRight (congrN e).hom (pb ι)) :
        compactificationUpperShriek h (CompactificationOf.ofFactorization P ι π w) ⟶
          compactificationUpperShriek h (CompactificationOf.ofFactorization P ι π' w')) := by
  subst e
  rw [compactificationUpperShriekIso_refl, congrN_self, Iso.refl_hom, Iso.refl_hom,
    Functor.whiskerRight_id']
  exact (Functor.whiskerLeft_id _).symm

/-- **An isomorphism of compactifications preserves the interior.** -/
theorem _root_.AlgebraicGeometry.CompactificationOf.preservesInterior_of_isIso {S : Scheme.{u}}
    {X : Over S} {j k : CompactificationOf X} (g : j ⟶ k)
    [IsIso (CompactificationOf.Hom.map g)] : CompactificationOf.PreservesInterior g := by
  have hinj : Function.Injective (CompactificationOf.Hom.map g).base :=
    (CompactificationOf.Hom.map g).isOpenEmbedding.injective
  have e := CompactificationOf.immersion_comp_homMap g
  ext x
  simp only [Set.mem_preimage, Set.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, hinj ((apply_eq e y).trans hy)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, (apply_eq e y).symm⟩

/-- **Changing the compactification of the first morphism in the isomorphism of
[Stacks, Tag 0ATX]** is composing with the comparison of [Stacks, Tag 0AA0]. -/
theorem upperShriekCompIsoAtModel_change_inner {X Y Z : FTS S} {f : X ⟶ Y} {g : Y ⟶ Z}
    (k : CompactificationOf (Over.mk (f ≫ g).left)) (j j' : CompactificationOf (Over.mk f.left))
    (i : CompactificationOf (Over.mk g.left)) :
    upperShriekCompIsoAtModel k j' i =
      upperShriekCompIsoAtModel k j i ≪≫ isoWhiskerLeft (upperShriekPlusAtModel i)
        (compactificationUpperShriekIso f j j') := by
  have hb : basePlusIsoAPI i i = Iso.refl _ := by
    show liftIsoOf _ _ _ (compactificationUpperShriekIso g i i) = _
    rw [compactificationUpperShriekIso_refl]
    exact liftIsoOf_refl _ _
  have n := upperShriekCompIsoAtModel_naturality k k j j' i i
  rw [compactificationUpperShriekIso_refl, hb, hcomp_refl_left, Iso.refl_trans] at n
  exact n

section Triple

variable {X Y Z T : FTS S} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ T}
  (E : CompositionData g h) (t : CompactificationOf (Over.mk (f.left ≫ E.top.immersion)))

namespace CompositionData

/-- **The choice for `f` and `h ∘ g`**: the compactification `Y ⟶ Ȳ ⟶ T` of `h ∘ g` of `E` and
the compactification `X ⟶ X̄ ⟶ Ȳ` given. -/
def tripleLeft : CompositionData f (g ≫ h) := ⟨E.outer, t⟩

include t in
/-- The compactification `X ⟶ X̄ ⟶ Ȳ ⟶ Z̄` of `(g ∘ f) ≫ i` for the compactification `Z ⟶ Z̄` of
`h` of `E`. -/
def tripleRightTop : CompactificationOf (Over.mk ((f ≫ g).left ≫ E.base.immersion)) :=
  CompactificationOf.ofFactorization t.space t.immersion (t.toBase ≫ E.top.toBase) (by
    rw [← Category.assoc, t.immersion_comp_toBase']
    change (f.left ≫ E.top.immersion) ≫ E.top.toBase = _
    rw [Category.assoc, E.top.immersion_comp_toBase']
    rfl)

/-- **The choice for `g ∘ f` and `h`**: the compactification `Z ⟶ Z̄ ⟶ T` of `h` of `E` and the
compactification `X ⟶ X̄ ⟶ Z̄`. -/
def tripleRight : CompositionData (f ≫ g) h := ⟨E.base, tripleRightTop E t⟩

/-- The morphism `V ⟶ W` from the inverse image `V` of `Z` in `X̄` to the inverse image `W` of `Z`
in `Ȳ`. -/
def tripleMap : (tripleRight E t).innerSpace ⟶ E.innerSpace :=
  pullback.lift (((tripleRight E t).innerFst : _ ⟶ t.space) ≫ t.toBase)
    (tripleRight E t).innerSnd ((Category.assoc _ _ _).trans pullback.condition)

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The composite `V ⟶ W ⟶ Ȳ` is `V ⟶ X̄ ⟶ Ȳ`. -/
@[reassoc (attr := simp)]
theorem tripleMap_fst : tripleMap E t ≫ E.innerFst =
    ((tripleRight E t).innerFst : _ ⟶ t.space) ≫ t.toBase :=
  pullback.lift_fst _ _ _

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The composite `V ⟶ W ⟶ Z` is the projection `V ⟶ Z`. -/
@[reassoc (attr := simp)]
theorem tripleMap_snd : tripleMap E t ≫ E.innerSnd = (tripleRight E t).innerSnd :=
  pullback.lift_snd _ _ _

omit [AlgebraicGeometry.IsNoetherian S] in
/-- **The square `B` of the source**: `V ⟶ X̄` over `W ⟶ Ȳ` is cartesian, as the upper half of
the cartesian square `V ⟶ X̄` over `Z ⟶ Z̄` whose lower half `W ⟶ Ȳ` over `Z ⟶ Z̄` is
cartesian. -/
theorem isPullback_tripleMap :
    IsPullback ((tripleRight E t).innerFst : _ ⟶ t.space) (tripleMap E t) t.toBase
      E.innerFst := by
  have s : IsPullback (tripleRight E t).innerFst (tripleMap E t ≫ E.innerSnd)
      (t.toBase ≫ E.top.toBase) E.baseImm := by
    rw [tripleMap_snd]
    exact (tripleRight E t).isPullback_innerFst
  exact IsPullback.of_bot s (tripleMap_fst E t).symm E.isPullback_innerFst

/-- The morphism `V ⟶ W` is proper, as a base change of the proper morphism `X̄ ⟶ Ȳ`. -/
instance isProper_tripleMap : IsProper (tripleMap E t) :=
  MorphismProperty.of_isPullback (P := @IsProper) (isPullback_tripleMap E t) t.property.2

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The composite `X ⟶ V ⟶ W` is `X ⟶ Y ⟶ W`. -/
theorem tripleRight_innerImmersion_tripleMap :
    (tripleRight E t).innerImmersion ≫ tripleMap E t = f.left ≫ E.innerImmersion := by
  apply pullback.hom_ext
  · rw [Category.assoc, tripleMap_fst, Category.assoc, innerImmersion_fst]
    exact ((tripleRight E t).innerImmersion_fst_assoc t.toBase).trans
      t.immersion_comp_toBase'
  · rw [Category.assoc, tripleMap_snd, Category.assoc, innerImmersion_snd]
    exact (congrArg (f.left ≫ ·) E.innerImmersion_snd).symm

include t in
/-- The compactification `X ⟶ V ⟶ W` of `X` over the compactification `W` of `g` of `E`. -/
def tripleInnerTop : CompactificationOf (Over.mk (f.left ≫ E.inner.immersion)) :=
  @CompactificationOf.ofFactorization X.left E.inner.space _ (tripleRight E t).innerSpace
    (tripleRight E t).innerImmersion (tripleMap E t) inferInstance (isProper_tripleMap E t)
    (tripleRight_innerImmersion_tripleMap E t)

/-- **The choice for `f` and `g`**: the compactification `Y ⟶ W ⟶ Z` of `g` determined by `E` and
the compactification `X ⟶ V ⟶ W`. -/
def tripleInner : CompositionData f g := ⟨E.inner, tripleInnerTop E t⟩

omit [AlgebraicGeometry.IsNoetherian S] in
/-- **The rectangle `A + B` of the source**: `U' ⟶ V ⟶ X̄` over `Y ⟶ W ⟶ Ȳ` is cartesian, `U'`
being the inverse image of `Y` in `V` for the choice for `f` and `g`. -/
theorem isPullback_tripleRow :
    IsPullback ((tripleInner E t).innerFst ≫ (tripleRight E t).innerFst : _ ⟶ t.space)
      (tripleInner E t).innerSnd t.toBase E.topImm := by
  have h := ((tripleInner E t).isPullback_innerFst).paste_horiz (isPullback_tripleMap E t)
  rwa [show (tripleInner E t).baseImm ≫ E.innerFst = E.topImm from E.innerImmersion_fst] at h

/-- The comparison `U' ⟶ U` of the inverse image of `Y` in `V` with the inverse image of `Y` in
`X̄`. -/
def tripleComparison : (tripleInner E t).innerSpace ⟶ (tripleLeft E t).innerSpace :=
  pullback.lift ((tripleInner E t).innerFst ≫ (tripleRight E t).innerFst : _ ⟶ t.space)
    (tripleInner E t).innerSnd (isPullback_tripleRow E t).w

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The composite `U' ⟶ U ⟶ X̄` is `U' ⟶ V ⟶ X̄`. -/
@[reassoc (attr := simp)]
theorem tripleComparison_fst : tripleComparison E t ≫ (tripleLeft E t).innerFst =
    ((tripleInner E t).innerFst ≫ (tripleRight E t).innerFst : _ ⟶ t.space) :=
  pullback.lift_fst _ _ _

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The composite `U' ⟶ U ⟶ Y` is the projection `U' ⟶ Y`. -/
@[reassoc (attr := simp)]
theorem tripleComparison_snd : tripleComparison E t ≫ (tripleLeft E t).innerSnd =
    (tripleInner E t).innerSnd :=
  pullback.lift_snd _ _ _

/-- The comparison `U' ⟶ U` is an isomorphism, both being inverse images of `Y` in `X̄`. -/
instance isIso_tripleComparison : IsIso (tripleComparison E t) := by
  have : tripleComparison E t = (isPullback_tripleRow E t).isoPullback.hom := by
    apply pullback.hom_ext
    · rw [tripleComparison_fst]
      exact (IsPullback.isoPullback_hom_fst (isPullback_tripleRow E t)).symm
    · rw [tripleComparison_snd]
      exact (IsPullback.isoPullback_hom_snd (isPullback_tripleRow E t)).symm
  rw [this]
  exact Iso.isIso_hom _

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The composite `X ⟶ U' ⟶ U` is the immersion `X ⟶ U`. -/
theorem innerImmersion_tripleComparison :
    (tripleInner E t).innerImmersion ≫ tripleComparison E t = (tripleLeft E t).innerImmersion := by
  apply pullback.hom_ext
  · rw [Category.assoc, tripleComparison_fst]
    exact ((tripleInner E t).innerImmersion_fst_assoc
      ((tripleRight E t).innerFst : _ ⟶ t.space)).trans
      ((tripleRight E t).innerImmersion_fst.trans (tripleLeft E t).innerImmersion_fst.symm)
  · rw [Category.assoc, tripleComparison_snd, innerImmersion_snd, innerImmersion_snd]

/-- The comparison `U' ⟶ U` as a morphism of compactifications of `f`. -/
def tripleComparisonHom : (tripleInner E t).inner ⟶ (tripleLeft E t).inner :=
  ObjectProperty.homMk (StructuredArrow.homMk
    (Over.homMk (tripleComparison E t) (tripleComparison_snd E t))
    (Over.OverMorphism.ext (innerImmersion_tripleComparison E t)))

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The underlying morphism of `tripleComparisonHom` is `tripleComparison`. -/
@[simp] theorem tripleComparisonHom_map :
    CompactificationOf.Hom.map (tripleComparisonHom E t) = tripleComparison E t := rfl

/-- The underlying morphism of `tripleComparisonHom` is an isomorphism. -/
instance : IsIso (CompactificationOf.Hom.map (tripleComparisonHom E t)) :=
  isIso_tripleComparison E t

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The comparison `U' ⟶ U` preserves the interior, being an isomorphism. -/
theorem preservesInterior_tripleComparisonHom :
    CompactificationOf.PreservesInterior (tripleComparisonHom E t) :=
  CompactificationOf.preservesInterior_of_isIso _

/-! ### The chase for the triple -/

/-- `U' ⟶ V ⟶ X̄` is an open immersion. -/
instance isOpenImmersion_tripleRow :
    IsOpenImmersion ((tripleInner E t).innerFst ≫ (tripleRight E t).innerFst : _ ⟶ t.space) := by
  have : @IsOpenImmersion (tripleInner E t).top.space t.space (tripleRight E t).innerFst :=
    instIsOpenImmersionInnerFst (tripleRight E t)
  exact IsOpenImmersion.comp _ _

omit [AlgebraicGeometry.IsNoetherian S] in
/-- `X ⟶ U' ⟶ V ⟶ X̄` is the open immersion of `X` into `X̄`. -/
theorem tripleRow_immersion :
    (tripleInner E t).innerImmersion ≫
      ((tripleInner E t).innerFst ≫ (tripleRight E t).innerFst : _ ⟶ t.space) =
        (tripleLeft E t).topImm :=
  ((tripleInner E t).innerImmersion_fst_assoc ((tripleRight E t).innerFst : _ ⟶ t.space)).trans
    (tripleRight E t).innerImmersion_fst

/-- `(X ⟶ X̄)^* = (X ⟶ U')^* ∘ (U' ⟶ X̄)^*`. -/
def tripleRowRestrict : pb (tripleLeft E t).topImm ≅
    pb ((tripleInner E t).innerFst ≫ (tripleRight E t).innerFst : _ ⟶ t.space) ⋙
      pb (tripleInner E t).innerImmersion :=
  pbCongrN (tripleRow_immersion E t).symm ≪≫ (pbCompN _ _).symm

/-- The base change map of [Stacks, Tag 0AA6] for the rectangle `A + B`. -/
abbrev tripleRowBaseChange :
    tw t.toBase ⋙ pb ((tripleInner E t).innerFst ≫ (tripleRight E t).innerFst : _ ⟶ t.space) ⟶
      pb E.topImm ⋙ tw (tripleInner E t).innerSnd :=
  @bcO _ _ _ _ _ _ _ _ _ _ _ _ (isOpenImmersion_tripleRow E t) _ (isPullback_tripleRow E t)

/-- **The comparison of [Stacks, Tag 0ATX] for `f` and `h ∘ g` read on the rectangle `A + B`**:
the construction of `Stacks.Duality.CompositionData.compMap` for the choice of `f` and `h ∘ g`,
with the inverse image `U` of `Y` in `X̄` replaced by the inverse image `U'` of `Y` in `V`. -/
def tripleRowMap : tw ((tripleLeft E t).top.toBase ≫ (tripleLeft E t).base.toBase) ⋙
      pb (tripleLeft E t).topImm ⟶
    tw (tripleLeft E t).base.toBase ⋙ pb (tripleLeft E t).baseImm ⋙
      tw (tripleInner E t).innerSnd ⋙ pb (tripleInner E t).innerImmersion :=
  chainMap (compN (tripleLeft E t).top.toBase (tripleLeft E t).base.toBase).hom
    (tripleRowRestrict E t).hom (tripleRowBaseChange E t)

/-- `tripleRowMap` unfolded as a chain of its three constituent transformations. -/
theorem tripleRowMap_eq : tripleRowMap E t =
    chainMap (compN (tripleLeft E t).top.toBase (tripleLeft E t).base.toBase).hom
      (tripleRowRestrict E t).hom (tripleRowBaseChange E t) := rfl

/-- The component of `tripleRowMap` at `K` as a composite of three morphisms. -/
theorem tripleRowMap_app (K : quasiCoherentDerivedCategory T.left) :
    (tripleRowMap E t).app K =
      (pb (tripleLeft E t).topImm).map
          ((compN (tripleLeft E t).top.toBase (tripleLeft E t).base.toBase).hom.app K) ≫
        (tripleRowRestrict E t).hom.app ((tw (tripleLeft E t).top.toBase).obj
          ((tw (tripleLeft E t).base.toBase).obj K)) ≫
          (pb (tripleInner E t).innerImmersion).map
            ((tripleRowBaseChange E t).app ((tw (tripleLeft E t).base.toBase).obj K)) :=
  (congrArg (fun φ => NatTrans.app φ K) (tripleRowMap_eq E t)).trans (chainMap_app _ _ _ K)

omit [AlgebraicGeometry.IsNoetherian S] in
/-- **The square `A` of the source**, `U' ⟶ V` over `Y ⟶ W`, with its right edge spelled as
`Stacks.Duality.CompositionData.tripleMap`. -/
theorem isPullback_tripleInner :
    IsPullback (tripleInner E t).innerFst (tripleInner E t).innerSnd (tripleMap E t)
      E.innerImmersion :=
  (tripleInner E t).isPullback_innerFst

/-- The base change map of the square `A`. -/
abbrev tripleInnerBaseChange :
    tw (tripleMap E t) ⋙ pb (tripleInner E t).innerFst ⟶
      pb E.innerImmersion ⋙ tw (tripleInner E t).innerSnd :=
  @bcO _ _ _ _ _ _ _ _ _ _ _ _ (instIsOpenImmersionInnerFst (tripleInner E t)) _
    (isPullback_tripleInner E t)

/-- The base change map of the square `B`. -/
abbrev tripleMapBaseChange :
    tw t.toBase ⋙ pb ((tripleRight E t).innerFst : _ ⟶ t.space) ⟶
      pb E.innerFst ⋙ tw (tripleMap E t) :=
  @bcO _ _ _ _ _ _ _ _ _ _ _ _ (instIsOpenImmersionInnerFst (tripleRight E t))
    (instIsOpenImmersionInnerFst E) (isPullback_tripleMap E t)

/-- The base change map of the stack of `B` over `C`. -/
abbrev tripleStackBaseChange :
    tw (t.toBase ≫ E.top.toBase) ⋙ pb ((tripleRight E t).innerFst : _ ⟶ t.space) ⟶
      pb E.baseImm ⋙ tw (tripleMap E t ≫ E.innerSnd) :=
  @bcO _ _ _ _ _ _ _ _ _ _ _ _ (instIsOpenImmersionInnerFst (tripleRight E t)) _
    ((isPullback_tripleMap E t).paste_vert E.isPullback_innerFst)

/-- The base change map of the choice for `g ∘ f` and `h` is that of the stack of `B` over `C`,
up to the transport along `V ⟶ Z = V ⟶ W ⟶ Z`. -/
theorem tripleStack_congr :
    (tripleRight E t).baseChange =
      whiskerRight (congrN (rfl : t.toBase ≫ E.top.toBase = t.toBase ≫ E.top.toBase)).hom
          (pb ((tripleRight E t).innerFst : _ ⟶ t.space)) ≫
        tripleStackBaseChange E t ≫
          whiskerLeft (pb E.baseImm) (congrN (tripleMap_snd E t).symm).inv :=
  @bcN_congr_vert _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (instIsOpenImmersionInnerFst (tripleRight E t)) _ (tripleMap_snd E t).symm rfl
      (tripleRight E t).isPullback_innerFst
      ((isPullback_tripleMap E t).paste_vert E.isPullback_innerFst)

/-- **The comparisons of [Stacks, Tag 0ATX] for the twisted inverse image are coherent** for
`X̄ ⟶ Ȳ ⟶ Z̄ ⟶ T`: the hypothesis `H1` of `Stacks.Duality.tripleChaseNat`. -/
theorem tripleCocycle :
    (compN t.toBase (E.top.toBase ≫ E.base.toBase)).hom ≫
        whiskerRight (compN E.top.toBase E.base.toBase).hom (tw t.toBase) =
      (compN (t.toBase ≫ E.top.toBase) E.base.toBase).hom ≫
        whiskerLeft (tw E.base.toBase) (compN t.toBase E.top.toBase).hom :=
  NatTrans.ext (funext fun K => (compN_cocycleR t.toBase E.top.toBase E.base.toBase K).trans
    ((congrArg (· ≫ _) (congrN_assoc_app t.toBase E.top.toBase E.base.toBase K)).trans
      (Category.id_comp _)))

/-- **[Stacks, Tag 0ATQ] for the stack of `B` over `C`**, through the identification of the left
edge `V ⟶ Z` with `V ⟶ W ⟶ Z`: the hypothesis `H2` of `Stacks.Duality.tripleChaseNat`. -/
theorem tripleStackNat :
    (tripleRight E t).baseChange ≫ whiskerLeft (pb E.baseImm)
        ((congrN (tripleMap_snd E t).symm).hom ≫ (compN (tripleMap E t) E.innerSnd).hom) =
      whiskerRight (compN t.toBase E.top.toBase).hom
          (pb ((tripleRight E t).innerFst : _ ⟶ t.space)) ≫
        whiskerLeft (tw E.top.toBase) (tripleMapBaseChange E t) ≫
          whiskerRight E.baseChange (tw (tripleMap E t)) :=
  stackNat (compN t.toBase E.top.toBase) (compN (tripleMap E t) E.innerSnd)
    (congrN (tripleMap_snd E t).symm) (congrN rfl) (congrN_self _) E.baseChange
    (tripleRight E t).baseChange (tripleStackBaseChange E t) (tripleMapBaseChange E t)
    (tripleStack_congr E t)
    (@bcN_vcomp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (instIsOpenImmersionInnerFst (tripleRight E t)) (instIsOpenImmersionInnerFst E) _
      (isPullback_tripleMap E t) E.isPullback_innerFst)

/-- The cocycle identity of derived pullback for `X ⟶ U' ⟶ V ⟶ X̄`, as an identity of
transformations. -/
theorem tripleRowCocycle :
    (tripleRowRestrict E t).hom ≫
        whiskerRight (pbCompN (tripleInner E t).innerFst
          ((tripleRight E t).innerFst : _ ⟶ t.space)).inv (pb (tripleInner E t).innerImmersion) =
      (tripleRight E t).restrictCompIso.hom ≫
        whiskerLeft (pb ((tripleRight E t).innerFst : _ ⟶ t.space))
          (tripleInner E t).restrictCompIso.hom :=
  pbCompN_cocycle_nat (tripleInner E t).innerImmersion (tripleInner E t).innerFst
    ((tripleRight E t).innerFst : _ ⟶ t.space) (tripleInner E t).topImm
    (tripleLeft E t).topImm (tripleInner E t).innerImmersion_fst.symm
    (tripleRight E t).innerImmersion_fst.symm (tripleRow_immersion E t).symm

/-- **[Stacks, Tag 0ATR] for the row of `A` and `B`**: the hypothesis `H3` of
`Stacks.Duality.tripleChaseNat`. -/
theorem tripleRowNat :
    whiskerLeft (tw t.toBase) (tripleRowRestrict E t).hom ≫
        whiskerRight (tripleRowBaseChange E t) (pb (tripleInner E t).innerImmersion) ≫
          whiskerRight (whiskerRight E.restrictCompIso.hom (tw (tripleInner E t).innerSnd))
            (pb (tripleInner E t).innerImmersion) =
      whiskerLeft (tw t.toBase) (tripleRight E t).restrictCompIso.hom ≫
        whiskerRight (tripleMapBaseChange E t) (pb (tripleRight E t).innerImmersion) ≫
          whiskerLeft (pb E.innerFst ⋙ tw (tripleMap E t)) (tripleInner E t).restrictCompIso.hom ≫
            whiskerLeft (pb E.innerFst)
              (whiskerRight (tripleInnerBaseChange E t) (pb (tripleInner E t).innerImmersion)) := by
  have := isOpenImmersion_tripleRow E t
  exact rowNat (tripleRowRestrict E t) (tripleRight E t).restrictCompIso
    (tripleInner E t).restrictCompIso (pbCongrN rfl) (pbCongrN_self _)
    (pbCongrN E.innerImmersion_fst.symm)
    (pbCompN (tripleInner E t).innerFst ((tripleRight E t).innerFst : _ ⟶ t.space))
    (pbCompN E.innerImmersion E.innerFst) (tripleRowBaseChange E t)
    (@bcO _ _ _ _ _ _ _ _ _ _ _ _ (isOpenImmersion_tripleRow E t) _
      ((isPullback_tripleInner E t).paste_horiz (isPullback_tripleMap E t)))
    (tripleInnerBaseChange E t) (tripleMapBaseChange E t)
    (@bcN_congr_horiz _ _ _ _ _ _ _ _ _ _ _ _ _ _ (isOpenImmersion_tripleRow E t)
      (isOpenImmersion_tripleRow E t) _ _ rfl E.innerImmersion_fst.symm
      ((isPullback_tripleInner E t).paste_horiz (isPullback_tripleMap E t))
      (isPullback_tripleRow E t))
    (@bcN_hcomp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (instIsOpenImmersionInnerFst (tripleInner E t))
      (instIsOpenImmersionInnerFst (tripleRight E t))
      inferInstance (instIsOpenImmersionInnerFst E)
      (isPullback_tripleInner E t) (isPullback_tripleMap E t))
    (tripleRowCocycle E t)

/-- **The diagram chase of the proof of [Stacks, Tag 0ATY] for the triple**, as an identity of
transformations of functors out of `D_QCoh(𝒪_T)`: the comparison of [Stacks, Tag 0ATX] for `f`
and `h ∘ g`, read on the rectangle `A + B`, followed by the one for `g` and `h`, is the comparison
for `g ∘ f` and `h` followed by the one for `f` and `g`. -/
theorem tripleNat :
    tripleRowMap E t ≫
        whiskerRight E.compMap
          (tw (tripleInner E t).innerSnd ⋙ pb (tripleInner E t).innerImmersion) =
      (tripleRight E t).compMap ≫ whiskerLeft (tw E.base.toBase ⋙ pb E.baseImm)
        (whiskerRight (congrN (tripleMap_snd E t).symm).hom (pb (tripleRight E t).innerImmersion) ≫
          (tripleInner E t).compMap) :=
  tripleChaseNat (compN (tripleLeft E t).top.toBase (tripleLeft E t).base.toBase)
    (compN E.top.toBase E.base.toBase)
    (compN (tripleRight E t).top.toBase (tripleRight E t).base.toBase)
    (compN t.toBase E.top.toBase)
    (compN (tripleInner E t).top.toBase (tripleInner E t).base.toBase)
    (congrN (tripleMap_snd E t).symm)
    (tripleRowRestrict E t) E.restrictCompIso (tripleRight E t).restrictCompIso
    (tripleInner E t).restrictCompIso
    (tripleRowBaseChange E t) E.baseChange (tripleRight E t).baseChange
    (tripleInner E t).baseChange (tripleMapBaseChange E t)
    (tripleCocycle E t) (tripleStackNat E t) (tripleRowNat E t)

end CompositionData

end Triple

end Stacks.Duality

end
