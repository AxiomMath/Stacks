module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingCanonicalSquare
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingDiagonal

/-!
# The 2-cell of the canonical square of Stacks 0CMR

`AlgebraicGeometry.Stack.IsLimitPreserving` and
`AlgebraicGeometry.Stack.IsFullyFaithfulOnAffineLimits` quantify over the data `(T, H, η)` of the
square of Stacks 0CMR and pin all three down. `T` and the stagewise 2-cell are built in
`StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingCanonicalSquare`; this file supplies the two
remaining pieces, `H` and `η`, and packages all of the pinned data together.

The key identity is that the colimit of `AlgebraicGeometry.Stack.fiberDiagramMap` is compatible
with the two restriction cocones of Stacks 004A, which is exactly
`AlgebraicGeometry.Stack.splitFiberMap_naturality` read through the universal property of the
colimit. With that, `η` is the stagewise 2-cell
`AlgebraicGeometry.Stack.splitEvaluationIso` whiskered into the colimit descent.

## Main definitions

* `AlgebraicGeometry.Stack.canonicalTwoCell`: the 2-cell `η` of the square of Stacks 0CMR.

## Main results

* `AlgebraicGeometry.Stack.colimMap_fiberDiagramMap_desc`: the colimit of the componentwise maps
  of split fibres intertwines the two restriction cocones.
* `AlgebraicGeometry.Stack.canonicalTwoCell_app_ι`: the third pinning condition of Stacks 0CMR —
  on every colimit generator `η` is the base-change comparison of the fibred 1-morphism.
* `AlgebraicGeometry.Stack.exists_canonicalSquareData`: the whole of the pinned data `(T, H, η)`
  of Stacks 0CMR exists for every 1-morphism, so both
  `AlgebraicGeometry.Stack.IsLimitPreserving` and
  `AlgebraicGeometry.Stack.IsFullyFaithfulOnAffineLimits` reduce to a property of the resulting
  square alone.

## References

* [Stacks Project, Tag 0CMR](https://stacks.math.columbia.edu/tag/0CMR)
* [Stacks Project, Tag 004A](https://stacks.math.columbia.edu/tag/004A)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u v w uX vX

attribute [local implicit_reducible] Bicategory.InducedBicategory Functor.Fiber
  Functor.Fiber.fiberInclusion Functor.SplitFiber.restrict Deformation.Artin.fiberCocone
  Deformation.Artin.fiberDiagram Functor.splitPresheaf Cat.asSmallFunctor

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : CatFiberedInGroupoids.{u, vX, u + 1, uX} (BigFppfOver B S hS)}
  {I : Type v} [Category.{w} I]

/-- **The colimit of `AlgebraicGeometry.Stack.fiberDiagramMap` intertwines the two restriction
cocones of Stacks 004A.** Descending the stage fibres of `𝒳` to the cone point and then pushing
them to `𝒴` is the same as pushing each stage to `𝒴` and then descending. -/
lemma colimMap_fiberDiagramMap_desc (f : 𝒳 ⟶ 𝒴) (E : I ⥤ BigFppfOver B S hS) (d : Cone E) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    colimit.desc (Deformation.Artin.fiberDiagram 𝒳.val.p E)
          (Deformation.Artin.fiberCocone 𝒳.val.p E d) ≫
        (AsSmall.down ⋙ splitFiberMap B S hS f d.pt ⋙ AsSmall.up).toCatHom =
      colimMap (fiberDiagramMap B S hS f E) ≫
        colimit.desc (Deformation.Artin.fiberDiagram 𝒴.val.p E)
          (Deformation.Artin.fiberCocone 𝒴.val.p E d) := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  refine colimit.hom_ext fun ⟨i⟩ => ?_
  rw [← Category.assoc, colimit.ι_desc, ← Category.assoc, ι_colimMap, Category.assoc,
    colimit.ι_desc, fiberDiagramMap_app]
  exact Cat.Hom.ext (congrArg (fun G => AsSmall.down ⋙ G ⋙ AsSmall.up)
    (splitFiberMap_naturality B S hS f (d.π.app i)))

/-- The same identity read as an equality of functors into the fibre at the cone point: this is
the target of the stagewise 2-cell `AlgebraicGeometry.Stack.splitEvaluationIso` whiskered into the
colimit descent. -/
lemma colimitComparison_comp_splitFiberMap (f : 𝒳 ⟶ 𝒴) (E : I ⥤ BigFppfOver B S hS)
    (d : Cone E) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    (colimit.desc (Deformation.Artin.fiberDiagram 𝒳.val.p E)
          (Deformation.Artin.fiberCocone 𝒳.val.p E d)).toFunctor ⋙ AsSmall.down ⋙
        splitFiberMap B S hS f d.pt ⋙ Deformation.Artin.evaluateSplitFiber 𝒴.val.p d.pt =
      (colimMap (fiberDiagramMap B S hS f E)).toFunctor ⋙
        Deformation.Artin.colimitComparison 𝒴.val.p E d :=
  have : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  have : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  congrArg (fun F => F.toFunctor ⋙ AsSmall.down ⋙
      Deformation.Artin.evaluateSplitFiber 𝒴.val.p d.pt)
    (colimMap_fiberDiagramMap_desc B S hS f E d)

/-- **The 2-cell `η` of the square of Stacks 0CMR.** Comparing the colimit of the stage fibres of
`𝒳` with the fibre at the cone point and then pushing to `𝒴` is, up to the base-change comparison
of the fibred 1-morphism, the same as pushing the colimit to `𝒴` and then comparing. -/
noncomputable def canonicalTwoCell (f : 𝒳 ⟶ 𝒴) (E : I ⥤ BigFppfOver B S hS) (d : Cone E) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙
        Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt ≅
      (colimMap (fiberDiagramMap B S hS f E)).toFunctor ⋙
        Deformation.Artin.colimitComparison 𝒴.val.p E d :=
  letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  Functor.isoWhiskerLeft
      ((colimit.desc (Deformation.Artin.fiberDiagram 𝒳.val.p E)
        (Deformation.Artin.fiberCocone 𝒳.val.p E d)).toFunctor ⋙ AsSmall.down)
      (splitEvaluationIso B S hS f d.pt) ≪≫
    eqToIso (colimitComparison_comp_splitFiberMap B S hS f E d)

/-- A component of a whiskered natural transformation, postcomposed with an `eqToHom` correcting
the codomain functor, is heterogeneously equal to the component of the unwhiskered
transformation. -/
lemma heq_whiskerLeft_app_comp_eqToHom {C D E : Type*} [Category C] [Category D] [Category E]
    (P : C ⥤ D) {F G : D ⥤ E} (σ : F ⟶ G) {K : C ⥤ E} (hK : P ⋙ G = K)
    {a : C} {b : D} (hab : P.obj a = b) :
    HEq ((Functor.whiskerLeft P σ ≫ eqToHom hK).app a) (σ.app b) := by
  subst hK
  subst hab
  simp

/-- **The 2-cell `η` of the square of Stacks 0CMR, in the lifted universe** in which the square
of `AlgebraicGeometry.Stack.IsLimitPreserving` is stated. -/
noncomputable def canonicalTwoCellUp (f : 𝒳 ⟶ 𝒴) (E : I ⥤ BigFppfOver B S hS) (d : Cone E) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙
        AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}) ⋙
        AsSmall.down.{vX, uX, max v w vX (u + 1) uX u} ⋙
        Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt ⋙
          AsSmall.up.{vX, uX, max v w vX (u + 1) uX u} ≅
      (colimMap (fiberDiagramMap B S hS f E)).toFunctor ⋙
        Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙
          AsSmall.up.{vX, uX, max v w vX (u + 1) uX u} :=
  letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  Functor.isoWhiskerRight (canonicalTwoCell B S hS f E d)
    AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}

/-- **The third pinning condition of Stacks 0CMR.** On every colimit generator the 2-cell `η` is
the canonical base-change comparison of the fibred 1-morphism underlying `f`. -/
lemma canonicalTwoCellUp_app_ι (f : 𝒳 ⟶ 𝒴) (E : I ⥤ BigFppfOver B S hS) (d : Cone E) (i : I)
    (x : 𝒳.val.p.SplitFiber (E.obj i)) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    HEq
      (AsSmall.down.map
        (((canonicalTwoCellUp B S hS f E d).app
          ((colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E)
              (op i)).toFunctor.obj
            (AsSmall.up.{vX, max (u + 1) uX, max v w}.obj x))).hom))
      ((isFibredOneMorphism B S hS f).mapPullbackFiberIso x.obj (d.π.app i ≫ x.hom)).inv := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  have hobj : AsSmall.down.{vX, max (u + 1) uX, max v w}.obj
      ((colimit.desc (Deformation.Artin.fiberDiagram 𝒳.val.p E)
          (Deformation.Artin.fiberCocone 𝒳.val.p E d)).toFunctor.obj
        ((colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E) (op i)).toFunctor.obj
          (AsSmall.up.{vX, max (u + 1) uX, max v w}.obj x))) =
      (Functor.SplitFiber.restrict 𝒳.val.p (d.π.app i)).obj x :=
    congrArg AsSmall.down.{vX, max (u + 1) uX, max v w}.obj
      (Functor.congr_obj
        (congrArg Cat.Hom.toFunctor
          (colimit.ι_desc (Deformation.Artin.fiberCocone 𝒳.val.p E d) (op i)))
        (AsSmall.up.{vX, max (u + 1) uX, max v w}.obj x))
  exact heq_whiskerLeft_app_comp_eqToHom
    ((colimit.desc (Deformation.Artin.fiberDiagram 𝒳.val.p E)
        (Deformation.Artin.fiberCocone 𝒳.val.p E d)).toFunctor ⋙ AsSmall.down)
    (splitEvaluationIso B S hS f d.pt).hom
    (colimitComparison_comp_splitFiberMap B S hS f E d) hobj

/-- **The canonical square of Stacks 0CMR** attached to a 1-morphism and a cone, with all three
pieces of data `T`, `H`, `η` the pinned ones. -/
noncomputable def canonicalSquare (f : 𝒳 ⟶ 𝒴) (E : I ⥤ BigFppfOver B S hS) (d : Cone E) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    Bicategory.TwoCommSq
      (AsSmall.down.{vX, uX, max v w vX (u + 1) uX u} ⋙
        Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt ⋙
        AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}).toCatHom
      (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙
        AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}).toCatHom :=
  letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  { pt := (colimit (Deformation.Artin.fiberDiagram 𝒳.val.p E) : Cat)
    fst := (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙
      AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}).toCatHom
    snd := (colimMap (fiberDiagramMap B S hS f E)).toFunctor.toCatHom
    iso := Cat.Hom.isoMk (canonicalTwoCellUp B S hS f E d) }

/-- **Stacks 0CMR for a 1-morphism whose canonical square is 2-cartesian.** All of the pinned data
of the square being available, limit preservation is exactly the 2-cartesian property of
`AlgebraicGeometry.Stack.canonicalSquare`. -/
theorem isLimitPreserving_of_canonicalSquare (f : 𝒳 ⟶ 𝒴)
    (h : ∀ (I : Type v) [Category.{w} I] [IsCofiltered I]
      (D : I ⥤ BigAffineFppf B S hS) (c : Cone D),
      IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c) →
      Nonempty (Bicategory.IsTwoFibreProduct
        (canonicalSquare.{u, v, w, uX, vX} B S hS f (D ⋙ BigAffineFppf.inclusion B S hS)
          ((BigAffineFppf.inclusion B S hS).mapCone c)))) :
    IsLimitPreserving.{u, v, w, uX, vX} B S hS f := by
  intro I _ _ D c hc
  exact ⟨_, _, _, fiberDiagramMap_app B S hS f _, rfl,
    canonicalTwoCellUp_app_ι B S hS f _ _, h I D c hc⟩

/-- **Stacks 0CMW, condition (2) for a 1-morphism whose canonical square has a fully faithful
comparison.** All of the pinned data of the square being available, the condition is exactly full
faithfulness of the comparison out of `AlgebraicGeometry.Stack.canonicalSquare`. -/
theorem isFullyFaithfulOnAffineLimits_of_canonicalSquare (f : 𝒳 ⟶ 𝒴)
    (h : ∀ (I : Type v) [Category.{w} I] [IsCofiltered I]
      (D : I ⥤ BigAffineFppf B S hS) (c : Cone D),
      IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c) →
      (Cat.toCategoricalPullbackFunctor
          (canonicalSquare.{u, v, w, uX, vX} B S hS f (D ⋙ BigAffineFppf.inclusion B S hS)
            ((BigAffineFppf.inclusion B S hS).mapCone c))).Full ∧
        (Cat.toCategoricalPullbackFunctor
          (canonicalSquare.{u, v, w, uX, vX} B S hS f (D ⋙ BigAffineFppf.inclusion B S hS)
            ((BigAffineFppf.inclusion B S hS).mapCone c))).Faithful) :
    IsFullyFaithfulOnAffineLimits.{u, v, w, uX, vX} B S hS f := by
  intro I _ _ D c hc
  exact ⟨_, _, _, fiberDiagramMap_app B S hS f _, rfl,
    canonicalTwoCellUp_app_ι B S hS f _ _, (h I D c hc).1, (h I D c hc).2⟩

end AlgebraicGeometry.Stack

end
