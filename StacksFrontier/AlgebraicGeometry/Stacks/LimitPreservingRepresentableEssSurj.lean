module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingCanonicalCell
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingCanonicalDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LimitPreservingOnObjects
public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCat
public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCatStagewiseEquivalence

/-!
# Essential surjectivity of the comparison of Stacks 0CMR from the descent datum of Stacks 06CU

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf category of a
scheme `S`. Essential surjectivity of the comparison functor

`colim 𝒳_{Uᵢ} ⟶ 𝒳_U ×_{𝒴_U} colim 𝒴_{Uᵢ}`

out of the canonical square of Stacks 0CMR is the step of the proof of Stacks 0CMV that the source
records as "since we are assuming (2) we know that it is essentially surjective". This file carries
it, out of the descent datum of Stacks 06CU read at a cone in the big fppf category: the input, the
two components of the witnessing isomorphism, and the coherence between them, which is where the
commuting square of Stacks 06CU is consumed.

## Main definitions

* `AlgebraicGeometry.Stack.RelativeDescentObj`: descent of objects relative to `f`, which is the
  condition of Stacks 06CU read at a cone in the big fppf category rather than at a cone of
  affines.
* `AlgebraicGeometry.Stack.descentComparison`: the cartesian comparison that Stacks 06CU consumes,
  assembled from an object of the explicit 2-fibre product.
* `AlgebraicGeometry.Stack.descentFstIso` and `AlgebraicGeometry.Stack.descentSndIso`: the two
  components, at the first and the second projection of the canonical square, of the isomorphism
  that identifies the image of the descended object with the given object of the 2-fibre product.

## Main results

* `AlgebraicGeometry.Stack.exists_stage_datum_of_categoricalPullback`: the second component of an
  object of the explicit 2-fibre product is the image of a pair of the split model of Stacks 004A
  at a stage.
* `AlgebraicGeometry.Stack.colimitComparison_obj_ι_up`: the colimit comparison sends that image to
  the chosen pullback of the pair to the cone point.
* `AlgebraicGeometry.Stack.colimitComparison_map_ι_up`: on a morphism of the split model at a
  stage the colimit comparison is base change along the cone's projection.
* `AlgebraicGeometry.Stack.relativeDescentObj_of_isLimitPreservingOnObjects`: Stacks 06CU gives
  `AlgebraicGeometry.Stack.RelativeDescentObj`.
* `AlgebraicGeometry.Stack.isStronglyCartesian_descentComparison`: the comparison is cartesian over
  the cone's projection, so Stacks 06CU applies to it.
* `AlgebraicGeometry.Stack.essSurj_toCategoricalPullbackFunctor_canonicalSquare`: the comparison
  out of `AlgebraicGeometry.Stack.canonicalSquare` is essentially surjective.

## Implementation notes

An object of the explicit 2-fibre product is a triple `(x, Y, φ)` with `x` in the fibre of `𝒳`
over the limit `U`, `Y` in `colim 𝒴_{Uᵢ}` and `φ` an isomorphism between the images of the two in
`𝒴_U`. An object of a filtered colimit in `Cat` comes from a stage
(`CategoryTheory.Cat.exists_stage_obj_of_colimit`), so `Y` is the image of a pair `(y, g)` of the
split model at some stage `i`, and the comparison sends that pair to the chosen pullback of `y`
along `U ⟶ Uᵢ ⟶ base y`. Composing `φ` with the chosen cartesian lift therefore turns the triple
into exactly the datum Stacks 06CU consumes, which is
`AlgebraicGeometry.Stack.descentComparison`.

Stacks 06CU returns a later stage `i'`, an object `x'` of `𝒳` there, and the two comparisons `δ`
(cartesian, from an object over `U` isomorphic to `x` by `β`) and `γ'` (cartesian, from the image
of `x'` to `y`), together with a commuting square relating them. The object of the colimit that
essential surjectivity asks for is the image of `(x', id)` at the stage `i'`. Its first component
under the comparison is the chosen pullback of `x'` to the cone point, which `δ` and `β` identify
with `x` — this is `AlgebraicGeometry.Stack.descentFstIso`. Its second component is the image of
`(f(x'), id)`, which `γ'` identifies with the restriction of `(y, g)` to the stage `i'`, and
`CategoryTheory.Limits.colimit.w` identifies that with `Y` — this is
`AlgebraicGeometry.Stack.descentSndIso`.

That the two components are the two halves of a single isomorphism of the explicit 2-fibre product
is the coherence condition relating them through the 2-cell of the canonical square. Both of its
sides are morphisms out of the chosen pullback of `x'` to the cone point, which is cartesian, so
they agree as soon as they agree after the cartesian projection of the chosen pullback of `(y, g)`;
after that projection the commuting square returned by Stacks 06CU is exactly the identity needed,
once the comparison `δ` has been inverted (the fibres are groupoids) and the 2-cell of the square
has been read at the stage with `AlgebraicGeometry.Stack.canonicalTwoCellUp_app_ι_eq`. The
coherence is a declaration of its own, since the identity it proves has to be assembled from the
two components' definitions and is far longer than either.

## References

* [Stacks Project, Tag 0CMV](https://stacks.math.columbia.edu/tag/0CMV)
* [Stacks Project, Tag 0CMR](https://stacks.math.columbia.edu/tag/0CMR)
* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
* [Stacks Project, Tag 0CMS](https://stacks.math.columbia.edu/tag/0CMS)
* [Stacks Project, Tag 004A](https://stacks.math.columbia.edu/tag/004A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u v w uX vX uC vC wC uD vD

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion
  Functor.SplitFiber.restrict Bicategory.InducedBicategory
  AsSmall.up AsSmall.down

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : CatFiberedInGroupoids.{u, vX, u + 1, uX} (BigFppfOver B S hS)}
  {I : Type v} [Category.{w} I]

/-- **The stage datum underlying an object of the explicit 2-fibre product.** An object of
`𝒳_U ×_{𝒴_U} colim 𝒴_{Uᵢ}` is, after replacing it by an equal one, given by an object `x` of `𝒳`
over the cone point, a pair `ys` of the split model of `𝒴` at a stage `i`, and an isomorphism in
`𝒴_U` from the image of `x` to the chosen pullback of `ys` to the cone point. -/
theorem exists_stage_datum_of_categoricalPullback (f : 𝒳 ⟶ 𝒴) (E : I ⥤ BigFppfOver B S hS)
    (d : Cone E)
    (W : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
      Limits.CategoricalPullback
        (AsSmall.down.{vX, uX, max v w vX (u + 1) uX u} ⋙
          Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt ⋙
          AsSmall.up.{vX, uX, max v w vX (u + 1) uX u})
        (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙
          AsSmall.up.{vX, uX, max v w vX (u + 1) uX u})) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    ∃ (i : I) (ys : 𝒴.val.p.SplitFiber (E.obj i)),
      (Limits.colimit.ι (Deformation.Artin.fiberDiagram 𝒴.val.p E)
        (op i)).toFunctor.obj (AsSmall.up.{vX, max (u + 1) uX, max v w}.obj ys) = W.snd := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  obtain ⟨j, b, hb⟩ := Cat.exists_stage_obj_of_colimit.{max (u + 1) uX vX, v, w}
    (Deformation.Artin.fiberDiagram 𝒴.val.p E) W.snd
  exact ⟨j.unop, AsSmall.down.{vX, max (u + 1) uX, max v w}.obj b, hb⟩

/-- **The comparison of the stage datum with the fibre at the cone point.** The colimit comparison
of `𝒴` sends the image of a pair `(y, g)` of the split model at the stage `i` to the chosen
pullback of `y` along `U ⟶ Uᵢ ⟶ base y`. -/
theorem colimitComparison_obj_ι_up (𝒵 : CatFiberedInGroupoids.{u, vX, u + 1, uX}
      (BigFppfOver B S hS)) (E : I ⥤ BigFppfOver B S hS) (d : Cone E) (i : I)
    (o : letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
      𝒵.val.p.SplitFiber (E.obj i)) :
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    (Deformation.Artin.colimitComparison 𝒵.val.p E d).obj
        ((Limits.colimit.ι (Deformation.Artin.fiberDiagram 𝒵.val.p E)
          (op i)).toFunctor.obj (AsSmall.up.{vX, max (u + 1) uX, max v w}.obj o)) =
      𝒵.val.p.pullbackFiber o.obj (d.π.app i ≫ o.hom) :=
  let : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
  Functor.congr_obj (Deformation.Artin.colimitComparison_ι 𝒵.val.p E d i)
    (AsSmall.up.{vX, max (u + 1) uX, max v w}.obj o)

/-- **The comparison of the stage datum with the fibre at the cone point, on morphisms.** On a
morphism of the split model at the stage `i` the colimit comparison is base change along the
cone's projection, read through the identifications of
`AlgebraicGeometry.Stack.colimitComparison_obj_ι_up` at the two ends. -/
theorem colimitComparison_map_ι_up (𝒵 : CatFiberedInGroupoids.{u, vX, u + 1, uX}
      (BigFppfOver B S hS)) (E : I ⥤ BigFppfOver B S hS) (d : Cone E) (i : I)
    (o o' : letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
      𝒵.val.p.SplitFiber (E.obj i))
    (α : letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
      o ⟶ o') :
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    (Deformation.Artin.colimitComparison 𝒵.val.p E d).map
        ((Limits.colimit.ι (Deformation.Artin.fiberDiagram 𝒵.val.p E)
          (op i)).toFunctor.map (AsSmall.up.{vX, max (u + 1) uX, max v w}.map α)) =
      eqToHom (colimitComparison_obj_ι_up B S hS 𝒵 E d i o) ≫
        Functor.SplitFiber.restrictHom (d.π.app i) (Functor.SplitFiber.toFiberHom α) ≫
        eqToHom (colimitComparison_obj_ι_up B S hS 𝒵 E d i o').symm :=
  let : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
  Functor.congr_hom (Deformation.Artin.colimitComparison_ι 𝒵.val.p E d i)
    (AsSmall.up.{vX, max (u + 1) uX, max v w}.map α)

/-- **The second projection of the canonical square at the image of a stage.** The colimit of the
stagewise maps of split fibres sends the image of a pair `(x, g)` of the split model of `𝒳` to the
image of `(f(x), g)`, whose chosen pullback to the cone point the comparison of `𝒴` computes. -/
theorem colimitComparison_colimMap_obj_ι_up [IsCofiltered I] (f : 𝒳 ⟶ 𝒴)
    (E : I ⥤ BigFppfOver B S hS)
    (d : Cone E) (i : I)
    (o : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      𝒳.val.p.SplitFiber (E.obj i)) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    (Deformation.Artin.colimitComparison 𝒴.val.p E d).obj
        ((Limits.colimMap (fiberDiagramMap B S hS f E)).toFunctor.obj
          ((Limits.colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E)
            (op i)).toFunctor.obj (AsSmall.up.{vX, max (u + 1) uX, max v w}.obj o))) =
      𝒴.val.p.pullbackFiber
        ((Functor.fiberFunctorOfCompEq
          (CatFiberedInGroupoids.homFunctor_comp_p f) o.base).obj o.obj)
        (d.π.app i ≫ o.hom) :=
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  (congrArg (Deformation.Artin.colimitComparison 𝒴.val.p E d).obj
      (Cat.colimMap_ι_obj.{max vX (u + 1) uX u, v, w} (fiberDiagramMap B S hS f E) (op i)
        (AsSmall.up.{vX, max (u + 1) uX, max v w}.obj o))).trans
    (colimitComparison_obj_ι_up B S hS 𝒴 E d i
      ((splitFiberMap B S hS f (E.obj i)).obj o))

/-- **The 2-cell of the canonical square of Stacks 0CMR at the image of a stage, transported.**
`AlgebraicGeometry.Stack.canonicalTwoCellUp_app_ι` pins the 2-cell at a colimit generator to the
base-change comparison of the fibred 1-morphism, but only up to the identifications of the two
corners, so it is stated as a heterogeneous equality. This is the same fact as an equation,
with those identifications written out; it is the form the coherence of the isomorphism
witnessing essential surjectivity consumes. -/
theorem canonicalTwoCellUp_app_ι_eq [IsCofiltered I] (f : 𝒳 ⟶ 𝒴)
    (E : I ⥤ BigFppfOver B S hS) (d : Cone E) (i : I)
    (o : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      𝒳.val.p.SplitFiber (E.obj i)) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    AsSmall.down.map (((canonicalTwoCellUp B S hS f E d).app
          ((Limits.colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E)
            (op i)).toFunctor.obj
            (AsSmall.up.{vX, max (u + 1) uX, max v w}.obj o))).hom) ≫
        eqToHom (colimitComparison_colimMap_obj_ι_up B S hS f E d i o) =
      eqToHom (congrArg (Functor.fiberFunctorOfCompEq
            (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt).obj
          (colimitComparison_obj_ι_up B S hS 𝒳 E d i o)) ≫
        ((isFibredOneMorphism B S hS f).mapPullbackFiberIso o.obj (d.π.app i ≫ o.hom)).inv :=
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  Cat.transport_hom_of_heq _ _ (canonicalTwoCellUp_app_ι B S hS f E d i o)

/-- **Descent of objects along a cofiltered limit, relative to a 1-morphism.** This is the datum
Stacks 06CU provides, read at a cone in the big fppf category rather than at a cone of affines:
every object of `𝒳` over the cone point, with a cartesian comparison of its image to an object of
`𝒴` at a stage, descends to a later stage compatibly with that comparison. -/
def RelativeDescentObj (f : 𝒳 ⟶ 𝒴) (E : I ⥤ BigFppfOver B S hS) (d : Cone E) : Prop :=
  letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  ∀ (i : I) (y : 𝒴.val.p.Fiber (E.obj i)) (x : 𝒳.val.p.Fiber d.pt)
    (γ : (CatFiberedInGroupoids.homFunctor f).obj x.1 ⟶ y.1),
    𝒴.val.p.IsStronglyCartesian (d.π.app i) γ →
    ∃ (i' : I) (j : i' ⟶ i) (x' : 𝒳.val.p.Fiber (E.obj i')) (xU : 𝒳.val.p.Fiber d.pt)
      (δ : xU.1 ⟶ x'.1) (β : xU.1 ⟶ x.1)
      (γ' : (CatFiberedInGroupoids.homFunctor f).obj x'.1 ⟶ y.1),
      𝒳.val.p.IsStronglyCartesian (d.π.app i') δ ∧
        𝒳.val.p.IsHomLift (𝟙 d.pt) β ∧ IsIso β ∧
        𝒴.val.p.IsStronglyCartesian (E.map j) γ' ∧
        (CatFiberedInGroupoids.homFunctor f).map δ ≫ γ' =
          (CatFiberedInGroupoids.homFunctor f).map β ≫ γ

/-- **Stacks 06CU gives `AlgebraicGeometry.Stack.RelativeDescentObj` at every cone of affines
whose image in schemes is limiting.** The two conditions are the same statement: the inclusion of
the affines into the big fppf category takes the cone's projections to the cone's projections. -/
theorem relativeDescentObj_of_isLimitPreservingOnObjects [IsCofiltered I] (f : 𝒳 ⟶ 𝒴)
    (D : I ⥤ BigAffineFppf B S hS) (c : Cone D)
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c))
    (hlim : BigFppfOver.IsLimitPreservingOnObjects.{u, v, w, vX, uX} B S hS 𝒳 𝒴 f) :
    RelativeDescentObj B S hS f (D ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c) :=
  fun i y x γ hγ => hlim I D c hc i y x γ hγ

section Descent

variable [IsCofiltered I] (f : 𝒳 ⟶ 𝒴) (E : I ⥤ BigFppfOver B S hS) (d : Cone E)

/-- **The object of `𝒳` over the cone point that an object of the explicit 2-fibre product
names**, namely the first component read down the universe lift. -/
abbrev pullbackObjFst
    (W : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
      Limits.CategoricalPullback
        (AsSmall.down.{vX, uX, max v w vX (u + 1) uX u} ⋙
          Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt ⋙
          AsSmall.up.{vX, uX, max v w vX (u + 1) uX u})
        (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙
          AsSmall.up.{vX, uX, max v w vX (u + 1) uX u})) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    𝒳.val.p.Fiber d.pt :=
  AsSmall.down.{vX, uX, max v w vX (u + 1) uX u}.obj W.fst

/-- **The cartesian comparison that Stacks 06CU consumes**, assembled from an object of the
explicit 2-fibre product: the isomorphism of the 2-fibre product followed by the chosen cartesian
lift of the cone's projection. -/
noncomputable abbrev descentComparison (i : I)
    (ys : letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
      𝒴.val.p.SplitFiber (E.obj i))
    (x : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      𝒳.val.p.Fiber d.pt)
    (e : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
      (Functor.fiberFunctorOfCompEq
          (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt).obj x ≅
        𝒴.val.p.pullbackFiber ys.obj (d.π.app i ≫ ys.hom)) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    (CatFiberedInGroupoids.homFunctor f).obj x.1 ⟶ ys.toFiber.1 :=
  letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  Functor.Fiber.fiberInclusion.map e.hom ≫
    Functor.pullbackFiberProj ys.obj ys.hom (d.π.app i)

omit [IsCofiltered I] in
/-- `AlgebraicGeometry.Stack.descentComparison` is cartesian over the cone's projection, which is
what makes it the datum Stacks 06CU consumes. -/
theorem isStronglyCartesian_descentComparison (i : I)
    (ys : letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
      𝒴.val.p.SplitFiber (E.obj i))
    (x : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      𝒳.val.p.Fiber d.pt)
    (e : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
      (Functor.fiberFunctorOfCompEq
          (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt).obj x ≅
        𝒴.val.p.pullbackFiber ys.obj (d.π.app i ≫ ys.hom)) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    𝒴.val.p.IsStronglyCartesian (d.π.app i)
      (descentComparison B S hS f E d i ys x e) := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  have h0 : 𝒴.val.p.IsHomLift (𝟙 d.pt ≫ d.π.app i)
      (descentComparison B S hS f E d i ys x e) := inferInstance
  rw [Category.id_comp] at h0
  let := h0
  exact 𝒴.2.isStronglyCartesian_homLift (d.π.app i) _

/-- **The first component of the isomorphism witnessing essential surjectivity.** The object of
`colim 𝒳_{Uᵢ}` that the descent datum of Stacks 06CU produces has, for its image under the first
projection of the canonical square, the chosen pullback of `x'` to the cone point, which `δ`
identifies with `xU` and `β` with `x`. -/
noncomputable def descentFstIso (i' : I)
    (x' : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      𝒳.val.p.Fiber (E.obj i'))
    (xU x : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      𝒳.val.p.Fiber d.pt)
    (δ : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      xU.1 ⟶ x'.1)
    (β : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      xU.1 ⟶ x.1)
    (hδ : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      𝒳.val.p.IsStronglyCartesian (d.π.app i') δ)
    (hβ : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      𝒳.val.p.IsHomLift (𝟙 d.pt) β)
    (hβiso : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      IsIso β) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}.obj
        ((Deformation.Artin.colimitComparison 𝒳.val.p E d).obj
          ((Limits.colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E)
            (op i')).toFunctor.obj (AsSmall.up.{vX, max (u + 1) uX, max v w}.obj
              ⟨E.obj i', x', 𝟙 _⟩))) ≅
      AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}.obj x :=
  letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  letI := hδ.toIsHomLift
  letI := hβiso
  haveI : IsIso (Functor.toPullbackFiber 𝒳.val.p xU x' (d.π.app i') δ) :=
    (𝒳.2.fiber_isGroupoid d.pt).all_isIso _
  eqToIso (congrArg AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}.obj
      (colimitComparison_obj_ι_up B S hS 𝒳 E d i' ⟨E.obj i', x', 𝟙 _⟩)) ≪≫
    AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}.mapIso
      (eqToIso (congrArg (𝒳.val.p.pullbackFiber x') (Category.comp_id (d.π.app i'))) ≪≫
        (asIso (Functor.toPullbackFiber 𝒳.val.p xU x' (d.π.app i') δ)).symm ≪≫
        Functor.Fiber.isoMk (asIso β) hβ)

/-- **The second component of the isomorphism witnessing essential surjectivity.** The cartesian
comparison `γ'` of Stacks 06CU identifies the image of `(x', id)` under the stagewise map of the
canonical square with the restriction of the stage datum `ys` to the later stage, and the colimit
relation identifies the two images in `colim 𝒴_{Uᵢ}`. -/
noncomputable def descentSndIso (i i' : I) (j : i' ⟶ i)
    (ys : letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
      𝒴.val.p.SplitFiber (E.obj i))
    (x' : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      𝒳.val.p.Fiber (E.obj i'))
    (γ' : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
      (CatFiberedInGroupoids.homFunctor f).obj x'.1 ⟶ ys.toFiber.1)
    (hγ' : letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
      letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      𝒴.val.p.IsStronglyCartesian (E.map j) γ') :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    (Limits.colimMap (fiberDiagramMap B S hS f E)).toFunctor.obj
        ((Limits.colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E)
          (op i')).toFunctor.obj (AsSmall.up.{vX, max (u + 1) uX, max v w}.obj
            ⟨E.obj i', x', 𝟙 _⟩)) ≅
      (Limits.colimit.ι (Deformation.Artin.fiberDiagram 𝒴.val.p E)
        (op i)).toFunctor.obj (AsSmall.up.{vX, max (u + 1) uX, max v w}.obj ys) := by
  letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  letI := hγ'.toIsHomLift
  letI σfib : 𝒴.val.p.pullbackFiber
        ((Functor.fiberFunctorOfCompEq
          (CatFiberedInGroupoids.homFunctor_comp_p f) (E.obj i')).obj x') (𝟙 (E.obj i')) ⟶
      𝒴.val.p.pullbackFiber ys.obj (E.map j ≫ ys.hom) :=
    (Functor.pullbackFiberIdIso
      ((Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f)
        (E.obj i')).obj x')).hom ≫
    Functor.toPullbackFiber 𝒴.val.p _ ys.obj (E.map j ≫ ys.hom) (γ' ≫ ys.proj)
  haveI : IsIso σfib := (𝒴.2.fiber_isGroupoid (E.obj i')).all_isIso _
  letI σiso : (splitFiberMap B S hS f (E.obj i')).obj
        (⟨E.obj i', x', 𝟙 (E.obj i')⟩ : 𝒳.val.p.SplitFiber (E.obj i')) ≅
      (Functor.SplitFiber.restrict 𝒴.val.p (E.map j)).obj ys :=
    { hom := Functor.SplitFiber.ofFiberHom σfib
      inv := Functor.SplitFiber.ofFiberHom (inv σfib)
      hom_inv_id := Functor.SplitFiber.toFiberHom_injective (by simp)
      inv_hom_id := Functor.SplitFiber.toFiberHom_injective (by simp) }
  exact eqToIso (Cat.colimMap_ι_obj.{max vX (u + 1) uX u, v, w}
      (fiberDiagramMap B S hS f E) (op i')
      (AsSmall.up.{vX, max (u + 1) uX, max v w}.obj ⟨E.obj i', x', 𝟙 _⟩)) ≪≫
    (Limits.colimit.ι (Deformation.Artin.fiberDiagram 𝒴.val.p E)
      (op i')).toFunctor.mapIso (AsSmall.up.{vX, max (u + 1) uX, max v w}.mapIso σiso) ≪≫
    eqToIso (Functor.congr_obj (congrArg Cat.Hom.toFunctor
      (Limits.colimit.w (Deformation.Artin.fiberDiagram 𝒴.val.p E) (op j)))
      (AsSmall.up.{vX, max (u + 1) uX, max v w}.obj ys))

attribute [local implicit_reducible] Deformation.Artin.fiberDiagram Deformation.Artin.fiberCocone
  Functor.splitPresheaf Cat.asSmallFunctor canonicalSquare splitPresheafMap fiberDiagramMap

/-- The universe lift and its inverse are strictly mutually inverse on morphisms. Stated so that
it can be rewritten with at `implicit` transparency, where `CategoryTheory.Functor.comp_map`
cannot see through the `Cat.Hom` wrapper of the legs of the canonical square. -/
private lemma asSmall_down_up_map {C : Type uC} [Category.{vC} C] {a b : C} (g : a ⟶ b) :
    AsSmall.down.map (AsSmall.up.{vC, uC, wC}.map g) = g := rfl

/-- A functor conjugated by the universe lift, read on morphisms down the lift. -/
private lemma down_sandwich_map {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (F : C ⥤ D) {a b : AsSmall.{wC} C} (g : a ⟶ b) :
    AsSmall.down.map ((AsSmall.down.{vC, uC, wC} ⋙ F ⋙ AsSmall.up.{vD, uD, wC}).map g) =
      F.map (AsSmall.down.map g) := rfl

/-- A functor followed by the universe lift, read on morphisms down the lift. -/
private lemma down_comp_up_map {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (F : D ⥤ C) {a b : D} (g : a ⟶ b) :
    AsSmall.down.map ((F ⋙ AsSmall.up.{vC, uC, wC}).map g) = F.map g := rfl

set_option maxHeartbeats 1600000 in
/-- **The two components of the isomorphism witnessing essential surjectivity are compatible with
the 2-cell of the canonical square.** This is the coherence condition that makes
`AlgebraicGeometry.Stack.descentFstIso` and `AlgebraicGeometry.Stack.descentSndIso` the two
components of a single isomorphism of the explicit 2-fibre product, and it is where the commuting
square of Stacks 06CU is consumed: both sides are morphisms out of the image of `x'`, so they
agree as soon as they agree after the cartesian projection of the chosen pullback of `ys`, and
after that projection the commuting square is exactly the identity needed. -/
private theorem descentIso_w (i : I)
    (ys : letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
      𝒴.val.p.SplitFiber (E.obj i))
    (x : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      𝒳.val.p.Fiber d.pt)
    (Wi : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
      (AsSmall.down.{vX, uX, max v w vX (u + 1) uX u} ⋙
            Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt ⋙
            AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}).toCatHom.toFunctor.obj
          (AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}.obj x) ≅
        (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙
            AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}).toCatHom.toFunctor.obj
          ((Limits.colimit.ι (Deformation.Artin.fiberDiagram 𝒴.val.p E)
            (op i)).toFunctor.obj (AsSmall.up.{vX, max (u + 1) uX, max v w}.obj ys)))
    (i' : I) (j : i' ⟶ i)
    (x' : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      𝒳.val.p.Fiber (E.obj i'))
    (xU : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      𝒳.val.p.Fiber d.pt)
    (δ : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      xU.1 ⟶ x'.1)
    (β : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      xU.1 ⟶ x.1)
    (γ' : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
      (CatFiberedInGroupoids.homFunctor f).obj x'.1 ⟶ ys.toFiber.1)
    (hδ : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      𝒳.val.p.IsStronglyCartesian (d.π.app i') δ)
    (hβ : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      𝒳.val.p.IsHomLift (𝟙 d.pt) β)
    (hβiso : IsIso β)
    (hγ' : letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
      𝒴.val.p.IsStronglyCartesian (E.map j) γ')
    (hsq : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
      (CatFiberedInGroupoids.homFunctor f).map δ ≫ γ' =
        (CatFiberedInGroupoids.homFunctor f).map β ≫
          descentComparison B S hS f E d i ys x
            (AsSmall.down.{vX, uX, max v w vX (u + 1) uX u}.mapIso Wi ≪≫
              eqToIso (colimitComparison_obj_ι_up B S hS 𝒴 E d i ys))) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    (AsSmall.down.{vX, uX, max v w vX (u + 1) uX u} ⋙
            Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt ⋙
            AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}).toCatHom.toFunctor.map
          (descentFstIso B S hS E d i' x' xU x δ β hδ hβ hβiso).hom ≫ Wi.hom =
      ((Cat.toCategoricalPullbackFunctor (canonicalSquare B S hS f E d)).obj
            ((Limits.colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E)
              (op i')).toFunctor.obj
              (AsSmall.up.{vX, max (u + 1) uX, max v w}.obj ⟨E.obj i', x', 𝟙 _⟩))).iso.hom ≫
        (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙
            AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}).toCatHom.toFunctor.map
          (descentSndIso B S hS f E i i' j ys x' γ' hγ').hom := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  have hT : AsSmall.down.{vX, uX, max v w vX (u + 1) uX u}.map
        ((((Cat.toCategoricalPullbackFunctor (canonicalSquare B S hS f E d)).obj
          ((Limits.colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E) (op i')).toFunctor.obj
            (AsSmall.up.{vX, max (u + 1) uX, max v w}.obj
              (⟨E.obj i', x', 𝟙 (unop (E.op.obj (op i')))⟩ :
                𝒳.val.p.SplitFiber (unop (E.op.obj (op i'))))))).iso.hom)) =
      (eqToHom (congrArg (Functor.fiberFunctorOfCompEq
            (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt).obj
          (colimitComparison_obj_ι_up B S hS 𝒳 E d i' ⟨E.obj i', x', 𝟙 _⟩)) ≫
        ((isFibredOneMorphism B S hS f).mapPullbackFiberIso x'
          (d.π.app i' ≫ 𝟙 (E.obj i'))).inv) ≫
        eqToHom (colimitComparison_colimMap_obj_ι_up B S hS f E d i'
          ⟨E.obj i', x', 𝟙 _⟩).symm :=
    (comp_eqToHom_iff _ _ _).mp
      (canonicalTwoCellUp_app_ι_eq B S hS f E d i' ⟨E.obj i', x', 𝟙 _⟩)
  refine asSmall_down_map_injective ?_
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Functor.toCatHom]
  rw [down_sandwich_map, down_comp_up_map, hT]
  refine (cancel_mono (eqToHom (colimitComparison_obj_ι_up B S hS 𝒴 E d i ys))).mp ?_
  refine Functor.Fiber.hom_ext ?_
  refine Functor.IsStronglyCartesian.ext 𝒴.val.p (d.π.app i ≫ ys.hom)
    (Functor.IsPreFibered.pullbackMap ys.obj.2 (d.π.app i ≫ ys.hom)) (𝟙 d.pt) ?_
  have hsq3 := (reassoc_of% hsq) (Functor.IsPreFibered.pullbackMap ys.obj.2 ys.hom)
  simp only [descentFstIso, descentSndIso, eqToIso.hom, Functor.mapIso, Iso.trans,
    Functor.map_comp, Category.assoc, asSmall_down_up_map, eqToHom_map, eqToHom_trans,
    eqToHom_trans_assoc,
    Functor.Fiber.fiberInclusion_map_isoMk_hom, asIso_hom, asIso_inv, Iso.symm_hom,
    Functor.fiberInclusion_map_fiberFunctorOfCompEq_map,
    Functor.pullbackFiberProj_fac] at hsq3 ⊢
  let := hδ.toIsHomLift
  let : IsIso (𝒳.val.p.toPullbackFiber xU x' (d.π.app i') δ) :=
    (𝒳.2.fiber_isGroupoid d.pt).all_isIso _
  have hinv : Functor.Fiber.fiberInclusion.map
        (inv (𝒳.val.p.toPullbackFiber xU x' (d.π.app i') δ)) ≫ δ =
      Functor.IsPreFibered.pullbackMap x'.2 (d.π.app i') := by
    have h0 : Functor.Fiber.fiberInclusion.map
            (inv (𝒳.val.p.toPullbackFiber xU x' (d.π.app i') δ)) ≫
          (Functor.Fiber.fiberInclusion.map
              (𝒳.val.p.toPullbackFiber xU x' (d.π.app i') δ) ≫
            Functor.IsPreFibered.pullbackMap x'.2 (d.π.app i')) =
        Functor.IsPreFibered.pullbackMap x'.2 (d.π.app i') := by
      rw [← Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id]
      simp
    rwa [Functor.toPullbackFiber_fac] at h0
  let := hγ'.toIsHomLift
  have hinvF := congrArg (CatFiberedInGroupoids.homFunctor f).map hinv
  rw [Functor.map_comp] at hinvF
  rw [← hsq3, reassoc_of% hinvF, colimitComparison_map_ι_up B S hS 𝒴 E d i']
  simp only [Functor.map_comp, Category.assoc, eqToHom_map, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp, Functor.SplitFiber.toFiberHom_ofFiberHom]
  have hfac := Functor.SplitFiber.restrictHom_fac (p := 𝒴.val.p) (d.π.app i')
    (o := (splitFiberMap B S hS f (E.obj i')).obj ⟨E.obj i', x', 𝟙 _⟩)
    (o' := (Functor.SplitFiber.restrict 𝒴.val.p (E.map j)).obj ys)
    ((Functor.pullbackFiberIdIso ((Functor.fiberFunctorOfCompEq
        (CatFiberedInGroupoids.homFunctor_comp_p f) (E.obj i')).obj x')).hom ≫
      𝒴.val.p.toPullbackFiber ((Functor.fiberFunctorOfCompEq
        (CatFiberedInGroupoids.homFunctor_comp_p f) (E.obj i')).obj x') ys.obj
        (E.map j ≫ ys.hom) (γ' ≫ ys.proj))
  dsimp only [Functor.SplitFiber.restrict_obj_base, Functor.SplitFiber.restrict_obj_obj,
    Functor.SplitFiber.restrict_obj_hom] at hfac
  rw [Functor.eqToHom_comp_pullbackMap ys.obj
      (show d.π.app i' ≫ E.map j ≫ ys.hom = d.π.app i ≫ ys.hom by
        rw [← Category.assoc, d.w j]) _, hfac]
  simp only [Functor.SplitFiber.proj, Functor.SplitFiber.restrict_obj_obj,
    Functor.SplitFiber.restrict_obj_hom, splitFiberMap,
    Functor.map_comp, Category.assoc, Functor.toPullbackFiber_fac,
    Functor.pullbackFiberIdIso_hom_fac, Functor.pullbackFiberProj_fac_assoc,
    Functor.IsFibredOneMorphism.mapPullbackFiberIso_inv_fac_assoc]
  rw [← Functor.eqToHom_comp_pullbackMap x' (Category.comp_id (d.π.app i'))
    (congrArg (fun g => (𝒳.val.p.pullbackFiber x' g).1) (Category.comp_id (d.π.app i')))]
  simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc]

/-- **Essential surjectivity of the comparison out of the canonical square of Stacks 0CMR**, for a
1-morphism whose objects descend along the cofiltered limit. This is the step of the proof of
Stacks 0CMV that the source records as "since we are assuming (2) we know that it is essentially
surjective". -/
theorem essSurj_toCategoricalPullbackFunctor_canonicalSquare
    (hd : RelativeDescentObj B S hS f E d) :
    (Cat.toCategoricalPullbackFunctor
      (canonicalSquare.{u, v, w, uX, vX} B S hS f E d)).EssSurj := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  refine ⟨fun W => ?_⟩
  obtain ⟨i, ys, hys⟩ := exists_stage_datum_of_categoricalPullback B S hS f E d W
  obtain ⟨Wf, Ws, Wi⟩ := W
  subst hys
  obtain ⟨x, rfl⟩ : ∃ x : 𝒳.val.p.Fiber d.pt,
      AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}.obj x = Wf :=
    ⟨AsSmall.down.{vX, uX, max v w vX (u + 1) uX u}.obj Wf, rfl⟩
  let e := AsSmall.down.{vX, uX, max v w vX (u + 1) uX u}.mapIso Wi ≪≫
    eqToIso (colimitComparison_obj_ι_up B S hS 𝒴 E d i ys)
  obtain ⟨i', j, x', xU, δ, β, γ', hδ, hβ, hβiso, hγ', hsq⟩ :=
    hd i ys.toFiber x (descentComparison B S hS f E d i ys x e)
      (isStronglyCartesian_descentComparison B S hS f E d i ys x e)
  exact ⟨_, ⟨Limits.CategoricalPullback.mkIso
    (descentFstIso B S hS E d i' x' xU x δ β hδ hβ hβiso)
    (descentSndIso B S hS f E i i' j ys x' γ' hγ')
    (descentIso_w B S hS f E d i ys x Wi i' j x' xU δ β γ' hδ hβ hβiso hγ' hsq)⟩⟩

end Descent

end AlgebraicGeometry.Stack

end
