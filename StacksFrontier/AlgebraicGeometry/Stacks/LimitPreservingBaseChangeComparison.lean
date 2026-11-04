module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingBaseChangeObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingCanonicalCell
public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCatTwoFibreProductEquivalence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverSplitFibre

/-!
# The split fibre of a base change is the 2-fibre product of the split fibres (Stacks 0CMT)

Stacks 0CMT asserts that the base change `p' : 𝒳 ×_𝒴 𝒵 ⟶ 𝒵` of a limit preserving 1-morphism is
limit preserving. By `StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingCanonicalCell` that is
the 2-cartesian property of `AlgebraicGeometry.Stack.canonicalSquare` for `p'`, whose left
vertical functor has `colim (𝒳 ×_𝒴 𝒵)_{Uᵢ}` as its source. The source's own proof replaces that
colimit by `colim 𝒳_{Uᵢ} ×_{colim 𝒴_{Uᵢ}} colim 𝒵_{Uᵢ}`, citing without proof that filtered
colimits of categories commute with 2-fibre products; that statement is
`CategoryTheory.Cat.isEquivalence_colimitTwoFibreProductComparison`, and to use it one needs the
*diagram* of split fibres of the base change compared stagewise with the stagewise 2-fibre
product `CategoryTheory.Cat.twoFibreProductDiagram` of the diagrams of split fibres.

This file builds that comparison at a single stage and proves it strictly natural in the base.
The mathematical content — that reading an object or a morphism of the split fibre of the
2-fibre product componentwise is well defined and commutes with restriction — is
`StacksFrontier.CategoryTheory.TwoFibreProduct.OverSplitFibre`; here it is assembled into a functor.

## Main definitions

* `AlgebraicGeometry.Stack.splitFiberTwoFibreProductComparisonApp`: the comparison
  `(𝒳 ×_𝒴 𝒵)'_V ⥤ 𝒳'_V ×_{𝒴'_V} 𝒵'_V` of split fibres over one object `V` of the base.
* `AlgebraicGeometry.Stack.splitFiberTwoFibreProductComparisonStage`: the same comparison with
  its target the stage of `CategoryTheory.Cat.twoFibreProductDiagram`, that is, after the
  universe lift.
* `AlgebraicGeometry.Stack.splitFiberTwoFibreProductComparison`: the comparison `Φ` of
  *diagrams* over the index category of a cone, which is what
  `CategoryTheory.Limits.colimMap` consumes.

## Main results

* `AlgebraicGeometry.Stack.splitFiberTwoFibreProductComparisonApp_naturality`: the comparison
  commutes with the strict restriction functors of Stacks 004A *on the nose*. Strictness is what
  the colimit needs: `CategoryTheory.Limits.colimMap` takes a natural transformation of diagrams,
  and the composite of `CategoryTheory.Functor.SplitFiber.fiberEquiv` with
  `CategoryTheory.TwoFibreProductOver.fiberEquiv` is natural only up to isomorphism, which is why
  the comparison is defined directly instead.

## Implementation notes

Restriction along `g : V' ⟶ V` is `h ↦ g ≫ h` on both sides, so the two composites in the
naturality square agree on objects and on morphisms; the equality of functors is therefore proved
with `CategoryTheory.Functor.ext`, and the transports it produces drop out by
`CategoryTheory.Cat.eq_eqToHom_conj`, whose two equalities are taken as arguments so that it
applies where the endpoints agree only definitionally.

Functoriality of the comparison is conjugation by isomorphisms and is proved in term mode with
`AlgebraicGeometry.Stack.isoConj_id` and `AlgebraicGeometry.Stack.isoConj_comp`: `simp` on the
goals left by `CategoryTheory.Limits.CategoricalPullback.Hom.ext` runs into the chosen pullback
`CategoryTheory.Functor.SplitFiber.toFiber` under two spellings.

## References

* [Stacks Project, Tag 0CMT](https://stacks.math.columbia.edu/tag/0CMT)
* [Stacks Project, Tag 0CMR](https://stacks.math.columbia.edu/tag/0CMR)
* [Stacks Project, Tag 02XI](https://stacks.math.columbia.edu/tag/02XI)
* [Stacks Project, Tag 004A](https://stacks.math.columbia.edu/tag/004A)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u v w

attribute [local implicit_reducible] Bicategory.InducedBicategory Functor.Fiber
  Functor.Fiber.fiberInclusion Functor.SplitFiber.restrict Functor.fiberMap
  Deformation.Artin.fiberDiagram Functor.splitPresheaf Cat.asSmallFunctor

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w}
    (BigFppfOver B S hS))
  (p : 𝒳 ⟶ 𝒴) (q : 𝒵 ⟶ 𝒴)

/-- Conjugating an identity by an isomorphism gives the identity. -/
lemma isoConj_id {C : Type*} [Category C] {a b : C} (e : a ≅ b) :
    e.inv ≫ 𝟙 a ≫ e.hom = 𝟙 b := by
  simp

/-- Conjugating a composite by three isomorphisms is the composite of the conjugates. -/
lemma isoConj_comp {C : Type*} [Category C] {a a' a'' b b' b'' : C}
    (e : a ≅ b) (e' : a' ≅ b') (e'' : a'' ≅ b'') (f : a ⟶ a') (g : a' ⟶ a'') :
    e.inv ≫ (f ≫ g) ≫ e''.hom =
      (e.inv ≫ f ≫ e'.hom) ≫ (e'.inv ≫ g ≫ e''.hom) := by
  simp

/-- **The split fibre of the base change read componentwise.** An object `(U, P, h)` of the split
fibre of `𝒳 ×_𝒴 𝒵` over `V` is sent to the pair `(U, P.x, h)`, `(U, P.y, h)` together with the
chosen pullback along `h` of the comparison isomorphism of `P`, and a morphism to its two
components conjugated by the comparisons of the chosen pullbacks. -/
noncomputable def splitFiberTwoFibreProductComparisonApp (V : BigFppfOver B S hS) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.SplitFiber V ⥤
      CategoricalPullback (splitFiberMap B S hS p V) (splitFiberMap B S hS q V) :=
  letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
  letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  letI : (TwoFibreProductOver.structureFunctor 𝒳.val.p 𝒵.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)).IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  let hp := isFibredOneMorphism B S hS p
  let hq := isFibredOneMorphism B S hS q
  let tf := fun (U : BigFppfOver B S hS) =>
    TwoFibreProductOver.toFiberPullback 𝒳.val.p 𝒵.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)
      hp.comp_eq hq.comp_eq U
  let af := fun {U V' : BigFppfOver B S hS}
      (P : (TwoFibreProductOver.structureFunctor 𝒳.val.p 𝒵.val.p 𝒴.val.p
        (CatFiberedInGroupoids.homFunctor p)
        (CatFiberedInGroupoids.homFunctor q)).Fiber U) (f : V' ⟶ U) =>
    TwoFibreProductOver.pullbackFiberFstIsoOfFiberedInGroupoids 𝒳.val.p 𝒵.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)
      hp.comp_eq hq.comp_eq P f 𝒳.isFiberedInGroupoids
  let bf := fun {U V' : BigFppfOver B S hS}
      (P : (TwoFibreProductOver.structureFunctor 𝒳.val.p 𝒵.val.p 𝒴.val.p
        (CatFiberedInGroupoids.homFunctor p)
        (CatFiberedInGroupoids.homFunctor q)).Fiber U) (f : V' ⟶ U) =>
    TwoFibreProductOver.pullbackFiberSndIsoOfFiberedInGroupoids 𝒳.val.p 𝒵.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)
      hp.comp_eq hq.comp_eq P f 𝒵.isFiberedInGroupoids
  { obj o :=
      {  fst := ⟨o.base, ((tf o.base).obj o.obj).fst, o.hom⟩
         snd := ⟨o.base, ((tf o.base).obj o.obj).snd, o.hom⟩
         iso := Functor.SplitFiber.isoOfFiberIso
           (Functor.pullbackFiberIso ((tf o.base).obj o.obj).iso o.hom) }
    map := fun {o o'} α =>
      {  fst := Functor.SplitFiber.ofFiberHom
           ((af o.obj o.hom).inv ≫
             ((tf V).map (Functor.SplitFiber.toFiberHom α)).fst ≫ (af o'.obj o'.hom).hom)
         snd := Functor.SplitFiber.ofFiberHom
           ((bf o.obj o.hom).inv ≫
             ((tf V).map (Functor.SplitFiber.toFiberHom α)).snd ≫ (bf o'.obj o'.hom).hom)
         w := Functor.SplitFiber.toFiberHom_injective
           (TwoFibreProductOver.mapPullbackFiberIso_conj_w 𝒳.val.p 𝒵.val.p 𝒴.val.p
             (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)
             hp hq 𝒳.isFiberedInGroupoids 𝒵.isFiberedInGroupoids
             o.obj o.hom o'.obj o'.hom (Functor.SplitFiber.toFiberHom α)) }
    map_id o := CategoricalPullback.Hom.ext
      (Functor.SplitFiber.toFiberHom_injective (isoConj_id (af o.obj o.hom)))
      (Functor.SplitFiber.toFiberHom_injective (isoConj_id (bf o.obj o.hom)))
    map_comp := fun {o o' o''} α β => CategoricalPullback.Hom.ext
      (Functor.SplitFiber.toFiberHom_injective
        (isoConj_comp (af o.obj o.hom) (af o'.obj o'.hom) (af o''.obj o''.hom)
          ((tf V).map (Functor.SplitFiber.toFiberHom α)).fst
          ((tf V).map (Functor.SplitFiber.toFiberHom β)).fst))
      (Functor.SplitFiber.toFiberHom_injective
        (isoConj_comp (bf o.obj o.hom) (bf o'.obj o'.hom) (bf o''.obj o''.hom)
          ((tf V).map (Functor.SplitFiber.toFiberHom α)).snd
          ((tf V).map (Functor.SplitFiber.toFiberHom β)).snd)) }

/-- **The comparison is strictly natural in the base.** Restriction along `g : V' ⟶ V` is
`h ↦ g ≫ h` on both sides, so the two composites agree on the nose, not merely up to
isomorphism. -/
lemma splitFiberTwoFibreProductComparisonApp_naturality
    {V V' : BigFppfOver B S hS} (g : V' ⟶ V) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    Functor.SplitFiber.restrict
          (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p g ⋙
        splitFiberTwoFibreProductComparisonApp B S hS 𝒳 𝒴 𝒵 p q V' =
      splitFiberTwoFibreProductComparisonApp B S hS 𝒳 𝒴 𝒵 p q V ⋙
        CategoricalPullback.map (splitFiberMap B S hS p V) (splitFiberMap B S hS q V)
          (Functor.SplitFiber.restrict 𝒳.val.p g) (Functor.SplitFiber.restrict 𝒵.val.p g)
          (Functor.SplitFiber.restrict 𝒴.val.p g)
          (splitFiberMap B S hS p V') (splitFiberMap B S hS q V')
          (eqToIso (splitFiberMap_naturality B S hS q g))
          (eqToIso (splitFiberMap_naturality B S hS p g).symm) := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
  let : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  let : (TwoFibreProductOver.structureFunctor 𝒳.val.p 𝒵.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)).IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  refine CategoryTheory.Functor.ext (fun o => ?_) (fun o o' α => ?_)
  · refine Cat.categoricalPullback_obj_ext rfl rfl ?_
    simp only [Functor.comp_obj, CategoricalPullback.map_obj_iso_hom, eqToIso.inv, eqToHom_app]
    refine Cat.eq_eqToHom_conj _ _ _ _ (heq_of_eq ?_)
    refine Cat.eq_eqToHom_conj _ _ _ _ (heq_of_eq ?_)
    exact Functor.SplitFiber.toFiberHom_injective
      (TwoFibreProductOver.restrictHom_pullbackFiberHom
        (p := 𝒴.val.p) _ o.hom g).symm
  · refine CategoricalPullback.Hom.ext ?_ ?_ <;>
      simp only [Functor.comp_map, CategoricalPullback.comp_fst, CategoricalPullback.comp_snd,
        Cat.categoricalPullback_eqToHom_fst, Cat.categoricalPullback_eqToHom_snd,
        CategoricalPullback.map_map_fst, CategoricalPullback.map_map_snd] <;>
      refine Cat.eq_eqToHom_conj _ _ _ _ (heq_of_eq
        (Functor.SplitFiber.toFiberHom_injective (Eq.symm ?_)))
    · exact TwoFibreProductOver.restrictHom_conj_fst 𝒳.val.p 𝒵.val.p 𝒴.val.p
        (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)
        (isFibredOneMorphism B S hS p) (isFibredOneMorphism B S hS q)
        𝒳.isFiberedInGroupoids o.obj o.hom o'.obj o'.hom
        (Functor.SplitFiber.toFiberHom α) g
    · exact TwoFibreProductOver.restrictHom_conj_snd 𝒳.val.p 𝒵.val.p 𝒴.val.p
        (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)
        (isFibredOneMorphism B S hS p) (isFibredOneMorphism B S hS q)
        𝒵.isFiberedInGroupoids o.obj o.hom o'.obj o'.hom
        (Functor.SplitFiber.toFiberHom α) g

variable {I : Type v} [Category.{w} I]

/-- **The comparison at one stage of the diagram of split fibres.** The componentwise reading of
`AlgebraicGeometry.Stack.splitFiberTwoFibreProductComparisonApp`, followed by the universe lift
that turns the 2-fibre product of split fibres into the stage of
`CategoryTheory.Cat.twoFibreProductDiagram`. -/
noncomputable def splitFiberTwoFibreProductComparisonStage (E : I ⥤ BigFppfOver B S hS)
    (j : Iᵒᵖ) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.SplitFiber (E.obj j.unop) ⥤
      CategoricalPullback
        ((fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS p E).app j).toFunctor
        ((fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS q E).app j).toFunctor :=
  letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
  letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  splitFiberTwoFibreProductComparisonApp B S hS 𝒳 𝒴 𝒵 p q (E.obj j.unop) ⋙
    CategoricalPullback.map (splitFiberMap B S hS p (E.obj j.unop))
      (splitFiberMap B S hS q (E.obj j.unop)) AsSmall.up AsSmall.up AsSmall.up
      ((fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS p E).app j).toFunctor
      ((fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS q E).app j).toFunctor
      (eqToIso (asSmall_up_comp_fiberDiagramMap_app B S hS q E j))
      (eqToIso (asSmall_up_comp_fiberDiagramMap_app B S hS p E j).symm)

/-- **The stagewise comparison is strictly natural in the stage.** The unlifted comparison is
natural on the nose by
`AlgebraicGeometry.Stack.splitFiberTwoFibreProductComparisonApp_naturality`, and the universe
lift commutes with a change of cospan by
`CategoryTheory.Cat.categoricalPullback_map_comp_asSmallMap`. -/
lemma splitFiberTwoFibreProductComparisonStage_naturality (E : I ⥤ BigFppfOver B S hS)
    {j k : Iᵒᵖ} (s : j ⟶ k) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    Functor.SplitFiber.restrict
          (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p (E.map s.unop) ⋙
        splitFiberTwoFibreProductComparisonStage B S hS 𝒳 𝒴 𝒵 p q E k =
      splitFiberTwoFibreProductComparisonStage B S hS 𝒳 𝒴 𝒵 p q E j ⋙
        CategoricalPullback.map
          (AsSmall.down ⋙ splitFiberMap B S hS p (E.obj j.unop) ⋙ AsSmall.up)
          (AsSmall.down ⋙ splitFiberMap B S hS q (E.obj j.unop) ⋙ AsSmall.up)
          (AsSmall.down ⋙ Functor.SplitFiber.restrict 𝒳.val.p (E.map s.unop) ⋙ AsSmall.up)
          (AsSmall.down ⋙ Functor.SplitFiber.restrict 𝒵.val.p (E.map s.unop) ⋙ AsSmall.up)
          (AsSmall.down ⋙ Functor.SplitFiber.restrict 𝒴.val.p (E.map s.unop) ⋙ AsSmall.up)
          (AsSmall.down ⋙ splitFiberMap B S hS p (E.obj k.unop) ⋙ AsSmall.up)
          (AsSmall.down ⋙ splitFiberMap B S hS q (E.obj k.unop) ⋙ AsSmall.up)
          (eqToIso (congrArg (fun F => AsSmall.down ⋙ F ⋙ AsSmall.up)
            (splitFiberMap_naturality B S hS q (E.map s.unop))))
          (eqToIso (congrArg (fun F => AsSmall.down ⋙ F ⋙ AsSmall.up)
            (splitFiberMap_naturality B S hS p (E.map s.unop)).symm)) :=
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
  let : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  Eq.trans
    (congrArg
      (fun F => F ⋙ CategoricalPullback.map (splitFiberMap B S hS p (E.obj k.unop))
        (splitFiberMap B S hS q (E.obj k.unop)) AsSmall.up AsSmall.up AsSmall.up
        ((fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS p E).app k).toFunctor
        ((fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS q E).app k).toFunctor
        (eqToIso (asSmall_up_comp_fiberDiagramMap_app B S hS q E k))
        (eqToIso (asSmall_up_comp_fiberDiagramMap_app B S hS p E k).symm))
      (splitFiberTwoFibreProductComparisonApp_naturality B S hS 𝒳 𝒴 𝒵 p q (E.map s.unop)))
    (congrArg
      (fun F => splitFiberTwoFibreProductComparisonApp B S hS 𝒳 𝒴 𝒵 p q (E.obj j.unop) ⋙ F)
      (Cat.categoricalPullback_map_comp_asSmallMap
        (splitFiberMap B S hS p (E.obj j.unop)) (splitFiberMap B S hS q (E.obj j.unop))
        (splitFiberMap B S hS p (E.obj k.unop)) (splitFiberMap B S hS q (E.obj k.unop))
        (Functor.SplitFiber.restrict 𝒳.val.p (E.map s.unop))
        (Functor.SplitFiber.restrict 𝒵.val.p (E.map s.unop))
        (Functor.SplitFiber.restrict 𝒴.val.p (E.map s.unop))
        (splitFiberMap_naturality B S hS q (E.map s.unop))
        (splitFiberMap_naturality B S hS p (E.map s.unop))))

/-- **The transition functor of the stagewise 2-fibre product, read through the universe
lifts.** Both sides are the same functor; the point of the lemma is that it is stated in the
spelling produced by `CategoryTheory.Cat.categoricalPullback_map_comp_asSmallMap`, so that
assembling the stagewise comparison into a morphism of diagrams costs one transport-free
rewrite instead of a definitional unfolding of the whole diagram. -/
lemma twoFibreProductMap_fiberDiagramMap (E : I ⥤ BigFppfOver B S hS) {j k : Iᵒᵖ} (s : j ⟶ k) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    Cat.twoFibreProductMap
          (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS p E)
          (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS q E) s =
      CategoricalPullback.map
        (AsSmall.down ⋙ splitFiberMap B S hS p (E.obj j.unop) ⋙ AsSmall.up)
        (AsSmall.down ⋙ splitFiberMap B S hS q (E.obj j.unop) ⋙ AsSmall.up)
        (AsSmall.down ⋙ Functor.SplitFiber.restrict 𝒳.val.p (E.map s.unop) ⋙ AsSmall.up)
        (AsSmall.down ⋙ Functor.SplitFiber.restrict 𝒵.val.p (E.map s.unop) ⋙ AsSmall.up)
        (AsSmall.down ⋙ Functor.SplitFiber.restrict 𝒴.val.p (E.map s.unop) ⋙ AsSmall.up)
        (AsSmall.down ⋙ splitFiberMap B S hS p (E.obj k.unop) ⋙ AsSmall.up)
        (AsSmall.down ⋙ splitFiberMap B S hS q (E.obj k.unop) ⋙ AsSmall.up)
        (eqToIso (congrArg (fun F => AsSmall.down ⋙ F ⋙ AsSmall.up)
          (splitFiberMap_naturality B S hS q (E.map s.unop))))
        (eqToIso (congrArg (fun F => AsSmall.down ⋙ F ⋙ AsSmall.up)
          (splitFiberMap_naturality B S hS p (E.map s.unop)).symm)) := rfl

/-- **The diagram-level comparison `Φ`.** The split fibres of the base change `𝒳 ×_𝒴 𝒵`, as a
diagram over the index category of a cone, compared stagewise with the stagewise 2-fibre product
of the diagrams of split fibres of `𝒳`, `𝒴` and `𝒵`. It is a morphism of diagrams, not merely a
stagewise comparison, because
`AlgebraicGeometry.Stack.splitFiberTwoFibreProductComparisonStage_naturality` is an equality of
functors; that strictness is what `CategoryTheory.Limits.colimMap` needs. -/
noncomputable def splitFiberTwoFibreProductComparison (E : I ⥤ BigFppfOver B S hS) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    Deformation.Artin.fiberDiagram
        (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p E ⟶
      Cat.twoFibreProductDiagram
        (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS p E)
        (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS q E) :=
  letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
  letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  { app := fun j =>
      (AsSmall.down ⋙
        splitFiberTwoFibreProductComparisonStage B S hS 𝒳 𝒴 𝒵 p q E j).toCatHom
    naturality := fun j _ s =>
      Cat.Hom.ext
        ((congrArg (fun F => AsSmall.down ⋙ F)
            (splitFiberTwoFibreProductComparisonStage_naturality B S hS 𝒳 𝒴 𝒵 p q E s)).trans
          (congrArg
            (fun G => AsSmall.down ⋙
              (splitFiberTwoFibreProductComparisonStage B S hS 𝒳 𝒴 𝒵 p q E j ⋙ G))
            (twoFibreProductMap_fiberDiagramMap B S hS 𝒳 𝒴 𝒵 p q E s).symm)) }

/-- **A component of `Φ` is an equivalence as soon as the unlifted comparison is.** The component
is the unlifted comparison sandwiched between two universe lifts, and both lifts are
equivalences: `CategoryTheory.AsSmall.down` on the source and, on the target,
`CategoryTheory.Cat.isEquivalence_categoricalPullback_asSmallMap`, which is Stacks 02XB (3) for
the lift of a cospan. So the one thing a stagewise equivalence needs is that the componentwise
reading of the split fibre of the 2-fibre product is an equivalence at each `V`. -/
lemma isEquivalence_splitFiberTwoFibreProductComparison_app (E : I ⥤ BigFppfOver B S hS)
    (j : Iᵒᵖ)
    (h : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
      letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
      letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
        (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
      (splitFiberTwoFibreProductComparisonApp B S hS 𝒳 𝒴 𝒵 p q
        (E.obj j.unop)).IsEquivalence) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    Functor.IsEquivalence
      ((splitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒵 p q E).app j).toFunctor := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
  let : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  let := h
  exact inferInstanceAs
    (((AsSmall.down ⋙ splitFiberTwoFibreProductComparisonApp B S hS 𝒳 𝒴 𝒵 p q (E.obj j.unop)) ⋙
      CategoricalPullback.map (splitFiberMap B S hS p (E.obj j.unop))
        (splitFiberMap B S hS q (E.obj j.unop)) AsSmall.up AsSmall.up AsSmall.up
        (AsSmall.down ⋙ splitFiberMap B S hS p (E.obj j.unop) ⋙ AsSmall.up)
        (AsSmall.down ⋙ splitFiberMap B S hS q (E.obj j.unop) ⋙ AsSmall.up)
        (eqToIso rfl) (eqToIso rfl)).IsEquivalence)

end AlgebraicGeometry.Stack

end
