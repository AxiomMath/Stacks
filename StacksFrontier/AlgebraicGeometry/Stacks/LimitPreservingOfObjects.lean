module

public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingDiagonalCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingRepresentableEssSurj
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Diagonal
public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCatStagewiseEquivalence
public import StacksFrontier.CategoryTheory.Sites.Stackification.RawLocalEquality
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatCategoricalPullbackConverse

/-!
# Limit preservation from limit preservation on objects of a 1-morphism and its two diagonals

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf category of
a scheme `S`. If `f`, its relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` and the diagonal `Δ_{Δ_f}` of
that are all limit preserving on objects (Stacks 06CU), then `f` is limit preserving
(Stacks 0CMR). This is the formal half of the proof of Stacks 0CMY, implication (3) ⟹ (1), and
of the proof of the implication (2) ⟹ (1) of Stacks 0CMV.

## Main results

* `CategoryTheory.Cat.full_toCategoricalPullbackFunctor_of_full_snd` and
  `CategoryTheory.Cat.faithful_toCategoricalPullbackFunctor_of_faithful_snd`: the comparison of
  a 2-commutative square into the explicit 2-fibre product is fully faithful as soon as its
  second leg is and the first leg of the cospan is faithful.
* `AlgebraicGeometry.Stack.isFullyFaithfulOnAffineLimits_of_full_of_faithful`: condition (2) of
  Stacks 0CMW holds for a 1-morphism which is fully faithful.
* `Stack.isLimitPreserving_of_isLimitPreservingOnObjects_of_isFullyFaithfulOnAffineLimits`:
  limit preservation on objects together with condition (2) of Stacks 0CMW is limit preservation.
* `AlgebraicGeometry.Stack.isLimitPreserving_of_isLimitPreservingOnObjects_diagonals`: the
  statement of this module.

## Implementation notes

The comparison `colim 𝒳_{Uᵢ} ⟶ 𝒳_U ×_{𝒴_U} colim 𝒴_{Uᵢ}` of the canonical square of Stacks 0CMR
is an equivalence exactly when the square is 2-cartesian (Stacks 003Q). Limit preservation on
objects makes it essentially surjective
(`AlgebraicGeometry.Stack.relativeDescentObj_of_isLimitPreservingOnObjects` and
`AlgebraicGeometry.Stack.essSurj_toCategoricalPullbackFunctor_canonicalSquare`); full
faithfulness is condition (2) of Stacks 0CMW, which **Stacks 0CMW** equates with limit
preservation of the diagonal. Applied to `Δ_f` and then to `f`, this reduces everything to full
faithfulness of the comparison for `Δ_{Δ_f}`, which holds because `Δ_{Δ_f}` is a fully faithful
functor: `Δ_f` is faithful, being injective on the first component, and the diagonal of a
faithful functor is full. For a fully faithful 1-morphism the comparison is fully faithful
because the second leg of the canonical square, the colimit of the stagewise maps of split
fibres, is (`CategoryTheory.Cat.full_colimMap`, `CategoryTheory.Cat.faithful_colimMap`), and the
first leg of the cospan, the map of fibres over the limit, is faithful.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
* [Stacks Project, Tag 0CMR](https://stacks.math.columbia.edu/tag/0CMR)
* [Stacks Project, Tag 0CMV](https://stacks.math.columbia.edu/tag/0CMV)
* [Stacks Project, Tag 0CMW](https://stacks.math.columbia.edu/tag/0CMW)
* [Stacks Project, Tag 0CMY](https://stacks.math.columbia.edu/tag/0CMY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Cat

universe v u

variable {A B C : Cat.{v, max u v}} {F : A ⟶ C} {G : B ⟶ C}

/-- **The comparison into the explicit 2-fibre product is full when the second leg is fully
faithful and the first leg of the cospan is faithful.** A morphism `(α, β)` of triples has `β`
in the image of the second leg; its preimage `m` has first image `α`, because both `F α` and
`F (fst m)` are the conjugate of `G β` by the fillers. -/
theorem full_toCategoricalPullbackFunctor_of_full_snd (P : Bicategory.TwoCommSq F G)
    [P.snd.toFunctor.Full] [F.toFunctor.Faithful] :
    (toCategoricalPullbackFunctor P).Full where
  map_surjective {x y} m := by
    obtain ⟨n, hn⟩ := P.snd.toFunctor.map_surjective m.snd
    refine ⟨n, CategoricalPullback.hom_ext ?_ hn⟩
    apply F.toFunctor.map_injective
    have hw : F.toFunctor.map m.fst ≫ ((Cat.Hom.toNatIso P.iso).app y).hom =
        ((Cat.Hom.toNatIso P.iso).app x).hom ≫ G.toFunctor.map m.snd := m.w
    rw [← hn] at hw
    exact (cancel_mono ((Cat.Hom.toNatIso P.iso).app y).hom).1
      (((Cat.Hom.toNatIso P.iso).hom.naturality n).trans hw.symm)

/-- **The comparison into the explicit 2-fibre product is faithful when the second leg is.** -/
theorem faithful_toCategoricalPullbackFunctor_of_faithful_snd (P : Bicategory.TwoCommSq F G)
    [P.snd.toFunctor.Faithful] :
    (toCategoricalPullbackFunctor P).Faithful where
  map_injective {_ _} _ _ h :=
    P.snd.toFunctor.map_injective (congrArg CategoricalPullback.Hom.snd h)

end CategoryTheory.Cat

namespace AlgebraicGeometry.Stack

universe u v w uX vX

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion
  Bicategory.InducedBicategory AsSmall.up AsSmall.down Deformation.Artin.fiberDiagram
  Functor.splitPresheaf Cat.asSmallFunctor

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The map of split fibres of a fully faithful 1-morphism is fully faithful.** It is the map
of fibres conjugated by the base-change comparisons of the fibred 1-morphism, and the map of
fibres of a fully faithful functor strictly over the base is fully faithful. -/
theorem fullyFaithful_splitFiberMap
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, vX, u + 1, uX} (BigFppfOver B S hS)} (g : 𝒳 ⟶ 𝒴)
    [(CatFiberedInGroupoids.homFunctor g).Full] [(CatFiberedInGroupoids.homFunctor g).Faithful]
    (V : BigFppfOver B S hS) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    (splitFiberMap B S hS g V).Full ∧ (splitFiberMap B S hS g V).Faithful := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let hF := isFibredOneMorphism B S hS g
  obtain ⟨e⟩ := Functor.fullyFaithful_fiberFunctorOfCompEq hF.comp_eq inferInstance
    inferInstance V
  have key : ∀ {a b} (α : a ⟶ b), Functor.SplitFiber.toFiberHom ((splitFiberMap B S hS g V).map α) =
      (hF.mapPullbackFiberIso a.obj a.hom).hom ≫
        (Functor.fiberFunctorOfCompEq hF.comp_eq V).map (Functor.SplitFiber.toFiberHom α) ≫
        (hF.mapPullbackFiberIso b.obj b.hom).inv := fun _ => rfl
  refine ⟨⟨fun {a b} β => ?_⟩, ⟨fun {a b} α α' h => ?_⟩⟩
  · refine ⟨Functor.SplitFiber.ofFiberHom (e.preimage
      ((hF.mapPullbackFiberIso a.obj a.hom).inv ≫ Functor.SplitFiber.toFiberHom β ≫
        (hF.mapPullbackFiberIso b.obj b.hom).hom)), ?_⟩
    apply Functor.SplitFiber.toFiberHom_injective
    rw [key]
    erw [e.map_preimage]
    simp
  · apply Functor.SplitFiber.toFiberHom_injective
    apply e.map_injective
    have h' := congrArg Functor.SplitFiber.toFiberHom h
    rw [key, key] at h'
    simpa using h'

/-- **Condition (2) of Stacks 0CMW holds for a fully faithful 1-morphism.** The second leg of the
canonical square of Stacks 0CMR is the colimit of the stagewise maps of split fibres, which are
fully faithful, so it is fully faithful; and the first leg of the cospan, the map of fibres over
the limit, is faithful. -/
theorem isFullyFaithfulOnAffineLimits_of_full_of_faithful
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, vX, u + 1, uX} (BigFppfOver B S hS)} (g : 𝒳 ⟶ 𝒴)
    [(CatFiberedInGroupoids.homFunctor g).Full] [(CatFiberedInGroupoids.homFunctor g).Faithful] :
    IsFullyFaithfulOnAffineLimits.{u, v, w, uX, vX} B S hS g := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  apply isFullyFaithfulOnAffineLimits_of_canonicalSquare
  intro I _ _ D c hc
  let E := D ⋙ BigAffineFppf.inclusion B S hS
  let d := (BigAffineFppf.inclusion B S hS).mapCone c
  let T := fiberDiagramMap.{u, v, w, uX, vX} B S hS g E
  have hstage : ∀ j : Iᵒᵖ, (T.app j).toFunctor.Full ∧ (T.app j).toFunctor.Faithful := by
    intro j
    obtain ⟨hfull, hfaith⟩ := fullyFaithful_splitFiberMap B S hS g (E.obj j.unop)
    exact ⟨⟨fun {a b} β => ⟨⟨(hfull.map_surjective β.down).choose⟩,
        congrArg ULift.up (hfull.map_surjective β.down).choose_spec⟩⟩,
      ⟨fun {a b} α α' h => ULift.ext _ _ (hfaith.map_injective (congrArg ULift.down h))⟩⟩
  obtain ⟨e⟩ := Functor.fullyFaithful_fiberFunctorOfCompEq
    (isFibredOneMorphism B S hS g).comp_eq inferInstance
    inferInstance d.pt
  have : (AsSmall.down.{vX, uX, max v w vX (u + 1) uX u} ⋙
      Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p g) d.pt ⋙
      AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}).toCatHom.toFunctor.Faithful :=
    ⟨fun {a b} α α' h => ULift.ext _ _ (e.map_injective (congrArg ULift.down h))⟩
  have : (canonicalSquare.{u, v, w, uX, vX} B S hS g E d).snd.toFunctor.Full :=
    Cat.full_colimMap.{max v w vX (u + 1) uX u, v, w} T fun j => (hstage j).1
  have : (canonicalSquare.{u, v, w, uX, vX} B S hS g E d).snd.toFunctor.Faithful :=
    Cat.faithful_colimMap.{max v w vX (u + 1) uX u, v, w} T fun j => (hstage j).2
  exact ⟨Cat.full_toCategoricalPullbackFunctor_of_full_snd _,
    Cat.faithful_toCategoricalPullbackFunctor_of_faithful_snd _⟩

/-- **Limit preservation on objects together with condition (2) of Stacks 0CMW is limit
preservation.** The comparison of the canonical square of Stacks 0CMR into the explicit 2-fibre
product is then essentially surjective and fully faithful, hence an equivalence, so the square is
2-cartesian (Stacks 003Q). This is the last step of the proofs of Stacks 0CMV and Stacks 0CMY. -/
theorem isLimitPreserving_of_isLimitPreservingOnObjects_of_isFullyFaithfulOnAffineLimits
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, vX, u + 1, uX} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (hobj : BigFppfOver.IsLimitPreservingOnObjects.{u, v, w, vX, uX} B S hS 𝒳 𝒴 f)
    (hff : IsFullyFaithfulOnAffineLimits.{u, v, w, uX, vX} B S hS f) :
    IsLimitPreserving.{u, v, w, uX, vX} B S hS f := by
  apply isLimitPreserving_of_canonicalSquare
  intro I _ _ D c hc
  obtain ⟨hfull, hfaith⟩ :=
    fullyFaithful_canonicalSquare_of_isFullyFaithfulOnAffineLimits B S hS f hff I D c hc
  exact Cat.nonempty_isTwoFibreProduct_of_isEquivalence_toCategoricalPullbackFunctor _
    { faithful := hfaith, full := hfull
      essSurj := essSurj_toCategoricalPullbackFunctor_canonicalSquare B S hS f
        (D ⋙ BigAffineFppf.inclusion B S hS) ((BigAffineFppf.inclusion B S hS).mapCone c)
        (relativeDescentObj_of_isLimitPreservingOnObjects B S hS f D c hc hobj) }

/-- **A 1-morphism which is limit preserving on objects, with both diagonals limit preserving on
objects, is limit preserving.** The second diagonal `Δ_{Δ_f}` is a fully faithful functor, so it
satisfies condition (2) of Stacks 0CMW and is limit preserving; by Stacks 0CMW the diagonal `Δ_f`
then satisfies condition (2), so it is limit preserving; by Stacks 0CMW again `f` satisfies
condition (2), so it is limit preserving. -/
theorem isLimitPreserving_of_isLimitPreservingOnObjects_diagonals
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴)
    (hobj : BigFppfOver.IsLimitPreservingOnObjects.{u, v, w} B S hS 𝒳 𝒴 f)
    (hΔ : BigFppfOver.IsLimitPreservingOnObjects.{u, v, w} B S hS 𝒳
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f)
      (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f))
    (hΔΔ : BigFppfOver.IsLimitPreservingOnObjects.{u, v, w} B S hS 𝒳
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳
        (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f) 𝒳
        (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f)
        (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f))
      (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳
        (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f)
        (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f))) :
    IsLimitPreserving.{u, v, w, max (u + 1) v w, max u v} B S hS f := by
  let P := BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f
  let Δ := BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f
  let ΔΔ := BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 P Δ
  have : (CatFiberedInGroupoids.homFunctor Δ).Faithful :=
    TwoFibreProductOver.faithful_diagonal (CatFiberedInGroupoids.homFunctor_comp_p f)
  have : (CatFiberedInGroupoids.homFunctor ΔΔ).Faithful :=
    TwoFibreProductOver.faithful_diagonal (CatFiberedInGroupoids.homFunctor_comp_p Δ)
  have : (CatFiberedInGroupoids.homFunctor ΔΔ).Full :=
    TwoFibreProductOver.full_diagonal (CatFiberedInGroupoids.homFunctor_comp_p Δ)
  have hLPΔΔ : IsLimitPreserving.{u, v, w, max (u + 1) v w, max u v} B S hS ΔΔ :=
    isLimitPreserving_of_isLimitPreservingOnObjects_of_isFullyFaithfulOnAffineLimits B S hS ΔΔ
      hΔΔ (isFullyFaithfulOnAffineLimits_of_full_of_faithful B S hS ΔΔ)
  have hLPΔ := isLimitPreserving_of_isLimitPreservingOnObjects_of_isFullyFaithfulOnAffineLimits
    B S hS Δ hΔ ((isLimitPreserving_twoFibreProductDiagonal_iff B S hS 𝒳 P Δ).mp hLPΔΔ)
  exact isLimitPreserving_of_isLimitPreservingOnObjects_of_isFullyFaithfulOnAffineLimits B S hS f
    hobj ((isLimitPreserving_twoFibreProductDiagonal_iff B S hS 𝒳 𝒴 f).mp hLPΔ)

end AlgebraicGeometry.Stack

end
