module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentedTwoFibreProductPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEvery
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverCancelSnd

/-!
# Smooth-local properties of morphisms of stacks: the every- and some-diagram conditions

For a property of morphisms of algebraic spaces that is smooth-local on source and target, a
morphism of stacks has the property on every smooth diagram exactly when it has it on some
smooth diagram. That equivalence, and the implication from some to every that carries it, are
`StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse`:

* `AlgebraicGeometry.Stack.hasPropertyOnEverySmoothDiagram_iff_some`
* `AlgebraicGeometry.Stack.hasPropertyOnEverySmoothDiagram_of_hasPropertyOnSomeSmoothDiagram`

and tag 06FM is registered there. This module re-exports them under the module name its
consumers import.

## References

* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A smooth base change, read off any cartesian square.** For a property `P` of morphisms of
algebraic spaces over `S` smooth local on the source-and-target, a morphism `m` with `P` and a
smooth morphism `n` with the same target, every cartesian square over `(m, n)` has `P` on its
projection to the source of `n`.

`AlgebraicGeometry.Space.IsSmoothLocalOnSourceAndTarget.pullbackSnd_of_smooth` says this for the
canonical pullback; the comparison of the two cartesian squares is an isomorphism over the source
of `n`, and smooth locality on the source transports `P` across it. -/
theorem prop_of_isPullback_of_isSmooth
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hP : Space.IsSmoothLocalOnSourceAndTarget B S hS P)
    {X Y Y' W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hY' : IsAlgebraicSpace B S hS Y') (hW : IsAlgebraicSpace B S hS W)
    (m : X ⟶ Y) (n : Y' ⟶ Y) (p : W ⟶ X) (q : W ⟶ Y')
    (sq : IsPullback p q m n) (hm : P m) (hn : Space.IsSmooth B S hS n) :
    P q := by
  have hpb : IsPullback (pullback.fst m n) (pullback.snd m n) m n := IsPullback.of_hasPullback m n
  have hsnd : P (pullback.snd m n) := hP.pullbackSnd_of_smooth hX hY hY' m n hm hn
  have hpbalg : IsAlgebraicSpace B S hS (pullback m n) :=
    isAlgebraicSpace_pullback B S hS m n hX hY' hY
  have he : (hpb.isoIsPullback X Y' sq).hom ≫ q = pullback.snd m n :=
    IsPullback.isoIsPullback_hom_snd X Y' hpb sq
  have hcomp : P ((hpb.isoIsPullback X Y' sq).inv ≫ (hpb.isoIsPullback X Y' sq).hom ≫ q) :=
    hP.precomp hW hpbalg hY' (hpb.isoIsPullback X Y' sq).inv
      ((hpb.isoIsPullback X Y' sq).hom ≫ q)
      (Space.isSmooth_of_isIso B S hS hW hpbalg (hpb.isoIsPullback X Y' sq).inv)
      (by rw [he]; exact hsnd)
  rwa [Iso.inv_hom_id_assoc] at hcomp

/-- **The two iterated 2-fibre products describing `U ×_𝒴 V'` are comparable over `V'`.** Let
`f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf site of `S`, let
`a`, `b`, `b'` be 1-morphisms out of the categories of elements of presheaves `U`, `V`, `V'` with
`a` over `𝒳` and `b`, `b'` over `𝒴`, let `h : U ⟶ V`, and let `η` identify the two composites
`U ⟶ 𝒴`. Then the apex of `(V ×_𝒴 V') ×_V U` maps to the apex of `(𝒳 ×_𝒴 V') ×_𝒳 U` by an
equivalence of the underlying categories, compatibly with the two projections to the category of
elements of `V'`.

Both apexes are compared with `V' ×_𝒴 U` by `CategoryTheory.TwoFibreProductOver.cancelSnd`, which
is an equivalence over the site; `η` is the reindexing that makes the two comparisons land in the
same target, and `CategoryTheory.TwoFibreProductOver.cancelSnd_comp_fst` — an equality of functors
on the nose — is what makes the 2-cell comparing the projections to `V'` the counit of the first
comparison whiskered on both sides. -/
theorem exists_twoIso_cancelIteratedTwoFibreProduct
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) {U V V' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : fibredCategory B S hS U ⟶ 𝒳) (b : fibredCategory B S hS V ⟶ 𝒴)
    (b' : fibredCategory B S hS V' ⟶ 𝒴) (h : U ⟶ V)
    (η : (associatedMap B S hS h).1 ≫ b ≅ a ≫ f) :
    ∃ d : (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
            (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b' b).snd
            (associatedMap B S hS h).1).pt ⟶
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
            (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b' f).snd a).pt,
      Functor.IsEquivalence d.hom.toFunctor ∧
        Nonempty ((CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
              (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b' b).snd
              (associatedMap B S hS h).1).fst ≫
            (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b' b).fst ≅
          d ≫ (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
              (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b' f).snd a).fst ≫
            (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b' f).fst) := by
  set Q : Bicategory.TwoCommSq b' f :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b' f with hQdef
  set Nq : Bicategory.TwoCommSq b' b :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b' b with hNqdef
  set Mq : Bicategory.TwoCommSq Nq.snd (associatedMap B S hS h).1 :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Nq.snd
      (associatedMap B S hS h).1 with hMqdef
  set Dq : Bicategory.TwoCommSq Q.snd a :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Q.snd a with hDqdef
  -- the common target `V' ×_𝒴 U` of the two cancellations
  have hcf : (CatFiberedInGroupoids.homFunctor a ⋙ CatFiberedInGroupoids.homFunctor f) ⋙
      𝒴.val.p = (fibredCategory B S hS U).val.p := by
    rw [Functor.assoc, CatFiberedInGroupoids.homFunctor_comp_p f,
      CatFiberedInGroupoids.homFunctor_comp_p a]
  set targetP := TwoFibreProductOver.structureFunctor (fibredCategory B S hS V').val.p
    (fibredCategory B S hS U).val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor b')
    (CatFiberedInGroupoids.homFunctor a ⋙ CatFiberedInGroupoids.homFunctor f) with htargetPdef
  have htarget : targetP.IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids (fibredCategory B S hS V').val.p
      (fibredCategory B S hS U).val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor b')
      (CatFiberedInGroupoids.homFunctor a ⋙ CatFiberedInGroupoids.homFunctor f)
      (fibredCategory B S hS V').isFiberedInGroupoids
      (fibredCategory B S hS U).isFiberedInGroupoids 𝒴.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor_comp_p b') hcf
  have hθrefl : ∀ uu : (fibredCategory B S hS U).val.obj,
      𝒴.val.p.IsHomLift (𝟙 ((fibredCategory B S hS U).val.p.obj uu))
        ((Iso.refl (CatFiberedInGroupoids.homFunctor a ⋙
          CatFiberedInGroupoids.homFunctor f)).hom.app uu) := by
    intro uu
    have hbb : (fibredCategory B S hS U).val.p.obj uu =
        𝒴.val.p.obj ((CatFiberedInGroupoids.homFunctor a ⋙
          CatFiberedInGroupoids.homFunctor f).obj uu) :=
      (Functor.congr_obj hcf uu).symm
    rw [hbb]
    change 𝒴.val.p.IsHomLift _ (𝟙 ((CatFiberedInGroupoids.homFunctor a ⋙
      CatFiberedInGroupoids.homFunctor f).obj uu))
    infer_instance
  set cancD := TwoFibreProductOver.cancelSnd (fibredCategory B S hS V').val.p 𝒳.val.p 𝒴.val.p
    (fibredCategory B S hS U).val.p (CatFiberedInGroupoids.homFunctor b')
    (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor a)
    (CatFiberedInGroupoids.homFunctor a ⋙ CatFiberedInGroupoids.homFunctor f)
    (CatFiberedInGroupoids.homFunctor_comp_p f) (Iso.refl _) hθrefl with hcancDdef
  set cancM := TwoFibreProductOver.cancelSnd (fibredCategory B S hS V').val.p
    (fibredCategory B S hS V).val.p 𝒴.val.p (fibredCategory B S hS U).val.p
    (CatFiberedInGroupoids.homFunctor b') (CatFiberedInGroupoids.homFunctor b)
    (CatFiberedInGroupoids.homFunctor (associatedMap B S hS h).1)
    (CatFiberedInGroupoids.homFunctor a ⋙ CatFiberedInGroupoids.homFunctor f)
    (CatFiberedInGroupoids.homFunctor_comp_p b)
    (CatFiberedInGroupoids.underlyingIso η) (fun x => η.hom.hom.isHomLift' x) with hcancMdef
  have hcancDstr : cancD ⋙ targetP = Dq.pt.val.p :=
    TwoFibreProductOver.cancelSnd_comp_structureFunctor (fibredCategory B S hS V').val.p
      𝒳.val.p 𝒴.val.p (fibredCategory B S hS U).val.p (CatFiberedInGroupoids.homFunctor b')
      (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor a)
      (CatFiberedInGroupoids.homFunctor a ⋙ CatFiberedInGroupoids.homFunctor f)
      (CatFiberedInGroupoids.homFunctor_comp_p f) (Iso.refl _) hθrefl
  have hcancMstr : cancM ⋙ targetP = Mq.pt.val.p :=
    TwoFibreProductOver.cancelSnd_comp_structureFunctor (fibredCategory B S hS V').val.p
      (fibredCategory B S hS V).val.p 𝒴.val.p (fibredCategory B S hS U).val.p
      (CatFiberedInGroupoids.homFunctor b') (CatFiberedInGroupoids.homFunctor b)
      (CatFiberedInGroupoids.homFunctor (associatedMap B S hS h).1)
      (CatFiberedInGroupoids.homFunctor a ⋙ CatFiberedInGroupoids.homFunctor f)
      (CatFiberedInGroupoids.homFunctor_comp_p b)
      (CatFiberedInGroupoids.underlyingIso η) (fun x => η.hom.hom.isHomLift' x)
  -- a quasi-inverse of the first cancellation, over the site, by Stacks 003Z
  obtain ⟨FD, hFD, ηD, εD, hηD, hεD⟩ :=
    Functor.IsFiberedInGroupoids.isEquivalence_over Dq.pt.val.p targetP
      Dq.pt.isFiberedInGroupoids htarget cancD hcancDstr
      (TwoFibreProductOver.isEquivalence_cancelSnd (fibredCategory B S hS V').val.p
        𝒳.val.p 𝒴.val.p (fibredCategory B S hS U).val.p (CatFiberedInGroupoids.homFunctor b')
        (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor a)
        (CatFiberedInGroupoids.homFunctor a ⋙ CatFiberedInGroupoids.homFunctor f)
        (CatFiberedInGroupoids.homFunctor_comp_p f)
        (CatFiberedInGroupoids.homFunctor_comp_p a) (Iso.refl _) hθrefl)
  have hwc : (cancM ⋙ FD) ⋙ Dq.pt.val.p = Mq.pt.val.p :=
    (congrArg (fun k₀ : _ ⥤ BigFppfOver B S hS => cancM ⋙ k₀) hFD).trans hcancMstr
  have hFDequiv : Functor.IsEquivalence FD :=
    (CategoryTheory.Equivalence.mk cancD FD ηD.symm εD).symm.isEquivalence_functor
  refine ⟨Bicategory.InducedBicategory.mkHom ⟨cancM ⋙ FD, hwc⟩, ?_, ?_⟩
  · change Functor.IsEquivalence (cancM ⋙ FD)
    have h1 := TwoFibreProductOver.isEquivalence_cancelSnd (fibredCategory B S hS V').val.p
      (fibredCategory B S hS V).val.p 𝒴.val.p (fibredCategory B S hS U).val.p
      (CatFiberedInGroupoids.homFunctor b') (CatFiberedInGroupoids.homFunctor b)
      (CatFiberedInGroupoids.homFunctor (associatedMap B S hS h).1)
      (CatFiberedInGroupoids.homFunctor a ⋙ CatFiberedInGroupoids.homFunctor f)
      (CatFiberedInGroupoids.homFunctor_comp_p b)
      (CatFiberedInGroupoids.homFunctor_comp_p (associatedMap B S hS h).1)
      (CatFiberedInGroupoids.underlyingIso η) (fun x => η.hom.hom.isHomLift' x)
    have h2 := hFDequiv
    infer_instance
  -- the comparison 2-cell of the two projections to the category of elements of `V'`
  set fstT := TwoFibreProductOver.fst (fibredCategory B S hS V').val.p
    (fibredCategory B S hS U).val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor b')
    (CatFiberedInGroupoids.homFunctor a ⋙ CatFiberedInGroupoids.homFunctor f) with hfstTdef
  have hvert : ∀ x : Mq.pt.val.obj,
      (fibredCategory B S hS V').val.p.IsHomLift (𝟙 (Mq.pt.val.p.obj x))
        (fstT.map (εD.inv.app (cancM.obj x))) := by
    intro x
    have h1 : targetP.IsHomLift (𝟙 (targetP.obj (cancM.obj x))) (εD.inv.app (cancM.obj x)) :=
      @IsHomLift.lift_id_inv _ _ _ _ targetP (targetP.obj (cancM.obj x)) _ _
        (εD.app (cancM.obj x)) (hεD (cancM.obj x))
    have h2 : (fibredCategory B S hS V').val.p.IsHomLift
        (𝟙 (targetP.obj (cancM.obj x))) (fstT.map (εD.inv.app (cancM.obj x))) :=
      Functor.isHomLift_map_of_comp_eq TwoFibreProductOver.fst_comp_eq
        (𝟙 (targetP.obj (cancM.obj x))) (εD.inv.app (cancM.obj x))
    have hb2 : targetP.obj (cancM.obj x) = Mq.pt.val.p.obj x := Functor.congr_obj hcancMstr x
    rw [hb2] at h2
    exact h2
  refine ⟨Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso
    { hom := Functor.whiskerLeft cancM (Functor.whiskerRight εD.inv fstT)
      inv := Functor.whiskerLeft cancM (Functor.whiskerRight εD.hom fstT)
      hom_inv_id := by
        ext x
        change fstT.map (εD.inv.app (cancM.obj x)) ≫
          fstT.map (εD.hom.app (cancM.obj x)) = _
        rw [← Functor.map_comp, Iso.inv_hom_id_app]
        exact fstT.map_id _
      inv_hom_id := by
        ext x
        change fstT.map (εD.hom.app (cancM.obj x)) ≫
          fstT.map (εD.inv.app (cancM.obj x)) = _
        rw [← Functor.map_comp, Iso.hom_inv_id_app]
        exact fstT.map_id _ } hvert)⟩

/-- **The smooth surjection `U ×_𝒴 V' ⟶ 𝒳 ×_𝒴 V'`.** In the situation of
`AlgebraicGeometry.Stack.exists_twoIso_cancelIteratedTwoFibreProduct`, with `a` moreover smooth
and surjective on objects, the apex of `(V ×_𝒴 V') ×_V U` carries a 1-morphism to the apex of
`𝒳 ×_𝒴 V'` which is representable by algebraic spaces, smooth and surjective, and which is
compatible with the two projections to the category of elements of `V'`.

The 1-morphism is the comparison of
`AlgebraicGeometry.Stack.exists_twoIso_cancelIteratedTwoFibreProduct` followed by the projection
of `(𝒳 ×_𝒴 V') ×_𝒳 U`, which is the base change of `a` (**Stacks 045C** and **06D7**); the
properties cross the comparison by
`AlgebraicGeometry.Stack.relativeProperty_of_forall_nonempty_equivalenceOver_fst`. -/
theorem exists_smoothSurjective_twoIso_iteratedTwoFibreProduct
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) {U V V' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : fibredCategory B S hS U ⟶ 𝒳) (b : fibredCategory B S hS V ⟶ 𝒴)
    (b' : fibredCategory B S hS V' ⟶ 𝒴) (h : U ⟶ V)
    (η : (associatedMap B S hS h).1 ≫ b ≅ a ≫ f)
    (ha : IsRelativelySmooth B S hS a)
    (hasurj : IsSurjectiveOnObjects B S hS (fibredCategory B S hS U).val.p 𝒳.val.p
      (CatFiberedInGroupoids.homFunctor a)) :
    ∃ (m : (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
              (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b' b).snd
              (associatedMap B S hS h).1).pt ⟶
            (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b' f).pt)
        (hm : IsRepresentableByAlgebraicSpaces B S hS m.hom),
      HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.smoothMorphismProperty B S hS) m hm ∧
        HasRelativeProperty.{u, u, u + 1, u} B S hS
          (Space.surjectiveMorphismProperty B S hS) m hm ∧
        Nonempty ((CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
              (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b' b).snd
              (associatedMap B S hS h).1).fst ≫
            (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b' b).fst ≅
          m ≫ (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b' f).fst) := by
  set Q : Bicategory.TwoCommSq b' f :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b' f with hQdef
  set Nq : Bicategory.TwoCommSq b' b :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b' b with hNqdef
  set Mq : Bicategory.TwoCommSq Nq.snd (associatedMap B S hS h).1 :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Nq.snd
      (associatedMap B S hS h).1 with hMqdef
  set Dq : Bicategory.TwoCommSq Q.snd a :=
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Q.snd a with hDqdef
  have hDq : Bicategory.IsTwoFibreProduct Dq :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} Q.snd a
  have hDfstRep : IsRepresentableByAlgebraicSpaces B S hS Dq.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS
      (fibredCategory B S hS U) 𝒳 Q.pt a Q.snd Dq hDq ha.1
  have hDfstSm : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.smoothMorphismProperty B S hS) Dq.fst hDfstRep :=
    hasRelativeProperty_baseChange.{u, u, u + 1, u} B S hS
      (Space.smoothMorphismProperty B S hS) (fibredCategory B S hS U) 𝒳 Q.pt a Q.snd Dq hDq
      ha.1 ha.2
  have haSu : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) a ha.1 :=
    (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u} B S hS a ha.1).1 hasurj
  have hDfstSu : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) Dq.fst hDfstRep :=
    hasRelativeProperty_baseChange.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) (fibredCategory B S hS U) 𝒳 Q.pt a Q.snd Dq hDq
      ha.1 haSu
  obtain ⟨dMor, hdEquiv, hθ⟩ :=
    exists_twoIso_cancelIteratedTwoFibreProduct B S hS f a b b' h η
  have heD : ∀ (W₀ : BigFppfOver B S hS)
      (y : BigFppfOver B W₀.left.1 W₀.left.2 ⥤ Q.pt.val.obj),
      y ⋙ Q.pt.val.p = Over.map W₀.hom →
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map W₀.hom) Mq.pt.val.p Q.pt.val.p y
          (CatFiberedInGroupoids.homFunctor (dMor ≫ Dq.fst)))
        (TwoFibreProductOver.fst (Over.map W₀.hom) Dq.pt.val.p Q.pt.val.p y
          (CatFiberedInGroupoids.homFunctor Dq.fst))) :=
    fun W₀ y hy => nonempty_equivalenceOver_fst_of_equivalence_source B S hS dMor.hom
      Dq.fst.hom W₀ y hy
  have hmRep : IsRepresentableByAlgebraicSpaces B S hS (dMor ≫ Dq.fst).hom :=
    isRepresentableByAlgebraicSpaces_of_forall_nonempty_equivalenceOver_fst heD hDfstRep
  refine ⟨dMor ≫ Dq.fst, hmRep,
    relativeProperty_of_forall_nonempty_equivalenceOver_fst B S hS
      (Space.smoothMorphismProperty B S hS) Dq.fst (dMor ≫ Dq.fst) heD hDfstSm,
    relativeProperty_of_forall_nonempty_equivalenceOver_fst B S hS
      (Space.surjectiveMorphismProperty B S hS) Dq.fst (dMor ≫ Dq.fst) heD hDfstSu,
    ⟨hθ.some ≪≫ (Bicategory.associator dMor Dq.fst Q.fst).symm⟩⟩

end AlgebraicGeometry.Stack

end
