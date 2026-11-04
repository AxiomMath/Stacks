module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingMorphism
public import StacksFrontier.CategoryTheory.Sites.Stackification.TwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# Limit preserving 1-morphisms are stable under composition (Stacks 0CMU)

If `p : 𝒳 ⟶ 𝒴` and `q : 𝒴 ⟶ 𝒵` are limit preserving 1-morphisms of categories fibred in
groupoids over the big fppf category of a scheme `S`, then so is `p ≫ q`.

## Main results

* `AlgebraicGeometry.Stack.isLimitPreserving_comp`: **Stacks 0CMU**.

## Implementation notes

The square of Stacks 0CMR for `p ≫ q` is the horizontal pasting of the square for `p` on top of
the square for `q`, so the mathematical content is the pasting law for 2-fibre products,
`CategoryTheory.Bicategory.isTwoFibreProduct_pasteFst`, applied in `Cat`. What takes work is
that the two squares do not paste on the nose:

* the bottom edge of the pasted rectangle is the composite of the two fibre functors induced by
  `p` and by `q`, while the square for `p ≫ q` has the single fibre functor induced by `p ≫ q`
  as its bottom edge. The two are equal, because `CategoryTheory.Functor.IsFibredOneMorphism` is
  a proposition and so the compatibility proofs of `p ≫ q` and of the composite agree, but only
  as an equality of functors, not definitionally; `AlgebraicGeometry.Stack.twoCommSq_congr_fst`
  transports a 2-fibre product along such an equality.
* the induced functor out of the colimit of the stage fibres is the colimit of the
  componentwise maps, and the colimit of a composite of natural transformations is the composite
  of the colimits, which is where `colimit.hom_ext` is used.
* the 2-cell of the pasted square is pinned to the base-change comparison of `p ≫ q`, and that
  comparison is the composite of the comparisons of `p` and `q`
  (`CategoryTheory.Functor.IsFibredOneMorphism.mapPullbackFiberIso_comp_inv`). The pinning is a
  heterogeneous equality, so it is transported with the three `HEq` helpers of this file rather
  than by `rw`.

The composite of the two 2-cells is formed in a single universe reached by `AsSmall`, and
`AlgebraicGeometry.Stack.asSmall_conj_comp` is the cancellation
`AsSmall.up ⋙ AsSmall.down = 𝟭` in the middle of such a composite; it is an equality of
functors between types in different universes, hence proved with `CategoryTheory.Functor.hext`.

## References

* [Stacks Project, Tag 0CMU](https://stacks.math.columbia.edu/tag/0CMU)
* [Stacks Project, Tag 0CMR](https://stacks.math.columbia.edu/tag/0CMR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Opposite

namespace AlgebraicGeometry.Stack

universe u v w uX vX

/-- The colimit of a composite of natural transformations is the composite of their colimits. -/
private lemma colimMap_comp_colimMap
    {I : Type v} [Category.{w} I] {C : Type*} [Category C]
    {F G H : Iᵒᵖ ⥤ C} [HasColimit F] [HasColimit G] [HasColimit H]
    (α : F ⟶ G) (β : G ⟶ H) :
    colimMap α ≫ colimMap β = colimMap (α ≫ β) := by
  apply colimit.hom_ext
  intro i
  simp only [ι_colimMap_assoc, ι_colimMap, NatTrans.comp_app, Category.assoc]

/-- The colimit of a morphism of diagrams in `Cat` acts on the image of a stage by the stage
component. -/
private lemma colimMap_obj_ι
    {I : Type v} [Category.{w} I] {F G : Iᵒᵖ ⥤ Cat.{vX, uX}} [HasColimit F] [HasColimit G]
    (T : F ⟶ G) (j : Iᵒᵖ) (x : F.obj j) :
    (colimMap T).toFunctor.obj ((colimit.ι F j).toFunctor.obj x) =
      (colimit.ι G j).toFunctor.obj ((T.app j).toFunctor.obj x) :=
  Functor.congr_obj (congrArg Cat.Hom.toFunctor (ι_colimMap T j)) x

/-- Conjugating two functors by the universe-raising equivalence `AsSmall` one after the other
is the same as conjugating their composite. -/
private lemma asSmall_conj_comp {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) :
    AsSmall.down ⋙ F ⋙ AsSmall.up ⋙ AsSmall.down ⋙ G ⋙ AsSmall.up =
      AsSmall.down ⋙ F ⋙ G ⋙ AsSmall.up :=
  Functor.hext (fun _ => rfl) fun _ _ _ => heq_of_eq rfl

/-- A 2-fibre product in `Cat` over a cospan whose first leg is replaced by a 1-morphism with the
same underlying functor is again a 2-fibre product, after composing the filler with the
corresponding `eqToIso`. -/
private noncomputable def twoCommSq_congr_fst
    {X Y Z : Cat.{v, u}} {g g' : Z ⟶ Y} {f : X ⟶ Y}
    (e : g.toFunctor = g'.toFunctor) (P : TwoCommSq g' f)
    (hP : IsTwoFibreProduct P) :
    IsTwoFibreProduct
      ({ pt := P.pt, fst := P.fst, snd := P.snd,
         iso := Cat.Hom.isoMk
           (eqToIso (congrArg (fun F => P.fst.toFunctor ⋙ F) e) ≪≫
             Cat.Hom.toNatIso P.iso) } : TwoCommSq g f) := by
  have h : g = g' := Cat.Hom.ext e
  subst g'
  simpa using hP

/-- Precomposing a natural isomorphism with an `eqToIso` does not change the image of its
components under a functor. -/
private lemma map_eqToIso_trans_app_heq
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F F' G : C ⥤ D} (e : F = F') (η : F' ≅ G) (K : D ⥤ E) (x : C) :
    HEq (K.map ((eqToIso e ≪≫ η).app x).hom) (K.map (η.app x).hom) := by
  subst F'
  simp

/-- A functor carries a heterogeneous equality of morphisms to one of their images. -/
private lemma functor_map_heq
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {x y x' y' : C} (hx : x = x') (hy : y = y')
    {f : x ⟶ y} {f' : x' ⟶ y'} (h : HEq f f') : HEq (F.map f) (F.map f') := by
  subst x' y'
  cases h
  rfl

/-- The components of a natural isomorphism at equal objects have heterogeneously equal
images. -/
private lemma natIso_app_map_heq
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F G : C ⥤ D} (η : F ≅ G) (K : D ⥤ E)
    {x y : C} (h : x = y) :
    HEq (K.map (η.app x).hom) (K.map (η.app y).hom) := by
  subst y
  rfl

/-- **Stacks 0CMU.** The composite of two limit preserving 1-morphisms of categories fibred in
groupoids over the big fppf category of `S` is limit preserving: the square of Stacks 0CMR for
the composite is the horizontal pasting of the two given 2-cartesian squares. -/
@[stacks 0CMU]
theorem isLimitPreserving_comp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, vX, u + 1, uX} (BigFppfOver B S hS)}
    (p : 𝒳 ⟶ 𝒴) (q : 𝒴 ⟶ 𝒵)
    (hp : IsLimitPreserving.{u, v, w, uX, vX} B S hS p)
    (hq : IsLimitPreserving.{u, v, w, uX, vX} B S hS q) :
    IsLimitPreserving.{u, v, w, uX, vX} B S hS (p ≫ q) := by
  dsimp [IsLimitPreserving] at hp hq ⊢
  intro I hI hIc D c hc
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
  rcases hp I D c hc with ⟨Tp, Hp, ηp, hTp, hHp, hηp, hFp⟩
  rcases hq I D c hc with ⟨Tq, Hq, ηq, hTq, hHq, hηq, hFq⟩
  let E := D ⋙ BigAffineFppf.inclusion B S hS
  let d := (BigAffineFppf.inclusion B S hS).mapCone c
  let hmapP := isFibredOneMorphism B S hS p
  let hmapQ := isFibredOneMorphism B S hS q
  have hcompEq : CatFiberedInGroupoids.homFunctor_comp_p (p ≫ q) =
      (hmapP.comp hmapQ).comp_eq := by
    apply Subsingleton.elim
  have hbaseAt (V : BigFppfOver B S hS) :
      Functor.fiberFunctorOfCompEq
          (CatFiberedInGroupoids.homFunctor_comp_p (p ≫ q)) V =
        Functor.fiberFunctorOfCompEq
          (CatFiberedInGroupoids.homFunctor_comp_p p) V ⋙
          Functor.fiberFunctorOfCompEq
            (CatFiberedInGroupoids.homFunctor_comp_p q) V := by
    rw [hcompEq]
    exact Functor.hext (fun _ => rfl) fun _ _ _ => heq_of_eq (Functor.Fiber.hom_ext rfl)
  have hsource :
      (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up ⋙ AsSmall.down ⋙
        Functor.fiberFunctorOfCompEq
          (CatFiberedInGroupoids.homFunctor_comp_p (p ≫ q)) c.pt.obj ⋙ AsSmall.up) =
        (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up) ⋙
          (AsSmall.down ⋙ Functor.fiberFunctorOfCompEq
            (CatFiberedInGroupoids.homFunctor_comp_p p) c.pt.obj ⋙ AsSmall.up) ⋙
          (AsSmall.down ⋙ Functor.fiberFunctorOfCompEq
            (CatFiberedInGroupoids.homFunctor_comp_p q) c.pt.obj ⋙ AsSmall.up) := by
    rw [hbaseAt]
    simpa only [Functor.assoc] using
      congrArg (fun F => Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up ⋙ F)
        (asSmall_conj_comp
          (Functor.fiberFunctorOfCompEq
            (CatFiberedInGroupoids.homFunctor_comp_p p) c.pt.obj)
          (Functor.fiberFunctorOfCompEq
            (CatFiberedInGroupoids.homFunctor_comp_p q) c.pt.obj)).symm
  let g : Cat.Hom _ _ :=
    (AsSmall.down.{vX, uX, max v w vX (u + 1) uX u} ⋙
      Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p q) d.pt ⋙
      AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}).toCatHom
  let f : Cat.Hom _ _ :=
    (Deformation.Artin.colimitComparison 𝒵.val.p E d ⋙
      AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}).toCatHom
  let k : Cat.Hom _ _ :=
    (AsSmall.down.{vX, uX, max v w vX (u + 1) uX u} ⋙
      Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p p) d.pt ⋙
      AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}).toCatHom
  let H := Hp ⋙ Hq
  let SqQ : TwoCommSq g f :=
    { pt := colimit (Deformation.Artin.fiberDiagram 𝒴.val.p E)
      fst := (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙
        AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}).toCatHom
      snd := Hq.toCatHom
      iso := Cat.Hom.isoMk ηq }
  have hSqQ : IsTwoFibreProduct SqQ :=
    Classical.choice (by simpa [SqQ, g, f, E, d] using hFq)
  let SqP : TwoCommSq k SqQ.fst :=
    { pt := colimit (Deformation.Artin.fiberDiagram 𝒳.val.p E)
      fst := (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙
        AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}).toCatHom
      snd := Hp.toCatHom
      iso := Cat.Hom.isoMk ηp }
  have hSqP : IsTwoFibreProduct SqP :=
    Classical.choice (by simpa [SqP, SqQ, k, E, d] using hFp)
  let R : TwoCommSq (k ≫ g) f :=
    { pt := colimit (Deformation.Artin.fiberDiagram 𝒳.val.p E)
      fst := (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙
        AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}).toCatHom
      snd := Hp.toCatHom ≫ Hq.toCatHom
      iso := (α_ SqP.fst k g).symm ≪≫ whiskerRightIso SqP.iso g ≪≫
        α_ SqP.snd SqQ.fst g ≪≫ whiskerLeftIso SqP.snd SqQ.iso ≪≫
          (α_ SqP.snd SqQ.snd f).symm }
  have hR : IsTwoFibreProduct R :=
    isTwoFibreProduct_pasteFst SqQ hSqQ SqP hSqP
  have hsourceR :
      (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up ⋙ AsSmall.down ⋙
        Functor.fiberFunctorOfCompEq
          (CatFiberedInGroupoids.homFunctor_comp_p (p ≫ q)) c.pt.obj ⋙ AsSmall.up) =
        (R.fst ≫ (k ≫ g)).toFunctor := by
    simpa [R, SqP, SqQ, k, g, E, d, BigAffineFppf.inclusion,
      Functor.mapCone_pt, Functor.assoc, Category.assoc] using hsource
  let η :
      (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up ⋙ AsSmall.down ⋙
        Functor.fiberFunctorOfCompEq
          (CatFiberedInGroupoids.homFunctor_comp_p (p ≫ q)) c.pt.obj ⋙ AsSmall.up) ≅
        H ⋙ Deformation.Artin.colimitComparison 𝒵.val.p E d ⋙ AsSmall.up :=
    eqToIso hsourceR ≪≫ Cat.Hom.toNatIso R.iso
  let T := Tp ≫ Tq
  refine ⟨T, H, η, ?_, ?_, ?_, ?_⟩
  · intro i
    have hPQ : isFibredOneMorphism B S hS (p ≫ q) = hmapP.comp hmapQ :=
      Subsingleton.elim _ _
    have hstageObj (x : 𝒳.val.p.SplitFiber (E.obj i)) :
        (Functor.fiberFunctorOfCompEq
            (CatFiberedInGroupoids.homFunctor_comp_p q) x.base).obj
            ((Functor.fiberFunctorOfCompEq
              (CatFiberedInGroupoids.homFunctor_comp_p p) x.base).obj x.obj) =
          (Functor.fiberFunctorOfCompEq
            (CatFiberedInGroupoids.homFunctor_comp_p (p ≫ q)) x.base).obj x.obj := by
      simpa only [Functor.comp_obj] using
        (Functor.congr_obj (hbaseAt x.base) x.obj).symm
    have hsplit :
        splitFiberMap B S hS p (E.obj i) ⋙ splitFiberMap B S hS q (E.obj i) =
          splitFiberMap B S hS (p ≫ q) (E.obj i) := by
      apply CategoryTheory.Functor.hext
      · intro x
        simpa [splitFiberMap, hPQ] using hstageObj x
      · intro x y α
        have hbaseX := hbaseAt x.base
        have hbaseY := hbaseAt y.base
        apply heq_of_eq
        apply CategoryTheory.Functor.SplitFiber.toFiberHom_injective
        dsimp only [splitFiberMap]
        simp only [Functor.comp_map, Functor.SplitFiber.toFiberHom_ofFiberHom]
        rw [hPQ]
        cases hbaseX
        cases hbaseY
        change
          (hmapQ.mapPullbackFiberIso
              ((Functor.fiberFunctorOfCompEq hmapP.comp_eq x.base).obj x.obj) x.hom).hom ≫
            (Functor.fiberFunctorOfCompEq hmapQ.comp_eq (E.obj i)).map
              ((hmapP.mapPullbackFiberIso x.obj x.hom).hom ≫
                (Functor.fiberFunctorOfCompEq hmapP.comp_eq (E.obj i)).map
                  (Functor.SplitFiber.toFiberHom α) ≫
                (hmapP.mapPullbackFiberIso y.obj y.hom).inv) ≫
            (hmapQ.mapPullbackFiberIso
              ((Functor.fiberFunctorOfCompEq hmapP.comp_eq y.base).obj y.obj) y.hom).inv =
          ((hmapP.comp hmapQ).mapPullbackFiberIso x.obj x.hom).hom ≫
            (Functor.fiberFunctorOfCompEq (hmapP.comp hmapQ).comp_eq (E.obj i)).map
              (Functor.SplitFiber.toFiberHom α) ≫
            ((hmapP.comp hmapQ).mapPullbackFiberIso y.obj y.hom).inv
        simp only [Functor.map_comp, Category.assoc]
        rw [Functor.IsFibredOneMorphism.mapPullbackFiberIso_comp hmapP hmapQ x.obj x.hom]
        rw [Functor.IsFibredOneMorphism.fiberFunctorOfCompEq_comp_map hmapP hmapQ
          (Functor.SplitFiber.toFiberHom α)]
        rw [Functor.IsFibredOneMorphism.mapPullbackFiberIso_comp_inv hmapP hmapQ y.obj y.hom]
        simp only [Category.assoc]
    show Tp.app (op i) ≫ Tq.app (op i) = _
    rw [hTp i, hTq i]
    apply Cat.Hom.ext
    show (AsSmall.down.{vX, max (u + 1) uX, max v w} ⋙
        splitFiberMap B S hS p (E.obj i) ⋙
        AsSmall.up.{vX, max (u + 1) uX, max v w} ⋙
          AsSmall.down.{vX, max (u + 1) uX, max v w} ⋙
          splitFiberMap B S hS q (E.obj i) ⋙
          AsSmall.up.{vX, max (u + 1) uX, max v w}) =
      (AsSmall.down.{vX, max (u + 1) uX, max v w} ⋙
        splitFiberMap B S hS (p ≫ q) (E.obj i) ⋙
        AsSmall.up.{vX, max (u + 1) uX, max v w})
    simpa only [asSmall_conj_comp, Functor.assoc] using
      congrArg (fun F => AsSmall.down.{vX, max (u + 1) uX, max v w} ⋙ F ⋙
        AsSmall.up.{vX, max (u + 1) uX, max v w}) hsplit
  · dsimp only [H, T]
    rw [hHp, hHq]
    show (colimMap Tp ≫ colimMap Tq).toFunctor = (colimMap (Tp ≫ Tq)).toFunctor
    exact congrArg Cat.Hom.toFunctor (colimMap_comp_colimMap Tp Tq)
  · intro i x
    let a := (colimit.ι (Deformation.Artin.fiberDiagram 𝒳.val.p E)
      (op i)).toFunctor.obj (AsSmall.up.{vX, max (u + 1) uX, max v w}.obj x)
    let y := (splitFiberMap B S hS p (E.obj i)).obj x
    let b := (colimit.ι (Deformation.Artin.fiberDiagram 𝒴.val.p E)
      (op i)).toFunctor.obj (AsSmall.up.{vX, max (u + 1) uX, max v w}.obj y)
    have hab : Hp.obj a = b := by
      rw [hHp]
      refine (colimMap_obj_ι Tp (op i) _).trans ?_
      rw [hTp i]
      rfl
    have hX := Functor.congr_obj
      (Deformation.Artin.colimitComparison_ι 𝒳.val.p E d i)
        (AsSmall.up.{vX, max (u + 1) uX, max v w}.obj x)
    have hY := Functor.congr_obj
      (Deformation.Artin.colimitComparison_ι 𝒴.val.p E d i)
        (AsSmall.up.{vX, max (u + 1) uX, max v w}.obj y)
    show HEq (AsSmall.down.{vX, uX, max v w vX (u + 1) uX u}.map
      (((eqToIso hsourceR ≪≫ Cat.Hom.toNatIso R.iso).app a).hom)) _
    apply HEq.trans (map_eqToIso_trans_app_heq hsourceR _
      AsSmall.down.{vX, uX, max v w vX (u + 1) uX u} a)
    simp only [Cat.coe_of, Cat.of_α, Functor.toCatHom_toFunctor, Cat.Hom.comp_toFunctor,
      Functor.comp_obj, Cat.Hom.toNatIso, Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom,
      Cat.Hom.isoMk_hom, whiskerLeftIso_hom, Cat.Hom.toNatTrans_comp,
      Cat.associator_inv_toNatTrans, Cat.whiskerRight_toNatTrans, NatTrans.toCatHom₂_toNatTrans,
      Cat.associator_hom_toNatTrans, Cat.whiskerLeft_toNatTrans, Iso.trans_inv, Iso.symm_inv,
      whiskerLeftIso_inv, Cat.Hom.isoMk_inv, Category.assoc, whiskerRightIso_inv, Iso.app_hom,
      NatTrans.comp_app, Functor.associator_inv_app, Functor.whiskerRight_app, Functor.comp_map,
      AsSmall.down_map, Functor.associator_hom_app, Functor.whiskerLeft_app, Category.comp_id,
      Category.id_comp, g, R, SqQ, SqP]
    have hX' : (Deformation.Artin.colimitComparison 𝒳.val.p E d).obj a =
        Functor.pullbackFiber 𝒳.val.p x.obj (d.π.app i ≫ x.hom) := hX
    have hY' : (Deformation.Artin.colimitComparison 𝒴.val.p E d).obj (Hp.obj a) =
        Functor.pullbackFiber 𝒴.val.p y.obj (d.π.app i ≫ y.hom) := by
      rw [hab]
      exact hY
    let z := (splitFiberMap B S hS q (E.obj i)).obj y
    have hbc : Hq.obj b =
        (colimit.ι (Deformation.Artin.fiberDiagram 𝒵.val.p E) (op i)).toFunctor.obj
            (AsSmall.up.{vX, max (u + 1) uX, max v w}.obj z) := by
      rw [hHq]
      refine (colimMap_obj_ι Tq (op i) _).trans ?_
      rw [hTq i]
      rfl
    have hZ : (Deformation.Artin.colimitComparison 𝒵.val.p E d).obj (Hq.obj (Hp.obj a)) =
        Functor.pullbackFiber 𝒵.val.p z.obj (d.π.app i ≫ z.hom) := by
      rw [hab, hbc]
      exact Functor.congr_obj (Deformation.Artin.colimitComparison_ι 𝒵.val.p E d i)
        (AsSmall.up.{vX, max (u + 1) uX, max v w}.obj z)
    refine HEq.trans ?_ (heq_of_eq
      (Functor.IsFibredOneMorphism.mapPullbackFiberIso_comp_inv
        hmapP hmapQ x.obj (d.π.app i ≫ x.hom)).symm)
    let fp := Functor.fiberFunctorOfCompEq hmapP.comp_eq d.pt
    let fq := Functor.fiberFunctorOfCompEq hmapQ.comp_eq d.pt
    show HEq (fq.map (AsSmall.down.map (ηp.app a).hom) ≫
        AsSmall.down.map (ηq.app (Hp.obj a)).hom)
      (fq.map (hmapP.mapPullbackFiberIso x.obj (d.π.app i ≫ x.hom)).inv ≫
        (hmapQ.mapPullbackFiberIso y.obj (d.π.app i ≫ y.hom)).inv)
    apply heq_comp (congrArg (fun t => fq.obj (fp.obj t)) hX')
      (congrArg fq.obj hY') hZ
    · exact functor_map_heq fq (congrArg fp.obj hX') hY' (hηp i x)
    · exact (natIso_app_map_heq ηq AsSmall.down hab).trans (hηq i y)
  · have hbottom :
        (AsSmall.down.{vX, uX, max v w vX (u + 1) uX u} ⋙ Functor.fiberFunctorOfCompEq
          (CatFiberedInGroupoids.homFunctor_comp_p (p ≫ q)) d.pt ⋙
          AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}) = k.toFunctor ⋙ g.toFunctor := by
      show (AsSmall.down.{vX, uX, max v w vX (u + 1) uX u} ⋙ Functor.fiberFunctorOfCompEq
          (CatFiberedInGroupoids.homFunctor_comp_p (p ≫ q)) d.pt ⋙
          AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}) =
        (AsSmall.down.{vX, uX, max v w vX (u + 1) uX u} ⋙ Functor.fiberFunctorOfCompEq
          (CatFiberedInGroupoids.homFunctor_comp_p p) d.pt ⋙
            AsSmall.up.{vX, uX, max v w vX (u + 1) uX u}) ⋙
        (AsSmall.down.{vX, uX, max v w vX (u + 1) uX u} ⋙ Functor.fiberFunctorOfCompEq
          (CatFiberedInGroupoids.homFunctor_comp_p q) d.pt ⋙
            AsSmall.up.{vX, uX, max v w vX (u + 1) uX u})
      rw [hbaseAt]
      simpa only [Functor.assoc] using
        (asSmall_conj_comp
          (Functor.fiberFunctorOfCompEq
            (CatFiberedInGroupoids.homFunctor_comp_p p) d.pt)
          (Functor.fiberFunctorOfCompEq
            (CatFiberedInGroupoids.homFunctor_comp_p q) d.pt)).symm
    exact ⟨twoCommSq_congr_fst hbottom R hR⟩

end AlgebraicGeometry.Stack

end
