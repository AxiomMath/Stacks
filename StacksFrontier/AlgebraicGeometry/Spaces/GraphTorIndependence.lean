module

public import
  StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.TorIndependenceBaseChange
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperFlatSingleDegreeRankLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceFinitePart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceComp

/-!
# Tor independence of the graph of a morphism to a flat scheme

Let `X` be an algebraic space over `S`, `u : U ⟶ X` an étale morphism from a scheme, `A` a scheme
flat over `S` and `j : U ⟶ A` a morphism. The graph `(u, j) : U ⟶ X ×_S A` is Tor independent
(Stacks 08IP) of every base change `(X ×_S A) ×_S S' ⟶ X ×_S A` along a morphism of schemes
`S' ⟶ S`. This is the case of Stacks 0CTQ used in the derived Chow lemma (Stacks 0CTR): the graph
factors as the graph `U ⟶ U ×_S A` of `j`, a morphism of schemes to which Stacks 0CTA applies,
followed by the étale base change `U ×_S A ⟶ X ×_S A` of `u`, which is flat.

## Main results

* `AlgebraicGeometry.Space.TorIndependent.of_isIso_comp`: Tor independence is invariant under an
  isomorphism of the first factor.
* `AlgebraicGeometry.isPullback_pullbackProductLift`: `(X ×_S S') ×_{S'} (Y ×_S S')` is the base
  change of `X ×_S Y` along `S' ⟶ S`.
* `AlgebraicGeometry.Space.torIndependent_graph_baseChange`: the Tor independence above.

## References

* [Stacks Project, Tag 0CTQ](https://stacks.math.columbia.edu/tag/0CTQ)
* [Stacks Project, Tag 0CTA](https://stacks.math.columbia.edu/tag/0CTA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- For `x : X ⟶ S`, `y : Y ⟶ S` and `s : S' ⟶ S`, the scheme `(X ×_S S') ×_{S'} (Y ×_S S')` with
its comparison map to `X ×_S Y` and its map to `S'` is the base change of `X ×_S Y` along `s`. -/
theorem isPullback_pullbackProductLift {S S' X Y : Scheme.{u}} (x : X ⟶ S) (y : Y ⟶ S)
    (s : S' ⟶ S) :
    IsPullback
      (pullback.lift
        (pullback.fst (pullback.snd x s) (pullback.snd y s) ≫ pullback.fst x s)
        (pullback.snd (pullback.snd x s) (pullback.snd y s) ≫ pullback.fst y s)
        (by simp only [Category.assoc, pullback.condition]
            rw [← Category.assoc, pullback.condition, Category.assoc]) : _ ⟶ pullback x y)
      (pullback.fst (pullback.snd x s) (pullback.snd y s) ≫ pullback.snd x s)
      (pullback.fst x y ≫ x) s := by
  refine IsPullback.paste_vert ?_ (IsPullback.of_hasPullback x s)
  refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback x y).flip
  rw [pullback.lift_snd, pullback.condition]
  exact (IsPullback.of_hasPullback (pullback.snd x s) (pullback.snd y s)).flip.paste_horiz
    (IsPullback.of_hasPullback y s)

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

set_option synthInstance.maxHeartbeats 400000 in
-- `HasPullbacks` for presheaves on the big fppf site needs a deep instance search
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_GraphTorIndependence :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_GraphTorIndependence
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **Tor independence is invariant under an isomorphism of the first factor.** -/
theorem TorIndependent.of_isIso_comp {X' X Y Bs : AlgebraicSpaces B S hS} (e : X' ⟶ X)
    [IsIso e.hom] (f : X ⟶ Bs) (g : Y ⟶ Bs)
    (h : TorIndependent X.2 Y.2 Bs.2 f.hom g.hom) :
    TorIndependent X'.2 Y.2 Bs.2 (e.hom ≫ f.hom) g.hom :=
  torIndependent_comp_of_isPullback B S hS e f g
    (V' := AlgebraicSpaces.fiberProduct B S hS f g) (ObjectProperty.homMk (pullback.fst _ _))
    (ObjectProperty.homMk (pullback.snd _ _)) (IsPullback.of_hasPullback _ _) h
    (torIndependent_of_isFlat_left e _ (isFlat_of_isEtale B S hS (isEtale_of_isIso B S hS e.hom)))

/-- Given a cartesian square `X' = X ×_S A` of algebraic spaces and a cartesian square
`P = Z ×_S A` of schemes, the lift `P ⟶ X'` of `v : Z ⟶ X` makes `P` the base change of `X'` along
`v`. -/
theorem isPullback_yoneda_lift {X X' : AlgebraicSpaces B S hS} {P Z A : BigFppfOver B S hS}
    (pX : X' ⟶ X) (pA : X'.1 ⟶ yoneda.obj A)
    (hX' : IsPullback pX.hom pA ((isTerminal_yoneda_obj_base B S hS).from X.1)
      (yoneda.map (Over.homMk A.hom : A ⟶ Over.mk (𝟙 (B.obj hS)))))
    (v : yoneda.obj Z ⟶ X.1) (f : P ⟶ Z) (g : P ⟶ A)
    (hP : IsPullback f g (Over.homMk Z.hom : Z ⟶ Over.mk (𝟙 (B.obj hS))) (Over.homMk A.hom)) :
    IsPullback (hX'.lift (yoneda.map f ≫ v) (yoneda.map g)
      ((isTerminal_yoneda_obj_base B S hS).hom_ext _ _)) (yoneda.map f) pX.hom v := by
  refine IsPullback.of_right ?_ (hX'.lift_fst _ _ _) hX'.flip
  rw [hX'.lift_snd, show v ≫ (isTerminal_yoneda_obj_base B S hS).from X.1 =
      yoneda.map (Over.homMk Z.hom : Z ⟶ Over.mk (𝟙 (B.obj hS))) from
    (isTerminal_yoneda_obj_base B S hS).hom_ext _ _]
  exact (hP.map yoneda).flip

/-- Let `u : U ⟶ X` be étale, `X ×_S A` a cartesian square `(pX, pA)`, `P' = U ×_S A` with
a section `gV` of its first projection, and `κ : Y' ⟶ X ×_S A` the base change of
`X ×_S A ⟶ S` along `Y ⟶ S`, with `P = P' ×_S Y`. If `i` is `gV` followed by the base change
`P' ⟶ X ×_S A` of `u`, and `gV` is Tor independent of `P ⟶ P'`, then `i` is Tor independent of
`κ`. -/
theorem torIndependent_of_graph_factorization {Xs Bs Wsp Y' : AlgebraicSpaces B S hS}
    {Zs As Ys P' P : BigFppfOver B S hS}
    (u : yoneda.obj Zs ⟶ Xs.1) (hu : IsEtale B S hS u) (jA : Zs ⟶ As)
    (pX : Bs ⟶ Xs) (pA : Bs.1 ⟶ yoneda.obj As)
    (hBs : IsPullback pX.hom pA ((isTerminal_yoneda_obj_base B S hS).from Xs.1)
      (yoneda.map (Over.homMk As.hom : As ⟶ Over.mk (𝟙 (B.obj hS)))))
    (i : Wsp ⟶ Bs) (eW : yoneda.obj Zs ≅ Wsp.1) (hiX : eW.hom ≫ i.hom ≫ pX.hom = u)
    (hiA : eW.hom ≫ i.hom ≫ pA = yoneda.map jA)
    (κ : Y' ⟶ Bs) (πY : Y'.1 ⟶ yoneda.obj Ys)
    (hY : IsPullback κ.hom πY ((isTerminal_yoneda_obj_base B S hS).from Bs.1)
      (yoneda.map (Over.homMk Ys.hom : Ys ⟶ Over.mk (𝟙 (B.obj hS)))))
    (fst : P' ⟶ Zs) (snd : P' ⟶ As) (gV : Zs ⟶ P') (gU : P ⟶ P') (prY : P ⟶ Ys)
    (hgVfst : gV ≫ fst = 𝟙 Zs) (hgVsnd : gV ≫ snd = jA)
    (I1 : IsPullback fst snd (Over.homMk Zs.hom : Zs ⟶ Over.mk (𝟙 (B.obj hS)))
      (Over.homMk As.hom))
    (I2 : IsPullback gU prY (Over.homMk P'.hom : P' ⟶ Over.mk (𝟙 (B.obj hS)))
      (Over.homMk Ys.hom))
    (hT : TorIndependent (isAlgebraicSpace_yoneda B S hS Zs) (isAlgebraicSpace_yoneda B S hS P)
      (isAlgebraicSpace_yoneda B S hS P') (yoneda.map gV) (yoneda.map gU)) :
    TorIndependent Wsp.2 Y'.2 Bs.2 i.hom κ.hom := by
  have hterm := isTerminal_yoneda_obj_base B S hS
  let e : yoneda.obj P' ⟶ Bs.1 := hBs.lift (yoneda.map fst ≫ u) (yoneda.map snd)
    (hterm.hom_ext _ _)
  have heX : e ≫ pX.hom = yoneda.map fst ≫ u := hBs.lift_fst _ _ _
  have heA : e ≫ pA = yoneda.map snd := hBs.lift_snd _ _ _
  have heEt : IsEtale B S hS e :=
    isEtale_of_isPullback_of_isAlgebraicSpace B S hS (isPullback_yoneda_lift pX pA hBs u fst snd I1)
      (isAlgebraicSpace_yoneda B S hS P') Bs.2 (isAlgebraicSpace_yoneda B S hS Zs) Xs.2 hu
  have hi : i.hom = eW.inv ≫ yoneda.map gV ≫ e := by
    refine hBs.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, heX, ← Category.assoc (yoneda.map gV),
        ← Functor.map_comp, hgVfst, CategoryTheory.Functor.map_id, Category.id_comp,
        ← hiX, Iso.inv_hom_id_assoc]
    · rw [Category.assoc, Category.assoc, heA, ← Functor.map_comp, hgVsnd, ← hiA,
        Iso.inv_hom_id_assoc]
  let π₂ : yoneda.obj P ⟶ Y'.1 := hY.lift (yoneda.map gU ≫ e) (yoneda.map prY)
    (hterm.hom_ext _ _)
  let Zsp : AlgebraicSpaces B S hS := ⟨yoneda.obj Zs, isAlgebraicSpace_yoneda B S hS Zs⟩
  let P'sp : AlgebraicSpaces B S hS := ⟨yoneda.obj P', isAlgebraicSpace_yoneda B S hS P'⟩
  let Psp : AlgebraicSpaces B S hS := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩
  let gVsp : Zsp ⟶ P'sp := ObjectProperty.homMk (yoneda.map gV)
  let esp : P'sp ⟶ Bs := ObjectProperty.homMk e
  have hcomp := torIndependent_comp_of_isPullback B S hS gVsp esp κ
    (ObjectProperty.homMk (yoneda.map gU) : Psp ⟶ P'sp) (ObjectProperty.homMk π₂ : Psp ⟶ Y')
    (isPullback_yoneda_lift κ πY hY e gU prY I2).flip
    (torIndependent_of_isFlat_left esp κ (isFlat_of_isEtale B S hS heEt)) hT
  have : IsIso (ObjectProperty.homMk eW.inv : Wsp ⟶ Zsp).hom := inferInstanceAs (IsIso eW.inv)
  rw [hi]
  exact TorIndependent.of_isIso_comp (X' := Wsp) (X := Zsp) (ObjectProperty.homMk eW.inv)
    (gVsp ≫ esp) κ hcomp

/-- **Stacks 0CTQ for the graph of a morphism to a flat scheme.** Let `u : U ⟶ X` be an étale
morphism from a scheme to an algebraic space over `S`, `A` a scheme flat over `S` and
`j : U ⟶ A` a morphism over `S`. Let `X ×_S A` be given by a cartesian square `(pX, pA)`, let
`i : W ⟶ X ×_S A` be the graph `(u, j)` read through an isomorphism `W ≅ U`, and let
`κ : Y' ⟶ X ×_S A` be the base change of `X ×_S A ⟶ S` along a morphism of schemes `S' ⟶ S`.
Then `W` and `Y'` are Tor independent over `X ×_S A`. -/
theorem torIndependent_graph_baseChange {Xs Bs Wsp Y' : AlgebraicSpaces B S hS}
    (Zs As Ys : BigFppfOver B S hS) [hAflat : Flat As.hom.hom]
    (u : yoneda.obj Zs ⟶ Xs.1) (hu : IsEtale B S hS u) (jA : Zs ⟶ As)
    (pX : Bs ⟶ Xs) (pA : Bs.1 ⟶ yoneda.obj As)
    (hBs : IsPullback pX.hom pA ((isTerminal_yoneda_obj_base B S hS).from Xs.1)
      (yoneda.map (Over.homMk As.hom : As ⟶ Over.mk (𝟙 (B.obj hS)))))
    (i : Wsp ⟶ Bs) (eW : yoneda.obj Zs ≅ Wsp.1) (hiX : eW.hom ≫ i.hom ≫ pX.hom = u)
    (hiA : eW.hom ≫ i.hom ≫ pA = yoneda.map jA)
    (κ : Y' ⟶ Bs) (πY : Y'.1 ⟶ yoneda.obj Ys)
    (hY : IsPullback κ.hom πY ((isTerminal_yoneda_obj_base B S hS).from Bs.1)
      (yoneda.map (Over.homMk Ys.hom : Ys ⟶ Over.mk (𝟙 (B.obj hS))))) :
    TorIndependent Wsp.2 Y'.2 Bs.2 i.hom κ.hom := by
  let x : (BigFppfOver.toScheme B S hS).obj Zs ⟶ S := Zs.hom.hom
  let y : (BigFppfOver.toScheme B S hS).obj As ⟶ S := As.hom.hom
  let s : (BigFppfOver.toScheme B S hS).obj Ys ⟶ S := Ys.hom.hom
  have hz : 𝟙 _ ≫ x = (BigFppfOver.toScheme B S hS).map jA ≫ y :=
    (Category.id_comp x).trans (congrArg (fun k => k.hom) (Over.w jA)).symm
  have hP : B.Contains (pullback (pullback.snd x s) (pullback.snd y s)) :=
    Scheme.size_pullback_lt _ _ (Scheme.size_pullback_lt x s Zs.left.property Ys.left.property)
      (Scheme.size_pullback_lt y s As.left.property Ys.left.property)
  have hsq := isPullback_pullbackProductLift x y s
  let P's : BigFppfOver B S hS :=
    siteObject B S hS (Scheme.size_pullback_lt x y Zs.left.property As.left.property)
      (pullback.fst x y ≫ x)
  let Ps : BigFppfOver B S hS := siteObject B S hS hP
    (pullback.fst (pullback.snd x s) (pullback.snd y s) ≫ pullback.snd x s ≫ s)
  let gU : Ps ⟶ P's := Over.homMk (ObjectProperty.homMk (pullback.lift
      (pullback.fst (pullback.snd x s) (pullback.snd y s) ≫ pullback.fst x s)
      (pullback.snd (pullback.snd x s) (pullback.snd y s) ≫ pullback.fst y s)
      (by simp only [Category.assoc, pullback.condition, pullback.condition_assoc])))
    (by ext1; exact hsq.w.trans (Category.assoc _ _ _))
  let gV : Zs ⟶ P's := Over.homMk (ObjectProperty.homMk (pullback.lift (𝟙 _)
      ((BigFppfOver.toScheme B S hS).map jA) hz))
    (by ext1; exact (pullback.lift_fst_assoc _ _ _ _).trans (Category.id_comp _))
  let fst' : P's ⟶ Zs := Over.homMk (ObjectProperty.homMk (pullback.fst x y)) (by ext1; rfl)
  let snd' : P's ⟶ As := Over.homMk (ObjectProperty.homMk (pullback.snd x y))
    (by ext1; exact (pullback.condition (f := x) (g := y)).symm)
  let prY : Ps ⟶ Ys := Over.homMk (ObjectProperty.homMk
      (pullback.fst (pullback.snd x s) (pullback.snd y s) ≫ pullback.snd x s))
    (by ext1; exact Category.assoc _ _ _)
  exact torIndependent_of_graph_factorization u hu jA pX pA hBs i eW hiX hiA κ πY hY
    fst' snd' gV gU prY (by ext1; ext1; exact pullback.lift_fst _ _ _)
    (by ext1; ext1; exact pullback.lift_snd _ _ _)
    (IsPullback.of_map (BigFppfOver.toScheme B S hS) (by ext1; ext1; exact pullback.condition)
      (IsPullback.of_hasPullback x y))
    (IsPullback.of_map (BigFppfOver.toScheme B S hS) (by ext1; ext1; exact hsq.w) hsq)
    (torIndependent_yoneda_of_torIndependent_scheme B S hS gU gV
      (torIndependent_pullback_product_of_flat s x y (𝟙 _)
        ((BigFppfOver.toScheme B S hS).map jA) hz)).symm

end Space

end AlgebraicGeometry

end
