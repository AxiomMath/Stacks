module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.OrdinaryLocality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.OrdinaryLocality

/-!
# The sectionwise right-square comparison and the cube of comparisons for Stacks 0EZR

`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.OrdinaryLocality` sets up the
statement of the first part of Stacks 0EZR for sheaves of sets: the base change map, the data of
the étale-local diagram, and the comparison `rightSquare` of the two composite direct images
around a commutative square of schemes.  This file proves two facts about those comparisons.

* `rightSquare_app`: **the right-square comparison on sections is the contravariant map of the
  site comparison** `siteSquare`.
* `rightSquare_cube`: **the cube of right-square comparisons commutes** — stacking the outer
  square on the `i`-th upper square gives the same rectangle as stacking the `i`-th local square
  on the `i`-th lower square.  This is the cube hypothesis that `isIso_map_mate_of_cube` of
  `OrdinaryLocality` consumes.

Both are private to the construction, as the comparisons themselves are; the file reaches them
through `import all`.  No part of Stacks 0EZR is concluded here.

## Implementation notes

`OrdinaryLocality` splits the sectionwise formula for `rightSquare` into two halves,
`rightSquare_app_eq` and `pushComp₃_app_hom_app_map`.  Gluing those two halves into
`rightSquare_app` costs nothing once the transport is given a name of its own, `pushCongrHom`.
What the kernel cannot pay for is not the glue and not the statement: it is *applying* a lemma
whose transport argument is the inline term
`eqToHom (congrArg (fun k ↦ push k) w)` at a position where the two spellings of a section of a
composite direct image, `((push e ⋙ push g).obj F).obj.obj (op V)` and
`F.obj.obj (op ((smallEtaleBaseChange g ⋙ smallEtaleBaseChange e).obj V))`, have to be
identified.  With the glue split into its three steps: the statement carrying
the inline transport across that identification type-checks well inside the budget, and so does
`pushComp₃_app_hom_app_map` with its transport argument abstract, but instantiating the latter
at the inline transport is a `(kernel) deterministic timeout`.  Replacing the inline term by
`pushCongrHom w`, which is definitionally the same transport, makes the identical application
check in about two seconds, because the kernel then reads the transport's type off a
declaration signature instead of re-deriving it through `congrArg` under an `eqToHom` on each
descent into `CategoryStruct.comp` at the sheaf categories.

This is worth recording because the obvious explanation is the wrong one.  `getLimitCone` is
indeed invisible here — it is `@[no_expose]` at its Mathlib declaration site, so no `public
import` chain reaches its body and `attribute [expose]` on it is rejected outright — but that is
not what blocks this formula.  The failure is a kernel timeout, not an exposure error, and it is
removed by naming a transport rather than by exposing anything.

With `rightSquare_app` available, the cube of comparisons of composite direct images reduces
sectionwise to the cube of site comparisons: every edge becomes a contravariant map of `F`, and
`map_op_three_congr` turns the two composites of three such maps into the single site-level
identity `siteSquare_cube`.

## References

* [Stacks Project, Tag 0EZR](https://stacks.math.columbia.edu/tag/0EZR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

universe u v z

namespace Stacks.EtaleCohomology

/-! ### The right square on sections -/

section RightSquareApp

/-- **The transport of a direct image along an equality of morphisms, as a named constant.**
Giving the transport a name of its own is what makes the sectionwise formula for the
right-square comparison affordable: see the implementation notes.  It is definitionally the
`eqToHom` of `congrArg`, so `rightSquare_hom_eq_pushCongrHom` holds by `rfl`. -/
private def pushCongrHom {X Y : Scheme.{u}} {f g : X ⟶ Y} (w : f = g) :
    push.{u, v} f ⟶ push.{u, v} g :=
  eqToHom (congrArg (fun k : X ⟶ Y => push.{u, v} k) w)

/-- The named transport of the direct image, on sections. -/
private lemma pushCongrHom_app {X Y : Scheme.{u}} {f g : X ⟶ Y} (w : f = g)
    (F : Sheaf (smallEtaleTopology X) (Type (max (u + 1) v))) (V : Y.Etale) :
    ((pushCongrHom.{u, v} w).app F).hom.app (op V) =
      F.obj.map (eqToHom (congrArg
        (fun k => (smallEtaleBaseChange k).obj V) w.symm)).op :=
  pushCongr_app.{u, v} w F V

/-- `rightSquare_hom_eq` with its transport factor written as the named `pushCongrHom`. -/
private lemma rightSquare_hom_eq_pushCongrHom {Y T X S : Scheme.{u}}
    (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S) (w : e ≫ g = h ≫ f) :
    (rightSquare.{u, v} e h g f w).hom =
      (smallEtalePushforwardCompIso.{u, v} e g).hom ≫
        pushCongrHom.{u, v} w ≫
        (smallEtalePushforwardCompIso.{u, v} h f).inv :=
  rfl

/-- `rightSquare_app_eq` with its transport factor written as the named `pushCongrHom`; this is
the form in which the sectionwise formula `rightSquare_app` is affordable. -/
private lemma rightSquare_app_eq_pushCongrHom {Y T X S : Scheme.{u}}
    (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S) (w : e ≫ g = h ≫ f)
    (F : Sheaf (smallEtaleTopology Y) (Type (max (u + 1) v))) (V : S.Etale) :
    ((rightSquare.{u, v} e h g f w).hom.app F).hom.app (op V) =
      (((smallEtalePushforwardCompIso.{u, v} e g).hom ≫
        pushCongrHom.{u, v} w ≫
        (smallEtalePushforwardCompIso.{u, v} h f).inv).app F).hom.app (op V) :=
  congrArg (fun t : push.{u, v} e ⋙ push.{u, v} g ⟶ push.{u, v} h ⋙ push.{u, v} f =>
    (NatTrans.app t F).hom.app (op V)) (rightSquare_hom_eq_pushCongrHom.{u, v} e h g f w)

/-- **The right-square comparison on sections is the contravariant map of the site
comparison.**  This glues `rightSquare_app_eq_pushCongrHom` to `pushComp₃_app_hom_app_map` and
rewrites the resulting triple by `siteSquare_hom_app`. -/
private lemma rightSquare_app {Y T X S : Scheme.{u}}
    (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S) (w : e ≫ g = h ≫ f)
    (F : Sheaf (smallEtaleTopology Y) (Type (max (u + 1) v))) (V : S.Etale) :
    ((rightSquare.{u, v} e h g f w).hom.app F).hom.app (op V) =
      F.obj.map ((siteSquare e h g f w).hom.app V).op :=
  ((rightSquare_app_eq_pushCongrHom.{u, v} e h g f w F V).trans
      (pushComp₃_app_hom_app_map.{u, v} e h g f F V _ _ (pushCongrHom_app.{u, v} w F V))).trans
    (congrArg (fun k => F.obj.map (Opposite.op k)) (siteSquare_hom_app e h g f w V).symm)

end RightSquareApp

/-! ### The cube of site comparisons -/

section SiteProjections

/-- `siteSquare_hom_fst` followed by a further morphism out of the underlying scheme of `V`. -/
private lemma siteSquare_hom_fst_assoc {Y T X S : Scheme.{u}}
    (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S) (w : e ≫ g = h ≫ f) (V : S.Etale)
    {Z : Scheme.{u}} (k : V.left ⟶ Z) :
    ((siteSquare e h g f w).hom.app V).left ≫
        pullback.fst (pullback.snd V.hom g) e ≫ pullback.fst V.hom g ≫ k =
      pullback.fst (pullback.snd V.hom f) h ≫ pullback.fst V.hom f ≫ k :=
  (reassoc_of% (siteSquare_hom_fst e h g f w V)) k

/-- Base change of a morphism of the site, followed by a projection: the projection is carried
along by `AlgebraicGeometry.Scheme.Etale.smallEtaleBaseChange_map_left_fst`. -/
private lemma baseChange_map_projection {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    {V W : Y.Etale} (k : V ⟶ W) {p : W.left ⟶ Z} {q : V.left ⟶ Z}
    (hk : k.left ≫ p = q) :
    ((smallEtaleBaseChange f).map k).left ≫ (pullback.fst W.hom f ≫ p) =
      pullback.fst V.hom f ≫ q :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ p) (smallEtaleBaseChange_map_left_fst f k)).trans
      ((Category.assoc _ _ _).trans (congrArg (fun t => pullback.fst V.hom f ≫ t) hk)))

/-- **The cube of site comparisons commutes.**  Stacking the outer square on the `i`-th upper
square gives the same rectangle `U i ⟶ X ⟶ S` as stacking the `i`-th local square on the `i`-th
lower square, because `U i → X → S` equals `U i → V i → S`.  Both ways around the cube project
to the structure morphism of `V`, and a morphism of the small étale site is determined by its
projections, so the two agree. -/
private lemma siteSquare_cube
    (D : EtaleLocalBaseChangeData.{u, z, max (u + 1) v, max (u + 1) v + 1}
      (Type (max (u + 1) v))) (i : D.I) (V : D.S.Etale) :
    (smallEtaleBaseChange (D.h_i i)).map
        ((siteSquare (D.u i) (D.f_i i) D.f (D.v i) (D.factorization i).symm).hom.app V) ≫
      (siteSquare (D.toY_i i) (D.h_i i) D.h (D.u i)
        (D.upper_cartesian i).w.symm).hom.app ((smallEtaleBaseChange D.f).obj V) ≫
      (smallEtaleBaseChange (D.toY_i i)).map
        ((siteSquare D.e D.h D.g D.f D.cartesian.w.symm).hom.app V) =
    (siteSquare (D.e_i i) (D.h_i i) (D.g_i i) (D.f_i i)
        (D.local_cartesian i).w.symm).hom.app ((smallEtaleBaseChange (D.v i)).obj V) ≫
      (smallEtaleBaseChange (D.e_i i)).map
        ((siteSquare (D.toT_i i) (D.g_i i) D.g (D.v i)
          (D.lower_cartesian i).w.symm).hom.app V) ≫
      (siteSquare (D.toY_i i) (D.e_i i) D.e (D.toT_i i)
        (D.e_i_compatible i).symm).hom.app ((smallEtaleBaseChange D.g).obj V) := by
  let a := (smallEtaleBaseChange (D.h_i i)).map
    ((siteSquare (D.u i) (D.f_i i) D.f (D.v i) (D.factorization i).symm).hom.app V)
  let b := (siteSquare (D.toY_i i) (D.h_i i) D.h (D.u i)
    (D.upper_cartesian i).w.symm).hom.app ((smallEtaleBaseChange D.f).obj V)
  let c := (smallEtaleBaseChange (D.toY_i i)).map
    ((siteSquare D.e D.h D.g D.f D.cartesian.w.symm).hom.app V)
  let d := (siteSquare (D.e_i i) (D.h_i i) (D.g_i i) (D.f_i i)
    (D.local_cartesian i).w.symm).hom.app ((smallEtaleBaseChange (D.v i)).obj V)
  let e := (smallEtaleBaseChange (D.e_i i)).map
    ((siteSquare (D.toT_i i) (D.g_i i) D.g (D.v i) (D.lower_cartesian i).w.symm).hom.app V)
  let f := (siteSquare (D.toY_i i) (D.e_i i) D.e (D.toT_i i)
    (D.e_i_compatible i).symm).hom.app ((smallEtaleBaseChange D.g).obj V)
  let lhs := a ≫ b ≫ c
  let rhs := d ≫ e ≫ f
  change lhs = rhs
  have ha := baseChange_map_projection (D.h_i i) _
    (siteSquare_hom_fst (D.u i) (D.f_i i) D.f (D.v i) (D.factorization i).symm V)
  have hb := siteSquare_hom_fst_assoc (D.toY_i i) (D.h_i i) D.h (D.u i)
    (D.upper_cartesian i).w.symm ((smallEtaleBaseChange D.f).obj V) (pullback.fst V.hom D.f)
  have hc := baseChange_map_projection (D.toY_i i) _
    (siteSquare_hom_fst D.e D.h D.g D.f D.cartesian.w.symm V)
  have hd := siteSquare_hom_fst_assoc (D.e_i i) (D.h_i i) (D.g_i i) (D.f_i i)
    (D.local_cartesian i).w.symm ((smallEtaleBaseChange (D.v i)).obj V)
    (pullback.fst V.hom (D.v i))
  have he := baseChange_map_projection (D.e_i i) _
    (siteSquare_hom_fst (D.toT_i i) (D.g_i i) D.g (D.v i) (D.lower_cartesian i).w.symm V)
  have hf := siteSquare_hom_fst_assoc (D.toY_i i) (D.e_i i) D.e (D.toT_i i)
    (D.e_i_compatible i).symm ((smallEtaleBaseChange D.g).obj V) (pullback.fst V.hom D.g)
  apply MorphismProperty.Over.Hom.ext
  refine ((IsPullback.of_hasPullback
    (pullback.snd (pullback.snd V.hom D.g) D.e) (D.toY_i i)).paste_horiz
      ((IsPullback.of_hasPullback (pullback.snd V.hom D.g) D.e).paste_horiz
        (IsPullback.of_hasPullback V.hom D.g))).hom_ext ?_ ?_
  · have three : ∀ {A B D E Z : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E)
        {pA : A ⟶ Z} {pB : B ⟶ Z} {pD : D ⟶ Z} {pE : E ⟶ Z},
        a ≫ pB = pA → b ≫ pD = pB → c ≫ pE = pD → (a ≫ b ≫ c) ≫ pE = pA := by
      intro _ _ _ _ _ a b c _ _ _ _ ha hb hc
      simp only [Category.assoc, hc, hb, ha]
    exact (three _ _ _ ha hb hc).trans (three _ _ _ hd he hf).symm
  · exact (MorphismProperty.Over.w lhs).trans (MorphismProperty.Over.w rhs).symm

end SiteProjections

/-! ### The cube of right-square comparisons -/

section RightSquareCube

/-- The direct image of a morphism of sheaves, on sections. -/
private lemma push_map_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F G : Sheaf (smallEtaleTopology X) (Type (max (u + 1) v))}
    (a : F ⟶ G) (V : Y.Etale) :
    ((push.{u, v} f).map a).hom.app (op V) =
      a.hom.app (op ((smallEtaleBaseChange f).obj V)) :=
  rfl

/-- The contravariant map of a direct image, on sections. -/
private lemma push_obj_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf (smallEtaleTopology X) (Type (max (u + 1) v)))
    {V W : Y.Etale} (a : V ⟶ W) :
    ((push.{u, v} f).obj F).obj.map a.op =
      F.obj.map ((smallEtaleBaseChange f).map a).op :=
  rfl

/-- Two composites of three contravariant maps agree as soon as the two underlying composites
of three morphisms agree. -/
lemma map_op_three_congr {A B : Type*} [Category* A] [Category* B]
    (F : Aᵒᵖ ⥤ B) {W X Y Z X' Y' : A}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z)
    (d : W ⟶ X') (e : X' ⟶ Y') (f : Y' ⟶ Z)
    (h : a ≫ b ≫ c = d ≫ e ≫ f) :
    F.map c.op ≫ F.map b.op ≫ F.map a.op =
      F.map f.op ≫ F.map e.op ≫ F.map d.op := by
  rw [map_op_triple, map_op_triple, h]

/-- **The cube of right-square comparisons commutes.**  Stacking the outer square on the `i`-th
upper square gives the same rectangle as stacking the `i`-th local square on the `i`-th lower
square; this is that identity for the comparisons of composite direct images, and it is the
cube hypothesis `isIso_map_mate_of_cube` consumes. -/
private lemma rightSquare_cube
    (D : EtaleLocalBaseChangeData.{u, z, max (u + 1) v, max (u + 1) v + 1}
      (Type (max (u + 1) v))) (i : D.I) :
    (TwoSquare.hComp (rightSquare.{u, v} (D.toY_i i) (D.h_i i) D.h (D.u i)
        (D.upper_cartesian i).w.symm).hom
      (rightSquare.{u, v} D.e D.h D.g D.f D.cartesian.w.symm).hom).whiskerBottom
        (rightSquare.{u, v} (D.u i) (D.f_i i) D.f (D.v i) (D.factorization i).symm).hom =
    (TwoSquare.hComp (rightSquare.{u, v} (D.e_i i) (D.h_i i) (D.g_i i) (D.f_i i)
        (D.local_cartesian i).w.symm).hom
      (rightSquare.{u, v} (D.toT_i i) (D.g_i i) D.g (D.v i)
        (D.lower_cartesian i).w.symm).hom).whiskerTop
          (rightSquare.{u, v} (D.toY_i i) (D.e_i i) D.e (D.toT_i i)
            (D.e_i_compatible i).symm).hom := by
  apply NatTrans.ext
  funext F
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  cases V with
  | op V =>
    dsimp only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop, TwoSquare.hComp,
      TwoSquare.mk, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app]
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id]
    rw [rightSquare_app, push_map_app, rightSquare_app, rightSquare_app, push_map_app,
      rightSquare_app, rightSquare_app, push_map_app, rightSquare_app, push_obj_map, push_obj_map,
      push_obj_map]
    exact map_op_three_congr F.obj _ _ _ _ _ _ (siteSquare_cube D i V)

end RightSquareCube

end Stacks.EtaleCohomology

end
