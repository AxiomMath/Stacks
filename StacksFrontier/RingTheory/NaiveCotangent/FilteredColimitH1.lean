module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.CategoryTheory.Filtered.FinallySmall
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Presentable.Directed
public import StacksFrontier.RingTheory.NaiveCotangent.Colimit
public import StacksFrontier.RingTheory.NaiveCotangent.SquareMap
import StacksCore.Tactic.EgaSgaAttribute

/-!
# First homology of the naive cotangent complex along a filtered colimit

Let `I` be a filtered category and let `g : R ⟶ S` be a morphism of `I`-shaped diagrams of
commutative rings, with colimits `R∞` and `S∞` and induced ring map `gInf : R∞ → S∞`.  This file
proves that a class of `H₁(L_{S i/R i})` which vanishes in `H₁(L_{S∞/R∞})` already vanishes at a
later stage of the diagram.  It is the form in which the compatibility of the naive cotangent
complex with filtered colimits (Stacks 07BQ, `RingMapSystemUnbundled.isIso_colim_NL`, stated
there for a directed set) is consumed on a site, where the diagram is the category of
neighbourhoods of a point, which is filtered but not a preorder.

## Main results

* `Stacks.NaiveCotangent.exists_ringEquiv_directLimit_of_final`: along a final functor from a
  directed set, the colimit of a diagram of rings is the direct limit of the restricted system.
* `Stacks.NaiveCotangent.exists_h1CotangentMapOfSquare_eq_zero_of_isColimit`: the vanishing
  statement above.

## Implementation notes

The diagram is first restricted along a final functor from a directed set, which exists for a
filtered category that is locally and finally small (`CategoryTheory.IsFiltered.exists_directed`
applied to `CategoryTheory.FinallySmall.fromFilteredFinalModel`); on that directed set the
colimits are `Ring.DirectLimit`s, where `RingMapSystemUnbundled.cotMapInf_eq_zero_of_stage`
applies.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Algebra

universe w v u

namespace Stacks.NaiveCotangent

section DirectLimit

variable {α : Type w} [Preorder α]

/-- **The direct limit of a directed system of rings is its colimit.**  For a diagram of
commutative rings on a preorder, the direct limit, with its canonical maps, is a colimit
cocone. -/
noncomputable def directLimitCocone (P : α ⥤ CommRingCat.{w}) : Cocone P where
  pt := CommRingCat.of (Ring.DirectLimit (fun a => P.obj a)
    (fun _ _ h => (P.map (homOfLE h)).hom))
  ι :=
    { app := fun a => CommRingCat.ofHom (Ring.DirectLimit.of (fun a => P.obj a)
        (fun _ _ h => (P.map (homOfLE h)).hom) a)
      naturality := fun a b h => by
        ext x
        exact (Ring.DirectLimit.of_f (G := fun a => P.obj a)
          (f := fun _ _ h => (P.map (homOfLE h)).hom) (leOfHom h) x).trans rfl }

/-- The direct limit cocone is a colimit. -/
noncomputable def isColimitDirectLimitCocone (P : α ⥤ CommRingCat.{w}) :
    IsColimit (directLimitCocone P) where
  desc s := CommRingCat.ofHom (Ring.DirectLimit.lift (fun a => P.obj a)
    (fun _ _ h => (P.map (homOfLE h)).hom) s.pt (fun a => (s.ι.app a).hom)
    (fun a b h x => congrArg (fun f => f.hom x) (s.w (homOfLE h))))
  fac s a := by
    ext x
    exact Ring.DirectLimit.lift_of (G := fun a => P.obj a)
      (f := fun _ _ h => (P.map (homOfLE h)).hom) s.pt (fun a => (s.ι.app a).hom)
      (fun a b h x => congrArg (fun f => f.hom x) (s.w (homOfLE h))) a x
  uniq s m hm := by
    apply CommRingCat.hom_ext
    apply Ring.DirectLimit.hom_ext
    intro a
    apply RingHom.ext
    intro x
    exact (congrArg (fun f => f.hom x) (hm a)).trans
      (Ring.DirectLimit.lift_of (G := fun a => P.obj a)
        (f := fun _ _ h => (P.map (homOfLE h)).hom) s.pt (fun a => (s.ι.app a).hom)
        (fun a b h x => congrArg (fun f => f.hom x) (s.w (homOfLE h))) a x).symm

end DirectLimit

/-- **Along a final functor from a directed set, a colimit of rings is a direct limit.**  If
`F : α ⥤ I` is final and `c` is a colimit cocone on `P : I ⥤ CommRingCat`, then the direct limit
of the restricted system is identified with `c.pt`, compatibly with the canonical maps. -/
theorem exists_ringEquiv_directLimit_of_final {α : Type w} [Preorder α]
    {I : Type u} [Category.{v} I] (F : α ⥤ I) [F.Final] {P : I ⥤ CommRingCat.{w}}
    {c : Cocone P} (hc : IsColimit c) :
    ∃ e : Ring.DirectLimit (fun a => (F ⋙ P).obj a)
        (fun _ _ h => ((F ⋙ P).map (homOfLE h)).hom) ≃+* c.pt,
      ∀ a x, e (Ring.DirectLimit.of (fun a => (F ⋙ P).obj a)
        (fun _ _ h => ((F ⋙ P).map (homOfLE h)).hom) a x) = (c.ι.app (F.obj a)).hom x := by
  have hc' : IsColimit (c.whisker F) := (Functor.Final.isColimitWhiskerEquiv F c).symm hc
  let e := ((isColimitDirectLimitCocone (F ⋙ P)).coconePointUniqueUpToIso hc')
  refine ⟨e.commRingCatIsoToRingEquiv, fun a x => ?_⟩
  exact congrArg (fun f => f.hom x)
    ((isColimitDirectLimitCocone (F ⋙ P)).comp_coconePointUniqueUpToIso_hom hc' a)

/-- A filtered category which is locally and finally small receives a final functor from a
directed set. -/
@[sga "4 I 8.1.6" "more general"]
theorem exists_directed_final (I : Type u) [Category.{v} I] [IsFiltered I]
    [LocallySmall.{w} I] [FinallySmall.{w} I] :
    ∃ (α : Type w) (_ : PartialOrder α) (_ : IsDirected α (· ≤ ·)) (_ : Nonempty α)
      (F : α ⥤ I), F.Final := by
  obtain ⟨α, hα, hd, hne, F, hF⟩ :=
    IsFiltered.exists_directed (FinallySmall.FilteredFinalModel.{w} I)
  exact ⟨α, hα, hd, hne, F ⋙ FinallySmall.fromFilteredFinalModel.{w} I, inferInstance⟩

/-- The directed system of ring maps obtained by restricting a morphism of diagrams of rings
along a functor out of a preorder. -/
noncomputable def diagramSystem {α : Type w} [Preorder α] {I : Type u} [Category.{v} I]
    (F : α ⥤ I) {R S : I ⥤ CommRingCat.{w}} (g : R ⟶ S) : RingMapSystemUnbundled.{w} α where
  R b := R.obj (F.obj b)
  S b := S.obj (F.obj b)
  commRingR _ := inferInstance
  commRingS _ := inferInstance
  fR _ _ h := (R.map (F.map (homOfLE h))).hom
  fS _ _ h := (S.map (F.map (homOfLE h))).hom
  fR_id b x := by
    rw [show homOfLE (le_refl b) = 𝟙 b from rfl, F.map_id, R.map_id]
    rfl
  fR_comp b c d hbc hcd x := by
    rw [← CommRingCat.comp_apply, ← R.map_comp, ← F.map_comp]
    rfl
  fS_id b x := by
    rw [show homOfLE (le_refl b) = 𝟙 b from rfl, F.map_id, S.map_id]
    rfl
  fS_comp b c d hbc hcd x := by
    rw [← CommRingCat.comp_apply, ← S.map_comp, ← F.map_comp]
    rfl
  g b := (g.app (F.obj b)).hom
  square b c h x := (ConcreteCategory.congr_hom (g.naturality (F.map (homOfLE h))) x).symm

/-- A leg of a cocone of rings is compatible with the transition maps of the diagram. -/
private theorem cocone_leg_comp_map {I : Type u} [Category.{v} I] {P : I ⥤ CommRingCat.{w}}
    (c : Cocone P) {i j : I} (t : i ⟶ j) :
    ((c.ι.app j).hom : P.obj j →+* c.pt).comp (P.map t).hom = (c.ι.app i).hom :=
  RingHom.ext fun x => ConcreteCategory.congr_hom (c.w t) x

section Vanishing

variable {I : Type u} [Category.{v} I] [IsFiltered I] [LocallySmall.{w} I] [FinallySmall.{w} I]
  {R S : I ⥤ CommRingCat.{w}} (g : R ⟶ S) {cR : Cocone R} (hR : IsColimit cR)
  {cS : Cocone S} (hS : IsColimit cS) (gInf : cR.pt ⟶ cS.pt)
  (hg : ∀ i, cR.ι.app i ≫ gInf = g.app i ≫ cS.ι.app i)

/-- A leg of a cocone of rings, as a ring homomorphism into the cocone point. -/
noncomputable abbrev coconeLeg {P : I ⥤ CommRingCat.{w}} (c : Cocone P) (i : I) :
    P.obj i →+* c.pt :=
  (c.ι.app i).hom

omit [IsFiltered I] [LocallySmall.{w, v, u} I] [FinallySmall I] in
include g in
/-- The square of a transition map of the diagram commutes. -/
theorem diagramSquare_comm {i j : I} (t : i ⟶ j) (r : R.obj i) :
    (S.map t).hom (@algebraMap _ _ _ _ (g.app i).hom.toAlgebra r) =
      @algebraMap _ _ _ _ (g.app j).hom.toAlgebra ((R.map t).hom r) :=
  (ConcreteCategory.congr_hom (g.naturality t) r).symm

omit [IsFiltered I] [LocallySmall.{w, v, u} I] [FinallySmall I] in
include hg in
/-- The square of a leg of the colimit cocones commutes. -/
theorem coconeSquare_comm (i : I) (r : R.obj i) :
    coconeLeg cS i (@algebraMap _ _ _ _ (g.app i).hom.toAlgebra r) =
      @algebraMap _ _ _ _ gInf.hom.toAlgebra (coconeLeg cR i r) :=
  (ConcreteCategory.congr_hom (hg i) r).symm

include hR hS in
/-- **A class of `H₁` which vanishes in the colimit vanishes at a later stage.** -/
theorem exists_h1CotangentMapOfSquare_eq_zero_of_isColimit (i : I)
    (z : @H1Cotangent (R.obj i) (S.obj i) _ _ (g.app i).hom.toAlgebra)
    (hz : @h1CotangentMapOfSquare _ _ _ _ _ _ _ _ (g.app i).hom.toAlgebra gInf.hom.toAlgebra
      (coconeLeg cR i) (coconeLeg cS i) (coconeSquare_comm g gInf hg i) z = 0) :
    ∃ (j : I) (t : i ⟶ j), @h1CotangentMapOfSquare _ _ _ _ _ _ _ _
      (g.app i).hom.toAlgebra (g.app j).hom.toAlgebra (R.map t).hom (S.map t).hom
      (diagramSquare_comm g t) z = 0 := by
  obtain ⟨α, _, _, _, F, _⟩ := exists_directed_final.{w} I
  have : IsDirectedOrder α := inferInstance
  obtain ⟨eR₀, heR₀⟩ := exists_ringEquiv_directLimit_of_final F hR
  obtain ⟨eS₀, heS₀⟩ := exists_ringEquiv_directLimit_of_final F hS
  let : ∀ k : I, Algebra (R.obj k) (S.obj k) := fun k => (g.app k).hom.toAlgebra
  let : Algebra cR.pt cS.pt := gInf.hom.toAlgebra
  -- Move the stage `i` into the image of the final functor.
  let a := Functor.Final.lift F i
  let s : i ⟶ F.obj a := Functor.Final.homToLift F i
  let z' := h1CotangentMapOfSquare (R.map s).hom (S.map s).hom (diagramSquare_comm g s) z
  -- The directed system of rings over `α`.
  let sys := diagramSystem F g
  let eR : sys.Rinf →+* cR.pt := eR₀.toRingHom
  let eS : sys.Sinf →+* cS.pt := eS₀.toRingHom
  let eR' : cR.pt →+* sys.Rinf := eR₀.symm.toRingHom
  let eS' : cS.pt →+* sys.Sinf := eS₀.symm.toRingHom
  have heR : ∀ b x, eR (sys.toRinf b x) = coconeLeg cR (F.obj b) x := heR₀
  have heS : ∀ b x, eS (sys.toSinf b x) = coconeLeg cS (F.obj b) x := heS₀
  -- The comparison of the colimits commutes with the two ring maps.
  have hsq : ∀ r : sys.Rinf, eS (algebraMap sys.Rinf sys.Sinf r) =
      algebraMap cR.pt cS.pt (eR r) := by
    intro r
    obtain ⟨b, x, rfl⟩ := Ring.DirectLimit.exists_of r
    show eS (sys.gInf (sys.toRinf b x)) = gInf.hom (eR (sys.toRinf b x))
    rw [← sys.toSinf_g b x]
    refine (heS b _).trans ?_
    refine Eq.trans ?_ (congrArg gInf.hom (heR b x).symm)
    exact (ConcreteCategory.congr_hom (hg (F.obj b)) x).symm
  have hsq' : ∀ r : cR.pt, eS' (algebraMap cR.pt cS.pt r) =
      algebraMap sys.Rinf sys.Sinf (eR' r) := by
    intro r
    apply eS₀.injective
    have h1 : eS₀ (eS' (algebraMap cR.pt cS.pt r)) = algebraMap cR.pt cS.pt r :=
      eS₀.apply_symm_apply _
    have h2 : eS₀ (algebraMap sys.Rinf sys.Sinf (eR' r)) = algebraMap cR.pt cS.pt (eR (eR' r)) :=
      hsq (eR' r)
    have h3 : eR (eR' r) = r := eR₀.apply_symm_apply r
    rw [h1]
    exact (h2.trans (congrArg _ h3)).symm
  have htoR : ∀ b, eR.comp (sys.toRinf b) = coconeLeg cR (F.obj b) :=
    fun b => RingHom.ext fun x => heR b x
  have htoS : ∀ b, eS.comp (sys.toSinf b) = coconeLeg cS (F.obj b) :=
    fun b => RingHom.ext fun x => heS b x
  -- The image of `z'` in the direct limit vanishes.
  have h0 : h1CotangentMapOfSquare eR eS hsq
      (h1CotangentMapOfSquare (sys.toRinf a) (sys.toSinf a) (fun x => sys.toSinf_g a x) z') =
        0 := by
    refine ((h1CotangentMapOfSquare_comp _ _ _ _ _ hsq _).trans
      (h1CotangentMapOfSquare_congr _ (coconeSquare_comm g gInf hg (F.obj a)) (htoR a) (htoS a)
        _)).trans ?_
    refine (h1CotangentMapOfSquare_comp _ _ (diagramSquare_comm g s) _ _
      (coconeSquare_comm g gInf hg (F.obj a)) z).trans ?_
    exact (h1CotangentMapOfSquare_congr (R' := cR.pt) (S' := cS.pt) _ _
      (cocone_leg_comp_map cR s) (cocone_leg_comp_map cS s) z).trans hz
  have hz' : h1CotangentMapOfSquare (sys.toRinf a) (sys.toSinf a) (fun x => sys.toSinf_g a x) z'
      = 0 := by
    have hback := congrArg (h1CotangentMapOfSquare eR' eS' hsq') h0
    rw [map_zero] at hback
    refine Eq.trans ?_ ((h1CotangentMapOfSquare_comp _ _ hsq _ _ hsq' _).symm.trans hback)
    have hidR : RingHom.id sys.Rinf = eR'.comp eR := eR₀.symm_toRingHom_comp_toRingHom.symm
    have hidS : RingHom.id sys.Sinf = eS'.comp eS := eS₀.symm_toRingHom_comp_toRingHom.symm
    refine (h1CotangentMapOfSquare_id _).symm.trans ?_
    exact h1CotangentMapOfSquare_congr _ _ hidR hidS _
  have hcot : sys.cotMapInf a z'.1 = 0 := congrArg Subtype.val hz'
  obtain ⟨b, hab, hb⟩ := sys.cotMapInf_eq_zero_of_stage a z'.1 hcot
  refine ⟨F.obj b, s ≫ F.map (homOfLE hab), ?_⟩
  apply Subtype.ext
  have hcomp := h1CotangentMapOfSquare_comp (R.map s).hom (S.map s).hom (diagramSquare_comm g s)
    (R.map (F.map (homOfLE hab))).hom (S.map (F.map (homOfLE hab))).hom
    (diagramSquare_comm g (F.map (homOfLE hab))) z
  refine (congrArg Subtype.val ((h1CotangentMapOfSquare_congr _ _
    (by rw [R.map_comp]; rfl) (by rw [S.map_comp]; rfl) z).trans hcomp.symm)).trans ?_
  exact hb

end Vanishing

end Stacks.NaiveCotangent

end
