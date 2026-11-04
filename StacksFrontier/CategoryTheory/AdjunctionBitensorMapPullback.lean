module

public import StacksFrontier.CategoryTheory.BifunctorProdMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupProductOfCohomologyClasses
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethMap

/-!
# The abstract relative cup product, transports and pullback legs

Bookkeeping for the abstract relative cup product
`Stacks.Cohomology.DerivedRelativeCupProduct.adjunctionBitensorMap` of Tag 0B68, at the
generality of arbitrary adjunctions and bifunctors.  These are the diagram chases behind the
global form of Cohomology, Lemma 0FP6 used for Remark 0G7W; the geometric file
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalKunnethCupWithClassCanonical`
only instantiates them.

## Main results

* `Stacks.Cohomology.AdjunctionBitensorPullback.adjunctionBitensorMap_ofNatIsoRight` — an
  adjunction transported along an isomorphism of right adjoints has the relative cup product read
  through that isomorphism.
* `Stacks.Cohomology.AdjunctionBitensorPullback.kunnethAdjunctionBitensorMap_eq` — the abstract
  Künneth map is the adjoints of its two legs followed by the abstract relative cup product.
* `Stacks.Cohomology.AdjunctionBitensorPullback.legs_adjunctionBitensorMap` — for
  `La ⋙ Lp ≅ Lf` with a composition law for the comparisons, the pullback legs followed by the
  relative cup product for `f` are the relative cup product for `a` followed by a pullback leg
  and the comparison for `Lp`: the relative form of Lemma 0FP6.
* `Stacks.Cohomology.AdjunctionBitensorPullback.sections_comp_cup` and
  `Stacks.Cohomology.AdjunctionBitensorPullback.sections_cup_compatible` — the same statements
  read on global sections through a lax structure `μ` and Leray-type isomorphisms.
-/

@[expose] public section

open CategoryTheory
open Stacks.Cohomology.DerivedRelativeCupProduct
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.AdjunctionBitensorPullback

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

/-! ### Transport along an isomorphism of right adjoints -/

section Transport

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {R R' : D ⥤ C} (adj : L ⊣ R) (cr : R ≅ R') (A : C × C ⥤ C) (B : D × D ⥤ D)
  (α : A ⋙ L ⟶ L.prod L ⋙ B)

/-- **An adjunction transported along an isomorphism of right adjoints** has its abstract
relative cup product read through the isomorphism. -/
theorem adjunctionBitensorMap_ofNatIsoRight (G G' : D) :
    adjunctionBitensorMap (adj.ofNatIsoRight cr) A B α G G' =
      A.map (cr.inv.app G ×ₘ cr.inv.app G') ≫ adjunctionBitensorMap adj A B α G G' ≫
        cr.hom.app (B.obj (G, G')) := by
  apply ((adj.ofNatIsoRight cr).homEquiv _ _).symm.injective
  have hid : adjunctionBitensorMap (adj.ofNatIsoRight cr) A B α G G' =
      A.map (𝟙 (R'.obj G) ×ₘ 𝟙 (R'.obj G')) ≫
        adjunctionBitensorMap (adj.ofNatIsoRight cr) A B α G G' := by
    rw [show A.map (𝟙 (R'.obj G) ×ₘ 𝟙 (R'.obj G')) = 𝟙 _ from A.map_id (R'.obj G, R'.obj G'),
      Category.id_comp]
  rw [hid, homEquiv_symm_adjunctionBitensorMap, Adjunction.homEquiv_ofNatIsoRight_symm_apply,
    Adjunction.homEquiv_ofNatIsoRight_symm_apply, Adjunction.homEquiv_ofNatIsoRight_symm_apply]
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id, Category.id_comp]
  rw [homEquiv_symm_adjunctionBitensorMap]

end Transport

/-! ### The abstract Künneth map through the abstract relative cup product -/

section Kunneth

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {C₁ : Type u₃} [Category.{v₃} C₁] {C₂ : Type u₄} [Category.{v₄} C₂]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (A : C × C ⥤ C) (B : D × D ⥤ D)
  (α : A ⋙ L ⟶ L.prod L ⋙ B)
  {R₁ : C₁ ⥤ C} {P₁ : C₁ ⥤ D} (β : R₁ ⋙ L ⟶ P₁)
  {R₂ : C₂ ⥤ C} {P₂ : C₂ ⥤ D} (γ : R₂ ⋙ L ⟶ P₂)

/-- **The abstract Künneth map is the adjoints of its two legs followed by the abstract relative
cup product.** -/
theorem kunnethAdjunctionBitensorMap_eq (K : C₁) (M : C₂) :
    Stacks.Cohomology.DerivedKunneth.adjunctionBitensorMap adj A B α β γ K M =
      A.map (adj.homEquiv _ _ (β.app K) ×ₘ adj.homEquiv _ _ (γ.app M)) ≫
        adjunctionBitensorMap adj A B α (P₁.obj K) (P₂.obj M) := by
  apply (adj.homEquiv _ _).symm.injective
  rw [homEquiv_symm_adjunctionBitensorMap]
  unfold Stacks.Cohomology.DerivedKunneth.adjunctionBitensorMap
  simp only [Equiv.symm_apply_apply]

end Kunneth

/-! ### Pullback legs and the relative cup product -/

section Legs

variable {CS : Type u₁} [Category.{v₁} CS] {CX : Type u₂} [Category.{v₂} CX]
  {CW : Type u₃} [Category.{v₃} CW]
  {La : CS ⥤ CX} {Ra : CX ⥤ CS} (adja : La ⊣ Ra) {Lf : CS ⥤ CW} {Rf : CW ⥤ CS} (adjf : Lf ⊣ Rf)
  (Lp : CX ⥤ CW) (c : La ⋙ Lp ≅ Lf)
  (AS : CS × CS ⥤ CS) (BX : CX × CX ⥤ CX) (BW : CW × CW ⥤ CW)
  (τa : AS ⋙ La ⟶ La.prod La ⋙ BX) (τp : BX ⋙ Lp ⟶ Lp.prod Lp ⋙ BW)
  (τf : AS ⋙ Lf ⟶ Lf.prod Lf ⋙ BW)

/-- **The relative form of Cohomology, Lemma 0FP6, at the pullback legs.**  Let
`c : La ⋙ Lp ≅ Lf` and suppose the comparison `τf` for `Lf` is the comparison for `La` followed
by the one for `Lp`, read through `c`.  For a family of legs `Lf Ra K ⟶ Lp K` equal to `c⁻¹`
followed by `Lp` of the counit of `La ⊣ Ra`, the adjoints of the legs followed by the relative
cup product for `Lf ⊣ Rf` are the relative cup product for `La ⊣ Ra`, followed by the adjoint of
a leg and `Rf` of the comparison for `Lp`. -/
theorem legs_adjunctionBitensorMap
    (hcomp : Functor.whiskerLeft AS c.hom ≫ τf =
      Functor.whiskerRight τa Lp ≫ Functor.whiskerLeft (La.prod La) τp ≫
        Functor.whiskerRight (NatTrans.prod c.hom c.hom) BW)
    (leg : ∀ K : CX, Lf.obj (Ra.obj K) ⟶ Lp.obj K)
    (hleg : ∀ K : CX, leg K = c.inv.app (Ra.obj K) ≫ Lp.map (adja.counit.app K)) (U V : CX) :
    AS.map (adjf.homEquiv _ _ (leg U) ×ₘ adjf.homEquiv _ _ (leg V)) ≫
        adjunctionBitensorMap adjf AS BW τf (Lp.obj U) (Lp.obj V) =
      adjunctionBitensorMap adja AS BX τa U V ≫ adjf.homEquiv _ _ (leg (BX.obj (U, V))) ≫
        Rf.map (τp.app (U, V)) := by
  apply (adjf.homEquiv _ _).symm.injective
  rw [homEquiv_symm_adjunctionBitensorMap, ← Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_naturality_left_symm]
  dsimp only [Functor.comp_obj, Functor.prod_obj]
  simp only [Equiv.symm_apply_apply]
  have hτ : ∀ P Q : CS, τf.app (P, Q) =
      c.inv.app (AS.obj (P, Q)) ≫ Lp.map (τa.app (P, Q)) ≫ τp.app (La.obj P, La.obj Q) ≫
        BW.map (c.hom.app P ×ₘ c.hom.app Q) := by
    intro P Q
    have h := NatTrans.congr_app hcomp (P, Q)
    change c.hom.app (AS.obj (P, Q)) ≫ τf.app (P, Q) =
      Lp.map (τa.app (P, Q)) ≫ τp.app (La.obj P, La.obj Q) ≫
        BW.map (c.hom.app P ×ₘ c.hom.app Q) at h
    rw [← h, Iso.inv_hom_id_app_assoc]
  have hrel : τa.app (Ra.obj U, Ra.obj V) ≫ BX.map (adja.counit.app U ×ₘ adja.counit.app V) =
      La.map (adjunctionBitensorMap adja AS BX τa U V) ≫ adja.counit.app (BX.obj (U, V)) := by
    have h := Equiv.symm_apply_apply (adja.homEquiv _ _)
      (τa.app (Ra.obj U, Ra.obj V) ≫ BX.map (adja.counit.app U ×ₘ adja.counit.app V))
    rw [Adjunction.homEquiv_counit] at h
    exact h.symm
  have hnat := bifunctor_comparison_naturality BX BW τp (adja.counit.app U)
    (adja.counit.app V)
  dsimp only [Functor.comp_obj, Functor.prod_obj] at hnat
  have hc := c.inv.naturality (adjunctionBitensorMap adja AS BX τa U V)
  change Lf.map (adjunctionBitensorMap adja AS BX τa U V) ≫ c.inv.app (Ra.obj (BX.obj (U, V))) =
    c.inv.app (AS.obj (Ra.obj U, Ra.obj V)) ≫
      Lp.map (La.map (adjunctionBitensorMap adja AS BX τa U V)) at hc
  rw [hτ, hleg, hleg, hleg]
  simp only [Category.assoc]
  rw [← BW.map_comp]
  have hpair : (c.hom.app (Ra.obj U) ×ₘ c.hom.app (Ra.obj V)) ≫
      ((c.inv.app (Ra.obj U) ≫ Lp.map (adja.counit.app U)) ×ₘ
        (c.inv.app (Ra.obj V) ≫ Lp.map (adja.counit.app V))) =
      (Lp.map (adja.counit.app U) ×ₘ Lp.map (adja.counit.app V)) := by
    rw [prod_comp, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app_assoc]
  rw [hpair, ← hnat, ← Lp.map_comp_assoc, hrel, Lp.map_comp_assoc, reassoc_of% hc]
  rfl

end Legs

/-! ### Read on global sections -/

section Sections

variable {CA : Type u₁} [Category.{v₁} CA] {CS : Type u₂} [Category.{v₂} CS]
  {CX : Type u₃} [Category.{v₃} CX] {CY : Type u₄} [Category.{v₄} CY]
  {CW : Type u₅} [Category.{v₅} CW]
  (T : CA × CA ⥤ CA) (BS : CS × CS ⥤ CS) (RS : CS ⥤ CA) (μ : RS.prod RS ⋙ T ⟶ BS ⋙ RS)
  {Ga : CX ⥤ CS} {Gb : CY ⥤ CS} {Gf : CW ⥤ CS} {Fa : CX ⥤ CA} {Fb : CY ⥤ CA} {Ff : CW ⥤ CA}
  (la : Ga ⋙ RS ≅ Fa) (lb : Gb ⋙ RS ≅ Fb) (lf : Gf ⋙ RS ≅ Ff)

/-- **Two maps on global sections induced through Leray-type isomorphisms, followed by a cup
product on the target read through the same isomorphisms**, are the cup product on the base
followed by the two maps and the relative product. -/
theorem sections_comp_cup {K : CX} {M : CY} {K' M' N : CW} (x : Ga.obj K ⟶ Gf.obj K')
    (y : Gb.obj M ⟶ Gf.obj M') (rel : BS.obj (Gf.obj K', Gf.obj M') ⟶ Gf.obj N) :
    T.map ((la.inv.app K ≫ RS.map x ≫ lf.hom.app K') ×ₘ (lb.inv.app M ≫ RS.map y ≫ lf.hom.app M')) ≫
        T.map (lf.inv.app K' ×ₘ lf.inv.app M') ≫ μ.app (Gf.obj K', Gf.obj M') ≫ RS.map rel ≫
          lf.hom.app N =
      T.map (la.inv.app K ×ₘ lb.inv.app M) ≫ μ.app (Ga.obj K, Gb.obj M) ≫
        RS.map (BS.map (x ×ₘ y) ≫ rel) ≫ lf.hom.app N := by
  have hμ := μ.naturality (x ×ₘ y)
  change T.map (RS.map x ×ₘ RS.map y) ≫ μ.app (Gf.obj K', Gf.obj M') =
    μ.app (Ga.obj K, Gb.obj M) ≫ RS.map (BS.map (x ×ₘ y)) at hμ
  rw [← T.map_comp_assoc, prod_comp]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  dsimp only [Functor.comp_obj]
  simp only [Category.comp_id]
  rw [bifunctor_map_comp_both, Category.assoc, reassoc_of% hμ, RS.map_comp_assoc]

/-- **Compatibility of the cup products with the maps on global sections**, from its relative
form `hrel`: the maps `π` induced by `x` are compatible with the cup products on the source and
on the target read through the Leray-type isomorphisms, the right-hand route being continued by
`Ff` of a morphism `t` of the target. -/
theorem sections_cup_compatible {U V UV : CX} {U' V' UV' N : CW} (xU : Ga.obj U ⟶ Gf.obj U')
    (xV : Ga.obj V ⟶ Gf.obj V') (xUV : Ga.obj UV ⟶ Gf.obj UV')
    (relW : BS.obj (Gf.obj U', Gf.obj V') ⟶ Gf.obj N)
    (relX : BS.obj (Ga.obj U, Ga.obj V) ⟶ Ga.obj UV) (t : UV' ⟶ N)
    (hrel : BS.map (xU ×ₘ xV) ≫ relW = relX ≫ xUV ≫ Gf.map t) :
    T.map ((la.inv.app U ≫ RS.map xU ≫ lf.hom.app U') ×ₘ
          (la.inv.app V ≫ RS.map xV ≫ lf.hom.app V')) ≫
        (T.map (lf.inv.app U' ×ₘ lf.inv.app V') ≫ μ.app (Gf.obj U', Gf.obj V') ≫ RS.map relW ≫
          lf.hom.app N) =
      (T.map (la.inv.app U ×ₘ la.inv.app V) ≫ μ.app (Ga.obj U, Ga.obj V) ≫ RS.map relX ≫
          la.hom.app UV) ≫ (la.inv.app UV ≫ RS.map xUV ≫ lf.hom.app UV') ≫ Ff.map t := by
  rw [sections_comp_cup T BS RS μ la la lf xU xV relW, hrel]
  have hl := lf.hom.naturality t
  change RS.map (Gf.map t) ≫ lf.hom.app N = lf.hom.app UV' ≫ Ff.map t at hl
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, RS.map_comp, hl]

end Sections

end Stacks.Cohomology.AdjunctionBitensorPullback
