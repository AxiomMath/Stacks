module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupProductOfCohomologyClasses

/-!
# The counit legs of a Künneth map under a change of the spaces, abstractly

This file proves, over arbitrary categories, functors and adjunctions, the coherence that
compares the counit leg of the relative Künneth map of [Stacks, Tag 0FLP] on one level of ringed
spaces with the counit leg on a second level, through a derived base change map. Everything is
stated for abstract functors and isomorphisms constrained by equations — the composition
isomorphisms of [Stacks, Tag 0D5S], their cocycle identities, and the identification of the
derived adjunction of a composite with the composite adjunction — so that a geometric client
passes its own definitions and leaves the kernel only their delta unfoldings: at the derived
categories of module sheaves the kernel cannot settle definitional equalities between components
of natural transformations in reasonable time (see the implementation notes of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/KunnethBaseChangeLeg.lean`).

## Main results

* `CategoryTheory.KunnethLegRingChange.leg_ringChange`: the coherence of the counit legs, and
  `leg_ringChange'`, `leg_ringChange_of_eq` the same for named legs and transported composites.
* `CategoryTheory.KunnethLegRingChange.kunneth_ringChange`: the Künneth map of the first level,
  read through the composition isomorphisms, is the one of the second level followed by the
  base change maps and the relative cup product of the change of spaces.
-/

@[expose] public section

open CategoryTheory Functor

namespace CategoryTheory.KunnethLegRingChange

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

variable {CS : Type u₁} [Category.{v₁} CS] {CX₂ : Type u₂} [Category.{v₂} CX₂]
  {CX₁ : Type u₃} [Category.{v₃} CX₁] {CW₂ : Type u₄} [Category.{v₄} CW₂]
  {CW₁ : Type u₅} [Category.{v₅} CW₁]

variable {La₂ : CS ⥤ CX₂} {Ra₂ : CX₂ ⥤ CS} (adja₂ : La₂ ⊣ Ra₂)
  {LιX : CX₂ ⥤ CX₁} {RιX : CX₁ ⥤ CX₂} (adjιX : LιX ⊣ RιX)
  {LA : CS ⥤ CX₁} {RA : CX₁ ⥤ CS} (adjA : LA ⊣ RA)
  {LιW : CW₂ ⥤ CW₁} {RιW : CW₁ ⥤ CW₂} (adjιW : LιW ⊣ RιW)
  {Lp₁ : CX₁ ⥤ CW₁} {Lp₂ : CX₂ ⥤ CW₂} {Lf₂ : CS ⥤ CW₂} {Lf₁ LT : CS ⥤ CW₁}
  {Lc Lc' : CX₂ ⥤ CW₁}
  (eXA : La₂ ⋙ LιX ≅ LA) (cX : RιX ⋙ Ra₂ ≅ RA)
  (eP : LA ⋙ Lp₁ ≅ LT) (e₂ : La₂ ⋙ Lp₂ ≅ Lf₂) (eW : Lf₂ ⋙ LιW ≅ Lf₁)
  (compC : LιX ⋙ Lp₁ ≅ Lc) (compC' : Lp₂ ⋙ LιW ≅ Lc')
  (compCA : La₂ ⋙ Lc ≅ LT) (compC'A : La₂ ⋙ Lc' ≅ Lf₁)

/-- **The coherence of the counit legs under a change of the spaces.** The data are those of
two commutative squares `p₁ ≫ ι_X = ι_W ≫ p₂` and of `a₁ = ι_X ≫ a₂`, `f₂ = p₂ ≫ a₂`,
`f₁ = ι_W ≫ f₂`, read through their derived functors: `eXA`, `eP`, `e₂`, `eW`, `compC`,
`compC'`, `compCA`, `compC'A` are composition isomorphisms, `cX` the composition isomorphism of
the right adjoints, `hadjA` the identification of the adjunction of `a₁` with the composite
adjunction, `hX` and `hW` the cocycle identities, and `hcA` the transport of the composition
isomorphism with `a₂` along `ι_W ≫ p₂ = p₁ ≫ ι_X`. The counit leg of the first level, read
through `cX`, is the counit leg of the second level followed by the base change map, the mate
of the comparison of the two iterated pullbacks, and the counit of `Lι_W ⊣ Rι_W`. -/
theorem leg_ringChange
    (hadjA : ((adja₂.comp adjιX).ofNatIsoLeft eXA).ofNatIsoRight cX = adjA)
    (hX : isoWhiskerLeft La₂ compC ≪≫ compCA =
      (Functor.associator La₂ LιX Lp₁).symm ≪≫ isoWhiskerRight eXA Lp₁ ≪≫ eP)
    (hW : isoWhiskerLeft La₂ compC' ≪≫ compC'A =
      (Functor.associator La₂ Lp₂ LιW).symm ≪≫ isoWhiskerRight e₂ LιW ≪≫ eW)
    (hc : Lc' = Lc) (hT : Lf₁ = LT)
    (hcA : isoWhiskerLeft La₂ (eqToIso hc) ≪≫ compCA = compC'A ≪≫ eqToIso hT)
    (K : CX₁) :
    LιW.map (Lf₂.map (cX.hom.app K)) ≫ eW.hom.app (RA.obj K) ≫
        eqToHom (congrArg (fun F : CS ⥤ CW₁ => F.obj (RA.obj K)) hT) ≫
        eP.inv.app (RA.obj K) ≫ Lp₁.map (adjA.counit.app K) =
      LιW.map (e₂.inv.app (Ra₂.obj (RιX.obj K)) ≫
          Lp₂.map (adja₂.counit.app (RιX.obj K))) ≫
        LιW.map ((mateEquiv adjιX adjιW (TwoSquare.mk _ _ _ _
          ((compC' ≪≫ eqToIso hc).hom ≫ compC.inv))).app K) ≫
        adjιW.counit.app (Lp₁.obj K) := by
  subst hadjA hc hT
  have hX' := congrArg (fun e => e.inv.app (Ra₂.obj (RιX.obj K))) hX
  have hW' := congrArg (fun e => e.hom.app (Ra₂.obj (RιX.obj K))) hW
  have hcA' := congrArg (fun e => e.hom.app (Ra₂.obj (RιX.obj K))) hcA
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, isoWhiskerLeft_inv,
    isoWhiskerLeft_hom, isoWhiskerRight_inv, isoWhiskerRight_hom, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, associator_hom_app, associator_inv_app, eqToIso_refl,
    Iso.refl_hom, NatTrans.id_app, Category.comp_id, Category.id_comp, comp_obj] at hX' hW' hcA'
  have hmate := mateEquiv_counit adjιX adjιW (TwoSquare.mk _ _ _ _
    ((compC' ≪≫ eqToIso rfl).hom ≫ compC.inv)) K
  simp only [eqToIso_refl, Iso.trans_refl] at hmate
  simp only [Adjunction.ofNatIsoRight_counit, Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, Adjunction.comp_counit_app, eqToHom_refl,
    Category.id_comp, Functor.map_comp, Category.assoc, eqToIso_refl, Iso.trans_refl]
  rw [hmate]
  have n1 := eW.hom.naturality (cX.hom.app K)
  have n2 := eP.inv.naturality (cX.hom.app K)
  have n3 := compC'.hom.naturality (adja₂.counit.app (RιX.obj K))
  have n4 := compC.inv.naturality (adja₂.counit.app (RιX.obj K))
  simp only [Functor.comp_map, Functor.comp_obj] at n1 n2 n3 n4 ⊢
  simp only [reassoc_of% n1, reassoc_of% n2, ← Lp₁.map_comp_assoc, NatTrans.comp_app,
    Category.assoc, reassoc_of% n3, reassoc_of% n4]
  rw [← LA.map_comp_assoc, Iso.hom_inv_id_app]
  dsimp only [Functor.comp_obj]
  simp only [Functor.map_id, Category.id_comp]
  have key : eW.hom.app (Ra₂.obj (RιX.obj K)) ≫ eP.inv.app (Ra₂.obj (RιX.obj K)) ≫
      Lp₁.map (eXA.inv.app (Ra₂.obj (RιX.obj K))) =
      LιW.map (e₂.inv.app (Ra₂.obj (RιX.obj K))) ≫
        compC'.hom.app (La₂.obj (Ra₂.obj (RιX.obj K))) ≫
        compC.inv.app (La₂.obj (Ra₂.obj (RιX.obj K))) := by
    have h5 : eW.hom.app (Ra₂.obj (RιX.obj K)) =
        LιW.map (e₂.inv.app (Ra₂.obj (RιX.obj K))) ≫
          compC'.hom.app (La₂.obj (Ra₂.obj (RιX.obj K))) ≫
          compCA.hom.app (Ra₂.obj (RιX.obj K)) := by
      rw [hcA', hW', ← LιW.map_comp_assoc, Iso.inv_hom_id_app, LιW.map_id, Category.id_comp]
    rw [← hX', h5]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  simp only [Functor.map_comp, ← reassoc_of% key, Category.assoc]

/-- **The coherence of the counit legs, for the legs themselves.** `leg_ringChange` with the two
counit legs named: `leg₁` is the transport along `hT` of the counit leg built from `eP` and the
counit of `adjA`, and `leg₂` the transport along an arbitrary self-equality of the counit leg built
from `e₂` and the counit of `adja₂`, which is the shape of
`Stacks.Cohomology.DerivedKunneth.pullbackCounitLeg`. -/
theorem leg_ringChange'
    (hadjA : ((adja₂.comp adjιX).ofNatIsoLeft eXA).ofNatIsoRight cX = adjA)
    (hX : isoWhiskerLeft La₂ compC ≪≫ compCA =
      (Functor.associator La₂ LιX Lp₁).symm ≪≫ isoWhiskerRight eXA Lp₁ ≪≫ eP)
    (hW : isoWhiskerLeft La₂ compC' ≪≫ compC'A =
      (Functor.associator La₂ Lp₂ LιW).symm ≪≫ isoWhiskerRight e₂ LιW ≪≫ eW)
    (hc : Lc' = Lc) (hT : Lf₁ = LT)
    (hcA : isoWhiskerLeft La₂ (eqToIso hc) ≪≫ compCA = compC'A ≪≫ eqToIso hT)
    (leg₁ : RA ⋙ Lf₁ ⟶ Lp₁) (hT' : RA ⋙ Lf₁ = RA ⋙ LT)
    (hleg₁ : leg₁ = eqToHom hT' ≫ Functor.whiskerLeft RA eP.inv ≫
      (Functor.associator RA LA Lp₁).inv ≫ Functor.whiskerRight adjA.counit Lp₁ ≫
        (Functor.leftUnitor Lp₁).hom)
    (leg₂ : Ra₂ ⋙ Lf₂ ⟶ Lp₂) (h₂ : Ra₂ ⋙ Lf₂ = Ra₂ ⋙ Lf₂)
    (hleg₂ : leg₂ = eqToHom h₂ ≫ Functor.whiskerLeft Ra₂ e₂.inv ≫
      (Functor.associator Ra₂ La₂ Lp₂).inv ≫ Functor.whiskerRight adja₂.counit Lp₂ ≫
      (Functor.leftUnitor Lp₂).hom)
    (K : CX₁) :
    LιW.map (Lf₂.map (cX.hom.app K)) ≫ eW.hom.app (RA.obj K) ≫ leg₁.app K =
      LιW.map (leg₂.app (RιX.obj K)) ≫
        LιW.map ((mateEquiv adjιX adjιW (TwoSquare.mk _ _ _ _
          ((compC' ≪≫ eqToIso hc).hom ≫ compC.inv))).app K) ≫
        adjιW.counit.app (Lp₁.obj K) := by
  have h := leg_ringChange adja₂ adjιX adjA adjιW eXA cX eP e₂ eW compC compC' compCA compC'A
    hadjA hX hW hc hT hcA K
  subst hleg₁ hleg₂
  simp only [NatTrans.comp_app, eqToHom_app, eqToHom_refl, Category.id_comp,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app,
    Functor.leftUnitor_hom_app, Functor.comp_obj, Functor.id_obj] at h ⊢
  simpa only [Category.comp_id] using h

/-- **The coherence of the counit legs, with transported composites.** `leg_ringChange'` for a
second-level leg built from a composition isomorphism `e₂ : La₂ ⋙ Lp₂ ≅ LT₂` into a functor
equal, by `hT₂`, to the derived pullback `Lf₂` the leg is indexed by, and for a composition
isomorphism `eW'` out of `LT₂ ⋙ Lι_W` related to `eW` by the transport `heW`. This is the shape
of a leg over the second projection of a fibre product, where `q ≫ b = p ≫ a` holds only up to a
proof. -/
theorem leg_ringChange_of_eq {LT₂ : CS ⥤ CW₂} {LG : CS ⥤ CW₁}
    (e₂' : La₂ ⋙ Lp₂ ≅ LT₂) (eW' : LT₂ ⋙ LιW ≅ LG) (compC'A' : La₂ ⋙ Lc' ≅ LG)
    (hadjA : ((adja₂.comp adjιX).ofNatIsoLeft eXA).ofNatIsoRight cX = adjA)
    (hX : isoWhiskerLeft La₂ compC ≪≫ compCA =
      (Functor.associator La₂ LιX Lp₁).symm ≪≫ isoWhiskerRight eXA Lp₁ ≪≫ eP)
    (hW : isoWhiskerLeft La₂ compC' ≪≫ compC'A' =
      (Functor.associator La₂ Lp₂ LιW).symm ≪≫ isoWhiskerRight e₂' LιW ≪≫ eW')
    (hT₂ : Lf₂ = LT₂) (hG : Lf₁ = LG)
    (heW : isoWhiskerRight (eqToIso hT₂) LιW ≪≫ eW' = eW ≪≫ eqToIso hG)
    (hc : Lc' = Lc) (hT : LG = LT)
    (hcA : isoWhiskerLeft La₂ (eqToIso hc) ≪≫ compCA = compC'A' ≪≫ eqToIso hT)
    (leg₁ : RA ⋙ Lf₁ ⟶ Lp₁) (hT' : RA ⋙ Lf₁ = RA ⋙ LT)
    (hleg₁ : leg₁ = eqToHom hT' ≫ Functor.whiskerLeft RA eP.inv ≫
      (Functor.associator RA LA Lp₁).inv ≫ Functor.whiskerRight adjA.counit Lp₁ ≫
      (Functor.leftUnitor Lp₁).hom)
    (leg₂ : Ra₂ ⋙ Lf₂ ⟶ Lp₂) (h₂ : Ra₂ ⋙ Lf₂ = Ra₂ ⋙ LT₂)
    (hleg₂ : leg₂ = eqToHom h₂ ≫ Functor.whiskerLeft Ra₂ e₂'.inv ≫
      (Functor.associator Ra₂ La₂ Lp₂).inv ≫ Functor.whiskerRight adja₂.counit Lp₂ ≫
      (Functor.leftUnitor Lp₂).hom)
    (bc : TwoSquare RιX Lp₁ Lp₂ RιW)
    (hbc : bc = mateEquiv adjιX adjιW (TwoSquare.mk _ _ _ _
      ((compC' ≪≫ eqToIso hc).hom ≫ compC.inv)))
    (K : CX₁) :
    LιW.map (Lf₂.map (cX.hom.app K)) ≫ eW.hom.app (RA.obj K) ≫ leg₁.app K =
      LιW.map (leg₂.app (RιX.obj K)) ≫ LιW.map (bc.app K) ≫ adjιW.counit.app (Lp₁.obj K) := by
  subst hT₂ hG hbc
  have heW' : eW' = eW := by
    simpa only [eqToIso_refl, isoWhiskerRight_refl, Iso.refl_trans, Iso.trans_refl] using heW
  subst heW'
  exact leg_ringChange' adja₂ adjιX adjA adjιW eXA cX eP e₂' eW' compC compC' compCA compC'A'
    hadjA hX hW hc hT (by simpa only [eqToIso_refl, Iso.trans_refl] using hcA) leg₁ hT' hleg₁
    leg₂ h₂ hleg₂ K


section Assembly

universe w₁ w₂ w₃ w₄ w₅ w₆ w₇ t₁ t₂ t₃ t₄ t₅ t₆ t₇

variable {DS : Type t₁} [Category.{w₁} DS] {DW₂ : Type t₂} [Category.{w₂} DW₂]
  {DW₁ : Type t₃} [Category.{w₃} DW₁] {DX₁ : Type t₄} [Category.{w₄} DX₁]
  {DY₁ : Type t₅} [Category.{w₅} DY₁] {DX₂ : Type t₆} [Category.{w₆} DX₂]
  {DY₂ : Type t₇} [Category.{w₇} DY₂]
  {Lf₂ : DS ⥤ DW₂} {Rf₂ : DW₂ ⥤ DS} (adj₂ : Lf₂ ⊣ Rf₂)
  {LιW : DW₂ ⥤ DW₁} {RιW : DW₁ ⥤ DW₂} (adjW : LιW ⊣ RιW)
  {Lf₁ : DS ⥤ DW₁} {Rf₁ : DW₁ ⥤ DS} (adj₁ : Lf₁ ⊣ Rf₁)
  (cl : Lf₂ ⋙ LιW ≅ Lf₁) (cr : RιW ⋙ Rf₂ ≅ Rf₁)
  (TS : DS × DS ⥤ DS) (T₂ : DW₂ × DW₂ ⥤ DW₂) (T₁ : DW₁ × DW₁ ⥤ DW₁)
  (α₂ : TS ⋙ Lf₂ ⟶ Lf₂.prod Lf₂ ⋙ T₂) (β : T₂ ⋙ LιW ⟶ LιW.prod LιW ⋙ T₁)
  (α₁ : TS ⋙ Lf₁ ⟶ Lf₁.prod Lf₁ ⋙ T₁)
  {R₁ : DX₁ ⥤ DS} {P₁ : DX₁ ⥤ DW₁} (leg₁ : R₁ ⋙ Lf₁ ⟶ P₁)
  {R₂ : DY₁ ⥤ DS} {P₂ : DY₁ ⥤ DW₁} (leg₂ : R₂ ⋙ Lf₁ ⟶ P₂)
  {R₁' : DX₂ ⥤ DS} {P₁' : DX₂ ⥤ DW₂} (leg₁' : R₁' ⋙ Lf₂ ⟶ P₁')
  {R₂' : DY₂ ⥤ DS} {P₂' : DY₂ ⥤ DW₂} (leg₂' : R₂' ⋙ Lf₂ ⟶ P₂')
  {RιX : DX₁ ⥤ DX₂} {RιY : DY₁ ⥤ DY₂} (cX : RιX ⋙ R₁' ≅ R₁) (cY : RιY ⋙ R₂' ≅ R₂)

open scoped CategoryTheory.Prod in
/-- **The Künneth map of [Stacks, Tag 0FLP] under a change of the spaces, abstractly.** Let
`adj₁` be the composite of `adj₂` and `adjW` transported along `cl` and `cr`, and let the
pullback–tensor comparison `α₁` be the composite of `α₂` and `β` transported along `cl`. If the
counit legs on the first level are those of the second level followed by morphisms
`μ₁ K : P₁'(Rι_X K) ⟶ Rι_W(P₁ K)` and `μ₂ M`, in the transposed form `hL₁` and `hL₂`, then the
Künneth map of the first level, read through `cX` and `cY`, is the one of the second level at
`Rι_X K` and `Rι_Y M` followed by `Rf₂` of `μ₁ ⊗ μ₂` and of the relative cup product of
`adjW`. -/
theorem kunneth_ringChange
    (hadj : ((adj₂.comp adjW).ofNatIsoLeft cl).ofNatIsoRight cr = adj₁)
    (hα : Functor.whiskerLeft TS cl.hom ≫ α₁ =
      (Functor.whiskerRight α₂ LιW ≫ Functor.whiskerLeft (Lf₂.prod Lf₂) β) ≫
        Functor.whiskerRight (NatTrans.prod cl.hom cl.hom) T₁)
    (K : DX₁) (M : DY₁)
    (μ₁ : P₁'.obj (RιX.obj K) ⟶ RιW.obj (P₁.obj K)) (μ₂ : P₂'.obj (RιY.obj M) ⟶ RιW.obj (P₂.obj M))
    (hL₁ : LιW.map (Lf₂.map (cX.hom.app K)) ≫ cl.hom.app (R₁.obj K) ≫ leg₁.app K =
      LιW.map (leg₁'.app (RιX.obj K)) ≫ LιW.map μ₁ ≫ adjW.counit.app (P₁.obj K))
    (hL₂ : LιW.map (Lf₂.map (cY.hom.app M)) ≫ cl.hom.app (R₂.obj M) ≫ leg₂.app M =
      LιW.map (leg₂'.app (RιY.obj M)) ≫ LιW.map μ₂ ≫ adjW.counit.app (P₂.obj M)) :
    TS.map (cX.hom.app K ×ₘ cY.hom.app M) ≫
        Stacks.Cohomology.DerivedKunneth.adjunctionBitensorMap adj₁ TS T₁ α₁ leg₁ leg₂ K M =
      Stacks.Cohomology.DerivedKunneth.adjunctionBitensorMap adj₂ TS T₂ α₂ leg₁' leg₂'
          (RιX.obj K) (RιY.obj M) ≫
        Rf₂.map (T₂.map (μ₁ ×ₘ μ₂) ≫
          Stacks.Cohomology.DerivedRelativeCupProduct.adjunctionBitensorMap adjW T₂ T₁ β
            (P₁.obj K) (P₂.obj M)) ≫
        cr.hom.app (T₁.obj (P₁.obj K, P₂.obj M)) := by
  subst hadj
  unfold Stacks.Cohomology.DerivedKunneth.adjunctionBitensorMap
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_ofNatIsoLeft_apply,
    Adjunction.comp_homEquiv, Equiv.trans_apply, ← Category.assoc,
    ← Adjunction.homEquiv_naturality_left]
  conv_rhs => rw [← Category.assoc, ← Adjunction.homEquiv_naturality_right]
  congr 2
  rw [← Adjunction.homEquiv_naturality_left]
  apply (adjW.homEquiv _ _).symm.injective
  have hT : T₂.map (leg₁'.app (RιX.obj K) ×ₘ leg₂'.app (RιY.obj M)) ≫ T₂.map (μ₁ ×ₘ μ₂) =
      T₂.map ((leg₁'.app (RιX.obj K) ≫ μ₁) ×ₘ (leg₂'.app (RιY.obj M) ≫ μ₂)) := by
    rw [← T₂.map_comp]; rfl
  rw [Equiv.symm_apply_apply, Category.assoc, ← Category.assoc (T₂.map _), hT,
    Adjunction.homEquiv_naturality_left_symm]
  dsimp only [Functor.comp_obj, Functor.prod_obj]
  rw [Stacks.Cohomology.DerivedRelativeCupProduct.homEquiv_symm_adjunctionBitensorMap,
    Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  have n1 := cl.hom.naturality (TS.map (cX.hom.app K ×ₘ cY.hom.app M))
  have n2 := α₁.naturality (cX.hom.app K ×ₘ cY.hom.app M)
  have hα' := NatTrans.congr_app hα (R₁'.obj (RιX.obj K), R₂'.obj (RιY.obj M))
  simp only [Functor.comp_map, Functor.comp_obj, Functor.prod_map, Functor.prod_obj,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc] at n1 n2 hα'
  rw [reassoc_of% n1, reassoc_of% n2, reassoc_of% hα']
  congr 2
  rw [← T₁.map_comp, ← T₁.map_comp]
  congr 1
  refine Prod.ext ?_ ?_ <;> dsimp
  · simpa [← cl.hom.naturality_assoc] using hL₁
  · simpa [← cl.hom.naturality_assoc] using hL₂

end Assembly

end CategoryTheory.KunnethLegRingChange
