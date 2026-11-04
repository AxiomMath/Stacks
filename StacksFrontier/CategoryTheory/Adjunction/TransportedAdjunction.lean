module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Equivalence

/-!
# Adjunctions transported along equivalences, and squares of them

Let `a : L ⊣ R` be an adjunction between `A` and `B`, let `EA : A ≌ A'` and `EB : B ≌ B'` be
equivalences, and let `b : L' ⊣ R'` be an adjunction between `A'` and `B'` together with an
identification `π : R' ≅ EB⁻¹ ⋙ R ⋙ EA` of right adjoints. Then `L'` is identified with the
transported left adjoint `EA⁻¹ ⋙ L ⋙ EB` by the uniqueness of left adjoints. This file records the
compatibility of the resulting comparisons `R ⋙ EA ≅ EB ⋙ R'` and `EA ⋙ L' ≅ L ⋙ EB` with the
units and counits, and the transport of the comparison of the two composite pullbacks around a
commutative square of adjunctions.

## Main definitions

* `Stacks.CategoryTheory.TransportedAdjunction.rightComparison` and `.leftComparison`: the
  comparisons of right and of left adjoints.

## Main results

* `Stacks.CategoryTheory.TransportedAdjunction.leftComparison_counit` and
  `.unit_leftComparison`: the compatibility with counits and units.
* `Stacks.CategoryTheory.TransportedAdjunction.square_transport`: a comparison of the two composite
  pushforwards around a square which is carried to another one by the pushforward comparisons
  forces the corresponding comparisons of composite pullbacks to be carried to each other.

## Implementation notes

`square_transport` is stated for arbitrary functors `Φ` and arbitrary comparisons, with the
compatibility with the units as hypotheses; for the comparisons of this file those hypotheses
are `unit_leftComparison`. Its proof compares adjuncts under the composite adjunction of the
second square.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory.TransportedAdjunction

variable {A A' B B' : Type*} [Category A] [Category A'] [Category B] [Category B']
  (EA : A ≌ A') (EB : B ≌ B') {L : A ⥤ B} {R : B ⥤ A} (a : L ⊣ R)
  {L' : A' ⥤ B'} {R' : B' ⥤ A'} (b : L' ⊣ R') (π : R' ≅ EB.inverse ⋙ R ⋙ EA.functor)

/-- The adjunction `EA⁻¹ ⋙ L ⋙ EB ⊣ R'` obtained by transporting `a : L ⊣ R` along the
equivalences and identifying the transported right adjoint with `R'` through `π`. -/
noncomputable abbrev transported : EA.inverse ⋙ L ⋙ EB.functor ⊣ R' :=
  (EA.symm.toAdjunction.comp (a.comp EB.toAdjunction)).ofNatIsoRight π.symm

/-- The comparison `R ⋙ EA ≅ EB ⋙ R'` of right adjoints, read off `π`. -/
noncomputable def rightComparison : R ⋙ EA.functor ≅ EB.functor ⋙ R' :=
  ((Functor.isoWhiskerLeft EB.functor π) ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight EB.unitIso.symm _ ≪≫ Functor.leftUnitor _).symm

/-- The comparison `EA ⋙ L' ≅ L ⋙ EB` of left adjoints: the uniqueness of the left adjoint of
`R'`, applied to `b` and to the transported adjunction. -/
noncomputable def leftComparison : EA.functor ⋙ L' ≅ L ⋙ EB.functor :=
  (Functor.isoWhiskerLeft EA.functor (b.leftAdjointUniq (transported EA EB a π))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight EA.unitIso.symm _ ≪≫ Functor.leftUnitor _

/-- **The left comparison is compatible with the counits**: `L'` of the right comparison followed
by the counit of `b` is the left comparison followed by `EB` of the counit of `a`. -/
theorem leftComparison_counit (K : B) :
    L'.map ((rightComparison EA EB π).hom.app K) ≫ b.counit.app (EB.functor.obj K) =
      (leftComparison EA EB a b π).hom.app (R.obj K) ≫ EB.functor.map (a.counit.app K) := by
  have h := Adjunction.leftAdjointUniq_hom_app_counit b (transported EA EB a π)
    (EB.functor.obj K)
  rw [← h]
  simp only [Functor.comp_obj, Functor.id_obj, rightComparison, Iso.trans_symm, Iso.symm_symm_eq,
    Iso.trans_assoc, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_inv, Iso.symm_inv,
    Functor.isoWhiskerLeft_inv, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.whiskerRight_app, Functor.comp_map, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Category.id_comp, Functor.map_comp, transported, Equivalence.symm_inverse,
    Equivalence.symm_functor, Adjunction.ofNatIsoRight_counit, Adjunction.comp_counit_app,
    Equivalence.toAdjunction_counit, Equivalence.symm_counit, Category.assoc,
    NatTrans.naturality_assoc, Equivalence.inv_fun_map, leftComparison, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.associator_inv_app, Functor.leftUnitor_hom_app,
    Category.comp_id, NatIso.cancel_natIso_hom_left]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj]
  simp only [Functor.map_id, Category.id_comp]
  rw [show EA.unit.app (R.obj (EB.inverse.obj (EB.functor.obj K))) ≫
      EA.unitInv.app (R.obj (EB.inverse.obj (EB.functor.obj K))) = 𝟙 _ from
    EA.unitIso.hom_inv_id_app _]
  dsimp only [Functor.id_obj]
  rw [Category.comp_id]
  have hn := a.counit.naturality (EB.unitIso.hom.app K)
  dsimp at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [← EB.functor.map_comp_assoc (L.map (R.map _)), hn, Functor.map_comp_assoc,
    Equivalence.functor_unit_comp, Category.comp_id]

/-- **The left comparison is compatible with the units**: the unit of `b` followed by `R'` of the
left comparison is `EA` of the unit of `a` followed by the right comparison. -/
theorem unit_leftComparison (K : A) :
    b.unit.app (EA.functor.obj K) ≫ R'.map ((leftComparison EA EB a b π).hom.app K) =
      EA.functor.map (a.unit.app K) ≫ (rightComparison EA EB π).hom.app (L.obj K) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app b (transported EA EB a π) (EA.functor.obj K)
  simp only [Functor.id_obj, Functor.comp_obj, transported, Equivalence.symm_inverse,
    Equivalence.symm_functor, Adjunction.unit_leftAdjointUniq_hom_app,
    Adjunction.ofNatIsoRight_unit, Iso.symm_hom, NatTrans.comp_app, Adjunction.comp_unit_app,
    Equivalence.toAdjunction_unit, Equivalence.symm_unit, Functor.map_comp, Functor.whiskerLeft_app,
    Category.assoc, leftComparison, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.associator_inv_app, Functor.whiskerRight_app,
    Functor.comp_map, Functor.leftUnitor_hom_app, Category.comp_id, Category.id_comp,
    Adjunction.unit_leftAdjointUniq_hom_app_assoc, rightComparison, Iso.trans_symm,
    Iso.symm_symm_eq, Iso.trans_assoc, Functor.isoWhiskerRight_inv, Iso.symm_inv,
    Functor.isoWhiskerLeft_inv, Functor.leftUnitor_inv_app, Functor.associator_hom_app] at h ⊢
  have n1 := a.unit.naturality (EA.unitIso.inv.app K)
  have n2 := EB.unit.naturality (L.map (EA.unitIso.inv.app K))
  have n3 := π.inv.naturality (EB.functor.map (L.map (EA.unitIso.inv.app K)))
  dsimp at n1 n2 n3
  rw [← n3]
  simp only [← Functor.map_comp_assoc, ← R.map_comp]
  rw [← n2, R.map_comp, ← Category.assoc (a.unit.app _), ← n1]
  simp

/-- The identification of right adjoints `R' ≅ EB⁻¹ ⋙ R ⋙ EA` read off a comparison
`R ⋙ EA ≅ EB ⋙ R'`; `rightComparison` of it is the comparison one started with
(`rightComparison_piOfRightComparison`). -/
noncomputable def piOfRightComparison {R : B ⥤ A} {R' : B' ⥤ A'}
    (c : R ⋙ EA.functor ≅ EB.functor ⋙ R') :
    R' ≅ EB.inverse ⋙ R ⋙ EA.functor :=
  (Functor.leftUnitor R').symm ≪≫ Functor.isoWhiskerRight EB.counitIso.symm R' ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft EB.inverse c.symm

/-- The right comparison of `piOfRightComparison EA EB c` is the comparison `c` itself. -/
theorem rightComparison_piOfRightComparison {R : B ⥤ A} {R' : B' ⥤ A'}
    (c : R ⋙ EA.functor ≅ EB.functor ⋙ R') :
    rightComparison EA EB (piOfRightComparison EA EB c) = c := by
  ext K
  have h := c.hom.naturality (EB.unitIso.hom.app K)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at h
  simp only [rightComparison, piOfRightComparison]
  simp only [Functor.comp_obj, Functor.isoWhiskerLeft_trans, Functor.isoWhiskerLeft_twice,
    Iso.trans_assoc, Iso.self_symm_id_assoc, Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_hom,
    Iso.symm_hom, Functor.isoWhiskerRight_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv,
    NatTrans.comp_app, Functor.id_obj, Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
    Functor.comp_map, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app, Category.comp_id, Category.id_comp]
  rw [reassoc_of% h, ← R'.map_comp]
  simp

section Square

variable {VY VX VY' VX' RY RX RY' RX' : Type*}
  [Category VY] [Category VX] [Category VY'] [Category VX']
  [Category RY] [Category RX] [Category RY'] [Category RX']
  {ΦY : VY ⥤ RY} {ΦX : VX ⥤ RX} {ΦY' : VY' ⥤ RY'} {ΦX' : VX' ⥤ RX'}
  {pf : VY ⥤ VX} {qf : VX ⥤ VY} {pg : VY ⥤ VY'} {qg : VY' ⥤ VY}
  {pf' : VY' ⥤ VX'} {qf' : VX' ⥤ VY'} {pg' : VX ⥤ VX'} {qg' : VX' ⥤ VX}
  {rf : RY ⥤ RX} {sf : RX ⥤ RY} {rg : RY ⥤ RY'} {sg : RY' ⥤ RY}
  {rf' : RY' ⥤ RX'} {sf' : RX' ⥤ RY'} {rg' : RX ⥤ RX'} {sg' : RX' ⥤ RX}
  (af : pf ⊣ qf) (ag : pg ⊣ qg) (af' : pf' ⊣ qf') (ag' : pg' ⊣ qg')
  (bf : rf ⊣ sf) (bg : rg ⊣ sg) (bf' : rf' ⊣ sf') (bg' : rg' ⊣ sg')
  (cf : qf ⋙ ΦY ⟶ ΦX ⋙ sf) (cg : qg ⋙ ΦY ⟶ ΦY' ⋙ sg)
  (cf' : qf' ⋙ ΦY' ⟶ ΦX' ⋙ sf') (cg' : qg' ⋙ ΦX ⟶ ΦX' ⋙ sg')
  (mf : ΦY ⋙ rf ⟶ pf ⋙ ΦX) (mg : ΦY ⋙ rg ⟶ pg ⋙ ΦY')
  (mf' : ΦY' ⋙ rf' ⟶ pf' ⋙ ΦX') (mg' : ΦX ⋙ rg' ⟶ pg' ⋙ ΦX')
  (SV : pg ⋙ pf' ≅ pf ⋙ pg') (ρV : qg' ⋙ qf ⟶ qf' ⋙ qg)
  (S : rg ⋙ rf' ≅ rf ⋙ rg') (ρR : sg' ⋙ sf ⟶ sf' ⋙ sg)

/-- **Transport of the comparison of the two pullbacks around a square.** Consider two squares of
adjunctions (pullbacks `p`, `r` left adjoint to pushforwards `q`, `s`), related by functors `Φ`,
by comparisons `c : q ⋙ Φ ⟶ Φ ⋙ s` of the pushforwards and `m : Φ ⋙ r ⟶ p ⋙ Φ` of the
pullbacks compatible with the units (`uf`, `ug`, `uf'`, `ug'`). Let `SV` and `S` be isomorphisms
of the two composite pullbacks around each square, characterized against isomorphisms `ρV`, `ρR`
of the two composite pushforwards through the units of the composite adjunctions (`hV`, `hR`).
If the comparisons of the pushforwards carry `ρV` to `ρR` (`hP`), then the comparisons of the
pullbacks carry `SV` to `S`. -/
theorem square_transport
    (uf : ∀ K, bf.unit.app (ΦY.obj K) ≫ sf.map (mf.app K) =
      ΦY.map (af.unit.app K) ≫ cf.app (pf.obj K))
    (ug : ∀ K, bg.unit.app (ΦY.obj K) ≫ sg.map (mg.app K) =
      ΦY.map (ag.unit.app K) ≫ cg.app (pg.obj K))
    (uf' : ∀ K, bf'.unit.app (ΦY'.obj K) ≫ sf'.map (mf'.app K) =
      ΦY'.map (af'.unit.app K) ≫ cf'.app (pf'.obj K))
    (ug' : ∀ K, bg'.unit.app (ΦX.obj K) ≫ sg'.map (mg'.app K) =
      ΦX.map (ag'.unit.app K) ≫ cg'.app (pg'.obj K))
    (hV : ∀ K, ag.unit.app K ≫ qg.map (af'.unit.app (pg.obj K)) ≫ qg.map (qf'.map (SV.hom.app K)) =
      af.unit.app K ≫ qf.map (ag'.unit.app (pf.obj K)) ≫ ρV.app (pg'.obj (pf.obj K)))
    (hR : ∀ K, bg.unit.app K ≫ sg.map (bf'.unit.app (rg.obj K)) ≫ sg.map (sf'.map (S.hom.app K)) =
      bf.unit.app K ≫ sf.map (bg'.unit.app (rf.obj K)) ≫ ρR.app (rg'.obj (rf.obj K)))
    (hP : ∀ M, cf.app (qg'.obj M) ≫ sf.map (cg'.app M) ≫ ρR.app (ΦX'.obj M) =
      ΦY.map (ρV.app M) ≫ cg.app (qf'.obj M) ≫ sg.map (cf'.app M))
    (K : VY) :
    S.hom.app (ΦY.obj K) ≫ rg'.map (mf.app K) ≫ mg'.app (pf.obj K) =
      rf'.map (mg.app K) ≫ mf'.app (pg.obj K) ≫ ΦX'.map (SV.hom.app K) := by
  apply ((bg.comp bf').homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Adjunction.comp_unit_app, Functor.comp_map, Functor.map_comp,
    Category.assoc]
  rw [reassoc_of% (hR (ΦY.obj K))]
  have n1 := ρR.naturality (rg'.map (mf.app K))
  have n2 := ρR.naturality (mg'.app (pf.obj K))
  have n3 := bg'.unit.naturality (mf.app K)
  have n4 := cf.naturality (ag'.unit.app (pf.obj K))
  have n1' := bf'.unit.naturality (mg.app K)
  have n4' := cg.naturality (af'.unit.app (pg.obj K))
  have n5' := cf'.naturality (SV.hom.app K)
  have n6' := cg.naturality (qf'.map (SV.hom.app K))
  have h7 := congrArg ΦY.map (hV K)
  dsimp at n1 n2 n3 n4 n1' n4' n5' n6'
  simp only [Functor.map_comp] at h7
  rw [← reassoc_of% n1, ← n2, ← sf.map_comp_assoc, ← n3, sf.map_comp_assoc,
    reassoc_of% (uf K), ← sf.map_comp_assoc, ug', sf.map_comp_assoc, ← reassoc_of% n4, hP]
  rw [← sg.map_comp_assoc, ← n1', sg.map_comp_assoc, reassoc_of% (ug K)]
  rw [← sg.map_comp_assoc, uf', sg.map_comp_assoc, ← reassoc_of% n4',
    ← sg.map_comp, ← n5', sg.map_comp, ← reassoc_of% n6']
  simp only [← Category.assoc] at h7 ⊢
  rw [h7]

end Square

end Stacks.CategoryTheory.TransportedAdjunction
