module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiStructureSheaf
public import StacksCore.Tactic.StacksAttribute

/-!
# Modules on the small Zariski site and on a scheme

The category of modules over the structure sheaf of the small Zariski site of a scheme is
equivalent to the category of sheaves of modules on the scheme, and the equivalence is the
usual comparison on sections: an object of the small Zariski site is an open subscheme, and the
sections of a module over it are the sections of the corresponding module over its open image.

## Main definitions

* `AlgebraicGeometry.SmallZariskiModuleComparison` is the data that an equivalence of these two
  module categories is the usual sectionwise comparison: isomorphisms on sections, linear over
  the canonical structure-sheaf identification and natural in both the site and the module.

## Main results

* `AlgebraicGeometry.smallZariskiModuleEquiv` is the equivalence of module categories.
* `AlgebraicGeometry.smallZariskiModuleEquiv_forgetIso` identifies its underlying-sheaf functor
  with the small-Zariski-site comparison of Tag 020X.
* `AlgebraicGeometry.smallZariskiModuleEquiv_comparison` exhibits the equivalence as the usual
  sectionwise comparison.

## Implementation notes

Both sides use the same arbitrary module universe, so the comparison also applies to sheaves
whose sections are larger than the scheme's universe. On the site side the ring sheaf is
`AlgebraicGeometry.SmallZariski.structureSheaf`.

The equivalence is `SheafOfModules.pushforwardPushforwardEquivalence` applied to the
equivalence of sites of Tag 020X, so the two triangle identities it asks for are the content
of the construction; both are checked on sections, where they come down to the structure-sheaf
comparison `AlgebraicGeometry.smallZariskiStructureSheaf_pullbackIso` being an isomorphism and
to naturality of the canonical isomorphism `AlgebraicGeometry.openImmersion_ΓIsoTop_inv` on
global functions.

`smallZariskiModuleEquiv_forgetIso` records that the equivalence is the usual one on underlying
sheaves rather than merely an abstract equivalence of categories, and
`smallZariskiModuleEquiv_comparison` records that on sections it is the identity — which is why
`SmallZariskiModuleComparison` is a structure rather than a conjunction: its four fields are
what a consumer needs, and they are all `rfl`.

## References

* [Stacks Project, Tag 03FG](https://stacks.math.columbia.edu/tag/03FG)
-/

@[expose] public section

open CategoryTheory

universe u m

namespace AlgebraicGeometry

/-- The `RingCat`-valued structure sheaf of a scheme has the restriction maps of its
`CommRingCat`-valued one: the two differ only by `forget₂ CommRingCat RingCat`, so a section of
the `CommRingCat`-valued sheaf restricts the same way under either, and naming the identification
keeps proofs from depending on that unfolding silently. -/
public lemma ringCatSheaf_map_apply (S : Scheme.{u}) {U V : (TopologicalSpace.Opens S.carrier)ᵒᵖ}
    (g : U ⟶ V) (x : S.sheaf.obj.obj U) :
    (S.ringCatSheaf.obj.map g) x = (S.sheaf.obj.map g) x := rfl


/-- Sheaves of modules on the small Zariski site are the same as sheaves of
modules on the ringed space of the scheme. -/
@[stacks 03FG "equivalence of module categories"]
public noncomputable def smallZariskiModuleEquiv
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    SheafOfModules.{m} (SmallZariski.structureSheaf B S hS) ≌
      SheafOfModules.{m} S.ringCatSheaf := by
  let E := smallZariskiSiteEquiv B S hS
  let φ : SmallZariski.structureSheaf B S hS ⟶
      (E.functor.sheafPushforwardContinuous RingCat.{u}
        (SmallZariski.topology B S hS)
        (Opens.grothendieckTopology S.carrier)).obj
          S.ringCatSheaf :=
    ObjectProperty.homMk ((smallZariskiStructureSheaf_pullbackIso B S hS).inv.hom)
  let ψ : S.ringCatSheaf ⟶
      (E.inverse.sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology S.carrier)
        (SmallZariski.topology B S hS)).obj
          (SmallZariski.structureSheaf B S hS) :=
    ObjectProperty.homMk ((smallZariskiStructureSheaf_iso B S hS).inv.hom)
  have hψ_hom :
      ψ.hom =
        ((smallZariskiSheafEquivWith B S hS RingCat).counitIso.app
          S.ringCatSheaf).inv.hom ≫
        ((smallZariskiSheafEquivWith B S hS RingCat).functor.map
          (smallZariskiStructureSheaf_pullbackIso B S hS).hom).hom := by
    rfl
  have hleft :
      Functor.whiskerRight (NatTrans.op E.counit) S.ringCatSheaf.obj =
        ((smallZariskiSheafEquivWith B S hS RingCat).counitIso.app
          S.ringCatSheaf).inv.hom := rfl
  have hcancel :
      ((smallZariskiSheafEquivWith B S hS RingCat).functor.map
        (smallZariskiStructureSheaf_pullbackIso B S hS).hom).hom ≫
        E.inverse.op.whiskerLeft φ.hom = 𝟙 _ := by
    ext X x
    have hglobal :
        (smallZariskiStructureSheaf_pullbackIso B S hS).hom ≫
          (smallZariskiStructureSheaf_pullbackIso B S hS).inv = 𝟙 _ :=
      (smallZariskiStructureSheaf_pullbackIso B S hS).hom_inv_id
    have happ := congrArg
      (fun f => f.hom.app (E.inverse.op.obj X)) hglobal
    exact congrArg (fun f => f x) happ
  have h₁ :
      Functor.whiskerRight (NatTrans.op E.counit)
          (S.ringCatSheaf : Sheaf (Opens.grothendieckTopology S.carrier) RingCat).obj =
        ψ.hom ≫ E.inverse.op.whiskerLeft φ.hom := by
    rw [hleft, hψ_hom]
    exact ((congrArg (fun z =>
      ((smallZariskiSheafEquivWith B S hS RingCat).counitIso.app S.ringCatSheaf).inv.hom ≫ z)
      hcancel).trans (Category.comp_id _)).symm
  have htri (X : SmallZariski B S hS) :
      E.functor.map (E.unit.app X) ≫ E.counitIso.hom.app (E.functor.obj X) =
        𝟙 (E.functor.obj X) := E.functor_unitIso_comp X
  have h₂ :
      φ.hom ≫ E.functor.op.whiskerLeft ψ.hom ≫
        Functor.whiskerRight (NatTrans.op E.unit)
          (SmallZariski.structureSheaf B S hS).obj =
        𝟙 (SmallZariski.structureSheaf B S hS).obj := by
    ext X x
    let j := E.unit.app (Opposite.unop X)
    have hαnat :
        S.ringCatSheaf.obj.map (E.functor.map j).op ≫
            (smallZariskiStructureSheaf_pullbackIso B S hS).hom.hom.app X =
          (smallZariskiStructureSheaf_pullbackIso B S hS).hom.hom.app
            (E.inverse.op.obj (E.functor.op.obj X)) ≫
            (SmallZariski.structureSheaf B S hS).obj.map j.op :=
      (smallZariskiStructureSheaf_pullbackIso B S hS).hom.hom.naturality j.op
    have hres :
        S.sheaf.obj.map (E.counitIso.hom.app (E.functor.obj (Opposite.unop X))).op ≫
          S.sheaf.obj.map (E.functor.map j).op = 𝟙 _ := by
      rw [← Functor.map_comp, ← op_comp, htri]
      simp
    let r := (RingCat.Hom.hom
      ((smallZariskiStructureSheaf_pullbackIso B S hS).inv.hom.app X)) x
    let t := (CommRingCat.Hom.hom
      (S.sheaf.obj.map (E.counitIso.hom.app (E.functor.obj (Opposite.unop X))).op)) r
    have hαnat_apply := congrArg (fun f => f t) hαnat
    have hres_apply := congrArg (fun f => f r) hres
    simp only [SmallZariski.structureSheaf_obj, Functor.comp_obj, Functor.op_obj,
      Functor.id_obj, Opposite.op_unop, ObjectProperty.ι_obj, Over.forget_obj, Scheme.Γ_obj,
      CommRingCat.forgetToRingCat_obj, NatTrans.id_app, RingCat.hom_id]
    change (CommRingCat.Hom.hom
        (Scheme.Hom.appTop (Over.Hom.left j.hom).hom))
        ((RingCat.Hom.hom
            ((smallZariskiStructureSheaf_pullbackIso B S hS).hom.hom.app
              (E.inverse.op.obj (E.functor.op.obj X))))
          ((CommRingCat.Hom.hom
              (S.sheaf.obj.map (E.counitIso.hom.app
                (E.functor.obj (Opposite.unop X))).op))
            ((RingCat.Hom.hom
                ((smallZariskiStructureSheaf_pullbackIso B S hS).inv.hom.app X)) x))) = x
    have hstep1 :
        (CommRingCat.Hom.hom (Scheme.Hom.appTop (Over.Hom.left j.hom).hom))
            ((RingCat.Hom.hom
                ((smallZariskiStructureSheaf_pullbackIso B S hS).hom.hom.app
                  (E.inverse.op.obj (E.functor.op.obj X)))) t) =
          (RingCat.Hom.hom
              ((smallZariskiStructureSheaf_pullbackIso B S hS).hom.hom.app X))
            ((S.ringCatSheaf.obj.map (E.functor.map j).op) t) :=
      hαnat_apply.symm
    have hstep2 : (S.ringCatSheaf.obj.map (E.functor.map j).op) t = r := by
      rw [ringCatSheaf_map_apply]
      exact hres_apply
    refine hstep1.trans ?_
    rw [hstep2]
    dsimp [r]
    have hglobal := (smallZariskiStructureSheaf_pullbackIso B S hS).inv_hom_id
    have happ := congrArg (fun f => f.hom.app X) hglobal
    exact congrArg (fun f => f x) happ
  exact (SheafOfModules.pushforwardPushforwardEquivalence
    (eqv := E) φ ψ h₁ h₂).symm
/-- The module equivalence induces the usual equivalence on underlying sheaves
of sets. -/
@[stacks 03FG "compatibility with underlying sheaves"]
public noncomputable def smallZariskiModuleEquiv_forgetIso
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (SheafOfModules.toSheaf.{m} (SmallZariski.structureSheaf B S hS) ⋙
      sheafCompose (SmallZariski.topology B S hS)
        (forget AddCommGrpCat.{m}) ⋙
      (smallZariskiSheafEquiv B S hS).functor) ≅
    ((smallZariskiModuleEquiv.{u, m} B S hS).functor ⋙
      SheafOfModules.toSheaf.{m} S.ringCatSheaf ⋙
      sheafCompose (Opens.grothendieckTopology S.carrier)
        (forget AddCommGrpCat.{m})) := by
  refine NatIso.ofComponents (fun M => ObjectProperty.isoMk _ ?_) ?_
  · refine NatIso.ofComponents (fun U => ?_) ?_
    · dsimp [smallZariskiModuleEquiv, SheafOfModules.toSheaf,
        SheafOfModules.pushforward, PresheafOfModules.pushforward,
        sheafCompose]
      exact Iso.refl _
    · intro U V f
      ext x
      rfl
  · intro M N f
    ext U x
    rfl

/-- Canonical isomorphisms on sections, linear over the canonical structure-sheaf
identification, and natural in both site morphisms and module morphisms. -/
public structure SmallZariskiModuleComparison
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (E : SheafOfModules.{m} (SmallZariski.structureSheaf B S hS) ≌
      SheafOfModules.{m} S.ringCatSheaf) where
  /-- The isomorphism between the sections of the transported module over `X` and the sections
  of `F` over the open image of `X` in `S`. -/
  sectionIso (F : SheafOfModules.{m} S.ringCatSheaf)
      (X : SmallZariski B S hS) :
    (E.inverse.obj F).val.presheaf.obj (.op X) ≅
      F.val.presheaf.obj (.op (smallZariskiOpenImmersion B S hS X).opensRange)
  /-- `sectionIso` is linear over the canonical identification of rings of sections
  `IsOpenImmersion.ΓIsoTop`. -/
  smul (F : SheafOfModules.{m} S.ringCatSheaf)
      (X : SmallZariski B S hS)
      (r : (SmallZariski.structureSheaf B S hS).obj.obj (.op X))
      (m : (E.inverse.obj F).val.presheaf.obj (.op X)) :
    letI : Module Γ(S, (smallZariskiOpenImmersion B S hS X).opensRange)
        (F.val.presheaf.obj (.op (smallZariskiOpenImmersion B S hS X).opensRange)) :=
      (F.val.obj (.op (smallZariskiOpenImmersion B S hS X).opensRange)).isModule
    (sectionIso F X).hom (r • m) =
      (IsOpenImmersion.ΓIsoTop (smallZariskiOpenImmersion B S hS X)).hom r •
        (sectionIso F X).hom m
  /-- `sectionIso` is natural in morphisms of modules. -/
  naturalInModule {F G : SheafOfModules.{m} S.ringCatSheaf} (φ : F ⟶ G)
      (X : SmallZariski B S hS)
      (m : (E.inverse.obj F).val.presheaf.obj (.op X)) :
    (sectionIso G X).hom ((E.inverse.map φ).val.app (.op X) m) =
      φ.val.app (.op (smallZariskiOpenImmersion B S hS X).opensRange)
        ((sectionIso F X).hom m)
  /-- `sectionIso` is compatible with restriction along morphisms of the small Zariski site. -/
  naturalInOpen (F : SheafOfModules.{m} S.ringCatSheaf)
      {X Y : SmallZariski B S hS}
      (g : X ⟶ Y)
      (h : (smallZariskiOpenImmersion B S hS X).opensRange ≤
        (smallZariskiOpenImmersion B S hS Y).opensRange)
      (m : (E.inverse.obj F).val.presheaf.obj (.op Y)) :
    (sectionIso F X).hom ((E.inverse.obj F).val.presheaf.map g.op m) =
      F.val.presheaf.map (homOfLE h).op ((sectionIso F Y).hom m)

/-- The equivalence is the usual open-subscheme comparison, including its
sectionwise scalar action and both naturality properties. -/
@[stacks 03FG "canonical sectionwise comparison"]
public noncomputable def smallZariskiModuleEquiv_comparison
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    SmallZariskiModuleComparison B S hS
      (smallZariskiModuleEquiv.{u, m} B S hS) := by
  refine {
    sectionIso := fun F X => Iso.refl _
    smul := ?_
    naturalInModule := ?_
    naturalInOpen := ?_ }
  · intro F X r m
    rfl
  · intro F G φ X m
    rfl
  · intro F X Y g h m
    rfl


end AlgebraicGeometry

end
