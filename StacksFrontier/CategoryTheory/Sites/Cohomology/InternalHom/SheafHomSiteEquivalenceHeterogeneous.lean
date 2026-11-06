module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SheafHomSiteEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteEquivalenceSlicesHeterogeneous
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallHomComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallDerivedInternalHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteEquivalenceSlicesHeterogeneousSupplement

/-!
# The internal Hom complex along an equivalence of ringed sites in different universes

Let `X` be a ringed site whose objects live in a universe `c` and whose morphisms and structure
sheaf live in `u`, let `Y` be a ringed site all of whose universes are `u`, and let
`e : Y.C ≌ X.C` be an equivalence of the underlying sites, continuous in both directions, with
structure maps `φ` and `ψ` exhibiting the two pushforwards of sheaves of modules as mutually
inverse equivalences.  The case in view is the small étale ringed site of an algebraic space,
an `AlgebraicGeometry.RingedSite.{u + 1, u, u}`, against its equi-universe model.

For complexes `A`, `B` of `O_X`-modules with sections in `u`, the internal Hom complex
`SheafHom^•(A, B)` of `X` has its sections in `Type (max c u)`, those of `Y` in `Type u`.  This
file proves

`φ_* SheafHom_X^•(A, B) ≅ SheafHom_Y^•(φ_* A, φ_* B)`

twice: with the sections of the right side raised to `max c u`
(`AlgebraicGeometry.RingedSite.siteEquivSheafHomComplexIsoHet`), and, on an essentially
`u`-small `X`, with the internal Hom complex `sheafHomComplexSmall` of `X` at the module
universe on the left (`AlgebraicGeometry.RingedSite.siteEquivSheafHomComplexSmallIso`).

This is `AlgebraicGeometry.RingedSite.siteEquivSheafHomComplexIso` with the two ringed sites in
different universes; the proof is the same, the cochains on the slices being carried across by
the slice equivalences of `Stacks.SheafOfModules.InternalHom.siteEquivModulesOverHet`, whose two
categories of modules have morphisms in different universes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RingedSite

universe c u v w

/-- A fully faithful additive functor between preadditive categories whose morphisms may live in
different universes is a bijection on cochains between two cochain complexes. -/
def cochainMapAddEquiv {C : Type*} [Category.{v} C] {D : Type*} [Category.{w} D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    (P I : CochainComplex C ℤ) (n : ℤ) :
    CochainComplex.HomComplex.Cochain P I n ≃+
      CochainComplex.HomComplex.Cochain
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) n where
  toFun z := z.map F
  invFun z := CochainComplex.HomComplex.Cochain.mk (fun p q hpq => F.preimage (z.v p q hpq))
  left_inv := by intro z; ext p q hpq; simp
  right_inv := by intro z; ext p q hpq; simp
  map_add' z w := CochainComplex.HomComplex.Cochain.map_add z w F

/-- **A fully faithful additive functor preserves the Hom complex**, for categories whose
morphisms live in different universes: the Hom complex of the source is the Hom complex of the
images, with its groups raised to the larger universe. -/
def homComplexMapIsoHet {C : Type*} [Category.{max v w} C] {D : Type*} [Category.{w} D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    (P I : CochainComplex C ℤ) :
    P.HomComplex I ≅
      (AddCommGrpCat.uliftFunctor.{max v w}.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (CochainComplex.HomComplex ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => ((cochainMapAddEquiv F P I n).trans AddEquiv.ulift.symm).toAddCommGrpIso) ?_
  intro i j hij
  ext z
  exact congrArg ULift.up (CochainComplex.HomComplex.δ_map i j z F)

/-- In degree `n`, `homComplexMapIsoHet` sends a cochain `z` to its image `z.map F`, lifted to
the larger universe. -/
theorem homComplexMapIsoHet_hom_apply {C : Type*} [Category.{max v w} C] {D : Type*}
    [Category.{w} D] [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive] [F.Full]
    [F.Faithful] (P I : CochainComplex C ℤ) (n : ℤ)
    (z : CochainComplex.HomComplex.Cochain P I n) :
    AddCommGrpCat.Hom.hom ((homComplexMapIsoHet.{v, w} F P I).hom.f n) z = ULift.up (z.map F) :=
  rfl

/-- An isomorphism between the images of two cochain complexes under a fully faithful functor
is the image of a unique isomorphism; this is that isomorphism, taken degreewise. -/
def preimageIsoOfMapHomologicalComplex {C : Type*} [Category* C] {D : Type*} [Category* D]
    [Preadditive C] [Preadditive D] {F : C ⥤ D} (hF : F.FullyFaithful) [F.Additive]
    {K L : CochainComplex C ℤ}
    (e : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ≅
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) :
    K ≅ L :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => hF.preimageIso ((HomologicalComplex.eval _ _ n).mapIso e))
    (fun i j _ => hF.map_injective (by
      simp only [Functor.map_comp, Functor.FullyFaithful.preimageIso_hom,
        Functor.FullyFaithful.map_preimage]
      exact e.hom.comm i j))

attribute [local implicit_reducible]
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
  ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
  PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj
  PresheafOfModules.presheaf
  PresheafOfModules.toPresheaf
  PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
  SheafOfModules.pushforward
  SheafOfModules.overFunctor
  SheafOfModules.toSheaf
  SheafOfModules.forget

variable {X : RingedSite.{c, u, u}} {Y : RingedSite.{u, u, u}} (eqv : Y.C ≌ X.C)
  [eqv.functor.IsContinuous Y.J X.J] [eqv.inverse.IsContinuous X.J Y.J]
  (φ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
    (eqv.functor.sheafPushforwardContinuous RingCat.{u} Y.J X.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  (ψ : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
    (eqv.inverse.sheafPushforwardContinuous RingCat.{u} X.J Y.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (H₁ : Functor.whiskerRight (NatTrans.op eqv.counit)
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj =
    ψ.hom ≫ eqv.inverse.op.whiskerLeft φ.hom)
  (H₂ : φ.hom ≫ eqv.functor.op.whiskerLeft ψ.hom ≫
    Functor.whiskerRight (NatTrans.op eqv.unit) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj =
      𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)

/-- Transport of sheaves of modules on the slice over `W`, along the equivalence of slices. -/
abbrev sliceFunctorHet (W : Y.C) :
    SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (eqv.functor.obj W)) ⥤
      SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W) :=
  (Stacks.SheafOfModules.InternalHom.siteEquivModulesOverHet.{c, u, u, u, u, u}
    eqv φ ψ H₁ H₂ W).functor

/-- The transport `sliceFunctorHet` of sheaves of modules along the slice equivalence is
additive. -/
instance sliceFunctorHet_additive (W : Y.C) : (sliceFunctorHet eqv φ ψ H₁ H₂ W).Additive where
  map_add := by intros; rfl

/-- The transport `sliceFunctorHet` of sheaves of modules along the slice equivalence is an
equivalence. -/
instance sliceFunctorHet_isEquivalence (W : Y.C) :
    (sliceFunctorHet eqv φ ψ H₁ H₂ W).IsEquivalence :=
  (Stacks.SheafOfModules.InternalHom.siteEquivModulesOverHet.{c, u, u, u, u, u}
    eqv φ ψ H₁ H₂ W).isEquivalence_functor

section

variable (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- The complex of sections over `e(W)` of the internal Hom complex of `X` is the complex of
sections over `W` of the internal Hom complex of the transports, raised to the universe of the
former: both are the cochains on the slices, and the equivalence of slices carries the one to
the other. -/
def siteEquivSectionIsoHet (W : Y.C) :
    sectionComplex X (sheafHomComplex X A B).obj (eqv.functor.obj W) ≅
      (AddCommGrpCat.uliftFunctor.{max c u}.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (sectionComplex Y (sheafHomComplex Y (((SheafOfModules.pushforward.{u}
          φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj A)
          (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            B)).obj W) :=
  (sheafHomComplex X A B).sectionsIso (eqv.functor.obj W) ≪≫
    homComplexMapIsoHet.{c, u} (sliceFunctorHet eqv φ ψ H₁ H₂ W) _ _ ≪≫
    (AddCommGrpCat.uliftFunctor.{max c u}.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      ((sheafHomComplex Y (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj A)
        (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          B)).sectionsIso W).symm

/-- On cochains, `siteEquivSectionIsoHet` transports each local homogeneous component along the
equivalence of slices. -/
theorem siteEquivSectionIsoHet_apply (W : Y.C) (n p q : ℤ) (hpq : p + n = q)
    (s : ((sheafHomComplex X A B).obj.X n).val.obj (op (eqv.functor.obj W))) :
    (AddCommGrpCat.Hom.hom
      (((sheafHomComplex Y (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj A)
        (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          B)).sectionsIso W).hom.f n)
      (AddCommGrpCat.Hom.hom
        ((siteEquivSectionIsoHet eqv φ ψ H₁ H₂ A B W).hom.f n) s).down).v p q hpq =
    (sliceFunctorHet eqv φ ψ H₁ H₂ W).map
      ((AddCommGrpCat.Hom.hom
        (((sheafHomComplex X A B).sectionsIso (eqv.functor.obj W)).hom.f n) s).v p q hpq) := by
  have h := Iso.inv_hom_id_apply
    ((HomologicalComplex.eval _ _ n).mapIso
      ((sheafHomComplex Y (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj A)
        (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          B)).sectionsIso W))
    ((AddCommGrpCat.Hom.hom
      (((sheafHomComplex X A B).sectionsIso (eqv.functor.obj W)).hom.f n) s).map
        (sliceFunctorHet eqv φ ψ H₁ H₂ W))
  exact congrArg (fun z => z.v p q hpq) h

/-- `siteEquivSectionIsoHet` evaluated on a section over a slice object: the local homogeneous
component is the one of the original cochain, read at the image slice object. -/
theorem siteEquivSectionIsoHet_apply_section (W : Y.C) (n p q : ℤ) (hpq : p + n = q)
    (s : ((sheafHomComplex X A B).obj.X n).val.obj (op (eqv.functor.obj W)))
    {Z : Y.C} (g : Z ⟶ W)
    (x : (((((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj A).X
      p).val.obj (op Z))) :
    ((AddCommGrpCat.Hom.hom
      (((sheafHomComplex Y (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj A)
        (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          B)).sectionsIso W).hom.f n)
      (AddCommGrpCat.Hom.hom
        ((siteEquivSectionIsoHet eqv φ ψ H₁ H₂ A B W).hom.f n) s).down).v p q hpq).val.app
          (op (Over.mk g)) x =
    ((AddCommGrpCat.Hom.hom
      (((sheafHomComplex X A B).sectionsIso (eqv.functor.obj W)).hom.f n) s).v
        p q hpq).val.app (op (Over.mk (eqv.functor.map g))) x := by
  rw [siteEquivSectionIsoHet_apply]
  rfl

/-- `siteEquivSectionIsoHet_apply_section` with the slice object of `X` presented by any
morphism equal to the image of `g`. -/
theorem siteEquivSectionIsoHet_apply_section_of_eq (W : Y.C) (n p q : ℤ) (hpq : p + n = q)
    (s : ((sheafHomComplex X A B).obj.X n).val.obj (op (eqv.functor.obj W)))
    {Z : Y.C} (g : Z ⟶ W) (m : eqv.functor.obj Z ⟶ eqv.functor.obj W)
    (hm : m = eqv.functor.map g)
    (x : (((((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj A).X
      p).val.obj (op Z))) :
    ((AddCommGrpCat.Hom.hom
      (((sheafHomComplex Y (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj A)
        (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          B)).sectionsIso W).hom.f n)
      (AddCommGrpCat.Hom.hom
        ((siteEquivSectionIsoHet eqv φ ψ H₁ H₂ A B W).hom.f n) s).down).v p q hpq).val.app
          (op (Over.mk g)) x =
    ((AddCommGrpCat.Hom.hom
      (((sheafHomComplex X A B).sectionsIso (eqv.functor.obj W)).hom.f n) s).v
        p q hpq).val.app (op (Over.mk m)) x := by
  subst hm
  exact siteEquivSectionIsoHet_apply_section eqv φ ψ H₁ H₂ A B W n p q hpq s g x

attribute [local instance] Stacks.SheafOfModules.moduleULiftModule in
/-- `siteEquivSectionIsoHet` is linear for the action of the structure sheaf of `Y`, the source
being a module over it through `φ` and the target through the universe lift. -/
def siteEquivSectionLinearEquivHet (W : Y.C) (n : ℤ) :
    ((((SheafOfModules.pushforward.{max c u} φ).obj
        ((sheafHomComplex X A B).obj.X n)).val.obj (op W)))
        ≃ₗ[(Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (op W)]
      (((Stacks.SheafOfModules.moduleULift.{max c u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
          ((sheafHomComplex Y (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj A)
            (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              B)).obj.X n)).val.obj (op W)) where
  toFun := AddCommGrpCat.Hom.hom ((siteEquivSectionIsoHet eqv φ ψ H₁ H₂ A B W).hom.f n)
  invFun := AddCommGrpCat.Hom.hom ((siteEquivSectionIsoHet eqv φ ψ H₁ H₂ A B W).inv.f n)
  left_inv := Iso.hom_inv_id_apply ((HomologicalComplex.eval _ _ n).mapIso
    (siteEquivSectionIsoHet eqv φ ψ H₁ H₂ A B W))
  right_inv := Iso.inv_hom_id_apply ((HomologicalComplex.eval _ _ n).mapIso
    (siteEquivSectionIsoHet eqv φ ψ H₁ H₂ A B W))
  map_add' := map_add _
  map_smul' r s := by
    apply ULift.ext
    apply sheafHomSection_ext (sheafHomComplex Y (((SheafOfModules.pushforward.{u}
      φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj A)
      (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj B)) W n
    intro p q hpq T x
    obtain ⟨T⟩ := T
    obtain ⟨Z, g, rfl⟩ := Over.mk_surjective T
    change (((AddCommGrpCat.Hom.hom
      (((sheafHomComplex Y (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj A)
        (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          B)).sectionsIso W).hom.f n)
      (AddCommGrpCat.Hom.hom
        ((siteEquivSectionIsoHet eqv φ ψ H₁ H₂ A B W).hom.f n) (r • s)).down).v p q hpq).val.app
          (op (Over.mk g)) x) =
      (((AddCommGrpCat.Hom.hom
      (((sheafHomComplex Y (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj A)
        (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          B)).sectionsIso W).hom.f n)
      (r • (show ((sheafHomComplex Y (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj A)
        (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          B)).obj.X n).val.obj (op W) from (AddCommGrpCat.Hom.hom
        ((siteEquivSectionIsoHet eqv φ ψ H₁ H₂ A B W).hom.f n) s).down))).v p q hpq).val.app
          (op (Over.mk g)) x)
    rw [siteEquivSectionIsoHet_apply_section eqv φ ψ H₁ H₂ A B W n p q hpq (r • s) g x]
    rw [(sheafHomComplex Y (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj A)
      (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        B)).smul_natural W r n p q hpq _ g x]
    rw [siteEquivSectionIsoHet_apply_section eqv φ ψ H₁ H₂ A B W n p q hpq s g x]
    refine Eq.trans ((sheafHomComplex X A B).smul_natural (eqv.functor.obj W)
      (φ.hom.app (op W) r) n p q hpq s (eqv.functor.map g) x) ?_
    have hφ : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map (eqv.functor.map g).op
        (φ.hom.app (op W) r) =
          φ.hom.app (op Z) ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.map g.op r) :=
      (congrArg (fun m => (RingCat.Hom.hom m) r) (φ.hom.naturality g.op)).symm
    rw [hφ]
    rfl

attribute [local instance] Stacks.SheafOfModules.moduleULiftModule in
/-- `siteEquivSectionLinearEquivHet` is compatible with restriction along an arrow of `Y`. -/
theorem siteEquivSectionLinearEquivHet_natural (n : ℤ) {Z W : Y.C} (g : Z ⟶ W)
    (s : ((((SheafOfModules.pushforward.{max c u} φ).obj
        ((sheafHomComplex X A B).obj.X n)).val.obj (op W)))) :
    siteEquivSectionLinearEquivHet eqv φ ψ H₁ H₂ A B Z n
        (((SheafOfModules.pushforward.{max c u} φ).obj
          ((sheafHomComplex X A B).obj.X n)).val.map g.op s) =
      (((Stacks.SheafOfModules.moduleULift.{max c u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
          ((sheafHomComplex Y (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj A)
            (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              B)).obj.X n)).val.map g.op)
        (siteEquivSectionLinearEquivHet eqv φ ψ H₁ H₂ A B W n s) := by
  apply ULift.ext
  apply sheafHomSection_ext (sheafHomComplex Y (((SheafOfModules.pushforward.{u}
    φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj A)
    (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj B)) Z n
  intro p q hpq T x
  obtain ⟨T⟩ := T
  obtain ⟨Z', h, rfl⟩ := Over.mk_surjective T
  have hLHS := siteEquivSectionIsoHet_apply_section eqv φ ψ H₁ H₂ A B Z n p q hpq
    (((SheafOfModules.pushforward.{max c u} φ).obj
      ((sheafHomComplex X A B).obj.X n)).val.map g.op s) h x
  have hX := (sheafHomComplex X A B).restrict_natural (eqv.functor.map g) n p q hpq s
    (eqv.functor.map h) x
  have hW := siteEquivSectionIsoHet_apply_section_of_eq eqv φ ψ H₁ H₂ A B W n p q hpq s (h ≫ g)
    (eqv.functor.map h ≫ eqv.functor.map g) (eqv.functor.map_comp h g).symm x
  have hY := (sheafHomComplex Y (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj A)
    (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      B)).restrict_natural g n p q hpq
      (AddCommGrpCat.Hom.hom
        ((siteEquivSectionIsoHet eqv φ ψ H₁ H₂ A B W).hom.f n) s).down h x
  exact hLHS.trans (hX.symm.trans (hW.symm.trans hY))

attribute [local instance] Stacks.SheafOfModules.moduleULiftModule in
/-- The degree-`n` part of `siteEquivSheafHomComplexIsoHet`, on underlying presheaves of
modules. -/
def siteEquivSheafHomTermPresheafIsoHet (n : ℤ) :
    ((SheafOfModules.pushforward.{max c u} φ).obj ((sheafHomComplex X A B).obj.X n)).val ≅
      ((Stacks.SheafOfModules.moduleULift.{max c u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
          ((sheafHomComplex Y (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj A)
            (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              B)).obj.X n)).val :=
  PresheafOfModules.isoMk
    (fun W => (siteEquivSectionLinearEquivHet eqv φ ψ H₁ H₂ A B W.unop n).toModuleIso)
    (by
      intro W Z f
      ext s
      exact siteEquivSectionLinearEquivHet_natural eqv φ ψ H₁ H₂ A B n f.unop s)

/-- The degree-`n` part of `siteEquivSheafHomComplexIsoHet`. -/
def siteEquivSheafHomTermIsoHet (n : ℤ) :
    (SheafOfModules.pushforward.{max c u} φ).obj ((sheafHomComplex X A B).obj.X n) ≅
      (Stacks.SheafOfModules.moduleULift.{max c u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
          ((sheafHomComplex Y (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj A)
            (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              B)).obj.X n) :=
  (SheafOfModules.fullyFaithfulForget (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).preimageIso
    (siteEquivSheafHomTermPresheafIsoHet eqv φ ψ H₁ H₂ A B n)

/-- `siteEquivSheafHomTermIsoHet` acts on sections by `siteEquivSectionIsoHet`. -/
theorem siteEquivSheafHomTermIsoHet_hom_val_app_apply (n : ℤ) (W : Y.Cᵒᵖ)
    (s : ((SheafOfModules.pushforward.{max c u} φ).obj
      ((sheafHomComplex X A B).obj.X n)).val.obj W) :
    (siteEquivSheafHomTermIsoHet eqv φ ψ H₁ H₂ A B n).hom.val.app W s =
      AddCommGrpCat.Hom.hom ((siteEquivSectionIsoHet eqv φ ψ H₁ H₂ A B W.unop).hom.f n) s :=
  rfl

/-- The degreewise isomorphisms `siteEquivSheafHomTermIsoHet` commute with the differentials. -/
theorem siteEquivSheafHomTermIsoHet_comm (i j : ℤ) :
    (siteEquivSheafHomTermIsoHet eqv φ ψ H₁ H₂ A B i).hom ≫
        (Stacks.SheafOfModules.moduleULift.{max c u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
          ((sheafHomComplex Y (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj A)
            (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              B)).obj.d i j) =
      (SheafOfModules.pushforward.{max c u} φ).map ((sheafHomComplex X A B).obj.d i j) ≫
        (siteEquivSheafHomTermIsoHet eqv φ ψ H₁ H₂ A B j).hom := by
  apply SheafOfModules.hom_ext
  ext W s
  have h := ConcreteCategory.congr_hom
    ((siteEquivSectionIsoHet eqv φ ψ H₁ H₂ A B W.unop).hom.comm i j) s
  rw [SheafOfModules.comp_val, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    PresheafOfModules.comp_app, ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
    LinearMap.comp_apply, siteEquivSheafHomTermIsoHet_hom_val_app_apply,
    siteEquivSheafHomTermIsoHet_hom_val_app_apply]
  exact h

/-- **The internal Hom complex is invariant under an equivalence of ringed sites in different
universes.** The transport along the equivalence of the internal Hom complex `SheafHom_X(A, B)`
is the internal Hom complex of the transports, its sections raised to the universe `max c u` of
the sections of the former. -/
def siteEquivSheafHomComplexIsoHet :
    ((SheafOfModules.pushforward.{max c u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (sheafHomComplex X A B).obj ≅
      ((Stacks.SheafOfModules.moduleULift.{max c u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (sheafHomComplex Y (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj A) (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj B)).obj :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => siteEquivSheafHomTermIsoHet eqv φ ψ H₁ H₂ A B n)
    (fun i j _ => siteEquivSheafHomTermIsoHet_comm eqv φ ψ H₁ H₂ A B i j)

end

section Small

variable [EssentiallySmall.{u} X.C]
  (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- Transporting a complex along the equivalence commutes with raising the universe of its
sections, on the nose. -/
def moduleULiftPushComplexIso
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((Stacks.SheafOfModules.moduleULift.{max c u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≅
      ((SheafOfModules.pushforward.{max c u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((Stacks.SheafOfModules.moduleULift.{max c u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (fun _ _ _ => rfl)

/-- **The internal Hom complex at the module universe is invariant under an equivalence of
ringed sites in different universes.** On an essentially `u`-small `X`, the transport of the
internal Hom complex `SheafHom_X(A, B)` with sections in `Type u`
(`AlgebraicGeometry.RingedSite.sheafHomComplexSmall`) is the internal Hom complex of the
transports on `Y`. Both sides become `siteEquivSheafHomComplexIsoHet` once their sections are
raised to `max c u`, and raising the universe is fully faithful. -/
def siteEquivSheafHomComplexSmallIso :
    ((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (sheafHomComplexSmall X A B) ≅
      (sheafHomComplex Y (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj A) (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj B)).obj :=
  preimageIsoOfMapHomologicalComplex
    (Stacks.SheafOfModules.moduleULiftFullyFaithful.{max c u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (moduleULiftPushComplexIso eqv φ (sheafHomComplexSmall X A B) ≪≫
      ((SheafOfModules.pushforward.{max c u} φ).mapHomologicalComplex
        (ComplexShape.up ℤ)).mapIso (sheafHomComplexSmallIso X A B) ≪≫
      siteEquivSheafHomComplexIsoHet eqv φ ψ H₁ H₂ A B)

end Small

section Derived

universe d d'

variable [EssentiallySmall.{u} X.C]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{max c u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max c u}]
  [hDX : HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [hDY : HasDerivedCategory.{d'} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]

/-- The pushforward of sheaves of modules along `φ` is additive. -/
instance pushforwardHet_additive : (SheafOfModules.pushforward.{u} φ).Additive where
  map_add := by intros; rfl

variable [PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ)]
  [PreservesFiniteColimits (SheafOfModules.pushforward.{u} φ)]

/-- **The derived internal Hom at the module universe is invariant under an equivalence of
ringed sites in different universes.** On an essentially `u`-small `X`, the transport of
`RSheafHom_X(K, L)` (`AlgebraicGeometry.RingedSite.derivedSheafHomSmallBifunctor`) is the derived
internal Hom of the transports on `Y`.

A representative `N` of `K` and the chosen K-injective resolution `I` of a representative of `L`
are chosen; both sides are then the class of an internal Hom complex, and the comparison is the
class of `siteEquivSheafHomComplexSmallIso`. The transport of `I` stays K-injective because the
inverse of the equivalence is exact (Stacks 08BJ). -/
def siteEquivDerivedSheafHomSmallIso
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj
        (((derivedSheafHomSmallBifunctor X).obj (op K)).obj L) ≅
      ((derivedSheafHomBifunctor Y).obj
        (op ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj K))).obj
          ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj L) := by
  letI : PreservesFiniteLimits (SheafOfModules.pushforward.{u} ψ) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.pushforwardPushforwardEquivalence eqv φ
      ψ H₁ H₂).inverse)
  letI : PreservesFiniteColimits (SheafOfModules.pushforward.{u} ψ) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.pushforwardPushforwardEquivalence eqv
      φ ψ H₁ H₂).inverse)
  letI : (SheafOfModules.pushforward.{u} ψ).Additive := ⟨by intros; rfl⟩
  let N := DerivedCategory.Q.objPreimage K
  let eN : DerivedCategory.Q.obj N ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let M₀ := DerivedCategory.Q.objPreimage L
  let I := (kInjectiveResolutionSmall X).obj M₀
  letI : I.IsKInjective :=
    Stacks.Injectives.kInjectiveResolutionFunctor_obj_isKInjective
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) M₀
  let eI : DerivedCategory.Q.obj I ≅ L :=
    (asIso (DerivedCategory.Q.map ((kInjectiveAugmentationSmall X).app M₀))).symm ≪≫
      DerivedCategory.Q.objObjPreimageIso L
  letI : CochainComplex.IsKInjective
      (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    CochainComplex.isKInjective_mapHomologicalComplex_of_exact
      (SheafOfModules.pushforward.{u} φ) (SheafOfModules.pushforward.{u} ψ)
      (SheafOfModules.pushforwardPushforwardEquivalence eqv φ ψ H₁ H₂).symm.toAdjunction I
  let epN : DerivedCategory.Q.obj (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj N) ≅
      (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj K :=
    ((SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors.app N).symm ≪≫
      (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.mapIso eN
  let epI : DerivedCategory.Q.obj (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj I) ≅
      (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj L :=
    ((SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors.app I).symm ≪≫
      (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.mapIso eI
  exact (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.mapIso
      (((derivedSheafHomSmallBifunctor X).mapIso eN.op).app L ≪≫
        ((derivedSheafHomSmallBifunctor X).obj (op (DerivedCategory.Q.obj N))).mapIso eI.symm ≪≫
        derivedSheafHomSmallComparison X N I) ≪≫
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors.app
      (sheafHomComplexSmall X N I) ≪≫
    DerivedCategory.Q.mapIso (siteEquivSheafHomComplexSmallIso eqv φ ψ H₁ H₂ N I) ≪≫
    (derivedSheafHomComparison Y (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N)
      (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).symm
        ≪≫
    (((derivedSheafHomBifunctor Y).mapIso epN.op).app _ ≪≫
      ((derivedSheafHomBifunctor Y).obj
        (op (DerivedCategory.Q.obj (((SheafOfModules.pushforward.{u} φ).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N)))).mapIso epI.symm).symm

end Derived

end AlgebraicGeometry.RingedSite

end
