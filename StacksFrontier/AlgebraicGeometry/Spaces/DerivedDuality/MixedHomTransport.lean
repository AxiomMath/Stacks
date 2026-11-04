module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SheafHomSiteEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.RaisedDerivedInternalHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroUnitULift
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSmallModelPullbackExact
public import StacksFrontier.Homology.Injectives.KInjective.RightAdjointOfExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftFiniteColimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Topologies.GlobalPresentationComparison

/-!
# The internal Hom complex along a small model of a ringed site

Let `X` be a ringed site whose objects may lie in a larger universe than its morphisms and
structure rings, and `e : C' ≌ X.C` an equivalence with a category in the universe of the
morphisms, continuous in both directions. The restriction of the structure sheaf of `X` along `e`
makes `C'` a ringed site `AlgebraicGeometry.RingedSite.Mixed.pull X J' e` all of whose universes
agree, and restriction of modules along `e` is an equivalence `Φ` of categories of modules.

The internal Hom complex of Stacks 0A8X on `X` takes values in a raised module universe; on the
model it does not. This file identifies the restriction to the model of the internal Hom complex
`SheafHom^•(P, J)` of `X` with the universe lift of the internal Hom complex
`SheafHom^•(Φ P, Φ J)` of the model, degreewise on sections: the sections over `V` are the
cochains between the restrictions to the slice at `e(V)`, and the equivalence of slices
`C'/V ≌ X.C/e(V)` carries those to the cochains between the restrictions to the slice at `V`.

## Main definitions

* `AlgebraicGeometry.RingedSite.Mixed.pull`: the model ringed site.
* `AlgebraicGeometry.RingedSite.Mixed.sliceFunctor`: restriction of modules along the
  equivalence of slices.
* `AlgebraicGeometry.RingedSite.Mixed.cochainEquiv`: a fully faithful additive functor between
  categories with Hom types in different universes identifies the cochains, up to `ULift`.

## References

* [Stacks Project, Tag 0A8X](https://stacks.math.columbia.edu/tag/0A8X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe c u

namespace AlgebraicGeometry.RingedSite.Mixed

/-- **Cochains along a fully faithful additive functor**, between categories whose Hom types lie
in two universes: a cochain is carried to the cochain of its images, up to `ULift`. -/
def cochainEquiv {C D : Type*} [Category.{c} C] [Category.{u} D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    (P I : CochainComplex C ℤ) (n : ℤ) :
    CochainComplex.HomComplex.Cochain P I n ≃+
      ULift.{c} (CochainComplex.HomComplex.Cochain
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) n) where
  toFun z := ⟨z.map F⟩
  invFun z := CochainComplex.HomComplex.Cochain.mk (fun p q hpq => F.preimage (z.down.v p q hpq))
  left_inv z := by
    ext p q hpq
    simp
  right_inv z := by
    apply ULift.ext
    ext p q hpq
    simp
  map_add' z w := by
    apply ULift.ext
    exact CochainComplex.HomComplex.Cochain.map_add z w F

/-- `cochainEquiv` commutes with the differentials of the Hom complexes. -/
theorem cochainEquiv_δ {C D : Type*} [Category.{c} C] [Category.{u} D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    (P I : CochainComplex C ℤ) (n m : ℤ) (z : CochainComplex.HomComplex.Cochain P I n) :
    (cochainEquiv F P I m (CochainComplex.HomComplex.δ n m z)).down =
      CochainComplex.HomComplex.δ n m (cochainEquiv F P I n z).down :=
  (CochainComplex.HomComplex.δ_map n m z F).symm

variable (X : RingedSite.{c, u, u}) {C' : Type u} [SmallCategory C']
  (J' : GrothendieckTopology C') (e : C' ≌ X.C)
  [e.functor.IsContinuous J' X.J] [e.inverse.IsContinuous X.J J']

/-- **The model ringed site**: `C'` with the restriction along `e` of the structure sheaf. -/
abbrev pull : RingedSite.{u, u, u} where
  C := C'
  J := J'
  O := (e.functor.sheafPushforwardContinuous CommRingCat.{u} J' X.J).obj X.O

/-- Restriction of modules to the model: an equivalence. -/
abbrev modulesEquiv :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≌
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (pull X J' e).O) :=
  Stacks.SheafOfModules.SiteEquivalence.restrictEquivalence e J' X.J
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

/-- Restriction of modules along the equivalence of slices `C'/V ≌ X.C/e(V)`. -/
abbrev sliceEquiv (V : C') :
    SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (e.functor.obj V)) ≌
      SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (pull X J' e).O).over V) :=
  Stacks.SheafOfModules.SiteEquivalence.restrictEquivalence (Over.postEquiv V e) (J'.over V)
    (X.J.over (e.functor.obj V))
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (e.functor.obj V))

/-- Restriction of modules to the model is additive. -/
instance modulesEquiv_functor_additive : (modulesEquiv X J' e).functor.Additive where
  map_add := by intros; rfl

/-- Restriction of modules along the equivalence of slices is additive. -/
instance sliceEquiv_functor_additive (V : C') : (sliceEquiv X J' e V).functor.Additive where
  map_add := by intros; rfl

variable (P J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- Restriction of complexes of modules to the model. -/
abbrev pushC : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ ⥤
    CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (pull X J' e).O)) ℤ :=
  (modulesEquiv X J' e).functor.mapHomologicalComplex (ComplexShape.up ℤ)

/-- **The sections of the two internal Hom complexes agree**, degreewise, up to `ULift`: over
`V` the internal Hom complex of `X` has the cochains between the restrictions to the slice at
`e(V)`, the internal Hom complex of the model has the cochains between the restrictions to the
slice at `V`, and these correspond along the equivalence of slices. -/
def sectionEquiv (V : C') (n : ℤ) :
    ((sheafHomComplex X P J).obj.X n).val.obj (op (e.functor.obj V)) ≃+
      ULift.{c} (((sheafHomComplex (pull X J' e) ((pushC X J' e).obj P)
        ((pushC X J' e).obj J)).obj.X n).val.obj (op V)) :=
  ((HomologicalComplex.eval _ _ n).mapIso
      ((sheafHomComplex X P J).sectionsIso (e.functor.obj V))).addCommGroupIsoToAddEquiv.trans <|
    (cochainEquiv (sliceEquiv X J' e V).functor (restrictComplex X P (e.functor.obj V))
      (restrictComplex X J (e.functor.obj V)) n).trans <|
    AddEquiv.ulift.trans <|
      ((HomologicalComplex.eval _ _ n).mapIso
        ((sheafHomComplex (pull X J' e) ((pushC X J' e).obj P)
          ((pushC X J' e).obj J)).sectionsIso V)).symm.addCommGroupIsoToAddEquiv.trans
        AddEquiv.ulift.symm

/-- The cochain underlying the image under `sectionEquiv` of a section `s` is, in each pair of
degrees, the restriction along the equivalence of slices of the cochain underlying `s`. -/
theorem sectionEquiv_apply (V : C') (n p q : ℤ) (hpq : p + n = q)
    (s : ((sheafHomComplex X P J).obj.X n).val.obj (op (e.functor.obj V))) :
    (AddCommGrpCat.Hom.hom (((sheafHomComplex (pull X J' e) ((pushC X J' e).obj P)
        ((pushC X J' e).obj J)).sectionsIso V).hom.f n) (sectionEquiv X J' e P J V n s).down).v
        p q hpq =
      (sliceEquiv X J' e V).functor.map
        ((AddCommGrpCat.Hom.hom (((sheafHomComplex X P J).sectionsIso (e.functor.obj V)).hom.f n)
          s).v p q hpq) := by
  have h := Iso.inv_hom_id_apply
    ((HomologicalComplex.eval _ _ n).mapIso
      ((sheafHomComplex (pull X J' e) ((pushC X J' e).obj P)
        ((pushC X J' e).obj J)).sectionsIso V))
    ((AddCommGrpCat.Hom.hom
      (((sheafHomComplex X P J).sectionsIso (e.functor.obj V)).hom.f n) s).map
        (sliceEquiv X J' e V).functor)
  exact congrArg (fun z => z.v p q hpq) h

/-- The value of the image under `sectionEquiv` of a section `s` at `x` over `g : Z ⟶ V` is the
value of `s` at `x` over `e.functor.map g`. -/
theorem sectionEquiv_apply_section (V : C') (n p q : ℤ) (hpq : p + n = q)
    (s : ((sheafHomComplex X P J).obj.X n).val.obj (op (e.functor.obj V)))
    {Z : C'} (g : Z ⟶ V) (x : ((((pushC X J' e).obj P).X p).val.obj (op Z))) :
    ((AddCommGrpCat.Hom.hom (((sheafHomComplex (pull X J' e) ((pushC X J' e).obj P)
        ((pushC X J' e).obj J)).sectionsIso V).hom.f n) (sectionEquiv X J' e P J V n s).down).v
        p q hpq).val.app (op (Over.mk g)) x =
      ((AddCommGrpCat.Hom.hom (((sheafHomComplex X P J).sectionsIso (e.functor.obj V)).hom.f n)
        s).v p q hpq).val.app (op (Over.mk (e.functor.map g))) x := by
  rw [sectionEquiv_apply]
  rfl

/-- The value of the image under `sectionEquiv` of a section `s` at `x` over `g : Z ⟶ V` is the
value of `s` at `x` over any arrow `m` equal to `e.functor.map g`. -/
theorem sectionEquiv_apply_section_of_eq (V : C') (n p q : ℤ) (hpq : p + n = q)
    (s : ((sheafHomComplex X P J).obj.X n).val.obj (op (e.functor.obj V)))
    {Z : C'} (g : Z ⟶ V) (m : e.functor.obj Z ⟶ e.functor.obj V) (hm : m = e.functor.map g)
    (x : ((((pushC X J' e).obj P).X p).val.obj (op Z))) :
    ((AddCommGrpCat.Hom.hom (((sheafHomComplex (pull X J' e) ((pushC X J' e).obj P)
        ((pushC X J' e).obj J)).sectionsIso V).hom.f n) (sectionEquiv X J' e P J V n s).down).v
        p q hpq).val.app (op (Over.mk g)) x =
      ((AddCommGrpCat.Hom.hom (((sheafHomComplex X P J).sectionsIso (e.functor.obj V)).hom.f n)
        s).v p q hpq).val.app (op (Over.mk m)) x := by
  subst hm
  exact sectionEquiv_apply_section X J' e P J V n p q hpq s g x

/-- `sectionEquiv` is compatible with restriction along an arrow of the model. -/
theorem sectionEquiv_natural (n : ℤ) {Z V : C'} (g : Z ⟶ V)
    (s : ((sheafHomComplex X P J).obj.X n).val.obj (op (e.functor.obj V))) :
    (sectionEquiv X J' e P J Z n (((sheafHomComplex X P J).obj.X n).val.map
        (e.functor.map g).op s)).down =
      ((sheafHomComplex (pull X J' e) ((pushC X J' e).obj P)
        ((pushC X J' e).obj J)).obj.X n).val.map g.op (sectionEquiv X J' e P J V n s).down := by
  apply sheafHomSection_ext (sheafHomComplex (pull X J' e) ((pushC X J' e).obj P)
    ((pushC X J' e).obj J)) Z n
  intro p q hpq T x
  obtain ⟨T⟩ := T
  obtain ⟨Z', h, rfl⟩ := Over.mk_surjective T
  have hLHS := sectionEquiv_apply_section X J' e P J Z n p q hpq
    (((sheafHomComplex X P J).obj.X n).val.map (e.functor.map g).op s) h x
  have hX := (sheafHomComplex X P J).restrict_natural (e.functor.map g) n p q hpq s
    (e.functor.map h) x
  have hW := sectionEquiv_apply_section_of_eq X J' e P J V n p q hpq s (h ≫ g)
    (e.functor.map h ≫ e.functor.map g) (e.functor.map_comp h g).symm x
  have hY := (sheafHomComplex (pull X J' e) ((pushC X J' e).obj P)
    ((pushC X J' e).obj J)).restrict_natural g n p q hpq (sectionEquiv X J' e P J V n s).down h x
  exact hLHS.trans (hX.symm.trans (hW.symm.trans hY))

/-- `sectionEquiv` commutes with the differentials. -/
theorem sectionEquiv_d (V : C') (n m : ℤ)
    (s : ((sheafHomComplex X P J).obj.X n).val.obj (op (e.functor.obj V))) :
    (sectionEquiv X J' e P J V m
        (((sheafHomComplex X P J).obj.d n m).val.app (op (e.functor.obj V)) s)).down =
      ((sheafHomComplex (pull X J' e) ((pushC X J' e).obj P)
        ((pushC X J' e).obj J)).obj.d n m).val.app (op V) (sectionEquiv X J' e P J V n s).down := by
  have h₁ := ConcreteCategory.congr_hom
    (((sheafHomComplex X P J).sectionsIso (e.functor.obj V)).hom.comm n m) s
  have h₃ := ConcreteCategory.congr_hom
    (((sheafHomComplex (pull X J' e) ((pushC X J' e).obj P)
      ((pushC X J' e).obj J)).sectionsIso V).inv.comm n m)
    ((cochainEquiv (sliceEquiv X J' e V).functor (restrictComplex X P (e.functor.obj V))
      (restrictComplex X J (e.functor.obj V)) n
        (AddCommGrpCat.Hom.hom (((sheafHomComplex X P J).sectionsIso
          (e.functor.obj V)).hom.f n) s)).down)
  show AddCommGrpCat.Hom.hom (((sheafHomComplex (pull X J' e) ((pushC X J' e).obj P)
      ((pushC X J' e).obj J)).sectionsIso V).inv.f m)
      (cochainEquiv (sliceEquiv X J' e V).functor (restrictComplex X P (e.functor.obj V))
        (restrictComplex X J (e.functor.obj V)) m
          (AddCommGrpCat.Hom.hom (((sheafHomComplex X P J).sectionsIso (e.functor.obj V)).hom.f m)
            (((sheafHomComplex X P J).obj.d n m).val.app (op (e.functor.obj V)) s))).down = _
  have h₁' : AddCommGrpCat.Hom.hom (((sheafHomComplex X P J).sectionsIso (e.functor.obj V)).hom.f m)
      (((sheafHomComplex X P J).obj.d n m).val.app (op (e.functor.obj V)) s) =
      CochainComplex.HomComplex.δ n m (AddCommGrpCat.Hom.hom
        (((sheafHomComplex X P J).sectionsIso (e.functor.obj V)).hom.f n) s) := h₁.symm
  rw [h₁']
  refine (congrArg (fun w => AddCommGrpCat.Hom.hom (((sheafHomComplex (pull X J' e)
      ((pushC X J' e).obj P) ((pushC X J' e).obj J)).sectionsIso V).inv.f m) w)
    (cochainEquiv_δ (sliceEquiv X J' e V).functor (restrictComplex X P (e.functor.obj V))
      (restrictComplex X J (e.functor.obj V)) n m _)).trans h₃.symm

/-- The structure map of the model: the identity. -/
abbrev pullRingMap : Stacks.SheafOfModules.Tensor.ringSheaf (pull X J' e).O ⟶
    (e.functor.sheafPushforwardContinuous RingCat.{u} J' X.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  𝟙 _

/-- `sectionEquiv` is linear over the structure sheaf of the model. -/
def sectionLinearEquiv (V : C') (n : ℤ) :
    (((SheafOfModules.pushforward.{max c u} (pullRingMap X J' e)).obj
        ((sheafHomComplex X P J).obj.X n)).val.obj (op V)) ≃ₗ[
        (Stacks.SheafOfModules.Tensor.ringSheaf (pull X J' e).O).obj.obj (op V)]
      (((Stacks.SheafOfModules.moduleULift.{c, u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (pull X J' e).O)).obj ((sheafHomComplex (pull X J' e) ((pushC X J' e).obj P)
          ((pushC X J' e).obj J)).obj.X n)).val.obj (op V)) where
  toFun := sectionEquiv X J' e P J V n
  invFun := (sectionEquiv X J' e P J V n).symm
  left_inv := (sectionEquiv X J' e P J V n).left_inv
  right_inv := (sectionEquiv X J' e P J V n).right_inv
  map_add' := map_add _
  map_smul' r s := by
    apply ULift.ext
    apply sheafHomSection_ext (sheafHomComplex (pull X J' e) ((pushC X J' e).obj P)
      ((pushC X J' e).obj J)) V n
    intro p q hpq T x
    obtain ⟨T⟩ := T
    obtain ⟨Z, g, rfl⟩ := Over.mk_surjective T
    refine (sectionEquiv_apply_section X J' e P J V n p q hpq _ g x).trans ?_
    refine ((sheafHomComplex X P J).smul_natural (e.functor.obj V) r n p q hpq s
      (e.functor.map g) x).trans ?_
    refine Eq.trans ?_ ((sheafHomComplex (pull X J' e) ((pushC X J' e).obj P)
      ((pushC X J' e).obj J)).smul_natural V r n p q hpq (sectionEquiv X J' e P J V n s).down
        g x).symm
    rw [sectionEquiv_apply_section X J' e P J V n p q hpq s g x]
    rfl

/-- **The internal Hom complex of `X`, restricted to the model, is the universe lift of the
internal Hom complex of the model.** -/
def sheafHomComplexIso :
    ((SheafOfModules.pushforward.{max c u} (pullRingMap X J' e)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (sheafHomComplex X P J).obj ≅
      ((Stacks.SheafOfModules.moduleULift.{c, u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (pull X J' e).O)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (sheafHomComplex (pull X J' e) ((pushC X J' e).obj P) ((pushC X J' e).obj J)).obj := by
  refine HomologicalComplex.Hom.isoOfComponents (fun n =>
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun W => (sectionLinearEquiv X J' e P J W.unop n).toModuleIso)
        (by
          intro W Z f
          ext s
          apply ULift.ext
          exact sectionEquiv_natural X J' e P J n f.unop s))) ?_
  intro i j _
  ext W s
  apply ULift.ext
  exact (sectionEquiv_d X J' e P J W.unop i j s).symm

/-- Raising the universe of the sections of a sheaf of modules to an arbitrary universe preserves
finite limits: they are computed on the underlying presheaves of abelian groups, where the lift
is postcomposition with `AddCommGrpCat.uliftFunctor`. -/
theorem preservesFiniteLimits_moduleULift {C : Type*} [Category C] {K : GrothendieckTopology C}
    (R : Sheaf K RingCat.{u}) :
    PreservesFiniteLimits (Stacks.SheafOfModules.moduleULift.{c, u} R) := by
  let G := _root_.SheafOfModules.forget.{max u c} R ⋙ PresheafOfModules.toPresheaf R.obj
  have hG : PreservesFiniteLimits (Stacks.SheafOfModules.moduleULift.{c, u} R ⋙ G) := by
    show PreservesFiniteLimits
      ((_root_.SheafOfModules.forget.{u} R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙
        (Functor.whiskeringRight Cᵒᵖ AddCommGrpCat.{u} AddCommGrpCat.{max u c}).obj
          AddCommGrpCat.uliftFunctor.{c, u})
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves
    (Stacks.SheafOfModules.moduleULift.{c, u} R) G

/-- The universe lift of sheaves of modules reflects zero objects. -/
theorem isZero_of_isZero_moduleULift {C : Type*} [Category C] {K : GrothendieckTopology C}
    {R : Sheaf K RingCat.{u}} (N : SheafOfModules.{u} R)
    (h : IsZero ((Stacks.SheafOfModules.moduleULift.{c, u} R).obj N)) : IsZero N := by
  rw [IsZero.iff_id_eq_zero]
  have h₀ := h.eq_of_src ((Stacks.SheafOfModules.moduleULift.{c, u} R).map (𝟙 N))
    ((Stacks.SheafOfModules.moduleULift.{c, u} R).map 0)
  ext U x
  exact congrArg (fun f => ((f.val.app U) (ULift.up x)).down) h₀

/-- **Vanishing of a cohomology sheaf of the raised derived internal Hom of `X` gives vanishing
of the corresponding cohomology sheaf of the derived internal Hom of the model.** -/
theorem isZero_homology_derivedSheafHom_pull (P M : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (j : ℤ)
    [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [EssentiallySmall.{u} X.C]
    [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
    [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify X.J AddCommGrpCat.{max c u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{max c u}]
    [IsGrothendieckAbelian.{u} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    [HasDerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    [HasDerivedCategory (SheafOfModules.{max c u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    [HasSheafify J' AddCommGrpCat.{u}] [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify J' AddCommGrpCat.{max c u}] [J'.WEqualsLocallyBijective AddCommGrpCat.{max c u}]
    (h : IsZero ((DerivedCategory.homologyFunctor _ j).obj
      (((Raised.mixedDerivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj P))).obj
        (DerivedCategory.Q.obj M)))) :
    letI := HasDerivedCategory.standard (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (pull X J' e).O))
    IsZero ((DerivedCategory.homologyFunctor _ j).obj
      (((derivedSheafHomBifunctor (pull X J' e)).obj
        (op (DerivedCategory.Q.obj ((pushC X J' e).obj P)))).obj
        (DerivedCategory.Q.obj ((pushC X J' e).obj M)))) := by
  let := HasDerivedCategory.standard (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (pull X J' e).O))
  let := HasDerivedCategory.standard (SheafOfModules.{max c u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (pull X J' e).O))
  let I := (Stacks.Injectives.kInjectiveResolutionFunctor
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).obj M
  let ι := (Stacks.Injectives.kInjectiveResolutionInclusion
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).app M
  have hX : IsZero ((DerivedCategory.homologyFunctor _ j).obj
      (DerivedCategory.Q.obj (sheafHomComplex X P I).obj)) :=
    h.of_iso ((DerivedCategory.homologyFunctor _ j).mapIso
      (Raised.mixedDerivedSheafHomResolutionComparison X P M)).symm
  let F := SheafOfModules.pushforward.{max c u} (pullRingMap X J' e)
  have : F.IsEquivalence :=
    (Stacks.SheafOfModules.SiteEquivalence.restrictEquivalence.{max c u} e J' X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).isEquivalence_functor
  have hF : IsZero ((DerivedCategory.homologyFunctor _ j).obj
      (DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (sheafHomComplex X P I).obj))) :=
    (F.map_isZero hX).of_iso
      (((DerivedCategory.homologyFunctor _ j).mapIso
        ((F.mapDerivedCategoryFactors).app (sheafHomComplex X P I).obj).symm) ≪≫
        (F.mapDerivedCategoryHomologyIso j).app _)
  let G := Stacks.SheafOfModules.moduleULift.{c, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (pull X J' e).O)
  have : PreservesFiniteLimits G := preservesFiniteLimits_moduleULift _
  have : PreservesFiniteColimits G := Stacks.SheafOfModules.preservesFiniteColimits_moduleULift _
  let HY := (sheafHomComplex (pull X J' e) ((pushC X J' e).obj P) ((pushC X J' e).obj I)).obj
  have hG : IsZero (G.obj ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (pull X J' e).O)) j).obj
        (DerivedCategory.Q.obj HY))) :=
    (hF.of_iso ((DerivedCategory.homologyFunctor _ j).mapIso
      (DerivedCategory.Q.mapIso (sheafHomComplexIso X J' e P I)).symm)).of_iso
      (((G.mapDerivedCategoryHomologyIso j).app _).symm ≪≫
        (DerivedCategory.homologyFunctor _ j).mapIso ((G.mapDerivedCategoryFactors).app HY))
  have hY := isZero_of_isZero_moduleULift _ hG
  have : ((pushC X J' e).obj I).IsKInjective :=
    Stacks.Injectives.isKInjective_mapHomologicalComplex_of_isEquivalence _ I
  let Φ := (modulesEquiv X J' e).functor
  let eM : DerivedCategory.Q.obj ((pushC X J' e).obj M) ≅
      DerivedCategory.Q.obj ((pushC X J' e).obj I) :=
    (Φ.mapDerivedCategoryFactors.app M).symm ≪≫
      Φ.mapDerivedCategory.mapIso (asIso (DerivedCategory.Q.map ι)) ≪≫
      Φ.mapDerivedCategoryFactors.app I
  exact hY.of_iso ((DerivedCategory.homologyFunctor _ j).mapIso
    (((derivedSheafHomBifunctor (pull X J' e)).obj
        (op (DerivedCategory.Q.obj ((pushC X J' e).obj P)))).mapIso eM ≪≫
      derivedSheafHomComparison (pull X J' e) _ _))

end AlgebraicGeometry.RingedSite.Mixed
