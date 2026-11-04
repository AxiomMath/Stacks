module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartComparisonComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardCompIsoSheafTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeModulePushforwardComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsChartPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardComparison

/-!
# The direct image of modules along base change of charts is compatible with composition

For representable morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of algebraic spaces,
`AlgebraicGeometry.Space.modulePushforwardChartIso` identifies the direct image of modules of
Stacks 03LU with the direct image taken along base change of étale scheme charts.  This file
proves that those identifications are compatible with composition: they carry the composition
comparison `AlgebraicGeometry.Space.modulePushforwardCompIso` of Stacks 03LU to the composition
comparison `AlgebraicGeometry.Space.smallBaseChangeModulePushforwardCompIsoOfRepresentable` of the
chart-base-change direct images.

## Main results

* `AlgebraicGeometry.Space.modulePushforwardChartIso_hom_comp`: the composition law.

## Implementation notes

Everything is checked on underlying sheaves of sets, where a morphism of sheaves of modules is
determined; the content is then the sheaf-of-sets law
`AlgebraicGeometry.Space.chartComparison_comp`.

Why the file is shaped the way it is.  The statement of the composition law,
and the statement of each comparison below, elaborate well inside the heartbeat budget — checked
by making each the hypothesis of a `True`-valued theorem — while every *proof* that decomposes a
composite **at the level of sheaves** exceeds it: such a decomposition asks for the
identification of several spellings of one underlying sheaf, and each of those costs a sizeable
fraction of the budget on its own.  Read on **sections** the same identifications are between
section types, which is one unfolding each.  So every comparison here is first read on sections,
and the composition law itself is reduced to sections by
`CategoryTheory.natTrans_three_eq_two_of_val_app`; the only passage between the two levels is
`CategoryTheory.Sheaf.moduleSheafFunctor_map_hom_app_apply`, at plain variables.

The composition comparison of Stacks 03LU, read on sections, is
`AlgebraicGeometry.Space.modulePushforwardCompIso_hom_app_val_app` of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardCompIsoSheafTransfer.lean`, and it is
what the composition law below consumes.  Its four factors are read on sections here, as is the
assembly helper `CategoryTheory.eqToIso_four_hom_app_val_app_apply`, which takes the
factorisation as a *hypothesis* so that the decomposition is performed by `subst` at plain
variables before any geometric term is in sight.  One further point is forced:
the passage from the source spelling of the composite to the one the inner factors are stated at
must be a `cast` — that is, an `Eq.rec` along
`AlgebraicGeometry.Space.modulePushforward_comp_eq` — and not a definitional identification,
because as a definitional identification it is a **kernel** deterministic timeout, which no
`attribute [local irreducible]` can reach.

`attribute [local irreducible]` on `AlgebraicGeometry.Space.smallBaseChange` and the structure
presheaf is needed here: without it the elaborator normalises objects of the
small étale site, `AlgebraicGeometry.Space.smallBaseChange` being unfolded some 27,000 times
into the `Classical.choose` of the chosen fibre product.  It is a per-file judgement, as the
notes of `StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeSquareCommutes.lean`
record; here it is necessary.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.RingedToposModules (hom_ext_moduleSheafFunctor)

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace CategoryTheory.Sheaf

universe w vv uu

variable {C : Type uu} [Category.{vv} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  {R : Sheaf J RingCat.{w}}

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- **A morphism of sheaves of modules and a morphism of the underlying sheaves of sets agree as
soon as they agree on sections.**  This is `CategoryTheory.Sheaf.hom_ext_sections` with the
passage from `CategoryTheory.Sheaf.sectionsFunctor` to the `val` of a morphism of sheaves of
modules done at plain variables. -/
theorem moduleSheafFunctor_map_eq_of_val_app {M N : SheafOfModules.{w} R} (m : M ⟶ N)
    (s : Sheaf.moduleSheaf R M ⟶ Sheaf.moduleSheaf R N)
    (h : ∀ (W : Cᵒᵖ) (z : M.val.obj W), (m.val.app W).hom z = s.hom.app W z) :
    (Sheaf.moduleSheafFunctor R).map m = s :=
  hom_ext_sections fun W z ↦ h W z

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The underlying morphism of sheaves of sets of a morphism of sheaves of modules, read on
sections.  Stated at plain variables; it is the only passage between the two levels used below,
and it is the passage whose instantiation at a geometric composite is unaffordable when the two
levels are mixed inside one statement. -/
theorem moduleSheafFunctor_map_hom_app_apply {M N : SheafOfModules.{w} R} (m : M ⟶ N)
    (W : Cᵒᵖ) (z : M.val.obj W) :
    ((Sheaf.moduleSheafFunctor R).map m).hom.app W z = (m.val.app W).hom z :=
  rfl

end CategoryTheory.Sheaf

namespace CategoryTheory

universe wm vm um va ua

variable {A : Type ua} [Category.{va} A] {C : Type um} [Category.{vm} C]
  {J : GrothendieckTopology C} {R : Sheaf J RingCat.{wm}}

/-- **A fourfold composite of isomorphisms of functors into sheaves of modules whose outer two
factors are transports along equalities of functors, read on sections.**  Both `eqToIso`s are
substituted away, which is the only way to reduce such a transport on sections; the two inner
factors are plain variables, and the factorisation of the composite is a hypothesis so that no
`CategoryTheory.eqToHom` ever enters a unification problem.  This is the fourfold analogue of
`CategoryTheory.eqToIso_trans_hom_app_val_app_apply`. -/
theorem eqToIso_four_hom_app_val_app_apply {F G H K L : A ⥤ SheafOfModules.{wm} R} (e : F ≅ L)
    (E₁ : F = G) (b : G ≅ H) (c : H ≅ K) (E₂ : K = L)
    (he : e = eqToIso E₁ ≪≫ b ≪≫ c ≪≫ eqToIso E₂) (M : A) (W : Cᵒᵖ)
    (z : (F.obj M).val.obj W) (y : (L.obj M).val.obj W)
    (hy : HEq (((c.hom.app M).val.app W).hom (((b.hom.app M).val.app W).hom
      (cast (congrArg
        (fun T : A ⥤ SheafOfModules.{wm} R ↦ ToType ((T.obj M).val.obj W)) E₁) z))) y) :
    ((e.hom.app M).val.app W).hom z = y := by
  subst he
  subst E₁
  subst E₂
  rw [eqToIso_refl, eqToIso_refl, Iso.refl_trans, Iso.trans_refl]
  exact eq_of_heq hy

/-- **A threefold composite of natural transformations of functors into sheaves of modules is a
twofold one as soon as it is, on sections.**  Stated at plain variables; it is the only place
where the two composites are decomposed, and at the instantiation below it is matched
first-order against the goal. -/
theorem natTrans_three_eq_two_of_val_app {Φ Ψ₁ Ψ₂ Ψ₃ Ω : A ⥤ SheafOfModules.{wm} R}
    (α : Φ ⟶ Ψ₁) (β : Ψ₁ ⟶ Ψ₂) (γ : Ψ₂ ⟶ Ψ₃) (δ : Φ ⟶ Ω) (ε : Ω ⟶ Ψ₃)
    (h : ∀ (M : A) (W : Cᵒᵖ) (z : (Φ.obj M).val.obj W),
      ((γ.app M).val.app W).hom (((β.app M).val.app W).hom (((α.app M).val.app W).hom z)) =
        ((ε.app M).val.app W).hom (((δ.app M).val.app W).hom z)) :
    α ≫ β ≫ γ = δ ≫ ε :=
  NatTrans.ext (funext fun M ↦ SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W ↦
    ModuleCat.hom_ext (LinearMap.ext fun z ↦ h M W z)))

/-- If `moduleSheafFunctor.map m` equals `s`, then `m` acts on sections as `s` does. -/
private theorem val_app_hom_apply_of_moduleSheafFunctor_map_eq
    [J.HasSheafCompose (forget AddCommGrpCat.{wm})] {M N : SheafOfModules.{wm} R}
    {m : M ⟶ N} {s : Sheaf.moduleSheaf R M ⟶ Sheaf.moduleSheaf R N}
    (h : (Sheaf.moduleSheafFunctor R).map m = s) (W : Cᵒᵖ) (z : M.val.obj W) :
    (m.val.app W).hom z = s.hom.app W z :=
  (Sheaf.moduleSheafFunctor_map_hom_app_apply m W z).symm.trans (Sheaf.hom_congr_app_apply h W z)

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Z : AlgebraicSpaces B S hS}

attribute [local irreducible] AlgebraicGeometry.Space.smallBaseChange
  AlgebraicGeometry.Space.structureSheaf AlgebraicGeometry.Space.structureSheaf'
  AlgebraicGeometry.Space.structurePresheaf

/-- `AlgebraicGeometry.Space.modulePushforwardCompIso` written out as the fourfold composite it
is defined to be.  Recorded as its own `rfl` so that the decomposition below is supplied to the
generic engine as a hypothesis rather than discovered by the unifier. -/
theorem modulePushforwardCompIso_eq_trans (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePushforwardCompIso B S hS f g =
      eqToIso (modulePushforward_comp_eq B S hS f g) ≪≫
        (RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS f)
          (smallEtaleRingedToposHom B S hS g)).symm ≪≫
        pushforwardModulesCompTransport B S hS f g ≪≫
        eqToIso (pushforwardModules_eq_modulePushforward B S hS (f ≫ g)) :=
  rfl

/-! ### The four comparisons, each read on sections -/

/-- **The identification of the direct image of modules with chart base change is the chart
comparison of sheaves of sets.**  This is
`AlgebraicGeometry.Space.modulePushforwardChartIso_hom_app_apply` read as an identity of
morphisms of sheaves of sets, with the right-hand side at the `CategoryTheory.Iso.trans`
spelling that the sections formula uses. -/
theorem moduleSheafFunctor_map_modulePushforwardChartIso_hom_app_ran (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (M : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
        ((modulePushforwardChartIso B S hS f hf).hom.app M) =
      (smallEtaleDirectImageRanIso B S hS f ≪≫ chartRanIso B S hS f hf).hom.app
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) M) :=
  CategoryTheory.Sheaf.moduleSheafFunctor_map_eq_of_val_app
    (R := structureRingSheaf B S hS Y)
    ((modulePushforwardChartIso B S hS f hf).hom.app M)
    ((smallEtaleDirectImageRanIso B S hS f ≪≫ chartRanIso B S hS f hf).hom.app
      (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) M))
    (fun W z ↦ modulePushforwardChartIso_hom_app_apply B S hS f hf M W.unop z)

/-- `AlgebraicGeometry.Space.modulePushforwardChartIso_hom_app_apply` with the right-hand side
named as `AlgebraicGeometry.Space.chartComparison`. -/
theorem modulePushforwardChartIso_hom_app_chartComparison (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (M : Modules.{u, u} B S hS X.1 X.2)
    (W : (SmallEtale B S hS Y.1)ᵒᵖ)
    (z : ((modulePushforward B S hS f).obj M).val.obj W) :
    (((modulePushforwardChartIso B S hS f hf).hom.app M).val.app W).hom z =
      ((chartComparison B S hS f hf).hom.app
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) M)).hom.app W z :=
  (modulePushforwardChartIso_hom_app_apply B S hS f hf M W.unop z).trans
    (CategoryTheory.Sheaf.hom_congr_app_apply
      (chartComparison_hom_app B S hS f hf
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) M)).symm W z)

/-- The comparison of the direct images of modules for the honest composite of the two morphisms
of ringed topoi is the identity on sections.  This is
`AlgebraicGeometry.Space.moduleSheafFunctor_map_pushforwardModulesCompIso_inv_app` read on
sections. -/
theorem pushforwardModulesCompIso_inv_app_val_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Modules.{u, u} B S hS X.1 X.2) (W : (SmallEtale B S hS Z.1)ᵒᵖ)
    (z : (((smallEtaleRingedToposHom B S hS f).pushforwardModules ⋙
      (smallEtaleRingedToposHom B S hS g).pushforwardModules).obj M).val.obj W) :
    (((RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS f)
        (smallEtaleRingedToposHom B S hS g)).inv.app M).val.app W).hom z = z :=
  val_app_hom_apply_of_moduleSheafFunctor_map_eq
    (moduleSheafFunctor_map_pushforwardModulesCompIso_inv_app B S hS f g M) W z

/-- The transport of `AlgebraicGeometry.Space.pushforwardModulesCompTransport` is the geometric
comparison `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` of Stacks 03G2, part (3), read
on sections.  This is the one factor of the composition comparison with content. -/
theorem pushforwardModulesCompTransport_hom_app_val_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Modules.{u, u} B S hS X.1 X.2) (W : (SmallEtale B S hS Z.1)ᵒᵖ)
    (y : ((((smallEtaleRingedToposHom B S hS g).comp
      (smallEtaleRingedToposHom B S hS f)).pushforwardModules).obj M).val.obj W) :
    (((pushforwardModulesCompTransport B S hS f g).hom.app M).val.app W).hom y =
      ((smallToposMorphismTypeU_comp B S hS f g).hom.app
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) M)).hom.app W y :=
  val_app_hom_apply_of_moduleSheafFunctor_map_eq
    (moduleSheafFunctor_map_pushforwardModulesCompTransport_hom_app B S hS f g M) W y

/-- The direct image of modules of Stacks 03LU acts on a morphism, on sections, by the direct
image of sheaves of sets of the underlying morphism.  This is
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforward_map` read on sections. -/
theorem modulePushforward_map_val_app_apply (g : Y ⟶ Z)
    {M N : Modules.{u, u} B S hS Y.1 Y.2} (φ : M ⟶ N) (W : (SmallEtale B S hS Z.1)ᵒᵖ)
    (z : ((modulePushforward B S hS g).obj M).val.obj W) :
    (((modulePushforward B S hS g).map φ).val.app W).hom z =
      ((smallEtaleDirectImage B S hS g).map
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map φ)).hom.app W z :=
  val_app_hom_apply_of_moduleSheafFunctor_map_eq
    (moduleSheafFunctor_map_modulePushforward_map B S hS g φ) W z

/-! ### The composition law -/

/-- The composition comparison of the chart-base-change direct images of modules is the
composition comparison of the restriction functors, on sections. -/
theorem smallBaseChangeModulePushforwardCompIso_hom_app_val_app_comp' (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable (f ≫ g).hom)
    (M : Modules.{u, u} B S hS X.1 X.2) (W : (SmallEtale B S hS Z.1)ᵒᵖ)
    (y : ((smallBaseChangeModulePushforward.{u, u} B S hS f hf ⋙
      smallBaseChangeModulePushforward.{u, u} B S hS g hg).obj M).val.obj W) :
    (((smallBaseChangeModulePushforwardCompIsoOfRepresentable.{u, u} B S hS f g hf hg hfg).hom.app
        M).val.app W).hom y =
      ((Functor.sheafPushforwardContinuousComp'
          (smallBaseChange_comp B S hS f g hf hg hfg) (Type u)
          (SmallEtale.topology B S hS Z.1) (SmallEtale.topology B S hS Y.1)
          (SmallEtale.topology B S hS X.1)).hom.app
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) M)).hom.app W y :=
  (smallBaseChangeModulePushforwardCompIso_hom_app_val_app B S hS f g hf hg hfg M W y).trans
    (sheafPushforwardContinuousComp'_smallBaseChange_comp_app B S hS f g hf hg hfg
      (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) M) W.unop y).symm

/-- The composition law on sections.  Each of the five factors is replaced by the morphism of
sheaves of sets it is, after which the identity is
`AlgebraicGeometry.Space.chartComparison_comp` read on sections. -/
theorem modulePushforwardChartIso_hom_comp_val_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable (f ≫ g).hom)
    (M : Modules.{u, u} B S hS X.1 X.2) (W : (SmallEtale B S hS Z.1)ᵒᵖ)
    (z : ((modulePushforward B S hS f ⋙ modulePushforward B S hS g).obj M).val.obj W) :
    (((smallBaseChangeModulePushforwardCompIsoOfRepresentable.{u, u} B S hS f g hf hg hfg).hom.app
            M).val.app W).hom
        ((((modulePushforwardChartIso B S hS g hg).hom.app
            ((smallBaseChangeModulePushforward.{u, u} B S hS f hf).obj M)).val.app W).hom
          ((((modulePushforward B S hS g).map
            ((modulePushforwardChartIso B S hS f hf).hom.app M)).val.app W).hom z)) =
      (((modulePushforwardChartIso B S hS (f ≫ g) hfg).hom.app M).val.app W).hom
        ((((modulePushforwardCompIso B S hS f g).hom.app M).val.app W).hom z) := by
  refine Eq.trans (smallBaseChangeModulePushforwardCompIso_hom_app_val_app_comp'
    B S hS f g hf hg hfg M W _) ?_
  refine Eq.trans (congrArg
    (fun y ↦ ((Functor.sheafPushforwardContinuousComp'
        (smallBaseChange_comp B S hS f g hf hg hfg) (Type u)
        (SmallEtale.topology B S hS Z.1) (SmallEtale.topology B S hS Y.1)
        (SmallEtale.topology B S hS X.1)).hom.app
      (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) M)).hom.app W y)
    (modulePushforwardChartIso_hom_app_chartComparison B S hS g hg
      ((smallBaseChangeModulePushforward.{u, u} B S hS f hf).obj M) W _)) ?_
  refine Eq.trans (congrArg
    (fun y ↦ ((Functor.sheafPushforwardContinuousComp'
          (smallBaseChange_comp B S hS f g hf hg hfg) (Type u)
          (SmallEtale.topology B S hS Z.1) (SmallEtale.topology B S hS Y.1)
          (SmallEtale.topology B S hS X.1)).hom.app
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) M)).hom.app W
      (((chartComparison B S hS g hg).hom.app
        (((smallBaseChange B S hS f hf).sheafPushforwardContinuous (Type u)
            (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)).obj
          (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) M))).hom.app W y))
    ((modulePushforward_map_val_app_apply B S hS g
        ((modulePushforwardChartIso B S hS f hf).hom.app M) W z).trans
      (congrArg (fun m ↦ ((smallEtaleDirectImage B S hS g).map m).hom.app W z)
        (moduleSheafFunctor_map_modulePushforwardChartIso_hom_app B S hS f hf M)))) ?_
  refine Eq.trans (CategoryTheory.Sheaf.hom_congr_app_apply
    (CategoryTheory.NatTrans.congr_app (chartComparison_comp B S hS f g hf hg hfg)
      (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) M)) W z) ?_
  refine Eq.trans (congrArg
    (fun y ↦ ((chartComparison B S hS (f ≫ g) hfg).hom.app
      (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) M)).hom.app W y)
    (modulePushforwardCompIso_hom_app_val_app B S hS f g M W z).symm) ?_
  exact (modulePushforwardChartIso_hom_app_chartComparison B S hS (f ≫ g) hfg M W _).symm

/-- **The identification of the direct image of modules of Stacks 03LU with the direct image
along base change of étale scheme charts is compatible with composition.**  For representable
`f : X ⟶ Y` and `g : Y ⟶ Z` the two identifications, composed with the composition comparison
of the chart-base-change direct images, agree with the composition comparison
`AlgebraicGeometry.Space.modulePushforwardCompIso` of Stacks 03LU followed by the
identification attached to `f ≫ g`.

Everything is checked on underlying sheaves of sets, where it is
`AlgebraicGeometry.Space.chartComparison_comp`. -/
theorem modulePushforwardChartIso_hom_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable (f ≫ g).hom) :
    Functor.whiskerRight (modulePushforwardChartIso B S hS f hf).hom
            (modulePushforward B S hS g) ≫
          Functor.whiskerLeft (smallBaseChangeModulePushforward.{u, u} B S hS f hf)
            (modulePushforwardChartIso B S hS g hg).hom ≫
        (smallBaseChangeModulePushforwardCompIsoOfRepresentable.{u, u} B S hS f g hf hg hfg).hom =
      (modulePushforwardCompIso B S hS f g).hom ≫
        (modulePushforwardChartIso B S hS (f ≫ g) hfg).hom :=
  CategoryTheory.natTrans_three_eq_two_of_val_app _ _ _ _ _
    (fun M W z ↦ modulePushforwardChartIso_hom_comp_val_app B S hS f g hf hg hfg M W z)

end AlgebraicGeometry.Space

end
