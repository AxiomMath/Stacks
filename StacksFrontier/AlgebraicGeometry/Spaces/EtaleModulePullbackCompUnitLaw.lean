module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitSetBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompMate
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompIsoEtaleRestriction

/-!
# The strict composition of pushforwards of sheaves of modules, and the unit it carries

Mathlib's `SheafOfModules.pushforwardComp` identifies the composite of two pushforwards of sheaves
of modules with the pushforward along the composite functor of sites, and it is
`CategoryTheory.Iso.refl`: the two functors are definitionally equal. Along an étale morphism of
algebraic spaces the pushforward at an identity structure map is étale restriction
(`AlgebraicGeometry.Space.etaleModulePullback`), so
`AlgebraicGeometry.Space.etaleModulePullbackComp` is an instance of `pushforwardComp`. This file
proves the composition law for the units of two pushforward adjunctions, reduced to an equation of
sections, together with the chart-level comparisons used to read it for étale restriction.

## Main results

* `SheafOfModules.pushforwardComp_hom_app_eq_id`: **the strict composition of pushforwards of
  sheaves of modules is the identity**, at every sheaf of modules.
* `SheafOfModules.unit_ofNatIsoLeft_pushforwardComp`: **the composition law for the units of two
  pushforward adjunctions**, reduced to one equation of morphisms of the underlying objects of a
  faithful functor.
* `SheafOfModules.unit_ofNatIsoLeft_pushforwardComp_sections`: the same law, reduced further to
  **one equation of sections** per sheaf of modules, chart and section.
* `AlgebraicGeometry.Space.etaleModulePullbackComp_obj_eq`: **the strict composition of étale
  restrictions at concrete charts**, as an equation of modules.
* `AlgebraicGeometry.Space.modulePushforwardCompGeometricSection` and
  `AlgebraicGeometry.Space.modulePushforwardCompIso_hom_app_val_app_geometricSection`: the
  geometric comparison of Stacks 03G2, part (3) acting on a module section, and the reading of
  Stacks 03LU against it.
* `AlgebraicGeometry.Space.modulePushforward_map_val_app_geometric`: the direct image of a
  morphism of modules, on a section, is the geometric direct image of the underlying map.
* `AlgebraicGeometry.Space.modulePushforward_obj_etaleModulePullbackComp_eq` and
  `AlgebraicGeometry.Space.etaleUnitAtCompositeChart`: the two spellings of the restricted module
  through one direct image, and the unit of étale restriction read with its codomain at the
  composite chart.
* `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction_unit_comp_app_sections`: the
  composition law of Stacks 03LQ at an arbitrary sheaf of sets, read on a section.

## References

* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public section

open CategoryTheory Opposite

namespace SheafOfModules

universe vv vv₁ vv₂ vv₃ vvt uut uu₁ uu₂ uu₃ uu

variable {CC : Type uu₁} [Category.{vv₁} CC] {DD : Type uu₂} [Category.{vv₂} DD]
  {DD' : Type uu₃} [Category.{vv₃} DD']
  {J : GrothendieckTopology CC} {K : GrothendieckTopology DD} {K' : GrothendieckTopology DD'}
  {F : CC ⥤ DD} {G : DD ⥤ DD'}
  {Sp : Sheaf J RingCat.{uu}} {R : Sheaf K RingCat.{uu}} {R' : Sheaf K' RingCat.{uu}}
  [Functor.IsContinuous F J K] [Functor.IsContinuous G K K']
  [Functor.IsContinuous (F ⋙ G) J K']

omit [(F ⋙ G).IsContinuous J K'] in
/-- **The strict composition of pushforwards of sheaves of modules is the identity.**
`SheafOfModules.pushforwardComp` is `CategoryTheory.Iso.refl`, so its component at a sheaf of
modules is the identity of the iterated pushforward. -/
theorem pushforwardComp_hom_app_eq_id
    (φ : Sp ⟶ (F.sheafPushforwardContinuous RingCat.{uu} J K).obj R)
    (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{uu} K K').obj R')
    (M : SheafOfModules.{vv} R') :
    (pushforwardComp.{vv} φ ψ).hom.app M =
      CategoryStruct.id ((pushforward.{vv} ψ ⋙ pushforward.{vv} φ).obj M) :=
  rfl

/-- **The composition law for the units of two pushforward adjunctions.**  Let `pushforward ψ`
and `pushforward φ` be two pushforwards of sheaves of modules with right adjoints `Gg` and `Gh`,
let `iso` identify the composite `Gh ⋙ Gg` of the right adjoints with a functor `GG`, and let
`adj2` be an adjunction between the pushforward along the composite functor of sites and `GG`.
Then the adjunction assembled from the two factors through `iso`, read through
`SheafOfModules.pushforwardComp`, has the same unit as `adj2` as soon as the three factors of its
unit compose to the unit of `adj2`.

The first two factors are composed **with their composite's codomain written out** as
`(Gh ⋙ Gg).obj` of the pushforward along the composite functor of sites, rather than as the
iterated pushforward that the two factors themselves produce. -/
theorem unit_ofNatIsoLeft_pushforwardComp
    (φ : Sp ⟶ (F.sheafPushforwardContinuous RingCat.{uu} J K).obj R)
    (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{uu} K K').obj R')
    {Gg : SheafOfModules.{vv} R ⥤ SheafOfModules.{vv} R'}
    {Gh : SheafOfModules.{vv} Sp ⥤ SheafOfModules.{vv} R}
    {GG : SheafOfModules.{vv} Sp ⥤ SheafOfModules.{vv} R'}
    (adjg : pushforward.{vv} ψ ⊣ Gg) (adjh : pushforward.{vv} φ ⊣ Gh)
    (iso : Gh ⋙ Gg ≅ GG)
    (adj2 : pushforward.{vv} (F := F ⋙ G)
      (φ ≫ (F.sheafPushforwardContinuous RingCat.{uu} J K).map ψ) ⊣ GG)
    (hyp : ∀ M : SheafOfModules.{vv} R',
      @CategoryStruct.comp _ _ M (Gg.obj ((pushforward.{vv} ψ).obj M))
          ((Gh ⋙ Gg).obj ((pushforward.{vv} (F := F ⋙ G)
            (φ ≫ (F.sheafPushforwardContinuous RingCat.{uu} J K).map ψ)).obj M))
          (adjg.unit.app M) (Gg.map (adjh.unit.app ((pushforward.{vv} ψ).obj M))) ≫
        iso.hom.app ((pushforward.{vv} (F := F ⋙ G)
          (φ ≫ (F.sheafPushforwardContinuous RingCat.{uu} J K).map ψ)).obj M) =
      adj2.unit.app M) :
    (((adjg.comp adjh).ofNatIsoRight iso).ofNatIsoLeft (pushforwardComp.{vv} φ ψ)).unit =
      adj2.unit := by
  refine NatTrans.ext (funext fun M ↦ ?_)
  refine Eq.trans (NatTrans.congr_app
    (Adjunction.ofNatIsoLeft_unit ((adjg.comp adjh).ofNatIsoRight iso)
      (pushforwardComp.{vv} φ ψ)) M) ?_
  refine Eq.trans (NatTrans.comp_app _ _ M) ?_
  refine Eq.trans (congrArg (fun m ↦ ((adjg.comp adjh).ofNatIsoRight iso).unit.app M ≫ m)
    ((congrArg GG.map (pushforwardComp_hom_app_eq_id φ ψ M)).trans (GG.map_id _))) ?_
  refine Eq.trans (Category.comp_id _) ?_
  refine Eq.trans (Adjunction.comp_ofNatIsoRight_unit_app adjg adjh iso M) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact hyp M

/-- **The composition law for the units of two pushforward adjunctions, read on sections.**
This is `SheafOfModules.unit_ofNatIsoLeft_pushforwardComp` with its hypothesis split at the two
composites and read on a section: one equation of sections per sheaf of modules, chart and section.
-/
theorem unit_ofNatIsoLeft_pushforwardComp_sections
    (φ : Sp ⟶ (F.sheafPushforwardContinuous RingCat.{uu} J K).obj R)
    (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{uu} K K').obj R')
    {Gg : SheafOfModules.{vv} R ⥤ SheafOfModules.{vv} R'}
    {Gh : SheafOfModules.{vv} Sp ⥤ SheafOfModules.{vv} R}
    {GG : SheafOfModules.{vv} Sp ⥤ SheafOfModules.{vv} R'}
    (adjg : pushforward.{vv} ψ ⊣ Gg) (adjh : pushforward.{vv} φ ⊣ Gh)
    (iso : Gh ⋙ Gg ≅ GG)
    (adj2 : pushforward.{vv} (F := F ⋙ G)
      (φ ≫ (F.sheafPushforwardContinuous RingCat.{uu} J K).map ψ) ⊣ GG)
    (hyp : ∀ (M : SheafOfModules.{vv} R') (U : DD'ᵒᵖ) (t : M.val.obj U),
      (iso.hom.app ((pushforward.{vv} (F := F ⋙ G)
            (φ ≫ (F.sheafPushforwardContinuous RingCat.{uu} J K).map ψ)).obj M)).val.app U
          ((Gg.map (adjh.unit.app ((pushforward.{vv} ψ).obj M))).val.app U
            ((adjg.unit.app M).val.app U t)) =
        (adj2.unit.app M).val.app U t) :
    (((adjg.comp adjh).ofNatIsoRight iso).ofNatIsoLeft (pushforwardComp.{vv} φ ψ)).unit =
      adj2.unit := by
  refine unit_ofNatIsoLeft_pushforwardComp φ ψ adjg adjh iso adj2 fun M ↦ ?_
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦
    ModuleCat.hom_ext (LinearMap.ext fun t ↦ ?_))
  refine Eq.trans (SheafOfModules.comp_val_app_apply _ _ U t) ?_
  refine Eq.trans (SheafOfModules.comp_val_app_apply _ _ U t) ?_
  exact hyp M U t

end SheafOfModules

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {A C D X Y Z : AlgebraicSpaces B S hS}
variable (h : D ⟶ A) (g : A ⟶ C) (hh : IsEtale B S hS h.hom) (hg : IsEtale B S hS g.hom)
    (hhg : IsEtale B S hS (h ≫ g).hom)

-- Postcomposition along `h` and then along `g` is continuous for the topologies of the small
-- étale ringed sites.
attribute [local instance] smallEtaleRingedSite_isContinuous_smallEtalePostcomp_comp

/-- **The composition law of Stacks 03LQ at an arbitrary sheaf of sets, read on a section.**
The unit of the small étale restriction adjunction along `h ≫ g`, on a section over a chart of
the target, is the unit along `g` followed by the direct image along `g` of the unit along `h`
and by the comparison of direct images of Stacks 03G2, part (3). -/
theorem smallEtaleSetRestrictionAdjunction_unit_comp_app_sections
    (Q : Sheaf (SmallEtale.topology B S hS C.1) (Type u))
    (U : (SmallEtale B S hS C.1)ᵒᵖ) (s : Q.obj.obj U) :
    ((smallEtaleSetRestrictionAdjunction B S hS (h ≫ g) hhg).unit.app Q).hom.app U s =
      ((smallToposMorphismTypeU_comp B S hS h g).hom.app
          ((smallEtaleSetRestriction B S hS (h ≫ g) hhg).obj Q)).hom.app U
        (((smallEtaleDirectImage B S hS g).map
            ((smallEtaleSetRestrictionAdjunction B S hS h hh).unit.app
              ((smallEtaleSetRestriction B S hS g hg).obj Q))).hom.app U
          (((smallEtaleSetRestrictionAdjunction B S hS g hg).unit.app Q).hom.app U s)) :=
  congrArg (fun m ↦ m.hom.app U s)
    (smallEtaleSetRestrictionAdjunction_unit_comp_app B S hS h g hh hg hhg Q).symm

/-- **The direct image of a morphism of modules, read on a section, is the geometric direct
image of the underlying map of sheaves of sets.** -/
theorem modulePushforward_map_val_app_geometric (f : X ⟶ Y)
    {M₁ M₂ : Modules.{u, u} B S hS X.1 X.2} (φ : M₁ ⟶ M₂) (V : (SmallEtale B S hS Y.1)ᵒᵖ)
    (y : ((modulePushforward B S hS f).obj M₁).val.obj V) :
    ((modulePushforward B S hS f).map φ).val.app V y =
      ((smallToposMorphismTypeU B S hS f).pushforward.map
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map φ)).hom.app V y :=
  (moduleSheafFunctor_map_hom_app_apply B S hS ((modulePushforward B S hS f).map φ) V y).symm.trans
    (congrArg (fun m ↦ m.hom.app V y)
      (moduleSheafFunctor_map_modulePushforward_map B S hS f φ))

/-- **The geometric comparison of Stacks 03G2, part (3), acting on a module section.** Its domain
and codomain are the module-side spellings of the sections of the iterated direct image and of the
direct image along the composite. -/
noncomputable def modulePushforwardCompGeometricSection (f : X ⟶ Y) (k : Y ⟶ Z)
    (N : Modules.{u, u} B S hS X.1 X.2) (V : (SmallEtale B S hS Z.1)ᵒᵖ)
    (y : ((modulePushforward B S hS f ⋙ modulePushforward B S hS k).obj N).val.obj V) :
    ((modulePushforward B S hS (f ≫ k)).obj N).val.obj V :=
  ((smallToposMorphismTypeU_comp B S hS f k).hom.app
    (moduleSetSheaf B S hS X N)).hom.app V y

/-- **Stacks 03LU on a module section, against the named geometric comparison.**  The comparison
of direct images of Stacks 03LU acts on a section of the iterated direct image by
`AlgebraicGeometry.Space.modulePushforwardCompGeometricSection`. -/
theorem modulePushforwardCompIso_hom_app_val_app_geometricSection (f : X ⟶ Y) (k : Y ⟶ Z)
    (N : Modules.{u, u} B S hS X.1 X.2) (V : (SmallEtale B S hS Z.1)ᵒᵖ)
    (y : ((modulePushforward B S hS f ⋙ modulePushforward B S hS k).obj N).val.obj V) :
    ((modulePushforwardCompIso B S hS f k).hom.app N).val.app V y =
      modulePushforwardCompGeometricSection B S hS f k N V y :=
  modulePushforwardCompIso_hom_app_val_app B S hS f k N V y

/-- **Iterated étale restriction is restriction along the composite chart, at a concrete
module.**  Both sides are the pushforward of sheaves of modules along postcomposition with the
composite chart, so the two objects are equal on the nose. -/
theorem etaleModulePullbackComp_obj_eq (M : Modules.{u, u} B S hS C.1 C.2) :
    (etaleModulePullback.{u, u} B S hS g hg ⋙
        etaleModulePullback.{u, u} B S hS h hh).obj M =
      (etaleModulePullback.{u, u} B S hS (h ≫ g) hhg).obj M :=
  rfl

/-- The direct image along `h` of iterated étale restriction is the direct image along `h` of
restriction along the composite chart: the two restrictions are the same module, so their direct
images are the same module. -/
theorem modulePushforward_obj_etaleModulePullbackComp_eq
    (M : Modules.{u, u} B S hS C.1 C.2) :
    (modulePushforward B S hS h).obj
        ((etaleModulePullback.{u, u} B S hS h hh).obj
          ((etaleModulePullback.{u, u} B S hS g hg).obj M)) =
      (modulePushforward B S hS h).obj
        ((etaleModulePullback.{u, u} B S hS (h ≫ g) hhg).obj M) :=
  rfl

/-- **The unit of étale restriction along `h`, at the restriction of `M` along `g`, with its
codomain written at the composite chart.**  This is
`(etaleModulePullbackAdjunction B S hS h hh).unit` at `g^*M`, retyped through
`AlgebraicGeometry.Space.modulePushforward_obj_etaleModulePullbackComp_eq`. -/
noncomputable def etaleUnitAtCompositeChart (M : Modules.{u, u} B S hS C.1 C.2) :
    (etaleModulePullback.{u, u} B S hS g hg).obj M ⟶
      (modulePushforward B S hS h).obj
        ((etaleModulePullback.{u, u} B S hS (h ≫ g) hhg).obj M) :=
  (etaleModulePullbackAdjunction B S hS h hh).unit.app
    ((etaleModulePullback.{u, u} B S hS g hg).obj M)

end AlgebraicGeometry.Space

end
