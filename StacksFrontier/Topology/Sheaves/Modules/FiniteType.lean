module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Sheaves.Module
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModuleFunctors
import StacksCore.Tactic.StacksAttribute

/-!
# Pullback of a finite type module

A sheaf of modules on a ringed space is of finite type when it is generated, locally on an
open cover, by finitely many sections. This property is stable under pullback along a
morphism of ringed spaces.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.siteRestrict`, `siteRestrictAdjunction`,
  `overFunctorIsoSiteRestrict`, `overFunctorIsoPullback`: restriction of a sheaf of modules to
  an open subspace, and its identification with pullback along the open immersion.
* `Stacks.SheafOfModules.modulePullbackGeneratingSections`: pullback of global generating
  sections.
* `Stacks.SheafOfModules.OpenPreimageFactorization`,
  `Stacks.SheafOfModules.openPreimageFactorization`: the factorization of `f` through the
  restrictions to an open set of the target and to its preimage.
* `Stacks.SheafOfModules.modulePullbackOpenPreimageIso`: pullback commutes with restriction to
  an open set and its preimage.

## Main results

* `AlgebraicGeometry.SheafOfModules.pullback_isFiniteType`: the pullback of a finite type
  module along a morphism of ringed spaces is again of finite type.

## Implementation notes

A sheaf of modules on a ringed space is `Modules`, its pullback is `pullback`, and finite
type is Mathlib's `SheafOfModules.IsFiniteType`, that is, local finite generation.

The generating sections of the pullback are produced one open set of the cover at a time. A
cover of the target by opens `V` pulls back to a cover of the source by the preimages
`f⁻¹ V`, and the restriction of `f` factors through a morphism of ringed spaces
`f⁻¹ V ⟶ V` of the restricted spaces. Pullback along that morphism carries generating
sections of `G|_V` to generating sections of `(f^* G)|_{f⁻¹ V}`, which is what the
local-generators datum of the pullback needs. Transporting between the restricted space and
the slice site is Mathlib's `sheafOfModulesEquivOver`.

The conclusion is an instance, so that later constructions obtain preservation of finite type
by typeclass inference.

## References

* [Stacks Project, Tag 01B6](https://stacks.math.columbia.edu/tag/01B6)
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace
open RingedSpaceModuleAdjunction

namespace AlgebraicGeometry.SheafOfModules

/-- Restriction of sheaves of modules to an open subspace, realised as pushforward along the
continuous functor induced by the open embedding of the restricted space. -/
noncomputable def siteRestrict (X : RingedSpace.{u, u})
    (U : Opens (X : TopCat)) :
    _root_.SheafOfModules.{u} (structureSheafRing X) ⥤
      _root_.SheafOfModules.{u} (structureSheafRing (X.restrict U.isOpenEmbedding)) := by
  let j := X.ofRestrict U.isOpenEmbedding
  let h : Topology.IsOpenEmbedding j.hom.base :=
    (SheafedSpace.IsOpenImmersion.ofRestrict X U.isOpenEmbedding).base_open
  let F := h.functor
  letI : F.IsContinuous
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding : TopCat))
      (Opens.grothendieckTopology (X : TopCat)) := h.functor_isContinuous
  exact _root_.SheafOfModules.pushforward (F := F) (𝟙 _)

/-- Restriction to an open subspace is left adjoint to pushforward along the open
immersion. -/
noncomputable def siteRestrictAdjunction (X : RingedSpace.{u, u})
    (U : Opens (X : TopCat)) :
    siteRestrict X U ⊣ modulePushforward (X.ofRestrict U.isOpenEmbedding) := by
  let j := X.ofRestrict U.isOpenEmbedding
  let h : Topology.IsOpenEmbedding j.hom.base :=
    (SheafedSpace.IsOpenImmersion.ofRestrict X U.isOpenEmbedding).base_open
  let F := h.functor
  let G := Opens.map j.hom.base
  let adj : F ⊣ G := h.isOpenMap.adjunction
  letI : F.IsContinuous
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding : TopCat))
      (Opens.grothendieckTopology (X : TopCat)) := h.functor_isContinuous
  letI : G.IsContinuous
      (Opens.grothendieckTopology (X : TopCat))
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding : TopCat)) := by
    infer_instance
  let R := structureSheafRing X
  let S := structureSheafRing (X.restrict U.isOpenEmbedding)
  let φ : S ⟶ (F.sheafPushforwardContinuous RingCat _ _).obj R := 𝟙 _
  let ψ : R ⟶ (G.sheafPushforwardContinuous RingCat _ _).obj S := structureSheafHom j
  have h1 : Functor.whiskerRight (NatTrans.op adj.counit) R.obj =
      ψ.hom ≫ G.op.whiskerLeft φ.hom := by
    ext V x
    rfl
  have h2 : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op adj.unit) S.obj = 𝟙 S.obj := by
    ext V x
    change (R.obj.map (adj.counit.app (F.obj V.unop)).op ≫
      R.obj.map (F.map (adj.unit.app V.unop)).op) x = x
    rw [← Functor.map_comp, ← op_comp]
    have htri := adj.left_triangle_components V.unop
    rw [htri]
    exact CategoryTheory.Functor.map_id_apply R.obj (Opposite.op (F.obj V.unop)) x
  change _root_.SheafOfModules.pushforward φ ⊣ _root_.SheafOfModules.pushforward ψ
  exact _root_.SheafOfModules.pushforwardPushforwardAdj adj φ ψ h1 h2

/-- Passing to the slice site over an open set and then transporting to the restricted space
is the same as restricting to that open subspace. -/
noncomputable def overFunctorIsoSiteRestrict
    (X : RingedSpace.{u, u}) (U : Opens (X : TopCat)) :
    _root_.SheafOfModules.overFunctor (structureSheafRing X) U ⋙
      (U.sheafOfModulesEquivOver (structureSheafRing X)).functor ≅ siteRestrict X U := by
  haveI : ((Opens.overEquivalence U).symm.functor).IsContinuous
      (Opens.grothendieckTopology U)
      ((Opens.grothendieckTopology X).over U) := inferInstance
  haveI : (Over.forget U).IsContinuous
      ((Opens.grothendieckTopology X).over U)
      (Opens.grothendieckTopology X) := inferInstance
  have hcont : ((Opens.overEquivalence U).symm.functor ⋙ Over.forget U).IsContinuous
      (Opens.grothendieckTopology U)
      (Opens.grothendieckTopology X) :=
    Functor.isContinuous_comp _ _ _ ((Opens.grothendieckTopology X).over U) _
  refine _root_.SheafOfModules.pushforwardComp _ _ ≪≫
    _root_.SheafOfModules.pushforwardCongr ?_
  ext W x
  rfl

/-- The restriction of a sheaf of modules to an open subspace, transported to the restricted
space, is the pullback along the open immersion. -/
noncomputable def overFunctorIsoPullback
    (X : RingedSpace.{u, u}) (U : Opens (X : TopCat))
    (M : _root_.SheafOfModules (structureSheafRing X)) :
    ((U.sheafOfModulesEquivOver (structureSheafRing X)).functor.obj (M.over U)) ≅
      (modulePullback (X.ofRestrict U.isOpenEmbedding)).obj M :=
  (overFunctorIsoSiteRestrict X U).app M ≪≫
    ((siteRestrictAdjunction X U).leftAdjointUniq
      (modulePullbackPushforwardAdjunction (X.ofRestrict U.isOpenEmbedding))).app M

end AlgebraicGeometry.SheafOfModules

namespace Stacks.SheafOfModules

/-- Generating sections of a sheaf of modules on a ringed space pull back to generating
sections of its pullback: the pullback functor is a left adjoint, and it takes the unit
module to the unit module. -/
noncomputable def modulePullbackGeneratingSections
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : _root_.SheafOfModules.{u} (structureSheafRing Y)) (σ : G.GeneratingSections) :
    ((modulePullback f).obj G).GeneratingSections := by
  letI : (_root_.SheafOfModules.pushforward (structureSheafHom f)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint f
  letI : (modulePullback f).IsLeftAdjoint :=
    ⟨_, ⟨modulePullbackPushforwardAdjunction f⟩⟩
  letI : (Opens.map f.hom.base).Final := CategoryTheory.final_of_representablyFlat _
  letI : IsIso (_root_.SheafOfModules.pullbackObjUnitToUnit (structureSheafHom f)) :=
    inferInstance
  exact σ.map (modulePullback f)
    (asIso (_root_.SheafOfModules.pullbackObjUnitToUnit (structureSheafHom f))).symm

/-- A factorization of a morphism of ringed spaces through the restrictions to an open set of
the target and to its preimage. -/
structure OpenPreimageFactorization
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (V : Opens (Y : TopCat)) where
  /-- The induced morphism between the restricted ringed spaces. -/
  map : X.restrict ((Opens.map f.hom.base).obj V).isOpenEmbedding ⟶
    Y.restrict V.isOpenEmbedding
  /-- The factorization identity. -/
  fac : X.ofRestrict ((Opens.map f.hom.base).obj V).isOpenEmbedding ≫ f =
    map ≫ Y.ofRestrict V.isOpenEmbedding

/-- A morphism of ringed spaces restricts to a morphism from the preimage of an open set of
the target to that open set, because the image of the preimage lies in it. -/
noncomputable def openPreimageFactorization
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (V : Opens (Y : TopCat)) :
    OpenPreimageFactorization f V := by
  let U := (Opens.map f.hom.base).obj V
  let jU : X.restrict U.isOpenEmbedding ⟶ X := X.ofRestrict U.isOpenEmbedding
  let jV : Y.restrict V.isOpenEmbedding ⟶ Y := Y.ofRestrict V.isOpenEmbedding
  let F := SheafedSpace.forgetToPresheafedSpace (C := CommRingCat)
  have hrange : Set.range (jU.hom.base ≫ f.hom.base) ⊆ Set.range jV.hom.base := by
    have hrV : Set.range jV.hom.base = (V : Set Y) := Opens.set_range_inclusion' V
    rw [hrV, Set.range_subset_iff]
    intro x
    change f.hom.base (jU.hom.base x) ∈ V
    have hxU : (ConcreteCategory.hom (F.map jU).base) x ∈ U := by
      have hrU : Set.range jU.hom.base = (U : Set X) := Opens.set_range_inclusion' U
      have hxrange : jU.hom.base x ∈ Set.range jU.hom.base := Set.mem_range_self x
      rw [hrU] at hxrange
      exact hxrange
    exact hxU
  let glift : F.obj (X.restrict U.isOpenEmbedding) ⟶
      F.obj (Y.restrict V.isOpenEmbedding) :=
    PresheafedSpace.IsOpenImmersion.lift (F.map jV) (F.map (jU ≫ f)) hrange
  let g : X.restrict U.isOpenEmbedding ⟶ Y.restrict V.isOpenEmbedding := F.preimage glift
  have hfac : jU ≫ f = g ≫ jV := by
    apply F.map_injective
    rw [F.map_comp, F.map_comp, show F.map g = glift from F.map_preimage glift]
    exact (PresheafedSpace.IsOpenImmersion.lift_fac (F.map jV) (F.map (jU ≫ f)) hrange).symm
  exact ⟨g, hfac⟩

/-- Pullback commutes with restriction: the pullback of a sheaf of modules, restricted to the
preimage of an open set `V`, is the pullback of its restriction to `V` along the restricted
morphism. -/
noncomputable def modulePullbackOpenPreimageIso
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (V : Opens (Y : TopCat))
    (M : _root_.SheafOfModules (structureSheafRing Y)) :
    (((Opens.map f.hom.base).obj V).sheafOfModulesEquivOver (structureSheafRing X)).functor.obj
        (((modulePullback f).obj M).over ((Opens.map f.hom.base).obj V)) ≅
    (modulePullback (openPreimageFactorization f V).map).obj
        ((V.sheafOfModulesEquivOver (structureSheafRing Y)).functor.obj (M.over V)) := by
  let U := (Opens.map f.hom.base).obj V
  let jU := X.ofRestrict U.isOpenEmbedding
  let jV := Y.ofRestrict V.isOpenEmbedding
  let g := (openPreimageFactorization f V).map
  have hfac : jU ≫ f = g ≫ jV := (openPreimageFactorization f V).fac
  exact AlgebraicGeometry.SheafOfModules.overFunctorIsoPullback X U
      ((modulePullback f).obj M) ≪≫
    ((pullbackComp jU f).app M).symm ≪≫
    eqToIso (by rw [hfac]) ≪≫
    (pullbackComp g jV).app M ≪≫
    (modulePullback g).mapIso
      (AlgebraicGeometry.SheafOfModules.overFunctorIsoPullback Y V M).symm

end Stacks.SheafOfModules

namespace AlgebraicGeometry.SheafOfModules

open Stacks.SheafOfModules (modulePullbackGeneratingSections openPreimageFactorization modulePullbackOpenPreimageIso)

/-- Finitely many sections generating a sheaf of modules over an open set `V` of the target
pull back to finitely many sections generating the pullback over the preimage of `V`. The
transport runs through the restricted ringed spaces: the sections are carried to the
restriction of the target over `V`, pulled back along the restricted morphism
`f⁻¹ V ⟶ V`, and carried back to the slice site over `f⁻¹ V`. -/
private noncomputable def pullbackGeneratorsOver
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : _root_.SheafOfModules.{u} (structureSheafRing Y)) (V : Opens (Y : TopCat))
    (σ : (G.over V).GeneratingSections) [σ.IsFiniteType] :
    {τ : (((modulePullback f).obj G).over
      ((Opens.map f.hom.base).obj V)).GeneratingSections // τ.IsFiniteType} := by
  let U := (Opens.map f.hom.base).obj V
  let eY := V.sheafOfModulesEquivOver (structureSheafRing Y)
  let hpresY : Limits.PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1}
      eY.functor := eY.toAdjunction.leftAdjoint_preservesColimits
  let ηY := TopologicalSpace.Opens.sheafOfModulesEquivOverUnit V (structureSheafRing Y)
  let σY := @_root_.SheafOfModules.GeneratingSections.map _ _ _ _ _ _ _ _ _ _ _ _ _
    σ eY.functor hpresY ηY
  let g := (openPreimageFactorization f V).map
  let σX := modulePullbackGeneratingSections g (eY.functor.obj (G.over V)) σY
  let eX := U.sheafOfModulesEquivOver (structureSheafRing X)
  let σRest := σX.equivOfIso (modulePullbackOpenPreimageIso f V G).symm
  let hpres : Limits.PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1}
      eX.symm.functor := eX.symm.toAdjunction.leftAdjoint_preservesColimits
  let η := (TopologicalSpace.Opens.sheafOfModulesEquivOverInverseUnit U (structureSheafRing X)).symm
  let σOver := @_root_.SheafOfModules.GeneratingSections.map _ _ _ _ _ _ _ _ _ _ _ _ _
    σRest eX.symm.functor hpres η
  let result := σOver.equivOfIso
    (eX.unitIso.app (((modulePullback f).obj G).over U)).symm
  exact ⟨result, ⟨inferInstanceAs (Finite σ.I)⟩⟩

/-- Finite type is preserved by pullback of sheaves of modules along a morphism of ringed
spaces, stated for `modulePullback`. The cover witnessing finite generation of `G` is pulled
back open set by open set. -/
private theorem isFiniteType_modulePullback {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : _root_.SheafOfModules.{u} (structureSheafRing Y)) [G.IsFiniteType] :
    ((modulePullback f).obj G).IsFiniteType := by
  classical
  obtain ⟨p, hp⟩ := (inferInstance : G.IsFiniteType).exists_localGeneratorsData
  let q := p.shrink
  have hq : ∀ i : q.I, (q.generators i).IsFiniteType := fun i => by
    dsimp [q]
    exact hp.isFiniteType i.2.choose
  let gen := fun i : ULift q.I =>
    @pullbackGeneratorsOver _ _ f G (q.X i.down) (q.generators i.down) (hq i.down)
  let data : _root_.SheafOfModules.LocalGeneratorsData.{u, u, u, u}
      ((modulePullback f).obj G) :=
    { I := ULift q.I
      X := fun i => (Opens.map f.hom.base).obj (q.X i.down)
      coversTop := coversTop_preimage f q.X q.coversTop
      generators := fun i => (gen i).1 }
  have hdata : data.IsFiniteType := by
    constructor
    intro i
    exact (gen i).2
  exact _root_.SheafOfModules.IsFiniteType.mk.{u, u, u} ⟨data, hdata⟩

/-- **Stacks Project, Tag 01B6.** The pullback of a finite type module along a morphism of
ringed spaces is of finite type. -/
@[stacks 01B6]
noncomputable instance pullback_isFiniteType {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    (G : _root_.Modules Y) [G.IsFiniteType] :
    ((_root_.pullback f).obj G).IsFiniteType := by
  let _ : _root_.SheafOfModules.IsFiniteType (R := structureSheafRing Y) G := by assumption
  exact isFiniteType_modulePullback f G

end AlgebraicGeometry.SheafOfModules
