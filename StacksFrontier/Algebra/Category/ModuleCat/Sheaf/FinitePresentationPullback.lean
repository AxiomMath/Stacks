module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
import StacksCore.Tactic.StacksAttribute

/-!
# Pullback preserves finite presentation

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and `G` a sheaf of
`𝒪_Y`-modules of finite presentation. Stacks 01BQ says that `f^* G` is again of finite
presentation.

Finite presentation is witnessed by a `SheafOfModules.QuasicoherentData` whose presentations
are finite: a cover `Y = ⋃ V i` together with a finite presentation of `G|_{V i}` for each
`i`. The proof transports that witness along `f`. The preimages `f^{-1}(V i)` cover `X`, and
over each one the restriction of `f^* G` is the pullback of `G|_{V i}` along the induced
morphism of over-sites; the latter identification is the content of
`pullbackOverFunctorIso`, obtained by comparing the two composite adjunctions
`(-)|_{V} ⊣` and `f^* ⊣ f_*` through a base-change isomorphism of pushforwards. A
presentation is carried through a pullback functor by `SheafOfModules.Presentation.map`, since
a pullback preserves colimits and carries the structure sheaf to the structure sheaf, and the
index types of generators and relations are literally unchanged, so finiteness is preserved.

## Main results

* `Stacks.SheafOfModules.modulePullback_isFinitePresentation`: **Tag 01BQ**, the pullback of a
  sheaf of modules of finite presentation along a morphism of ringed spaces is of finite
  presentation.

## Implementation notes

Everything is stated for `RingedSpace.{u, u}` and `SheafOfModules.{u}`, which is the universe
range `RingedSpaceModuleAdjunction.modulePullback` is available in; that restriction comes
from Mathlib's `PresheafOfModules.instIsRightAdjointPushforward` rather than being chosen here.

The base-change isomorphism `pushforwardBaseChangeIso` compares two composites of
pushforwards along the square of sites
`Opens Y ← (Opens Y)/V` and `Opens X ← (Opens X)/f^{-1}V`. It is assembled from
`SheafOfModules.pushforwardComp` on both sides and
`SheafOfModules.pushforwardCongr₂` in the middle, the latter applied to the isomorphism of
site morphisms `siteBaseChangeIso`; the compatibility of the two scalar maps that
`pushforwardCongr₂` requires is checked on sections, where it is naturality of `f^♯` together
with the fact that any two parallel morphisms of opens agree.

## References

* [Stacks Project, Tag 01BQ](https://stacks.math.columbia.edu/tag/01BQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SheafOfModules TopologicalSpace

universe u

namespace Stacks.SheafOfModules

open RingedSpaceModuleAdjunction

/-- A presentation remains a presentation after pullback along a continuous functor of sites
whose pullback identifies the structure sheaves. The finality hypothesis identifies the
pulled-back structure sheaf with the structure sheaf on the source, and the pullback functor
preserves colimits because it is a left adjoint. -/
noncomputable def pullbackPresentation
    {C D : Type u} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [Functor.IsContinuous F J K]
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    [(_root_.SheafOfModules.pushforward φ).IsRightAdjoint] [F.Final]
    [HasWeakSheafify J AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : _root_.SheafOfModules.{u} S} (P : M.Presentation) :
    ((_root_.SheafOfModules.pullback φ).obj M).Presentation :=
  P.map (_root_.SheafOfModules.pullback φ)
    (asIso (_root_.SheafOfModules.pullbackObjUnitToUnit φ)).symm

/-- The preimages of a family of opens covering `Y` cover `X`. -/
lemma preimage_opens_cover {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    {I : Type _} (V : I → Opens Y.carrier)
    (hV : (Opens.grothendieckTopology Y.carrier).CoversTop V) :
    (Opens.grothendieckTopology X.carrier).CoversTop
      (fun i ↦ (Opens.map f.hom.base).obj (V i)) := by
  rw [Opens.coversTop_iff] at hV ⊢
  change (iSup V) = ⊤ at hV
  change (iSup (fun i ↦ (Opens.map f.hom.base).obj (V i))) = ⊤
  calc
    iSup (fun i ↦ (Opens.map f.hom.base).obj (V i)) =
        (Opens.map f.hom.base).obj (iSup V) := (Opens.map_iSup _ _).symm
    _ = ⊤ := by rw [hV, Opens.map_top]

/-- The functor `(Opens Y)/V ⟶ (Opens X)/f^{-1}V` induced by `f` is continuous. -/
instance overMap_isContinuous {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (V : Opens Y.carrier) :
    (Over.post (Opens.map f.hom.base) (X := V)).IsContinuous
      ((Opens.grothendieckTopology Y.carrier).over V)
      ((Opens.grothendieckTopology X.carrier).over ((Opens.map f.hom.base).obj V)) := by
  let F := Opens.map f.hom.base
  have : RepresentablyFlat F := inferInstance
  have : PreservesFiniteLimits F := CategoryTheory.preservesFiniteLimits_of_flat F
  have : Limits.HasPullbacks (Opens Y.carrier) := inferInstance
  have : Limits.PreservesLimitsOfShape Limits.WalkingCospan F := inferInstance
  have : F.PreservesOneHypercovers (Opens.grothendieckTopology Y.carrier)
      (Opens.grothendieckTopology X.carrier) :=
    Functor.PreservesOneHypercovers.of_coverPreserving (coverPreserving_opens_map _)
  have : (Over.post F (X := V)).PreservesOneHypercovers
      ((Opens.grothendieckTopology Y.carrier).over V)
      ((Opens.grothendieckTopology X.carrier).over (F.obj V)) := inferInstance
  infer_instance

/-- The scalar map of the morphism of over-sites induced by `f` above an open `V` of `Y`:
`structureSheafHom f` pushed forward along `Over.forget V`. -/
noncomputable def overStructureSheafHom {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (V : Opens Y.carrier) :
    (structureSheafRing Y).over V ⟶
    (((Over.post (Opens.map f.hom.base) (X := V)).sheafPushforwardContinuous RingCat
      ((Opens.grothendieckTopology Y.carrier).over V)
      ((Opens.grothendieckTopology X.carrier).over ((Opens.map f.hom.base).obj V))).obj
        ((structureSheafRing X).over ((Opens.map f.hom.base).obj V))) :=
  ((Over.forget V).sheafPushforwardContinuous RingCat
    ((Opens.grothendieckTopology Y.carrier).over V)
    (Opens.grothendieckTopology Y.carrier)).map (structureSheafHom f)

/-- Pullback of sheaves of modules along the morphism of over-sites induced by `f`. -/
noncomputable def pullbackOverFunctor {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (V : Opens Y.carrier) :
    _root_.SheafOfModules ((structureSheafRing Y).over V) ⥤
      _root_.SheafOfModules ((structureSheafRing X).over ((Opens.map f.hom.base).obj V)) := by
  letI : (PresheafOfModules.pushforward (overStructureSheafHom f V).hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward _
  letI : (_root_.SheafOfModules.pushforward (overStructureSheafHom f V)).IsRightAdjoint :=
    _root_.SheafOfModules.instIsRightAdjointPushforward _
  exact _root_.SheafOfModules.pullback (overStructureSheafHom f V)

/-- The two ways round the square of sites agree: restricting an open of `Y` to `V` and then
taking preimages is taking preimages and then restricting to `f^{-1}V`. -/
noncomputable def siteBaseChangeIso {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (V : Opens Y.carrier) :
    (Over.star V ⋙ Over.post (Opens.map f.hom.base)) ≅
      (Opens.map f.hom.base ⋙ Over.star ((Opens.map f.hom.base).obj V)) := by
  refine NatIso.ofComponents (fun W ↦ Over.isoMk (eqToIso ?_)) ?_
  · ext x
    simp
  · intro W W' g
    ext
    exact Subsingleton.elim _ _

/-- Base change for pushforward: pushing forward along the morphism of over-sites and then out
of `(Opens Y)/V` is pushing out of `(Opens X)/f^{-1}V` and then along `f`. -/
noncomputable def pushforwardBaseChangeIso {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (V : Opens Y.carrier) :
    _root_.SheafOfModules.pushforward (overStructureSheafHom f V) ⋙
      _root_.SheafOfModules.pushforward
        (_root_.SheafOfModules.pushforwardOver (R := structureSheafRing Y) V) ≅
    _root_.SheafOfModules.pushforward (_root_.SheafOfModules.pushforwardOver
      (R := structureSheafRing X) ((Opens.map f.hom.base).obj V)) ⋙
      _root_.SheafOfModules.pushforward (structureSheafHom f) := by
  let F := Opens.map f.hom.base
  let U := F.obj V
  let b := overStructureSheafHom f V
  haveI : F.IsContinuous (Opens.grothendieckTopology Y.carrier)
      (Opens.grothendieckTopology X.carrier) := inferInstance
  haveI : (Over.post F (X := V)).IsContinuous
      ((Opens.grothendieckTopology Y.carrier).over V)
      ((Opens.grothendieckTopology X.carrier).over U) := overMap_isContinuous f V
  haveI : (PresheafOfModules.pushforward b.hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward _
  haveI : (_root_.SheafOfModules.pushforward b).IsRightAdjoint :=
    _root_.SheafOfModules.instIsRightAdjointPushforward _
  haveI : (Over.star V).IsContinuous (Opens.grothendieckTopology Y.carrier)
      ((Opens.grothendieckTopology Y.carrier).over V) := inferInstance
  haveI : (Over.star V ⋙ Over.post F).IsContinuous
      (Opens.grothendieckTopology Y.carrier)
      ((Opens.grothendieckTopology X.carrier).over U) :=
    Functor.isContinuous_comp (Over.star V) (Over.post F)
      (Opens.grothendieckTopology Y.carrier)
      ((Opens.grothendieckTopology Y.carrier).over V)
      ((Opens.grothendieckTopology X.carrier).over U)
  haveI : (Over.star U).IsContinuous (Opens.grothendieckTopology X.carrier)
      ((Opens.grothendieckTopology X.carrier).over U) := inferInstance
  haveI : (F ⋙ Over.star U).IsContinuous (Opens.grothendieckTopology Y.carrier)
      ((Opens.grothendieckTopology X.carrier).over U) :=
    Functor.isContinuous_comp F (Over.star U)
      (Opens.grothendieckTopology Y.carrier) (Opens.grothendieckTopology X.carrier)
      ((Opens.grothendieckTopology X.carrier).over U)
  let a := _root_.SheafOfModules.pushforwardOver (R := structureSheafRing Y) V
  let c := _root_.SheafOfModules.pushforwardOver (R := structureSheafRing X) U
  let d := structureSheafHom f
  let e := siteBaseChangeIso f V
  let α := _root_.SheafOfModules.pushforwardComp.{u} a b
  let β := _root_.SheafOfModules.pushforwardComp.{u} d c
  let A := (Over.star V).sheafPushforwardContinuous RingCat
    (Opens.grothendieckTopology Y.carrier) ((Opens.grothendieckTopology Y.carrier).over V)
  let D := F.sheafPushforwardContinuous RingCat
    (Opens.grothendieckTopology Y.carrier) (Opens.grothendieckTopology X.carrier)
  let φL := a ≫ A.map b
  let φR := d ≫ D.map c
  let H₁ := (Over.star V ⋙ Over.post F).sheafPushforwardContinuous RingCat
    (Opens.grothendieckTopology Y.carrier) ((Opens.grothendieckTopology X.carrier).over U)
  let H₂ := (F ⋙ Over.star U).sheafPushforwardContinuous RingCat
    (Opens.grothendieckTopology Y.carrier) ((Opens.grothendieckTopology X.carrier).over U)
  let compL : _ ≅ H₁ := Functor.sheafPushforwardContinuousComp
    (Over.star V) (Over.post F) RingCat (Opens.grothendieckTopology Y.carrier)
    ((Opens.grothendieckTopology Y.carrier).over V)
    ((Opens.grothendieckTopology X.carrier).over U)
  let compR : _ ≅ H₂ := Functor.sheafPushforwardContinuousComp
    F (Over.star U) RingCat (Opens.grothendieckTopology Y.carrier)
    (Opens.grothendieckTopology X.carrier) ((Opens.grothendieckTopology X.carrier).over U)
  let φL' : structureSheafRing Y ⟶ H₁.obj ((structureSheafRing X).over U) :=
    φL ≫ compL.hom.app ((structureSheafRing X).over U)
  let φR' : structureSheafRing Y ⟶ H₂.obj ((structureSheafRing X).over U) :=
    φR ≫ compR.hom.app ((structureSheafRing X).over U)
  let nt := Functor.sheafPushforwardContinuousNatTrans e.symm.hom RingCat
    (Opens.grothendieckTopology Y.carrier)
    ((Opens.grothendieckTopology X.carrier).over U)
  have h : φL' ≫ nt.app ((structureSheafRing X).over U) = φR' := by
    ext W x
    let g : (Over.forget V).obj ((Over.star V).obj W.unop) ⟶ W.unop :=
      Limits.prod.snd
    let gX : (Over.forget U).obj ((Over.star U).obj (F.obj W.unop)) ⟶ F.obj W.unop :=
      Limits.prod.snd
    have hnat := d.hom.naturality
      (g.op : Opposite.op W.unop ⟶ Opposite.op (V ⨯ W.unop))
    have hx := ConcreteCategory.congr_hom hnat x
    have ht : Over.Hom.left (e.inv.app W.unop) ≫
        (opensMap f).map g.op.unop = gX :=
      Subsingleton.elim _ _
    have hmap : (structureSheafRing X).obj.map ((opensMap f).map g.op.unop).op ≫
        (structureSheafRing X).obj.map (Over.Hom.left (e.inv.app W.unop)).op =
        (structureSheafRing X).obj.map gX.op :=
      ((structureSheafRing X).obj.map_comp _ _).symm.trans
        (congrArg (structureSheafRing X).obj.map
          (op_comp.symm.trans (congrArg Quiver.Hom.op ht)))
    change (ConcreteCategory.hom ((structureSheafRing X).obj.map
        (Over.Hom.left (e.inv.app W.unop)).op))
        ((ConcreteCategory.hom (d.hom.app (Opposite.op
          ((Over.forget V).obj ((Over.star V).obj W.unop)))))
          ((ConcreteCategory.hom ((structureSheafRing Y).obj.map g.op)) x)) =
      (ConcreteCategory.hom ((structureSheafRing X).obj.map gX.op))
        ((ConcreteCategory.hom (d.hom.app (Opposite.op W.unop))) x)
    have hx' : (ConcreteCategory.hom (d.hom.app (Opposite.op
          ((Over.forget V).obj ((Over.star V).obj W.unop)))))
          ((ConcreteCategory.hom ((structureSheafRing Y).obj.map g.op)) x) =
        (ConcreteCategory.hom ((structureSheafRing X).obj.map
          ((opensMap f).map g.op.unop).op))
          ((ConcreteCategory.hom (d.hom.app (Opposite.op W.unop))) x) := by
      convert hx using 1
      rfl
    calc
      _ = (ConcreteCategory.hom ((structureSheafRing X).obj.map
            (Over.Hom.left (e.inv.app W.unop)).op))
            ((ConcreteCategory.hom ((structureSheafRing X).obj.map
              ((opensMap f).map g.op.unop).op))
              ((ConcreteCategory.hom (d.hom.app (Opposite.op W.unop))) x)) :=
        congrArg (ConcreteCategory.hom ((structureSheafRing X).obj.map
          (Over.Hom.left (e.inv.app W.unop)).op)) hx'
      _ = _ := ConcreteCategory.congr_hom hmap _
  have hL : φL = φL' := by
    dsimp [φL', compL]
    rfl
  exact α ≪≫ _root_.SheafOfModules.pushforwardCongr.{u} hL ≪≫
    _root_.SheafOfModules.pushforwardCongr₂.{u} φL' e.symm h ≪≫ β.symm

/-- Restriction to `f^{-1}V` of the pullback of a sheaf of modules is the pullback along the
induced morphism of over-sites of its restriction to `V`. -/
noncomputable def pullbackOverFunctorIso {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (V : Opens Y.carrier) :
    _root_.SheafOfModules.pushforward (𝟙 ((structureSheafRing Y).over V)) ⋙
        pullbackOverFunctor f V ≅
      modulePullback f ⋙
        _root_.SheafOfModules.pushforward
          (𝟙 ((structureSheafRing X).over ((Opens.map f.hom.base).obj V))) := by
  let U := (Opens.map f.hom.base).obj V
  letI : (PresheafOfModules.pushforward (overStructureSheafHom f V).hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward _
  letI : (_root_.SheafOfModules.pushforward (overStructureSheafHom f V)).IsRightAdjoint :=
    _root_.SheafOfModules.instIsRightAdjointPushforward _
  let adj₁ := (_root_.SheafOfModules.overPushforwardOverAdj (R := structureSheafRing Y) V).comp
    (_root_.SheafOfModules.pullbackPushforwardAdjunction (overStructureSheafHom f V))
  let adj₂ := (modulePullbackPushforwardAdjunction f).comp
    (_root_.SheafOfModules.overPushforwardOverAdj (R := structureSheafRing X) U)
  exact adj₁.leftAdjointUniq (adj₂.ofNatIsoRight (pushforwardBaseChangeIso f V).symm)

/-- `Over.post G` is a final functor: the over-category of the identity is a terminal
structured arrow. -/
instance post_final {C D : Type _} [Category C] [Category D]
    (G : C ⥤ D) (x : C) : (Over.post G (X := x)).Final := by
  refine ⟨fun d => ?_⟩
  let top : Over x := Over.mk (𝟙 x)
  let t : StructuredArrow d (Over.post G (X := x)) :=
    StructuredArrow.mk (Over.homMk (U := d) (V := (Over.post G).obj top) d.hom (by
      change d.hom ≫ G.map (𝟙 x) = d.hom
      simp))
  have : Nonempty (StructuredArrow d (Over.post G (X := x))) := ⟨t⟩
  apply IsConnected.of_induct (j₀ := t)
  intro p hp h j
  let q : j.right ⟶ top := Over.homMk j.right.hom (by
    change j.right.hom ≫ 𝟙 x = j.right.hom
    simp)
  exact (h (StructuredArrow.homMk q (by
    apply Over.OverMorphism.ext
    change j.hom.left ≫ G.map j.right.hom = d.hom
    exact Over.w j.hom))).mpr hp

/-- A presentation of `G|_V` gives a presentation of `(f^* G)|_{f^{-1}V}`. -/
noncomputable def pullbackOverPresentation {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : _root_.SheafOfModules.{u} (structureSheafRing Y)) (V : Opens Y.carrier)
    (P : (G.over V).Presentation) :
    (((modulePullback f).obj G).over ((Opens.map f.hom.base).obj V)).Presentation := by
  let ψ := overStructureSheafHom f V
  let F := Over.post (Opens.map f.hom.base) (X := V)
  haveI : F.IsContinuous
      ((Opens.grothendieckTopology Y.carrier).over V)
      ((Opens.grothendieckTopology X.carrier).over ((Opens.map f.hom.base).obj V)) :=
    overMap_isContinuous f V
  haveI : F.Final := post_final (Opens.map f.hom.base) V
  letI : (PresheafOfModules.pushforward ψ.hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward _
  letI : (_root_.SheafOfModules.pushforward ψ).IsRightAdjoint :=
    _root_.SheafOfModules.instIsRightAdjointPushforward _
  let e := pullbackOverFunctorIso f V
  have he : IsIso (e.app G).hom := (e.app G).isIso_hom
  exact @_root_.SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ (e.app G).hom
    he (pullbackPresentation ψ P)

/-- That presentation is finite when the original one is: the index types of generators and of
relations are unchanged. -/
private theorem pullback_over_presentation_isFinite {X Y : RingedSpace.{u, u}}
    (f : X ⟶ Y) (G : _root_.SheafOfModules.{u} (structureSheafRing Y)) (V : Opens Y.carrier)
    (P : (G.over V).Presentation) [P.IsFinite] :
    (pullbackOverPresentation f G V P).IsFinite := by
  let _ : (PresheafOfModules.pushforward (overStructureSheafHom f V).hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward _
  let _ : (_root_.SheafOfModules.pushforward (overStructureSheafHom f V)).IsRightAdjoint :=
    _root_.SheafOfModules.instIsRightAdjointPushforward _
  have : (pullbackPresentation (overStructureSheafHom f V) P).IsFinite := by
    unfold pullbackPresentation
    constructor <;> refine ⟨?_⟩
    · rw [Presentation.map_generators_I]
      exact (Presentation.IsFinite.isFiniteType_generators (p := P)).finite
    · rw [Presentation.map_relations_I]
      exact (Presentation.IsFinite.isFiniteType_relations (p := P)).finite
  change (Presentation.ofIsIso ((pullbackOverFunctorIso f V).app G).hom
    (pullbackPresentation (overStructureSheafHom f V) P)).IsFinite
  -- explicit, since instance search cannot unify the `Presentation.ofIsIso` arguments
  exact @instIsFiniteOfIsIso _ _ _ _ _ _ _ _ _ _ _ this

/-- **Stacks 01BQ.** The pullback of a sheaf of modules of finite presentation along a
morphism of ringed spaces is of finite presentation. -/
@[stacks 01BQ]
lemma modulePullback_isFinitePresentation {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : _root_.SheafOfModules.{u} (structureSheafRing Y)) [G.IsFinitePresentation] :
    ((modulePullback f).obj G).IsFinitePresentation := by
  obtain ⟨q, hq⟩ := _root_.SheafOfModules.IsFinitePresentation.exists_quasicoherentData G
  have : q.IsFinitePresentation := hq
  let q' : _root_.SheafOfModules.QuasicoherentData.{u, u, u, u} ((modulePullback f).obj G) := {
    I := q.I
    X := fun i ↦ (Opens.map f.hom.base).obj (q.X i)
    coversTop := preimage_opens_cover f q.X q.coversTop
    presentation := fun i ↦ pullbackOverPresentation f G (q.X i) (q.presentation i)
  }
  have hq' : q'.IsFinitePresentation := by
    constructor
    intro i
    exact pullback_over_presentation_isFinite f G (q.X i) (q.presentation i)
  constructor
  exact ⟨q', hq'⟩

/-- Sheafification on a doubly-sliced opens site has a left adjoint.  Stated and named rather
than left to instance search: the site term `((Opens.grothendieckTopology T).over W).over Y` is
long, and naming the instance puts it in the discrimination tree so that use sites resolve
without a `synthInstance` budget for it. -/
public instance isRightAdjoint_sheafToPresheaf_opensOverOver {T : Type u} [TopologicalSpace T]
    (W : Opens T) (Y : CategoryTheory.Over W) :
    (CategoryTheory.sheafToPresheaf (((Opens.grothendieckTopology T).over W).over Y)
      AddCommGrpCat.{u}).IsRightAdjoint := inferInstance

end Stacks.SheafOfModules

end
