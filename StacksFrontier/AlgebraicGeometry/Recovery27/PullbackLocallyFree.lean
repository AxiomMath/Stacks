module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree

/-!
# Pullback preserves being finite locally free of a fixed rank

For a continuous map of topological spaces and a morphism of sheaves of rings over it,
the pullback of a sheaf of modules that is finite locally free of rank `r` is again
finite locally free of rank `r`.

## Main results

* `AlgebraicGeometry.Grassmannian.exists_pullbackRestrictionData`: over a fixed open of
  the target, the pullback is computed by a colimit-preserving functor between the
  categories of modules on the two slice sites.
* `AlgebraicGeometry.Grassmannian.isFiniteLocallyFreeOfRank_pullback`: pullback preserves
  being finite locally free of a given rank.

## Implementation notes

The local data is produced by restricting the morphism of sheaves of rings to a slice
site and taking the mate of the comparison isomorphism between the two ways of
restricting and pushing forward. The comparison between the product of opens and its
image uses that the inverse-image functor on opens preserves finite limits.

## References

* [Stacks Project, Tag 089S](https://stacks.math.columbia.edu/tag/089S)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

attribute [local implicit_reducible] CategoryTheory.Functor.sheafPushforwardContinuous

universe u

namespace AlgebraicGeometry.Grassmannian

open Limits TopologicalSpace

/-- Over a fixed open `U` of the target, the pullback of sheaves of modules along `φ` is
computed by a colimit-preserving functor between the slice sites which matches the unit
objects. -/
public theorem exists_pullbackRestrictionData {X Y : TopCat.{u}} (f : X ⟶ Y)
    {S : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat _ _).obj R)
    (M : SheafOfModules.{u} S) (U : Opens Y) :
    ∃ (G : SheafOfModules.{u} (S.over U) ⥤
        SheafOfModules.{u} (R.over ((Opens.map f).obj U)))
      (_ : PreservesColimitsOfSize.{u, u} G),
      Nonempty (SheafOfModules.unit (R.over ((Opens.map f).obj U)) ≅
        G.obj (SheafOfModules.unit (S.over U))) ∧
      Nonempty (G.obj (M.over U) ≅
        ((SheafOfModules.pullback φ).obj M).over ((Opens.map f).obj U)) := by
  let F := Opens.map f
  have : PreservesFiniteLimits F := preservesFiniteLimits_of_flat F
  have : F.PreservesOneHypercovers.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) :=
    Functor.PreservesOneHypercovers.of_coverPreserving
      (coverPreserving_opens_map f)
  let φU : S.over U ⟶
      ((Over.post F).sheafPushforwardContinuous RingCat
        ((Opens.grothendieckTopology Y).over U)
        ((Opens.grothendieckTopology X).over (F.obj U))).obj (R.over (F.obj U)) :=
    ((Over.forget U).sheafPushforwardContinuous RingCat _ _).map φ
  let e : Over.star U ⋙ Over.post F ≅ F ⋙ Over.star (F.obj U) :=
    NatIso.ofComponents (fun V ↦ Over.isoMk (PreservesLimitPair.iso F U V))
  have : (Over.star U ⋙ Over.post F).IsContinuous (Opens.grothendieckTopology Y)
      ((Opens.grothendieckTopology X).over (F.obj U)) :=
    Functor.isContinuous_comp _ _ _ ((Opens.grothendieckTopology Y).over U) _
  have : (F ⋙ Over.star (F.obj U)).IsContinuous (Opens.grothendieckTopology Y)
      ((Opens.grothendieckTopology X).over (F.obj U)) :=
    Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology X) _
  let eR :
      SheafOfModules.pushforward (SheafOfModules.pushforwardOver (R := R) (F.obj U)) ⋙
        SheafOfModules.pushforward φ ≅
      SheafOfModules.pushforward φU ⋙
        SheafOfModules.pushforward (SheafOfModules.pushforwardOver (R := S) U) :=
    SheafOfModules.pushforwardComp _ _ ≪≫
      SheafOfModules.pushforwardCongr₂ _ e (by
        ext : 2
        funext V
        show φ.hom.app V ≫ R.obj.map prod.snd.op ≫
          R.obj.map (prodComparison F U V.unop).op =
            S.obj.map prod.snd.op ≫ φ.hom.app _
        rw [← R.obj.map_comp, ← op_comp, prodComparison_snd]
        exact (φ.hom.naturality prod.snd.op).symm) ≪≫
      (SheafOfModules.pushforwardComp _ _).symm
  let eL := ((conjugateIsoEquiv
    ((SheafOfModules.pullbackPushforwardAdjunction φ).comp
      (SheafOfModules.overPushforwardOverAdj (R := R) (F.obj U)))
    ((SheafOfModules.overPushforwardOverAdj (R := S) U).comp
      (SheafOfModules.pullbackPushforwardAdjunction φU))).symm eR)
  exact ⟨SheafOfModules.pullback φU, inferInstance,
    ⟨(asIso (SheafOfModules.pullbackObjUnitToUnit φU)).symm⟩, ⟨eL.app M⟩⟩

/-- A locally free local-generator presentation of `M` pulls back to one of the pullback, indexed
by the same cover, whose generating sections have the same index types. -/
private theorem exists_isLocallyFreeData_pullback {X Y : TopCat.{u}} (f : X ⟶ Y)
    {S : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat _ _).obj R)
    (M : SheafOfModules.{u} S) (q : SheafOfModules.LocalGeneratorsData.{u} M)
    (hq : q.IsLocallyFreeData) :
    ∃ (q' : SheafOfModules.LocalGeneratorsData.{u} ((SheafOfModules.pullback φ).obj M))
      (_ : q'.IsLocallyFreeData) (p : q.I → q'.I), Function.Surjective p ∧
      ∀ k, (∀ y, f y ∈ q.X k → y ∈ q'.X (p k)) ∧
        Cardinal.mk (q'.generators (p k)).I = Cardinal.mk (q.generators k).I := by
  choose G hG eUnit eM using fun k ↦ exists_pullbackRestrictionData f φ M (q.X k)
  let q' : SheafOfModules.LocalGeneratorsData.{u}
      ((SheafOfModules.pullback φ).obj M) :=
    { I := q.I
      X k := (Opens.map f).obj (q.X k)
      coversTop := (Opens.coversTop_iff _ _).2
        (((Opens.coversTop_iff _ _).1 q.coversTop).comap f.hom)
      generators k := ((q.generators k).map (G k) (eUnit k).some).ofEpi (eM k).some.hom }
  refine ⟨q', ?_, id, Function.surjective_id, fun k ↦ ⟨fun y hy ↦ hy, rfl⟩⟩
  constructor
  intro k
  have : IsIso (q.generators k).π := hq.isIso k
  have : PreservesColimitsOfSize.{u, u} (G k) := hG k
  have hcomp : IsIso (((q.generators k).map (G k) (eUnit k).some).π ≫ (eM k).some.hom) :=
    inferInstance
  show IsIso (((q.generators k).map (G k) (eUnit k).some).ofEpi (eM k).some.hom).π
  exact Eq.mpr (congrArg IsIso (SheafOfModules.GeneratingSections.ofEpi_π
    ((q.generators k).map (G k) (eUnit k).some) (eM k).some.hom)) hcomp

/-- Pullback of sheaves of modules preserves being finite locally free of rank `r`. -/
public theorem isFiniteLocallyFreeOfRank_pullback {X Y : TopCat.{u}} (f : X ⟶ Y)
    {S : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat _ _).obj R)
    (M : SheafOfModules.{u} S) (r : ℕ)
    (h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((SheafOfModules.pullback φ).obj M) r := by
  obtain ⟨q, hq, hr⟩ := h.exists_isFiniteLocallyFreeOfRankData
  obtain ⟨q', hq', p, hp, h'⟩ := exists_isLocallyFreeData_pullback f φ M q hq
  constructor
  refine ⟨q', hq', fun j ↦ ?_⟩
  obtain ⟨k, rfl⟩ := hp j
  exact ⟨(Cardinal.eq.1 (h' k).2).some.trans (hr k).some⟩

/-- **A locally free local-generator presentation pulls back to a locally free local-generator
presentation of the pullback.** Above the member containing the image of a point `y` there is a
member containing `y`, and its generating sections have the same index type.

This is the construction inside
`AlgebraicGeometry.Grassmannian.isFiniteLocallyFreeOfRank_pullback` with the data at one index
exposed instead of only the rank conclusion, which is what a *descent* of the rank needs: there
one knows the rank of the pullback and wants it on the base. The transported presentation is
reported at one index, with an equality of cardinals, rather than through an equivalence of the
two index types, because a statement of the second kind forces
`HasWeakSheafify ((Opens.grothendieckTopology Y).over (q.X (e i)))` to be synthesized afresh at
the composite index, which exceeds the elaborator's budget at the import closures that consume
this. -/
public theorem exists_localGeneratorsData_pullback {X Y : TopCat.{u}} (f : X ⟶ Y)
    {S : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat _ _).obj R)
    (M : SheafOfModules.{u} S) (q : SheafOfModules.LocalGeneratorsData.{u} M)
    (hq : q.IsLocallyFreeData) (i : q.I) (y : X) (hy : f y ∈ q.X i) :
    ∃ (q' : SheafOfModules.LocalGeneratorsData.{u} ((SheafOfModules.pullback φ).obj M))
      (_ : q'.IsLocallyFreeData) (j : q'.I),
      y ∈ q'.X j ∧ Cardinal.mk (q'.generators j).I = Cardinal.mk (q.generators i).I := by
  have := exists_isLocallyFreeData_pullback f φ M q hq
  obtain ⟨q', hq', p, -, h'⟩ := this
  refine ⟨q', hq', p i, ?_, ?_⟩
  · exact (h' i).1 y hy
  · exact (h' i).2

end AlgebraicGeometry.Grassmannian

end
