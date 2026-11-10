module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Topology.OpensMapFinal
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import StacksCore.Tactic.StacksAttribute

/-!
# Pullback preserves finite local freeness of a fixed rank

Let `f : X ⟶ Y` be a continuous map of topological spaces and `φ` a morphism from a sheaf of
rings on `Y` to the direct image of a sheaf of rings on `X`. This file shows that the pullback
along `φ` of a sheaf of modules that is finite locally free of rank `r` is again finite locally
free of rank `r`, with the *same* index types for the local bases.

This is the pullback-rank input of Stacks Tag 0AYW: restricting a finite locally free sheaf to a
one-dimensional component must again be finite locally free of the same rank, or else the
degree on the component cannot even be formed.

## Main results

* `Stacks.AlgebraicGeometry.ComponentDegrees.opensMap_final` and `opensOverPost_final`: the
  functor `Opens.map f` is final, and so is its action on slices. Finality is what makes the
  pullback of the structure sheaf be the structure sheaf (Mathlib's
  `SheafOfModules.pullbackObjUnitToUnit`).
* `Stacks.AlgebraicGeometry.ComponentDegrees.exists_pullbackOver`: over a fixed open `U` of `Y`,
  there is a colimit-preserving functor from sheaves of modules on the slice site over `U` to
  sheaves of modules on the slice site over `f ⁻¹ U` which carries the structure sheaf to the
  structure sheaf and `M.over U` to `((pullback φ).obj M).over (f ⁻¹ U)`.
* `Stacks.AlgebraicGeometry.ComponentDegrees.rankPullbackData`: the pullback of a finite locally
  free sheaf of rank `r` is finite locally free of rank `r`.

## Implementation notes

Mathlib's `SheafOfModules.pullbackObjFreeIso` says that the pullback of a free sheaf is free, but
`LocalGeneratorsData` records generating sections over the *slice* sites `J.over (X i)`, so the
global statement does not suffice: the local data must be transported slice by slice. That is
what `exists_pullbackOver` does, by identifying the pullback along the slice morphism `φU` with
the restriction of the pullback along `φ` — a conjugate-isomorphism argument from the two
composite adjunctions.

`exists_pullbackOver` is isolated in its own section so that
`attribute [local implicit_reducible] CategoryTheory.Functor.sheafPushforwardContinuous` can be
confined to it. The attribute is needed for the compatibility square fed to
`SheafOfModules.pushforwardCongr₂`: without it the two spellings of the source of
`R.obj.map prod.snd.op` are not recognised as equal at `implicit` transparency. Keeping it out of
`rankPullbackData` matters for elaboration cost — with the attribute in scope, the final
`defeq` check that identifies the transported local data with the original times out.

`(SheafOfModules.pushforward φ).IsRightAdjoint` is taken as an instance hypothesis rather than
synthesized: synthesis succeeds but only well past the default `synthInstance` budget. It is a
`Prop`-valued class, so supplying it explicitly at a call site cannot disagree with whatever
instance Mathlib's `Scheme.Modules.pullback` was defined with.

## References

* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Stacks.AlgebraicGeometry.ComponentDegrees

universe u u₁ v

/-- The functor `Opens.map f` between lattices of opens is final: the structured arrow category
over any open has a terminal object, namely the one given by the whole space. -/
alias opensMap_final := Stacks.Topology.final_opensMap

/-- The functor induced by `Opens.map f` on slices over an open `U` is final. -/
theorem opensOverPost_final {X Y : TopCat.{u}} (f : X ⟶ Y) (U : Opens Y) :
    (Over.post (Opens.map f) : Over U ⥤ Over ((Opens.map f).obj U)).Final := by
  let F := Opens.map f
  refine ⟨fun A ↦ ?_⟩
  let T : Over (F.obj U) := (Over.post F).obj (Over.mk (𝟙 U))
  let t : StructuredArrow A (Over.post F) :=
    StructuredArrow.mk (Over.homMk A.hom : A ⟶ T)
  have : ∀ a : StructuredArrow A (Over.post F), Unique (a ⟶ t) := fun a ↦ {
    default := StructuredArrow.homMk (Over.mkIdTerminal.from a.right) (by
      apply (Over.mkIdTerminal (X := F.obj U)).hom_ext)
    uniq := fun m ↦ StructuredArrow.hom_ext _ _ ((Over.mkIdTerminal (X := U)).hom_ext _ _) }
  exact CategoryTheory.isConnected_of_isTerminal _ (IsTerminal.ofUnique t)

section Transparency

attribute [local implicit_reducible] CategoryTheory.Functor.sheafPushforwardContinuous

/-- Over a fixed open `U`, the pullback along the slice morphism `φU` is a colimit-preserving
functor carrying the structure sheaf to the structure sheaf and the restriction `M.over U` to the
restriction of `(pullback φ).obj M` to `f ⁻¹ U`. This is what transports local generating
sections through a pullback. -/
theorem exists_pullbackOver {X Y : TopCat.{u}} (f : X ⟶ Y)
    {S : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat _ _).obj R)
    [(SheafOfModules.pushforward φ).IsRightAdjoint]
    (M : SheafOfModules.{u} S) (U : Opens Y) :
    ∃ (G : SheafOfModules.{u} (S.over U) ⥤
        SheafOfModules.{u} (R.over ((Opens.map f).obj U)))
      (_ : PreservesColimitsOfSize.{u, u} G),
      Nonempty (SheafOfModules.unit (R.over ((Opens.map f).obj U)) ≅
        G.obj (SheafOfModules.unit (S.over U))) ∧
      Nonempty (G.obj (M.over U) ≅
        ((SheafOfModules.pullback φ).obj M).over ((Opens.map f).obj U)) := by
  let F := Opens.map f
  have : F.Final := opensMap_final f
  have : PreservesFiniteLimits F := preservesFiniteLimits_of_flat F
  have : F.PreservesOneHypercovers.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) :=
    Functor.PreservesOneHypercovers.of_coverPreserving (coverPreserving_opens_map f)
  let φU : S.over U ⟶
      ((Over.post F).sheafPushforwardContinuous RingCat
        ((Opens.grothendieckTopology Y).over U)
        ((Opens.grothendieckTopology X).over (F.obj U))).obj (R.over (F.obj U)) :=
    ((Over.forget U).sheafPushforwardContinuous RingCat _ _).map φ
  have : (Over.post F : Over U ⥤ Over (F.obj U)).Final := opensOverPost_final f U
  have : (SheafOfModules.pushforward φU).IsRightAdjoint :=
    (SheafOfModules.pullbackPushforwardAdjunction φU).isRightAdjoint
  let e : Over.star U ⋙ Over.post F ≅ F ⋙ Over.star (F.obj U) :=
    NatIso.ofComponents (fun V ↦ Over.isoMk (Limits.PreservesLimitPair.iso F U V))
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
        change φ.hom.app V ≫ R.obj.map prod.snd.op ≫
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

end Transparency

/-- The pullback of a sheaf of modules that is finite locally free of rank `r` is finite locally
free of rank `r`: the transported local data has the same index types for its bases. -/
theorem rankPullbackData {X Y : TopCat.{u}} (f : X ⟶ Y)
    {S : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat _ _).obj R)
    [(SheafOfModules.pushforward φ).IsRightAdjoint]
    (M : SheafOfModules.{u} S) (r : ℕ)
    (h : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r) :
    _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((SheafOfModules.pullback φ).obj M) r := by
  obtain ⟨q, hq, hrank⟩ := h.exists_isFiniteLocallyFreeOfRankData
  choose G hG eUnit eM using fun i ↦ exists_pullbackOver f φ M (q.X i)
  let q' : SheafOfModules.LocalGeneratorsData.{u, u, u, u}
      ((SheafOfModules.pullback φ).obj M) := {
    I := q.I
    X i := (Opens.map f).obj (q.X i)
    coversTop := (Opens.coversTop_iff _ _).2
      (((Opens.coversTop_iff _ _).1 q.coversTop).comap f.hom)
    generators i := ((q.generators i).map (G i) (eUnit i).some).ofEpi (eM i).some.hom }
  have hfree : q'.IsLocallyFreeData.{u, u, u, u} := by
    constructor
    intro i
    have : IsIso (q.generators i).π := hq.isIso i
    have h : IsIso (((q.generators i).map (G i) (eUnit i).some).π ≫ (eM i).some.hom) :=
      inferInstance
    exact Eq.mpr (congrArg IsIso (SheafOfModules.GeneratingSections.ofEpi_π
      ((q.generators i).map (G i) (eUnit i).some) (eM i).some.hom)) h
  exact { exists_isFiniteLocallyFreeOfRankData := ⟨q', hfree, hrank⟩ }

end Stacks.AlgebraicGeometry.ComponentDegrees
