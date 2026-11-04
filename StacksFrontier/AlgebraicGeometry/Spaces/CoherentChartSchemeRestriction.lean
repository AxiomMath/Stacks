module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleSections
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherent
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.Basic

/-!
# Coherence of the chart restriction of a coherent module on an algebraic space

Let `X` be an algebraic space over a scheme `S` in a big fppf site `B`, and let `M` be a
quasi-coherent `𝒪_X`-module. On an étale scheme chart `V` of `X`, `M` restricts to a
quasi-coherent `AlgebraicGeometry.Scheme.Modules` on the chart's scheme,
`AlgebraicGeometry.Space.chartSchemeModule`. Over a Noetherian affine chart this restriction is
coherent if `M` is; this reduces Stacks 07UM on a Noetherian algebraic space to the scheme-level
Stacks 01YB on an affine étale chart.

## Main definitions

* `AlgebraicGeometry.Space.chartFppfObject` is the object of the big fppf site over `S`
  underlying an étale chart of `X`.
* `AlgebraicGeometry.Space.openChartOfComparison` is the étale chart of `X` which a Zariski open
  of the chart's scheme becomes under the two comparison equivalences.

## Main results

* `AlgebraicGeometry.Space.openChartOfComparisonTopIso`: at `W = ⊤` that chart is the given one.
* `AlgebraicGeometry.Space.moduleFinite_sectionsTop_chartSchemeModule`: over an affine chart the
  global sections of the transport form a finite module over the chart's ring.
* `AlgebraicGeometry.Space.isFiniteType_chartSchemeModule` and
  `AlgebraicGeometry.Space.isCoherent_chartSchemeModule`: **over a Noetherian affine chart the
  transport is of finite type, hence coherent.**
* `AlgebraicGeometry.Space.exists_surjective_isNoetherianAffineChart_isCoherent_chartSchemeModule`:
  on a Noetherian algebraic space there is a surjective Noetherian affine chart on which the
  transport is coherent.
* `Stacks.Module.finite_of_surjective_of_smul_eq`: finiteness of a module descends along a
  surjective ring map.
* `Stacks.SheafOfModules.moduleFinite_sections_pushforward`: finiteness of sections passes to a
  pushforward of sheaves of modules along a continuous functor.
* `Stacks.SheafOfModules.moduleFinite_sections_of_iso`: finiteness of sections is invariant under
  isomorphism of sheaves of modules.
* `Stacks.SheafOfModules.bijective_reindexBackSharp_app` and
  `AlgebraicGeometry.SmallEtale.bijective_structureMap_hom_app`: the two comparison maps of
  structure sheaves are bijective.

## Implementation notes

`AlgebraicGeometry.Space.chartSchemeModule` is a chosen preimage under the inverse of
`AlgebraicGeometry.SmallEtale.associatedModuleEquivalence'` (Descent, Proposition 03DX (2) at
`τ = étale`), so it agrees with `AlgebraicGeometry.SmallEtale.restrictModule` only up to the
isomorphism `AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule`, and its sections are
not computed by `rfl`. Finiteness of sections is transported instead along a chain of four
pushforwards by `Stacks.SheafOfModules.moduleFinite_sections_pushforward`, which needs only
surjectivity of the ring maps involved.

The chart attached to `⊤` is isomorphic to the given chart but not definitionally equal to it;
`AlgebraicGeometry.Space.openChartOfComparisonTopIso` is built from terminality of `⊤` in the
small étale site of the chart's scheme and of the identity in the slice at the chart.

## References

* [Stacks Project, Tag 07UM](https://stacks.math.columbia.edu/tag/07UM)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.FiniteDirectImageCoherent

universe u v

namespace Stacks.Module

/-- **Finiteness descends along a surjective ring map.** If the action of `R` on `N` is the
action of `R'` read through a surjective ring map `f : R →+* R'`, then `N` is a finite
`R`-module as soon as it is a finite `R'`-module. -/
theorem finite_of_surjective_of_smul_eq {R R' : Type*} [Ring R] [Ring R'] {N : Type*}
    [AddCommGroup N] [Module R N] [Module R' N] (f : R →+* R')
    (hf : Function.Surjective f) (hsmul : ∀ (r : R) (n : N), r • n = f r • n)
    (hfin : Module.Finite R' N) : Module.Finite R N := by
  obtain ⟨s, hs⟩ := Module.finite_def.1 hfin
  have key : ∀ n : N, n ∈ Submodule.span R' (s : Set N) → n ∈ Submodule.span R (s : Set N) := by
    intro n hn
    induction hn using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul r' x _ hx =>
        obtain ⟨r, rfl⟩ := hf r'
        exact (hsmul r x) ▸ Submodule.smul_mem _ r hx
  exact Module.finite_def.2 ⟨s, eq_top_iff.2 fun n _ => key n (hs ▸ Submodule.mem_top)⟩

end Stacks.Module

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X))

/-- The object of the big fppf site over `S` underlying an étale chart of `X`. -/
noncomputable abbrev chartFppfObject (V : SmallEtale B S hS X.1) : BigFppfOver B S hS :=
  (SmallEtale.toOver B S hS X.1).obj V

/-- The étale chart of `X` which a Zariski open `W` of the chart's scheme becomes under the
comparison equivalences of Stacks 04M0 and of the representable case of Stacks 03ED. -/
noncomputable abbrev openChartOfComparison (V : SmallEtale B S hS X.1)
    (W : (chartScheme V).Opens) : SmallEtale B S hS X.1 :=
  ((SmallEtale.chartLocalizationEquivalence B S hS X.1 V).functor.obj
    ((representedSmallEtaleEquivalence B S hS (chartFppfObject B S hS X V)).inverse.obj
      (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
        (chartScheme V) (chartFppfObject B S hS X V).left.property W))).left

/-- **At the whole chart, the comparison equivalences give back the chart.**  The étale chart of
`X` attached by `AlgebraicGeometry.Space.openChartOfComparison` to the open `⊤` of the chart's
scheme is isomorphic to the chart itself. -/
noncomputable def openChartOfComparisonTopIso (V : SmallEtale B S hS X.1) :
    openChartOfComparison B S hS X V ⊤ ≅ V :=
  (Over.forget V).mapIso
    ((((_root_.AlgebraicGeometry.SmallEtale.isTerminalOpensObjTop (associatedBigEtaleSite B)
        (chartScheme V) (chartFppfObject B S hS X V).left.property).isTerminalObj
          (representedSmallEtaleEquivalence B S hS
            (chartFppfObject B S hS X V)).inverse _).isTerminalObj
          (SmallEtale.chartLocalizationEquivalence B S hS X.1 V).functor _).uniqueUpToIso
      Over.mkIdTerminal)

/-- The scheme of the chart attached to the whole of a chart's scheme is affine as soon as the
chart's scheme is. -/
theorem isAffine_chartScheme_openChartOfComparison_top (V : SmallEtale B S hS X.1)
    (hV : IsAffine (chartScheme V)) :
    IsAffine (chartScheme (openChartOfComparison B S hS X V ⊤)) :=
  have : IsIso (openChartOfComparisonTopIso B S hS X V).hom := Iso.isIso_hom _
  have : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj V) := hV
  IsAffine.of_isIso ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).map
    (openChartOfComparisonTopIso B S hS X V).hom)

end AlgebraicGeometry.Space

namespace Stacks.SheafOfModules

universe w m v₁ v₂ u₁ u₂

open CategoryTheory

/-- **Finiteness of sections passes to a pushforward of sheaves of modules.** The sections over
`A` of the pushforward of `N` along a continuous functor `F` and a morphism of sheaves of rings
`φ` form a finite module as soon as the sections of `N` over `F.obj A` do and `φ` is surjective
at `A`. -/
theorem moduleFinite_sections_pushforward {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
    {S : CategoryTheory.Sheaf J RingCat.{w}} {R : CategoryTheory.Sheaf K RingCat.{w}}
    [F.IsContinuous J K] (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R)
    (N : _root_.SheafOfModules.{m} R) (A : C)
    (hφ : Function.Surjective (φ.hom.app (Opposite.op A)).hom)
    (h : Module.Finite (R.obj.obj (Opposite.op (F.obj A)))
      (N.val.obj (Opposite.op (F.obj A)))) :
    Module.Finite (S.obj.obj (Opposite.op A))
      (((_root_.SheafOfModules.pushforward.{m} φ).obj N).val.obj (Opposite.op A)) :=
  @Stacks.Module.finite_of_surjective_of_smul_eq _ _ _ _ _ _
    (((_root_.SheafOfModules.pushforward.{m} φ).obj N).val.obj (Opposite.op A)).isModule
    (N.val.obj (Opposite.op (F.obj A))).isModule (φ.hom.app (Opposite.op A)).hom hφ
    (fun _ _ => rfl) h

/-- **Finiteness of sections is invariant under isomorphism.** If `F ≅ G` and the sections of
`G` over `A` form a finite module, so do the sections of `F` over `A`. -/
theorem moduleFinite_sections_of_iso {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} {R : CategoryTheory.Sheaf J RingCat.{w}}
    {F G : _root_.SheafOfModules.{m} R} (e : F ≅ G) (A : C)
    (h : Module.Finite (R.obj.obj (Opposite.op A)) (G.val.obj (Opposite.op A))) :
    Module.Finite (R.obj.obj (Opposite.op A)) (F.val.obj (Opposite.op A)) :=
  have e' : F.val.obj (Opposite.op A) ≅ G.val.obj (Opposite.op A) :=
    { hom := e.hom.val.app (Opposite.op A)
      inv := e.inv.val.app (Opposite.op A)
      hom_inv_id := congrArg (fun k : F ⟶ F => k.val.app (Opposite.op A)) e.hom_inv_id
      inv_hom_id := congrArg (fun k : G ⟶ G => k.val.app (Opposite.op A)) e.inv_hom_id }
  have := h
  Module.Finite.equiv e'.toLinearEquiv.symm

variable {C : Type u} [Category.{v} C] {C' : Type u} [Category.{v} C']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}

/-- The structure map of the inverse of an equivalence of ringed sites is bijective at every
object. -/
theorem bijective_reindexBackSharp_app (e : C' ≌ C)
    [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
    (R : CategoryTheory.Sheaf J RingCat.{w}) (A : C) :
    Function.Bijective ((reindexBackSharp (J' := J') e R).hom.app (Opposite.op A)).hom := by
  have : IsIso ((reindexBackSharp (J' := J') e R).hom.app (Opposite.op A)) := by
    show IsIso (R.obj.map (e.counit.app A).op)
    infer_instance
  exact ConcreteCategory.bijective_of_isIso
    ((reindexBackSharp (J' := J') e R).hom.app (Opposite.op A))

/-- The structure map of the inverse of an equivalence of ringed sites is surjective at every
object. -/
theorem surjective_reindexBackSharp_app (e : C' ≌ C)
    [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
    (R : CategoryTheory.Sheaf J RingCat.{w}) (A : C) :
    Function.Surjective ((reindexBackSharp (J' := J') e R).hom.app (Opposite.op A)).hom :=
  (bijective_reindexBackSharp_app e R A).2

end Stacks.SheafOfModules

namespace AlgebraicGeometry.SmallEtale

/-- The comparison of structure sheaves is bijective over every open `U` of `S`. -/
theorem bijective_structureMap_hom_app (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (U : S.Opens) :
    Function.Bijective ((structureMap B S hS).hom.app (Opposite.op U)).hom := by
  have : IsIso ((structureMap B S hS).hom.app (Opposite.op U)) := by
    rw [structureMap_hom_app]
    exact Iso.isIso_hom ((CategoryTheory.forget₂ CommRingCat RingCat.{u}).mapIso
      (Scheme.Opens.topIso U).symm)
  exact ConcreteCategory.bijective_of_isIso ((structureMap B S hS).hom.app (Opposite.op U))

/-- The comparison of structure sheaves is surjective over every open `U` of `S`. -/
theorem surjective_structureMap_hom_app (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (U : S.Opens) :
    Function.Surjective ((structureMap B S hS).hom.app (Opposite.op U)).hom :=
  (bijective_structureMap_hom_app B S hS U).2

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X))

/-- **The global sections of the chart restriction are finite.** For a coherent `𝒪_X`-module and
an affine étale chart, the global sections of the `AlgebraicGeometry.Scheme.Modules` which `M`
becomes on the chart's scheme form a finite module over the global functions of that scheme. -/
theorem moduleFinite_sectionsTop_chartSchemeModule
    (hM : IsCoherent B S hS X.1 X.2 M) (V : SmallEtale B S hS X.1)
    (hV : IsAffine (chartScheme V)) :
    Module.Finite ((chartScheme V).ringCatSheaf.obj.obj (op (⊤ : (chartScheme V).Opens)))
      ((chartSchemeModule B S hS X M hM.toIsQuasicoherentOnSite V).val.obj
        (op (⊤ : (chartScheme V).Opens))) := by
  let T := _root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
    (chartScheme V) (chartFppfObject B S hS X V).left.property ⊤
  let R := (representedSmallEtaleEquivalence B S hS (chartFppfObject B S hS X V)).inverse.obj T
  have h0 := moduleFinite_sections_of_isCoherent B S hS X.1 X.2 M hM
    (isAffine_chartScheme_openChartOfComparison_top B S hS X V hV)
  have h1 := Stacks.SheafOfModules.moduleFinite_sections_pushforward
    (𝟙 ((structureRingSheaf B S hS X).over V)) M
    ((SmallEtale.chartLocalizationEquivalence B S hS X.1 V).functor.obj R)
    (fun x => ⟨x, rfl⟩) h0
  have h2 := @Stacks.SheafOfModules.moduleFinite_sections_pushforward
    (SmallEtale B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V))) inferInstance
    (Over V) inferInstance
    (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
    ((SmallEtale.topology B S hS X.1).over V)
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 V).functor
    (chartStructureRingSheaf B S hS X V) ((structureRingSheaf B S hS X).over V)
    (isContinuous_chartLocalization_chartSpace B S hS X V)
    (𝟙 (chartStructureRingSheaf B S hS X V)) (M.over V)
    R (fun x => ⟨x, rfl⟩) h1
  have h3 := Stacks.SheafOfModules.moduleFinite_sections_pushforward
    (Stacks.SheafOfModules.reindexBackSharp
      (J' := SmallEtale.topology B S hS (yoneda.obj (chartFppfObject B S hS X V)))
      (representedSmallEtaleEquivalence B S hS (chartFppfObject B S hS X V))
      (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X V)))
    (chartSmallEtaleRestriction B S hS X M V)
    T
    (Stacks.SheafOfModules.surjective_reindexBackSharp_app _ _ _) h2
  have h4 := Stacks.SheafOfModules.moduleFinite_sections_pushforward
    (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B) (chartScheme V)
      (chartFppfObject B S hS X V).left.property)
    (chartSchemeEtaleModule B S hS X M hM.toIsQuasicoherentOnSite V)
    (⊤ : (chartScheme V).Opens)
    (_root_.AlgebraicGeometry.SmallEtale.surjective_structureMap_hom_app _ _ _ _) h3
  exact Stacks.SheafOfModules.moduleFinite_sections_of_iso
    (chartSchemeModuleIsoRestrictModule B S hS X M hM.toIsQuasicoherentOnSite V) ⊤ h4

/-- **The chart restriction of a coherent module is of finite type on an affine chart.** -/
theorem isFiniteType_chartSchemeModule (hM : IsCoherent B S hS X.1 X.2 M)
    (V : SmallEtale B S hS X.1) (hV : IsAffine (chartScheme V)) :
    SheafOfModules.IsFiniteType (chartSchemeModule B S hS X M hM.toIsQuasicoherentOnSite V) :=
  have _hq : SheafOfModules.IsQuasicoherent
      (chartSchemeModule B S hS X M hM.toIsQuasicoherentOnSite V) :=
    isQuasicoherent_chartSchemeModule B S hS X M hM.toIsQuasicoherentOnSite V
  Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_of_cover_isFiniteTildeOn _
    (fun _ : PUnit.{u + 1} => (⊤ : (chartScheme V).Opens))
    (TopologicalSpace.IsOpenCover.mk iSup_const)
    (fun _ => isAffineOpen_top _)
    (fun _ => isFiniteTildeOn_of_moduleFinite_sections _ ⟨⊤, isAffineOpen_top _⟩
      (moduleFinite_sectionsTop_chartSchemeModule B S hS X M hM V hV))

/-- **The chart restriction of a coherent module on an algebraic space is coherent over a
Noetherian affine chart.** -/
theorem isCoherent_chartSchemeModule (hM : IsCoherent B S hS X.1 X.2 M)
    (V : SmallEtale B S hS X.1) (hV : IsNoetherianAffineChart B S hS X.1 V) :
    SheafOfModules.IsCoherent (chartSchemeModule B S hS X M hM.toIsQuasicoherentOnSite V) :=
  have haff : IsAffine (chartScheme V) := hV.1
  have hln : IsLocallyNoetherian (chartScheme V) :=
    isLocallyNoetherian_of_affine_cover
      (S := fun _ : Unit => ⟨⊤, isAffineOpen_top (chartScheme V)⟩) (by simp) (fun _ => hV.2)
  have hq : SheafOfModules.IsQuasicoherent
      (chartSchemeModule B S hS X M hM.toIsQuasicoherentOnSite V) :=
    isQuasicoherent_chartSchemeModule B S hS X M hM.toIsQuasicoherentOnSite V
  have hft : SheafOfModules.IsFiniteType
      (chartSchemeModule B S hS X M hM.toIsQuasicoherentOnSite V) :=
    isFiniteType_chartSchemeModule B S hS X M hM V hV.1
  Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType _

/-! ### A surjective Noetherian affine chart -/

/-- **A coherent module on a Noetherian algebraic space is coherent on a surjective Noetherian
affine chart.** There is an étale chart whose underlying scheme is affine with Noetherian ring
of global sections, which is surjective on points, and on which the chart restriction of a
coherent `𝒪_X`-module is a coherent `AlgebraicGeometry.Scheme.Modules`. -/
theorem exists_surjective_isNoetherianAffineChart_isCoherent_chartSchemeModule
    (hZ : B.Contains (⊤_ Scheme.{u})) (hN : IsNoetherian B S hS hZ X.1)
    (hM : IsCoherent B S hS X.1 X.2 M) :
    ∃ V : SmallEtale B S hS X.1, IsNoetherianAffineChart B S hS X.1 V ∧
      Function.Surjective (pointsMap B S hS
          (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V)) V.1.hom) ∧
        SheafOfModules.IsCoherent
          (chartSchemeModule B S hS X M hM.toIsQuasicoherentOnSite V) := by
  obtain ⟨V, hV, -, hsurj⟩ := exists_surjective_isNoetherianAffineChart B S hS hZ X hN
  exact ⟨V, hV, hsurj, isCoherent_chartSchemeModule B S hS X M hM V hV⟩

end AlgebraicGeometry.Space

end
