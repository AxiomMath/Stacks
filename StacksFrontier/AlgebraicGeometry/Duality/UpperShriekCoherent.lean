module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.FiniteTilde
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexCoverCriterion
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekStructureSheafCharts
public import StacksFrontier.AlgebraicGeometry.Duality.SeparatedFiniteTypeProper
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.CompactificationMap
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness

/-!
# The upper shriek functor preserves bounded below complexes with coherent cohomology

Let `S` be a Noetherian scheme and `f : X ⟶ Y` a morphism of `FTS S`, with `f^!` computed at any
compactification. Then `f^!` maps `D⁺_Coh(𝒪_Y)` into `D⁺_Coh(𝒪_X)`: this is [Stacks, Tag 0AU1].

The source factors `f` on affine charts as a closed immersion into affine space and uses
[Stacks, Tag 0AA1], [Stacks, Tag 0A79] and [Stacks, Tag 0A7J]. Here the same affine input is read
through the chart description of `f^!` ([Stacks, Tag 0BV2]): on affine charts `f^!E` is the
associated sheaf of the algebraic upper shriek of a model of `E`, the model lies in
`D⁺_Coh` of the chart ring, and the algebraic upper shriek preserves `D⁺_Coh`
([Stacks, Tag 0BZK] (1)). Boundedness below of `f^!E` holds for any `E ∈ D⁺_QCoh`
(`Stacks.Duality.isBoundedBelow_upperShriek_obj`).

## Main results

* `Stacks.Duality.finite_homology_of_tildeModel` and
  `Stacks.Duality.isZero_homology_of_tildeModel` — a model over an affine open of a complex with
  cohomology of finite type, resp. vanishing in a degree, has finite, resp. vanishing, cohomology
  in that degree.
* `Stacks.Duality.isCoherent_homology_of_finiteTildeModels` — a complex which near every point is
  the associated sheaf of a complex with finite cohomology has coherent cohomology.
* `Stacks.Duality.derivedCategoryBPlus_upperShriek` — [Stacks, Tag 0AU1].
* `Stacks.Duality.derivedCategoryBBounded_upperShriek` — [Stacks, Tag 0B6U] (d): for `f` perfect,
  `f^!` maps `D^b_Coh` into `D^b_Coh`.

## References

* [Stacks Project, Tag 0AU1](https://stacks.math.columbia.edu/tag/0AU1)
* [Stacks Project, Tag 0BV2](https://stacks.math.columbia.edu/tag/0BV2)
* [Stacks Project, Tag 0BZK](https://stacks.math.columbia.edu/tag/0BZK)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.CoherentTFAE Stacks.AlgebraicGeometry.CoherentOfFiniteType

attribute [local instance 5000] HasDerivedCategory.standard
attribute [local instance 10000] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

universe u w w'

namespace Stacks.Duality

/-! ### The cohomology of a model over an affine open -/

section TildeModel

variable {X : Scheme.{u}} [HasDerivedCategory.{w} X.Modules] {K : DerivedCategory X.Modules}
  {U : X.Opens} {hU : IsAffineOpen U} [HasDerivedCategory.{w'} U.toScheme.Modules]
  {ω : DerivedCategory.{u + 1, u, u + 1} (ModuleCat.{u} Γ(X, U))}

/-- If `K|_U` is the associated sheaf of `ω`, transported to `U`, then `H^i(K)|_U` is the
associated sheaf of `H^i(ω)`, transported to `U`; any model of `D(𝒪_U)` may be used. -/
def homologyRestrictIsoRestrictTilde
    (e : (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
      (tilde.functor Γ(X, U) ⋙
        Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj ω) (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj K).restrict U.ι ≅
      (tilde ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) i).obj ω)).restrict
        hU.isoSpec.hom :=
  ((Dualizing.mapDerivedCategoryHomologyIso
      (Scheme.Modules.restrictFunctor U.ι) i).app K).symm ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso e ≪≫
    (Dualizing.mapDerivedCategoryHomologyIso
      (tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom) i).app ω

/-- The associated sheaf of the cohomology of a model of `K` over `U` is the cohomology of `K`,
restricted to `U` and transported to `Spec Γ(X, U)`. -/
def tildeHomologyIsoOfTildeModel
    (e : (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
      (tilde.functor Γ(X, U) ⋙
        Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj ω) (i : ℤ) :
    tilde ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) i).obj ω) ≅
      (((DerivedCategory.homologyFunctor X.Modules i).obj K).restrict U.ι).restrict
        hU.isoSpec.inv :=
  (Scheme.Modules.restrictFunctorId.app _).symm ≪≫
    ((Scheme.Modules.restrictFunctorCongr (f := 𝟙 _)
      (g := hU.isoSpec.inv ≫ hU.isoSpec.hom) (by simp)).app _) ≪≫
    ((Scheme.Modules.restrictFunctorComp hU.isoSpec.inv hU.isoSpec.hom).app _) ≪≫
    (Scheme.Modules.restrictFunctor hU.isoSpec.inv).mapIso
      (homologyRestrictIsoRestrictTilde e i).symm

/-- **A model of a complex whose cohomology is of finite type has finite cohomology.** If `K|_U`
is the associated sheaf of `ω` and `H^i(K)` is of finite type, then `H^i(ω)` is a finite
`Γ(X, U)`-module ([Stacks, Tag 01PB]). -/
theorem finite_homology_of_tildeModel
    (he : Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
      (tilde.functor Γ(X, U) ⋙
        Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj ω)) (i : ℤ)
    [((DerivedCategory.homologyFunctor X.Modules i).obj K).IsFiniteType] :
    Module.Finite Γ(X, U) ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) i).obj ω) := by
  have : (((DerivedCategory.homologyFunctor X.Modules i).obj K).restrict U.ι).IsFiniteType :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_restrict U.ι _
  have : ((((DerivedCategory.homologyFunctor X.Modules i).obj K).restrict U.ι).restrict
      hU.isoSpec.inv).IsFiniteType :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_restrict hU.isoSpec.inv _
  have : (tilde ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) i).obj ω)).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u} (tildeHomologyIsoOfTildeModel he.some i).symm
  exact (AlgebraicGeometry.tilde_isFiniteType_iff _).mp this

/-- **A model of a complex vanishing in degree `i` vanishes in degree `i`**: `tilde` reflects
zero objects, being faithful. -/
theorem isZero_homology_of_tildeModel
    (he : Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
      (tilde.functor Γ(X, U) ⋙
        Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj ω)) (i : ℤ)
    (hz : IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj K)) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) i).obj ω) := by
  have h : IsZero ((tilde.functor Γ(X, U)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) i).obj ω)) :=
    IsZero.of_iso ((Scheme.Modules.restrictFunctor hU.isoSpec.inv).map_isZero
      ((Scheme.Modules.restrictFunctor U.ι).map_isZero hz)) (tildeHomologyIsoOfTildeModel he.some i)
  exact (IsZero.iff_id_eq_zero _).mpr
    ((tilde.functor Γ(X, U)).map_injective (h.eq_of_src _ _))

end TildeModel

/-! ### Globalisation -/

/-- **The cohomology sheaves of a complex with finite tilde models are coherent.** If around
every point `K` is, on an affine open, the associated sheaf of a complex with finite cohomology,
then the cohomology sheaves of `K` are coherent ([Stacks, Tag 01XZ]). -/
theorem isCoherent_homology_of_finiteTildeModels {X : Scheme.{u}} [IsLocallyNoetherian X]
    [HasDerivedCategory.{w} X.Modules] {K : DerivedCategory X.Modules}
    (h : ∀ x : X, ∃ (U : X.Opens) (hU : IsAffineOpen U), x ∈ U ∧
      ∃ ω : DerivedCategory.{u + 1, u, u + 1} (ModuleCat.{u} Γ(X, U)),
        (∀ i : ℤ, Module.Finite Γ(X, U)
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) i).obj ω)) ∧
        Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
          (tilde.functor Γ(X, U) ⋙
            Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj ω))
    (i : ℤ) :
    _root_.SheafOfModules.IsCoherent ((DerivedCategory.homologyFunctor X.Modules i).obj K) := by
  choose U hU hxU ω hω he using h
  set F := (DerivedCategory.homologyFunctor X.Modules i).obj K
  have hcov : IsOpenCover U := by
    refine SetLike.ext fun x => ⟨fun _ => trivial, fun _ => ?_⟩
    simpa only [Opens.mem_iSup] using ⟨x, hxU x⟩
  have hfin : ∀ x : X, IsFiniteTildeOn F (U x) (hU x) := fun x =>
    isFiniteTildeOn_homology_of_tildeModel i (hω x i) (he x)
  have _ : F.IsQuasicoherent := isQuasicoherent_of_cover_isFiniteTildeOn F U hcov hU hfin
  have _ : F.IsFiniteType := isFiniteType_of_cover_isFiniteTildeOn F U hcov hU hfin
  exact isCoherent_of_isQuasicoherent_of_isFiniteType F

/-! ### Tag 0AU1 -/

open ChartCompactification _root_.Stacks.Duality.ProjectiveSpace
  _root_.AlgebraicGeometry.ProjectiveSpace Stacks.AlgebraicGeometry.ProjPolyChart

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The source of an object of `FTS S` is locally Noetherian when `S` is Noetherian. -/
private theorem isLocallyNoetherian_left {S : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S]
    (X : FTS S) : IsLocallyNoetherian X.left :=
  have : IsLocallyNoetherian ((Functor.fromPUnit S).obj X.right) :=
    inferInstanceAs (IsLocallyNoetherian S)
  LocallyOfFiniteType.isLocallyNoetherian X.hom

/-- A point of `X` has affine charts `x ∈ U ≤ f⁻¹V` with `E|_V` the associated sheaf of a complex
`ω` with finite cohomology, when `E` has coherent cohomology. -/
private theorem exists_chart_finiteTildeModel
    {S : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
    (E : quasiCoherentDerivedCategory Y.left)
    (hE : ∀ n : ℤ, _root_.SheafOfModules.IsCoherent
      ((DerivedCategory.homologyFunctor Y.left.Modules n).obj E.obj))
    [IsLocallyNoetherian X.left] [IsLocallyNoetherian Y.left] (x : X.left) :
    ∃ (V : Y.left.Opens) (hV : IsAffineOpen V) (U : X.left.Opens),
      IsAffineOpen U ∧ x ∈ U ∧ U ≤ f.left ⁻¹ᵁ V ∧
      letI := HasDerivedCategory.standard V.toScheme.Modules
      ∃ ω : DerivedCategory.{u + 1, u, u + 1} (ModuleCat.{u} Γ(Y.left, V)),
        Nonempty ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj E.obj ≅
          (tilde.functor Γ(Y.left, V) ⋙
            Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapDerivedCategory.obj ω) ∧
        ∀ n : ℤ, Module.Finite Γ(Y.left, V)
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(Y.left, V)) n).obj ω) := by
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y.left) (x := f.left.base x) (U := ⊤) (by simp)
  obtain ⟨U, hU, hxU, hUV⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X.left) (x := x) (U := f.left ⁻¹ᵁ V) hxV
  have : IsNoetherianRing Γ(Y.left, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let := HasDerivedCategory.standard V.toScheme.Modules
  obtain ⟨ω, hω⟩ := exists_nonempty_iso_tilde_of_isQuasicoherent hV E.property
  refine ⟨V, hV, U, hU, hxU, hUV, ω, hω, fun n => ?_⟩
  have := hE n
  have := (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
    ((DerivedCategory.homologyFunctor Y.left.Modules n).obj E.obj)).2
  exact finite_homology_of_tildeModel hω n

/-- **Stacks Project, Tag 0AU1 (Lemma 48.17.6).** In Situation 48.16.1 let `f : X ⟶ Y` be a
morphism of `FTS S`. Then `f^!` maps `D⁺_Coh(𝒪_Y)` into `D⁺_Coh(𝒪_X)`. Here `f^!` is computed at
an arbitrary compactification `j`. -/
@[stacks 0AU1]
theorem derivedCategoryBPlus_upperShriek
    {S : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
    (j : CompactificationOf (Over.mk f.left)) (E : quasiCoherentDerivedCategory Y.left)
    (hE : DerivedCategoryB.derivedCategoryBPlus
      (fun M : Y.left.Modules ↦ _root_.SheafOfModules.IsCoherent M) E.obj) :
    DerivedCategoryB.derivedCategoryBPlus
      (fun M : X.left.Modules ↦ _root_.SheafOfModules.IsCoherent M)
      ((upperShriek f j).obj E).obj := by
  have hcharts : UpperShriekCharts f j E := upperShriekCharts f j E hE.1
  refine ⟨isBoundedBelow_upperShriek_obj f j E hE.1, fun i => ?_⟩
  refine isCoherent_homology_of_finiteTildeModels (fun x => ?_) i
  obtain ⟨V, hV, U, hU, hxU, hUV, ω, hω, hωfin⟩ := exists_chart_finiteTildeModel f E hE.2 x
  have : IsNoetherianRing Γ(Y.left, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : IsNoetherianRing Γ(X.left, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let := HasDerivedCategory.standard V.toScheme.Modules
  have hωbb : DerivedCategoryB.IsBoundedBelow ω :=
    let ⟨n₀, hn₀⟩ := hE.1
    ⟨n₀, fun n hn => isZero_homology_of_tildeModel hω n (hn₀ n hn)⟩
  obtain ⟨p⟩ := Dualizing.nonempty_polynomialPresentation _ (f.left.finiteType_appLE hV hU hUV)
  exact ⟨U, hU, hxU, p.upperShriekFunctor.{u, u}.obj ω,
    (Dualizing.PolynomialPresentation.upperShriekFunctor_derivedCategoryBPlus p
      ⟨hωbb, hωfin⟩).2, hcharts V hV U hU hUV p ω hω⟩

/-- **Stacks Project, Tag 0B6U (Lemma 48.17.9), part (d).** In Situation 48.16.1 let
`f : X ⟶ Y` be a perfect morphism of `FTS S`. Then `f^!` maps `D^b_Coh(𝒪_Y)` into
`D^b_Coh(𝒪_X)`. Here `f^!` is computed at an arbitrary compactification `j`. -/
@[stacks 0B6U "part (d)"]
theorem derivedCategoryBBounded_upperShriek {S : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S]
    {X Y : FTS S} (f : X ⟶ Y) (j : CompactificationOf (Over.mk f.left)) [Perfect f.left]
    (E : quasiCoherentDerivedCategory Y.left)
    (hE : DerivedCategoryB.derivedCategoryBBounded
      (fun M : Y.left.Modules ↦ _root_.SheafOfModules.IsCoherent M) E.obj) :
    DerivedCategoryB.derivedCategoryBBounded
      (fun M : X.left.Modules ↦ _root_.SheafOfModules.IsCoherent M)
      ((upperShriek f j).obj E).obj := by
  have hYn := isLocallyNoetherian_left Y
  have hXn := isLocallyNoetherian_left X
  have hXc : CompactSpace X.left := by
    have : CompactSpace ((Functor.fromPUnit S).obj X.right) :=
      inferInstanceAs (CompactSpace S)
    exact QuasiCompact.compactSpace_of_compactSpace X.hom
  have hcharts : UpperShriekCharts f j E := upperShriekCharts f j E hE.1.1
  have hmodels : ∀ x : X.left, HasTildeModelAt ((upperShriek f j).obj E).obj x := by
    intro x
    obtain ⟨V, hV, U, hU, hxU, hUV, ω, hω, hωfin⟩ :=
      exists_chart_finiteTildeModel f E hE.2 x
    have : IsNoetherianRing Γ(Y.left, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    have : IsNoetherianRing Γ(X.left, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    let := HasDerivedCategory.standard V.toScheme.Modules
    have hωb : DerivedCategoryB.IsBounded ω := by
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hE.1
      exact ⟨⟨a, fun n hn => isZero_homology_of_tildeModel hω n (ha n hn)⟩,
        ⟨b, fun n hn => isZero_homology_of_tildeModel hω n (hb n hn)⟩⟩
    obtain ⟨p⟩ := Dualizing.nonempty_polynomialPresentation _ (f.left.finiteType_appLE hV hU hUV)
    exact ⟨U, hU, hxU, p.upperShriekFunctor.{u, u}.obj ω,
      Dualizing.upperShriekFunctor_derivedCategoryBBounded_of_perfect.{u, u} p
        (HasRingHomProperty.appLE @Perfect f.left ‹_› ⟨V, hV⟩ ⟨U, hU⟩ hUV) ⟨hωb, hωfin⟩,
      hcharts V hV U hU hUV p ω hω⟩
  exact ⟨isBounded_of_tildeModels hmodels, fun i => isCoherent_homology_of_tildeModels hmodels i⟩

end Stacks.Duality

end
