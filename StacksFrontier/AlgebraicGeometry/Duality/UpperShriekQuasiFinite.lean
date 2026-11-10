module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekFibreDimensionFlat
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekFibreDimensionCharts
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekFibreDimensionFlatCharts
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekRelativePerfectionPerfect
import all StacksFrontier.AlgebraicGeometry.Duality.UpperShriekFibreDimensionFlat

/-!
# `f^!𝒪_Y` for a flat quasi-finite morphism

Let `S` be a Noetherian scheme and let `f : X ⟶ Y` be a flat, locally quasi-finite morphism of
`AlgebraicGeometry.FTS S`. Then `f^!𝒪_Y ≅ ω_{X/Y}[0]` for a coherent `𝒪_X`-module `ω_{X/Y}` flat
over `Y` ([Stacks, Tag 0BV7]). The fibres of `f` are discrete, so by [Stacks, Tag 0BV6] the
complex `f^!𝒪_Y` is concentrated in degree `0` and has Tor amplitude in `[0, 0]` over `Y`; its
cohomology sheaves are coherent by [Stacks, Tag 0B6U].

## Main results

* `Stacks.Duality.topologicalKrullDim_fiber_le_zero_of_locallyQuasiFinite` — the fibres of a
  locally quasi-finite morphism have dimension at most `0`.
* `Stacks.Duality.exists_isCoherent_isFlatOver_iso_single` — **[Stacks, Tag 0BV7]**.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open StacksDraft.TorAmplitude

universe u

namespace Stacks.Duality

/-- The fibres of a locally quasi-finite morphism of schemes have dimension at most `0`: they
are locally Artinian, hence discrete. -/
theorem topologicalKrullDim_fiber_le_zero_of_locallyQuasiFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] (y : Y) :
    topologicalKrullDim (f.fiber y) ≤ ((0 : ℕ) : WithBot ℕ∞) :=
  have : DiscreteTopology (f.fiber y) := IsLocallyArtinian.discreteTopology
  topologicalKrullDim_zero_of_discreteTopology _

section Flat

attribute [local instance 10000] HasDerivedCategory.standard

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : AlgebraicGeometry.FTS S} (f : X ⟶ Y)
  (j : AlgebraicGeometry.CompactificationOf (Over.mk f.left))

/-- **The derived stalk of `f^!𝒪_Y` is flat in degree zero over the base.** For `f` flat and
locally quasi-finite, the derived stalk of `f^!𝒪_Y` at `x`, read over `𝒪_{Y, f x}`, has Tor
amplitude in `[0, 0]`: this is the ring-level [Stacks, Tag 0E9Q] on a chart, the fibres having
dimension `0`. -/
theorem hasTorAmplitudeCanonical_stalk_relativeDualizingComplexObj [Flat f.left]
    [LocallyQuasiFinite f.left] (x : X.left) :
    HasTorAmplitudeCanonical (Y.left.presheaf.stalk (f.left.base x))
      ((ModuleCat.restrictScalars (f.left.stalkMap x).hom).mapDerivedCategory.obj
        ((Stacks.Duality.modulesStalkFunctor x).mapDerivedCategory.obj
          (relativeDualizingComplexObj f j))) 0 0 := by
  obtain ⟨U, hU, V, hV, hUV, hxU, p, he⟩ :=
    isShriekOfStructureSheafOnCharts_of_upperShriekStructureSheafCharts f j
      (upperShriekStructureSheafCharts f j) x
  refine hasTorAmplitudeCanonical_stalk_of_chart f hU hV hUV p _ he _ _ ?_ x hxU
  have : IsNoetherianRing Γ(Y.left, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : IsNoetherianRing Γ(X.left, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let : Algebra Γ(Y.left, V) Γ(X.left, U) := (f.left.appLE V U hUV).hom.toAlgebra
  have : Module.Flat Γ(Y.left, V) Γ(X.left, U) := f.left.flat_appLE hV hU hUV
  have hdim : Algebra.relativeDimension Γ(Y.left, V) Γ(X.left, U) ≤ ((0 : ℕ) : WithBot ℕ∞) := by
    refine iSup_le fun r => ?_
    obtain ⟨w, hw, rfl⟩ := exists_mem_primeIdealOf_eq hU r
    exact (Stacks.Flatness.topologicalKrullDimAt_fiber_eq_relativeDimensionAt
      f.left ⟨V, hV⟩ ⟨U, hU⟩ hUV w hw).symm.trans_le
        ((topologicalKrullDimAt_le_topologicalKrullDim _).trans
          (topologicalKrullDim_fiber_le_zero_of_locallyQuasiFinite _ _))
  exact BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso (Iso.refl _) _ _
    ((hasTorAmplitudeIn_canonicalCertified_iff _ _ _ _).1
      (Dualizing.upperShriekFunctor_hasTorAmplitude_of_relativeDimension_le p 0 hdim))

/-- If an object of `D(𝒪_X)` is a module `ω` in degree `0` and its derived stalk at `x`, read over
`𝒪_{Y, f x}`, has Tor amplitude in `[0, 0]`, then the stalk of `ω` at `x` is flat over
`𝒪_{Y, f x}` ([Stacks, Tag 066F]). -/
theorem flat_modulesStalk_of_hasTorAmplitudeCanonical {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K : DerivedCategory X.Modules} {ω : X.Modules}
    (e : K ≅ (DerivedCategory.singleFunctor X.Modules 0).obj ω) (x : X)
    (ht : HasTorAmplitudeCanonical (Y.presheaf.stalk (f.base x))
      ((ModuleCat.restrictScalars (f.stalkMap x).hom).mapDerivedCategory.obj
        ((Stacks.Duality.modulesStalkFunctor x).mapDerivedCategory.obj K)) 0 0) :
    Module.Flat (Y.presheaf.stalk (f.base x))
      ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
        ((Stacks.Duality.modulesStalkFunctor x).obj ω)) := by
  let F := Stacks.Duality.modulesStalkFunctor x
  let G := ModuleCat.restrictScalars.{u} (f.stalkMap x).hom
  refine ((hasTorDimensionLECanonical_iff_hasFlatRepresentative _ _ 0).2).1 ?_
  refine BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso ?_ 0 0 ht
  exact G.mapDerivedCategory.mapIso (F.mapDerivedCategory.mapIso e ≪≫
      (F.mapDerivedCategorySingleFunctor 0).app ω) ≪≫
    (G.mapDerivedCategorySingleFunctor 0).app (F.obj ω)

/-- A module over `𝒪_X` whose stalk at `x`, read over `𝒪_{Y, f x}` through the stalk functor of
`Stacks.Duality.modulesStalkFunctor`, is flat, is flat over `Y` at `x`: the two module
structures on the stalk agree. -/
theorem isFlatOverAt_of_flat_modulesStalk {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (x : X)
    (hF : Module.Flat (Y.presheaf.stalk (f.base x))
      ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
        ((Stacks.Duality.modulesStalkFunctor x).obj F))) :
    IsFlatOverAt f.toLRSHom.toShHom F x := by
  let : Module (Y.presheaf.stalk (f x)) (F.presheaf.stalk x) :=
    Module.compHom _ (f.stalkMap x).hom
  let e : F.presheaf.stalk x ≃ₗ[Y.presheaf.stalk (f x)]
      ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
        ((Stacks.Duality.modulesStalkFunctor x).obj F)) :=
    { AddEquiv.refl _ with
      map_smul' := by
        intro r m
        let s := (SemilinearStalk.commStalkRingEquiv X.presheaf x).symm ((f.stalkMap x).hom r)
        have hs : SemilinearStalk.commStalkRingEquiv X.presheaf x s = (f.stalkMap x).hom r := by
          simp [s]
        have key := SemilinearStalk.comm_smul_eq X.presheaf x F.val s m
        rwa [hs] at key }
  change Module.Flat (Y.presheaf.stalk (f x)) (F.presheaf.stalk x)
  exact Module.Flat.of_linearEquiv e

end Flat

section QuasiFinite

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : AlgebraicGeometry.FTS S} (f : X ⟶ Y)
  (j : AlgebraicGeometry.CompactificationOf (Over.mk f.left))

/-- **Stacks Project, Tag 0BV7 (Lemma 48.21.6).** In Situation 48.16.1 let `f : X ⟶ Y` be a
morphism of `FTS S`. If `f` is flat and quasi-finite, then `f^!𝒪_Y = ω_{X/Y}[0]` for some
coherent `𝒪_X`-module `ω_{X/Y}` flat over `Y`, for every compactification `j` defining `f^!`.

The fibres are discrete, so by [Stacks, Tag 0BV6] `f^!𝒪_Y` is concentrated in degree `0` and
has Tor amplitude `[0, 0]` over `Y`; its cohomology sheaves are coherent by the chart models. -/
@[stacks 0BV7]
theorem exists_isCoherent_isFlatOver_iso_single [Flat f.left] [LocallyQuasiFinite f.left] :
    ∃ ω : X.left.Modules, _root_.SheafOfModules.IsCoherent ω ∧
      IsFlatOver f.left.toLRSHom.toShHom ω ∧
      Nonempty (relativeDualizingComplexObj f j ≅
        (DerivedCategory.singleFunctor X.left.Modules 0).obj ω) := by
  have := locallyOfFinitePresentation_left f
  have h := upperShriekStructureSheafCharts f j
  set K := relativeDualizingComplexObj f j
  -- `f^!𝒪_Y` is concentrated in degree `0`.
  have hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor X.left.Modules i).obj K) := fun i hi =>
    isZero_homology_upperShriek_derivedStructureSheaf_of_notMem_Icc f j
      (fun x => by
        obtain ⟨U, hU, V, hV, hUV, hxU, -, he⟩ :=
          exists_chart_of_upperShriekStructureSheafCharts f j h x ⊤ trivial
        exact ⟨U, hU, V, hV, hUV, hxU, he⟩)
      0 (fun z => (topologicalKrullDimAt_le_topologicalKrullDim _).trans
        (topologicalKrullDim_fiber_le_zero_of_locallyQuasiFinite _ _)) i
      (by simp only [Set.mem_Icc, CharP.cast_eq_zero, neg_zero]; omega)
  have : K.IsGE 0 := (DerivedCategory.isGE_iff K 0).2 fun i hi => hzero i (by omega)
  have : K.IsLE 0 := (DerivedCategory.isLE_iff K 0).2 fun i hi => hzero i (by omega)
  obtain ⟨ω', ⟨e'⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K 0
  let ω := (DerivedCategory.homologyFunctor X.left.Modules 0).obj K
  let e : K ≅ (DerivedCategory.singleFunctor X.left.Modules 0).obj ω :=
    e' ≪≫ (DerivedCategory.singleFunctor X.left.Modules 0).mapIso
      (((DerivedCategory.singleFunctorCompHomologyFunctorIso X.left.Modules 0).app ω').symm ≪≫
        ((DerivedCategory.homologyFunctor X.left.Modules 0).mapIso e').symm)
  refine ⟨ω, ?_, fun x => ?_, ⟨e⟩⟩
  · -- coherence: the cohomology sheaves have coherent chart models.
    have hmodels : ∀ x : X.left, HasTildeModelAt.{u, u} K x := by
      intro x
      obtain ⟨U, hU, V, hV, hUV, hxU, -, p, he⟩ :=
        exists_chart_of_upperShriekStructureSheafCharts f j h x ⊤ trivial
      exact ⟨U, hU, hxU, _,
        derivedCategoryBBounded_upperShriekFunctor_structureModel_of_perfect f hU hV hUV p, he⟩
    exact isCoherent_homology_of_tildeModels hmodels 0
  · -- flatness: the derived stalk has Tor amplitude in `[0, 0]` over `𝒪_{Y, f x}`.
    exact isFlatOverAt_of_flat_modulesStalk _ _ _
      (flat_modulesStalk_of_hasTorAmplitudeCanonical f.left (K := K)
        ((Stacks.Injectives.grothendieckModelEquiv X.left.Modules).inverse.mapIso e) x
        (hasTorAmplitudeCanonical_stalk_relativeDualizingComplexObj f j x))

end QuasiFinite

end Stacks.Duality

end
