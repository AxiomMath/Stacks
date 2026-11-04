module

public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.CoherentCohomologyConverse
public import StacksFrontier.AlgebraicGeometry.Perfect.TorAmplitudeQuasiCoherentTestsGlobal
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperSupportPerfection
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Comparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedPerfectPseudoCoherentTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BoundedAbove

/-!
# Perfectness on an affine étale chart from a Zariski Tor-vanishing statement

Let `Y` be an algebraic space, `V` a Noetherian affine étale chart of `Y` with scheme `V₀`, and
`K` an object of `D(𝒪_Y)` whose cohomology sheaves are coherent and vanish above `b`.  Suppose
that the étale restriction `K|_V` is `ε^*ω` for an object `ω` of `D_QCoh(𝒪_{V₀})` whose derived
tensor products with the quasi-coherent `𝒪_{V₀}`-modules have no cohomology below `a`.  Then
`K|_V` is perfect.

This is the last step of the proof of Stacks 08IS, read on an affine chart of the base: the
cohomology of `ω` is the restriction of the cohomology of `K` to the chart's scheme, so `ω` is
pseudo-coherent by Stacks 08E8; it has Tor amplitude in `[a, b]` by Stacks 08EA; it is
therefore perfect by Stacks 08CQ; and `ε^*` carries perfect objects to perfect objects
(Stacks 08HG).

## Main results

* `AlgebraicGeometry.Space.isPerfect_etaleModulePullback_chartToSpace_of_tensor`: the statement
  above.
* `AlgebraicGeometry.Space.isPerfect_of_forall_affineChart_tensor`: perfectness of an object of
  `D(𝒪_X)` on a locally Noetherian algebraic space from the same Zariski Tor-vanishing on every
  affine étale chart.

## References

* [Stacks Project, Tag 08IS](https://stacks.math.columbia.edu/tag/08IS)
* [Stacks Project, Tag 08EA](https://stacks.math.columbia.edu/tag/08EA)
* [Stacks Project, Tag 08E8](https://stacks.math.columbia.edu/tag/08E8)
* [Stacks Project, Tag 08CQ](https://stacks.math.columbia.edu/tag/08CQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] SmallEtale.preservesFiniteLimits_associatedModule

/-- The cohomology of a Zariski model `ω` of a chart restriction `E|_V`, read through `ε^*`, is
the chart restriction of the cohomology of `E`: `ε^*Hⁱ(ω) ≅ Hⁱ(E)|_V`. -/
def representedAssociatedModuleHomologyIso (V : SmallEtale B S hS X.1)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (ω : DerivedCategory
      ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj V)).Modules)
    (eω : (representedDerivedAssociatedModule B S hS ((SmallEtale.toOver B S hS X.1).obj V)).obj ω ≅
      (etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X V)
        (isEtale_chartToSpace B S hS X V)).mapDerivedCategory.obj E) (i : ℤ) :
    (representedAssociatedModule B S hS ((SmallEtale.toOver B S hS X.1).obj V)
        (isAlgebraicSpace_yoneda B S hS ((SmallEtale.toOver B S hS X.1).obj V))).obj
        ((DerivedCategory.homologyFunctor _ i).obj ω) ≅
      (etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X V)
        (isEtale_chartToSpace B S hS X V)).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E) := by
  let T := (SmallEtale.toOver B S hS X.1).obj V
  let F := etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X V)
    (isEtale_chartToSpace B S hS X V)
  let G := representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)
  exact ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso G i).app ω).symm ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso eω ≪≫
      (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso F i).app E

/-- **The cohomology of a Zariski model of a chart restriction is the chart restriction of the
cohomology.**  If `ε^*ω ≅ E|_V` on the small étale site of the algebraic space represented by an
étale chart `V`, then `Hⁱ(ω)` is the restriction of `Hⁱ(E)` to the scheme of the chart. -/
def homologyIsoChartSchemeModule (V : SmallEtale B S hS X.1)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hqc : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj
        E).IsQuasicoherentOnSite)
    (ω : DerivedCategory
      ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj V)).Modules)
    (hωqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj ω).IsQuasicoherent)
    (eω : (representedDerivedAssociatedModule B S hS ((SmallEtale.toOver B S hS X.1).obj V)).obj ω ≅
      (etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X V)
        (isEtale_chartToSpace B S hS X V)).mapDerivedCategory.obj E) (i : ℤ) :
    (DerivedCategory.homologyFunctor _ i).obj ω ≅
      chartSchemeModule B S hS X
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E) (hqc i) V :=
  chartSchemeIsoOfRepresentedAssociatedModuleIso B S hS X V _ _ (hωqc i)
      (representedAssociatedModuleHomologyIso B S hS X V E ω eω i) ≪≫
    restrictToChartSchemeIsoChartSchemeModule B S hS X _ (hqc i) V

/-- **Perfectness of a chart restriction from a Zariski Tor-vanishing statement.**  Let `V` be a
Noetherian affine étale chart of `X` with scheme `V₀`, and let `E` be an object of `D(𝒪_X)` with
coherent cohomology sheaves vanishing above `b`.  If `E|_V ≅ ε^*ω` for an object `ω` of
`D_QCoh(𝒪_{V₀})` such that `Hⁱ(ω ⊗^L_{𝒪_{V₀}} 𝓕) = 0` for `i < a` and every quasi-coherent
`𝒪_{V₀}`-module `𝓕`, then `E|_V` is perfect. -/
theorem isPerfect_etaleModulePullback_chartToSpace_of_tensor (V : SmallEtale B S hS X.1)
    (hV : IsNoetherianAffineChart B S hS X.1 V)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hcoh : ∀ i : ℤ,
      IsCoherent B S hS X.1 X.2 ((DerivedCategory.homologyFunctor _ i).obj E))
    (a b : ℤ) (hb : ∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj E))
    (ω : DerivedCategory
      ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj V)).Modules)
    (hωqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj ω).IsQuasicoherent)
    (eω : (representedDerivedAssociatedModule B S hS ((SmallEtale.toOver B S hS X.1).obj V)).obj ω ≅
      (etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X V)
        (isEtale_chartToSpace B S hS X V)).mapDerivedCategory.obj E)
    (hω : ∀ F : ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj V)).Modules,
      F.IsQuasicoherent → ∀ i : ℤ, i < a →
        IsZero ((DerivedCategory.homologyFunctor _ i).obj
          (((Stacks.Cohomology.TorAmplitude.derTensor
            ((BigFppfOver.toScheme B S hS).obj
              ((SmallEtale.toOver B S hS X.1).obj V)).toRingedSpace).tensor.obj ω).obj
            ((DerivedCategory.singleFunctor _ 0).obj F)))) :
    (smallEtaleRingedSite B S hS (chartSpace B S hS X V).1 (chartSpace B S hS X V).2).IsPerfect
      ((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X V)
        (isEtale_chartToSpace B S hS X V)).mapDerivedCategory.obj E) := by
  let T := (SmallEtale.toOver B S hS X.1).obj V
  let X₀ := (BigFppfOver.toScheme B S hS).obj T
  have hqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj
      E).IsQuasicoherentOnSite := fun i => (hcoh i).toIsQuasicoherentOnSite
  have : _root_.AlgebraicGeometry.IsNoetherian X₀ :=
    isNoetherian_chartScheme_of_isNoetherianAffineChart B S hS X V hV
  have : IsAffine X₀ := hV.1
  have hN := homologyIsoChartSchemeModule B S hS X V E hqc ω hωqc eω
  have := etaleModulePullback_additive B S hS (chartToSpace B S hS X V)
    (isEtale_chartToSpace B S hS X V)
  have hωb : ∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj ω) :=
    fun i hi => isZero_of_isZero_representedAssociatedModule B S hS T
      (isAlgebraicSpace_yoneda B S hS T) _ (hωqc i)
      ((Functor.map_isZero (etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X V)
        (isEtale_chartToSpace B S hS X V)) (hb i hi)).of_iso
          (representedAssociatedModuleHomologyIso B S hS X V E ω eω i))
  have hpc : RingedSpace.IsPseudoCoherent (X := X₀.toRingedSpace) ω :=
    (isPseudoCoherent_iff_boundedAbove_coherent_homology X₀ ⟨ω, hωqc⟩).2
      ⟨⟨b, hωb⟩, fun i => Stacks.AlgebraicGeometry.IrreducibleDevissage.isCoherent_of_iso' (hN i)
        (isCoherent_chartSchemeModule B S hS X _ (hcoh i) V hV)⟩
  have hLE : ω.IsLE b := (DerivedCategory.isLE_iff _ b).2 hωb
  have htor : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X₀.toRingedSpace ω a b := by
    refine hasTorAmplitude_of_hasTorAmplitudeOnQuasicoherent ω a b hωqc fun F hF i hi => ?_
    simp only [Set.mem_Icc, not_and_or, not_le] at hi
    rcases hi with hi | hi
    · exact hω F hF i hi
    · have := @Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProduct _ _ _
        X₀.toRingedSpace.sheaf _ _ _ _ _ _
        (Stacks.Cohomology.TorAmplitude.derTensor X₀.toRingedSpace) ω
        ((DerivedCategory.singleFunctor _ 0).obj F) b 0 hLE
        (inferInstance : ((DerivedCategory.singleFunctor
          (StrictlyPerfect.OXMod X₀.toRingedSpace) 0).obj F).IsLE 0)
      exact (DerivedCategory.isLE_iff _ (b + 0)).1 this i (by omega)
  have hP : RingedSpace.IsPerfect (X := X₀.toRingedSpace) ω :=
    Stacks.Cohomology.ProperSupportPerfection.isPerfect_of_isPseudoCoherent_of_hasFiniteTorDimension
      ω hpc ⟨a, b, htor⟩
  obtain ⟨K, hK, ⟨e⟩⟩ := isPerfect_representedDerivedAssociatedModule B S hS T ω hP
  exact ⟨K, hK, ⟨e ≪≫ eω⟩⟩

/-- **Perfectness on a locally Noetherian algebraic space from Zariski Tor-vanishing on the
affine charts.**  Let `E` be an object of `D(𝒪_X)` with coherent cohomology sheaves vanishing
above `b`.  Suppose that for every affine étale chart `V` of `X` there is an integer `a` such
that every Zariski model `ω` of `E|_V` on the scheme `V₀` of the chart — every object of
`D_QCoh(𝒪_{V₀})` with `ε^*ω ≅ E|_V` — satisfies `Hⁱ(ω ⊗^L 𝓕) = 0` for `i < a` and every
quasi-coherent `𝒪_{V₀}`-module `𝓕`.  Then `E` is perfect. -/
theorem isPerfect_of_forall_affineChart_tensor
    (hN : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hcoh : ∀ i : ℤ,
      IsCoherent B S hS X.1 X.2 ((DerivedCategory.homologyFunctor _ i).obj E))
    (b : ℤ) (hb : ∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj E))
    (h : ∀ V : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 V → ∃ a : ℤ,
      ∀ ω : DerivedCategory
        ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj V)).Modules,
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj ω).IsQuasicoherent) →
      Nonempty ((representedDerivedAssociatedModule B S hS
        ((SmallEtale.toOver B S hS X.1).obj V)).obj ω ≅
          (etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X V)
            (isEtale_chartToSpace B S hS X V)).mapDerivedCategory.obj E) →
      ∀ F : ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj V)).Modules,
        F.IsQuasicoherent → ∀ i : ℤ, i < a →
          IsZero ((DerivedCategory.homologyFunctor _ i).obj
            (((Stacks.Cohomology.TorAmplitude.derTensor
              ((BigFppfOver.toScheme B S hS).obj
                ((SmallEtale.toOver B S hS X.1).obj V)).toRingedSpace).tensor.obj ω).obj
              ((DerivedCategory.singleFunctor _ 0).obj F)))) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E := by
  have := Fact.mk hN
  refine isPerfect_of_forall_affineChart B S hS X E fun V hV => ?_
  have hV' := isNoetherianAffineChart_of_isAffine B S hS X.1 X.2 hV
  obtain ⟨a, ha⟩ := h V hV
  let T := (SmallEtale.toOver B S hS X.1).obj V
  let F := etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X V)
    (isEtale_chartToSpace B S hS X V)
  have hH : ∀ i : ℤ, (DerivedCategory.homologyFunctor _ i).obj (F.mapDerivedCategory.obj E) ≅
      F.obj ((DerivedCategory.homologyFunctor _ i).obj E) := fun i =>
    (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso F i).app E
  have hM' : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj T)
          (isAlgebraicSpace_yoneda B S hS T)).O))) (F.mapDerivedCategory.obj E) := fun n =>
    SheafOfModules.IsQuasicoherentOnSite.of_iso (hH n).symm
      (isQuasicoherentOnSite_etaleModulePullback_chartToSpace B S hS X _
        (hcoh n).toIsQuasicoherentOnSite V)
  obtain ⟨ω, hωqc, ⟨eω⟩⟩ :=
    exists_representedDerivedAssociatedModule_iso B S hS T (F.mapDerivedCategory.obj E) hM'
  exact isPerfect_etaleModulePullback_chartToSpace_of_tensor B S hS X V hV' E hcoh a b hb ω hωqc
    eω (ha ω hωqc ⟨eω⟩)

end AlgebraicGeometry.Space

end
