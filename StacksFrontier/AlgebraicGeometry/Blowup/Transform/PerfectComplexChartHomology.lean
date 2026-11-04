module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.PerfectComplexCharts
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.TwoTermResolution
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictTarget
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LocalPerfectness
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.LocalTorAmplitude
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.DerivedPullback

/-!
# Cohomology modules of a perfect complex that are perfect of Tor dimension at most one

The last step of the proof of Stacks 0ESQ, read on affine charts: if on an affine chart the
cohomology module of the chart complex in degree `i` is the cokernel of an injection of finite
projective modules, then the restriction of `H^i(E)` to the chart is perfect of Tor dimension at
most one; and these properties, being local, then hold on the whole scheme.

## Main results

* `AlgebraicGeometry.isPerfect_and_hasTorAmplitude_of_forall_restrict`: perfectness and Tor
  amplitude are local on a scheme.
* `AlgebraicGeometry.hasTwoTermFiniteLocallyFreeResolution_tilde`: the sheaf of a module with a
  two-term finite projective resolution has a two-term finite locally free resolution.
* `AffineChart.isPerfect_and_hasTorAmplitude_restrict_homology`, in the namespace
  `AlgebraicGeometry.ComplexAndDivisorSituation`, is the chart version.

## References

* [Stacks Project, Tag 0ESQ](https://stacks.math.columbia.edu/tag/0ESQ)
* [Stacks Project, Tag 05JM](https://stacks.math.columbia.edu/tag/05JM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect
open Stacks.Cohomology.PerfectComplexes Stacks.Cohomology.TorAmplitude

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry

/-- **Perfectness and Tor amplitude are local on a scheme.** An object of `D(𝒪_Y)` whose
restriction to a neighbourhood of every point is perfect of Tor amplitude in `[a, b]` is perfect
of Tor amplitude in `[a, b]`. -/
theorem isPerfect_and_hasTorAmplitude_of_forall_restrict {Y : Scheme.{u}}
    (K : DerivedCategory Y.Modules) (a b : ℤ)
    (h : ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧
      IsPerfect.{u, u, u + 1} (X := V.toScheme.toRingedSpace)
          ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj K) ∧
        HasTorAmplitude V.toScheme.toRingedSpace
          ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj K) a b) :
    IsPerfect.{u, u, u + 1} (X := Y.toRingedSpace) K ∧ HasTorAmplitude Y.toRingedSpace K a b := by
  choose V hyV hV using h
  have e : ∀ y, (RingedSpace.derivedRestrictModules Y.toRingedSpace (V y)).obj K ≅
      (Scheme.Modules.restrictFunctor (V y).ι).mapDerivedCategory.obj K :=
    fun y => (RingedSpace.derivedRestrictModulesIsoRestrictFunctor Y (V y)).app K
  refine ⟨Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_local_isPerfect
      (X := Y.toRingedSpace) K fun y => ⟨V y, hyV y, ?_⟩, ?_⟩
  · exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
      (X := (V y).toScheme.toRingedSpace) (e y).symm (hV y).1
  · refine hasTorAmplitude_of_iSup_eq_top (X := Y.toRingedSpace) K a b V
      (top_le_iff.mp fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hyV y⟩) fun y => ?_
    exact Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_of_iso.{u, u + 1}
      (hV y).2 (e y)

/-- **A module with a two-term finite projective resolution gives a sheaf with a two-term finite
locally free resolution.** On `Spec R`, the sheaf associated to an `R`-module which is the
cokernel of an injection of finite projective modules is the cokernel of an injection of finite
locally free `𝒪_{Spec R}`-modules: `M ↦ M̃` is exact and carries finite projective modules to
finite locally free ones (Stacks 05JM). -/
theorem hasTwoTermFiniteLocallyFreeResolution_tilde {R : CommRingCat.{u}}
    (T : ShortComplex (ModuleCat.{u} R)) (hT : T.ShortExact)
    [Module.Finite R T.X₁] [Module.Projective R T.X₁]
    [Module.Finite R T.X₂] [Module.Projective R T.X₂] :
    HasTwoTermFiniteLocallyFreeResolution ((tilde.functor R).obj T.X₃) := by
  have hflf : ∀ (P : ModuleCat.{u} R) [Module.Finite R P] [Module.Projective R P],
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := (Spec R).ringCatSheaf)
        ((tilde.functor R).obj P) := by
    intro P _ _
    have : SheafOfModules.IsFiniteLocallyFree.{u, u, u} ((tilde.functor R).obj P) :=
      (Stacks.Modules.tilde_isFiniteLocallyFree_iff_module (R := R) (M := P)).2
        ((Module.isFiniteLocallyFree_iff_finite_projective R P).2 ⟨inferInstance, inferInstance⟩)
    exact isFiniteLocallyFree_of_isFiniteLocallyFreeClass (Y := Spec R) _
  let : PreservesFiniteLimits (tilde.functor R) := AlgebraicGeometry.tilde.preservesFiniteLimits R
  let : PreservesFiniteColimits (tilde.functor R) :=
    Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor R
  exact ⟨T.map (tilde.functor R), hT.map_of_exact (tilde.functor R), hflf T.X₁, hflf T.X₂,
    ⟨Iso.refl _⟩⟩

namespace ComplexAndDivisorSituation

attribute [local instance 100000] modulesHasDerivedCategory

/-- **On an affine chart, a cohomology module of the chart complex with a two-term finite
projective resolution makes the cohomology sheaf perfect of Tor dimension at most one there.**
For an affine chart `C` with domain `U` and a degree `i`, if `H^i` of the chart complex is the
cokernel of an injection of finite projective `Γ(X, U)`-modules, then the restriction to `U` of
the `i`-th cohomology sheaf of the perfect object, placed in degree zero, is perfect of Tor
amplitude in `[-1, 0]`.

On `Spec Γ(X, U)` the associated sheaf has a two-term finite locally free resolution, so the
last step of the proof of Stacks 0ESQ applies there
(`AlgebraicGeometry.isPerfect_and_hasTorAmplitude_of_hasTwoTermFiniteLocallyFreeResolution`);
both properties are carried to `U` along `U ≅ Spec Γ(X, U)`, and the chart identifies the
restricted cohomology sheaf with the sheaf associated to `H^i` of its complex. -/
theorem AffineChart.isPerfect_and_hasTorAmplitude_restrict_homology
    {S : ComplexAndDivisorSituation.{u, u + 1}} (C : AffineChart S) (i : ℤ)
    (T : ShortComplex (ModuleCat.{u} Γ(S.X, C.U))) (hT : T.ShortExact)
    [Module.Finite Γ(S.X, C.U) T.X₁] [Module.Projective Γ(S.X, C.U) T.X₁]
    [Module.Finite Γ(S.X, C.U) T.X₂] [Module.Projective Γ(S.X, C.U) T.X₂]
    (e : T.X₃ ≅ (HomologicalComplex.homologyFunctor (ModuleCat Γ(S.X, C.U))
      (ComplexShape.up ℤ) i).obj C.complex.toCochainComplex) :
    IsPerfect.{u, u, u + 1} (X := C.U.1.toScheme.toRingedSpace)
        ((Scheme.Modules.restrictFunctor C.U.1.ι).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor S.X.Modules 0).obj
            ((@DerivedCategory.homologyFunctor (OXMod S.X.toRingedSpace) _ _ S.hasDerivedCategory
              i).obj
              S.M))) ∧
      HasTorAmplitude C.U.1.toScheme.toRingedSpace
        ((Scheme.Modules.restrictFunctor C.U.1.ι).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor S.X.Modules 0).obj
            ((@DerivedCategory.homologyFunctor (OXMod S.X.toRingedSpace) _ _ S.hasDerivedCategory
              i).obj
              S.M))) (-1) 0 := by
  let R := Γ(S.X, C.U)
  let j := C.U.2.isoSpec.hom
  let N := (tilde.functor R).obj T.X₃
  obtain ⟨hperf, htor⟩ := isPerfect_and_hasTorAmplitude_of_hasTwoTermFiniteLocallyFreeResolution N
    (hasTwoTermFiniteLocallyFreeResolution_tilde T hT)
  let eK : (Scheme.Modules.restrictFunctor C.U.1.ι).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor S.X.Modules 0).obj
          ((@DerivedCategory.homologyFunctor (OXMod S.X.toRingedSpace) _ _ S.hasDerivedCategory
              i).obj
              S.M)) ≅
      (Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (Spec R).Modules 0).obj N) :=
    ((Scheme.Modules.restrictFunctor C.U.1.ι).mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor C.U.1.toScheme.Modules 0).mapIso
        (AffineChart.chartHomologyIso C i ≪≫
          (AffineChart.chartTilde C).mapIso e.symm) ≪≫
      (((Scheme.Modules.restrictFunctor j).mapDerivedCategorySingleFunctor 0).app N).symm
  refine ⟨Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
      (X := C.U.1.toScheme.toRingedSpace) eK.symm
      (ComplexAndDivisorSituation.isPerfect_restrictFunctor_mapDerivedCategory j hperf), ?_⟩
  refine Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_of_iso.{u, u + 1} ?_ eK
  exact Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_of_iso.{u, u + 1}
    (Stacks.Cohomology.TorAmplitude.Pullback.hasTorAmplitude_derivedPullback
      j.toLRSHom.toShHom _ (-1) 0 htor)
    ((Scheme.Modules.derivedRestrictIsoDerivedPullback j).app _)

end ComplexAndDivisorSituation

end AlgebraicGeometry
