module

public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.PullbackFromTheStalkCriterion
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlatAndDerivedPullback.ResolvingDatum
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective

/-!
# Degreewise pullback of quasi-isomorphisms between K-flat complexes

For a morphism of ringed spaces `f : X ⟶ Y`, degreewise pullback along `f` carries a
quasi-isomorphism between K-flat complexes of `𝒪_Y`-modules to a quasi-isomorphism. Together with
`Stacks.SheafOfModules.KFlatPullback.kFlat_modulePullback_unconditional` (Stacks 06YC), this
inhabits `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.PullbackKFlatInput`.

## Main results

* `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.quasiIso_modulePullback_of_kFlat`:
  degreewise pullback carries a quasi-isomorphism between K-flat complexes of `𝒪_Y`-modules to a
  quasi-isomorphism.
* `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.pullbackKFlatInput`: the two facts of
  `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.PullbackKFlatInput` hold.

## References

* [Stacks Project, Tag 06YC](https://stacks.math.columbia.edu/tag/06YC)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect RingedSpaceModuleAdjunction

namespace AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

universe u

/-- **Degreewise pullback carries a quasi-isomorphism between K-flat complexes to a
quasi-isomorphism.** -/
theorem quasiIso_modulePullback_of_kFlat {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    {K L : CochainComplex (Modules Y) ℤ} (s : K ⟶ L) (hs : QuasiIso s)
    (hK : KFlat Y K) (hL : KFlat Y L) :
    QuasiIso (((StacksDraft.KFlat.modulePullback f).mapHomologicalComplex
      (ComplexShape.up ℤ)).map s) := by
  have hC : KFlat Y (CochainComplex.mappingCone s) := kFlat_mappingCone Y s hK hL
  have hCac : (CochainComplex.mappingCone s).Acyclic :=
    CategoryTheory.Functor.acyclic_mappingCone s hs
  have hpull : (((StacksDraft.KFlat.modulePullback f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (CochainComplex.mappingCone s)).Acyclic :=
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.acyclic_pullback_of_kFlat_of_acyclic f
      (CochainComplex.mappingCone s) hC hCac
  exact CategoryTheory.Functor.quasiIso_of_acyclic_mappingCone _ fun i =>
    HomologicalComplex.ExactAt.of_iso (hpull i)
      (CochainComplex.mappingCone.mapHomologicalComplexIso s (StacksDraft.KFlat.modulePullback f))

/-- The two facts of `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.PullbackKFlatInput` hold:
the degreewise pullback of a K-flat complex is K-flat, and degreewise pullback carries a
quasi-isomorphism between K-flat complexes to a quasi-isomorphism. -/
theorem pullbackKFlatInput : PullbackKFlatInput.{u} where
  kFlat_pullback := Stacks.SheafOfModules.KFlatPullback.kFlat_modulePullback_unconditional
  quasiIso_pullback := quasiIso_modulePullback_of_kFlat

end AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

end
