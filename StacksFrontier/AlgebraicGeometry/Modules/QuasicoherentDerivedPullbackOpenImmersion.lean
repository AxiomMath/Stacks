module

public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Modules.SpecFieldDerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.RelativeMayerVietoris.OpenImmersionPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPullbackRightExact

/-!
# Derived pullback along an open immersion preserves quasi-coherent cohomology

Along an open immersion of schemes `f : X ⟶ Y` degreewise pullback of sheaves of modules is exact,
so the derived pullback `Lf^*` is degreewise pullback and `H^i(Lf^*E) = f^*H^i(E)`; pullback
preserves quasi-coherence (Stacks 01BG). This is part (1) of Stacks 08DW for an open immersion,
read at the standard model of the derived categories.

## Main results

* `AlgebraicGeometry.isQuasicoherent_homology_derivedPullback_of_isOpenImmersion`.

## References

* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- **Derived pullback along an open immersion of schemes preserves quasi-coherence of the
cohomology sheaves.** -/
theorem isQuasicoherent_homology_derivedPullback_of_isOpenImmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f]
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)))
    (hE : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)) n).obj E).IsQuasicoherent)
    (i : ℤ) :
    ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      i).obj ((derivedPullback f.toLRSHom.toShHom).obj E)).IsQuasicoherent := by
  have : SheafedSpace.IsOpenImmersion f.toLRSHom.toShHom :=
    inferInstanceAs (LocallyRingedSpace.IsOpenImmersion f.toLRSHom)
  have : PreservesFiniteLimits (modulePullback f.toLRSHom.toShHom) :=
    (modulePullback f.toLRSHom.toShHom).preservesFiniteLimits_of_preservesHomology
  have : PreservesFiniteColimits (modulePullback f.toLRSHom.toShHom) :=
    preservesFiniteColimits_modulePullback _
  have hq : ((Scheme.Modules.pullback f).obj
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
        i).obj E)).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback f _ (hE i)
  exact (SheafOfModules.isQuasicoherent (structureSheafRing X.toRingedSpace)).prop_of_iso
    (derivedHomologyMapIso (modulePullback f.toLRSHom.toShHom) E i ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso
        ((SpecField.derivedPullbackMapDerivedIso f.toLRSHom.toShHom).app E).symm) hq

end AlgebraicGeometry

end
