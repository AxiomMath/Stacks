module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.KFlatResolvingDatum
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional
public import StacksFrontier.Topology.Sheaves.RingedSpace.FlatModulePullback

/-!
# The derived pullback along a flat morphism is the degreewise pullback

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces.  Stacks 06YJ constructs
`Lf^* : D(𝒪_Y) ⟶ D(𝒪_X)` as the total left derived functor of degreewise pullback, and the
canonical comparison `Lf^*(QM) ⟶ Q(f^*M)` is invertible as soon as `M` is K-flat.  When `f` is
*flat* — flat at every point of `X` in the sense of `AlgebraicGeometry.IsFlat` — degreewise
pullback is exact, hence already derived, and the comparison is invertible at *every* complex.

The comparison then assembles into a natural isomorphism of functors `Lf^* ≅ D(f^*)`, where
`D(f^*)` is `CategoryTheory.Functor.mapDerivedCategory` of the exact functor `f^*`.

## Main definitions

* `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackComparisonIsoOfIsFlat`: the canonical
  comparison `Qh ⋙ Lf^* ⟶ K(f^*) ⋙ Qh`, packaged as a natural isomorphism.
* `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackIsoOfIsFlat`: the isomorphism
  `Lf^*(QM) ≅ Q(f^*M)` at an arbitrary complex `M` of `𝒪_Y`-modules.
* `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackIsoMapDerivedCategory`: the natural
  isomorphism of functors `Lf^* ≅ D(f^*)`.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.quasiIso_mapHomotopyCategory_map_of_isFlat`: a flat
  `f^*` carries a quasi-isomorphism of `K(𝒪_Y)` to a quasi-isomorphism of `K(𝒪_X)`.
* `Stacks.Cohomology.DerivedPullbackTensor.isIso_derivedPullbackComparison_app_of_isFlat`: for a
  flat `f` the canonical comparison of `Lf^*` is invertible at *every* object of `K(𝒪_Y)`, not
  only at the K-flat ones.

## References

* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 06YF](https://stacks.math.columbia.edu/tag/06YF)
* [Stacks Project, Tag 02N3](https://stacks.math.columbia.edu/tag/02N3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace Stacks.Cohomology.DerivedPullbackTensor

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- For a flat morphism `f`, the functor `f^*` carries a quasi-isomorphism of `K(𝒪_Y)` to a
quasi-isomorphism of `K(𝒪_X)`. -/
theorem quasiIso_mapHomotopyCategory_map_of_isFlat (hf : AlgebraicGeometry.IsFlat f)
    {K M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)}
    (s : K ⟶ M)
    (hs : HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y))
      (ComplexShape.up ℤ) s) :
    HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)
      (((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).map s) := by
  have := preservesHomology_modulePullback_of_isFlat f hf
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
    (ComplexShape.up ℤ)).map_surjective s
  have hg : QuasiIso g := (HomotopyCategory.quotient_map_mem_quasiIso_iff g).1 hs
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff
    (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map g)).2
      (HomologicalComplex.quasiIso_map_of_preservesHomology g (modulePullback f))

/-- For a flat morphism the canonical comparison of `Lf^*` is invertible at every object of
`K(𝒪_Y)`, not merely at the K-flat ones. -/
theorem isIso_derivedPullbackComparison_app_of_isFlat (hf : AlgebraicGeometry.IsFlat f)
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) :
    IsIso ((derivedPullbackComparison f).app M) := by
  obtain ⟨N, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
  obtain ⟨P, p, hP, -, hp, -⟩ :=
    Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution Y N
  set s := (HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
    (ComplexShape.up ℤ)).map p
  have hs : HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y))
      (ComplexShape.up ℤ) s :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff p).2 hp
  have h1 : IsIso (DerivedCategory.Qh.map s) :=
    Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
      s hs
  have h1' : IsIso ((DerivedCategory.Qh ⋙ derivedPullback f).map s) :=
    inferInstanceAs (IsIso ((derivedPullback f).map (DerivedCategory.Qh.map s)))
  have h2 : IsIso ((derivedPullbackComparison f).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
        (ComplexShape.up ℤ)).obj P)) :=
    Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat f P hP
  have h3 : IsIso ((pullbackOnHomotopy f).map s) :=
    Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) _
      (quasiIso_mapHomotopyCategory_map_of_isFlat f hf s hs)
  have h4 : IsIso ((DerivedCategory.Qh ⋙ derivedPullback f).map s ≫
      (derivedPullbackComparison f).app
        ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
          (ComplexShape.up ℤ)).obj N)) := by
    rw [(derivedPullbackComparison f).naturality s]
    infer_instance
  exact IsIso.of_isIso_comp_left ((DerivedCategory.Qh ⋙ derivedPullback f).map s) _

/-- For a flat morphism, the canonical comparison `Qh ⋙ Lf^* ⟶ K(f^*) ⋙ Qh` as a natural
isomorphism. -/
def derivedPullbackComparisonIsoOfIsFlat (hf : AlgebraicGeometry.IsFlat f) :
    DerivedCategory.Qh ⋙ derivedPullback f ≅ pullbackOnHomotopy f :=
  haveI := isIso_derivedPullbackComparison_app_of_isFlat f hf
  haveI := NatIso.isIso_of_isIso_app (derivedPullbackComparison f)
  asIso (derivedPullbackComparison f)

/-- **For a flat morphism the derived pullback is computed by the degreewise pullback at every
complex**: `Lf^*(QM) ≅ Q(f^*M)` for an arbitrary complex `M` of `𝒪_Y`-modules. -/
def derivedPullbackIsoOfIsFlat (hf : AlgebraicGeometry.IsFlat f)
    (M : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) :
    (derivedPullback f).obj (DerivedCategory.Q.obj M) ≅
      DerivedCategory.Q.obj
        (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) :=
  (derivedPullback f).mapIso
      ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (structureSheafRing Y))).app M).symm ≪≫
    (@asIso _ _ _ _ ((derivedPullbackComparison f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M))
      (isIso_derivedPullbackComparison_app_of_isFlat f hf _)) ≪≫
    (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X))).app
      (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)

section MapDerivedCategory

variable [PreservesFiniteLimits (modulePullback f)] [PreservesFiniteColimits (modulePullback f)]

/-- For a flat morphism, `Lf^*` is a lifting of `K(f^*) ⋙ Qh` through the localization `Qh`. -/
@[instance_reducible]
def liftingDerivedPullbackOfIsFlat (hf : AlgebraicGeometry.IsFlat f) :
    Localization.Lifting DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
      ((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (derivedPullback f) :=
  ⟨derivedPullbackComparisonIsoOfIsFlat f hf⟩

/-- **For a flat morphism the derived pullback is the functor induced on derived categories by
the exact functor `f^*`**: a natural isomorphism of functors `Lf^* ≅ D(f^*)`. -/
def derivedPullbackIsoMapDerivedCategory (hf : AlgebraicGeometry.IsFlat f) :
    derivedPullback f ≅ (modulePullback f).mapDerivedCategory :=
  haveI := liftingDerivedPullbackOfIsFlat f hf
  Localization.liftNatIso DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
    ((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    ((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (derivedPullback f) ((modulePullback f).mapDerivedCategory) (Iso.refl _)

end MapDerivedCategory

end Stacks.Cohomology.DerivedPullbackTensor

end
