module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.DerivedSectionsModelComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyBoundary

/-!
# Relative de Rham cohomology as Čech-computable hypercohomology

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space `X` and let
`Ω^•` be the relative de Rham complex, a complex of sheaves of `A`-modules concentrated in
nonnegative degrees. Relative de Rham cohomology `H^n_{dR}` is defined in
`StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.Basic` with the unbounded derived functor of
global sections. The Čech description of hypercohomology, its cup product and its long exact
sequences, `Stacks.Cech.Hypercohomology`, is stated for bounded below complexes with the bounded
below derived functor. The two models agree on bounded below complexes
(`Stacks.Cohomology.DerivedSectionsModels.derivedSectionsFunctorIso`); this file records that
agreement for the de Rham complex, as an isomorphism of modules over the global sections of `A`.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.deRhamComplexPlus`: the relative de Rham complex as a bounded
  below complex of sheaves of `A`-modules.
* `AlgebraicGeometry.SheafOfModules.hypercohomologyIsoDeRhamCohomology`: the hypercohomology of
  that bounded below complex is relative de Rham cohomology.

## References

* [Stacks Project, Tag 0FL6](https://stacks.math.columbia.edu/tag/0FL6)
* [Stacks Project, Tag 08BN](https://stacks.math.columbia.edu/tag/08BN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-- The relative de Rham complex is concentrated in nonnegative degrees. -/
instance isStrictlyGE_deRhamComplexInt : (deRhamComplexInt B D).IsStrictlyGE 0 := by
  change CochainComplex.IsStrictlyGE ((deRhamComplex B D).extend embeddingUpNat) 0
  infer_instance

/-- **The relative de Rham complex as a bounded below complex** of sheaves of `A`-modules: it is
concentrated in nonnegative degrees. -/
def deRhamComplexPlus : CochainComplex.Plus (_root_.SheafOfModules.{u} (ringSheaf A)) :=
  ⟨deRhamComplexInt B D, 0, isStrictlyGE_deRhamComplexInt B D⟩

/-- The underlying complex of `deRhamComplexPlus B D` is concentrated in nonnegative degrees. -/
instance isStrictlyGE_deRhamComplexPlus : (deRhamComplexPlus B D).obj.IsStrictlyGE 0 :=
  isStrictlyGE_deRhamComplexInt B D

/-- The structure sheaf of the ringed space attached to the base ring sheaf is that ring sheaf,
read as a sheaf of rings. -/
theorem structureSheafRing_baseRingedSpace :
    structureSheafRing (baseRingedSpace A) = ringSheaf A :=
  rfl

/-- **Relative de Rham cohomology is the hypercohomology of the bounded below de Rham complex**,
as modules over the global sections of the base ring sheaf `A`. -/
def hypercohomologyIsoDeRhamCohomology (n : ℤ) :
    Stacks.Cech.Hypercohomology.hypercohomology A (deRhamComplexPlus B D) n ≅
      deRhamCohomology B D n :=
  (DerivedCategory.homologyFunctor _ n).mapIso
    ((Stacks.Cohomology.DerivedSectionsModels.derivedSectionsFunctorIso
      (baseRingedSpace A) ⊤).app
        (show CochainComplex.Plus (_root_.SheafOfModules.{u}
          (structureSheafRing (baseRingedSpace A))) from deRhamComplexPlus (X := X) B D))

end AlgebraicGeometry.SheafOfModules

end
