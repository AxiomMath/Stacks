module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModelNaiveCotangentHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentHomologyQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsFiniteTypeEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeFromGlobalGenerators
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentClosure
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissage

/-!
# The cohomology sheaves of `NL_{X/Y}` on the model are coherent

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, locally of finite type, with
`X` locally Noetherian.  The naive cotangent complex `NL_{X/Y}` formed on the `Type u` model of
the small étale site of `X` has its cohomology sheaves, carried back to `X`,
`AlgebraicGeometry.Space.modelNaiveCotangentHomology f i`.  This file compares them with the
cohomology sheaves of the naive cotangent complex `NL_{X/Y}` of Stacks 0D0V, whose sections lie
one universe up, and proves that they are coherent.

* In every degree, raising the universe of the sections of the `i`-th cohomology sheaf on the
  model gives the `i`-th cohomology sheaf of `NL_{X/Y}`
  (`AlgebraicGeometry.Space.spaceULiftModelNaiveCotangentHomologyIso`).
* In degree `0` it is the sheaf of differentials `Ω_{X/Y}`
  (`AlgebraicGeometry.Space.modelNaiveCotangentHomologyZeroIso`), which is quasi-coherent
  (Stacks 04CV) and of finite type (Stacks 05ZE), hence coherent on the locally Noetherian `X`
  (Stacks 07UB).

## Main results

* `AlgebraicGeometry.Space.spaceULiftModelNaiveCotangentHomologyIso`
* `AlgebraicGeometry.Space.modelNaiveCotangentHomologyZeroIso`
* `AlgebraicGeometry.Space.isCoherent_modelNaiveCotangentHomology_zero`

## References

* [Stacks Project, Tag 0D0Y](https://stacks.math.columbia.edu/tag/0D0Y)
* [Stacks Project, Tag 0D0Z](https://stacks.math.columbia.edu/tag/0D0Z)
* [Stacks Project, Tag 05ZE](https://stacks.math.columbia.edu/tag/05ZE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}
  (f : X ⟶ Y)

/-! ### The two universes of the cohomology sheaves -/

/-- **Raising the universe of the sections of the cohomology sheaves of `NL_{X/Y}` on the model
gives the cohomology sheaves of `NL_{X/Y}`.** -/
def spaceULiftModelNaiveCotangentHomologyIso (i : ℤ) :
    (spaceULift B S hS X).obj (modelNaiveCotangentHomology B S hS f i) ≅
      (naiveCotangentComplex B S hS f).homology i :=
  let E' := smallEtaleModelModulesEquivULift B S hS X
  let U := modelULift B S hS X
  spaceULiftModelIso B S hS X _ ≪≫
    E'.inverse.mapIso
      (((StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso U
        (ComplexShape.up ℤ) i).app (modelNaiveCotangentComplex B S hS f)).symm ≪≫
      HomologicalComplex.homologyMapIso (restrictedNaiveCotangentComplexIso B S hS f).symm i ≪≫
      (StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso E'.functor
        (ComplexShape.up ℤ) i).app (naiveCotangentComplex B S hS f)) ≪≫
    E'.unitIso.symm.app _

/-! ### Degree zero -/

/-- **The degree `0` cohomology sheaf of `NL_{X/Y}` on the model is `Ω_{X/Y}`**: raising the
universe of its sections gives the degree `0` cohomology sheaf of `NL_{X/Y}`, which is the
universe lift of `Ω_{X/Y}` (Stacks 0D0Y), and raising the universe is fully faithful. -/
def modelNaiveCotangentHomologyZeroIso :
    modelNaiveCotangentHomology B S hS f 0 ≅ sheafOfDifferentials B S hS f :=
  (Functor.FullyFaithful.ofFullyFaithful (spaceULift B S hS X)).preimageIso
    (spaceULiftModelNaiveCotangentHomologyIso B S hS f 0 ≪≫
      naiveCotangentComplexHomologyZeroIsoSheafOfDifferentials B S hS f)

/-- **`Ω_{X/Y}` is coherent** for `f` locally of finite type and `X` locally Noetherian: it is
quasi-coherent (Stacks 04CV) and of finite type (Stacks 05ZE), and on a locally Noetherian
algebraic space that is coherence (Stacks 07UB). -/
theorem isCoherent_sheafOfDifferentials (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hX : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V)) :
    IsCoherent B S hS X.1 X.2 (sheafOfDifferentials B S hS f) := by
  have : Fact (HasEtaleLocalProperty B S hS X.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hX⟩
  exact (isCoherent_iff_isQuasicoherentOnSite_and_isFiniteType B S hS X.1 X.2 _).2
    ⟨isQuasicoherentOnSite_sheafOfDifferentials B S hS f,
      Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite _
        (isFiniteTypeOnSite_sheafOfDifferentials_of_isLocallyOfFiniteType_hom B S hS f hf)⟩

/-- **The degree `0` cohomology sheaf of `NL_{X/Y}` on the model is coherent**, for `f` locally of
finite type and `X` locally Noetherian. -/
theorem isCoherent_modelNaiveCotangentHomology_zero (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hX : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V)) :
    IsCoherent B S hS X.1 X.2 (modelNaiveCotangentHomology B S hS f 0) :=
  isCoherent_of_iso B S hS X.2 (modelNaiveCotangentHomologyZeroIso B S hS f).symm
    (isCoherent_sheafOfDifferentials B S hS f hf hX)

end AlgebraicGeometry.Space

end
