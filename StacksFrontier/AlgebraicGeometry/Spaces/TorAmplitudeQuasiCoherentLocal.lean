module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SingleDegreeFreeLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPushforwardDirectSums
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedEtaleDiagonalSplitEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.TorAmplitudeQuasiCoherentTests
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.DirectSummands

/-!
# Tor amplitude on an algebraic space is local on the affine étale charts

Let `X` be an algebraic space and `E` an object of `D(𝒪_X)`.  This file proves the two
reduction steps of the source's proof of Stacks 08IL:

* Tor amplitude in `[a, b]` holds on `X` as soon as it holds for the derived pullback of `E` to
  every affine étale chart `j : U ⟶ X`: the cohomology sheaves of `E ⊗^L 𝓜` pull back to those
  of `Lj^*E ⊗^L j^*𝓜` (Stacks 07A4, with `j^*` exact), and a module vanishing on every affine
  chart vanishes;
* if `X` is quasi-separated, condition (2) of Stacks 08IL passes from `E` to `Lj^*E`: a
  quasi-coherent `𝒪_U`-module `𝓖` is a retract of `j^*j_*𝓖` (Stacks 0HAP, `j` being separated
  and étale), and `j_*𝓖` is quasi-coherent (Stacks 03M9, `j` being quasi-compact and
  quasi-separated).

## Main results

* `AlgebraicGeometry.Space.etaleTensorHomologyIso`: `Hⁱ(Lf^*E ⊗^L (f^*𝓜)[0]) ≅ f^*Hⁱ(E ⊗^L 𝓜[0])`
  for an étale `f`.
* `AlgebraicGeometry.Space.hasTorAmplitude_of_forall_isAffineChart`: Tor amplitude is local on
  the affine étale charts.
* `AlgebraicGeometry.Space.hasTorAmplitudeOnQuasicoherent_chart`: condition (2) of Stacks 08IL
  passes to the affine étale charts of a quasi-separated algebraic space.

## References

* [Stacks Project, Tag 08IL](https://stacks.math.columbia.edu/tag/08IL)
* [Stacks Project, Tag 0HAP](https://stacks.math.columbia.edu/tag/0HAP)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open Stacks.SheafOfModules (DerivedTensorProduct)

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- For an étale morphism `f : X ⟶ Y`, an object `E` of `D(𝒪_Y)` and an `𝒪_Y`-module `𝓜`, the
cohomology sheaves of `Lf^*E ⊗^L (f^*𝓜)[0]` are the pullbacks of those of `E ⊗^L 𝓜[0]`. -/
def etaleTensorHomologyIso {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) (E : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (M : Modules.{u, u} B S hS Y.1 Y.2) (i : ℤ) :
    (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj
        (((smallEtaleDerivedTensor B S hS X).obj
          ((smallEtaleDerivedModulePullback B S hS f).obj E)).obj
            ((DerivedCategory.singleFunctor _ 0).obj ((modulePullback B S hS f).obj M))) ≅
      (modulePullback B S hS f).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).obj
          (((smallEtaleDerivedTensor B S hS Y).obj E).obj
            ((DerivedCategory.singleFunctor _ 0).obj M))) :=
  (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).mapIso
      (((smallEtaleDerivedTensor B S hS X).obj
          ((smallEtaleDerivedModulePullback B S hS f).obj E)).mapIso
        (smallEtaleDerivedModulePullbackSingleIsoOfIsEtale f hf M 0).symm ≪≫
      ((smallEtaleDerivedPullbackTensorIso f).app
        (E, (DerivedCategory.singleFunctor _ 0).obj M)).symm) ≪≫
    smallEtaleDerivedModulePullbackHomologyIsoOfIsEtale f hf _ i

/-- **Tor amplitude is local on the affine étale charts.**  If for every affine étale chart
`j : U ⟶ X` the derived pullback `Lj^*E` has Tor amplitude in `[a, b]`, then so has `E`. -/
theorem hasTorAmplitude_of_forall_isAffineChart (X : AlgebraicSpaces B S hS)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (a b : ℤ)
    (h : ∀ A : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 A →
      DerivedTensorProduct.HasTorAmplitude
        (smallEtaleDerivedTensorProduct B S hS (chartSpace B S hS X A))
        ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X A)).obj E) a b) :
    DerivedTensorProduct.HasTorAmplitude (smallEtaleDerivedTensorProduct B S hS X) E a b := by
  intro M i hi
  refine isZero_of_forall_isAffineChart B S hS X _ fun A hA => ?_
  have hj := isEtale_chartToSpace B S hS X A
  exact (h A hA ((modulePullback B S hS (chartToSpace B S hS X A)).obj M) i hi).of_iso
    ((modulePullbackIsoEtaleModulePullback B S hS _ hj).symm.app _ ≪≫
      (etaleTensorHomologyIso B S hS (chartToSpace B S hS X A) hj E M i).symm)

/-- **Condition (2) of Stacks 08IL passes to the affine étale charts of a quasi-separated
algebraic space.**  For `j : U ⟶ X` an affine étale chart and `𝓖` a quasi-coherent
`𝒪_U`-module, `𝓖` is a retract of `j^*j_*𝓖` (Stacks 0HAP) and `j_*𝓖` is quasi-coherent
(Stacks 03M9), so the vanishing for `E` and `j_*𝓖` gives the vanishing for `Lj^*E` and `𝓖`. -/
theorem hasTorAmplitudeOnQuasicoherent_chart (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (a b : ℤ)
    (hE : HasTorAmplitudeOnQuasicoherent B S hS X.2 (smallEtaleDerivedTensorProduct B S hS X)
      E a b)
    (A : SmallEtale B S hS X.1) (hA : IsAffineChart B S hS X.1 A) :
    HasTorAmplitudeOnQuasicoherent B S hS (chartSpace B S hS X A).2
      (smallEtaleDerivedTensorProduct B S hS (chartSpace B S hS X A))
      ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X A)).obj E) a b := by
  intro G hG i hi
  set j := chartToSpace B S hS X A
  have hj : IsEtale B S hS j.hom := isEtale_chartToSpace B S hS X A
  have hjsep : IsSeparated B S hS j.hom :=
    isSeparated_of_isEtale_of_isAffine B S hS X.2 _ hA j.hom hj
  have hjqc : IsQuasiCompact B S hS j.hom :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ X.2 hXqs
      (isQuasiCompactSpace_chart B S hS A hA) j.hom
  have : G.IsQuasicoherentOnSite := hG
  have hjG := isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS j hjqc
    (isQuasiSeparated_of_isSeparated B S hS hjsep) G hG
  have hz := (hE _ hjG i hi).of_iso (Iso.refl _)
  have hz' : IsZero ((DerivedCategory.homologyFunctor _ i).obj
      (((smallEtaleDerivedTensor B S hS (chartSpace B S hS X A)).obj
        ((smallEtaleDerivedModulePullback B S hS j).obj E)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((modulePullback B S hS j).obj ((modulePushforward B S hS j).obj G))))) :=
    (Functor.map_isZero (modulePullback B S hS j) hz).of_iso
      (etaleTensorHomologyIso B S hS j hj E _ i)
  let s := counitSplitEpiOfSeparatedEtale B S hS j hj hjsep G
  exact Stacks.Cohomology.TorAmplitude.isZero_obj_of_retract
    (DerivedCategory.singleFunctor (Modules.{u, u} B S hS _ _) 0 ⋙
      (smallEtaleDerivedTensor B S hS (chartSpace B S hS X A)).obj
        ((smallEtaleDerivedModulePullback B S hS j).obj E) ⋙
      DerivedCategory.homologyFunctor (Modules.{u, u} B S hS _ _) i)
    s.section_ ((modulePullbackAdjunction B S hS j).counit.app G) s.id hz'

end AlgebraicGeometry.Space

end
