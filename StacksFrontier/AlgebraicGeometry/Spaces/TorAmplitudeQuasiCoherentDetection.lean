module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineTorAmplitude
public import StacksFrontier.AlgebraicGeometry.Spaces.TorAmplitudeQuasiCoherentLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.TorAmplitudeQuasiCoherentTests
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.IndependenceOfDerivedTensor
import StacksCore.Tactic.StacksAttribute

/-!
# Tor amplitude on a quasi-separated algebraic space is detected by quasi-coherent modules

For `X` a quasi-separated algebraic space and `E` in `D_QCoh(𝒪_X)`, Stacks 08IL says that `E`
has Tor amplitude in `[a, b]` if and only if `Hⁱ(E ⊗^L_{𝒪_X} ℱ) = 0` for `i ∉ [a, b]` and every
quasi-coherent `𝒪_X`-module `ℱ`.

## Main results

* `AlgebraicGeometry.Space.HasTorAmplitudeOnQuasicoherent.of_derivedTensorProduct`: condition
  (2) does not depend on the derived tensor product it is read against.
* `AlgebraicGeometry.Space.hasTorAmplitude_iff_hasTorAmplitudeOnQuasicoherent_standardModel`:
  **Stacks 08IL** at the standard model of `D(𝒪_X)`.

## Implementation notes

Condition (2) is `AlgebraicGeometry.Space.HasTorAmplitudeOnQuasicoherent`.  The proof of
(2) ⟹ (1) reduces to an affine étale chart `j : U ⟶ X`
(`AlgebraicGeometry.Space.hasTorAmplitude_of_forall_isAffineChart` and
`AlgebraicGeometry.Space.hasTorAmplitudeOnQuasicoherent_chart`, which use that `j` is
quasi-compact and separated) and proves the affine case on the small étale site by the argument
of Stacks 08E9, as
`AlgebraicGeometry.Space.hasTorAmplitude_of_hasTorAmplitudeOnQuasicoherent_representedAffine`.
The hypothesis `a ≤ b` of the source is not used.

## References

* [Stacks Project, Lemma 75.13.8 (Tag 08IL)](https://stacks.math.columbia.edu/tag/08IL)
* [Stacks Project, Tag 08E9](https://stacks.math.columbia.edu/tag/08E9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u d

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck


namespace AlgebraicGeometry.Space

open Stacks.SheafOfModules (DerivedTensorProduct)

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Condition (2) of Stacks 08IL does not depend on the derived tensor product it is read
against. -/
theorem HasTorAmplitudeOnQuasicoherent.of_derivedTensorProduct {X : AlgebraicSpaces B S hS}
    {T : DerivedTensorProduct (smallEtaleRingedSite B S hS X.1 X.2)}
    (T' : DerivedTensorProduct (smallEtaleRingedSite B S hS X.1 X.2))
    {E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)} {a b : ℤ}
    (h : HasTorAmplitudeOnQuasicoherent B S hS X.2 T E a b) :
    HasTorAmplitudeOnQuasicoherent B S hS X.2 T' E a b := fun M hM i hi => by
  obtain ⟨e⟩ := DerivedTensorProduct.nonempty_tensorSingleIso T T' E M
  exact (h M hM i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e.symm)

/-- **Stacks 08IL.**  Let `X` be a quasi-separated algebraic space and `E` an object of
`D_QCoh(𝒪_X)`.  Then `E` has Tor amplitude in `[a, b]` if and only if
`Hⁱ(E ⊗^L_{𝒪_X} ℱ) = 0` for `i ∉ [a, b]` and every quasi-coherent `𝒪_X`-module `ℱ`.

This is the form at the standard model of `D(𝒪_X)`, with no hypothesis on the tensor product of
sheaves.  The derived tensor product is any `T`; Tor amplitude and condition (2) do not depend on
it.  The hypothesis `a ≤ b` of the source is not needed.  For (2) ⟹ (1), Tor amplitude is checked
on the affine étale charts `j : U ⟶ X`; condition (2) passes to `Lj^*E` because `X` is
quasi-separated (`AlgebraicGeometry.Space.hasTorAmplitudeOnQuasicoherent_chart`), `Lj^*E` lies in
`D_QCoh`, and the affine case is
`AlgebraicGeometry.Space.hasTorAmplitude_of_hasTorAmplitudeOnQuasicoherent_representedAffine`. -/
@[stacks 08IL]
theorem hasTorAmplitude_iff_hasTorAmplitudeOnQuasicoherent_standardModel
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (T : DerivedTensorProduct (smallEtaleRingedSite B S hS X.1 X.2))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hE : QcohDerived B S hS X E)
    (a b : ℤ) :
    DerivedTensorProduct.HasTorAmplitude T E a b ↔
      HasTorAmplitudeOnQuasicoherent B S hS X.2 T E a b := by
  refine ⟨hasTorAmplitudeOnQuasicoherent_of_hasTorAmplitude B S hS X.2 T E a b, fun h => ?_⟩
  refine (DerivedTensorProduct.hasTorAmplitude_congr (smallEtaleDerivedTensorProduct B S hS X) T
    E a b).mp ?_
  have h₀ := h.of_derivedTensorProduct (smallEtaleDerivedTensorProduct B S hS X)
  refine hasTorAmplitude_of_forall_isAffineChart B S hS X E a b fun A hA => ?_
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj A)) := hA
  exact hasTorAmplitude_of_hasTorAmplitudeOnQuasicoherent_representedAffine B S hS
    ((SmallEtale.toOver B S hS X.1).obj A) _
    (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ (chartToSpace B S hS X A) E hE) a b
    (hasTorAmplitudeOnQuasicoherent_chart B S hS hZ X hXqs E a b h₀ A hA)

end AlgebraicGeometry.Space

end
