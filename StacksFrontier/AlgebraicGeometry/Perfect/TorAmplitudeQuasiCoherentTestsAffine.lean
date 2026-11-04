module

public import StacksFrontier.AlgebraicGeometry.DerivedTildeTorAmplitude
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
public import StacksFrontier.AlgebraicGeometry.Perfect.TorAmplitudeQuasiCoherentTests
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 08EA on an affine scheme

Let `X = Spec R` and let `E` be an object of `D_QCoh(𝒪_X)`. Then `E` has Tor amplitude in
`[a, b]` — a condition on the derived tensor product of `E` with *every* `𝒪_X`-module — as soon
as the derived tensor product with every *quasi-coherent* `𝒪_X`-module has no cohomology
outside `[a, b]`. This is the converse half of Stacks 08EA on an affine scheme.

## Main results

* `AlgebraicGeometry.hasTorAmplitude_of_hasTorAmplitudeOnQuasicoherent_spec`: Stacks 08EA,
  (2) implies (1), on an affine scheme.
* `AlgebraicGeometry.hasTorAmplitude_iff_hasTorAmplitudeOnQuasicoherent_spec`: the equivalence of
  the two conditions of Stacks 08EA on an affine scheme.

## References

* [Stacks Project, Lemma 36.10.3 (Tag 08EA)](https://stacks.math.columbia.edu/tag/08EA)
* [Stacks Project, Lemma 36.10.2 (Tag 08E9)](https://stacks.math.columbia.edu/tag/08E9)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Definition 20.48.1 (Tag 08CG)](https://stacks.math.columbia.edu/tag/08CG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open StrictlyPerfect

namespace AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {R : CommRingCat.{u}}

/-- **Stacks 08EA on an affine scheme, (2) implies (1), with the Stacks 06Z0 datum in
binders.** If `E` is isomorphic to the derived sheafification of an object `M` of `D(R)` and
satisfies condition (2), then it has Tor amplitude in `[a, b]`. -/
private theorem hasTorAmplitude_of_tests_of_iso_tilde
    (E : DerivedCategory (OXMod.{u, u} (Spec R).toRingedSpace)) (a b : ℤ)
    (M : DerivedCategory (ModuleCat.{u} R))
    (e : (tilde.functor R).mapDerivedCategory.obj M ≅ E)
    (h : Stacks.Cohomology.TorAmplitude.HasTorAmplitudeOnQuasicoherent
      (Spec R).toRingedSpace E a b) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude (Spec R).toRingedSpace E a b := by
  have hM : Stacks.Cohomology.TorAmplitude.HasTorAmplitude (Spec R).toRingedSpace
      ((tilde.functor R).mapDerivedCategory.obj M) a b := by
    refine (hasTorAmplitude_tilde_iff_tilde_tests M a b).2 fun N i hi => ?_
    refine IsZero.of_iso (h (tilde N) ?_ i hi)
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} (Spec R).toRingedSpace) i).mapIso
        (((Stacks.Cohomology.TorAmplitude.derTensor (Spec R).toRingedSpace).tensor.mapIso
          e).app _))
    exact inferInstanceAs
      (SheafOfModules.IsQuasicoherent (R := (Spec R).ringCatSheaf) (tilde N))
  intro F i hi
  exact IsZero.of_iso (hM F i hi)
    ((DerivedCategory.homologyFunctor (OXMod.{u, u} (Spec R).toRingedSpace) i).mapIso
      (((Stacks.Cohomology.TorAmplitude.derTensor (Spec R).toRingedSpace).tensor.mapIso
        e.symm).app _))

/-- **Stacks 08EA on an affine scheme, (2) implies (1).** An object of `D(𝒪_{Spec R})` whose
cohomology sheaves are quasi-coherent, and whose derived tensor product with every
quasi-coherent `𝒪_{Spec R}`-module has no cohomology outside `[a, b]`, has Tor amplitude in
`[a, b]`. -/
theorem hasTorAmplitude_of_hasTorAmplitudeOnQuasicoherent_spec
    (E : DerivedCategory (OXMod.{u, u} (Spec R).toRingedSpace)) (a b : ℤ)
    (hqc : ∀ n : ℤ,
      ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj E).IsQuasicoherent)
    (h : Stacks.Cohomology.TorAmplitude.HasTorAmplitudeOnQuasicoherent
      (Spec R).toRingedSpace E a b) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude (Spec R).toRingedSpace E a b :=
  hasTorAmplitude_of_tests_of_iso_tilde E a b
    (Stacks.AffineTilde.exists_iso_mapDerivedCategory_tilde_of_isQuasicoherent_standard
      E hqc).choose
    (Stacks.AffineTilde.exists_iso_mapDerivedCategory_tilde_of_isQuasicoherent_standard
      E hqc).choose_spec.some h

/-- **Stacks 08EA on an affine scheme.** For an object of `D_QCoh(𝒪_{Spec R})` the two
conditions of Stacks 08EA are equivalent: Tor amplitude in `[a, b]`, and the vanishing of
`H^i(E ⊗^L ℱ)` outside `[a, b]` for every quasi-coherent `ℱ`. -/
theorem hasTorAmplitude_iff_hasTorAmplitudeOnQuasicoherent_spec
    (E : DerivedCategory (OXMod.{u, u} (Spec R).toRingedSpace)) (a b : ℤ)
    (hqc : ∀ n : ℤ,
      ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj E).IsQuasicoherent) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude (Spec R).toRingedSpace E a b ↔
      Stacks.Cohomology.TorAmplitude.HasTorAmplitudeOnQuasicoherent
        (Spec R).toRingedSpace E a b :=
  ⟨Stacks.Cohomology.TorAmplitude.hasTorAmplitudeOnQuasicoherent_of_hasTorAmplitude E a b,
    hasTorAmplitude_of_hasTorAmplitudeOnQuasicoherent_spec E a b hqc⟩

end AlgebraicGeometry

end
