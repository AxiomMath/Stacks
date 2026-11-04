module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Dualizing.Complexes.TensorInvertible
public import StacksFrontier.RingTheory.Dualizing.FiniteMapDualizing
public import StacksFrontier.RingTheory.Dualizing.LocallyShiftedSingle
import all StacksFrontier.RingTheory.Dualizing.Complex
import all StacksFrontier.RingTheory.Dualizing.Complexes.TensorInvertible
import all StacksFrontier.RingTheory.Dualizing.LocallyShiftedSingle

/-!
# Uniqueness and endomorphisms of a dualizing complex

Let `(A, 𝔪, κ)` be a Noetherian local ring. Two dualizing complexes for `A` differ by derived
tensor product with an invertible object ([Stacks, Tag 0A7F]), an invertible object is a shifted
copy of the ring on a principal neighbourhood of every prime ([Stacks, Tag 0FNT]), and over a
local ring one such neighbourhood is already the whole of `Spec(A)`, because the element cutting
it out misses the maximal ideal and is therefore a unit. So two dualizing complexes for `A`
differ by a shift, and the normalization convention of [Stacks, Tag 0A7M] pins that shift to
zero: a normalized dualizing complex is unique up to isomorphism.

Over any Noetherian ring the endomorphism ring of a dualizing complex in the derived category is
the base ring, so its automorphism group is the group of units `Aˣ`. That is the derived reading
of the homothety condition built into `Dualizing.IsDualizingComplex`, which is stated at the
chain level. Together with the uniqueness above, these are the two assertions compared in
[Stacks, Tag 0A83] against the corresponding ones for an injective hull of the residue field,
whose automorphism group is instead the units of the completion.

## Main results

* `Dualizing.exists_iso_single_of_isLocallyShiftedUnit` — over a local ring, an object of the
  derived category that is locally a shifted copy of the ring is globally one.
* `Dualizing.IsNormalizedDualizingComplex.nonempty_iso` — two normalized dualizing complexes over
  a Noetherian local ring are isomorphic.
* `Dualizing.IsDualizingComplex.endAlgEquiv` — the endomorphism ring of a dualizing complex in the
  derived category is the base ring, as an `A`-algebra.
* `Dualizing.IsDualizingComplex.autMulEquivUnits` — hence its automorphism group is `Aˣ`.

## Implementation notes

The collapse of "locally a shifted unit" to "a shift of the ring" is the transport of the local
isomorphism back along the localization away from a unit, which is
`Dualizing.unit_local_shift_iso`; only the choice of the maximal ideal as the prime is added
here.

The shift relating the two complexes is produced by `Dualizing.derivedTensorSingleIso`, which
identifies tensoring with the ring in degree `n` with the shift by `-n`, and the shift is then
forced to be zero by `Dualizing.isNormalizedDualizingComplex_shift_iff_eq`. Both the appeal to
[Stacks, Tag 0A7F] and the invertibility statement are taken in the form
`Dualizing.exists_isLocallyShiftedUnit_iso_derivedTensor`, which already reads Tag 0A7F at the
canonical derived tensor product; that form pins the module universe to the ring's own, so the
statements below are at `ModuleCat.{u} A` rather than at an independent module universe.

The endomorphism ring is computed on a bounded injective representative `I` of the complex, which
is K-injective, so `Dualizing.homologyZeroEndLinearEquiv` identifies the degree-zero cohomology of
`Hom^•(I, I)` with `End_{D(A)}(I)`; the homothety condition makes that cohomology free of rank one
over `A` (`Dualizing.linearEquiv_homology_homComplexR_of_quasiIso_homothety`), and a rank-one free
endomorphism module has bijective structure map. The `A`-linear isomorphism alone would not
suffice — an `A`-algebra linearly isomorphic to `A` need not be `A` — which is why the conclusion
is drawn from bijectivity of `algebraMap A (End ω)` rather than from the linear isomorphism
directly. That step, too, is available only at the ring's own module universe, because the
Hom-complex computation is.

## References

* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
* [Stacks Project, Tag 0A7F](https://stacks.math.columbia.edu/tag/0A7F)
* [Stacks Project, Tag 0A7M](https://stacks.math.columbia.edu/tag/0A7M)
* [Stacks Project, Tag 0A83](https://stacks.math.columbia.edu/tag/0A83)
* [Stacks Project, Tag 0FNT](https://stacks.math.columbia.edu/tag/0FNT)
-/

@[expose] public noncomputable section

open CategoryTheory
open CochainComplex.DerivedTensor

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- **Over a local ring a locally shifted unit is a shift of the ring.** If the derived
localization of `L` away from some element outside each prime is a shifted copy of the localized
ring, then over a local ring `L` itself is a shifted copy of the ring: the element provided at the
maximal ideal is a unit, so the localization away from it changes nothing. -/
public theorem exists_iso_single_of_isLocallyShiftedUnit
    {A : Type u} [CommRing A] [IsLocalRing A]
    (L : DerivedCategory (ModuleCat.{u} A))
    (hL : DerivedCategory.Invertible.IsLocallyShiftedUnit L) :
    ∃ n : ℤ, Nonempty (L ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) n).obj (ModuleCat.of A A)) := by
  obtain ⟨g, hg, n, hshift⟩ :=
    hL (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal.isMaximal A).isPrime
  exact ⟨n, unit_local_shift_iso g (IsLocalRing.notMem_maximalIdeal.mp hg) n L hshift⟩

/-- **A normalized dualizing complex over a Noetherian local ring is unique up to isomorphism.**
Two dualizing complexes differ by derived tensor product with an invertible object
([Stacks, Tag 0A7F]); over a local ring such an object is the ring placed in a single degree
([Stacks, Tag 0FNT]), so the two complexes differ by a shift; and the normalization convention of
[Stacks, Tag 0A7M] admits exactly one normalizing shift, so that shift is zero.

This is the uniqueness half of the comparison made in [Stacks, Tag 0A83], whose other side —
uniqueness of an injective hull of the residue field — is [Stacks, Tag 08Y4]. -/
@[stacks 0A83 "a normalized dualizing complex is unique up to isomorphism; stated at the ring's \
own module universe"]
public theorem IsNormalizedDualizingComplex.nonempty_iso
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {ω ω' : DerivedCategory (ModuleCat.{u} A)}
    (hω : IsNormalizedDualizingComplex.{u, u} ω)
    (hω' : IsNormalizedDualizingComplex.{u, u} ω') :
    Nonempty (ω ≅ ω') := by
  obtain ⟨L, hL, ⟨eTensor⟩⟩ := exists_isLocallyShiftedUnit_iso_derivedTensor hω.1 hω'.1
  obtain ⟨n, ⟨eL⟩⟩ := exists_iso_single_of_isLocallyShiftedUnit L hL
  let eShift : ω' ≅ ω⟦-n⟧ :=
    eTensor ≪≫ ((canonicalDerivedTensorProductFunctor A).obj ω).mapIso eL ≪≫
      derivedTensorSingleIso (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A) ω n
  have ezero : ω⟦(-0 : ℤ)⟧ ≅ ω := by
    rw [neg_zero]
    exact (shiftFunctorZero (DerivedCategory (ModuleCat.{u} A)) ℤ).app ω
  have hzero : IsNormalizedDualizingComplex.{u, u} (ω⟦(-0 : ℤ)⟧) :=
    (isNormalizedDualizingComplex_congr.{u, u} ezero).mpr hω
  have hn : IsNormalizedDualizingComplex.{u, u} (ω⟦-n⟧) :=
    (isNormalizedDualizingComplex_congr.{u, u} eShift).mp hω'
  obtain rfl : n = 0 :=
    (isNormalizedDualizingComplex_shift_iff_eq.{u, u} ω 0 hzero n).mp hn
  exact ⟨(eShift ≪≫ ezero).symm⟩

/-- **Scalars exhaust the endomorphisms of a dualizing complex.** For a dualizing complex `ω` the
structure map `A → End_{D(A)}(ω)` is bijective: on a bounded injective representative `I` of `ω`
the homothety `A[0] ⟶ Hom^•(I, I)` is a quasi-isomorphism, so the degree-zero cohomology of the
endomorphism complex is free of rank one over `A`, and that cohomology is `End_{D(A)}(I)`. -/
public theorem IsDualizingComplex.bijective_algebraMap_end
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {ω : DerivedCategory (ModuleCat.{u} A)} (hω : IsDualizingComplex ω) :
    Function.Bijective (algebraMap A (End ω)) := by
  obtain ⟨a, b, I, hIGE, hILE, hIinj, ⟨eI⟩⟩ := hω.finiteInjectiveDimension
  have := hIGE
  have := hILE
  have : ∀ i : ℤ, Injective (I.X i) := hIinj
  have : I.IsKInjective := CochainComplex.isKInjective_of_injective I a
  obtain ⟨eB⟩ := linearEquiv_homology_homComplexR_of_quasiIso_homothety I
    (hω.homothetyQuasiIso I ⟨eI.symm⟩ hIinj ⟨a, b, hIGE, hILE⟩)
  exact bijective_algebraMap_end_of_linearEquiv ω
    (((endLinearEquivOfIso.{u, u} eI).trans
      ((homologyZeroEndLinearEquiv I).symm.trans eB)).symm)

/-- **The endomorphism ring of a dualizing complex is the base ring.** For a dualizing complex `ω`
over a Noetherian ring `A`, the endomorphism ring of `ω` in `D(A)` is `A` itself, as an
`A`-algebra; in particular every endomorphism of `ω` is multiplication by a unique scalar.

This is the derived form of the homothety condition in `Dualizing.IsDualizingComplex`, which is
stated at the chain level as a quasi-isomorphism `A[0] ⟶ Hom^•(I, I)`. -/
public def IsDualizingComplex.endAlgEquiv
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {ω : DerivedCategory (ModuleCat.{u} A)} (hω : IsDualizingComplex ω) :
    End ω ≃ₐ[A] A :=
  (AlgEquiv.ofBijective (Algebra.ofId A (End ω)) hω.bijective_algebraMap_end).symm

/-- **The automorphism group of a dualizing complex is the unit group of the base ring.** Reading
off the units of `Dualizing.IsDualizingComplex.endAlgEquiv`: an automorphism of `ω` in `D(A)` is
multiplication by a unique unit of `A`.

This is the automorphism-group half of the comparison made in [Stacks, Tag 0A83]. The source
states it for a normalized dualizing complex over a Noetherian local ring; no normalization and
no local hypothesis are needed, so the statement here is more general. The other side of the
comparison is `Dualizing.LocalDuality.injectiveHullUnitsMulEquivUnitsAdicCompletion`, where the
automorphism group is instead the units of the `𝔪`-adic completion. -/
@[stacks 0A83 "the automorphism group of a dualizing complex is the group of units of the base \
ring; proved for every dualizing complex, not only a normalized one, and stated at the ring's own \
module universe"]
public def IsDualizingComplex.autMulEquivUnits
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {ω : DerivedCategory (ModuleCat.{u} A)} (hω : IsDualizingComplex ω) :
    Aut ω ≃* Aˣ :=
  (Aut.unitsEndEquivAut ω).symm.trans
    (Units.mapEquiv hω.endAlgEquiv.toRingEquiv.toMulEquiv)

end Dualizing

end
