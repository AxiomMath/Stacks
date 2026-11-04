module

public import StacksFrontier.Algebra.Homology.SpectralSequence.OriginVanishing
public import StacksFrontier.Algebra.Module.InjectiveHull.Basic
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PuncturedSpectrumCohomology
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PuncturedSpectrum
public import StacksFrontier.Homology.Tor.DerivedTensorDirectSum
public import StacksFrontier.RingTheory.Dualizing.Gorenstein
public import StacksFrontier.RingTheory.Dualizing.InjectiveHullTor
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyOverBase
public import StacksFrontier.RingTheory.Support.Finite

/-!
# Tor of the cohomology of an étale scheme over a punctured spectrum against the residue field

Let `(A, 𝔪)` be a regular local ring containing a field, let `f : V ⟶ Spec A` be étale and
quasi-compact, and suppose `f` factors through the punctured spectrum `Spec A ∖ {𝔪}` by an affine
morphism. [Stacks, Tag 0ECB] says that `H ⁿ(V, 𝒪_V)` is, for `n > 0`, a direct sum of copies of an
injective hull `E` of the residue field of `A`, and [Stacks, Tag 0EBT] says that
`Tor_r^A(E, A ⧸ 𝔪)` vanishes for `r ≠ dim(A)`. Since `Tor` commutes with arbitrary direct sums,
`Tor_r^A(H ⁿ(V, 𝒪_V), A ⧸ 𝔪)` vanishes for `r ≠ dim(A)` as well.

This is the input called `hTor` in the proof of [Stacks, Tag 0ECC]: the vanishing of the
second-page terms of the tensor spectral sequence lying on the incoming diagonal at the origin.

## Main results

* `Stacks.PuncturedSpectrum.puncturedSpectrum_eq_complementZeroLocus` — the punctured spectrum of
  a local ring is the complement of the zero locus of the maximal ideal, which reconciles the
  model of `Spec A ∖ {𝔪}` used by [Stacks, Tag 0ECB] with the one used by [Stacks, Tag 0ECC].
* `Stacks.PuncturedSpectrum.isZero_derivedTensorHomology_cohomologyOverBase_residueField` — the
  vanishing, in the derived form `H ^{-r}(H ⁿ(V, 𝒪_V)[0] ⊗ᴸ_A (A ⧸ 𝔪)[0]) = 0`.

## Implementation notes

The `A`-module model of `H ⁿ(V, 𝒪_V)` used here is `Stacks.LocalCohomology.cohomologyOverBase`,
which is the one [Stacks, Tag 0ECC] is assembled from; [Stacks, Tag 0ECB] is stated for
`Stacks.EtaleDerivation.structureSheafCohomology`, and the two are the same module (the
definitions agree term for term).

[Stacks, Tag 0EBT] is used through
`Dualizing.LocalDuality.nonempty_injectiveHull_derivedTensor_residueField_iso`, the
derived-category form proved in the same module as the tag's two `Tor` clauses: it identifies
`E[0] ⊗ᴸ_A κ[0]` with `κ[0]⟦d⟧`, and reading cohomology in degree `-r` off that shift is what makes
the `Tor` group vanish away from `r = d`. Going through the `Tor` clauses themselves would need the
`Tor_r ≅ H ^{-r}(− ⊗ᴸ −)` comparison, which that module keeps private.

The dimension appears as a natural number `d` with `ringKrullDim A = d`, as in [Stacks, Tag 0EBT]
and [Stacks, Tag 0AWS]; for a Noetherian local ring such a `d` exists
(`Stacks.RegularLocalRing.KernelRegularity.exists_natCast_eq_ringKrullDim`).

## References

* [Stacks Project, Tag 0ECC](https://stacks.math.columbia.edu/tag/0ECC)
* [Stacks Project, Tag 0ECB](https://stacks.math.columbia.edu/tag/0ECB)
* [Stacks Project, Tag 0EBT](https://stacks.math.columbia.edu/tag/0EBT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.LocalCohomology Stacks.SpectralSequence CochainComplex.DerivedTensor

universe u

namespace Stacks.PuncturedSpectrum

attribute [local instance 2000] HasDerivedCategory.standard

/-- **The punctured spectrum is the complement of the zero locus of the maximal ideal.** The two
models of `Spec A ∖ {𝔪}` used in this chapter agree, because the zero locus of the maximal ideal
of a local ring is its closed point. -/
theorem puncturedSpectrum_eq_complementZeroLocus (A : Type u) [CommRing A] [IsLocalRing A] :
    LocalCohomology.puncturedSpectrum (CommRingCat.of A)
      = LocalCohomology.complementZeroLocus A (IsLocalRing.maximalIdeal A) :=
  TopologicalSpace.Opens.ext (congrArg compl zeroLocus_maximalIdeal.symm)

/-- An injective hull of the residue field contributes nothing to the derived tensor product with
the residue field outside the dimension: `H ^{-r}(E[0] ⊗ᴸ_A κ[0]) = 0` for `r ≠ d`.

This is [Stacks, Tag 0EBT] in derived form: the derived tensor product is `κ[0]⟦d⟧`, whose
cohomology is concentrated in degree `-d`. -/
theorem isZero_derivedTensorHomology_injectiveHull_residueField (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (hA : Dualizing.IsGorensteinLocalRing A) (d : ℕ)
    (hdim : ringKrullDim A = (d : WithBot ℕ∞)) (E : ModuleCat.{u} A)
    (j : ModuleCat.of A (IsLocalRing.ResidueField A) ⟶ E) [Mono j]
    (hj : Module.IsInjectiveHull j) (r : ℤ) (hr : r ≠ (d : ℤ)) :
    IsZero (derivedTensorHomology A
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj E)
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (A ⧸ IsLocalRing.maximalIdeal A))) (-r)) := by
  obtain ⟨eTensor⟩ :=
    Dualizing.LocalDuality.nonempty_injectiveHull_derivedTensor_residueField_iso A hA d hdim E j hj
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-r)).mapIso eTensor)
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-r)).mapIso
    (((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso (d : ℤ) (-(d : ℤ)) 0
      (by omega)).app (ModuleCat.of A (IsLocalRing.ResidueField A))))
  have hneq : (-r : ℤ) ≠ -(d : ℤ) := by omega
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · exact DerivedCategory.isZero_of_isGE _ (-(d : ℤ)) (-r) hlt
  · exact DerivedCategory.isZero_of_isLE _ (-(d : ℤ)) (-r) hgt

/-- **The incoming terms of the tensor spectral sequence of [Stacks, Tag 0ECC].** In the situation
of [Stacks, Tag 0ECB] — `A` a regular local ring containing a field `k`, `f : V ⟶ Spec A` étale
and quasi-compact, and the structure morphism factored through the punctured spectrum by an affine
morphism `g` — write `d` for the Krull dimension of `A`. Then for every `n > 0` and every
`r ≠ d`,
`Tor_r^A(H ⁿ(V, 𝒪_V), A ⧸ 𝔪) = 0`,
in the derived form `H ^{-r}(H ⁿ(V, 𝒪_V)[0] ⊗ᴸ_A (A ⧸ 𝔪)[0]) = 0`.

By [Stacks, Tag 0ECB] the cohomology is a direct sum of copies of an injective hull of the residue
field, by [Stacks, Tag 0EBT] each copy contributes nothing away from the dimension, and the
derived tensor product commutes with the direct sum. -/
@[stacks 0ECC "the incoming terms of the tensor spectral sequence: Tor_r(H ⁿ(V,𝒪_V), A/𝔪) = 0 \
for n > 0 and r ≠ dim A, from Tags 0ECB and 0EBT"]
theorem isZero_derivedTensorHomology_cohomologyOverBase_residueField (A k : Type u) [CommRing A]
    [IsRegularLocalRing A] [Field k] [Algebra k A] {V : Scheme.{u}}
    (f : V ⟶ Spec (CommRingCat.of A)) [Etale f] [QuasiCompact f]
    (g : V ⟶ (LocalCohomology.puncturedSpectrum (CommRingCat.of A) : Scheme)) [IsAffineHom g]
    (hg : g ≫ (LocalCohomology.puncturedSpectrum (CommRingCat.of A)).ι = f)
    (d : ℕ) (hdim : ringKrullDim A = (d : WithBot ℕ∞)) (n : ℕ) (hn : 0 < n) (r : ℤ)
    (hr : r ≠ (d : ℤ)) :
    IsZero (derivedTensorHomology A
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (cohomologyOverBase A f (SheafOfModules.unit V.ringCatSheaf) n))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (A ⧸ IsLocalRing.maximalIdeal A))) (-r)) := by
  classical
  -- an injective hull of the residue field
  obtain ⟨E, jhull, hmono, hhull⟩ :=
    Module.exists_isInjectiveHull.{u, u} A (ModuleCat.of A (IsLocalRing.ResidueField A))
  have : Mono jhull := hmono
  -- the factorization through the punctured spectrum, read in the model of [Stacks, Tag 0ECB]
  obtain ⟨g', hg', hg'affine⟩ : ∃ g' : V ⟶ (LocalCohomology.complementZeroLocus A
      (IsLocalRing.maximalIdeal A) : Scheme),
      g' ≫ (LocalCohomology.complementZeroLocus A (IsLocalRing.maximalIdeal A)).ι = f ∧
        IsAffineHom g' := by
    rw [← puncturedSpectrum_eq_complementZeroLocus A]
    exact ⟨g, hg, inferInstance⟩
  have : IsAffineHom g' := hg'affine
  -- [Stacks, Tag 0ECB]: the cohomology is a direct sum of copies of the hull
  obtain ⟨J, ⟨e⟩⟩ := EtalePuncturedSpectrum.exists_directSum_injectiveHull_residueField
    A k E f g' hg' jhull hhull n hn
  -- [Stacks, Tag 0EBT] for one copy, then the direct sum
  exact Stacks.DerivedTensor.isZero_derivedTensorHomology_directSum_single A E _ _ e (-r)
    (isZero_derivedTensorHomology_injectiveHull_residueField A
      (Dualizing.IsRegularLocalRing.isGorensteinLocalRing A) d hdim _ jhull hhull r hr)

end Stacks.PuncturedSpectrum

end
