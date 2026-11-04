module

public import StacksFrontier.RingTheory.LocalCohomology.AffineLocalizationTriangle
public import StacksFrontier.RingTheory.LocalCohomology.LongExactSequence.AllModules

/-!
# Local cohomology and the emptiness of the zero locus

Let `I` be a finitely generated ideal of a commutative ring `A` and `Y = V(I)` its zero locus in
`Spec A`. The three conditions of [Stacks, Tag 0DX7] are, for a bound `d ≥ -1`,

1. `H^i_Y(A) = 0` for all `i > d`;
2. `H^i_Y(M) = 0` for all `i > d`, for every `A`-module `M`;
3. a geometric condition on `Y` and on `Spec A \ Y`, which for `d = -1` reads `Y = ∅`, for
  `d = 0` reads that `Y` is open and closed, and for `d > 0` is the vanishing of the sheaf
  cohomology `H^n(Spec A \ Y, F)` of every quasi-coherent module `F` in degrees `n ≥ d`.

`StacksFrontier.RingTheory.LocalCohomology.LongExactSequence.AllModules` proves that (1) and (2) are
equivalent. This file settles the `d = -1` case of the third condition, in both directions:
`H^i_Y(A) = 0` for every `i > -1` if and only if `Y = ∅`.

Neither direction uses the sheaf cohomology of the complement, which is why they can be proved
here. Both rest on the fact that every cohomology module of `RΓ_Y(M)` is `I`-power torsion, which
is how local cohomology is constructed in this library:
`Stacks.LocalCohomology.localCohomologyModule` is a homology module of an object of
`Dualizing.PowerTorsionDerivedCategory`:

* if `Y = ∅` then an `I`-power torsion module has empty support and is therefore zero, so *every*
  local cohomology module of *every* module vanishes in *every* degree;
* conversely the vanishing for `i > -1`, applied to `M = A/I` in degree `0`, gives `A/I = 0`
  because `H^0_Y(M) ≅ M` for an `I`-power torsion `M`: the unit of the local-cohomology adjunction
  of Stacks 0A6Q is an isomorphism at an object of `D(A)` all of whose cohomology is `I`-power
  torsion. And `A/I = 0` means `I = A`, that is `V(I) = ∅`.

The degree-zero isomorphism is recorded separately as
`Stacks.LocalCohomology.localCohomologyZeroIsoOfTorsion`, since it is the general statement that
local cohomology is the identity on torsion modules and has nothing to do with the bound.

## Main definitions

* `Stacks.LocalCohomology.localCohomologyZeroIsoOfTorsion` — `H^0_Y(M) ≅ M` for an `I`-power
  torsion module `M`.

## Main results

* `Stacks.LocalCohomology.isZero_localCohomologyModule_of_zeroLocus_empty` — if `V(I) = ∅` then
  every local cohomology module vanishes, in every degree and for every module.
* `Stacks.LocalCohomology.zeroLocus_empty_of_isZero_localCohomologyModule` — the converse
  direction of the `d = -1` case: vanishing of `H^i_Y(A)` for all `i > -1` forces `V(I) = ∅`.
* `Stacks.LocalCohomology.zeroLocus_empty_iff_isZero_localCohomologyModule` — the two together,
  which is **(1) ⇔ (3) of [Stacks, Tag 0DX7] at `d = -1`**.

## Implementation notes

No `@[stacks 0DX7]` attribute is placed. The tagged statement is the three-way equivalence for an
arbitrary `d ≥ -1`; what is proved here is one of its three clauses at one value of `d`, and the
clauses at `d = 0` and `d > 0` both require the comparison between the sheaf cohomology of a
quasi-coherent module on `Spec A \ V(I)` and the local cohomology of the module that generates it,
which this library does not have in degrees above one. (Degrees zero and one are
`StacksFrontier.RingTheory.LocalCohomology.LowDegree.ExactSequence`.)

The standard derived category is pinned as a local instance, as it is in
`StacksFrontier.RingTheory.LocalCohomology.LongExactSequence.AllModules` and in the definition of
`Stacks.LocalCohomology.localCohomologyModule` itself. This is not a weakening: the objects here
live in `D(ModuleCat A)` and no statement below needs coproducts of a derived category of sheaves,
which is the situation in which the standard model is the wrong one.

## References

* [Stacks Project, Tag 0DX7](https://stacks.math.columbia.edu/tag/0DX7)
* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
* [Stacks Project, Tag 0953](https://stacks.math.columbia.edu/tag/0953)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

/-- **Local cohomology is the identity on torsion modules in degree zero.** For an `I`-power
torsion module `M` the canonical comparison `H^0_{V(I)}(M) ≅ M` is an isomorphism.

The module placed in degree zero already lies in the full subcategory of `D(A)` on the objects
with `I`-power-torsion cohomology — its only nonvanishing cohomology is `M` itself — so the unit
of the adjunction of Stacks 0A6Q is an isomorphism there, and applying `H^0` gives the claim. -/
def localCohomologyZeroIsoOfTorsion (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{v} A) (hM : IsIPowerTorsion A M I) :
    localCohomologyModule A I hI M 0 ≅ M := by
  let K := (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M
  have hK : Dualizing.derivedPowerTorsionProperty A I hI K := by
    intro i
    rcases eq_or_ne i 0 with rfl | hi
    · exact isIPowerTorsion_of_iso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{v} A) 0).app M).symm hM
    · exact isIPowerTorsion_of_isZero ((lt_or_gt_of_ne hi).elim
        (fun h => DerivedCategory.isZero_of_isGE K 0 i h)
        (fun h => DerivedCategory.isZero_of_isLE K 0 i h))
  exact (DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).mapIso
      ((Dualizing.derivedPowerTorsionProperty A I hI).ι.mapIso
        (asIso ((Dualizing.localCohomologyAdjunction A I hI).unit.app ⟨K, hK⟩))).symm ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{v} A) 0).app M

/-- **An empty zero locus kills all local cohomology.** If `V(I) = ∅` then `H^i_{V(I)}(M) = 0`
for every `A`-module `M` and every degree `i`.

Every cohomology module of `RΓ_{V(I)}(M)` is `I`-power torsion, hence has support inside `V(I)`
by Stacks 0953; an empty support means the module is zero. No bound on `i` is involved. -/
theorem isZero_localCohomologyModule_of_zeroLocus_empty (A : Type u) [CommRing A] (I : Ideal A)
    (hI : I.FG) (h : PrimeSpectrum.zeroLocus (I : Set A) = ∅) (M : ModuleCat.{v} A) (i : ℤ) :
    IsZero (localCohomologyModule A I hI M i) := by
  have hs := (isIPowerTorsion_iff_support_subset A _ I hI).mp
    (((Dualizing.localCohomologyFunctor A I hI).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M)).property i)
  rw [h, Set.subset_empty_iff, Module.support_eq_empty_iff] at hs
  exact ModuleCat.isZero_iff_subsingleton.mpr hs

/-- **(1) implies (3) of [Stacks, Tag 0DX7] at `d = -1`.** If `H^i_{V(I)}(A) = 0` for every
`i > -1` then `V(I) = ∅`.

The vanishing for the ring propagates to every module by
`Stacks.LocalCohomology.isZero_homology_localCohomology_of_isZero_homology_self`; applied to
`A/I` in degree `0`, where local cohomology is the identity because `A/I` is `I`-power torsion, it
gives `A/I = 0`, that is `I = A`. -/
theorem zeroLocus_empty_of_isZero_localCohomologyModule (A : Type u) [CommRing A] (I : Ideal A)
    (hI : I.FG)
    (h : ∀ i : ℤ, -1 < i → IsZero (localCohomologyModule A I hI (ModuleCat.of A A) i)) :
    PrimeSpectrum.zeroLocus (I : Set A) = ∅ := by
  have hM : IsIPowerTorsion A (A ⧸ I) I := by
    intro x
    refine ⟨1, by omega, fun a ha => ?_⟩
    show Ideal.Quotient.mk I a * x = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa using ha), zero_mul]
  have hz := isZero_homology_localCohomology_of_isZero_homology_self.{0} I hI (-1) h
    (ModuleCat.of A (A ⧸ I)) 0 (by omega)
  exact PrimeSpectrum.zeroLocus_empty_iff_eq_top.mpr
    (Ideal.Quotient.subsingleton_iff.mp (ModuleCat.isZero_iff_subsingleton.mp
      (hz.of_iso (localCohomologyZeroIsoOfTorsion A I hI (ModuleCat.of A (A ⧸ I)) hM).symm)))

/-- **(1) ⇔ (3) of [Stacks, Tag 0DX7] at `d = -1`.** The local cohomology `H^i_{V(I)}(A)`
vanishes for every `i > -1` exactly when `V(I)` is empty. -/
theorem zeroLocus_empty_iff_isZero_localCohomologyModule (A : Type u) [CommRing A] (I : Ideal A)
    (hI : I.FG) :
    (∀ i : ℤ, -1 < i → IsZero (localCohomologyModule A I hI (ModuleCat.of A A) i)) ↔
      PrimeSpectrum.zeroLocus (I : Set A) = ∅ :=
  ⟨zeroLocus_empty_of_isZero_localCohomologyModule A I hI,
    fun h i _ => isZero_localCohomologyModule_of_zeroLocus_empty A I hI h _ i⟩

end Stacks.LocalCohomology

end
