module

public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.ComplementSheafCohomology
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.LowBoundTFAE

/-!
# The vanishing equivalence of Tag 0DX7, for every bound

Let `I` be a finitely generated ideal of a commutative ring `A` and `Y = V(I)` its zero locus in
`Spec A`. [Stacks, Tag 0DX7] asserts, for every `d ≥ -1`, the equivalence of

1. `H^i_Y(A) = 0` for all `i > d`;
2. `H^i_Y(M) = 0` for all `i > d`, for every `A`-module `M`, in any universe;
3. the geometric condition: `Y = ∅` if `d = -1`, `Y` open and closed if `d = 0`, and vanishing of
   the sheaf cohomology `H^n(Spec A \ Y, F)` for every quasi-coherent `F` and every `n ≥ d` if
   `d > 0`.

`StacksFrontier/RingTheory/LocalCohomology/VanishingTFAE/LowBoundTFAE.lean` proves that equivalence
for `-1 ≤ d ≤ 0`, the two regimes in which the third condition is a condition on `Y` itself.
This file proves it in the remaining regime `d ≥ 1`, where the third condition is about sheaf
cohomology on the complement, and then assembles the two into the statement of the source.

Both directions of the third clause come from the vanishing form of Stacks 0DWR in positive
degrees, `Stacks.LocalCohomology.isZero_hgroup_complementTilde_iff_isZero_localCohomologyModule`:

* from (1) to (3), Stacks 0DWR part (1) writes a quasi-coherent module on the complement as
  `M̃|U`, and `H^n(U, M̃|U) = 0` because `H^{n+1}_Y(M) = 0`, which holds for every `A`-module `M`
  by the descending induction giving (1) ⇒ (2);
* from (3) to (1), the single quasi-coherent module `Ã|U` suffices: the degrees `i > d` are
  exactly the degrees `n + 1` for `n ≥ d`, and `d ≥ 1` keeps `n ≥ 1`, which is the range in which
  the comparison holds.

## Main results

* `Stacks.LocalCohomology.localCohomology_vanishing_tfae_of_one_le` — **[Stacks, Tag 0DX7] for
  `d ≥ 1`.**
* `Stacks.LocalCohomology.localCohomology_vanishing_tfae` — **[Stacks, Tag 0DX7].**

## Implementation notes

The third clause of condition (3) is stated for `F : (U : Scheme).Modules`, that is, for sheaves
of modules whose module universe is the universe of the scheme; that is the universe at which
Stacks 01ET, and hence the Čech computation of cohomology on the complement, is available. The
module universe of condition (2) is `max u v` with `v` free, as in `LowBoundTFAE`, because the
descending induction of
`StacksFrontier/RingTheory/LocalCohomology/LongExactSequence/AllModules.lean` is available there;
the bridge between the two is that condition (1), which is about `A` itself, is equivalent to
condition (2) at every module universe.

`HasDerivedCategory.standard` is pinned as a local instance, as in every file of this
development and as in the definition of `Stacks.LocalCohomology.localCohomologyModule` itself.

No `@[stacks 0DX7]` attribute is placed; the covering set is for the lead to verify.

## References

* [Stacks Project, Tag 0DX7](https://stacks.math.columbia.edu/tag/0DX7)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

/-- **The third condition of [Stacks, Tag 0DX7] follows from the first, for `d ≥ 1`.** If
`H^i_{V(I)}(A) = 0` for every `i > d` then every quasi-coherent module on `U = Spec A \ V(I)` has
vanishing cohomology in every degree `n ≥ d`.

The first condition is upgraded to the second by the descending induction
`Stacks.LocalCohomology.isZero_homology_localCohomology_of_isZero_homology_self`, and the second
is transported to the complement by
`Stacks.LocalCohomology.isZero_hgroup_of_isQuasicoherent`. -/
theorem isZero_hgroup_complement_of_isZero_localCohomologyModule_self
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) (d : ℤ) (hd : 1 ≤ d)
    (h₁ : ∀ i : ℤ, d < i → IsZero (localCohomologyModule A I hI (ModuleCat.of A A) i))
    (F : (complementZeroLocus A I : Scheme).Modules) (hF : F.IsQuasicoherent)
    (n : ℕ) (hn : d ≤ (n : ℤ)) :
    IsZero (Hgroup (complementZeroLocus A I : Scheme).ringCatSheaf ⊤ n F) :=
  isZero_hgroup_of_isQuasicoherent I hI d hd
    (fun M i hi ↦ isZero_homology_localCohomology_of_isZero_homology_self.{u} I hI d h₁ M i hi)
    F hF n hn

/-- **[Stacks, Tag 0DX7] for a bound `d ≥ 1`.** For a finitely generated ideal `I` of a
commutative ring `A` and `d ≥ 1`, the vanishing of `H^i_{V(I)}(A)` above `d`, the same vanishing
for every `A`-module in any universe, and the geometric condition on `V(I)` and its complement
are equivalent.

(1) ⇔ (2) is the descending induction of the source. The first two conjuncts of the geometric
condition are vacuous because `d ≥ 1`, and the third is the vanishing of the cohomology of every
quasi-coherent module on `U = Spec A \ V(I)` in degrees `≥ d`, which is equivalent to (1) by the
comparison of Stacks 0DWR in positive degrees. -/
theorem localCohomology_vanishing_tfae_of_one_le
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (d : ℤ) (hd : (1 : ℤ) ≤ d) :
    List.TFAE [
      ∀ (i : ℤ), d < i →
        IsZero (localCohomologyModule A I hI (ModuleCat.of A A) i),
      ∀ (M : ModuleCat.{max u v} A) (i : ℤ), d < i →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj
          ((Dualizing.derivedPowerTorsionProperty A I hI).ι.obj
            ((Dualizing.localCohomologyFunctor A I hI).obj
              ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)))),
      ((d = -1 → PrimeSpectrum.zeroLocus (I : Set A) = ∅) ∧
        (d = 0 → IsClopen (PrimeSpectrum.zeroLocus (I : Set A))) ∧
        (0 < d →
          let U : (Spec (CommRingCat.of A)).Opens :=
            ⟨(PrimeSpectrum.zeroLocus (I : Set A))ᶜ,
              (PrimeSpectrum.isClosed_zeroLocus (I : Set A)).isOpen_compl⟩
          ∀ (F : (U : Scheme).Modules),
            F.IsQuasicoherent → ∀ (n : ℕ), d ≤ (n : ℤ) →
              IsZero (Hgroup (U : Scheme).ringCatSheaf ⊤ n F)))] := by
  tfae_have 1 → 2 := fun h₁ M i hi =>
    isZero_homology_localCohomology_of_isZero_homology_self.{v} I hI d h₁ M i hi
  tfae_have 2 → 1 := fun h₂ => (isZero_homology_localCohomology_forall_iff.{v} I hI d).2 h₂
  tfae_have 1 → 3 := fun h₁ =>
    ⟨fun hneg => absurd hneg (by omega), fun hzero => absurd hzero (by omega),
      fun _ => isZero_hgroup_complement_of_isZero_localCohomologyModule_self A I hI d hd h₁⟩
  tfae_have 3 → 1 := fun h₃ =>
    isZero_localCohomologyModule_of_isZero_hgroup I hI d hd (h₃.2.2 (by omega))
  tfae_finish

/-- **[Stacks, Tag 0DX7].** Let `I` be a finitely generated ideal of a commutative ring `A`, let
`Y = V(I) ⊆ X = Spec A` and let `d ≥ -1` be an integer. The following are equivalent:
`H^i_Y(A) = 0` for `i > d`; `H^i_Y(M) = 0` for `i > d` for every `A`-module `M`; and the
geometric condition that `Y = ∅` if `d = -1`, that `Y` be open and closed in `X` if `d = 0`, and
that `H^n(X \ Y, ℱ) = 0` for `n ≥ d` for every quasi-coherent `𝒪_{X∖Y}`-module `ℱ` if `d > 0`.

The three regimes of the third condition are proved separately:
`Stacks.LocalCohomology.localCohomology_vanishing_tfae_of_nonpos` for `-1 ≤ d ≤ 0`, where the
condition is one on `Y` itself, and
`Stacks.LocalCohomology.localCohomology_vanishing_tfae_of_one_le` for `d ≥ 1`, where it is the
acyclicity of the complement. -/
@[stacks 0DX7]
theorem localCohomology_vanishing_tfae
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (d : ℤ) (hd : (-1 : ℤ) ≤ d) :
    List.TFAE [
      ∀ (i : ℤ), d < i →
        IsZero (localCohomologyModule A I hI (ModuleCat.of A A) i),
      ∀ (M : ModuleCat.{max u v} A) (i : ℤ), d < i →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj
          ((Dualizing.derivedPowerTorsionProperty A I hI).ι.obj
            ((Dualizing.localCohomologyFunctor A I hI).obj
              ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)))),
      ((d = -1 → PrimeSpectrum.zeroLocus (I : Set A) = ∅) ∧
        (d = 0 → IsClopen (PrimeSpectrum.zeroLocus (I : Set A))) ∧
        (0 < d →
          let U : (Spec (CommRingCat.of A)).Opens :=
            ⟨(PrimeSpectrum.zeroLocus (I : Set A))ᶜ,
              (PrimeSpectrum.isClosed_zeroLocus (I : Set A)).isOpen_compl⟩
          ∀ (F : (U : Scheme).Modules),
            F.IsQuasicoherent → ∀ (n : ℕ), d ≤ (n : ℤ) →
              IsZero (Hgroup (U : Scheme).ringCatSheaf ⊤ n F)))] := by
  rcases le_or_gt d 0 with hd' | hd'
  · exact localCohomology_vanishing_tfae_of_nonpos.{v} A I hI d hd hd'
  · exact localCohomology_vanishing_tfae_of_one_le.{v} A I hI d (by omega)

end Stacks.LocalCohomology

end
