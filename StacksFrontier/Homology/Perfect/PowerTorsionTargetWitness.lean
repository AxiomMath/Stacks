module

public import StacksFrontier.Homology.Perfect.PowerTorsionTarget
public import StacksFrontier.Homology.Perfect.KoszulSpreadingOut

/-!
# A non-degenerate instance of Stacks 08EJ in the affine case

Over `A = ℤ` with `f = 2`, the Koszul complex on `(2)` is a perfect object of `D(ℤ)`, and every
cohomology module of `ℤ/2` placed in degree zero has support inside `V(2)`. So
`StacksDraft.Perfect.exists_pow_smul_eq_zero_of_isPerfect_of_support_subset_zeroLocus` applies to
every morphism between these two nonzero objects.

## Main definitions

* `StacksDraft.Perfect.koszulTwo`: the Koszul complex on `(2) ⊆ ℤ`, as an object of `D(ℤ)`.
* `StacksDraft.Perfect.zmodTwoSingle`: `ℤ/2` placed in degree zero, as an object of `D(ℤ)`.

## Main results

* `StacksDraft.Perfect.support_subset_zeroLocus_of_smul_eq_zero`: a module annihilated by `f` has
  support inside `V(f)`.
* `StacksDraft.Perfect.support_homology_subset_zeroLocus_zmodTwoSingle`: every cohomology module
  of `ℤ/2[0]` has support inside `V(2)`.

## Implementation notes

The final `example` leaves its type to be inferred: `D(ℤ)` carries two `Linear ℤ` structures, and
a restatement of the conclusion would have to choose one.

## References

* [Stacks Project, Lemma 36.10.12 (Tag 08EJ)](https://stacks.math.columbia.edu/tag/08EJ)
* [Stacks Project, Lemma 15.90.6 (Tag 0953)](https://stacks.math.columbia.edu/tag/0953)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace StacksDraft.Perfect

attribute [local instance] HasDerivedCategory.standard

/-- A module annihilated by `f` has support inside the zero locus of `f`. -/
public theorem support_subset_zeroLocus_of_smul_eq_zero {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] {f : R} (h : ∀ m : M, f • m = 0) :
    Module.support R M ⊆ PrimeSpectrum.zeroLocus {f} := by
  rw [← PrimeSpectrum.zeroLocus_span]
  refine support_subset_zeroLocus_of_isIPowerTorsion fun m => ⟨1, Nat.one_pos, fun a ha => ?_⟩
  rw [pow_one, Ideal.mem_span_singleton] at ha
  obtain ⟨b, rfl⟩ := ha
  rw [mul_smul]
  exact h _

/-- The Koszul complex on `(2) ⊆ ℤ`, placed in degrees `-1, 0`, as an object of `D(ℤ)`. -/
public abbrev koszulTwo : DerivedCategory (ModuleCat.{0} ℤ) :=
  DerivedCategory.Q.obj
    ((Koszul.seqComplex (fun _ : Fin 1 => (2 : ℤ))).extend ComplexShape.embeddingDownNat)

/-- `ℤ/2` placed in cohomological degree zero, as an object of `D(ℤ)`. -/
public abbrev zmodTwoSingle : DerivedCategory (ModuleCat.{0} ℤ) :=
  (DerivedCategory.singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ (ZMod 2))

/-- Every element of `ℤ/2` is its own negative. -/
public theorem add_self_zmodTwo (y : ZMod 2) : y + y = 0 := by revert y; decide

/-- Every cohomology module of `ℤ/2[0]` has support inside `V(2)`. -/
public theorem support_homology_subset_zeroLocus_zmodTwoSingle (p : ℤ) :
    Module.support ℤ
      ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) p).obj zmodTwoSingle) ⊆
      PrimeSpectrum.zeroLocus {(2 : ℤ)} := by
  refine support_subset_zeroLocus_of_smul_eq_zero (f := (2 : ℤ)) fun x => ?_
  rcases eq_or_ne p 0 with rfl | hp
  · rw [two_smul]
    let e := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{0} ℤ) 0).app
      (ModuleCat.of ℤ (ZMod 2))
    have hinj : Function.Injective (ConcreteCategory.hom e.hom) :=
      (ConcreteCategory.bijective_of_isIso e.hom).1
    apply hinj
    rw [map_add, map_zero]
    exact add_self_zmodTwo _
  · have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) p).obj zmodTwoSingle) := by
      exact hp.lt_or_gt.elim (fun h => DerivedCategory.isZero_of_isGE _ 0 p h)
        fun h => DerivedCategory.isZero_of_isLE _ 0 p h
    have := ModuleCat.isZero_iff_subsingleton.mp hz
    exact Subsingleton.elim _ _

/-- Over `ℤ` with `f = 2`, every morphism in `D(ℤ)` from the Koszul complex on `(2)` to `ℤ/2[0]` is
annihilated by a power of `2`. -/
example (α : koszulTwo ⟶ zmodTwoSingle) :=
  exists_pow_smul_eq_zero_of_isPerfect_of_support_subset_zeroLocus
    (2 : ℤ) (isPerfect_extend_koszul _) support_homology_subset_zeroLocus_zmodTwoSingle α

end StacksDraft.Perfect

end
