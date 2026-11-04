module

public import StacksFrontier.Homology.Perfect.BaseChange
public import StacksFrontier.Homology.Perfect.FiniteFlatCoverDescent
public import StacksFrontier.Homology.Perfect.Local
public import StacksFrontier.Homology.Perfect.LargeUniverse

/-!
# Perfectness descends along a finite jointly surjective family of flat ring maps

Let `A` be a ring and `φ_i : A → A_i` finitely many flat ring maps such that every prime of `A`
comes from a prime of some `A_i`. If `K ⊗_A A_i` is perfect for every `i`, then `K` is perfect.
The map `A → ∏ A_i` is faithfully flat, so this follows from Stacks 068T once `K ⊗_A ∏ A_i` is
known to be perfect, which is Stacks 066Y for the idempotents `e_i` of `∏ A_i`: the localization
at `e_i` is `A_i`.

## Main results

* `StacksDraft.Perfect.isPerfect_Q_extendScalars_of_flat`: termwise base change along a flat map
  preserves perfectness (Stacks 066W).
* `StacksDraft.Perfect.isPerfect_of_finite_flat_family`: the descent statement.

## References

* [Stacks Project, Tag 068T](https://stacks.math.columbia.edu/tag/068T)
* [Stacks Project, Tag 066Y](https://stacks.math.columbia.edu/tag/066Y)
* [Stacks Project, Tag 066W](https://stacks.math.columbia.edu/tag/066W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

/-- The localization of a finite product of rings at the idempotent `Pi.single i 1` is the
factor `A i`, through the projection. -/
theorem isLocalization_away_piSingle {ι : Type} [DecidableEq ι] (A : ι → Type u)
    [∀ i, CommRing (A i)] (i : ι) :
    letI := (Pi.evalRingHom A i).toAlgebra
    IsLocalization.Away (Pi.single i 1 : ∀ j, A j) (A i) := by
  let := (Pi.evalRingHom A i).toAlgebra
  refine IsLocalization.away_of_isIdempotentElem_of_mul ?_ (fun x y => ?_)
    (fun a => ⟨Pi.single i a, by simp [RingHom.algebraMap_toAlgebra]⟩)
  · change Pi.single i 1 * Pi.single i 1 = Pi.single i (1 : A i)
    rw [← Pi.single_mul, one_mul]
  · change x i = y i ↔ _
    refine ⟨fun h => funext fun j => ?_, fun h => by simpa using congrFun h i⟩
    obtain rfl | hj := eq_or_ne j i
    · simp [h]
    · simp [hj]

/-- **Perfectness descends along a finite jointly surjective family of flat ring maps.** Let
`φ_i : A → A_i` be finitely many flat ring maps such that every prime of `A` is the inverse image
of a prime of some `A_i`, and let `K` be a complex of `A`-modules. If every `K ⊗_A A_i` is
perfect, then `K` is perfect: `A → ∏ A_i` is faithfully flat, `K ⊗_A ∏ A_i` is perfect because
its localizations at the idempotents of `∏ A_i` are the `K ⊗_A A_i` (Stacks 066Y), and Stacks
068T descends perfectness along a faithfully flat map. -/
theorem isPerfect_of_finite_flat_family {A : Type u} [CommRing A] {ι : Type} [Finite ι]
    (A' : ι → Type u) [∀ i, CommRing (A' i)] (φ : ∀ i, A →+* A' i) (hflat : ∀ i, (φ i).Flat)
    (hsurj : ∀ p : PrimeSpectrum A, ∃ i, ∃ q : PrimeSpectrum (A' i),
      PrimeSpectrum.comap (φ i) q = p)
    (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : ∀ i, IsPerfect (DerivedCategory.Q.obj
      (((ModuleCat.extendScalars.{u, u, u} (φ i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K))) :
    IsPerfect (DerivedCategory.Q.obj K) :=
  isPerfect_of_extendScalars_of_flat_of_comap_surjective (S := fun i : ULift.{u} ι => A' i.down)
    (fun i => φ i.down) (fun i => hflat i.down)
    (fun p => let ⟨i, q, hq⟩ := hsurj p; ⟨⟨i⟩, q, hq⟩) K fun i => hK i.down

end StacksDraft.Perfect
