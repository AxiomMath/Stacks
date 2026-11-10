module

public import Mathlib.RingTheory.Unramified.Locus
public import Mathlib.RingTheory.Unramified.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.NoetherDifferent.Basic
public import StacksFrontier.AlgebraicGeometry.Different.NoetherDifferent.Localization

/-!
# The vanishing locus of the Noether different

For an algebra of finite type, the primes containing the Noether different are exactly the primes
at which the algebra fails to be unramified. Equivalently, the zero locus of the Noether
different is the complement of the unramified locus.

## Main results

* `Stacks.Discriminant.zeroLocus_noetherDifferent` identifies the vanishing locus of the Noether
  different with the complement of the unramified locus.

## Implementation notes

Mathlib's `Algebra.unramifiedLocus` expresses unramifiedness at each prime using
`Algebra.IsUnramifiedAt`, and the equality is one of sets of points of `PrimeSpectrum B`. The
proof runs through the statement that the Noether different of an essentially finite type algebra
is the unit ideal exactly when the algebra is formally unramified, combined with the behaviour of
the Noether different under localization at one element.

## References

* [Stacks Project, Tag 0BVU](https://stacks.math.columbia.edu/tag/0BVU)
-/

@[expose] public section

namespace Stacks.Discriminant

universe u v

open scoped TensorProduct

private theorem specMap_ulift_away (B : Type v) [CommRing B] (f : B) :
    AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap B (Localization.Away f)).ulift.{v, v})) := by
  let C := Localization.Away f
  let g : ULift B →+* ULift C := (algebraMap B C).ulift
  let _ : Algebra (ULift B) (ULift C) := g.toAlgebra
  let f' : ULift B := ⟨f⟩
  let _ : IsLocalization.Away f' (ULift C) := by
    refine IsLocalization.Away.mk f' ?_ ?_ ?_
    · exact IsUnit.map (ULift.ringEquiv : ULift.{v} C ≃+* C).symm.toMonoidHom
        (IsLocalization.Away.algebraMap_isUnit f)
    · intro z
      obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj f z.down
      exact ⟨n, ⟨a⟩, by
        apply ULift.ext; simpa [g, C, RingHom.algebraMap_toAlgebra] using ha⟩
    · intro a b hab
      have hab' : algebraMap B C a.down = algebraMap B C b.down := congrArg ULift.down hab
      obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq f hab'
      exact ⟨n, by apply ULift.ext; simpa using hn⟩
  exact AlgebraicGeometry.IsOpenImmersion.of_isLocalization f'

private theorem noetherDifferent_eq_top_iff_formallyUnramified
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.EssFiniteType A B] :
    noetherDifferent A B = ⊤ ↔ Algebra.FormallyUnramified A B := by
  classical
  let μ := Algebra.TensorProduct.lmul' A (S := B)
  have hμ : Function.Surjective μ := fun b ↦
    ⟨b ⊗ₜ[A] (1 : B), by simp [μ, Algebra.TensorProduct.lmul'_apply_tmul]⟩
  rw [noetherDifferent, Ideal.eq_top_iff_one]
  change (1 ∈ Ideal.map μ.toRingHom (diagonalAnnihilator A B)) ↔ _
  rw [Ideal.mem_map_iff_of_surjective μ.toRingHom hμ]
  constructor
  · rintro ⟨t, ht, hμt⟩
    refine (Algebra.FormallyUnramified.iff_exists_tensorProduct
      (R := A) (S := B)).mpr ⟨t, fun b => ?_, hμt⟩
    simpa [Algebra.smul_def, mul_comm] using
      (Submodule.mem_annihilator.mp ht)
        ((1 : B) ⊗ₜ[A] b - b ⊗ₜ[A] (1 : B))
        (by simp [RingHom.mem_ker, Algebra.TensorProduct.lmul'_apply_tmul])
  · intro h
    obtain ⟨t, ht, hμt⟩ :=
      (Algebra.FormallyUnramified.iff_exists_tensorProduct
        (R := A) (S := B)).mp h
    refine ⟨t, ?_, hμt⟩
    change t ∈ (KaehlerDifferential.ideal A B).annihilator
    rw [← KaehlerDifferential.span_range_eq_ideal, Submodule.mem_annihilator_span]
    rintro ⟨_, ⟨b, rfl⟩⟩
    simpa [Algebra.smul_def, mul_comm] using ht b

/-- The primes containing the Noether different are exactly the primes at
which a finite type algebra is not unramified. -/
@[stacks 0BVU]
theorem zeroLocus_noetherDifferent
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.FiniteType A B] :
    PrimeSpectrum.zeroLocus (noetherDifferent A B : Set B) =
      (Algebra.unramifiedLocus A B)ᶜ := by
  classical
  ext q
  change (noetherDifferent A B ≤ q.asIdeal) ↔
    ¬ Algebra.IsUnramifiedAt A q.asIdeal
  constructor
  · intro hD hq
    obtain ⟨f, hfq, hloc⟩ :=
      Algebra.exists_unramified_of_isUnramifiedAt (R := A) (A := B) q.asIdeal
    let _ : Algebra.Unramified A (Localization.Away f) := hloc
    have htop : noetherDifferent A (Localization.Away f) = ⊤ :=
      (noetherDifferent_eq_top_iff_formallyUnramified A (Localization.Away f)).2
        hloc.formallyUnramified
    rw [noetherDifferent_eq_map A B (Localization.Away f)
      (specMap_ulift_away B f)] at htop
    have hnot : ¬ Disjoint (Submonoid.powers f : Set B)
        (noetherDifferent A B : Set B) := fun hd =>
      ((IsLocalization.map_algebraMap_ne_top_iff_disjoint
        (Submonoid.powers f) (Localization.Away f)
        (noetherDifferent A B)).2 hd) htop
    obtain ⟨x, hxpow, hxD⟩ := Set.not_disjoint_iff.mp hnot
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff x f).mp hxpow
    exact hfq (q.2.mem_of_pow_mem n (hD hxD))
  · intro hq
    by_contra hD
    obtain ⟨d, hdD, hdq⟩ := Set.not_subset.mp hD
    have hloc : noetherDifferent A (Localization.Away d) = ⊤ := by
      rw [noetherDifferent_eq_map A B (Localization.Away d)
        (specMap_ulift_away B d)]
      apply (Ideal.map (algebraMap B (Localization.Away d))
        (noetherDifferent A B)).eq_top_of_isUnit_mem
        (Ideal.mem_map_of_mem _ hdD)
      exact IsLocalization.Away.algebraMap_isUnit d
    have hu : Algebra.FormallyUnramified A (Localization.Away d) :=
      (noetherDifferent_eq_top_iff_formallyUnramified A (Localization.Away d)).mp hloc
    exact hq ((Algebra.basicOpen_subset_unramifiedLocus_iff.mpr hu)
      (by simpa using hdq))

end Stacks.Discriminant
