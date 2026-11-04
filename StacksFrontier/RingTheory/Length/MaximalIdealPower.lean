module

public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-!
# Finite length of a quotient by a power of the maximal ideal

Let `A` be a Noetherian local ring with maximal ideal `𝔪` and let `M` be a finite `A`-module.
Then `M / 𝔪 ^ (n + 1) M` has finite length over `A`, and so does any quotient of `M` by a
submodule containing `𝔪 ^ (n + 1) M`.

## Main results

* `Module.finiteLength_quotient_by_maximalIdealPower`: the quotient of a finite module by a
  positive power of the maximal ideal times the module has finite length.
* `Module.finiteLength_quotient_of_contains_maximalIdealPower`: the same for any larger
  submodule.

## Implementation notes

The quotient is a finite module over `B = A / 𝔪 ^ (n + 1)`, which is Noetherian local with
nilpotent maximal ideal, hence Artinian by Hopkins–Levitzki
(`isArtinianRing_iff_isNilpotent_maximalIdeal`). A finite module over an Artinian ring is both
Noetherian and Artinian, and both properties descend along the surjection `A → B`; finite length
is then `isFiniteLength_iff_isNoetherian_isArtinian`.

The exponent is written `n + 1` rather than `n` with `n ≠ 0` because the nilpotence witness is
exactly that exponent, and because the consumers produce an exponent and then enlarge it.
-/

@[expose] public section

namespace Module

/-- **The quotient of a finite module by a positive power of the maximal ideal has finite
length.** Here `A` is a Noetherian local ring and `M` a finite `A`-module. -/
public theorem finiteLength_quotient_by_maximalIdealPower
    (A : Type*) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] (n : ℕ) :
    IsFiniteLength A (M ⧸ IsLocalRing.maximalIdeal A ^ (n + 1) • (⊤ : Submodule A M)) := by
  let J : Ideal A := IsLocalRing.maximalIdeal A ^ (n + 1)
  let B := A ⧸ J
  have : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr <|
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      (Ideal.pow_le_self n.succ_ne_zero)
  have : IsLocalRing B :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have : IsNoetherianRing B := inferInstanceAs (IsNoetherianRing (A ⧸ J))
  have hnil : IsNilpotent (IsLocalRing.maximalIdeal B) := by
    refine ⟨n + 1, ?_⟩
    rw [← IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective, ← Ideal.map_pow]
    show Ideal.map (Ideal.Quotient.mk J) (IsLocalRing.maximalIdeal A ^ (n + 1)) = ⊥
    rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  have : IsArtinianRing B := (isArtinianRing_iff_isNilpotent_maximalIdeal B).mpr hnil
  let : Algebra A B := Ideal.Quotient.algebra A
  let : IsScalarTower A B (M ⧸ J • (⊤ : Submodule A M)) := inferInstance
  have : Module.Finite B (M ⧸ J • (⊤ : Submodule A M)) := inferInstance
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨inferInstance, isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := J))⟩

/-- **The quotient of a finite module by a submodule containing a positive power of the maximal
ideal times the module has finite length.** -/
public theorem finiteLength_quotient_of_contains_maximalIdealPower
    (A : Type*) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (N : Submodule A M) (n : ℕ)
    (hN : IsLocalRing.maximalIdeal A ^ (n + 1) • (⊤ : Submodule A M) ≤ N) :
    IsFiniteLength A (M ⧸ N) := by
  refine IsFiniteLength.of_surjective (finiteLength_quotient_by_maximalIdealPower A M n)
    (f := Submodule.mapQ _ N LinearMap.id hN) ?_
  intro y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N y
  exact ⟨Submodule.Quotient.mk x, by simp [Submodule.mapQ_apply]⟩

end Module

end
