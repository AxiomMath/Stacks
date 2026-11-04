module

public import Mathlib.RingTheory.LocalRing.Length
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormulaMultiplicities.TransversalIntersection
public import StacksFrontier.RingTheory.Tor.Balancing
public import StacksFrontier.RingTheory.Tor.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Tor-formula multiplicity under flat local base change

Let `A → B` be a flat local homomorphism of local rings with `𝔪_A B = 𝔪_B`. Such a map preserves
the two numbers of the Tor formula for intersection multiplicities:

* the length of a quotient, `length_B (B ⧸ I B) = length_A (A ⧸ I)`;
* the Tor-formula multiplicity, `e_B(I B, B ⧸ J B) = e_A(I, A ⧸ J)`, where
  `e_A(I, M) = ∑ (-1)^i length_A Tor_i^A(A ⧸ I, M)` is `Ideal.localIntersectionMultiplicity`.

The Tor-formula multiplicity of two quotients is also symmetric, `e_A(I, A ⧸ J) = e_A(J, A ⧸ I)`.

## Main results

* `Ideal.localIntersectionMultiplicity_quotient_comm`: `e_A(I, A ⧸ J) = e_A(J, A ⧸ I)`.
* `IsLocalRing.length_baseChange_eq_of_map_maximalIdeal_eq`: `length_B (B ⊗_A M) = length_A M`.
* `Ideal.length_quotient_map_of_flat`: `length_B (B ⧸ I B) = length_A (A ⧸ I)`.
* `Ideal.localIntersectionMultiplicity_map_of_flat`: `e_B(I B, B ⧸ J B) = e_A(I, A ⧸ J)`.

## Implementation notes

`Ideal.length_quotient_map_of_flat` and `Ideal.localIntersectionMultiplicity_map_of_flat` take
the ring map `f : A →+* B` explicitly, with flatness spelled `f.Flat`, rather than an `Algebra A B`
instance. The rings of `Ideal.localIntersectionMultiplicity_map_of_flat` live in `Type`.

## References

* [Stacks Project, Tag 00M8](https://stacks.math.columbia.edu/tag/00M8)
* [Stacks Project, Tag 00M3](https://stacks.math.columbia.edu/tag/00M3)
* [Stacks Project, Tag 0AZR](https://stacks.math.columbia.edu/tag/0AZR)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

/-- The Tor-formula multiplicity of two quotients is symmetric: the alternating sums of the
lengths of `Tor_i^A(A ⧸ I, A ⧸ J)` and of `Tor_i^A(A ⧸ J, A ⧸ I)` agree. -/
theorem Ideal.localIntersectionMultiplicity_quotient_comm {A : Type u} [CommRing A]
    (I J : Ideal A) :
    I.localIntersectionMultiplicity (A ⧸ J) = J.localIntersectionMultiplicity (A ⧸ I) := by
  refine tsum_congr fun i => ?_
  obtain ⟨e⟩ := tor_symm_canonically_iso A i
  rw [((e.app _).app _).toLinearEquiv.length_eq]
  rfl

/-- For a flat local homomorphism of local rings `A → B` which carries the maximal ideal of `A`
onto a generating set of the maximal ideal of `B`, the length of `B ⊗_A M` over `B` is the length
of `M` over `A`, for every `A`-module `M` (both possibly infinite). -/
@[ega "IV 2.5.5.1" "special case", ega "IV 4.7.1" "special case", ega "IV 4.7.2" "special case"]
theorem IsLocalRing.length_baseChange_eq_of_map_maximalIdeal_eq {A B : Type*} [CommRing A]
    [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Module.Flat A B] (hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
    (M : Type*) [AddCommGroup M] [Module A M] :
    Module.length B (TensorProduct A B M) = Module.length A M := by
  have : IsSimpleModule B (B ⧸ maximalIdeal B) :=
    isSimpleModule_iff_isCoatom.mpr (maximalIdeal.isMaximal B).out
  rw [IsLocalRing.length_baseChange, hm, Module.length_eq_one (R := B), mul_one]

/-- For a flat local homomorphism `f : A → B` of local rings with `𝔪_A B = 𝔪_B` and an ideal `I`
of `A`, the quotient `B ⧸ I B` has the same length over `B` as `A ⧸ I` over `A`. -/
@[ega "IV 4.7.1" "special case"]
theorem Ideal.length_quotient_map_of_flat {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) (hf : f.Flat) [IsLocalHom f]
    (hm : (maximalIdeal A).map f = maximalIdeal B) (I : Ideal A) :
    Module.length B (B ⧸ I.map f) = Module.length A (A ⧸ I) := by
  let := f.toAlgebra
  have : Module.Flat A B := hf
  have : IsLocalHom (algebraMap A B) := ‹IsLocalHom f›
  rw [← IsLocalRing.length_baseChange_eq_of_map_maximalIdeal_eq hm]
  exact (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toLinearEquiv.length_eq

/-- For a flat local homomorphism `f : A → B` of local rings with `𝔪_A B = 𝔪_B` and ideals `I`,
`J` of `A`, the alternating sum of the lengths of the modules `Tor_i^B(B ⧸ I B, B ⧸ J B)` equals
that of the modules `Tor_i^A(A ⧸ I, A ⧸ J)`. -/
theorem Ideal.localIntersectionMultiplicity_map_of_flat {A B : Type} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) (hf : f.Flat) [IsLocalHom f]
    (hm : (maximalIdeal A).map f = maximalIdeal B) (I J : Ideal A) :
    (I.map f).localIntersectionMultiplicity (B ⧸ J.map f) =
      I.localIntersectionMultiplicity (A ⧸ J) := by
  let := f.toAlgebra
  have : Module.Flat A B := hf
  have : IsLocalHom (algebraMap A B) := ‹IsLocalHom f›
  refine tsum_congr fun i => ?_
  let e (I : Ideal A) : ModuleCat.of B (B ⧸ I.map (algebraMap A B)) ≅
      (torBaseChange (R := A) (R' := B)).obj (ModuleCat.of A (A ⧸ I)) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toLinearEquiv.toModuleIso
  let E := ((Tor (ModuleCat.{0} B) i).mapIso (e I)).app _ ≪≫
    ((Tor (ModuleCat.{0} B) i).obj _).mapIso (e J) ≪≫ (torBaseChangeIso i _ _).symm
  rw [show f = algebraMap A B from rfl, E.toLinearEquiv.length_eq]
  exact congrArg (fun n : ℕ∞ => (-1 : ℚ) ^ i * ((n.toNat : ℕ) : ℚ))
    (IsLocalRing.length_baseChange_eq_of_map_maximalIdeal_eq hm _)

end
