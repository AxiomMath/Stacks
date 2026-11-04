module

public import StacksFrontier.Homology.Tor.IndependenceDescent

/-!
# The prime of a tensor product cut out by an evaluation in a field

Stacks 08HX checks Tor independence of two algebras `A₀`, `C₀` over `R₀` prime by prime: the
localization of every positive-degree `Tor_i^{R₀}(A₀, C₀)` at every prime of `A₀ ⊗_{R₀} C₀` has
to vanish.  `RingTheory.TorIndependence.subsingleton_localizedModule_torObj_of_flat_lifts`
provides that vanishing at a prime which is the *contraction* of a prime of `A' ⊗_{R'} C'`, for
a flat base change `R₀ → R'` with flat lifts of the two factors.  This file produces such a
prime upstairs from a homomorphism into a field: a prime of `A₀ ⊗_{R₀} C₀` presented as the
kernel of `ε : A₀ ⊗_{R₀} C₀ → Ω` is the contraction of the kernel of the homomorphism
`A' ⊗_{R'} C' → Ω` assembled from two `R'`-algebra homomorphisms extending `ε` on the two
factors.

It also records the change of the second factor of such a tensor product along a ring
equivalence, which is what lets the two sides of a pair be compared over *one* chosen base
change when each side naturally carries its own.

## Main results

* `RingHom.Flat.tensorProduct_lift_congr_base`: flatness of `C₀ ⊗_{R₀} T → C'` transports along
  a ring equivalence `T ≃+* T'` compatible with the structure maps.
* `RingTheory.TorIndependence.subsingleton_localizedModule_torObj_of_eval`: the localization of
  `Tor_i^{R₀}(A₀, C₀)` at the kernel of an evaluation in a field vanishes, given the two flat
  lifts and Tor independence upstairs.

## Implementation notes

The prime upstairs is the kernel of `Algebra.TensorProduct.lift fA' fC'`, which is prime because
`Ω` is a field, hence a domain (`RingHom.ker_isPrime`).  That it contracts to the kernel of `ε`
is `RingHom.comap_ker` together with the equality of the two homomorphisms out of
`A₀ ⊗_{R₀} C₀`, which is checked on pure tensors: both send `a ⊗ c` to `ε(a ⊗ 1) · ε(1 ⊗ c)`.

## References

* [Stacks Project, Tag 08HW](https://stacks.math.columbia.edu/tag/08HW)
* [Stacks Project, Tag 08HX](https://stacks.math.columbia.edu/tag/08HX)
* [Stacks Project, Tag 08IQ](https://stacks.math.columbia.edu/tag/08IQ)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace RingHom.Flat

/-- **Changing the second factor of a tensor product along a ring equivalence.**  Let `e` be a
ring equivalence `T ≃+* T'` of two `R₀`-algebras compatible with their structure maps and with
two given homomorphisms into a third algebra `C'`.  Then flatness of `C₀ ⊗_{R₀} T' → C'` gives
flatness of `C₀ ⊗_{R₀} T → C'`.

The two maps differ by `Algebra.TensorProduct.congr`, which is bijective, so the flatness is
transported by `RingHom.Flat.of_bijective`. -/
theorem tensorProduct_lift_congr_base {R₀ C₀ T T' C' : Type u}
    [CommRing R₀] [CommRing C₀] [CommRing T] [CommRing T'] [CommRing C']
    [Algebra R₀ C₀] [Algebra R₀ T] [Algebra R₀ T'] [Algebra R₀ C']
    [Algebra C₀ C'] [Algebra T C'] [Algebra T' C'] [IsScalarTower R₀ C₀ C']
    [IsScalarTower R₀ T C'] [IsScalarTower R₀ T' C']
    (e : T ≃+* T') (he : ∀ r : R₀, e (algebraMap R₀ T r) = algebraMap R₀ T' r)
    (he' : ∀ t : T, algebraMap T' C' (e t) = algebraMap T C' t)
    (hflat : RingHom.Flat (Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom R₀ C₀ C') (IsScalarTower.toAlgHom R₀ T' C')
      fun _ _ => Commute.all _ _).toRingHom) :
    RingHom.Flat (Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom R₀ C₀ C') (IsScalarTower.toAlgHom R₀ T C')
      fun _ _ => Commute.all _ _).toRingHom := by
  let eAlg : T ≃ₐ[R₀] T' := { e with commutes' := he }
  let c : (C₀ ⊗[R₀] T) ≃ₐ[R₀] (C₀ ⊗[R₀] T') :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : C₀ ≃ₐ[R₀] C₀) eAlg
  have hcomp : (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R₀ C₀ C')
        (IsScalarTower.toAlgHom R₀ T C') fun _ _ => Commute.all _ _).toRingHom =
      (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R₀ C₀ C')
          (IsScalarTower.toAlgHom R₀ T' C') fun _ _ => Commute.all _ _).toRingHom.comp
        c.toRingHom := by
    refine RingHom.ext fun z => ?_
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a t =>
      show algebraMap C₀ C' a * algebraMap T C' t =
        algebraMap C₀ C' a * algebraMap T' C' (e t)
      rw [he']
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [hcomp]
  exact (RingHom.Flat.of_bijective c.bijective).comp hflat

end RingHom.Flat

namespace RingTheory.TorIndependence

/-- **The vanishing of Tor localized at the kernel of an evaluation in a field.**  Let `R₀ → R'`
be flat, let `A₀`, `C₀` be `R₀`-algebras and `A'`, `C'` be `R'`-algebras receiving them over
`R₀` by maps whose lifts `A₀ ⊗_{R₀} R' → A'` and `C₀ ⊗_{R₀} R' → C'` are flat, and let `A'` and
`C'` be Tor independent over `R'`.  Let `ε : A₀ ⊗_{R₀} C₀ → Ω` be a homomorphism into a field
which extends to `R'`-algebra homomorphisms `fA' : A' → Ω` and `fC' : C' → Ω` on the two
factors.  Then the localization of `Tor_i^{R₀}(A₀, C₀)` at the kernel of `ε` vanishes for every
`i > 0`.

The kernel of the homomorphism `A' ⊗_{R'} C' → Ω` assembled from `fA'` and `fC'` is a prime
contracting to the kernel of `ε`, so this is
`RingTheory.TorIndependence.subsingleton_localizedModule_torObj_of_flat_lifts` at that pair of
primes. -/
theorem subsingleton_localizedModule_torObj_of_eval
    (R₀ A₀ C₀ R' A' C' : Type u) {Ω : Type u}
    [CommRing R₀] [CommRing A₀] [CommRing C₀] [CommRing R'] [CommRing A'] [CommRing C']
    [Field Ω]
    [Algebra R₀ A₀] [Algebra R₀ C₀] [Algebra R₀ R'] [Algebra R₀ A'] [Algebra R₀ C']
    [Algebra R' A'] [Algebra R' C'] [Algebra A₀ A'] [Algebra C₀ C']
    [IsScalarTower R₀ A₀ A'] [IsScalarTower R₀ C₀ C'] [IsScalarTower R₀ R' A']
    [IsScalarTower R₀ R' C'] [Algebra R' Ω]
    (hR' : RingHom.Flat (algebraMap R₀ R'))
    (hA : RingHom.Flat (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R₀ A₀ A')
      (IsScalarTower.toAlgHom R₀ R' A') fun _ _ => Commute.all _ _).toRingHom)
    (hC : RingHom.Flat (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R₀ C₀ C')
      (IsScalarTower.toAlgHom R₀ R' C') fun _ _ => Commute.all _ _).toRingHom)
    (hTor : RingTheory.TorIndependence.TorIndependent R' A' C')
    (ε : A₀ ⊗[R₀] C₀ →+* Ω) [(RingHom.ker ε).IsPrime]
    (fA' : A' →ₐ[R'] Ω) (fC' : C' →ₐ[R'] Ω)
    (hA' : ∀ a : A₀, fA' (algebraMap A₀ A' a) = ε (a ⊗ₜ[R₀] (1 : C₀)))
    (hC' : ∀ c : C₀, fC' (algebraMap C₀ C' c) = ε ((1 : A₀) ⊗ₜ[R₀] c))
    (i : ℕ) (hi : 0 < i) :
    letI := TorChangeOfRings.moduleStructure TorChangeOfRings.canonicalSystem_nonempty
      R₀ A₀ C₀ i
    Subsingleton (LocalizedModule (RingHom.ker ε).primeCompl
      (TorChangeOfRings.torObj R₀ i A₀ C₀)) := by
  set ε' := (Algebra.TensorProduct.lift fA' fC'
    fun _ _ => Commute.all _ _).toRingHom with hε'def
  have hlift : ∀ x y, ε' (x ⊗ₜ[R'] y) = fA' x * fC' y := fun x y =>
    Algebra.TensorProduct.lift_tmul _ _ _ x y
  have : (RingHom.ker ε').IsPrime := RingHom.ker_isPrime ε'
  have hεT : ε'.comp (TorChangeOfRings.tensorProductMap R₀ R' A₀ C₀ A' C'
      (IsScalarTower.toAlgHom R₀ A₀ A') (IsScalarTower.toAlgHom R₀ C₀ C')) = ε := by
    refine RingHom.ext fun z => ?_
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a c =>
      have hT : TorChangeOfRings.tensorProductMap R₀ R' A₀ C₀ A' C'
            (IsScalarTower.toAlgHom R₀ A₀ A') (IsScalarTower.toAlgHom R₀ C₀ C')
            (a ⊗ₜ[R₀] c) =
          (algebraMap A₀ A' a) ⊗ₜ[R'] (algebraMap C₀ C' c) := by
        show (_ ⊗ₜ[R'] (1 : C')) * ((1 : A') ⊗ₜ[R'] _) = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rfl
      rw [RingHom.comp_apply, hT, hlift, hA' a, hC' c, ← map_mul]
      refine congrArg ε ?_
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hsp : RingHom.ker ε = (RingHom.ker ε').comap
      (TorChangeOfRings.tensorProductMap R₀ R' A₀ C₀ A' C'
        (IsScalarTower.toAlgHom R₀ A₀ A') (IsScalarTower.toAlgHom R₀ C₀ C')) := by
    rw [RingHom.comap_ker, hεT]
  exact RingTheory.TorIndependence.subsingleton_localizedModule_torObj_of_flat_lifts
    R₀ A₀ C₀ R' A' C' (IsScalarTower.toAlgHom R₀ A₀ A') (IsScalarTower.toAlgHom R₀ C₀ C')
    hR' hA hC hTor (RingHom.ker ε) (RingHom.ker ε') hsp i hi

end RingTheory.TorIndependence

end
