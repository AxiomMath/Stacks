module

public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# Ramification indices across a square of ring isomorphisms

Let `R → S` and `R' → S'` be ring maps, given as `Algebra` structures, and let `e : R ≃+* R'` and
`e' : S ≃+* S'` be ring isomorphisms with `algebraMap R' S' (e x) = e' (algebraMap R S x)`. This
file shows that ramification indices are invariant under such a square, both for
`Ideal.ramificationIdx'`, the supremum of the exponents `n` with `map (algebraMap R S) p ≤ P ^ n`,
and for `Ideal.ramificationIdx`, the length of a quotient of the localization at the prime.

## Main results

* `Stacks.DiscreteValuationRing.EppLevelInduction.map_le_pow_iff_of_ringEquiv_square`: the
  inequality defining the ramification index is invariant under the square.
* `Stacks.DiscreteValuationRing.EppLevelInduction.ramificationIdx'_eq_of_ringEquiv_square`:
  `Ideal.ramificationIdx'` is invariant under the square.
* `ramificationIdx'_maximalIdeal_eq_of_ringEquiv_square`: the same for the maximal ideals of
  local rings.
* `Stacks.DiscreteValuationRing.EppLevelInduction.map_eq_comap_symm`, `isPrime_map`,
  `map_primeCompl`, `under_map`, `quotient_length_eq`: transports of `Ideal.map`, of primality, of
  the prime complement, of `Ideal.under` and of the length of a quotient along ring isomorphisms.
* `Stacks.DiscreteValuationRing.EppLevelInduction.ramificationIdx_map`: `Ideal.ramificationIdx`
  is invariant under the square.

## References

* [The Stacks Project, Tag 09F5](https://stacks.math.columbia.edu/tag/09F5)
-/

@[expose] public section

namespace Stacks.DiscreteValuationRing.EppLevelInduction

/-- **The inequality defining the ramification index is invariant under a square of ring
isomorphisms.** If `e : R ≃+* R'` and `e' : S ≃+* S'` commute with the structure maps, then
`Ideal.map (algebraMap R S) p ≤ P ^ n` holds if and only if it holds for the images of `p` and `P`
under `e` and `e'`. -/
theorem map_le_pow_iff_of_ringEquiv_square
    {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R S] [Algebra R' S']
    (e : R ≃+* R') (e' : S ≃+* S')
    (hsq : ∀ x : R, algebraMap R' S' (e x) = e' (algebraMap R S x))
    (p : Ideal R) (P : Ideal S) (n : ℕ) :
    Ideal.map (algebraMap R' S') (p.map (e : R →+* R')) ≤ (P.map (e' : S →+* S')) ^ n
      ↔ Ideal.map (algebraMap R S) p ≤ P ^ n := by
  have hcomp : (algebraMap R' S').comp (e : R →+* R') = (e' : S →+* S').comp (algebraMap R S) :=
    RingHom.ext hsq
  rw [Ideal.map_map, hcomp, ← Ideal.map_map, ← Ideal.map_pow]
  exact e'.idealComapOrderIso.symm.le_iff_le

/-- **The ramification index is invariant under a square of ring isomorphisms.** If
`e : R ≃+* R'` and `e' : S ≃+* S'` commute with the structure maps, then
`Ideal.ramificationIdx' p P` equals the ramification index of the images of `p` and `P`. -/
theorem ramificationIdx'_eq_of_ringEquiv_square
    {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R S] [Algebra R' S']
    (e : R ≃+* R') (e' : S ≃+* S')
    (hsq : ∀ x : R, algebraMap R' S' (e x) = e' (algebraMap R S x))
    (p : Ideal R) (P : Ideal S) :
    Ideal.ramificationIdx' p P
      = Ideal.ramificationIdx' (p.map (e : R →+* R')) (P.map (e' : S →+* S')) := by
  simp only [Ideal.ramificationIdx', map_le_pow_iff_of_ringEquiv_square e e' hsq]

/-- **The ramification index of local rings is invariant under a square of ring isomorphisms.**
If `e : A ≃+* A'` and `e' : B ≃+* B'` are isomorphisms of local rings commuting with the structure
maps, then the ramification index `Ideal.ramificationIdx'` of the maximal ideals of `A` and `B`
equals that of the maximal ideals of `A'` and `B'`. -/
theorem ramificationIdx'_maximalIdeal_eq_of_ringEquiv_square
    {A B A' B' : Type*} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing A'] [IsLocalRing B']
    [Algebra A B] [Algebra A' B']
    (e : A ≃+* A') (e' : B ≃+* B')
    (hsq : ∀ x : A, algebraMap A' B' (e x) = e' (algebraMap A B x)) :
    Ideal.ramificationIdx' (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B)
      = Ideal.ramificationIdx' (IsLocalRing.maximalIdeal A') (IsLocalRing.maximalIdeal B') := by
  rw [← IsLocalRing.map_maximalIdeal_of_surjective (e : A →+* A') e.surjective,
    ← IsLocalRing.map_maximalIdeal_of_surjective (e' : B →+* B') e'.surjective]
  exact ramificationIdx'_eq_of_ringEquiv_square e e' hsq _ _

/-! ### The same square for `Ideal.ramificationIdx` -/

section RamificationIdx

variable {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']

/-- `Ideal.map` along a ring isomorphism is `Ideal.comap` along its inverse, both written
through the bundled `→+*` coercion. -/
theorem map_eq_comap_symm (e : S ≃+* S') (q : Ideal S) :
    q.map (e : S →+* S') = q.comap (e.symm : S' →+* S) :=
  Ideal.map_comap_of_equiv e

/-- Primality is carried along a ring isomorphism. -/
theorem isPrime_map (e : S ≃+* S') (q : Ideal S) [q.IsPrime] :
    (q.map (e : S →+* S')).IsPrime :=
  Ideal.map_isPrime_of_equiv e

/-- The prime complement is carried along a ring isomorphism: its image under `e.toMonoidHom` is
the prime complement of the image ideal. -/
theorem map_primeCompl (e : S ≃+* S') (q : Ideal S) [q.IsPrime] :
    letI := isPrime_map e q
    Submonoid.map e.toMonoidHom q.primeCompl = (q.map (e : S →+* S')).primeCompl := by
  have := isPrime_map e q
  ext x
  simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff, map_eq_comap_symm, Ideal.mem_comap]
  refine ⟨?_, fun hx => ⟨_, hx, by simp⟩⟩
  rintro ⟨y, hy, rfl⟩
  simpa using hy

/-- `Ideal.under` is carried along the square. -/
theorem under_map [Algebra R S] [Algebra R' S'] (e : R ≃+* R') (e' : S ≃+* S')
    (hsq : ∀ x : R, algebraMap R' S' (e x) = e' (algebraMap R S x))
    (q : Ideal S) :
    (q.map (e' : S →+* S')).under R' = (q.under R).map (e : R →+* R') := by
  have hcomp : (e'.symm : S' →+* S).comp (algebraMap R' S')
      = (algebraMap R S).comp (e.symm : R' →+* R) :=
    RingHom.ext fun y => e'.injective (by simp [← hsq])
  rw [Ideal.under_def, Ideal.under_def, map_eq_comap_symm, map_eq_comap_symm,
    Ideal.comap_comap, Ideal.comap_comap, hcomp]

/-- The length of a quotient is carried by a ring isomorphism matching the two ideals: if
`c : T ≃+* U` maps `I` onto `J`, then `T ⧸ I` and `U ⧸ J` have the same length, each over its own
ring. -/
theorem quotient_length_eq (T U : Type*) [CommRing T] [CommRing U]
    (c : T ≃+* U) (I : Ideal T) (J : Ideal U) (hIJ : J = I.map (c : T →+* U)) :
    Module.length T (T ⧸ I) = Module.length U (U ⧸ J) := by
  let qc := Ideal.quotientEquiv I J c hIJ
  let lc : (T ⧸ I) →ₛₗ[(c : T →+* U)] (U ⧸ J) :=
    { toFun := qc
      map_add' := qc.map_add
      map_smul' := by
        intro sc el
        change qc (Ideal.Quotient.mk I sc * el) = Ideal.Quotient.mk J (c sc) * qc el
        rw [map_mul]
        rfl }
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective lc qc.bijective)]

/-- **`Ideal.ramificationIdx` is carried by a square of ring isomorphisms.** If
`e : R ≃+* R'` and `e' : S ≃+* S'` commute with the structure maps, then the ramification index of
a prime `q` of `S` over `R` equals that of its image `q.map e'` over `R'`. -/
theorem ramificationIdx_map [Algebra R S] [Algebra R' S'] (e : R ≃+* R') (e' : S ≃+* S')
    (hsq : ∀ x : R, algebraMap R' S' (e x) = e' (algebraMap R S x))
    (q : Ideal S) [q.IsPrime] :
    q.ramificationIdx R = (q.map (e' : S →+* S')).ramificationIdx R' := by
  have := isPrime_map e' q
  set q' := q.map (e' : S →+* S')
  set Sq := Localization.AtPrime q
  set Sq' := Localization.AtPrime q'
  have hH : Submonoid.map e'.toMonoidHom q.primeCompl = q'.primeCompl := map_primeCompl e' q
  let f : Sq ≃+* Sq' := IsLocalization.ringEquivOfRingEquiv Sq Sq' e' hH
  have hfcomp : ∀ r : R, f (algebraMap R Sq r) = algebraMap R' Sq' (e r) := by
    intro r
    rw [IsScalarTower.algebraMap_apply R S Sq]
    change IsLocalization.ringEquivOfRingEquiv Sq Sq' e' hH
        (algebraMap S Sq (algebraMap R S r)) = _
    rw [IsLocalization.ringEquivOfRingEquiv_eq, ← hsq,
      ← IsScalarTower.algebraMap_apply R' S' Sq']
  have hideal : ((q'.under R').map (algebraMap R' Sq'))
      = ((q.under R).map (algebraMap R Sq)).map (f : Sq →+* Sq') := by
    rw [under_map e e' hsq q, Ideal.map_map, Ideal.map_map]
    exact congrArg (fun g => Ideal.map g (q.under R)) (RingHom.ext fun r => (hfcomp r).symm)
  rw [Ideal.ramificationIdx_def, Ideal.ramificationIdx_def,
    quotient_length_eq Sq Sq' f _ _ hideal]

end RamificationIdx

end Stacks.DiscreteValuationRing.EppLevelInduction

end
