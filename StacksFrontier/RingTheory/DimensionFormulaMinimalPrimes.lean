module

public import StacksFrontier.RingTheory.DimensionFormula

/-!
# The dimension formula without integrality assumptions

Let `R → S` be a ring homomorphism of finite type with `R` Noetherian, let `q` be a prime of
`S` and `p = q ∩ R`. When `R` and `S` are domains and `R → S` is injective the dimension
formula bounds `height q + trdeg_{κ(p)} κ(q)` by `height p + trdeg_R S`
(`height_add_trdeg_residue_le`). This file removes the integrality assumptions: the
transcendence degree of `S` over `R` is replaced by the largest transcendence degree
`trdeg_{κ(r ∩ R)} κ(r)` of a residue field extension at a minimal prime `r` of `S` below `q`.

The reduction is the usual one. The height of `q` is computed along a chain of primes below
`q`; that chain starts above some minimal prime `r` of `S`, so it survives in `S ⧸ r`. The
extension `R ⧸ (r ∩ R) ⊆ S ⧸ r` is an injective finite-type extension of Noetherian domains, so
the integral dimension formula applies to it, and its two residue fields at the images of `p`
and `q` are the residue fields `κ(p)` and `κ(q)` themselves.

## Main definitions

* `Ideal.underResidueTrdeg`: the transcendence degree of the residue field extension
  `κ(r)/κ(r ∩ R)` cut out by a prime `r` of an `R`-algebra.

## Main results

* `Ideal.exists_mem_minimalPrimes_le_height_map`: any natural number below the height of a prime
  is already below the height of its image in the quotient by a suitable minimal prime.
* `Ideal.toNat_trdeg_residue_congr`: the residue-field transcendence degree of a pair of primes
  lying over one another depends only on the two primes.
* `height_add_trdeg_residue_le_of_forall_minimalPrimes`: the dimension formula with the
  transcendence degree of the extension replaced by a bound on the residue-field transcendence
  degrees at the minimal primes below `q`.

## Implementation notes

Transcendence degrees are `Cardinal`-valued; the ones occurring here are finite under the
finite-type hypothesis and are moved into `ℕ∞` by `Cardinal.toNat`. Heights are `Ideal.height`
and are not assumed finite, so the bound is stated additively, with the residue-field term on
the left rather than subtracted on the right.

The bound `E` is a parameter rather than the supremum over the minimal primes below `q`. The two
formulations are equivalent — take `E` to be that supremum — and the parametrised one is what
consumers can use directly, since the data they have is a uniform bound.

## References

* [Stacks Project, Tag 02IJ](https://stacks.math.columbia.edu/tag/02IJ)
* [Stacks Project, Tag 00P0](https://stacks.math.columbia.edu/tag/00P0)
-/

@[expose] public section

universe u v w

/-- An inequality `a + b ≤ c` in `ℕ∞` follows from its instances at the natural numbers below
`a`: if `a` is finite it is one of them, and if `a` is infinite then `c` is too. -/
theorem ENat.add_le_of_forall_natCast_le {a b c : ℕ∞}
    (h : ∀ n : ℕ, (n : ℕ∞) ≤ a → (n : ℕ∞) + b ≤ c) : a + b ≤ c := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · have hc : c = ⊤ := by
      by_contra hc
      obtain ⟨k, rfl⟩ := ENat.ne_top_iff_exists.mp hc
      have h2 : ((k + 1 : ℕ) : ℕ∞) ≤ (k : ℕ∞) := le_trans le_self_add (h (k + 1) le_top)
      have h3 : k + 1 ≤ k := by exact_mod_cast h2
      omega
    simp [hc]
  · obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp ha
    exact h m le_rfl

/-- If the base field maps onto an intermediate field of an extension, the transcendence degree
of the extension is unchanged: the intermediate field is algebraic over the base, so it
contributes nothing to the transcendence degree of the tower. -/
theorem lift_trdeg_eq_of_surjective_base {K : Type u} {K' : Type v} {L : Type w}
    [Field K] [Field K'] [CommRing L] [IsDomain L]
    [Algebra K K'] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
    (hsurj : Function.Surjective (algebraMap K K')) :
    Cardinal.lift.{v} (Algebra.trdeg K L) = Cardinal.lift.{v} (Algebra.trdeg K' L) := by
  have : Algebra.IsAlgebraic K K' := by
    refine ⟨fun x => ?_⟩
    obtain ⟨a, rfl⟩ := hsurj x
    exact isAlgebraic_algebraMap a
  have : FaithfulSMul K K' :=
    (faithfulSMul_iff_algebraMap_injective K K').mpr (algebraMap K K').injective
  have : FaithfulSMul K' L :=
    (faithfulSMul_iff_algebraMap_injective K' L).mpr (algebraMap K' L).injective
  have h := lift_trdeg_add_eq K K' L
  rw [trdeg_eq_zero, Cardinal.lift_zero, zero_add] at h
  exact h.symm

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- For a prime `q` and an ideal `r ≤ q`, the height of the image of `q` in `S ⧸ r` is the order
height of `q` in the zero locus of `r`, the two orders being matched by
`Ideal.primeSpectrumQuotientOrderIsoZeroLocus`. -/
theorem Ideal.height_map_quotientMk_eq_orderHeight (r : Ideal S) (q : Ideal S) [hq : q.IsPrime]
    (hrq : r ≤ q) :
    (q.map (Ideal.Quotient.mk r)).height =
      Order.height (⟨⟨q, hq⟩, hrq⟩ : ↑(PrimeSpectrum.zeroLocus (r : Set S))) := by
  have : (q.map (Ideal.Quotient.mk r)).IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hrq
  rw [PrimeSpectrum.height_eq_orderHeight
      (⟨q.map (Ideal.Quotient.mk r), ‹_›⟩ : PrimeSpectrum (S ⧸ r)),
    ← Order.height_orderIso (Ideal.primeSpectrumQuotientOrderIsoZeroLocus r)
      ⟨q.map (Ideal.Quotient.mk r), ‹_›⟩]
  congr 1
  exact Subtype.ext (PrimeSpectrum.ext (Ideal.comap_map_mk hrq))

/-- A natural number below the height of a prime `q` is below the height of the image of `q` in
the quotient by some minimal prime contained in `q`: a chain of primes realizing that height
starts above a minimal prime, and the whole chain then lies in the zero locus of that prime. -/
theorem Ideal.exists_mem_minimalPrimes_le_height_map (q : Ideal S) [hq : q.IsPrime] {n : ℕ}
    (hn : (n : ℕ∞) ≤ q.height) :
    ∃ r ∈ minimalPrimes S, r ≤ q ∧ (n : ℕ∞) ≤ (q.map (Ideal.Quotient.mk r)).height := by
  rw [PrimeSpectrum.height_eq_orderHeight (⟨q, hq⟩ : PrimeSpectrum S)] at hn
  obtain ⟨c, hlast, hlen⟩ := Order.exists_series_of_le_height (⟨q, hq⟩ : PrimeSpectrum S) hn
  obtain ⟨r, hr, hrle⟩ :=
    Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal S)) (J := (c 0).asIdeal) bot_le
  have hmem : ∀ i : Fin (c.length + 1), r ≤ (c i).asIdeal := fun i =>
    hrle.trans (c.monotone (Fin.zero_le i))
  have hrq : r ≤ q := by
    have h := hmem (Fin.last c.length)
    rwa [show c (Fin.last c.length) = (⟨q, hq⟩ : PrimeSpectrum S) from hlast] at h
  refine ⟨r, hr, hrq, ?_⟩
  let c' : LTSeries ↑(PrimeSpectrum.zeroLocus (r : Set S)) :=
    { length := c.length
      toFun := fun i => ⟨c i, hmem i⟩
      step := fun i => c.step i }
  have hc'last : RelSeries.last c' = ⟨⟨q, hq⟩, hrq⟩ := Subtype.ext hlast
  rw [Ideal.height_map_quotientMk_eq_orderHeight r q hrq, ← hlen, ← hc'last]
  exact Order.length_le_height_last (p := c')

/-- Passing to the quotients by a prime of `S` and its contraction to `R` commutes with the
structure maps. -/
theorem Ideal.algebraMap_quotient_under_comp_mk (r : Ideal S) :
    (algebraMap (R ⧸ Ideal.under R r) (S ⧸ r)).comp (Ideal.Quotient.mk (Ideal.under R r))
      = (Ideal.Quotient.mk r).comp (algebraMap R S) := by
  ext a
  exact Ideal.quotientMap_mk (J := Ideal.under R r) (I := r) (H := le_rfl) (x := a)

/-- The image of `q` in `S ⧸ r` contracts to `q ∩ R` in `R`. -/
private theorem liesOver_map_quotientMk (r q : Ideal S) (hrq : r ≤ q) :
    (q.map (Ideal.Quotient.mk r)).LiesOver (Ideal.under R q) := by
  refine ⟨?_⟩
  change Ideal.under R q = Ideal.comap (algebraMap R (S ⧸ r)) (q.map (Ideal.Quotient.mk r))
  rw [show (algebraMap R (S ⧸ r)) = (Ideal.Quotient.mk r).comp (algebraMap R S) from rfl,
    ← Ideal.comap_comap, Ideal.comap_map_mk hrq, Ideal.under_def]

/-- The contraction to `R ⧸ (r ∩ R)` of the image of `q` in `S ⧸ r` is the image of `q ∩ R`. -/
theorem Ideal.under_map_quotientMk (r q : Ideal S) (hrq : r ≤ q) :
    Ideal.under (R ⧸ Ideal.under R r) (q.map (Ideal.Quotient.mk r))
      = (Ideal.under R q).map (Ideal.Quotient.mk (Ideal.under R r)) := by
  have hIp : Ideal.under R r ≤ Ideal.under R q := Ideal.comap_mono hrq
  refine Ideal.comap_injective_of_surjective (Ideal.Quotient.mk (Ideal.under R r))
    Ideal.Quotient.mk_surjective ?_
  rw [Ideal.comap_map_mk hIp]
  exact (liesOver_map_quotientMk r q hrq).over.symm

/-- The transcendence degree of the residue field extension `κ(r)/κ(r ∩ R)` cut out by a prime
`r` of an `R`-algebra `S`, as a natural number. It is finite whenever `S` is of finite type over
a Noetherian ring `R`. -/
noncomputable def Ideal.underResidueTrdeg (R : Type u) {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (r : Ideal S) [r.IsPrime] : ℕ :=
  letI := Ideal.ResidueField.algebraOfLiesOver (Ideal.under R r) r
  Cardinal.toNat (Algebra.trdeg (Ideal.under R r).ResidueField r.ResidueField)

/-- The residue field extension at a prime `r` of `S` is the fraction field extension of the
quotient domains `R ⧸ (r ∩ R) ⊆ S ⧸ r`, so the two have the same transcendence degree. -/
theorem Ideal.underResidueTrdeg_eq_toNat_trdeg_quotient (r : Ideal S) [r.IsPrime] :
    (Ideal.underResidueTrdeg R r : ℕ)
      = Cardinal.toNat (Algebra.trdeg (R ⧸ Ideal.under R r) (S ⧸ r)) := by
  rw [Ideal.underResidueTrdeg, resfield_trdeg_eq_quot_trdeg (Ideal.under R r) r]

section Transport

variable (r q : Ideal S)

/-- The image of `q ∩ R` in `R ⧸ (r ∩ R)` contracts to `q ∩ R`. -/
private theorem liesOver_map_quotientMk_under (hrq : r ≤ q) :
    ((Ideal.under R q).map (Ideal.Quotient.mk (Ideal.under R r))).LiesOver (Ideal.under R q) :=
  ⟨(Ideal.comap_map_mk (Ideal.comap_mono hrq)).symm⟩

/-- The residue-field transcendence degree of a pair of primes lying over one another depends
only on the two primes, not on the proofs that they are prime or lie over one another. -/
theorem Ideal.toNat_trdeg_residue_congr {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] (P P' : Ideal A) (Q Q' : Ideal B) [P.IsPrime] [P'.IsPrime] [Q.IsPrime]
    [Q'.IsPrime] [Q.LiesOver P] [Q'.LiesOver P'] (hP : P = P') (hQ : Q = Q') :
    letI := Ideal.ResidueField.algebraOfLiesOver P Q
    letI := Ideal.ResidueField.algebraOfLiesOver P' Q'
    Cardinal.toNat (Algebra.trdeg P.ResidueField Q.ResidueField)
      = Cardinal.toNat (Algebra.trdeg P'.ResidueField Q'.ResidueField) := by
  subst hP hQ
  rfl

/-- Dividing out an ideal contained in `q` does not change the residue field extension at `q`:
the residue field of `q` is that of its image in the quotient, and the residue field of `q ∩ R`
is that of its image, so the two transcendence degrees agree. -/
theorem toNat_trdeg_residue_map_quotientMk_eq [q.IsPrime] (hrq : r ≤ q) :
    haveI : (q.map (Ideal.Quotient.mk r)).IsPrime :=
      Ideal.isPrime_map_quotientMk_of_isPrime hrq
    letI := Ideal.ResidueField.algebraOfLiesOver (Ideal.under R q) q
    letI := Ideal.ResidueField.algebraOfLiesOver
      (Ideal.under (R ⧸ Ideal.under R r) (q.map (Ideal.Quotient.mk r)))
      (q.map (Ideal.Quotient.mk r))
    Cardinal.toNat (Algebra.trdeg (Ideal.under R q).ResidueField q.ResidueField)
      = Cardinal.toNat (Algebra.trdeg
          (Ideal.under (R ⧸ Ideal.under R r) (q.map (Ideal.Quotient.mk r))).ResidueField
          (q.map (Ideal.Quotient.mk r)).ResidueField) := by
  have hq'prime : (q.map (Ideal.Quotient.mk r)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hrq
  set p := Ideal.under R q
  set I := Ideal.under R r
  set q' := q.map (Ideal.Quotient.mk r)
  set p' := Ideal.under (R ⧸ I) q'
  have hq'LO : q'.LiesOver p := liesOver_map_quotientMk r q hrq
  have hcomap : Ideal.comap (Ideal.Quotient.mk r) q' = q := Ideal.comap_map_mk hrq
  have hcomapLO : (Ideal.comap (Ideal.Quotient.mk r) q').LiesOver p := by
    rw [hcomap]
    infer_instance
  have hcomapPrime : (Ideal.comap (Ideal.Quotient.mk r) q').IsPrime := by
    rw [hcomap]
    infer_instance
  have hp'eq : p' = (Ideal.under R q).map (Ideal.Quotient.mk I) :=
    Ideal.under_map_quotientMk r q hrq
  have hp'LO : p'.LiesOver p := by
    rw [hp'eq]
    exact liesOver_map_quotientMk_under r q hrq
  let algpq' := Ideal.ResidueField.algebraOfLiesOver p q'
  let algpp' := Ideal.ResidueField.algebraOfLiesOver p p'
  let algp'q' := Ideal.ResidueField.algebraOfLiesOver p' q'
  -- the residue field of `q` is that of the image of `q` in `S ⧸ r`
  have htop : Cardinal.toNat (@Algebra.trdeg p.ResidueField q.ResidueField _ _
        (Ideal.ResidueField.algebraOfLiesOver p q))
      = Cardinal.toNat (Algebra.trdeg p.ResidueField q'.ResidueField) := by
    refine Eq.trans ?_ (congrArg Cardinal.toNat
      (resfield_trdeg_comap_eq (A := R) (Ideal.Quotient.mk r)
        Ideal.Quotient.mk_surjective rfl p q'))
    exact Ideal.toNat_trdeg_residue_congr p p q (Ideal.comap (Ideal.Quotient.mk r) q') rfl
      hcomap.symm
  -- the base `κ(q ∩ R)` may be replaced by the residue field of its image in `R ⧸ (r ∩ R)`
  have htower : IsScalarTower p.ResidueField p'.ResidueField q'.ResidueField := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    have hcompose : (algebraMap (R ⧸ I) (S ⧸ r)).comp (algebraMap R (R ⧸ I))
        = algebraMap R (S ⧸ r) := (IsScalarTower.algebraMap_eq R (R ⧸ I) (S ⧸ r)).symm
    change Ideal.ResidueField.map p q' (algebraMap R (S ⧸ r)) Ideal.LiesOver.over
      = (Ideal.ResidueField.map p' q' (algebraMap (R ⧸ I) (S ⧸ r)) Ideal.LiesOver.over).comp
          (Ideal.ResidueField.map p p' (algebraMap R (R ⧸ I)) Ideal.LiesOver.over)
    rw [residueField_map_comp p p' q' (algebraMap R (R ⧸ I)) (algebraMap (R ⧸ I) (S ⧸ r))
      Ideal.LiesOver.over Ideal.LiesOver.over (by rw [hcompose]; exact Ideal.LiesOver.over)]
    exact residueField_map_congr p q' _ _ hcompose.symm _ _
  have hsurj : Function.Surjective (algebraMap p.ResidueField p'.ResidueField) :=
    residueField_map_surjective p p' (algebraMap R (R ⧸ I)) Ideal.LiesOver.over
      Ideal.Quotient.mk_surjective
  rw [htop]
  simpa using congrArg Cardinal.toNat <| lift_trdeg_eq_of_surjective_base
    (K := p.ResidueField) (K' := p'.ResidueField) (L := q'.ResidueField) hsurj

end Transport

/-- **The dimension formula at a point of a finite-type algebra, without integrality.** Let `S`
be an algebra of finite type over a Noetherian ring `R`, let `q` be a prime of `S` and
`p = q ∩ R`. If `E` bounds the transcendence degree of the residue field extension
`κ(r)/κ(r ∩ R)` at every minimal prime `r` of `S` contained in `q`, then

`height q + trdeg_{κ(p)} κ(q) ≤ height p + E`.

This is the ring-theoretic content of the dimension formula for a morphism locally of finite
type to a locally Noetherian scheme, in the form that drops the integrality assumptions of
`height_add_trdeg_residue_le`. -/
theorem height_add_trdeg_residue_le_of_forall_minimalPrimes [IsNoetherianRing R]
    [Algebra.FiniteType R S] (p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsPrime] [q.LiesOver p]
    (E : ℕ∞)
    (hE : ∀ (r : Ideal S) [r.IsPrime], r ∈ minimalPrimes S → r ≤ q →
      (Ideal.underResidueTrdeg R r : ℕ∞) ≤ E) :
    letI := Ideal.ResidueField.algebraOfLiesOver p q
    q.height + (Cardinal.toNat (Algebra.trdeg p.ResidueField q.ResidueField) : ℕ∞)
      ≤ p.height + E := by
  obtain rfl : p = Ideal.under R q := Ideal.LiesOver.over
  let := Ideal.ResidueField.algebraOfLiesOver (Ideal.under R q) q
  refine ENat.add_le_of_forall_natCast_le fun n hn => ?_
  obtain ⟨r, hr, hrq, hn'⟩ := Ideal.exists_mem_minimalPrimes_le_height_map q hn
  have hrp : r.IsPrime := hr.isPrime
  have hIp : Ideal.under R r ≤ Ideal.under R q := Ideal.comap_mono hrq
  have hq'prime : (q.map (Ideal.Quotient.mk r)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hrq
  set I : Ideal R := Ideal.under R r
  set q' : Ideal (S ⧸ r) := q.map (Ideal.Quotient.mk r)
  set p' : Ideal (R ⧸ I) := Ideal.under (R ⧸ I) q' with hp'def
  -- the quotients are domains, finite type, and the extension is injective
  have : Algebra.FiniteType R (S ⧸ r) :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType R S)
      (Algebra.FiniteType.quotient S r)
  have : Algebra.FiniteType (R ⧸ I) (S ⧸ r) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (R ⧸ I) (S ⧸ r)
  have hinj : Function.Injective (algebraMap (R ⧸ I) (S ⧸ r)) :=
    Ideal.quotientMap_injective' (I := r) (J := I) (f := algebraMap R S) (H := le_rfl) le_rfl
  let := Ideal.ResidueField.algebraOfLiesOver p' q'
  -- the integral dimension formula on the quotients
  have hformula := height_add_trdeg_residue_le hinj p' q'
  -- the three identifications
  have hres : Cardinal.toNat (Algebra.trdeg (Ideal.under R q).ResidueField q.ResidueField)
      = Cardinal.toNat (Algebra.trdeg p'.ResidueField q'.ResidueField) :=
    toNat_trdeg_residue_map_quotientMk_eq (R := R) r q hrq
  have hheight : p'.height ≤ (Ideal.under R q).height := by
    rw [hp'def, Ideal.under_map_quotientMk r q hrq]
    exact le_trans le_self_add (height_map_quotient_add_height_le I (Ideal.under R q) hIp)
  have htrdeg : (Cardinal.toNat (Algebra.trdeg (R ⧸ I) (S ⧸ r)) : ℕ∞) ≤ E := by
    rw [← Ideal.underResidueTrdeg_eq_toNat_trdeg_quotient (R := R) r]
    exact hE r hr hrq
  calc (n : ℕ∞)
        + (Cardinal.toNat (Algebra.trdeg (Ideal.under R q).ResidueField q.ResidueField) : ℕ∞)
      ≤ q'.height + (Cardinal.toNat (Algebra.trdeg p'.ResidueField q'.ResidueField) : ℕ∞) := by
        rw [hres]
        exact add_le_add hn' le_rfl
    _ ≤ p'.height + (Cardinal.toNat (Algebra.trdeg (R ⧸ I) (S ⧸ r)) : ℕ∞) := hformula
    _ ≤ (Ideal.under R q).height + E := add_le_add hheight htrdeg

end
