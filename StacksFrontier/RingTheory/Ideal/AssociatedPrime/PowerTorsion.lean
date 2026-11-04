module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import StacksFrontier.Algebra.Module.IPowerTorsion

/-!
# Associated primes of the quotient by ideal-power torsion

Let `A` be a Noetherian ring, `M` an `A`-module and `J ⊆ A` an ideal, and write
`M[J^∞] = Ideal.primaryComponent M J` for the submodule of `J`-power torsion elements, that is
the sections of `M` supported on `V(J)`. Then

`Ass(M / M[J^∞]) = Ass(M) \ V(J)`,

the associated primes of `M` that do not contain `J`.

Both inclusions rest on one device. If `p = (M[J^∞] : x)` is prime, then `p · x` lies in `M[J^∞]`
and, `p` being finitely generated, a single power `J^n` annihilates it. So `p` cannot contain `J`,
as `J^{n+1}` would then annihilate `x` itself, and for `f ∈ J \ p` the element `f^n · x`
of `M` has annihilator exactly `p`. Conversely, if `Ann(x) = p` is prime and does not contain
`J`, then `(M[J^∞] : x) = p` as well, because `a · x ∈ M[J^∞]` forces `g^k a · x = 0` for a
`g ∈ J \ p` and hence `a ∈ p`.

## Main results

* `associatedPrimes_quotient_primaryComponent`: over a Noetherian ring,
  `Ass(M/M[J^∞]) = Ass(M) \ V(J)`.

## Implementation notes

No finiteness of `M` is needed: the only finiteness used is that of the associated prime `p`
itself, which `A` Noetherian supplies.

This is not the content of [Stacks, Tag 0AW0], whose two parts compare the local cohomology of
`M`, of `M[J^∞]` and of `M/M[J^∞]` and are formalized in
`StacksFrontier/RingTheory/Dualizing/TorsionQuotient.lean`, which carries seven of the tag's eight
clause registrations and the conjunction `Stacks.Duality.localCohomology_divide_by_torsion`
carrying it whole, and in `StacksFrontier/AlgebraicGeometry/Duality/DivideByTorsion.lean`, which
carries the eighth; the statement here is
the consequence of that tag which the proof of [Stacks, Tag 0EG2] invokes in order to cut `M`
down to a module with a prescribed single associated prime. It therefore carries no `stacks`
attribute.

## References

* [Stacks Project, Tag 0AW0](https://stacks.math.columbia.edu/tag/0AW0)
* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
-/

@[expose] public section

universe u v

/-- If a finitely generated ideal `p` moves `x` into the `J`-power torsion submodule of `M`, then
a single power of `J` annihilates all of `p · x`. -/
theorem exists_pow_smul_eq_zero_of_smul_mem_primaryComponent
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    (J : Ideal A) {p : Ideal A} (hp : p.FG) {x : M}
    (hpx : ∀ a ∈ p, a • x ∈ Ideal.primaryComponent M J) :
    ∃ n : ℕ, ∀ a ∈ p, ∀ c ∈ J ^ n, c • (a • x) = 0 := by
  classical
  obtain ⟨t, ht⟩ := hp
  have hgen : ∀ a ∈ (t : Set A), ∃ m : ℕ, ∀ c ∈ J ^ m, c • (a • x) = 0 := by
    intro a ha
    obtain ⟨m, hm⟩ := (Ideal.primaryComponent_mem M J (a • x)).mp
      (hpx a (ht ▸ Ideal.subset_span ha))
    exact ⟨m, fun c hc => (Submodule.mem_torsionBySet_iff _ _).mp hm ⟨c, hc⟩⟩
  choose! e he using hgen
  refine ⟨t.sup e, fun a ha c hc => ?_⟩
  rw [← ht] at ha
  induction ha using Submodule.span_induction with
  | mem y hy => exact he y hy c (Ideal.pow_le_pow_right (Finset.le_sup (f := e) hy) hc)
  | zero => simp
  | add y z _ _ hy hz => rw [add_smul, smul_add, hy, hz, add_zero]
  | smul r y _ hy => rw [smul_eq_mul, mul_smul, smul_comm, hy, smul_zero]

/-- If a prime `p` contains `f ^ n * b` but not `f`, then it contains `b`. -/
private theorem mem_of_pow_mul_mem {A : Type u} [CommRing A] {p : Ideal A} (hp : p.IsPrime)
    {f : A} (hf : f ∉ p) (n : ℕ) {b : A} (h : f ^ n * b ∈ p) : b ∈ p :=
  (hp.mem_or_mem h).resolve_left fun h => hf (hp.mem_of_pow_mem n h)

/-- **Associated primes of the quotient by ideal-power torsion.** Over a Noetherian ring `A`, the
associated primes of `M / M[J^∞]` are exactly the associated primes of `M` that do not contain
the ideal `J`. -/
theorem associatedPrimes_quotient_primaryComponent
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (M : Type v) [AddCommGroup M] [Module A M] (J : Ideal A) :
    associatedPrimes A (M ⧸ Ideal.primaryComponent M J) =
      associatedPrimes A M \ {p | J ≤ p} := by
  ext p
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, AssociatedPrimes.mem_iff, isAssociatedPrime_iff]
  constructor
  · rintro ⟨hp, q, hq⟩
    obtain ⟨x, rfl⟩ := (Ideal.primaryComponent M J).mkQ_surjective q
    have hpx : ∀ a : A, a ∈ p ↔ a • x ∈ Ideal.primaryComponent M J := fun a => by
      rw [hq, Submodule.mem_colon_singleton, Submodule.mem_bot, ← map_smul,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_smul_mem_primaryComponent J
      (Ideal.fg_of_isNoetherianRing p) fun a ha => (hpx a).mp ha
    have hJp : ¬ J ≤ p := fun hJ =>
      hp.ne_top ((Ideal.eq_top_iff_one p).mpr ((hpx 1).mpr (by
        simpa using mem_primaryComponent_of_smul_mem J (Ideal.fg_of_isNoetherianRing J) x
          fun a ha => (hpx a).mp (hJ ha))))
    obtain ⟨f, hfJ, hfp⟩ := SetLike.not_le_iff_exists.mp hJp
    refine ⟨⟨hp, f ^ n • x, ?_⟩, hJp⟩
    ext b
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_comm]
    refine ⟨fun hb => hn b hb _ (Ideal.pow_mem_pow hfJ n), fun hb => ?_⟩
    exact mem_of_pow_mul_mem hp hfp n ((hpx _).mpr (by rw [mul_smul, hb]; exact zero_mem _))
  · rintro ⟨⟨hp, x, hx⟩, hJp⟩
    obtain ⟨g, hgJ, hgp⟩ := SetLike.not_le_iff_exists.mp hJp
    have hax : ∀ a : A, a ∈ p ↔ a • x = 0 := fun a => by
      rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot]
    refine ⟨hp, (Ideal.primaryComponent M J).mkQ x, ?_⟩
    ext a
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, ← map_smul,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine ⟨fun ha => by rw [(hax a).mp ha]; exact zero_mem _, fun ha => ?_⟩
    obtain ⟨k, hk⟩ := (Ideal.primaryComponent_mem M J (a • x)).mp ha
    have hgk : g ^ k • (a • x) = 0 :=
      (Submodule.mem_torsionBySet_iff _ _).mp hk ⟨g ^ k, Ideal.pow_mem_pow hgJ k⟩
    exact mem_of_pow_mul_mem hp hgp k ((hax _).mpr (by rw [mul_smul]; exact hgk))

end
