module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.TotalFractionRing
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Vanishing
public import StacksFrontier.RingTheory.Length.ColengthAdditivity
public import StacksFrontier.RingTheory.Nagata.MonogenicN1

/-!
# The delta invariant of a local ring bounds those of its minimal-prime quotients

Let `A` be a reduced ring with finitely many minimal primes. Its normalization factors as

`A → ∏ A ⧸ p → ∏ (A ⧸ p)^ν`,

the product being over the minimal primes, the second map being injective and the composite
being the canonical map into the integral closure of `A` in its total ring of fractions. Colength
is additive along such a factorization, so the delta invariant of `A` is the colength of the
first map plus the colength of the second. If `A` is moreover local with at least two minimal
primes, the first map is not surjective, so its colength is at least one; hence a delta invariant
equal to one leaves nothing for the second map, and every minimal-prime quotient of `A` is
already integrally closed in its fraction field.

## Main results

* `Ring.deltaInvariant_quotient_minimalPrimes_eq_zero_of_deltaInvariant_eq_one` — a reduced local
  ring with finitely many minimal primes, at least two of them, and delta invariant one has
  delta invariant zero at every minimal-prime quotient.

## Implementation notes

The three ingredients are already available and only have to be put together. The product
decomposition of the integral closure is
`minimalPrimes.integralClosure_fractionRing_algEquiv_pi_quotient`, an `A`-algebra equivalence,
which is what lets the delta invariant of `A` — a length over `A` — be read on the product.
Additivity of colength is `Module.length_quotient_range_comp`, which holds in `ℕ∞` with no
finiteness hypothesis; the consequence used here is
`Module.length_quotient_range_eq_zero_of_length_comp_eq_one`. Non-surjectivity of `A → ∏ A ⧸ p`
is `RingHom.not_surjective_pi_of_isLocalRing`, the idempotent argument.

The conclusion is drawn without any change of base ring, which is the one step a naive
formulation forces: the delta invariants of `A` and of `A ⧸ p` are lengths over two different
rings, but the length that comes out of the additivity is *zero*, and a length is zero exactly
when the module is subsingleton (`Module.length_eq_zero_iff`), a condition that does not mention
the ring at all. So the vanishing transports for free, and the statement proved here is about
`Ring.deltaInvariant (A ⧸ p)` itself rather than about a length over `A`.

## References

* [Stacks Project, Tag 0C3T](https://stacks.math.columbia.edu/tag/0C3T)
* [Stacks Project, Tag 035P](https://stacks.math.columbia.edu/tag/035P)
-/

@[expose] public section

universe u

namespace Ring

/-- **A reduced local ring of delta invariant one with at least two minimal primes has
integrally closed minimal-prime quotients.** The normalization of `A` factors through
`∏ A ⧸ p`, the second factor being injective, so colength is additive along the factorization;
the first factor has colength at least one because a local ring does not surject onto a product
with two nontrivial factors, and a total colength of one therefore leaves the second factor
surjective. Surjectivity of the second factor is surjectivity of each `A ⧸ p → (A ⧸ p)^ν`, which
is the vanishing of the delta invariant of `A ⧸ p`. -/
public theorem deltaInvariant_quotient_minimalPrimes_eq_zero_of_deltaInvariant_eq_one
    (A : Type u) [CommRing A] [IsLocalRing A] [IsReduced A]
    (hA : (minimalPrimes A).Finite)
    {p q : minimalPrimes A} (hpq : p ≠ q)
    (hδ : Ring.deltaInvariant A = 1) (r : minimalPrimes A) :
    Ring.deltaInvariant (A ⧸ (r : Ideal A)) = 0 := by
  classical
  have hfin : Finite (minimalPrimes A) := hA
  have hprime : ∀ s : minimalPrimes A, (s : Ideal A).IsPrime := fun s => s.property.left.left
  have hdomain : ∀ s : minimalPrimes A, IsDomain (A ⧸ (s : Ideal A)) := fun s =>
    Ideal.Quotient.isDomain (s : Ideal A)
  -- the `A`-algebra structures on the factors, exactly as in the product decomposition
  let (s : minimalPrimes A) : Algebra A (FractionRing (A ⧸ (s : Ideal A))) :=
    ((algebraMap (A ⧸ (s : Ideal A)) (FractionRing (A ⧸ (s : Ideal A)))).comp
      (Ideal.Quotient.mk (s : Ideal A))).toAlgebra
  let (s : minimalPrimes A) : Algebra A
      (integralClosure (A ⧸ (s : Ideal A)) (FractionRing (A ⧸ (s : Ideal A)))) :=
    ((algebraMap (A ⧸ (s : Ideal A))
      (integralClosure (A ⧸ (s : Ideal A)) (FractionRing (A ⧸ (s : Ideal A))))).comp
        (Ideal.Quotient.mk (s : Ideal A))).toAlgebra
  obtain ⟨e⟩ := minimalPrimes.integralClosure_fractionRing_algEquiv_pi_quotient (A := A) hA
  -- the two factors of the normalization
  let f : A →ₗ[A] (∀ s : minimalPrimes A, A ⧸ (s : Ideal A)) :=
    Algebra.linearMap A (∀ s : minimalPrimes A, A ⧸ (s : Ideal A))
  let g : (∀ s : minimalPrimes A, A ⧸ (s : Ideal A)) →ₗ[A]
      (∀ s : minimalPrimes A,
        integralClosure (A ⧸ (s : Ideal A)) (FractionRing (A ⧸ (s : Ideal A)))) :=
    { toFun := fun x s => algebraMap (A ⧸ (s : Ideal A))
        (integralClosure (A ⧸ (s : Ideal A)) (FractionRing (A ⧸ (s : Ideal A)))) (x s)
      map_add' := fun x y => funext fun s => map_add _ _ _
      map_smul' := fun a x => by
        funext s
        simp only [RingHom.id_apply, Pi.smul_apply, Algebra.smul_def, map_mul]
        rfl }
  -- the second factor is injective, because `A ⧸ p` sits inside its fraction field
  have hcompinj : ∀ s : minimalPrimes A, Function.Injective
      (algebraMap (A ⧸ (s : Ideal A))
        (integralClosure (A ⧸ (s : Ideal A)) (FractionRing (A ⧸ (s : Ideal A))))) := by
    intro s x y hxy
    have := hdomain s
    exact IsFractionRing.injective (A ⧸ (s : Ideal A)) (FractionRing (A ⧸ (s : Ideal A)))
      (congrArg Subtype.val hxy)
  have hginj : Function.Injective g := fun x y hxy =>
    funext fun s => hcompinj s (congrFun hxy s)
  -- the composite is the canonical map into the product
  have hgf : g ∘ₗ f = Algebra.linearMap A
      (∀ s : minimalPrimes A,
        integralClosure (A ⧸ (s : Ideal A)) (FractionRing (A ⧸ (s : Ideal A)))) :=
    LinearMap.ext fun _ => rfl
  -- the delta invariant of `A`, read on the product
  have hrange : Submodule.map e.toLinearEquiv.toLinearMap
      (LinearMap.range (Algebra.linearMap A (integralClosure A (FractionRing A)))) =
      LinearMap.range (Algebra.linearMap A
        (∀ s : minimalPrimes A,
          integralClosure (A ⧸ (s : Ideal A)) (FractionRing (A ⧸ (s : Ideal A))))) := by
    rw [← LinearMap.range_comp]
    congr 1
    exact LinearMap.ext fun a => e.commutes a
  have hone : Module.length A
      ((∀ s : minimalPrimes A,
        integralClosure (A ⧸ (s : Ideal A)) (FractionRing (A ⧸ (s : Ideal A)))) ⧸
          LinearMap.range (g ∘ₗ f)) = 1 := by
    rw [hgf, ← (Submodule.Quotient.equiv _ _ e.toLinearEquiv hrange).length_eq]
    exact hδ
  -- the first factor is not surjective, `A` being local with two minimal primes
  have hfns : ¬ Function.Surjective f := RingHom.not_surjective_pi_of_isLocalRing
    (algebraMap A (∀ s : minimalPrimes A, A ⧸ (s : Ideal A))) p q hpq
  -- so the second factor is surjective
  have hgtop : LinearMap.range g = ⊤ :=
    Submodule.Quotient.subsingleton_iff.mp (Module.length_eq_zero_iff.mp
      (Module.length_quotient_range_eq_zero_of_length_comp_eq_one f g hginj hfns hone))
  have hrsurj : Function.Surjective
      (algebraMap (A ⧸ (r : Ideal A))
        (integralClosure (A ⧸ (r : Ideal A)) (FractionRing (A ⧸ (r : Ideal A))))) := by
    intro y
    obtain ⟨x, hx⟩ := LinearMap.range_eq_top.mp hgtop (Pi.single r y)
    have h := congrFun hx r
    rw [Pi.single_eq_same] at h
    exact ⟨x r, h⟩
  -- which is the vanishing of the delta invariant of `A ⧸ r`
  rw [Ring.deltaInvariant, LinearMap.range_eq_top.mpr hrsurj]
  exact Module.length_eq_zero_iff.mpr (Submodule.Quotient.subsingleton_iff.mpr rfl)

/-- **The minimal-prime quotients of a one-dimensional reduced local Nagata ring of delta
invariant one with at least two minimal primes are discrete valuation rings.** The delta
invariant of each quotient vanishes by
`Ring.deltaInvariant_quotient_minimalPrimes_eq_zero_of_deltaInvariant_eq_one`, and a reduced
one-dimensional Nagata local ring of vanishing delta invariant is a discrete valuation ring by
Tag 0C3U. The quotient is a domain, hence reduced, and Nagata by
`MonogenicN1.isNagataRing_quotient`; only its dimension has to be supplied, since nothing about
a minimal prime of `A` by itself says the quotient is again one-dimensional. -/
public theorem isDiscreteValuationRing_quotient_minimalPrimes_of_deltaInvariant_eq_one
    (A : Type u) [CommRing A] [IsLocalRing A] [IsReduced A]
    (hA : IsNagataRing A) (hfin : (minimalPrimes A).Finite)
    {p q : minimalPrimes A} (hpq : p ≠ q)
    (hδ : Ring.deltaInvariant A = 1) (r : minimalPrimes A)
    (hdim : ringKrullDim (A ⧸ (r : Ideal A)) = 1) :
    ∃ _ : IsDomain (A ⧸ (r : Ideal A)), IsDiscreteValuationRing (A ⧸ (r : Ideal A)) := by
  have hprime : (r : Ideal A).IsPrime := r.property.left.left
  have hdom : IsDomain (A ⧸ (r : Ideal A)) := Ideal.Quotient.isDomain (r : Ideal A)
  have hloc : IsLocalRing (A ⧸ (r : Ideal A)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (r : Ideal A)) Ideal.Quotient.mk_surjective
  exact (Ring.deltaInvariant_eq_zero_iff_isDiscreteValuationRing
    (MonogenicN1.isNagataRing_quotient hA (r : Ideal A)) hdim).mp <|
    deltaInvariant_quotient_minimalPrimes_eq_zero_of_deltaInvariant_eq_one A hfin hpq hδ r

end Ring

end
