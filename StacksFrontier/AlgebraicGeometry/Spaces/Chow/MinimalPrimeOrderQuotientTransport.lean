module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaChart.MinimalPrimeOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorRationalEquivalence

/-!
# The order of vanishing along a branch under a surjection of local rings

Let `π : O → O'` be a surjection of Noetherian local rings of dimension at most one carrying
nonzerodivisors to nonzerodivisors — the shape of the map of local rings of a closed immersion of
schemes at a point of the closed subscheme. This file transports `Ring.minimalPrimeOrd`, the
order of vanishing along a branch, along `π`.

Contraction along `π` is a bijection from the minimal primes of `O'` onto the primes of `O`
minimal over `ker π`. Whether those are minimal primes of `O` is extra information about `π`,
taken here as a hypothesis; geometrically it says that the irreducible components of the closed
subscheme are irreducible components of the ambient scheme.

## Main definitions

* `Ring.quotientComapEquivOfComap`: the isomorphism `O/π^{-1}(J) ≃ O'/J` induced by a surjection
  `π : O → O'`.
* `Ring.comapMinimalPrimesEquiv`: contraction along `π` as a bijection from the minimal primes of
  `O'` onto the minimal primes of `O` containing `ker π`, given that contraction lands in the
  minimal primes.

## Main results

* `Ring.minimalPrimeOrd_map_of_surjective`: the termwise equality
  `ord_𝔮(π(f)) = ord_{π^{-1}(𝔮)}(f)`.
* `Ring.finsum_minimalPrimeOrd_map_of_surjective`: the sum over the branches of `O'`,
  `∑_{𝔮 ⊂ O' minimal} ord_𝔮(π(f)) = ∑_{𝔭 ⊂ O minimal, ker π ≤ 𝔭} ord_𝔭(f)`.

Geometrically, the sum of Stacks 02QG over the minimal primes of the local ring of a chart of an
irreducible component `X'` is the subsum, over the branches lying on `X'`, of the sum over all the
branches on the ambient chart (Stacks 0EQ2).

## References

* [Stacks Project, Tag 02QG](https://stacks.math.columbia.edu/tag/02QG)
* [Stacks Project, Tag 0EQ2](https://stacks.math.columbia.edu/tag/0EQ2)
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors

universe u

namespace Ring

/-! ### The isomorphism of quotients induced by a surjection -/

section QuotientEquiv

variable {O O' : Type u} [CommRing O] [CommRing O']

/-- The isomorphism `O/π^{-1}(J) ≃ O'/J` induced by a surjection `π : O → O'` and an ideal `J` of
`O'`: the composite `O → O' → O'/J` is surjective with kernel `π^{-1}(J)`. -/
def quotientComapEquivOfComap (π : O →+* O') (hsurj : Function.Surjective π) (J : Ideal O') :
    (O ⧸ Ideal.comap π J) ≃+* (O' ⧸ J) :=
  (Ideal.quotEquivOfEq (by
      ext x
      simp [RingHom.mem_ker, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem])).trans
    (RingHom.quotientKerEquivOfSurjective
      (f := (Ideal.Quotient.mk J).comp π) (Ideal.Quotient.mk_surjective.comp hsurj))

/-- `Ring.quotientComapEquivOfComap` sends the class of `x` to the class of `π x`. -/
@[simp]
theorem quotientComapEquivOfComap_mk (π : O →+* O') (hsurj : Function.Surjective π) (J : Ideal O')
    (x : O) :
    quotientComapEquivOfComap π hsurj J (Ideal.Quotient.mk (Ideal.comap π J) x) =
      Ideal.Quotient.mk J (π x) := by
  simp [quotientComapEquivOfComap]

end QuotientEquiv

/-! ### The order of vanishing along a branch under a surjection -/

section Transport

variable {O O' : Type u} [CommRing O] [CommRing O']
    {K : Type u} [CommRing K] [Algebra O K] [IsFractionRing O K]
    {K' : Type u} [CommRing K'] [Algebra O' K'] [IsFractionRing O' K']

/-- The order of vanishing along a branch is unchanged by a surjection of local rings. Let
`π : O → O'` be a surjection of Noetherian local rings of dimension at most one carrying
nonzerodivisors to nonzerodivisors, let `𝔮` be a minimal prime of `O'` and let `𝔭 = π^{-1}(𝔮)`,
assumed to be a minimal prime of `O`. Then for a unit `f` of the total ring of fractions of `O`

`ord_𝔮(π(f)) = ord_𝔭(f)`,

both orders of vanishing being `Ring.minimalPrimeOrd`. -/
theorem minimalPrimeOrd_map_of_surjective [IsLocalRing O]
    [IsNoetherianRing O] [Ring.KrullDimLE 1 O]
    [IsNoetherianRing O'] [Ring.KrullDimLE 1 O']
    (π : O →+* O') (hsurj : Function.Surjective π) (hnzd : O⁰ ≤ O'⁰.comap π)
    (q : minimalPrimes O') (p : minimalPrimes O)
    (hpq : (p : Ideal O) = Ideal.comap π (q : Ideal O')) (f : K) (hf : IsUnit f) :
    minimalPrimeOrd q (IsLocalization.map (S := K) K' π hnzd f) (hf.map _) =
      minimalPrimeOrd p f hf := by
  have hqp : (q : Ideal O').IsPrime := q.2.1.1
  have hpp : (p : Ideal O).IsPrime := p.2.1.1
  have : Nontrivial O' := ⟨⟨0, 1, fun h => hqp.ne_top (Ideal.eq_top_of_isUnit_mem _
    (h ▸ (q : Ideal O').zero_mem) isUnit_one)⟩⟩
  have : IsLocalRing O' := IsLocalRing.of_surjective' π hsurj
  have : IsLocalRing (O ⧸ (p : Ideal O)) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have : IsLocalRing (O' ⧸ (q : Ideal O')) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have := krullDimLE_one_quotient (O := O) (p : Ideal O)
  have := krullDimLE_one_quotient (O := O') (q : Ideal O')
  set e : (O ⧸ (p : Ideal O)) ≃+* (O' ⧸ (q : Ideal O')) :=
    (Ideal.quotEquivOfEq hpq).trans (quotientComapEquivOfComap π hsurj (q : Ideal O')) with hedef
  have hemk : ∀ x : O, e (Ideal.Quotient.mk (p : Ideal O) x) =
      Ideal.Quotient.mk (q : Ideal O') (π x) := fun x => by
    rw [hedef]
    simpa using quotientComapEquivOfComap_mk π hsurj (q : Ideal O') x
  have hcomm : (minimalPrimeFractionMap (K := K') q).comp
        (IsLocalization.map (S := K) K' π hnzd) =
      (IsFractionRing.ringEquivOfRingEquiv
          (A := O ⧸ (p : Ideal O)) (K := FractionRing (O ⧸ (p : Ideal O)))
          (B := O' ⧸ (q : Ideal O')) (L := FractionRing (O' ⧸ (q : Ideal O')))
          e : FractionRing (O ⧸ (p : Ideal O)) →+* FractionRing (O' ⧸ (q : Ideal O'))).comp
        (minimalPrimeFractionMap (K := K) p) := by
    refine IsLocalization.ringHom_ext O⁰ (RingHom.ext fun x => ?_)
    simp only [RingHom.coe_comp, Function.comp_apply, IsLocalization.map_eq,
      minimalPrimeFractionMap, RingHom.coe_coe]
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap, hemk]
  have hmain := Ring.ordTotalFracInt_ringEquivOfRingEquiv
    (KA := FractionRing (O ⧸ (p : Ideal O))) (KB := FractionRing (O' ⧸ (q : Ideal O'))) e
    (minimalPrimeFractionMap (K := K) p f) (hf.map _)
  rw [minimalPrimeOrd, minimalPrimeOrd, ← hmain]
  exact ordTotalFracInt_congr _ _ _ (RingHom.congr_fun hcomm f)

end Transport

/-! ### Contraction as a bijection on minimal primes -/

section Index

variable {O O' : Type u} [CommRing O] [CommRing O']

/-- Contraction along a surjection is a bijection on minimal primes: for a surjective ring
homomorphism `π : O → O'` under which the minimal primes of `O'` contract to minimal primes of
`O`, contraction is a bijection from the minimal primes of `O'` onto the minimal primes of `O`
containing `ker π`. -/
def comapMinimalPrimesEquiv (π : O →+* O') (hsurj : Function.Surjective π)
    (hmin : ∀ J ∈ minimalPrimes O', Ideal.comap π J ∈ minimalPrimes O) :
    minimalPrimes O' ≃ {p : minimalPrimes O // RingHom.ker π ≤ (p : Ideal O)} := by
  refine Equiv.ofBijective
    (fun q => ⟨⟨Ideal.comap π (q : Ideal O'), hmin _ q.2⟩, fun x hx =>
      Ideal.mem_comap.2 (RingHom.mem_ker.1 hx ▸ (q : Ideal O').zero_mem)⟩) ⟨?_, ?_⟩
  · intro q₁ q₂ h
    exact Subtype.ext (Ideal.comap_injective_of_surjective π hsurj
      (congrArg (fun r : {p : minimalPrimes O // RingHom.ker π ≤ (p : Ideal O)} =>
        ((r.1 : minimalPrimes O) : Ideal O)) h))
  · intro p
    set p' : Ideal O := ((p.1 : minimalPrimes O) : Ideal O) with hp'
    have hpp : p'.IsPrime := p.1.2.1.1
    have hJ : (Ideal.map π p').IsPrime := Ideal.map_isPrime_of_surjective hsurj p.2
    have hcomap : Ideal.comap π (Ideal.map π p') = p' := by
      rw [Ideal.comap_map_of_surjective' π hsurj, sup_eq_left.2 p.2]
    refine ⟨⟨Ideal.map π p', ⟨hJ, bot_le⟩, fun J hJ' hle => ?_⟩,
      Subtype.ext (Subtype.ext hcomap)⟩
    have hJp : J.IsPrime := hJ'.1
    have h1 : Ideal.comap π J ≤ p' := hcomap ▸ Ideal.comap_mono hle
    have h2 : p' ≤ Ideal.comap π J := p.1.2.2 ⟨inferInstance, bot_le⟩ h1
    exact le_of_eq (Ideal.comap_injective_of_surjective π hsurj
      ((le_antisymm h1 h2).trans hcomap.symm)).symm

/-- `Ring.comapMinimalPrimesEquiv` sends a minimal prime `𝔮` of `O'` to `π^{-1}(𝔮)`. -/
@[simp]
theorem coe_comapMinimalPrimesEquiv (π : O →+* O') (hsurj : Function.Surjective π)
    (hmin : ∀ J ∈ minimalPrimes O', Ideal.comap π J ∈ minimalPrimes O) (q : minimalPrimes O') :
    (((comapMinimalPrimesEquiv π hsurj hmin q).1 : minimalPrimes O) : Ideal O) =
      Ideal.comap π (q : Ideal O') :=
  rfl

end Index

/-! ### The sum over the branches of a quotient -/

section Sum

variable {O O' : Type u} [CommRing O] [CommRing O']
    {K : Type u} [CommRing K] [Algebra O K] [IsFractionRing O K]
    {K' : Type u} [CommRing K'] [Algebra O' K'] [IsFractionRing O' K']

/-- The sum of the orders of vanishing over the branches of a quotient is the subsum over the
branches containing the kernel. Let `π : O → O'` be a surjection of Noetherian local rings of
dimension at most one carrying nonzerodivisors to nonzerodivisors, and suppose the minimal primes
of `O'` contract to minimal primes of `O` — which geometrically says that the irreducible
components of the closed subscheme `Spec O'` are irreducible components of `Spec O`. Then for a
unit `f` of the total ring of fractions of `O`

`∑_{𝔮 ⊂ O' minimal} ord_𝔮(π(f)) = ∑_{𝔭 ⊂ O minimal, ker π ≤ 𝔭} ord_𝔭(f)`. -/
theorem finsum_minimalPrimeOrd_map_of_surjective [IsLocalRing O]
    [IsNoetherianRing O] [Ring.KrullDimLE 1 O]
    [IsNoetherianRing O'] [Ring.KrullDimLE 1 O']
    (π : O →+* O') (hsurj : Function.Surjective π) (hnzd : O⁰ ≤ O'⁰.comap π)
    (hmin : ∀ J ∈ minimalPrimes O', Ideal.comap π J ∈ minimalPrimes O)
    (f : K) (hf : IsUnit f) :
    ∑ᶠ q : minimalPrimes O',
        minimalPrimeOrd q (IsLocalization.map (S := K) K' π hnzd f) (hf.map _) =
      ∑ᶠ p : {p : minimalPrimes O // RingHom.ker π ≤ (p : Ideal O)},
        minimalPrimeOrd p.1 f hf :=
  finsum_eq_of_bijective (comapMinimalPrimesEquiv π hsurj hmin)
    (comapMinimalPrimesEquiv π hsurj hmin).bijective fun q =>
      minimalPrimeOrd_map_of_surjective (K := K) (K' := K') π hsurj hnzd q _
        (coe_comapMinimalPrimesEquiv π hsurj hmin q) f hf

end Sum

end Ring

end
