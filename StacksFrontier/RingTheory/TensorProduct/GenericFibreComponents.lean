module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import StacksFrontier.RingTheory.Norm.BaseChangeProduct
public import StacksFrontier.RingTheory.TensorProduct.ReducedFractionRing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The components of a base change dominating the base, and the factors of a tensor product of
function fields

Let `A` be a domain with fraction field `K`, let `B` be a domain integral over `A` with `A → B`
injective and with fraction field `L`, and let `O` be a domain over `A` with fraction field `F`.
Geometrically: `Y = Spec A` and `X = Spec B` are integral with `X → Y` integral and dominant, so
`K = R(Y)` and `L = R(X)`; and `V = Spec O` is integral and dominates `Y`, so `F = R(V)`. The
base change is `U = V ×_Y X = Spec (O ⊗[A] B)`.

**The irreducible components of `U` which dominate `V` are the primes of `F ⊗[K] L`**, and the
factor of `F ⊗[K] L` at such a prime is the function field of the corresponding component.

This is the geometric half of the last step in the proof of **Stacks 0EQ4**, the half the source
does not state. The source states only the field-theoretic identity
`Nm_{L/K}(t) = ∏ᵢ Nm_{Mᵢ/M}(tᵢ)` for `M ⊗_K L = ∏ Mᵢ` — proved in this repository as
`Stacks.Norm.norm_baseChange_eq_prod_quotient`, at the point where the source writes "we omit
the proof" — and leaves implicit that the `Mᵢ` are the function fields of the components
`U_{j,i}` of `U = V ×_Y X` dominating the branch `V_j` of the étale chart. This file supplies
that dictionary and combines the two halves in
`Stacks.GenericFibre.norm_eq_finprod_norm_quotient`.

## Main definitions

* `Stacks.GenericFibre.primeSpectrumEquivDominating`: the bijection between the primes of
  `F ⊗[K] L` and the primes of `O ⊗[A] B` contracting to the zero ideal of `O` — that is, the
  points of `U` dominating `V`. It sends a prime to its contraction.

## Main results

* `IsLocalization.algebraMapSubmonoid_nonZeroDivisors_of_isIntegral`: **the generic fibre of an
  integral extension of domains.** If `B` is a domain integral over the domain `A` with `A → B`
  injective, then the fraction field of `B` is already the localization of `B` at the nonzero
  elements of `A`; equivalently `K ⊗_A B = L`, so the fibre of `Spec B → Spec A` over the
  generic point is `Spec L`.
* `Ideal.disjoint_algebraMapSubmonoid_nonZeroDivisors_iff_under_eq_bot`: an ideal of an algebra
  over a domain misses the image of the nonzero elements of the base exactly when it contracts
  to the zero ideal.
* `Stacks.GenericFibre.isLocalization_tensorProduct`: `F ⊗[K] L` is the localization of
  `O ⊗[A] B` at the nonzero elements of `O`, i.e. `R(V) ⊗_{R(Y)} R(X)` is the ring of the
  generic fibre of `U → V`.
* `Stacks.GenericFibre.under_under_eq_bot_left`: the contraction of a prime of `F ⊗[K] L`
  contracts further to the zero ideal of `O`, i.e. the corresponding point of `U` dominates `V`.
* `Stacks.GenericFibre.under_mem_minimalPrimes`: that contraction is a *minimal* prime of
  `O ⊗[A] B`, that is the generic point of an irreducible component of `U`.
* `Stacks.GenericFibre.under_under_eq_bot_right`: that component dominates `X` as well as `V`.
* `Stacks.GenericFibre.isFractionRing_quotient_under`: **the factorwise identification.** The
  factor `(F ⊗[K] L)/p` is the function field of the component cut out by `p ∩ (O ⊗[A] B)`,
  i.e. the fraction field of `(O ⊗[A] B)/(p ∩ (O ⊗[A] B))`.
* `Stacks.GenericFibre.norm_eq_finprod_norm_quotient`: the omitted step of Stacks 0EQ4 with the
  product indexed by the components of `U` dominating `V`.

## Implementation notes

The shape of the conclusion is a **bijection of index sets together with a factorwise
isomorphism**, not a single ring isomorphism onto an abstract finite product. The consumer needs
each factor named as the function field of a *particular* component `U_{j,i}`, because the
factors of the product in Stacks 0EQ4 are the norms `g_{j,i} = Nm_{R(U_{j,i})/R(V_j)}(f_{j,i})`
of the individual extensions `R(U_{j,i})/R(V_j)`, and the scheme case of the lemma is applied to
each `U_{j,i} → V_j` separately. An isomorphism `F ⊗[K] L ≅ ∏ Mᵢ` onto an anonymous product
would not let one recognize `Mᵢ` as `R(U_{j,i})`; and the ring isomorphism onto the product of
the residue fields is in any case already available, inside
`Stacks.Norm.norm_eq_prod_quotient`. So what is proved here is the index bijection
`Stacks.GenericFibre.primeSpectrumEquivDominating` together with, for each index, the
identification `Stacks.GenericFibre.isFractionRing_quotient_under` of the factor with the
function field of the component.

**Hypotheses, and why each is needed.** `A`, `O`, `B` are domains with fraction fields `K`, `F`,
`L`; the map `A → B` is injective and `B` is *integral* over `A`. Integrality is what makes
`K ⊗_A B` a field, hence equal to `L`: for a merely affine dominant `X → Y` the ring of the
generic fibre is a proper subring of `R(X)` — already for `𝔸¹_K → Spec K`, where it is `K[t]`
and not `K(t)` — so the generic fibre is not `Spec R(X)` and the statement fails. `O` is *not*
assumed integral over `A`, nor étale, nor Noetherian: the chart `V → Y` of Stacks 0EQ4 is étale,
but only dominance of `V → Y` and integrality of the ring `O` are used, which is strictly
weaker. `Module.Finite K L` — that is `[R(X) : R(Y)] < ∞`, a hypothesis of Stacks 0EQ4 — is
needed from `Stacks.GenericFibre.under_mem_minimalPrimes` onwards, where `F ⊗[K] L` has to be
zero-dimensional: without it a prime of `F ⊗[K] L` need not be minimal, so its contraction need
not be an irreducible component, and `(F ⊗[K] L)/p` need not be a field. Separability of `F/K`,
which is what an étale chart supplies, is needed only for the norm identity, and enters only
through `Stacks.Norm.norm_baseChange_eq_prod_quotient`.

`O ⊗[A] B` is *not* assumed to be a domain, and is not one: `U = V ×_Y X` is reducible, and its
several components dominating `V` are exactly what is being counted.

The algebra structure on `F ⊗[K] L` over `O ⊗[A] B` is the one of
`tensorProductFractionRingAlgebra`, carried in the statements by a `letI` exactly as
`isLocalization_tensorProduct_fractionRing` does; that theorem, which presents `F ⊗[K] L` as the
localization of `O ⊗[A] B` at the nonzero elements of `O`, is the single input from which the
whole dictionary is read off, through `IsLocalization.orderIsoOfPrime`.

**What a geometric consumer still has to supply.** Everything here is stated for the rings, so a
consumer working with the étale chart of Stacks 0EQ4 has to present the situation affinely
first: an affine open `Spec A ⊆ Y` over which `X ⟶ Y` is finite, with `B = Γ(X, p⁻¹(Spec A))`;
the branch `V_j` of the chart as an integral affine scheme `Spec O` dominating `Spec A`; and the
identification `Γ(U) = O ⊗[A] B` of the base change. That presentation is the affine
base-change identification and is not proved here. The scheme-level dictionary between the
points of a fibre and the maximal spectrum of a pushforward stalk, which is the other half of
such a presentation, is in
`StacksFrontier.AlgebraicGeometry.Morphisms.Affine.FiberMaximalSpectrum` and
`StacksFrontier.AlgebraicGeometry.Morphisms.Integral.PushforwardStalkFibre`.

**No Stacks tag is claimed.** The source states the field-theoretic half only, and omits its
proof; the geometric half, identifying the factors with the function fields of the components,
is never stated there, so there is no tag for it.

## References

* [Stacks Project, Tag 0EQ4](https://stacks.math.columbia.edu/tag/0EQ4)
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors TensorProduct

/-! ### The generic fibre of an integral extension of domains -/

section GenericFibre

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **The generic fibre of an integral extension of domains.** Let `A` be a domain with fraction
field `K` and let `B` be a domain integral over `A` with `A → B` injective. Then a fraction
field `L` of `B` is already the localization of `B` at the image of the nonzero elements of `A`;
equivalently the canonical map `K ⊗_A B → L` is an isomorphism, so the fibre of
`Spec B → Spec A` over the generic point is `Spec L`.

Indeed `K ⊗_A B` is the localization of `B` at that image (`IsLocalization.tensorRight`); the
image consists of nonzerodivisors, so `K ⊗_A B` is a domain; and it is integral over the field
`K`, hence itself a field, so every nonzero element of `B` is already inverted in it. -/
theorem IsLocalization.algebraMapSubmonoid_nonZeroDivisors_of_isIntegral
    (A B : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]
    [FaithfulSMul A B] [Algebra.IsIntegral A B] (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K] (L : Type*) [CommRing L] [Algebra B L] [IsFractionRing B L] :
    IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L := by
  have hle : Algebra.algebraMapSubmonoid B A⁰ ≤ B⁰ := by
    rintro _ ⟨a, ha, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A B)).mpr
        (mem_nonZeroDivisors_iff_ne_zero.mp ha))
  have _ : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) (K ⊗[A] B) :=
    IsLocalization.tensorRight (A := K) (M := A⁰)
  have _ : IsDomain (K ⊗[A] B) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
  have hfield : IsField (K ⊗[A] B) := isField_of_isIntegral_of_isField' (Field.toIsField K)
  have hinj : Function.Injective (algebraMap B (K ⊗[A] B)) := IsLocalization.injective _ hle
  have _ : IsLocalization B⁰ (K ⊗[A] B) := by
    refine IsLocalization.of_le _ _ hle fun r hr ↦ ?_
    let _ := hfield.toField
    exact isUnit_iff_ne_zero.mpr
      ((map_ne_zero_iff _ hinj).mpr (mem_nonZeroDivisors_iff_ne_zero.mp hr))
  exact IsLocalization.isLocalization_of_algEquiv _ (IsLocalization.algEquiv B⁰ (K ⊗[A] B) L)

end GenericFibre

/-! ### Primes contracting to the zero ideal -/

/-- An ideal of an algebra `S` over a domain `R` misses the image of the nonzero elements of `R`
exactly when it contracts to the zero ideal of `R`. Geometrically: a point of `Spec S` lies in
the fibre over the generic point of `Spec R` exactly when it dominates `Spec R`. -/
theorem Ideal.disjoint_algebraMapSubmonoid_nonZeroDivisors_iff_under_eq_bot
    {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S] (P : Ideal S) :
    Disjoint (Algebra.algebraMapSubmonoid S R⁰ : Set S) (P : Set S) ↔ P.under R = ⊥ := by
  rw [Set.disjoint_left, Submodule.eq_bot_iff]
  refine ⟨fun h r hr ↦ ?_, ?_⟩
  · by_contra hne
    exact h ⟨r, mem_nonZeroDivisors_of_ne_zero hne, rfl⟩ hr
  · rintro h x ⟨r, hrz, rfl⟩ hx
    exact mem_nonZeroDivisors_iff_ne_zero.mp hrz (h r hx)

/-! ### The components of the base change dominating the base -/

namespace Stacks.GenericFibre

variable (A O K F B L : Type*) [CommRing A] [IsDomain A] [CommRing O] [IsDomain O] [Field K]
  [Field F] [CommRing B] [IsDomain B] [Field L]
  [Algebra A O] [Algebra A K] [Algebra A F] [Algebra A B] [Algebra A L]
  [Algebra K F] [Algebra K L] [Algebra O F] [Algebra B L]
  [IsScalarTower A O F] [IsScalarTower A K F] [IsScalarTower A B L] [IsScalarTower A K L]
  [IsFractionRing A K] [IsFractionRing O F] [IsFractionRing B L]
  [FaithfulSMul A B] [Algebra.IsIntegral A B]

omit [IsDomain O] in
/-- **The ring of the generic fibre of `U → V` is `R(V) ⊗_{R(Y)} R(X)`.** For `B` a domain
integral over `A`, the ring `F ⊗[K] L` is the localization of `O ⊗[A] B` at the nonzero elements
of `O`.

This is `isLocalization_tensorProduct_fractionRing` with its hypothesis that `L` is the
localization of `B` at the nonzero elements of `A` discharged by
`IsLocalization.algebraMapSubmonoid_nonZeroDivisors_of_isIntegral`. -/
theorem isLocalization_tensorProduct :
    letI := tensorProductFractionRingAlgebra A O K F B L
    IsLocalization (Algebra.algebraMapSubmonoid (O ⊗[A] B) O⁰) (F ⊗[K] L) :=
  have := IsLocalization.algebraMapSubmonoid_nonZeroDivisors_of_isIntegral A B K L
  isLocalization_tensorProduct_fractionRing A O K F B L

/-- **The points of `U = V ×_Y X` dominating `V` are the primes of `R(V) ⊗_{R(Y)} R(X)`.** The
bijection sends a prime `p` of `F ⊗[K] L` to its contraction `p ∩ (O ⊗[A] B)`, which is
precisely a prime of `O ⊗[A] B` contracting to the zero ideal of `O`. -/
def primeSpectrumEquivDominating :
    PrimeSpectrum (F ⊗[K] L) ≃
      {P : PrimeSpectrum (O ⊗[A] B) // P.asIdeal.under O = ⊥} :=
  letI := tensorProductFractionRingAlgebra A O K F B L
  haveI := isLocalization_tensorProduct A O K F B L
  (IsLocalization.primeSpectrumOrderIso (Algebra.algebraMapSubmonoid (O ⊗[A] B) O⁰)
      (F ⊗[K] L)).toEquiv.trans
    (Equiv.subtypeEquivRight fun P ↦
      Ideal.disjoint_algebraMapSubmonoid_nonZeroDivisors_iff_under_eq_bot P.asIdeal)

/-- The bijection of `Stacks.GenericFibre.primeSpectrumEquivDominating` is contraction of
ideals. -/
theorem primeSpectrumEquivDominating_coe_asIdeal (p : PrimeSpectrum (F ⊗[K] L)) :
    letI := tensorProductFractionRingAlgebra A O K F B L
    (primeSpectrumEquivDominating A O K F B L p : PrimeSpectrum (O ⊗[A] B)).asIdeal =
      p.asIdeal.under (O ⊗[A] B) :=
  rfl

/-- For a finite extension `L/K` and any extension `F/K` of fields, `F ⊗[K] L` is Artinian. -/
private theorem isArtinianRing_tensorProduct (K F L : Type*) [Field K] [Field F] [Field L]
    [Algebra K F] [Algebra K L] [Module.Finite K L] : IsArtinianRing (F ⊗[K] L) :=
  IsArtinianRing.of_finite F _

/-- The contraction to `O ⊗[A] B` of a prime of `F ⊗[K] L` contracts to the zero ideal of `O`:
the corresponding point of `U` dominates `V`. -/
theorem under_under_eq_bot_left (p : Ideal (F ⊗[K] L)) [p.IsPrime] :
    letI := tensorProductFractionRingAlgebra A O K F B L
    (p.under (O ⊗[A] B)).under O = ⊥ :=
  let := tensorProductFractionRingAlgebra A O K F B L
  have := isLocalization_tensorProduct A O K F B L
  (Ideal.disjoint_algebraMapSubmonoid_nonZeroDivisors_iff_under_eq_bot _).mp
    ((IsLocalization.isPrime_iff_isPrime_disjoint
      (Algebra.algebraMapSubmonoid (O ⊗[A] B) O⁰) (F ⊗[K] L) p).1 ‹p.IsPrime›).2

/-- **The point of `U` dominating `V` attached to a prime of `F ⊗[K] L` is the generic point of
an irreducible component of `U`.** Since `L/K` is finite, `F ⊗[K] L` is a finite `F`-algebra,
hence Artinian, so every prime of it is minimal; and a prime of `O ⊗[A] B` below one contracting
to the zero ideal of `O` contracts to the zero ideal itself, hence comes from a prime of
`F ⊗[K] L` too. -/
@[sga "1 IV 2.5" "special case"]
theorem under_mem_minimalPrimes [Module.Finite K L] (p : Ideal (F ⊗[K] L)) [p.IsPrime] :
    letI := tensorProductFractionRingAlgebra A O K F B L
    p.under (O ⊗[A] B) ∈ minimalPrimes (O ⊗[A] B) := by
  let _ := tensorProductFractionRingAlgebra A O K F B L
  have _ := isLocalization_tensorProduct A O K F B L
  have := isArtinianRing_tensorProduct K F L
  have hpmin : p ∈ minimalPrimes (F ⊗[K] L) := IsArtinianRing.mem_minimalPrimes bot_le
  refine ⟨⟨Ideal.IsPrime.comap _, bot_le⟩, fun Q hQ hQle ↦ ?_⟩
  have : Q.IsPrime := hQ.1
  have hQbot : Q.under O = ⊥ :=
    le_bot_iff.mp (under_under_eq_bot_left A O K F B L p ▸ Ideal.comap_mono hQle)
  have hdisj : Disjoint (Algebra.algebraMapSubmonoid (O ⊗[A] B) O⁰ : Set (O ⊗[A] B))
      (Q : Set (O ⊗[A] B)) :=
    (Ideal.disjoint_algebraMapSubmonoid_nonZeroDivisors_iff_under_eq_bot Q).mpr hQbot
  have hqprime : (Q.map (algebraMap (O ⊗[A] B) (F ⊗[K] L))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ _ Q ‹Q.IsPrime› hdisj
  have hqle : Q.map (algebraMap (O ⊗[A] B) (F ⊗[K] L)) ≤ p := Ideal.map_le_iff_le_comap.mpr hQle
  exact (Ideal.comap_mono (hpmin.2 ⟨hqprime, bot_le⟩ hqle)).trans_eq
    (IsLocalization.under_map_of_isPrime_disjoint _ _ ‹Q.IsPrime› hdisj)

omit [IsDomain A] [IsDomain O] [IsDomain B] [IsFractionRing A K] [IsFractionRing O F]
  [FaithfulSMul A B] [Algebra.IsIntegral A B] in
/-- **The component of `U` attached to a prime of `F ⊗[K] L` dominates `X` as well as `V`**: its
prime contracts to the zero ideal of `B`.

A nonzero `b : B` becomes a unit in the field `L`, hence `1 ⊗ b` becomes a unit of `F ⊗[K] L`,
which therefore lies in no prime. -/
theorem under_under_eq_bot_right (p : Ideal (F ⊗[K] L)) [hp : p.IsPrime] :
    letI := tensorProductFractionRingAlgebra A O K F B L
    letI := Algebra.TensorProduct.rightAlgebra (R := A) (A := O) (B := B)
    (p.under (O ⊗[A] B)).under B = ⊥ := by
  let _ := tensorProductFractionRingAlgebra A O K F B L
  let _ : Algebra B (O ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  refine Submodule.eq_bot_iff _ |>.mpr fun b hb ↦ ?_
  by_contra hbne
  have hmem : algebraMap (O ⊗[A] B) (F ⊗[K] L) (1 ⊗ₜ[A] b) ∈ p := hb
  have himg : algebraMap (O ⊗[A] B) (F ⊗[K] L) (1 ⊗ₜ[A] b) = 1 ⊗ₜ[K] algebraMap B L b := by
    change (Algebra.TensorProduct.lift _ _ _).toRingHom _ = _
    simp
  have hunit : IsUnit (1 ⊗ₜ[K] algebraMap B L b : F ⊗[K] L) :=
    (isUnit_iff_ne_zero.mpr
      ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective B L)).mpr hbne)).map
      (Algebra.TensorProduct.includeRight : L →ₐ[K] F ⊗[K] L)
  exact hp.ne_top (p.eq_top_of_isUnit_mem (himg ▸ hmem) hunit)

omit [IsDomain O] in
/-- **The factor of `R(V) ⊗_{R(Y)} R(X)` at a prime is the function field of the corresponding
component of `U`.** For `p` a prime of `F ⊗[K] L`, the field `(F ⊗[K] L)/p` is the fraction
field of the integral domain `(O ⊗[A] B)/(p ∩ (O ⊗[A] B))`, the coordinate ring of the
reduced irreducible component of `U` cut out by `p`.

The quotient `(F ⊗[K] L)/p` is a field because `F ⊗[K] L` is Artinian, and `(O ⊗[A] B)/p ∩ -`
injects into it; every element of `F ⊗[K] L` is a fraction with denominator in the image of
`O`, and such a denominator stays nonzero in the quotient, so the field is generated by
fractions of the domain. -/
theorem isFractionRing_quotient_under [Module.Finite K L] (p : Ideal (F ⊗[K] L))
    [hp : p.IsPrime] :
    letI := tensorProductFractionRingAlgebra A O K F B L
    IsFractionRing ((O ⊗[A] B) ⧸ p.under (O ⊗[A] B)) ((F ⊗[K] L) ⧸ p) := by
  let _ := tensorProductFractionRingAlgebra A O K F B L
  have _ := isLocalization_tensorProduct A O K F B L
  have := isArtinianRing_tensorProduct K F L
  have : p.IsMaximal := IsArtinianRing.isMaximal_of_isPrime p
  have hfield : IsField ((F ⊗[K] L) ⧸ p) :=
    Ideal.Quotient.maximal_ideal_iff_isField_quotient p |>.mp ‹p.IsMaximal›
  have : IsDomain ((O ⊗[A] B) ⧸ p.under (O ⊗[A] B)) := Ideal.Quotient.isDomain _
  have hinj : Function.Injective
      (algebraMap ((O ⊗[A] B) ⧸ p.under (O ⊗[A] B)) ((F ⊗[K] L) ⧸ p)) :=
    Ideal.algebraMap_quotient_injective
  refine (isLocalization_iff _ _).mpr ⟨fun y ↦ ?_, fun z ↦ ?_, fun {x y} h ↦ ⟨1, by rw [hinj h]⟩⟩
  · obtain ⟨w, hw⟩ := hfield.mul_inv_cancel
      ((map_ne_zero_iff _ hinj).mpr (mem_nonZeroDivisors_iff_ne_zero.mp y.2))
    exact IsUnit.of_mul_eq_one _ hw
  · obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective (I := p) z
    obtain ⟨⟨r, s⟩, hrs⟩ :=
      IsLocalization.surj (Algebra.algebraMapSubmonoid (O ⊗[A] B) O⁰) t
    have hsp : (s : O ⊗[A] B) ∉ p.under (O ⊗[A] B) := fun hs ↦
      hp.ne_top (p.eq_top_of_isUnit_mem hs
        (IsLocalization.map_units (M := Algebra.algebraMapSubmonoid (O ⊗[A] B) O⁰) (F ⊗[K] L) s))
    refine ⟨⟨Ideal.Quotient.mk _ r, ⟨Ideal.Quotient.mk _ (s : O ⊗[A] B),
      mem_nonZeroDivisors_of_ne_zero fun hs ↦ hsp (Ideal.Quotient.eq_zero_iff_mem.mp hs)⟩⟩, ?_⟩
    simpa [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.algebraMap_quotient_map_quotient]
      using congrArg (Ideal.Quotient.mk p) hrs

/-- **The omitted step of Stacks 0EQ4, with the product indexed by the components of
`U = V ×_Y X` dominating `V`.** For `t` a nonzero rational function on `X`, the image in `R(V)`
of its norm `Nm_{R(X)/R(Y)}(t)` is the product, over the irreducible components of `U`
dominating `V`, of the norms over `R(V)` of the images of `t` in the function fields of those
components.

The product is the one of `Stacks.Norm.norm_baseChange_eq_prod_quotient` reindexed along
`Stacks.GenericFibre.primeSpectrumEquivDominating`; the factor at a component is the quotient of
`F ⊗[K] L` by the prime that component comes from, which
`Stacks.GenericFibre.isFractionRing_quotient_under` identifies with the function field of the
component. -/
theorem norm_eq_finprod_norm_quotient [Module.Finite K L] [Module.Finite K F]
    [Algebra.IsSeparable K F] (t : L) :
    letI := tensorProductFractionRingAlgebra A O K F B L
    algebraMap K F (Algebra.norm K t) =
      ∏ᶠ (P : PrimeSpectrum (O ⊗[A] B)) (_ : P.asIdeal.under O = ⊥),
        Algebra.norm F (Ideal.Quotient.mk
          (P.asIdeal.map (algebraMap (O ⊗[A] B) (F ⊗[K] L))) (1 ⊗ₜ[K] t)) := by
  let _ := tensorProductFractionRingAlgebra A O K F B L
  have _ := isLocalization_tensorProduct A O K F B L
  have := isArtinianRing_tensorProduct K F L
  let _ : Fintype (MaximalSpectrum (F ⊗[K] L)) := Fintype.ofFinite _
  let e : MaximalSpectrum (F ⊗[K] L) ≃
      {P : PrimeSpectrum (O ⊗[A] B) // P.asIdeal.under O = ⊥} :=
    IsArtinianRing.primeSpectrumEquivMaximalSpectrum.symm.trans
      (primeSpectrumEquivDominating A O K F B L)
  let _ : Fintype {P : PrimeSpectrum (O ⊗[A] B) // P.asIdeal.under O = ⊥} :=
    Fintype.ofEquiv _ e
  have hmap (q : MaximalSpectrum (F ⊗[K] L)) :
      ((e q : PrimeSpectrum (O ⊗[A] B)).asIdeal.map
        (algebraMap (O ⊗[A] B) (F ⊗[K] L))) = q.asIdeal :=
    IsLocalization.map_under (Algebra.algebraMapSubmonoid (O ⊗[A] B) O⁰) (F ⊗[K] L) q.asIdeal
  rw [Stacks.Norm.norm_baseChange_eq_prod_quotient t,
    ← finprod_subtype_eq_finprod_cond, finprod_eq_prod_of_fintype]
  exact Fintype.prod_equiv e _ _ fun q ↦ by rw [hmap q]

end Stacks.GenericFibre

end
