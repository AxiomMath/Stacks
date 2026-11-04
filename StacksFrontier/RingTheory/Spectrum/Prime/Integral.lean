module
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.QuasiFinite.Basic
public import StacksCore.Tactic.StacksAttribute
/-!
# Integral ring maps and prime spectra

Lying over (Stacks 00GQ) and incomparability (Stacks 00GT) for integral ring maps.

## Main results

* `integral_overring_surjective`: surjectivity of `PrimeSpectrum.comap f` for an injective
  integral `f` (Stacks 00GQ), a restatement of Mathlib's `RingHom.IsIntegral.comap_surjective`.
* `not_le_and_not_le_of_comap_eq_of_ne`: in an integral extension, distinct primes with the same
  contraction are incomparable (Stacks 00GT).

## Implementation notes

Two further tags are Mathlib results, recorded here with `add_to_stacks`:

* Stacks 00GU, going up — above a strict inclusion `p < p'` of primes of `R` and a prime `q` of
  `S` over `p` there is a prime `q' > q` over `p'` — is `Ideal.exists_ideal_gt_liesOver_of_lt`,
  for any algebra with the going-up property, which an integral algebra has by
  `Algebra.HasGoingUp.of_isIntegral`.
* Stacks 05DR, that a finite ring map has finite fibres on `Spec`, is
  `Algebra.QuasiFinite.finite_comap_preimage_singleton`, in the greater generality of a
  quasi-finite algebra, of which a module-finite one is an instance.
-/

@[expose] public section

add_to_stacks 00GU "for any algebra with the going-up property; an integral one has it by
  `Algebra.HasGoingUp.of_isIntegral`" Ideal.exists_ideal_gt_liesOver_of_lt
add_to_stacks 05DR "in the generality of a quasi-finite algebra"
  Algebra.QuasiFinite.finite_comap_preimage_singleton

/-- Lying over: if `f : R →+* S` is an injective integral ring map, then the induced
map `Spec S → Spec R` is surjective. -/
@[stacks 00GQ, ega "IV 6.15.5" "special case"]
theorem integral_overring_surjective
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : f.IsIntegral) (hinj : Function.Injective f) :
    Function.Surjective (PrimeSpectrum.comap f) :=
  hf.comap_surjective hinj

/-- Under an integral extension, two primes with equal contractions along
`algebraMap R S` cannot satisfy `q ≤ q'` unless they are equal. -/
private lemma eq_of_le_of_comap_eq_of_isIntegral
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (q q' : Ideal S) [q.IsPrime]
    (hcomap : q.comap (algebraMap R S) = q'.comap (algebraMap R S))
    (hsub : q ≤ q') : q = q' := by
  by_contra hne
  obtain ⟨x, hx_mem, hx_nmem⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hsub hne)
  have hmap_ne_bot : q'.map (Ideal.Quotient.mk q) ≠ ⊥ := fun hbot => hx_nmem <| by
    have hmem := Ideal.mem_map_of_mem (Ideal.Quotient.mk q) hx_mem
    rwa [hbot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmem
  refine Ideal.under_ne_bot (R ⧸ q.comap (algebraMap R S)) hmap_ne_bot ?_
  rw [Ideal.under_def, eq_bot_iff]
  intro y hy
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [Ideal.mem_comap, Ideal.Quotient.algebraMap_mk_of_liesOver,
      Ideal.mem_quotient_iff_mem_sup, sup_of_le_left hsub] at hy
  rwa [Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem, hcomap, Ideal.mem_comap]

/-- In an integral extension there are no inclusions between distinct primes with the
same contraction: if `q ≠ q'` are primes of `S` with equal contractions along
`algebraMap R S`, then neither contains the other. -/
@[stacks 00GT]
theorem not_le_and_not_le_of_comap_eq_of_ne
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (q q' : Ideal S) [q.IsPrime] [q'.IsPrime]
    (hcomap : q.comap (algebraMap R S) = q'.comap (algebraMap R S))
    (hne : q ≠ q') : ¬ q ≤ q' ∧ ¬ q' ≤ q :=
  ⟨fun h => hne (eq_of_le_of_comap_eq_of_isIntegral R S q q' hcomap h),
   fun h => hne (eq_of_le_of_comap_eq_of_isIntegral R S q' q hcomap.symm h).symm⟩

end
