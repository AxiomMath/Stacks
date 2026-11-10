module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.RingTheory.Norm.BaseChangeProduct
public import StacksFrontier.RingTheory.TensorProduct.GenericFibreComponents
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The components of an algebra over a domain which dominate the base, and the norm of its
generic fibre

Let `O` be a domain with fraction field `F`, let `C` be an `O`-algebra, and let `T` be the
localization of `C` at the nonzero elements of `O`. Geometrically: `V = Spec O` is integral,
`U = Spec C` is a `V`-scheme, and `T` is the ring of the fibre of `U → V` over the generic point
of `V`.

**The irreducible components of `U` which dominate `V` are the primes of `T`**, the factor of
`T` at such a prime is the function field of the corresponding component, and when `T` is a
reduced finite `F`-algebra the norm of an element of `T` over `F` is the product of the norms of
its images in those function fields.

This is the `A`-free restatement of
`StacksFrontier.RingTheory.TensorProduct.GenericFibreComponents`,
whose statements are made for `C = O ⊗[A] B` and `T = F ⊗[K] L` with `A` a domain with fraction
field `K` and `B` a domain integral over `A` with fraction field `L`. That shape is unusable in
the proof of **Stacks 0EQ4** for algebraic spaces: there `Y` is an algebraic space and has no
affine open, so there is no ring `A` with `Spec A ⊆ Y`, and `R(Y)` lives one universe up, so
`Spec K` is not an object of the site either. What the geometry does supply is the pair
`(O, C) = (Γ(V_j), Γ(U_j))` for a branch `V_j = Spec O` of an affine étale chart of `Y` and
`U_j = X ×_Y V_j`; the generic fibre of `U_j → V_j` is then `F ⊗[O] C`, which is the localization
of `C` at the nonzero elements of `O` by `IsLocalization.tensorRight`. Every statement below is
made for that pair, with `T` an arbitrary localization of `C` at the nonzero elements of `O`
rather than the tensor product itself, so that a consumer may use whichever presentation of the
generic fibre it has.

## Main definitions

* `Stacks.GenericFibre.primeSpectrumEquivDominatingOfLocalization`: the bijection between the
  primes of `T` and the primes of `C` contracting to the zero ideal of `O` — that is, the points
  of `U` dominating `V`. It sends a prime to its contraction.

## Main results

* `Stacks.GenericFibre.module_finite_of_localization` and
  `Stacks.GenericFibre.isArtinianRing_of_localization`: for `C` finite over `O` the generic fibre
  is a finite `F`-algebra, hence Artinian — the two finiteness hypotheses the statements below
  need.
* `Stacks.GenericFibre.under_under_eq_bot_of_localization`: the contraction of a prime of `T`
  contracts further to the zero ideal of `O`, i.e. the corresponding point of `U` dominates `V`.
* `Stacks.GenericFibre.under_mem_minimalPrimes_of_localization`: when `T` is Artinian that
  contraction is a *minimal* prime of `C`, that is the generic point of an irreducible component
  of `U`.
* `Stacks.GenericFibre.finite_dominating_of_localization`: there are only finitely many such
  components.
* `Stacks.GenericFibre.isFractionRing_quotient_map_of_localization`: **the factorwise
  identification.** For `P` a prime of `C` contracting to the zero ideal of `O`, the factor
  `T/PT` of `T` is the function field of the component of `U` cut out by `P`, that is the
  fraction field of `C/P`.
* `Stacks.GenericFibre.isFractionRing_quotient_under_of_localization`: the same, indexed by the
  primes of `T`.
* `Stacks.GenericFibre.norm_eq_finprod_norm_quotient_of_localization`: for `T` a reduced finite
  `F`-algebra, the norm over `F` of an element of `T` is the product, over the irreducible
  components of `U` dominating `V`, of the norms over `F` of its images in the function fields of
  those components.
* `Stacks.GenericFibre.norm_eq_finprod_norm_quotient_of_isPushout`: **the omitted step of
  Stacks 0EQ4 with no ring of functions on the base.** For `K ⊆ L` finite, `K ⊆ F` finite
  separable and `T` the base change of `L` along `K → F`, the image in `F` of `Nm_{L/K}(t)` is
  that product.
* `Stacks.GenericFibre.norm_eq_finprod_norm_quotient_of_isPushout_of_isReduced`: the same with
  the finiteness and separability of `F/K` replaced by reducedness of `T` — which is all the
  separability was used for, and which the geometry of Stacks 0EQ4 supplies directly.

## Implementation notes

**No hypothesis relates `O` to `F` in the component statements.** The dictionary between the
primes of `T` and the points of `U` dominating `V` uses only that `T` is the localization of `C`
at `O⁰`, and is proved here without mentioning a fraction field of `O` at all. The fraction field
appears only in the norm statement, and there only as a field `F` with `T` a reduced finite
`F`-algebra: no compatibility between the `F`-algebra structure of `T` and its `C`-algebra
structure is needed for that identity, and requiring none keeps the statement applicable when the
consumer's `F`-algebra structure on `T` arrives by a route of its own — in Stacks 0EQ4, through
the identification of the generic fibre with `R(V_j) ⊗_{R(Y)} R(X)`.

**`IsArtinianRing T` is a hypothesis, not a conclusion.** In the tensor-product statements it is
derived from `Module.Finite K L`, through `F ⊗[K] L` being a finite `F`-algebra. Here there is no
`K` and no `L`, so the finiteness that makes the generic fibre zero-dimensional has to be named
directly; a consumer with `C` finite over `O` gets it from `Module.Finite.of_isLocalization`
together with `isArtinian_of_tower`, and the norm statement derives it from its own hypothesis
`Module.Finite F T`. Without it a prime of `T` need not be minimal, so its contraction need not
be an irreducible component of `U`, and the factor `T/PT` need not be a field.

**`C` is not assumed to be a domain**, and in Stacks 0EQ4 it is not one: `U_j = X ×_Y V_j` is
reducible, and its several components dominating `V_j` are exactly what is being counted.

**What this does not supply.** `Stacks.GenericFibre.norm_eq_finprod_norm_quotient_of_isPushout`
carries `Algebra.IsPushout K F L T` as a hypothesis, and that hypothesis is where the remaining
geometric work of Stacks 0EQ4 sits: it says the generic fibre of `X ×_Y V_j → V_j` is the base
change of the generic fibre `R(X)` of `X → Y` along `R(Y) → R(V_j)`. Nothing here proves it for an
algebraic space, and it is not a weakening of the conclusion — it is a statement identifying the
ring `T`, exactly as the `C = O ⊗[A] B` of the tensor-product module identifies `C` there, and
`Stacks.GenericFibre.norm_eq_finprod_norm_quotient` is recovered from it by taking `T = F ⊗[K] L`
and `C = O ⊗[A] B`, where the pushout holds by `Algebra.IsPushout.instTensorProduct`.

## References

* [Stacks Project, Tag 0EQ4](https://stacks.math.columbia.edu/tag/0EQ4)
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors TensorProduct

namespace Stacks.GenericFibre

variable (O : Type*) [CommRing O] [IsDomain O] (C : Type*) [CommRing C] [Algebra O C]
  (T : Type*) [CommRing T] [Algebra C T] [IsLocalization (Algebra.algebraMapSubmonoid C O⁰) T]

/-! ### Finiteness of the generic fibre -/

section Finite

variable (F : Type*) [Field F] [Algebra O F] [IsFractionRing O F] [Algebra O T] [Algebra F T]
  [IsScalarTower O C T] [IsScalarTower O F T]

omit [IsDomain O] in
include O C in
/-- **The generic fibre of a finite algebra is finite over the fraction field of the base.**
Inverting the nonzero elements of `O` in a finite `O`-algebra `C` gives a finite `F`-algebra,
`F` being the fraction field of `O`. This is `Module.Finite.of_isLocalization` at `M = O⁰`, and
is how a consumer discharges the `Module.Finite F T` hypothesis of
`Stacks.GenericFibre.norm_eq_finprod_norm_quotient_of_localization`. -/
theorem module_finite_of_localization [Module.Finite O C] : Module.Finite F T :=
  Module.Finite.of_isLocalization O C O⁰

omit [IsDomain O] in
include O C F in
/-- **The generic fibre of a finite algebra is Artinian**: it is a finite-dimensional algebra
over the fraction field of the base by
`Stacks.GenericFibre.module_finite_of_localization`. This is how a consumer discharges the
`IsArtinianRing T` hypothesis of the statements below. -/
theorem isArtinianRing_of_localization [Module.Finite O C] : IsArtinianRing T :=
  have := module_finite_of_localization O C T F
  isArtinian_of_tower F inferInstance

end Finite

/-! ### The components dominating the base -/

/-- **The points of `U = Spec C` dominating `V = Spec O` are the primes of the generic fibre.**
For `T` the localization of `C` at the nonzero elements of `O`, the bijection sends a prime `p`
of `T` to its contraction `p ∩ C`, which is precisely a prime of `C` contracting to the zero
ideal of `O`. -/
def primeSpectrumEquivDominatingOfLocalization :
    PrimeSpectrum T ≃ {P : PrimeSpectrum C // P.asIdeal.under O = ⊥} :=
  (IsLocalization.primeSpectrumOrderIso (Algebra.algebraMapSubmonoid C O⁰) T).toEquiv.trans
    (Equiv.subtypeEquivRight fun P ↦
      Ideal.disjoint_algebraMapSubmonoid_nonZeroDivisors_iff_under_eq_bot P.asIdeal)

/-- The bijection of `Stacks.GenericFibre.primeSpectrumEquivDominatingOfLocalization` is
contraction of ideals. -/
theorem primeSpectrumEquivDominatingOfLocalization_coe_asIdeal (p : PrimeSpectrum T) :
    (primeSpectrumEquivDominatingOfLocalization O C T p : PrimeSpectrum C).asIdeal =
      p.asIdeal.under C :=
  rfl

/-- The contraction to `C` of a prime of the generic fibre contracts to the zero ideal of `O`:
the corresponding point of `U` dominates `V`. -/
theorem under_under_eq_bot_of_localization (p : Ideal T) [p.IsPrime] :
    (p.under C).under O = ⊥ :=
  (Ideal.disjoint_algebraMapSubmonoid_nonZeroDivisors_iff_under_eq_bot _).mp
    ((IsLocalization.isPrime_iff_isPrime_disjoint
      (Algebra.algebraMapSubmonoid C O⁰) T p).1 ‹p.IsPrime›).2

include O in
/-- **The point of `U` dominating `V` attached to a prime of the generic fibre is the generic
point of an irreducible component of `U`.** When the generic fibre `T` is Artinian every prime of
it is minimal, and a prime of `C` below one contracting to the zero ideal of `O` contracts to the
zero ideal itself, hence comes from a prime of `T` too. -/
@[sga "1 IV 2.5" "special case"]
theorem under_mem_minimalPrimes_of_localization [IsArtinianRing T] (p : Ideal T) [p.IsPrime] :
    p.under C ∈ minimalPrimes C := by
  have hpmin : p ∈ minimalPrimes T := IsArtinianRing.mem_minimalPrimes bot_le
  refine ⟨⟨Ideal.IsPrime.comap _, bot_le⟩, fun Q hQ hQle ↦ ?_⟩
  have : Q.IsPrime := hQ.1
  have hQbot : Q.under O = ⊥ :=
    le_bot_iff.mp (under_under_eq_bot_of_localization O C T p ▸ Ideal.comap_mono hQle)
  have hdisj : Disjoint (Algebra.algebraMapSubmonoid C O⁰ : Set C) (Q : Set C) :=
    (Ideal.disjoint_algebraMapSubmonoid_nonZeroDivisors_iff_under_eq_bot Q).mpr hQbot
  have hqprime : (Q.map (algebraMap C T)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ _ Q ‹Q.IsPrime› hdisj
  have hqle : Q.map (algebraMap C T) ≤ p := Ideal.map_le_iff_le_comap.mpr hQle
  exact (Ideal.comap_mono (hpmin.2 ⟨hqprime, bot_le⟩ hqle)).trans_eq
    (IsLocalization.under_map_of_isPrime_disjoint _ _ ‹Q.IsPrime› hdisj)

/-- **There are only finitely many components of `U` dominating `V`**, when the generic fibre is
Artinian: they are its primes, of which an Artinian ring has finitely many. -/
theorem finite_dominating_of_localization [IsArtinianRing T] :
    Finite {P : PrimeSpectrum C // P.asIdeal.under O = ⊥} :=
  have : Finite (PrimeSpectrum T) :=
    Finite.of_equiv _ IsArtinianRing.primeSpectrumEquivMaximalSpectrum.symm
  Finite.of_equiv _ (primeSpectrumEquivDominatingOfLocalization O C T)

/-! ### The factor at a component as its function field -/

include O in
/-- **The factor of the generic fibre at a dominating prime is the function field of the
corresponding component of `U`.** Let `q` be a prime of the Artinian generic fibre `T` and `P`
its contraction to `C`, and let the `C/P`-algebra structure on `T/q` be the one induced by
`C → T`. Then `T/q` is the fraction field of the integral domain `C/P`, the coordinate ring of
the reduced irreducible component of `U` cut out by `P`.

The quotient `T/q` is a field because `T` is Artinian, and `C/P` injects into it because `P` is
the contraction of `q`; every element of `T` is a fraction with denominator in the image of `O`,
and such a denominator stays nonzero in the quotient because `P` contracts to the zero ideal of
`O`, so the field is generated by fractions of the domain.

The algebra structure is a hypothesis rather than a fixed instance because the two indexings of
the components — by the primes of `C` dominating `O` and by the primes of `T` — carry two
different canonical ones, `Ideal.Quotient.algebraQuotientMapQuotient` and
`Ideal.Quotient.quotientAlgebra`; the two corollaries below supply each in turn. -/
theorem isFractionRing_quotient_of_localization [IsArtinianRing T] (P : Ideal C) [P.IsPrime]
    (q : Ideal T) [q.IsPrime] (hq : q.under C = P) [Algebra (C ⧸ P) (T ⧸ q)]
    (hcomm : ∀ c : C, algebraMap (C ⧸ P) (T ⧸ q) (Ideal.Quotient.mk P c) =
      Ideal.Quotient.mk q (algebraMap C T c)) :
    IsFractionRing (C ⧸ P) (T ⧸ q) := by
  have hPO : P.under O = ⊥ := hq ▸ under_under_eq_bot_of_localization O C T q
  have hdisj : Disjoint (Algebra.algebraMapSubmonoid C O⁰ : Set C) (P : Set C) :=
    (Ideal.disjoint_algebraMapSubmonoid_nonZeroDivisors_iff_under_eq_bot P).mpr hPO
  have : q.IsMaximal := IsArtinianRing.isMaximal_of_isPrime _
  have hfield : IsField (T ⧸ q) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient q).mp ‹_›
  have : IsDomain (C ⧸ P) := Ideal.Quotient.isDomain _
  have hinj : Function.Injective (algebraMap (C ⧸ P) (T ⧸ q)) := by
    refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective (I := P) x
    rw [hcomm, Ideal.Quotient.eq_zero_iff_mem] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hq ▸ hx)
  refine (isLocalization_iff _ _).mpr ⟨fun y ↦ ?_, fun z ↦ ?_, fun {x y} h ↦ ⟨1, by rw [hinj h]⟩⟩
  · obtain ⟨w, hw⟩ := hfield.mul_inv_cancel
      ((map_ne_zero_iff _ hinj).mpr (mem_nonZeroDivisors_iff_ne_zero.mp y.2))
    exact IsUnit.of_mul_eq_one _ hw
  · obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective (I := q) z
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid C O⁰) t
    have hsp : (s : C) ∉ P := fun hs ↦ Set.disjoint_left.mp hdisj s.2 hs
    refine ⟨⟨Ideal.Quotient.mk _ r, ⟨Ideal.Quotient.mk _ (s : C),
      mem_nonZeroDivisors_of_ne_zero fun hs ↦ hsp (Ideal.Quotient.eq_zero_iff_mem.mp hs)⟩⟩, ?_⟩
    rw [hcomm, hcomm, ← map_mul]
    exact congrArg (Ideal.Quotient.mk q) hrs

include O in
/-- **The factor of the generic fibre at a prime of `C` dominating `O`.** For `P` a prime of `C`
contracting to the zero ideal of `O` and `T` the Artinian generic fibre, the factor `T/PT` is
the fraction field of `C/P`: the function field of the component of `U` cut out by `P`. This is
`Stacks.GenericFibre.isFractionRing_quotient_of_localization` at `q = PT`, whose contraction is
`P` again. -/
theorem isFractionRing_quotient_map_of_localization [IsArtinianRing T] (P : Ideal C)
    [hP : P.IsPrime] (hPO : P.under O = ⊥) :
    IsFractionRing (C ⧸ P) (T ⧸ P.map (algebraMap C T)) :=
  have hdisj : Disjoint (Algebra.algebraMapSubmonoid C O⁰ : Set C) (P : Set C) :=
    (Ideal.disjoint_algebraMapSubmonoid_nonZeroDivisors_iff_under_eq_bot P).mpr hPO
  have _ : (P.map (algebraMap C T)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ _ P hP hdisj
  isFractionRing_quotient_of_localization O C T P (P.map (algebraMap C T))
    (IsLocalization.under_map_of_isPrime_disjoint _ _ hP hdisj) fun _ ↦ rfl

include O in
/-- **The factor of the generic fibre at one of its own primes.** For `p` a prime of the Artinian
generic fibre `T`, the field `T/p` is the fraction field of `C/(p ∩ C)`: the function field of the
component of `U` cut out by `p ∩ C`. This is
`Stacks.GenericFibre.isFractionRing_quotient_of_localization` at `P = p ∩ C`. -/
theorem isFractionRing_quotient_under_of_localization [IsArtinianRing T] (p : Ideal T)
    [p.IsPrime] :
    IsFractionRing (C ⧸ p.under C) (T ⧸ p) :=
  isFractionRing_quotient_of_localization O C T (p.under C) p rfl fun _ ↦ rfl

/-! ### The norm of the generic fibre -/

/-- **The norm on the generic fibre is the product of the norms on the function fields of the
components dominating the base.** Let `O` be a domain, `C` an `O`-algebra, and `T` the
localization of `C` at the nonzero elements of `O`; suppose `T` is a reduced finite-dimensional
algebra over a field `F`. Then for `t : T` the norm `Nm_{T/F}(t)` is the product, over the primes
`P` of `C` contracting to the zero ideal of `O` — that is, over the irreducible components of
`U = Spec C` dominating `V = Spec O` — of the norms over `F` of the images of `t` in the factors
`T/PT`, which `Stacks.GenericFibre.isFractionRing_quotient_map_of_localization` identifies with
the function fields of those components.

The product is the one of `Stacks.Norm.norm_eq_prod_quotient` over the maximal ideals of `T`,
reindexed along `Stacks.GenericFibre.primeSpectrumEquivDominatingOfLocalization`; the maximal
ideal attached to `P` is `PT`, because the ideal of the localization generated by a contraction
is the ideal itself.

This is the `A`-free form of `Stacks.GenericFibre.norm_eq_finprod_norm_quotient`: the hypotheses
there that `L/K` is finite and `F/K` finite separable enter only through the finiteness and the
reducedness of `T`, which are what is assumed here. -/
theorem norm_eq_finprod_norm_quotient_of_localization (F : Type*) [Field F] [Algebra F T]
    [Module.Finite F T] [IsReduced T] (t : T) :
    Algebra.norm F t =
      ∏ᶠ (P : PrimeSpectrum C) (_ : P.asIdeal.under O = ⊥),
        Algebra.norm F (Ideal.Quotient.mk (P.asIdeal.map (algebraMap C T)) t) := by
  have : IsArtinianRing T := isArtinian_of_tower F inferInstance
  let _ : Fintype (MaximalSpectrum T) := Fintype.ofFinite _
  let e : MaximalSpectrum T ≃ {P : PrimeSpectrum C // P.asIdeal.under O = ⊥} :=
    IsArtinianRing.primeSpectrumEquivMaximalSpectrum.symm.trans
      (primeSpectrumEquivDominatingOfLocalization O C T)
  let _ : Fintype {P : PrimeSpectrum C // P.asIdeal.under O = ⊥} := Fintype.ofEquiv _ e
  have hmap (q : MaximalSpectrum T) :
      ((e q : PrimeSpectrum C).asIdeal.map (algebraMap C T)) = q.asIdeal :=
    IsLocalization.map_under (Algebra.algebraMapSubmonoid C O⁰) T q.asIdeal
  rw [Stacks.Norm.norm_eq_prod_quotient t, ← finprod_subtype_eq_finprod_cond,
    finprod_eq_prod_of_fintype]
  exact Fintype.prod_equiv e _ _ fun q ↦ by rw [hmap q]

/-- The norm of `t : L` pushed to `F` is the product of the norms of its images in the factors of
a reduced base change `T` of `L` along `K → F`. -/
private theorem algebraMap_norm_eq_finprod_norm_quotient (K L F : Type*) [Field K] [Field L]
    [Field F] [Algebra K L] [Algebra K F] [Algebra K T] [Algebra L T] [Algebra F T]
    [IsScalarTower K L T] [IsScalarTower K F T] [Algebra.IsPushout K F L T]
    [Module.Finite K L] [IsReduced T] (t : L) :
    algebraMap K F (Algebra.norm K t) =
      ∏ᶠ (P : PrimeSpectrum C) (_ : P.asIdeal.under O = ⊥),
        Algebra.norm F
          (Ideal.Quotient.mk (P.asIdeal.map (algebraMap C T)) (algebraMap L T t)) := by
  let e : (F ⊗[K] L) ≃ₐ[F] T := Algebra.IsPushout.equiv K F L T
  have : Module.Finite F (F ⊗[K] L) := Module.Finite.base_change K F L
  have : Module.Finite F T := Module.Finite.equiv e.toLinearEquiv
  rw [← norm_eq_finprod_norm_quotient_of_localization O C T F (algebraMap L T t),
    ← Stacks.Norm.norm_tmul_one (A := F) t, ← Algebra.norm_eq_of_algEquiv e (1 ⊗ₜ[K] t)]
  congr 1
  rw [Algebra.IsPushout.equiv_tmul, map_one, one_mul]

/-- **The omitted step of Stacks 0EQ4, without a ring of functions on the base space.** Let
`K ⊆ L` be a finite extension of fields, `K ⊆ F` a finite separable one, `O` a domain, `C` an
`O`-algebra, and `T` the localization of `C` at the nonzero elements of `O`; suppose `T` is the
base change of `L` along `K → F`, that is `Algebra.IsPushout K F L T`. Then for `t : L` the image
in `F` of `Nm_{L/K}(t)` is the product, over the primes `P` of `C` contracting to the zero ideal
of `O`, of the norms over `F` of the image of `t` in the factor `T/PT`.

Read geometrically with `K = R(Y)`, `L = R(X)`, `O = Γ(V_j)` for a branch `V_j` of an affine
étale chart of `Y`, `F = R(V_j)` and `C = Γ(X ×_Y V_j)`: the norm `Nm_{R(X)/R(Y)}(f)`, restricted
to `V_j`, is the product of the norms `Nm_{R(U_{j,i})/R(V_j)}(f_{j,i})` over the irreducible
components `U_{j,i}` of `X ×_Y V_j` dominating `V_j`, whose function fields the factors `T/PT`
are by `Stacks.GenericFibre.isFractionRing_quotient_map_of_localization`.

This is `Stacks.GenericFibre.norm_eq_finprod_norm_quotient` with the ring `A` of functions on the
base eliminated. There `T` is literally `F ⊗[K] L` and `C` is literally `O ⊗[A] B`, which an
algebraic space cannot supply: it has no affine open, so there is no such `A`. Here the only
trace of the tensor product is the pushout hypothesis, which says that `T` is the base change of
the generic fibre `L` of `X → Y` along `R(Y) → R(V_j)` — a statement about fields and the one ring
`C` the chart does supply.

The pushout gives an `F`-algebra isomorphism `F ⊗[K] L ≃ T`, through which `T` inherits
finiteness over `F` and — separability of `F/K` being what makes `F ⊗[K] L` reduced —
reducedness; `Stacks.GenericFibre.norm_eq_finprod_norm_quotient_of_localization` then applies,
and `Stacks.Norm.norm_tmul_one` identifies `Nm_{T/F}` of the image of `t` with the image of
`Nm_{L/K}(t)`. -/
theorem norm_eq_finprod_norm_quotient_of_isPushout (K L F : Type*) [Field K] [Field L] [Field F]
    [Algebra K L] [Algebra K F] [Algebra K T] [Algebra L T] [Algebra F T]
    [IsScalarTower K L T] [IsScalarTower K F T] [Algebra.IsPushout K F L T]
    [Module.Finite K L] [Module.Finite K F] [Algebra.IsSeparable K F] (t : L) :
    algebraMap K F (Algebra.norm K t) =
      ∏ᶠ (P : PrimeSpectrum C) (_ : P.asIdeal.under O = ⊥),
        Algebra.norm F
          (Ideal.Quotient.mk (P.asIdeal.map (algebraMap C T)) (algebraMap L T t)) := by
  let e : (F ⊗[K] L) ≃ₐ[F] T := Algebra.IsPushout.equiv K F L T
  have : Module.Finite F (F ⊗[K] L) := Module.Finite.base_change K F L
  have : Algebra.FormallyUnramified K F := Algebra.FormallyUnramified.of_isSeparable K F
  have : IsReduced (L ⊗[K] F) := Algebra.FormallyUnramified.isReduced_of_field L _
  have : IsReduced (F ⊗[K] L) :=
    isReduced_of_injective (Algebra.TensorProduct.comm K F L)
      (Algebra.TensorProduct.comm K F L).injective
  have : IsReduced T := isReduced_of_injective e.symm e.symm.injective
  exact algebraMap_norm_eq_finprod_norm_quotient O C T K L F t

/-- **The omitted step of Stacks 0EQ4 with reducedness in place of separability.** Let `K ⊆ L`
be a finite extension of fields, `F` a field extension of `K`, `O` a domain, `C` an `O`-algebra
and `T` the localization of `C` at the nonzero elements of `O`; suppose `T` is the base change of
`L` along `K → F`, that is `Algebra.IsPushout K F L T`, and that `T` is reduced. Then for `t : L`
the image in `F` of `Nm_{L/K}(t)` is the product, over the primes `P` of `C` contracting to the
zero ideal of `O`, of the norms over `F` of the image of `t` in the factor `T/PT`.

This is `Stacks.GenericFibre.norm_eq_finprod_norm_quotient_of_isPushout` with `Module.Finite K F`
and `Algebra.IsSeparable K F` traded for `IsReduced T`. Those two hypotheses are used there for
exactly one thing — deducing `IsReduced (F ⊗[K] L)`, through
`Algebra.FormallyUnramified.isReduced_of_field` — so asking for the reducedness itself is the
weaker hypothesis, and `Module.Finite F T` still comes from `Module.Finite K L` alone by
`Module.Finite.base_change`.

The trade matters for the consumer of Stacks 0EQ4. Read geometrically with `K = R(Y)`,
`L = R(X)`, `F = R(V_j)` for a branch `V_j` of an affine étale chart of `Y` and
`C = Γ(X ×_Y V_j)`, the separability of `F/K` is the finite separability of the function-field
extension of an étale chart, which is a statement about rational functions of algebraic spaces;
whereas the reducedness of `T` is reducedness of a localization of `C`, and `X ×_Y V_j` is étale
over the integral — hence reduced — space `X`. So on the geometric side this form asks for
reducedness of a chart, in place of a separability statement about function fields. -/
theorem norm_eq_finprod_norm_quotient_of_isPushout_of_isReduced (K L F : Type*) [Field K]
    [Field L] [Field F] [Algebra K L] [Algebra K F] [Algebra K T] [Algebra L T] [Algebra F T]
    [IsScalarTower K L T] [IsScalarTower K F T] [Algebra.IsPushout K F L T]
    [Module.Finite K L] [IsReduced T] (t : L) :
    algebraMap K F (Algebra.norm K t) =
      ∏ᶠ (P : PrimeSpectrum C) (_ : P.asIdeal.under O = ⊥),
        Algebra.norm F
          (Ideal.Quotient.mk (P.asIdeal.map (algebraMap C T)) (algebraMap L T t)) :=
  algebraMap_norm_eq_finprod_norm_quotient O C T K L F t

end Stacks.GenericFibre

end
