module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.UniversalInjectivity
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.WeaklyAssociated
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.Functoriality
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.WeaklyAssociatedFieldExtension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The base clause of 05IG over a local base with projective `N`

Let `R` be a local ring with maximal ideal `𝔭`, let `S` be an `R`-algebra, let `N` be an
`S`-module which is projective as an `R`-module and whose closed fibre `N / 𝔭N` is finite over
the Noetherian closed-fibre ring `S / 𝔭S`, and let `M` be an arbitrary `R`-module.  For a prime
`𝔮` of `S` lying over `𝔭` whose image in `S / 𝔭S` dominates every prime associated to `N / 𝔭N`,
this file proves the base clause of [Stacks, Tag 05IG]:

`𝔮 ∈ WeakAss_S(N ⊗_R M)` implies `𝔭 ∈ WeakAss_R(M)`.

**No finiteness hypothesis is imposed on `𝔭`.**  This is the point of the file: the clause is
already available in
`StacksFrontier/RingTheory/Ideal/WeaklyAssociatedPrime/FlatFibreAtPrime.lean`, but only in the
weakened form that assumes `𝔭.FG`, whereas [Stacks, Tag 05IG] assumes no such thing.  The
hypotheses traded for it — a local base, `N` projective over `R`, and the domination condition on
`𝔮-bar` — are exactly what the source's étale-local reduction installs before its last paragraph.

The argument is the source's.  An element `s ∈ S` outside `𝔮` has image outside `𝔮-bar`, hence
lies in no prime associated to the closed fibre `N / 𝔭N`, hence acts regularly on it
(Stacks 00LD); by [Stacks, Tag 05FR] it therefore acts universally injectively on `N` over `R`,
so in particular injectively on `N ⊗_R M`.  Feeding that regularity into the descent of a weakly
associated prime along `R → S` shows `𝔭 ∈ WeakAss_R(N ⊗_R M)`, and projectivity of `N` over `R`
splits off the tensor factor to leave `𝔭 ∈ WeakAss_R(M)`.

## Main results

* `Stacks.WeaklyAssociatedPrimes.isWeaklyAssociatedPrime_base_of_projective_fibre`: the base
  clause above, carrying no finiteness hypothesis on the maximal ideal.
* `Stacks.WeaklyAssociatedPrimes.isWeaklyAssociatedPrime_of_tensorProduct_projective`: a prime
  weakly associated to `P ⊗[R] M` with `P` projective is weakly associated to `M`.
* `Stacks.WeaklyAssociatedPrimes.isWeaklyAssociatedPrime_comap_of_tensorProduct_projective`: the
  descent of a weakly associated prime of `N ⊗_R M` along `R → S`, given that every scalar
  outside `𝔮` acts injectively on `N ⊗_R M`.
* `Stacks.WeaklyAssociatedPrimes.isSMulRegular_of_notMem_associatedPrimes`: over a Noetherian
  ring, an element lying in no associated prime of a module acts regularly on it.
* `Stacks.WeaklyAssociatedPrimes.smul_injective_of_isSMulRegular_closedFibre`: an element acting
  regularly on the closed fibre acts injectively on `N ⊗_R M`.

## Implementation notes

The closed fibre ring is written `S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)` and
the closed fibre module `N ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) • ⊤)`, as in
`StacksFrontier/AlgebraicGeometry/Flatness/PureModules/UniversalInjectivity.lean`; the Noetherianity
of the first and the finiteness of the second are instance hypotheses.  The source writes the
tensor product as `M ⊗_R N`; the canonically isomorphic model `N ⊗_R M`, on which the `S`-module
structure is available directly, is used instead.

Universe-wise `N` and `M` must lie in the same universe, because `UniversallyInjective` quantifies
over test modules in the universe of its source and target.

## References

* [Stacks Project, Tag 05IG](https://stacks.math.columbia.edu/tag/05IG)
* [Stacks Project, Tag 05FR](https://stacks.math.columbia.edu/tag/05FR)
* [Stacks Project, Tag 00LD](https://stacks.math.columbia.edu/tag/00LD)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Stacks.WeaklyAssociatedPrimes

/-- If `P` is a projective `R`-module, a prime weakly associated to `P ⊗[R] M` is weakly
associated to `M`.  A projective module is a direct summand of a free one, so `P ⊗[R] M` embeds
into `(P →₀ R) ⊗[R] M` and the free case applies. -/
@[ega "IV 3.3.8" "special case"]
theorem isWeaklyAssociatedPrime_of_tensorProduct_projective
    {R P M : Type*} [CommRing R] [AddCommGroup P] [Module R P] [Module.Projective R P]
    [AddCommGroup M] [Module R M] {p : Ideal R}
    (h : IsWeaklyAssociatedPrime R (P ⊗[R] M) p) :
    IsWeaklyAssociatedPrime R M p := by
  obtain ⟨i, hi⟩ := (inferInstance : Module.Projective R P).out
  let e : (P →₀ R) →ₗ[R] P := Finsupp.linearCombination R id
  let f : P ⊗[R] M →ₗ[R] (P →₀ R) ⊗[R] M :=
    TensorProduct.map i (LinearMap.id : M →ₗ[R] M)
  let g : (P →₀ R) ⊗[R] M →ₗ[R] P ⊗[R] M :=
    TensorProduct.map e (LinearMap.id : M →ₗ[R] M)
  have hgf : g.comp f = LinearMap.id := by
    have hei : e.comp i = LinearMap.id := by
      ext x
      exact hi x
    rw [← TensorProduct.map_comp]
    simp [hei]
  have hf : Function.Injective f := fun x y hxy => by
    simpa [← LinearMap.comp_apply, hgf] using congrArg g hxy
  exact IsWeaklyAssociatedPrime.of_tensorProduct_free (P →₀ R)
    (Module.weaklyAssociatedPrimes_subset_of_injective (f := f) hf h)

/-- Descent of a weakly associated prime along `R → S`.  If `q` is weakly associated to the
`S`-module `N ⊗[R] M`, lies over `p`, and every scalar `s ∈ S` outside `q` acts injectively on
`N ⊗[R] M`, then `p` is weakly associated to `M`, provided `N` is projective over `R`.

The injectivity hypothesis is what turns minimality of `q` over `Ann_S(z)` into minimality of `p`
over `Ann_R(z)`: a power of `r ∈ p` is killed by `z` after multiplication by some `s ∉ q`, and
that `s` may then be cancelled. -/
theorem isWeaklyAssociatedPrime_comap_of_tensorProduct_projective
    {R S N M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Projective R N] [AddCommGroup M] [Module R M]
    {p : Ideal R} [p.IsPrime] {q : Ideal S} [q.IsPrime]
    (hq : IsWeaklyAssociatedPrime S (N ⊗[R] M) q)
    (hqp : q.comap (algebraMap R S) = p)
    (hreg : ∀ s, s ∉ q → Function.Injective (fun z : N ⊗[R] M => s • z)) :
    IsWeaklyAssociatedPrime R M p := by
  obtain ⟨z, hz⟩ := hq
  have hqmin : q ∈ (S ∙ z).annihilator.minimalPrimes := hz
  have hpTensor : IsWeaklyAssociatedPrime R (N ⊗[R] M) p := by
    refine ⟨z, minimalPrimes_of_radical_condition _ p ‹_› ?_ ?_⟩
    · intro r hr
      have hr' : algebraMap R S r ∈ (S ∙ z).annihilator := by
        rw [Submodule.mem_annihilator_span_singleton] at hr ⊢
        simpa [algebraMap_smul] using hr
      rw [← hqp]
      exact hqmin.1.2 hr'
    · intro r hr
      have hrq : algebraMap R S r ∈ q := Ideal.mem_comap.mp (hqp ▸ hr)
      obtain ⟨s, hs, n, hsn⟩ := exists_mul_pow_mem_of_mem_minimalPrimes hqmin hrq
      rw [Submodule.mem_annihilator_span_singleton] at hsn
      have hkill : s • (r ^ n • z) = 0 := by
        calc
          s • (r ^ n • z) = s • (algebraMap R S (r ^ n) • z) := by
            rw [IsScalarTower.algebraMap_smul]
          _ = (s * algebraMap R S (r ^ n)) • z := by rw [mul_smul]
          _ = 0 := by simpa [map_pow] using hsn
      refine ⟨1, fun hone => Ideal.IsPrime.ne_top ‹p.IsPrime› (p.eq_top_iff_one.mpr hone), n, ?_⟩
      simpa [Submodule.mem_annihilator_span_singleton] using hreg s hs hkill
  exact isWeaklyAssociatedPrime_of_tensorProduct_projective hpTensor

/-- **Stacks 00LD**, one direction.  Over a Noetherian ring, an element of `A` lying in no
associated prime of `X` acts regularly on `X`, the set of zerodivisors on `X` being the union of
the associated primes. -/
theorem isSMulRegular_of_notMem_associatedPrimes
    {A X : Type*} [CommRing A] [IsNoetherianRing A] [AddCommGroup X] [Module A X]
    (a : A) (h : ∀ r ∈ associatedPrimes A X, a ∉ r) : IsSMulRegular X a := by
  by_contra hbad
  have hmem : a ∈ ⋃ r ∈ associatedPrimes A X, (r : Set A) := by
    rwa [biUnion_associatedPrimes_eq_compl_regular A X]
  obtain ⟨r, hr, har⟩ := Set.mem_iUnion₂.mp hmem
  exact h r hr har

/-- **Stacks 05FR**, applied to a tensor factor.  If `s : S` acts regularly on the closed fibre
`N / 𝔭N` of an `S`-module `N` which is projective over the local base `R`, then `s` acts
injectively on `N ⊗[R] M` for every `R`-module `M`: by Tag 05FR multiplication by `s` is
universally injective on `N` over `R`, and `M` is one of the test modules. -/
theorem smul_injective_of_isSMulRegular_closedFibre
    {R : Type u} {S : Type v} {N M : Type (max v w)}
    [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Projective R N]
    [IsNoetherianRing (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))]
    [Module.Finite (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
      (N ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) • (⊤ : Submodule S N)))]
    [AddCommGroup M] [Module R M] (s : S)
    (hs : IsSMulRegular
      (N ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) • (⊤ : Submodule S N))) s) :
    Function.Injective (fun z : N ⊗[R] M => s • z) :=
  Stacks.UniversalInjectivity.universallyInjective_lsmul_of_mem_nonZeroSMulDivisors_quotient
    (isSMulRegular_iff_mem_nonZeroSMulDivisors.mp hs) M

/-- **The base clause of [Stacks, Tag 05IG] over a local base with `N` projective.**

Let `R` be local with maximal ideal `𝔭`, let `N` be an `S`-module projective over `R` with
Noetherian closed-fibre ring and finite closed fibre, and let `M` be any `R`-module.  Let `𝔮` be a
prime of `S` lying over `𝔭` whose image in `S / 𝔭S` contains every prime associated to the closed
fibre `N / 𝔭N`.  If `𝔮` is weakly associated to `N ⊗[R] M`, then `𝔭` is weakly associated to `M`.

No finiteness hypothesis is placed on `𝔭`.

Each `s ∉ 𝔮` has image outside `𝔮-bar`, hence outside every associated prime of the closed
fibre, hence acts regularly there and so injectively on `N ⊗[R] M`; descent along `R → S` and
projectivity of `N` then give the conclusion. -/
theorem isWeaklyAssociatedPrime_base_of_projective_fibre
    {R : Type u} {S : Type v} {N M : Type (max v w)}
    [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Projective R N] [AddCommGroup M] [Module R M]
    [IsNoetherianRing (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))]
    [Module.Finite (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
      (N ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) • (⊤ : Submodule S N)))]
    (q : Ideal S) [q.IsPrime]
    (hqp : q.comap (algebraMap R S) = IsLocalRing.maximalIdeal R)
    (hbelow : ∀ r ∈ associatedPrimes
      (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
      (N ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) • (⊤ : Submodule S N))),
      r ≤ q.map (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))))
    (hweak : IsWeaklyAssociatedPrime S (N ⊗[R] M) q) :
    IsWeaklyAssociatedPrime R M (IsLocalRing.maximalIdeal R) := by
  let J := Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)
  let Q := N ⧸ (J • (⊤ : Submodule S N))
  have hJq : J ≤ q := Ideal.map_le_iff_le_comap.mpr hqp.ge
  have hqcomap : (q.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) = q := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hJq]
  refine isWeaklyAssociatedPrime_comap_of_tensorProduct_projective hweak hqp fun s hs => ?_
  have hnot : (Ideal.Quotient.mk J s) ∉ q.map (Ideal.Quotient.mk J) := fun h =>
    hs (hqcomap ▸ h)
  have hreg : IsSMulRegular Q (Ideal.Quotient.mk J s) :=
    isSMulRegular_of_notMem_associatedPrimes _ fun r hr har => hnot (hbelow r hr har)
  have hreg' : IsSMulRegular Q s := by
    simpa only [IsSMulRegular, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul] using hreg
  exact smul_injective_of_isSMulRegular_closedFibre s hreg'

end Stacks.WeaklyAssociatedPrimes

end
