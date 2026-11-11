module

public import StacksFrontier.RingTheory.GeometricallyIrreducible.Defs
import StacksFrontier.RingTheory.GeometricallyIrreducible.SeparableClosure
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u

/-!
# Criteria for geometric irreducibility of an algebra over a field

Let `k` be a field and `R` a commutative `k`-algebra. This file proves Stacks 037K: the spectrum
of `R ⊗[k] k'` is irreducible for every field extension `k'/k` as soon as it is irreducible for
the finite separable ones, equivalently for a single separable closure of `k`, equivalently for a
single algebraic closure of `k`.

Everything is run through `PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical`: the spectrum of
`A` is irreducible exactly when `nilradical A` is prime. In that language one identity does all
the descending: a ring map `φ : A → B` whose kernel consists of nilpotents satisfies
`nilradical A = (nilradical B).comap φ`, so it reflects nilpotency and pulls a prime nilradical
back to a prime nilradical. Applied to an injection this replaces the source's appeal to flatness
and going down, and applied to a reduction map it is the passage to the reduced quotient.

Two ascents remain. Going up to a separable closure `k^{sep}` is a union argument: any two
elements of `R ⊗[k] k^{sep}` lie in the image of `R ⊗[k] k'` for a single finite subextension
`k'/k`, and there the hypothesis for finite separable extensions applies. Going up to an arbitrary
extension `k'/k` is where the mathematics sits, and is
`isPrime_nilradical_tensorProduct_of_isSepClosed_extension`: one picks a field `F` receiving both
`k^{sep}` and `k'`, notes `R ⊗[k] F = (R ⊗[k] k^{sep}) ⊗_{k^{sep}} F` and applies Stacks 00I7 over
the separably closed field `k^{sep}`, then descends to the subring `R ⊗[k] k'`.

## Main results

* `Stacks.Irreducibility.SeparableCriteria.solution`: Stacks 037K, the statement of
  `AlgebraicGeometry.geometricallyIrreducible_tfae`.

## Implementation notes

The implication graph proved here is `(1) → (2) → (3) → (1)`, `(1) → (4) → (3)`, together with
`(1) ↔ (5)`, which is Stacks 037L's
`Algebra.isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_tensorProduct`. It differs
from the source's cycle `(1) → (2) → (3) → (4) → (1)` in that `(4) → (3)` is proved instead of
`(3) → (4)`: an algebraic closure receives a separable closure, so `R ⊗[k] k^{sep}` is a subring
of `R ⊗[k] k̄` and the descent above applies verbatim. The source instead pushes irreducibility
forward along the purely inseparable extension `k̄/k^{sep}` using Stacks 0BRA, which needs the
characteristic split into `p > 0` and `0`; the route taken here needs neither, and `(4) → (1)`
becomes an instance of `(3) → (1)`.

The step `(3) → (1)` is proved for an arbitrary separably closed extension `k^{sep}/k` in place of
a separable closure: no algebraicity is used, only `IsSepClosed k^{sep}`. The field `F` it needs is
built as a quotient of `k^{sep} ⊗[k] k'` by a maximal ideal — that tensor product is nonzero,
being a tensor product of nonzero vector spaces over `k` — which is the cheapest witness for the
source's "we may choose a field `F` such that both `k'` and `k̄` are isomorphic to subfields of
`F`", and gives the `k^{sep}`-algebra structure on `F` for free.

Base change along an injection of `k`-algebras is injective because `R` is flat over the field `k`
(`TensorProduct.map_injective_of_flat_flat'`); this is the injectivity the source also reads off
from flatness.

The last step consumes Stacks 00I7 in its nilradical form, which this file restates and proves
locally as `isPrime_nilradical_tensorProduct_of_isSepClosed`; the registered statement of 00I7 is
`existsUnique_mem_minimalPrimes_tensorProduct_of_isSepClosed` in
`StacksFrontier.RingTheory.Spectrum.Prime.IrreducibleFibres`. The analytic heart of it, that a
field extension of a separably closed field is a geometrically irreducible algebra over it, is
`geomPure_baseChange_irreducible` in
`StacksFrontier.RingTheory.GeometricallyIrreducible.SeparableClosure`, and what remains is the
reduction of a pair of `k^{sep}`-algebras with prime nilradical to a pair (domain, field), which
is `isPrime_nilradical_tensorProduct_of_isSepClosed` below.

## References

* [Stacks Project, Tag 037K](https://stacks.math.columbia.edu/tag/037K)
-/

namespace Stacks.Irreducibility.SeparableCriteria



open AlgebraicGeometry CommRingCat TensorProduct

section Nilradical

variable {A B F : Type*} [CommRing A] [CommRing B] [FunLike F A B] [RingHomClass F A B]

/-- A ring map whose kernel consists of nilpotent elements pulls the nilradical back to the
nilradical, `√(0) = φ⁻¹(√(0))`: both sides are the radical of an ideal squeezed between `0` and
`√(0)`. Equivalently, such a map reflects nilpotency. -/
@[ega "0 1.1.1" "special case"]
private theorem nilradical_eq_comap (φ : F) (hφ : RingHom.ker φ ≤ nilradical A) :
    nilradical A = (nilradical B).comap φ := by
  rw [nilradical, nilradical, Ideal.comap_radical, Ideal.zero_eq_bot, Ideal.zero_eq_bot,
    ← RingHom.ker_eq_comap_bot]
  exact le_antisymm (Ideal.radical_mono bot_le)
    (Ideal.radical_idem (⊥ : Ideal A) ▸ Ideal.radical_mono hφ)

/-- An injective ring map pulls the nilradical back to the nilradical: an element is nilpotent
exactly when its image is. -/
theorem nilradical_eq_comap_of_injective (φ : F) (hφ : Function.Injective φ) :
    nilradical A = (nilradical B).comap φ :=
  nilradical_eq_comap φ (by
    rw [RingHom.ker_eq_comap_bot, Ideal.comap_bot_of_injective φ hφ]; exact bot_le)

/-- A ring map whose kernel consists of nilpotents transports a prime nilradical downwards. With
`φ` the reduction map this is the passage from a ring to its reduced quotient. -/
private theorem isPrime_nilradical_of_ker_le_nilradical (φ : F)
    (hφ : RingHom.ker φ ≤ nilradical A) (h : (nilradical B).IsPrime) :
    (nilradical A).IsPrime := by
  rw [nilradical_eq_comap φ hφ]; exact h.comap _

/-- The nilradical of a subring of a ring with prime nilradical is prime: it is the contraction
of the nilradical upstairs, and the contraction of a prime ideal is prime. This is the whole of
the source's descent steps, for which the source invokes flatness and going down. -/
theorem isPrime_nilradical_of_injective (φ : F) (hφ : Function.Injective φ)
    (h : (nilradical B).IsPrime) : (nilradical A).IsPrime := by
  rw [nilradical_eq_comap_of_injective φ hφ]; exact h.comap _

/-- A ring map carries the nilradical into the nilradical, since it preserves nilpotency. -/
private theorem map_nilradical_le (φ : F) : (nilradical A).map φ ≤ nilradical B := by
  rw [nilradical, nilradical]
  exact le_trans (Ideal.map_radical_le (f := φ)) (Ideal.radical_mono (by simp))

end Nilradical

section TensorMap

variable {k R : Type*} [Field k] [CommRing R] [Algebra k R]

/-- Base changing `R` along an injective map of `k`-algebras is injective, because `R` is flat
over the field `k`. -/
theorem injective_tensorProduct_map_id {E L : Type*} [CommRing E] [Algebra k E]
    [CommRing L] [Algebra k L] (f : E →ₐ[k] L) (hf : Function.Injective f) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id k R) f) := by
  have h : Function.Injective (TensorProduct.map (LinearMap.id : R →ₗ[k] R) f.toLinearMap) :=
    TensorProduct.map_injective_of_flat_flat' _ _ Function.injective_id hf
  intro x y hxy
  refine h (a₁ := x) (a₂ := y) ?_
  simpa [← AlgHom.toLinearMap_apply, Algebra.TensorProduct.toLinearMap_map,
    TensorProduct.AlgebraTensorModule.map_eq] using hxy

variable {K : Type*} [Field K] [Algebra k K]

/-- The image of `R ⊗[k] E` in `R ⊗[k] K` grows with the intermediate field `E`, because base
changing `R` along `E₁ ⊆ E₂ ⊆ K` factors through the base change along `E₂ ⊆ K`. -/
private theorem range_tensorProduct_map_val_mono {E₁ E₂ : IntermediateField k K} (h : E₁ ≤ E₂) :
    (Algebra.TensorProduct.map (AlgHom.id k R) E₁.val).range ≤
      (Algebra.TensorProduct.map (AlgHom.id k R) E₂.val).range := by
  have hcomp : (Algebra.TensorProduct.map (AlgHom.id k R) E₂.val).comp
      (Algebra.TensorProduct.map (AlgHom.id k R) (IntermediateField.inclusion h)) =
      Algebra.TensorProduct.map (AlgHom.id k R) E₁.val := by
    rw [← Algebra.TensorProduct.map_comp]; rfl
  rw [← hcomp]
  exact AlgHom.range_comp_le_range _ _

/-- For `K/k` algebraic, every element of `R ⊗[k] K` comes from `R ⊗[k] E` for some finite
intermediate field `E`: a pure tensor `r ⊗ a` comes from `E = k⟮a⟯`, and a sum is handled by the
compositum of two such, which is again finite over `k`. -/
private theorem exists_finiteDimensional_mem_range [Algebra.IsAlgebraic k K] (x : R ⊗[k] K) :
    ∃ E : IntermediateField k K, FiniteDimensional k E ∧
      x ∈ (Algebra.TensorProduct.map (AlgHom.id k R) E.val).range := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
      exact ⟨IntermediateField.adjoin k {a},
        IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a),
        ⟨r ⊗ₜ ⟨a, IntermediateField.subset_adjoin k _ rfl⟩, by simp⟩⟩
  | add x y hx hy =>
      obtain ⟨E₁, h₁, hx⟩ := hx
      obtain ⟨E₂, h₂, hy⟩ := hy
      exact ⟨E₁ ⊔ E₂, IntermediateField.finiteDimensional_sup E₁ E₂,
        add_mem (range_tensorProduct_map_val_mono le_sup_left hx)
          (range_tensorProduct_map_val_mono le_sup_right hy)⟩

/-- The union argument of the source's `(2) ⇒ (3)`, in the form it is used: if `K/k` is algebraic
and `nilradical (R ⊗[k] E)` is prime for every finite intermediate field `E`, then
`nilradical (R ⊗[k] K)` is prime. Two elements of `R ⊗[k] K` whose product is nilpotent come from
a single finite `E`, where the hypothesis applies; the contraction identity
`nilradical (R ⊗[k] E) = (nilradical (R ⊗[k] K)).comap` transports the alternative in both
directions, and at `E = ⊥` it also rules out `nilradical (R ⊗[k] K) = ⊤`. -/
private theorem isPrime_nilradical_tensorProduct_of_forall_finiteDimensional
    [Algebra.IsAlgebraic k K]
    (h : ∀ E : IntermediateField k K, FiniteDimensional k E → (nilradical (R ⊗[k] E)).IsPrime) :
    (nilradical (R ⊗[k] K)).IsPrime := by
  have key : ∀ E : IntermediateField k K, nilradical (R ⊗[k] E) =
      (nilradical (R ⊗[k] K)).comap (Algebra.TensorProduct.map (AlgHom.id k R) E.val) := fun E =>
    nilradical_eq_comap_of_injective _
      (injective_tensorProduct_map_id E.val E.val.toRingHom.injective)
  refine Ideal.isPrime_iff.2 ⟨fun htop => (h ⊥ inferInstance).ne_top ?_, fun {x y} hxy => ?_⟩
  · rw [key ⊥, htop, Ideal.comap_top]
  · obtain ⟨E₁, h₁, hx⟩ := exists_finiteDimensional_mem_range (R := R) x
    obtain ⟨E₂, h₂, hy⟩ := exists_finiteDimensional_mem_range (R := R) y
    obtain ⟨E, hE₁, hE₂, hfd⟩ :
        ∃ E : IntermediateField k K, E₁ ≤ E ∧ E₂ ≤ E ∧ FiniteDimensional k E :=
      ⟨E₁ ⊔ E₂, le_sup_left, le_sup_right, IntermediateField.finiteDimensional_sup E₁ E₂⟩
    have hprime := h E hfd
    rw [key E] at hprime
    obtain ⟨a, ha⟩ := (AlgHom.mem_range _).1 (range_tensorProduct_map_val_mono (R := R) hE₁ hx)
    obtain ⟨b, hb⟩ := (AlgHom.mem_range _).1 (range_tensorProduct_map_val_mono (R := R) hE₂ hy)
    have hab : a * b ∈ Ideal.comap (Algebra.TensorProduct.map (AlgHom.id k R) E.val)
        (nilradical (R ⊗[k] K)) := by
      rw [Ideal.mem_comap, map_mul, ha, hb]; exact hxy
    rcases hprime.mem_or_mem hab with hm | hm
    · exact Or.inl (by rw [← ha]; exact Ideal.mem_comap.1 hm)
    · exact Or.inr (by rw [← hb]; exact Ideal.mem_comap.1 hm)

end TensorMap

/-- A local restatement of Stacks 00I7 in nilradical form, used by this file. Let `K` be a
separably closed field and let `A`, `B` be `K`-algebras each with a unique minimal prime, that is,
with prime nilradical. Then `A ⊗[K] B` has a unique minimal prime. The registered statement of
00I7 is `existsUnique_mem_minimalPrimes_tensorProduct_of_isSepClosed`.

Separable closedness of `K` is what makes this true rather than formal: for `K'/K` a nontrivial
finite separable extension `Spec K'` is a point, hence irreducible, while `Spec (K' ⊗[K] K')` has
at least two points, no two of which are comparable.

The analytic content — a field extension of a separably closed field is a geometrically
irreducible algebra over it — is `geomPure_baseChange_irreducible`. What is added here is the
reduction of the pair `(A, B)` to a pair (domain, field): the surjection
`A ⊗[K] B → (A/√0) ⊗[K] (B/√0)` has kernel generated by nilpotents, so it reflects nilpotency,
and `(A/√0) ⊗[K] (B/√0)` embeds in `(A/√0) ⊗[K] Frac (B/√0)`. -/
private theorem isPrime_nilradical_tensorProduct_of_isSepClosed (K : Type*) [Field K]
    [IsSepClosed K] (A B : Type*) [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (hA : (nilradical A).IsPrime) (hB : (nilradical B).IsPrime) :
    (nilradical (A ⊗[K] B)).IsPrime := by
  have hAd : IsDomain (A ⧸ nilradical A) := Ideal.Quotient.isDomain _
  have hBd : IsDomain (B ⧸ nilradical B) := Ideal.Quotient.isDomain _
  refine isPrime_nilradical_of_ker_le_nilradical
    (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K (nilradical A))
      (Ideal.Quotient.mkₐ K (nilradical B))) ?_ ?_
  · rw [Algebra.TensorProduct.map_ker _ _ (Ideal.Quotient.mkₐ_surjective K _)
      (Ideal.Quotient.mkₐ_surjective K _), ← RingHom.ker_coe_toRingHom,
      ← RingHom.ker_coe_toRingHom (Ideal.Quotient.mkₐ K (nilradical B)),
      Ideal.Quotient.mkₐ_ker, Ideal.Quotient.mkₐ_ker]
    exact sup_le (map_nilradical_le _) (map_nilradical_le _)
  · have hF : (nilradical ((A ⧸ nilradical A) ⊗[K]
        FractionRing (B ⧸ nilradical B))).IsPrime := by
      rw [← PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical]
      exact geomPure_baseChange_irreducible K (A ⧸ nilradical A)
        (FractionRing (B ⧸ nilradical B))
        (IntermediateField.eq_bot_of_isSepClosed_of_isSeparable _)
    exact isPrime_nilradical_of_injective _
      (injective_tensorProduct_map_id (R := A ⧸ nilradical A)
        (IsScalarTower.toAlgHom K (B ⧸ nilradical B) (FractionRing (B ⧸ nilradical B)))
        (IsFractionRing.injective _ _)) hF

/-- **The mathematical heart of Stacks 037K**, its step `(3) ⇒ (1)`: if `nilradical (R ⊗[k] ksep)`
is prime for one separably closed extension field `ksep/k`, then `nilradical (R ⊗[k] k')` is prime
for *every* field extension `k'/k`.

Choose a maximal ideal `m` of `ksep ⊗[k] k'`, which is nonzero being a tensor product of nonzero
`k`-vector spaces, and put `F := (ksep ⊗[k] k') ⧸ m`; this is a field receiving both `ksep` and
`k'`. Over the separably closed `ksep`, Stacks 00I7 applied to the pair `F`, `ksep ⊗[k] R` gives
that `nilradical (F ⊗[ksep] (ksep ⊗[k] R))` is prime, and that ring is `R ⊗[k] F` by
`Algebra.TensorProduct.cancelBaseChange`. Finally `R ⊗[k] k'` is a subring of `R ⊗[k] F`, so it
inherits a prime nilradical.

Only `IsSepClosed ksep` is used, not that `ksep` is algebraic over `k`. -/
@[ega "IV 4.3.3" "forward implication"]
private theorem isPrime_nilradical_tensorProduct_of_isSepClosed_extension {k R : Type*} [Field k]
    [CommRing R] [Algebra k R] (ksep : Type*) [Field ksep] [Algebra k ksep] [IsSepClosed ksep]
    (k' : Type*) [Field k'] [Algebra k k'] (h : (nilradical (R ⊗[k] ksep)).IsPrime) :
    (nilradical (R ⊗[k] k')).IsPrime := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (ksep ⊗[k] k')
  have hF : (nilradical ((ksep ⊗[k] k') ⧸ m)).IsPrime := by
    rw [nilradical_eq_bot_iff.2 inferInstance]; exact Ideal.isPrime_bot
  have hR : (nilradical (ksep ⊗[k] R)).IsPrime :=
    isPrime_nilradical_of_injective (Algebra.TensorProduct.comm k ksep R) (AlgEquiv.injective _) h
  have hRF : (nilradical (R ⊗[k] ((ksep ⊗[k] k') ⧸ m))).IsPrime :=
    isPrime_nilradical_of_injective
      (((Algebra.TensorProduct.cancelBaseChange k ksep ksep ((ksep ⊗[k] k') ⧸ m)
            R).toRingEquiv.trans
          (Algebra.TensorProduct.comm k ((ksep ⊗[k] k') ⧸ m) R).toRingEquiv).symm)
      (RingEquiv.injective _)
      (isPrime_nilradical_tensorProduct_of_isSepClosed ksep _ _ hF hR)
  exact isPrime_nilradical_of_injective _
    (injective_tensorProduct_map_id (R := R)
      ((Ideal.Quotient.mkₐ k m).comp Algebra.TensorProduct.includeRight)
      (RingHom.injective _)) hRF

/-- **Stacks 037K.** Let `k` be a field, `R` a commutative `k`-algebra, `k^{sep}` a separable
closure of `k` and `k̄` an algebraic closure of `k`. The following are equivalent:
1. the spectrum of `R ⊗[k] k'` is irreducible for every field extension `k'/k`;
2. the spectrum of `R ⊗[k] k'` is irreducible for every finite separable field extension `k'/k`;
3. the spectrum of `R ⊗[k] k^{sep}` is irreducible;
4. the spectrum of `R ⊗[k] k̄` is irreducible;
5. `Spec R ⟶ Spec k` is geometrically irreducible. -/
public theorem solution (k R : Type u) [Field k]
    [CommRing R] [Algebra k R] (ksep kbar : Type u) [Field ksep] [Algebra k ksep]
    [IsSepClosure k ksep] [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar] :
    List.TFAE
      [∀ (k' : Type u) [Field k'] [Algebra k k'], IrreducibleSpace (PrimeSpectrum (R ⊗[k] k')),
        ∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k']
          [Algebra.IsSeparable k k'], IrreducibleSpace (PrimeSpectrum (R ⊗[k] k')),
        IrreducibleSpace (PrimeSpectrum (R ⊗[k] ksep)),
        IrreducibleSpace (PrimeSpectrum (R ⊗[k] kbar)),
        GeometricallyIrreducible (Spec.map (ofHom (algebraMap k R)))] := by
  have : IsSepClosed ksep := IsSepClosure.sep_closed k
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : Algebra.IsAlgebraic k ksep := Algebra.IsIntegral.isAlgebraic
  tfae_have 1 → 2 := fun h k' _ _ _ _ => h k'
  tfae_have 2 → 3 := by
    intro h2
    rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical]
    exact isPrime_nilradical_tensorProduct_of_forall_finiteDimensional (R := R) fun E _ =>
      PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.1 (h2 E)
  tfae_have 3 → 1 := by
    intro h3 k' _ _
    rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical] at h3 ⊢
    exact isPrime_nilradical_tensorProduct_of_isSepClosed_extension ksep k' h3
  tfae_have 1 → 4 := fun h => h kbar
  tfae_have 4 → 3 := by
    intro h4
    rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical] at h4 ⊢
    exact isPrime_nilradical_of_injective _
      (injective_tensorProduct_map_id (R := R) (IsAlgClosed.lift : ksep →ₐ[k] kbar)
        (RingHom.injective _)) h4
  tfae_have 1 ↔ 5 :=
    (Algebra.isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_tensorProduct k R).symm
  tfae_finish

end Stacks.Irreducibility.SeparableCriteria

/-!
# Criteria for geometric irreducibility of an algebra over a field

Let `k` be a field and let `R` be a commutative `k`-algebra. Recall that `R` is *geometrically
irreducible* over `k` when the spectrum of `R ⊗[k] k'` is an irreducible topological space for
every field extension `k'/k` (Stacks 037L). Testing every extension is unnecessary: it suffices
to test the finite separable ones, and in fact the single extension `k^{sep}/k` given by a
separable closure of `k`, or the single extension `k̄/k` given by an algebraic closure.

Indeed, a minimal prime of `R ⊗[k] k^{sep}` contracts to a minimal prime in each finite
subextension, because `R ⊗[k] k' → R ⊗[k] k^{sep}` is flat and flat maps satisfy going down, and
`k^{sep}` is the union of those subextensions; so two minimal primes of `R ⊗[k] k^{sep}` already
agree. The extension `k̄/k^{sep}` is purely inseparable, hence induces a homeomorphism
on spectra after base change, which passes irreducibility from `k^{sep}` to `k̄`. Finally, an
arbitrary extension `k'/k` embeds together with `k̄` into a common field `F`; over the separably
closed field `k̄` the ring `R ⊗[k] F = (R ⊗[k] k̄) ⊗_{k̄} F` has a unique minimal prime, and
`R ⊗[k] k' → R ⊗[k] F` is flat and injective, so `R ⊗[k] k'` has a unique minimal prime too.

## Main results

* `AlgebraicGeometry.geometricallyIrreducible_tfae`, Stacks 037K: the four conditions of the
  source — irreducible spectrum after base change along every field extension, along every finite
  separable field extension, along a separable closure, along an algebraic closure — are
  equivalent, and equivalent to Mathlib's `AlgebraicGeometry.GeometricallyIrreducible` for the
  morphism `Spec R ⟶ Spec k`.

## Implementation notes

The source's conditions (1)–(4) are items 1–4 of the `List.TFAE`, in the source's order and
in the source's algebraic form: `IrreducibleSpace (PrimeSpectrum (R ⊗[k] k'))`, with the tensor
factors in the order for which Mathlib's `AlgebraicGeometry.pullbackSpecIso` identifies
`Spec R ×_{Spec k} Spec k'` with `Spec (R ⊗[k] k')`. Item 5 is added: it is condition (1) in
Mathlib's own spelling, the morphism property `AlgebraicGeometry.GeometricallyIrreducible` applied
to `Spec R ⟶ Spec k`, which is how tags 0G31, 0G32 and 0G33 say "geometrically irreducible".
Unfolded, that property tests every field `k'` and every morphism `Spec k' ⟶ Spec k`, that is
every field extension `k'/k`, so items 1 and 5 say the same thing; carrying the bridge inside the
equivalence rather than asserting it in prose is what lets a user move between the algebraic and
the scheme-theoretic form. `IrreducibleSpace` demands nonemptiness, matching the source's footnote
to Definition 037L that an irreducible space is nonempty.

Conditions (3) and (4) name "the" separable algebraic closure and "the" algebraic closure of `k`.
They are stated here for an arbitrary separable closure `k^{sep}` and an arbitrary algebraic
closure `k̄`, given abstractly as hypotheses `IsSepClosure k ksep` and `IsAlgClosure k kbar`
rather than as the constructions `SeparableClosure k` and `AlgebraicClosure k`; since those
constructions witness the hypotheses, this is the source's statement for every choice at once, and
no user has to transport along an isomorphism of closures.

All types are taken in a single universe `u`, as they must be for `k → R` to be a morphism of
`CommRingCat`, and the test fields of items 1, 2 and 5 range over that universe. This is not a
restriction on the mathematics: by item 4 the whole condition is decided by the single extension
`k̄/k`, which lives in the universe of `k`, so the property tested against extensions in one
universe agrees with the property tested against extensions in any.

Faithfulness to the source: (1) no hypothesis is idle — `Field k`, `CommRing R` and `Algebra k R`
are the data of the `k`-algebra `R` and are used by every item, while `ksep` and `kbar` with their
closure hypotheses are exactly what items 3 and 4 speak about. (2) The scalars and base are the
source's: every tensor product is over `k` itself and every base change is of `R` along an
extension of `k`, with no closure or localization silently substituted for the base. (3) The maps
the source names are pinned: the structure map is `algebraMap k R`, the extension `k'/k` acts
through `algebraMap k k'` in the tensor product and through its own morphism `Spec k' ⟶ Spec k` in
item 5. (4) The instantiation is not degenerate: for `R = k[X]` all five conditions hold, since
`k[X] ⊗[k] k' ≅ k'[X]` is a domain, while for `k = ℚ` and `R = ℚ(i)` all five fail, since
`ℚ(i) ⊗[ℚ] ℚ(i)` has two minimal primes.

## References

* [Stacks Project, Tag 037K](https://stacks.math.columbia.edu/tag/037K)
-/




open AlgebraicGeometry CommRingCat TensorProduct

/-- **Stacks 037K.** Let `k` be a field, `R` a commutative `k`-algebra, `k^{sep}` a separable
closure of `k` and `k̄` an algebraic closure of `k`. The following are equivalent:
1. the spectrum of `R ⊗[k] k'` is irreducible for every field extension `k'/k`;
2. the spectrum of `R ⊗[k] k'` is irreducible for every finite separable field extension `k'/k`;
3. the spectrum of `R ⊗[k] k^{sep}` is irreducible;
4. the spectrum of `R ⊗[k] k̄` is irreducible;
5. `Spec R ⟶ Spec k` is geometrically irreducible. -/
@[stacks 037K]
public theorem AlgebraicGeometry.geometricallyIrreducible_tfae (k R : Type u) [Field k]
    [CommRing R] [Algebra k R] (ksep kbar : Type u) [Field ksep] [Algebra k ksep]
    [IsSepClosure k ksep] [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar] :
    List.TFAE
      [∀ (k' : Type u) [Field k'] [Algebra k k'], IrreducibleSpace (PrimeSpectrum (R ⊗[k] k')),
        ∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k']
          [Algebra.IsSeparable k k'], IrreducibleSpace (PrimeSpectrum (R ⊗[k] k')),
        IrreducibleSpace (PrimeSpectrum (R ⊗[k] ksep)),
        IrreducibleSpace (PrimeSpectrum (R ⊗[k] kbar)),
        GeometricallyIrreducible (Spec.map (ofHom (algebraMap k R)))] :=
    by apply Stacks.Irreducibility.SeparableCriteria.solution

/-!
# Geometric irreducibility over a separably closed field

Proof of `Algebra.isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum`: for a
separably algebraically closed field `k` and a `k`-algebra `R`, the algebra `R` is geometrically
irreducible over `k` if and only if `Spec R` is irreducible.

Geometric irreducibility asks that `Spec (R ⊗[k] k')` be irreducible for every field extension
`k'/k`, of which irreducibility of `Spec R` is the single instance `k' = k`. By Lemma 037K one
extension already decides the whole family, namely a separable closure of `k`; a separably closed
field is its own separable closure, so here that one extension is `k` itself and `R ⊗[k] k ≅ R`.

## Main results

* `Stacks.Irreducibility.SepClosedField.solution`: the statement of Stacks Tag 037M.

## Implementation notes

Lemma 037K is `AlgebraicGeometry.geometricallyIrreducible_tfae`: its fifth item is geometric
irreducibility as `Algebra.IsGeometricallyIrreducible` spells it and its third is irreducibility
of `Spec (R ⊗[k] k^{sep})` for a separable closure `k^{sep}` of `k`, so the two sides of this
lemma are those two items with `k^{sep} := k`. That choice is admissible because `IsSepClosed k`
gives `IsSepClosure k k`, and the algebraic closure the equivalence also speaks about is named by
`AlgebraicClosure k`; neither witness appears in the conclusion, so no generality is lost.

What remains is to identify the base change `R ⊗[k] k` with `R`, which is transport of
irreducibility along `Algebra.TensorProduct.rid`.

## References

* [Stacks Project, Tag 037M](https://stacks.math.columbia.edu/tag/037M)
-/

namespace Stacks.Irreducibility.SepClosedField

/-- Over a separably closed field `k`, a `k`-algebra `R` is geometrically irreducible if and
only if `Spec R` is irreducible: Stacks 037K with `k^{sep} := k`, followed by the identification
`R ⊗[k] k ≅ R`. -/
public theorem solution (k R : Type u) [Field k] [IsSepClosed k] [CommRing R] [Algebra k R] :
    Algebra.IsGeometricallyIrreducible k R ↔ IrreducibleSpace (PrimeSpectrum R) :=
  ((AlgebraicGeometry.geometricallyIrreducible_tfae k R k (AlgebraicClosure k)).out 5 3).trans
    (PrimeSpectrum.homeomorphOfRingEquiv
      (Algebra.TensorProduct.rid k k R).toRingEquiv).irreducibleSpace_iff

end Stacks.Irreducibility.SepClosedField

/-!
# Geometrically irreducible algebras over a separably closed field

Let `k` be a field and let `R` be a `k`-algebra. Recall that `R` is *geometrically irreducible
over `k`* when the spectrum of `R ⊗[k] k'` is irreducible for every field extension `k'/k`
[stacks, 037L]. This is in general strictly stronger than irreducibility of `Spec R` itself,
which is the case `k' = k`: `Spec (ℚ(i))` is a point, while `ℚ(i) ⊗[ℚ] ℚ(i) ≅ ℚ(i) × ℚ(i)` has
two minimal primes, so `ℚ(i)` is not geometrically irreducible over `ℚ`. Over a separably
algebraically closed base nothing is gained by base changing, and the two conditions agree.
Indeed geometric irreducibility need only be tested on the finite separable extensions of `k`,
equivalently on a separable closure of `k` [stacks, 037K], and a separably closed field is its
own separable closure.

## Main results

* `Algebra.isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum`: over a separably
  closed field `k`, a `k`-algebra `R` is geometrically irreducible over `k` if and only if
  `Spec R` is irreducible.

## Implementation notes

Geometric irreducibility is `Algebra.IsGeometricallyIrreducible` [stacks, 037L], which in this
tree is the morphism property `AlgebraicGeometry.GeometricallyIrreducible` applied to the
structure morphism `Spec R ⟶ Spec k`; that abbreviation, rather than the quantifier over
tensor products, is what tags 037K, 0G31, 0G32 and 0G33 use for the notion, and
`Algebra.isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_tensorProduct` is the
equivalence with the source's own sentence. Because that definition passes through `Spec`, the
field `k` and the algebra `R` lie in a common universe here, where the connected analogue
[stacks, 037U] leaves `R` in a universe of its own; by 037K the condition is decided by a single
extension living in the universe of `k`, so this is no restriction on the mathematics.

The right-hand side is the *absolute* spectrum `PrimeSpectrum R`, in the algebraic spelling that
tags 037K and 037U use for the same kind of conclusion, and not the carrier of the scheme
`Spec R`; the two are homeomorphic, and stating the algebraic form keeps the lemma usable
without going through the scheme-theoretic API.

Separable closedness is the exact hypothesis, rather than algebraic closedness, and it is not
removable: if `k` is not separably closed it has a nontrivial finite separable extension `k'/k`,
and then `R = k'` has a one-point, hence irreducible, spectrum while `k' ⊗[k] k'` is a product
of at least two fields, whose spectrum is not irreducible.

Faithfulness to the source. (1) No hypothesis is idle: `IsSepClosed k` is what the reverse
implication needs, and is necessary as just explained, while `Field k`, `CommRing R` and
`Algebra k R` are exactly the data of the `k`-algebra `R` and occur on both sides through
`algebraMap k R`. (2) The scalars and base are the source's: geometric irreducibility is taken
over `k` itself, with every tensor product over `k` and no closure of `k` silently substituted
for the base, and the right-hand side is the spectrum of `R` itself rather than of a base change.
(3) The maps the source names are pinned: the geometric side is base change along the morphism
`Spec.map (ofHom (algebraMap k R))` determined by the structure map, and the identification of
the case `k' = k` with the right-hand side is the canonical isomorphism `R ⊗[k] k ≅ R`, not an
arbitrary one. (4) The instantiation is not degenerate in either direction: with
`k = AlgebraicClosure ℚ`, which is separably closed, both sides hold for `R = k[X]`, since
`k[X] ⊗[k] k' ≅ k'[X]` is a domain, both fail for `R = k × k`, whose spectrum is two points, and
both fail for the zero algebra, whose spectrum is empty while an irreducible space is nonempty.

## References

* [stacks, Tag 037M]
-/




/-- **Stacks 037M.** Let `k` be a separably algebraically closed field and let `R` be a
`k`-algebra. Then `R` is geometrically irreducible over `k` if and only if the spectrum of `R`
is irreducible. -/
@[stacks 037M]
public theorem Algebra.isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum
    (k R : Type u) [Field k] [IsSepClosed k] [CommRing R] [Algebra k R] :
    Algebra.IsGeometricallyIrreducible k R ↔ IrreducibleSpace (PrimeSpectrum R) :=
    by apply Stacks.Irreducibility.SepClosedField.solution

end
