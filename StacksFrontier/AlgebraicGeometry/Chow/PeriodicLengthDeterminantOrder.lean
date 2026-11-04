module

public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Support
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.Basic
public import StacksFrontier.RingTheory.Support.Finite
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite-length submodules of a module filtered by a prime quotient

Let `R` be a Noetherian local ring and `q` a prime of `R` other than the maximal ideal. A
module carrying a finite filtration whose successive factors are all isomorphic to `R / q`
has no nonzero submodule of finite length: its only associated prime is `q`, while a nonzero
finite-length module over a local ring has the closed point in its support.

## Main results

* `Module.FiniteLength.subsingleton_of_isFiniteLength_of_associatedPrimes_subset`: a
  finite-length module whose associated primes are contained in `{q}` is zero.
* `Module.FiniteLength.eq_bot_of_isFiniteLength_of_le_span`: a finite-length submodule of the
  span of a sequence with successive factors `R / q` is zero.
* `Module.FiniteLength.inf_eq_of_isFiniteLength_map_mkQ`: a submodule containing `W` meets a
  submodule `V` with `V / W` so filtered in exactly `W`, as soon as the intersection has
  finite length modulo `W`.
* `Module.FiniteLength.length_quotient_eq_add_of_surjective`: colength is additive along a
  surjection.
* `Module.FiniteLength.length_quotient_eq_add_of_isFiniteLength_map_mkQ`: the resulting
  colength identity with the intersection replaced by `W`.

## Implementation notes

Filtrations use the subquotient presentation of Tag 02QC: a sequence `x : Fin l → M` whose
`i`-th factor is the quotient of `spanBefore x i ⊔ R ∙ x i` by `spanBefore x i`. The
auxiliary span `Module.FiniteLength.spanPrefix` indexes an initial segment by a natural
number rather than by an element of `Fin l`, which is what the induction along the filtration
needs.

## References

* [Stacks Project, Tag 02QD](https://stacks.math.columbia.edu/tag/02QD)
-/

@[expose] public section

namespace Module.FiniteLength

universe u v w

/-- The submodule spanned by the entries of `x` with index below `n`. Unlike
`Module.FiniteLength.spanBefore`, the cut-off is a natural number rather than an index, which
is what the inductions along a filtration need. -/
def spanPrefix {R : Type u} {M : Type v} [Ring R] [AddCommGroup M]
    [Module R M] {l : ℕ} (x : Fin l → M) (n : ℕ) : Submodule R M :=
  Submodule.span R (x '' {i | i.val < n})

/-- `spanBefore` is `spanPrefix` cut off at the value of the index. -/
theorem spanBefore_eq_spanPrefix {R : Type u} {M : Type v} [Ring R]
    [AddCommGroup M] [Module R M] {l : ℕ} (x : Fin l → M) (i : Fin l) :
    spanBefore (R := R) x i = spanPrefix x i.val :=
  rfl

/-- Lengthening the prefix by one adds the span of the new entry. -/
theorem spanPrefix_succ {R : Type u} {M : Type v} [Ring R]
    [AddCommGroup M] [Module R M] {l : ℕ} (x : Fin l → M) (n : ℕ) (hn : n < l) :
    spanPrefix x (n + 1) = spanPrefix x n ⊔ R ∙ x ⟨n, hn⟩ := by
  have himage : x '' {i | i.val < n + 1} = (x '' {i | i.val < n}) ∪ {x ⟨n, hn⟩} := by
    ext z
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      by_cases h : i.val < n
      · exact Or.inl ⟨i, h, rfl⟩
      · exact Or.inr (congrArg x (Fin.ext (show i.val = n by omega)))
    · rintro (⟨i, hi, rfl⟩ | rfl)
      · exact ⟨i, by omega, rfl⟩
      · exact ⟨⟨n, hn⟩, Nat.lt_succ_self n, rfl⟩
  unfold spanPrefix
  rw [himage, Submodule.span_union]

/-- The full prefix is the span of all the entries. -/
theorem spanPrefix_length {R : Type u} {M : Type v} [Ring R]
    [AddCommGroup M] [Module R M] {l : ℕ} (x : Fin l → M) :
    spanPrefix x l = Submodule.span R (Set.range x) := by
  simp [spanPrefix]

/-- Extending a submodule by a factor isomorphic to `R / q` adds at most `q` to the set of
associated primes. -/
theorem associatedPrimes_subset_of_extension
    {R : Type u} {M : Type v} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] (U V : Submodule R M) (hUV : U ≤ V)
    (q : Ideal R) [q.IsPrime] (e : (V ⧸ U.submoduleOf V) ≃ₗ[R] R ⧸ q) :
    associatedPrimes R V ⊆ associatedPrimes R U ∪ {q} := by
  have hrange : LinearMap.range (Submodule.inclusion hUV) = U.submoduleOf V := by
    ext z
    exact ⟨fun ⟨u, hu⟩ => hu ▸ u.property, fun hz => ⟨⟨z.1, hz⟩, rfl⟩⟩
  have hexact : Function.Exact (Submodule.inclusion hUV) (U.submoduleOf V).mkQ := by
    rw [LinearMap.exact_iff, Submodule.ker_mkQ, hrange]
  have hsub := associatedPrimes.subset_union_of_exact
    (f := Submodule.inclusion hUV) (g := (U.submoduleOf V).mkQ)
    (Submodule.inclusion_injective hUV) hexact
  rwa [show associatedPrimes R (V ⧸ U.submoduleOf V) = {q} by
    rw [LinearEquiv.AssociatedPrimes.eq e,
      associatedPrimes.eq_singleton_of_isPrimary (Ideal.IsPrime.isPrimary ‹q.IsPrime›),
      Ideal.IsPrime.radical ‹q.IsPrime›]] at hsub

/-- A module filtered with all factors isomorphic to `R / q` has no associated prime other
than `q`. -/
theorem associatedPrimes_spanPrefix_subset
    {R : Type u} {M : Type v} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] {l : ℕ} (q : Ideal R) [q.IsPrime]
    (x : Fin l → M)
    (hxf : ∀ i : Fin l,
      Nonempty
        (((spanBefore (R := R) x i ⊔ R ∙ x i : Submodule R M) ⧸
            (spanBefore (R := R) x i).comap
              (spanBefore (R := R) x i ⊔ R ∙ x i : Submodule R M).subtype) ≃ₗ[R]
          R ⧸ q))
    (n : ℕ) (hn : n ≤ l) :
    associatedPrimes R (spanPrefix (R := R) x n) ⊆ {q} := by
  induction n with
  | zero =>
    rw [show spanPrefix (R := R) x 0 = (⊥ : Submodule R M) by simp [spanPrefix],
      associatedPrimes.eq_empty_of_subsingleton (R := R) (M := ↥(⊥ : Submodule R M))]
    exact Set.empty_subset _
  | succ n ih =>
    have hnlt : n < l := by omega
    obtain ⟨e⟩ : Nonempty (((spanPrefix (R := R) x n ⊔ R ∙ x ⟨n, hnlt⟩ : Submodule R M) ⧸
        (spanPrefix (R := R) x n).submoduleOf
          (spanPrefix (R := R) x n ⊔ R ∙ x ⟨n, hnlt⟩ : Submodule R M)) ≃ₗ[R] R ⧸ q) :=
      hxf ⟨n, hnlt⟩
    rw [LinearEquiv.AssociatedPrimes.eq (LinearEquiv.ofEq _ _ (spanPrefix_succ x n hnlt))]
    exact (associatedPrimes_subset_of_extension _ _ le_sup_left q e).trans
      (Set.union_subset (ih (by omega)) subset_rfl)

/-- An associated prime of a module lies in its support. -/
theorem mem_support_of_isAssociatedPrime {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] {q : PrimeSpectrum R}
    (hq : IsAssociatedPrime q.asIdeal M) : q ∈ Module.support R M := by
  obtain ⟨-, m, hm⟩ := hq
  refine Module.mem_support_iff_exists_annihilator.mpr ⟨m, ?_⟩
  rw [hm, ← Submodule.bot_colon']
  exact Ideal.le_radical

/-- Over a Noetherian local ring, a module of finite length whose associated primes are all
equal to a prime other than the maximal ideal is zero. -/
theorem subsingleton_of_isFiniteLength_of_associatedPrimes_subset {R : Type u} {T : Type v}
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [AddCommGroup T] [Module R T]
    {q : PrimeSpectrum R} (hq : q ≠ IsLocalRing.closedPoint R) (hT : IsFiniteLength R T)
    (hass : associatedPrimes R T ⊆ {q.asIdeal}) :
    Subsingleton T := by
  by_contra hns
  have : Nontrivial T := not_subsingleton_iff_nontrivial.mp hns
  have : IsNoetherian R T := (isFiniteLength_iff_isNoetherian_isArtinian.mp hT).1
  obtain ⟨p, hp⟩ := associatedPrimes.nonempty R T
  have hmem : q ∈ Module.support R T :=
    mem_support_of_isAssociatedPrime (hass hp ▸ hp)
  rw [support_of_isFiniteLength hT] at hmem
  exact hq hmem

/-- Over a Noetherian local ring, a finite-length submodule of a module whose associated primes
are all equal to a prime other than the maximal ideal is zero. -/
theorem eq_bot_of_isFiniteLength_of_associatedPrimes_subset {R : Type u} {M : Type v}
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    {q : PrimeSpectrum R} (hq : q ≠ IsLocalRing.closedPoint R) {N T : Submodule R M}
    (hass : associatedPrimes R N ⊆ {q.asIdeal}) (hTN : T ≤ N) (hT : IsFiniteLength R T) :
    T = ⊥ := by
  have := subsingleton_of_isFiniteLength_of_associatedPrimes_subset hq hT
    ((associatedPrimes.subset_of_injective (Submodule.inclusion_injective hTN)).trans hass)
  exact Submodule.eq_bot_of_subsingleton

/-- The repair of the unjustified step in Tag 02QD. Over a Noetherian local ring, if the
successive factors of a sequence `x` are all isomorphic to `R / q` for a prime `q` other than
the maximal ideal, then the span of `x` has no nonzero submodule of finite length. -/
theorem eq_bot_of_isFiniteLength_of_le_span {R : Type u} {M : Type v}
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    {l : ℕ} (q : Ideal R) [q.IsPrime] (hq : q ≠ IsLocalRing.maximalIdeal R)
    (x : Fin l → M)
    (hxf : ∀ i : Fin l,
      Nonempty
        (((spanBefore (R := R) x i ⊔ R ∙ x i : Submodule R M) ⧸
            (spanBefore (R := R) x i).comap
              (spanBefore (R := R) x i ⊔ R ∙ x i : Submodule R M).subtype) ≃ₗ[R]
          R ⧸ q))
    {T : Submodule R M} (hTle : T ≤ Submodule.span R (Set.range x))
    (hT : IsFiniteLength R T) :
    T = ⊥ := by
  refine eq_bot_of_isFiniteLength_of_associatedPrimes_subset
    (q := ⟨q, ‹q.IsPrime›⟩) (fun h => hq (congrArg PrimeSpectrum.asIdeal h))
    (N := Submodule.span R (Set.range x)) ?_ hTle hT
  rw [← spanPrefix_length x]
  exact associatedPrimes_spanPrefix_subset q x hxf l le_rfl

/-- The form in which Tag 02QD needs the repair. If `V / W` is spanned by a sequence with
successive factors `R / q` for a prime `q` other than the maximal ideal, and `W ≤ K`, then
`K ⊓ V = W` as soon as `(K ⊓ V) / W` has finite length. -/
theorem inf_eq_of_isFiniteLength_map_mkQ {R : Type u} {M : Type v}
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    {l : ℕ} (q : Ideal R) [q.IsPrime] (hq : q ≠ IsLocalRing.maximalIdeal R)
    {W V K : Submodule R M} (hWV : W ≤ V) (hWK : W ≤ K) (x : Fin l → (M ⧸ W))
    (hxf : ∀ i : Fin l,
      Nonempty
        (((spanBefore (R := R) x i ⊔ R ∙ x i : Submodule R (M ⧸ W)) ⧸
            (spanBefore (R := R) x i).comap
              (spanBefore (R := R) x i ⊔ R ∙ x i : Submodule R (M ⧸ W)).subtype) ≃ₗ[R]
          R ⧸ q))
    (hV : V.map W.mkQ = Submodule.span R (Set.range x))
    (hfin : IsFiniteLength R ((K ⊓ V).map W.mkQ)) :
    K ⊓ V = W := by
  have hle : (K ⊓ V).map W.mkQ ≤ Submodule.span R (Set.range x) := by
    rw [← hV]
    exact Submodule.map_mono inf_le_right
  refine le_antisymm (fun a ha => ?_) (le_inf hWK hWV)
  have hmem : W.mkQ a ∈ (K ⊓ V).map W.mkQ := Submodule.mem_map_of_mem ha
  rw [eq_bot_of_isFiniteLength_of_le_span q hq x hxf hle hfin, Submodule.mem_bot] at hmem
  simpa using (Submodule.Quotient.mk_eq_zero W).mp hmem

/-- Colength is additive along a surjection: for `φ : M →ₗ[R] N` surjective with kernel `K` and
`V` a submodule of `M`, the length of `M ⧸ V` is the length of `K ⧸ (K ⊓ V)` plus the length of
`N ⧸ φ V`. -/
theorem length_quotient_eq_add_of_surjective {R : Type u} {M : Type v} {N : Type w}
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) (hφ : Function.Surjective φ) (V : Submodule R M) :
    Module.length R (M ⧸ V) =
      Module.length R (↥(LinearMap.ker φ) ⧸
          (LinearMap.ker φ ⊓ V).submoduleOf (LinearMap.ker φ)) +
        Module.length R (N ⧸ V.map φ) := by
  have hkereq : (LinearMap.ker φ ⊓ V).submoduleOf (LinearMap.ker φ) =
      LinearMap.ker (V.mkQ ∘ₗ (LinearMap.ker φ).subtype) := by
    ext k
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.mem_inf, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact ⟨And.right, fun h => ⟨k.2, h⟩⟩
  refine Module.length_eq_add_of_exact
    (((LinearMap.ker φ ⊓ V).submoduleOf (LinearMap.ker φ)).liftQ
      (V.mkQ ∘ₗ (LinearMap.ker φ).subtype) hkereq.le)
    (V.mapQ (V.map φ) φ fun _ hv => Submodule.mem_map_of_mem hv)
    (LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ hkereq.le hkereq.ge))
    (fun y => ?_) (LinearMap.exact_iff.mpr ?_)
  · obtain ⟨n, rfl⟩ := (V.map φ).mkQ_surjective y
    obtain ⟨m, rfl⟩ := hφ n
    exact ⟨V.mkQ m, rfl⟩
  · rw [Submodule.ker_mapQ, Submodule.range_liftQ, LinearMap.range_comp,
      Submodule.range_subtype, Submodule.comap_map_eq, Submodule.map_sup,
      Submodule.mkQ_map_self, bot_sup_eq]

/-- The repaired colength identity of Tag 02QD. With `φ : M →ₗ[R] N` surjective with kernel `K`,
a submodule `W ≤ K` such that `V / W` is spanned by a sequence with successive factors `R / q`
for a prime `q` other than the maximal ideal, and `(K ⊓ V) / W` of finite length, the length of
`M ⧸ V` is the length of `K ⧸ W` plus the length of `N ⧸ φ V`. -/
theorem length_quotient_eq_add_of_isFiniteLength_map_mkQ {R : Type u} {M : Type v} {N : Type w}
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {l : ℕ} (q : Ideal R) [q.IsPrime]
    (hq : q ≠ IsLocalRing.maximalIdeal R) (φ : M →ₗ[R] N) (hφ : Function.Surjective φ)
    {W V : Submodule R M} (hWV : W ≤ V) (hWK : W ≤ LinearMap.ker φ) (x : Fin l → (M ⧸ W))
    (hxf : ∀ i : Fin l,
      Nonempty
        (((spanBefore (R := R) x i ⊔ R ∙ x i : Submodule R (M ⧸ W)) ⧸
            (spanBefore (R := R) x i).comap
              (spanBefore (R := R) x i ⊔ R ∙ x i : Submodule R (M ⧸ W)).subtype) ≃ₗ[R]
          R ⧸ q))
    (hV : V.map W.mkQ = Submodule.span R (Set.range x))
    (hfin : IsFiniteLength R ((LinearMap.ker φ ⊓ V).map W.mkQ)) :
    Module.length R (M ⧸ V) =
      Module.length R (↥(LinearMap.ker φ) ⧸ W.submoduleOf (LinearMap.ker φ)) +
        Module.length R (N ⧸ V.map φ) := by
  rw [length_quotient_eq_add_of_surjective φ hφ V,
    inf_eq_of_isFiniteLength_map_mkQ q hq hWV hWK x hxf hV hfin]

end Module.FiniteLength

end
