module

public import StacksFrontier.RingTheory.CompleteLocalRing.CohenStructureTheorem
public import StacksFrontier.RingTheory.NodalChart.Regularity
public import StacksFrontier.RingTheory.RegularLocalRing.Colimit
public import StacksFrontier.RingTheory.RegularLocalRing.Criteria
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A complete local ring is a quotient of a regular local ring of its embedding dimension

Let `(R, 𝔪)` be a Noetherian complete local ring. By the Cohen structure theorem (Stacks 032A)
`R` is a quotient of `Λ[[x_1, …, x_n]]` with `Λ` a field or a Cohen ring, which is a regular local
ring. This file shrinks such a presentation until the regular local ring has the same embedding
dimension as `R`: the minimal number of generators of its maximal ideal, which is its dimension,
equals that of `𝔪`. No coefficient field is needed, so the statement holds in mixed
characteristic.

The shrinking step is the same in every characteristic. Let `φ : S → R` be a surjection from a
regular local ring. If `ker φ ⊆ 𝔪_S²`, then lifting a minimal generating set of `𝔪` to `S` gives a
set generating `𝔪_S` modulo `ker φ ⊆ 𝔪_S²`, hence generating `𝔪_S` by Nakayama, so `S` and `R` have
the same embedding dimension. Otherwise pick `x ∈ ker φ` outside `𝔪_S²`; then `S/xS` is regular
local of embedding dimension one less, and `φ` factors through it. Induction on the embedding
dimension of `S` concludes. The first case is `Stacks.spanFinrank_maximalIdeal_le_of_ker_le_sq`.

## Main results

* `IsRegularLocalRing.exists_surjective_spanFinrank_maximalIdeal_eq`: a local ring which is a
  quotient of a regular local ring is a quotient of one of its own embedding dimension.
* `IsLocalRing.exists_isRegularLocalRing_surjective_spanFinrank_maximalIdeal_eq`: a Noetherian
  complete local ring is a quotient of a regular local ring of its embedding dimension.

## References

* [Stacks Project, Tag 032A](https://stacks.math.columbia.edu/tag/032A)
* [Stacks Project, Tag 00NR](https://stacks.math.columbia.edu/tag/00NR)
-/

@[expose] public section

open IsLocalRing

universe u v

/-- **A quotient of a regular local ring is a quotient of one of its own embedding dimension.**
If a local ring `R` is a quotient of a regular local ring `S`, then it is a quotient of a regular
local ring `S'` whose maximal ideal needs exactly as many generators as that of `R`. The ring `S'`
is `S/(x_1, …, x_k)` for elements `x_i` of the kernel which are successively not in the square of
the maximal ideal. -/
theorem IsRegularLocalRing.exists_surjective_spanFinrank_maximalIdeal_eq {S : Type v}
    {R : Type v} [CommRing S] [CommRing R] [IsRegularLocalRing S] [IsLocalRing R]
    (φ : S →+* R) (hφ : Function.Surjective φ) :
    ∃ (S' : Type v) (_ : CommRing S') (_ : IsRegularLocalRing S') (ψ : S' →+* R),
      Function.Surjective ψ ∧
        (maximalIdeal S').spanFinrank = (maximalIdeal R).spanFinrank := by
  obtain ⟨N, hN⟩ : ∃ N, (maximalIdeal S).spanFinrank = N := ⟨_, rfl⟩
  induction N using Nat.strong_induction_on generalizing S with
  | _ N ih =>
    by_cases hker : RingHom.ker φ ≤ maximalIdeal S ^ 2
    · refine ⟨S, inferInstance, inferInstance, φ, hφ,
        le_antisymm (Stacks.spanFinrank_maximalIdeal_le_of_ker_le_sq φ hφ hker) ?_⟩
      rw [← IsLocalRing.map_maximalIdeal_of_surjective φ hφ]
      exact Ideal.spanFinrank_map_le_of_fg φ (IsNoetherian.noetherian _)
    · obtain ⟨x, hxker, hx2⟩ := Set.not_subset.mp hker
      have : IsLocalHom φ := IsLocalHom.of_surjective φ hφ
      have hx : x ∈ maximalIdeal S := by
        rw [← IsLocalRing.maximalIdeal_comap φ, Ideal.mem_comap, RingHom.mem_ker.mp hxker]
        exact zero_mem _
      have : IsRegularLocalRing (S ⧸ Ideal.span {x}) :=
        Stacks.RegularLocalRing.DirectedColimit.isRegularLocalRing_quotient_span_singleton hx hx2
      have hlt := Stacks.RegularLocalRing.SpanFinrank.spanFinrank_maximalIdeal_succ_le_of_surjective
        (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective hx hx2
        (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x))
      have hspan : Ideal.span {x} ≤ RingHom.ker φ := (Ideal.span_singleton_le_iff_mem _).mpr hxker
      have H : ∀ a ∈ Ideal.span {x}, φ a = 0 := fun a ha => RingHom.mem_ker.mp (hspan ha)
      exact ih _ (by omega) (Ideal.Quotient.lift (Ideal.span {x}) φ H)
        (Ideal.Quotient.lift_surjective_of_surjective _ H hφ) rfl

/-- **A Noetherian complete local ring is a quotient of a regular local ring of its embedding
dimension**, in every characteristic. The Cohen structure theorem (Stacks 032A) presents `R` as a
quotient of `Λ[[x_1, …, x_n]]` with `Λ` a field or a Cohen ring, which is regular local, and
`IsRegularLocalRing.exists_surjective_spanFinrank_maximalIdeal_eq` cuts it down. -/
@[sga "2 IV 4.8",
  sga "2 IX 1.5",
  sga "2 IX 2.3",
  sga "2 XIV 5.2" "more general",
  sga "2 XIV 5.3" "partial"]
theorem IsLocalRing.exists_isRegularLocalRing_surjective_spanFinrank_maximalIdeal_eq
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsRegularLocalRing S) (φ : S →+* R),
      Function.Surjective φ ∧
        (maximalIdeal S).spanFinrank = (maximalIdeal R).spanFinrank := by
  obtain ⟨n, Λ, _, _, hΛ, φ, hφ⟩ :=
    (IsLocalRing.exists_isCoefficientRing_and_exists_surjective_mvPowerSeries R).2
      (IsNoetherian.noetherian _)
  have : IsRegularLocalRing Λ := by
    rcases hΛ with hΛ | hΛ
    · let := hΛ.toField
      infer_instance
    · have := hΛ.isDVR
      infer_instance
  have := MvPowerSeries.isRegularLocalRing Λ n
  exact IsRegularLocalRing.exists_surjective_spanFinrank_maximalIdeal_eq φ hφ
