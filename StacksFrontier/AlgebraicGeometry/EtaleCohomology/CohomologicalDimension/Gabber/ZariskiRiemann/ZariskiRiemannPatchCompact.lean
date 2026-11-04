module

public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Instances.Discrete

/-!
# Quasi-compactness of sets of valuation rings cut out by containment conditions

Let `K` be a field. The valuation subrings `V` of `K` containing a set `R` and in which every
element of a set `P` is a non-unit form a quasi-compact space for the Zariski–Riemann topology,
whose basic open sets are `{V : S ⊆ V}` for finite `S ⊆ K` (Zariski–Samuel, Vol. II, Chapter VI,
§17, Theorem 40). The proof is Tychonoff's: `V ↦ (x ↦ [x ∈ V])` identifies these valuation rings
with a closed subset of the compact space `K → Bool`, and the basic open sets with open subsets.

This is the quasi-compactness of the Zariski–Riemann fibre used in Gabber's germ-killing step
(Travaux de Gabber, Exposé XVIII-A, last remark of §2): the valuation rings centered at a point
`y` of a model are those containing the image `R` of `𝒪_{Y,y}` in which the image `P` of its
maximal ideal consists of non-units.

## Main results

* `ValuationSubring.exists_finset_subcover_of_forall_subset` — a cover of
  `{V : R ⊆ V, ∀ x ∈ P, x⁻¹ ∉ V}` by basic open sets has a finite subcover.

## References

* O. Zariski, P. Samuel, *Commutative Algebra*, Vol. II, Chapter VI, §17, Theorem 40
* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
-/

@[expose] public section

namespace ValuationSubring

variable {K : Type*} [Field K]

/-- The valuation subring of `K` with membership predicate `c`, for `c : K → Bool` closed under
products and sums, containing `-1`, and containing `x` or `x⁻¹` for every `x`. -/
def ofBoolPred (c : K → Bool) (hmul : ∀ a b, c a = true → c b = true → c (a * b) = true)
    (hadd : ∀ a b, c a = true → c b = true → c (a + b) = true) (hneg : c (-1) = true)
    (hinv : ∀ a, c a = true ∨ c a⁻¹ = true) : ValuationSubring K where
  carrier := {x | c x = true}
  mul_mem' {a b} ha hb := hmul a b ha hb
  one_mem' := by simpa using hmul (-1) (-1) hneg hneg
  add_mem' {a b} ha hb := hadd a b ha hb
  zero_mem' := by simpa using hadd 1 (-1) (by simpa using hmul (-1) (-1) hneg hneg) hneg
  neg_mem' {a} ha := by simpa using hmul (-1) a hneg ha
  mem_or_inv_mem' a := hinv a

omit [Field K] in
/-- A set of `K → Bool` cut out by a condition on three coordinates is closed. -/
theorem isClosed_setOf_three (a b d : K) (Q : Bool → Bool → Bool → Prop) :
    IsClosed {c : K → Bool | Q (c a) (c b) (c d)} := by
  have hc : Continuous fun c : K → Bool ↦ (c a, c b, c d) :=
    (continuous_apply a).prodMk ((continuous_apply b).prodMk (continuous_apply d))
  exact (isClosed_discrete {t : Bool × Bool × Bool | Q t.1 t.2.1 t.2.2}).preimage hc

/-- **Quasi-compactness of the Zariski–Riemann space cut out by containment conditions.** Let
`R, P ⊆ K` and let `S i` be finite subsets of `K`. If every valuation subring `V` of `K`
containing `R` and with `x⁻¹ ∉ V` for all `x ∈ P` contains some `S i`, then finitely many of the
`S i` suffice. -/
theorem exists_finset_subcover_of_forall_subset (R P : Set K) {I : Type*} (S : I → Finset K)
    (hcov : ∀ V : ValuationSubring K, (∀ r ∈ R, r ∈ V) → (∀ x ∈ P, x⁻¹ ∉ V) →
      ∃ i, ∀ x ∈ S i, x ∈ V) :
    ∃ J : Finset I, ∀ V : ValuationSubring K, (∀ r ∈ R, r ∈ V) → (∀ x ∈ P, x⁻¹ ∉ V) →
      ∃ i ∈ J, ∀ x ∈ S i, x ∈ V := by
  classical
  let C : Set (K → Bool) :=
    (⋂ a : K, ⋂ b : K, {c | c a = true → c b = true → c (a * b) = true}) ∩
    (⋂ a : K, ⋂ b : K, {c | c a = true → c b = true → c (a + b) = true}) ∩
    {c | c (-1) = true} ∩ (⋂ a : K, {c | c a = true ∨ c a⁻¹ = true}) ∩
    (⋂ r ∈ R, {c | c r = true}) ∩ (⋂ x ∈ P, {c | c x⁻¹ = false})
  have hC : IsClosed C := by
    refine ((((((isClosed_iInter fun a ↦ isClosed_iInter fun b ↦
      isClosed_setOf_three a b (a * b) fun s t r ↦ s = true → t = true → r = true).inter
      (isClosed_iInter fun a ↦ isClosed_iInter fun b ↦
      isClosed_setOf_three a b (a + b) fun s t r ↦ s = true → t = true → r = true)).inter
      (isClosed_setOf_three (-1) (-1) (-1) fun s _ _ ↦ s = true)).inter
      (isClosed_iInter fun a ↦
      isClosed_setOf_three a a⁻¹ a fun s t _ ↦ s = true ∨ t = true)).inter
      (isClosed_biInter fun r _ ↦ isClosed_setOf_three r r r fun s _ _ ↦ s = true)).inter
      (isClosed_biInter fun x _ ↦ isClosed_setOf_three x⁻¹ x⁻¹ x⁻¹ fun s _ _ ↦ s = false))
  let ev : ValuationSubring K → K → Bool := fun V x ↦ decide (x ∈ V)
  have hev : ∀ V : ValuationSubring K, (∀ r ∈ R, r ∈ V) → (∀ x ∈ P, x⁻¹ ∉ V) → ev V ∈ C := by
    intro V hR hP
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;>
      simp only [Set.mem_iInter, Set.mem_setOf_eq, ev, decide_eq_true_eq, decide_eq_false_iff_not]
    exacts [fun a b ha hb ↦ V.mul_mem _ _ ha hb, fun a b ha hb ↦ V.add_mem _ _ ha hb,
      V.neg_mem _ V.one_mem, V.mem_or_inv_mem, hR, hP]
  let O : I → Set (K → Bool) := fun i ↦ ⋂ x ∈ S i, {c | c x = true}
  have hO : ∀ i, IsOpen (O i) := fun i ↦ isOpen_biInter_finset fun x _ ↦
    show IsOpen ((fun c : K → Bool ↦ c x) ⁻¹' ({true} : Set Bool)) from
      (isOpen_discrete ({true} : Set Bool)).preimage (continuous_apply x)
  have hcover : C ⊆ ⋃ i, O i := by
    rintro c ⟨⟨⟨⟨⟨hmul, hadd⟩, hneg⟩, hinv⟩, hR⟩, hP⟩
    simp only [Set.mem_iInter, Set.mem_setOf_eq] at hmul hadd hneg hinv hR hP
    let V := ofBoolPred c hmul hadd hneg hinv
    obtain ⟨i, hi⟩ := hcov V hR fun x hx h ↦ Bool.false_ne_true ((hP x hx).symm.trans h)
    exact Set.mem_iUnion.2 ⟨i, Set.mem_iInter₂.2 fun x hx ↦ hi x hx⟩
  obtain ⟨J, hJ⟩ := hC.isCompact.elim_finite_subcover O hO hcover
  refine ⟨J, fun V hR hP ↦ ?_⟩
  obtain ⟨i, hiJ, hi⟩ := Set.mem_iUnion₂.1 (hJ (hev V hR hP))
  refine ⟨i, hiJ, fun x hx ↦ ?_⟩
  simpa [ev] using Set.mem_iInter₂.1 hi x hx

end ValuationSubring

end
