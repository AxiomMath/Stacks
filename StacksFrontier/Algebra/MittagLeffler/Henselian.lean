module

import Mathlib.Tactic.ReduceModChar
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.RingTheory.Coalgebra.CoassocSimps

public import StacksFrontier.RingTheory.Henselian.FiniteType.StrictlyHenselian
public import StacksFrontier.Algebra.MittagLeffler.ShortExact
public import StacksFrontier.Algebra.MittagLeffler.Basic
public import StacksFrontier.Algebra.MittagLeffler.Endomorphism
import StacksFrontier.LinearAlgebra.DirectSum.CountablyGenerated

@[expose] public section

universe u v w

/-!
# Countably generated Mittag-Leffler modules over a henselian local ring

Let `R` be a henselian local ring and `M` a countably generated Mittag-Leffler `R`-module. This
file proves Stacks 05D6: `M` is a direct sum of finitely presented `R`-modules, in the internal
form — an independent set of finitely presented submodules of `M` with supremum `⊤`.

The argument is the source's. Everything rests on the claim that for every `x ∈ M` there is a
direct sum decomposition `M = N ⊕ K` with `x ∈ N`, the summand `N` finitely presented and `K`
again Mittag-Leffler and countably generated: granting it, a countable generating sequence
`x₀, x₁, …` of `M` is absorbed one element at a time into a growing direct sum of finitely
presented summands, and the summands split off are independent with supremum `⊤` because at each
stage what is left is a complement of what has been used.

The claim rests in turn on one statement about a single endomorphism. Over a henselian local ring,
an endomorphism `α` of `M` with `α · p(α) = 0` for some monic `p ∈ R[T]` splits off a direct
summand through any vector it fixes: there is an idempotent `E` with `x ∈ Im E ⊆ Im α`. For
`x ∈ M`, Stacks 05D2 provides such an `α` fixing `x` and factoring as `α = v ∘ u` through a
finitely presented module `Q`; the endomorphism `u ∘ v` of `Q` satisfies a monic polynomial `p`
(Stacks 05BT), and `v` intertwines `u ∘ v` with `α`, whence `α · p(α) = 0`. So `Im E` is a direct
summand containing `x`, with complement `Ker E`; it is finitely generated, being contained in
`Im v` and fixed by `E`, and Mittag-Leffler as a direct summand, hence finitely presented by
Stacks 059R (1). The complement `Ker E` is Mittag-Leffler for the same reason, and countably
generated as an image of `M`.

The splitting is where the hypotheses on `R` are consumed. Splitting off the exact power of `T - 1`
in the reduction `p̄ ∈ κ[T]` and lifting the resulting coprime factorization along the henselian
hypothesis (Stacks 04GG (3)) gives `p = q₂ q₁` in `R[T]` with `q₂ ≡ (T - 1)ᵉ` and `q₁(1)` a unit.
As `T q₁` and `q₂` have coprime reductions, Nakayama's lemma in the finite `R`-algebra `R[T]/(T p)`
produces `c, d, h` with `c · T q₁ + d · q₂ = 1 + T p · h`, so `E = (c · T q₁)(α)` and
`F = (d · q₂)(α)` satisfy `E + F = 1` and `E F = 0`, hence `E` is idempotent. Its image is the
image of `α q₁(α)`, which lies in `Im α` and contains `x` because `α q₁(α) x = q₁(1) x` with
`q₁(1)` a unit.

## Main results

* `Stacks.MittagLeffler.OverHenselianRing.solution`: the proof of Stacks 05D6, as stated in
  `Module.exists_sSupIndep_finitePresentation_of_countable_span_of_mittagLeffler`.

## Implementation notes

The source's factorization is of `T²P` rather than of `P`, with `P` a monic polynomial killing
`π ∘ α ∘ i`. Here the monic polynomial is taken for `u ∘ v` instead, for which the intertwining
identity `p(α) ∘ v = v ∘ p(u ∘ v)` gives `α · p(α) = 0` directly, so one factor `T` suffices
throughout; and the exponent of `T - 1` is taken to be its exact multiplicity in `p̄`, which makes
`q₁(1)` a unit by construction and removes the source's separate argument that the annihilator of
a nonzero `x` lies in the maximal ideal.

The source reads off the two summands as the images of `α²q₁(α)` and of `q₂(α)`. Here the second
summand is read off as `Ker E` instead, the two descriptions agreeing because `E` is idempotent;
this keeps the polynomial `q₂` out of everything downstream of the splitting.

The two summands are complementary submodules of `M`, not an external direct sum, so the descent of
the Mittag-Leffler property to them is Stacks 059N (1) for the split — hence universally injective
— inclusion of a summand, which is what the proof of Stacks 059P uses for its own summands.

The two hypotheses on `M` travel together through the induction, so they are bundled as the private
`IsMLCG`: countably generated, spelled as the existence of a countable spanning set, and
Mittag-Leffler, spelled as the private `IsML`; both are the spellings of the statement. That this
class is stable under passing to a direct summand (`IsMLCG.of_isCompl`) is what lets the induction
repeat.

## References

* [StacksProject 05D6](https://stacks.math.columbia.edu/tag/05D6)
-/

namespace Stacks.MittagLeffler.OverHenselianRing

open Polynomial IsLocalRing Submodule



/-- Being Mittag-Leffler, in the intrinsic form of Stacks 059E (1): every map `f : P → M` from a
finitely presented module dominates and is dominated by a map `g : P → Q` into a finitely presented
module, domination meaning `Ker(f ⊗ id_T) = Ker(g ⊗ id_T)` for every `R`-module `T`. -/
private def IsML (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P] (f : P →ₗ[R] M),
    ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q) (_ : Module.FinitePresentation R Q)
      (g : P →ₗ[R] Q), ∀ (T : Type v) [AddCommGroup T] [Module R T],
        LinearMap.ker (f.rTensor T) = LinearMap.ker (g.rTensor T)

/-- The hypotheses of Stacks 05D6 on a module: countably generated and Mittag-Leffler. The
induction of the source's proof runs inside this class of modules, what is left after splitting off
a finitely presented summand being again in it. -/
private structure IsMLCG (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] :
    Prop where
  /-- `M` has a countable spanning set. -/
  countable_span : ∃ t : Set M, t.Countable ∧ span R t = ⊤
  /-- `M` is Mittag-Leffler. -/
  mittagLeffler : IsML R M

/-! ### Transferring the hypotheses along maps -/

section Transfer

variable {R : Type u} [CommRing R]

/-- A split injection stays injective after tensoring with any module. -/
private lemma rTensor_injective_of_comp_eq_id {A B : Type v} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (s : A →ₗ[R] B) (r : B →ₗ[R] A) (h : r ∘ₗ s = LinearMap.id)
    (T : Type v) [AddCommGroup T] [Module R T] : Function.Injective (s.rTensor T) := by
  have hid : (r.rTensor T) ∘ₗ (s.rTensor T) = LinearMap.id := by
    rw [← LinearMap.rTensor_comp, h, LinearMap.rTensor_id]
  refine Function.LeftInverse.injective (g := r.rTensor T) fun y => ?_
  simpa using LinearMap.congr_fun hid y

/-- Composing with a map that is injective after every base change does not change the kernels of
the base changes. -/
private lemma ker_rTensor_comp {A B C : Type v} [AddCommGroup A] [Module R A] [AddCommGroup B]
    [Module R B] [AddCommGroup C] [Module R C] (f : A →ₗ[R] B) (s : B →ₗ[R] C) (T : Type v)
    [AddCommGroup T] [Module R T] (hs : Function.Injective (s.rTensor T)) :
    LinearMap.ker ((s ∘ₗ f).rTensor T) = LinearMap.ker (f.rTensor T) := by
  rw [LinearMap.rTensor_comp, LinearMap.ker_comp, LinearMap.ker_eq_bot.2 hs, Submodule.comap_bot]

/-- Being Mittag-Leffler is invariant under isomorphism. -/
private lemma IsML.of_linearEquiv {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (hM : IsML R M) (e : M ≃ₗ[R] N) : IsML R N := by
  intro P _ _ _ f
  obtain ⟨Q, _, _, _, g, hg⟩ := hM P ((e.symm : N →ₗ[R] M) ∘ₗ f)
  refine ⟨Q, ‹_›, ‹_›, ‹_›, g, fun T _ _ => ?_⟩
  rw [← hg T]
  exact (ker_rTensor_comp f (e.symm : N →ₗ[R] M) T
    (rTensor_injective_of_comp_eq_id (e.symm : N →ₗ[R] M) (e : M →ₗ[R] N)
      (by ext y; simp) T)).symm

/-- A countable spanning set pushes forward along a surjection. -/
private lemma exists_countable_span_of_surjective {M : Type*} {N : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (g : M →ₗ[R] N) (hg : Function.Surjective g)
    (h : ∃ t : Set M, t.Countable ∧ span R t = ⊤) : ∃ t : Set N, t.Countable ∧ span R t = ⊤ := by
  obtain ⟨t, ht, hspan⟩ := h
  refine ⟨g '' t, ht.image g, ?_⟩
  rw [Submodule.span_image, hspan, Submodule.map_top, LinearMap.range_eq_top.2 hg]

/-- Both hypotheses are invariant under isomorphism. -/
private lemma IsMLCG.of_linearEquiv {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (hM : IsMLCG R M) (e : M ≃ₗ[R] N) : IsMLCG R N where
  countable_span :=
    exists_countable_span_of_surjective (e : M →ₗ[R] N) e.surjective hM.countable_span
  mittagLeffler := hM.mittagLeffler.of_linearEquiv e

/-- Both hypotheses pass to a direct summand: the summand is countably generated as the image of
the projection onto it, and Mittag-Leffler because the inclusion of a summand is split, hence
universally injective, so that Stacks 059N (1) applies. -/
private lemma IsMLCG.of_isCompl [Small.{v} R] {M : Type v} [AddCommGroup M] [Module R M]
    (hM : IsMLCG R M) {N K : Submodule R M} (h : IsCompl N K) : IsMLCG R ↥N where
  countable_span := exists_countable_span_of_surjective (N.projectionOnto K h)
    (fun y => ⟨(y : M), Submodule.projectionOnto_apply_left h y⟩) hM.countable_span
  mittagLeffler :=
    (Function.Exact.mittagLeffler_M₁_and_mittagLeffler_M₂_of_forall_rTensor_injective
      (LinearMap.exact_subtype_mkQ N) N.mkQ_surjective fun T _ _ =>
        rTensor_injective_of_comp_eq_id N.subtype (N.projectionOnto K h)
          (LinearMap.ext fun z => Submodule.projectionOnto_apply_left h z) T).1 hM.mittagLeffler

end Transfer

/-! ### Lattice-theoretic bookkeeping -/

section Lattice

variable {α : Type*}

/-- A chain that grows by adjoining, at each step, a term disjoint from everything accumulated so
far is the chain of partial sums of an independent family, with the same supremum. -/
private lemma iSupIndep_and_iSup_eq_iSup_of_succ_eq_sup [CompleteLattice α] [IsModularLattice α]
    [IsCompactlyGenerated α] {A N : ℕ → α} (h0 : A 0 = ⊥) (hA : ∀ n, A (n + 1) = A n ⊔ N n)
    (hd : ∀ n, Disjoint (A n) (N n)) : iSupIndep N ∧ (⨆ n, N n) = ⨆ n, A n := by
  have hNle : ∀ n, N n ≤ A (n + 1) := fun n => le_sup_right.trans (hA n).ge
  have hmono : Monotone A := monotone_nat_of_le_succ fun n => le_sup_left.trans (hA n).ge
  have hAle : ∀ n, A n ≤ ⨆ i, N i := by
    intro n
    induction n with
    | zero => exact h0.le.trans bot_le
    | succ n ih => exact (hA n).le.trans (sup_le ih (le_iSup N n))
  refine ⟨Stacks.DirectSum.KaplanskySummand.iSupIndep_of_disjoint_biSup_lt
      fun n => (hd n).symm.mono_right ?_,
    le_antisymm (iSup_le fun n => (hNle n).trans (le_iSup A _)) (iSup_le hAle)⟩
  exact iSup₂_le fun j hj => (hNle j).trans (hmono (Nat.succ_le_of_lt hj))

/-- Refining a complement: if `K` is a complement of `A` and `K` is itself the direct sum of `B`
and `C`, then `C` is a complement of `A ⊔ B`. -/
private lemma isCompl_sup_left_of_disjoint [Lattice α] [BoundedOrder α] [IsModularLattice α]
    {A K B C : α} (h : IsCompl A K) (hd : Disjoint B C) (hs : B ⊔ C = K) : IsCompl (A ⊔ B) C := by
  refine ⟨?_, ?_⟩
  · have hinf : (A ⊔ B) ⊓ K = B := by
      rw [sup_comm, sup_inf_assoc_of_le _ (hs ▸ le_sup_left : B ≤ K), h.inf_eq_bot, sup_bot_eq]
    rw [disjoint_iff, ← inf_eq_right.2 (hs ▸ le_sup_right : C ≤ K), ← inf_assoc, hinf]
    exact hd.eq_bot
  · rw [codisjoint_iff, sup_assoc, hs, h.sup_eq_top]

end Lattice

/-! ### Polynomials in an endomorphism -/

section Aeval

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {Q : Type*} [AddCommGroup Q] [Module R Q]

/-- A linear map intertwining two endomorphisms intertwines their polynomial evaluations:
`g ∘ β = α ∘ g` gives `g ∘ c(β) = c(α) ∘ g` for every polynomial `c`. -/
private lemma comp_aeval_of_comp_eq {α : Module.End R M} {β : Module.End R Q} {g : Q →ₗ[R] M}
    (h : g ∘ₗ β = α ∘ₗ g) (c : R[X]) : g ∘ₗ aeval β c = aeval α c ∘ₗ g := by
  have hpow : ∀ n : ℕ, g ∘ₗ (β ^ n) = (α ^ n) ∘ₗ g := by
    intro n
    induction n with
    | zero => simp [Module.End.one_eq_id]
    | succ n ih =>
      rw [pow_succ, pow_succ, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
        ← LinearMap.comp_assoc, ih, LinearMap.comp_assoc, h, ← LinearMap.comp_assoc]
  induction c using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, LinearMap.comp_add, LinearMap.add_comp]
  | monomial n r =>
    simp [aeval_monomial, Algebra.algebraMap_eq_smul_one, LinearMap.comp_smul,
      LinearMap.smul_comp, hpow]

/-- If a polynomial `c` kills `u ∘ v` then `T · c` kills `v ∘ u`: the map `v` intertwines the two
composites, so `c(v ∘ u) ∘ v = v ∘ c(u ∘ v) = 0`. -/
private lemma mul_aeval_eq_zero (u : M →ₗ[R] Q) (v : Q →ₗ[R] M) {c : R[X]}
    (h : aeval (u ∘ₗ v : Module.End R Q) c = 0) :
    (v ∘ₗ u : Module.End R M) * aeval (v ∘ₗ u : Module.End R M) c = 0 := by
  have hint : v ∘ₗ aeval (u ∘ₗ v : Module.End R Q) c
      = aeval (v ∘ₗ u : Module.End R M) c ∘ₗ v :=
    comp_aeval_of_comp_eq (α := (v ∘ₗ u : Module.End R M)) (β := (u ∘ₗ v : Module.End R Q))
      (g := v) (LinearMap.comp_assoc v u v).symm c
  have hcomm : aeval (v ∘ₗ u : Module.End R M) ((X : R[X]) * c)
      = aeval (v ∘ₗ u : Module.End R M) (c * X) := by rw [mul_comm]
  rw [map_mul, map_mul, aeval_X] at hcomm
  rw [hcomm, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ← hint, h]
  simp

/-- A vector fixed by `α` lies in the image of `g(α)` as soon as `g(1)` is a unit. -/
private lemma mem_range_aeval_of_apply_eq_self {α : Module.End R M} {x : M} (hx : α x = x)
    {g : R[X]} (hg : IsUnit (g.eval 1)) : x ∈ LinearMap.range (aeval α g) := by
  obtain ⟨t, ht⟩ := hg
  have hx1 : α x = (1 : R) • x := by rwa [one_smul]
  refine ⟨((t⁻¹ : Rˣ) : R) • x, ?_⟩
  rw [map_smul, Module.End.aeval_apply_of_mem_apply_eq_smul hx1, ← ht, smul_smul, Units.inv_mul,
    one_smul]

/-- A direct summand of `M` contained in the image of a finite module is finite: it is fixed by the
idempotent, so it is the image of that module under the idempotent. -/
private lemma finite_range_of_isIdempotentElem [Module.Finite R Q] {E : Module.End R M}
    (hE : IsIdempotentElem E) (v : Q →ₗ[R] M) (h : LinearMap.range E ≤ LinearMap.range v) :
    Module.Finite R ↥(LinearMap.range E) := by
  have hrange : LinearMap.range E = LinearMap.range (E ∘ₗ v) := by
    refine le_antisymm (fun y hy => ?_) (LinearMap.range_comp_le_range _ _)
    obtain ⟨z, hz⟩ := h hy
    obtain ⟨w, rfl⟩ := hy
    exact ⟨z, by rw [LinearMap.comp_apply, hz, ← Module.End.mul_apply, hE]⟩
  rw [hrange, LinearMap.range_eq_map]
  exact Module.Finite.iff_fg.2 ((Module.finite_def.1 ‹Module.Finite R Q›).map (E ∘ₗ v))

end Aeval

/-! ### Bezout modulo a monic polynomial -/

section Bezout

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Nakayama's lemma for a finite algebra `A` over a local ring: an ideal which together with
`𝔪 A` is the unit ideal is the unit ideal. -/
private lemma eq_top_of_sup_map_maximalIdeal_eq_top {A : Type w} [CommRing A] [Algebra R A]
    [Module.Finite R A] {J : Ideal A}
    (h : J ⊔ Ideal.map (algebraMap R A) (maximalIdeal R) = ⊤) : J = ⊤ := by
  have hle : (⊤ : Submodule R A) ≤ Submodule.restrictScalars R J ⊔ maximalIdeal R • ⊤ := by
    intro a _
    obtain ⟨j, hj, m, hm, rfl⟩ := Submodule.mem_sup.1 (h ▸ Submodule.mem_top : a ∈ _)
    exact Submodule.mem_sup.2 ⟨j, hj, m, by rwa [Ideal.smul_top_eq_map], rfl⟩
  exact (Ideal.eq_top_iff_one _).2 (Submodule.le_of_le_smul_of_le_jacobson_bot
    (Module.finite_def.1 ‹Module.Finite R A›)
    (le_of_eq (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm) hle Submodule.mem_top)

/-- A polynomial whose reduction to the residue field vanishes has all its coefficients in the
maximal ideal, so its image in `R[T]/(f)` lies in `𝔪 · R[T]/(f)`. -/
private lemma mk_mem_map_maximalIdeal {f w : R[X]} (hw : w.map (residue R) = 0) :
    AdjoinRoot.mk f w ∈ Ideal.map (algebraMap R (AdjoinRoot f)) (maximalIdeal R) := by
  have hc : ∀ n, w.coeff n ∈ maximalIdeal R := fun n => by
    rw [← residue_eq_zero_iff, ← Polynomial.coeff_map, hw, Polynomial.coeff_zero]
  rw [Polynomial.as_sum_support w, map_sum]
  refine Ideal.sum_mem _ fun i _ => ?_
  have hmono : AdjoinRoot.mk f (monomial i (w.coeff i))
      = algebraMap R (AdjoinRoot f) (w.coeff i) * AdjoinRoot.mk f (X ^ i) := by
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]
  rw [hmono]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hc i))

/-- Over a local ring, two polynomials with coprime reductions to the residue field generate the
unit ideal modulo any monic polynomial: `R[T]/(f)` is a finite `R`-module, so Nakayama's lemma
applies to the ideal they generate there. -/
private lemma exists_bezout {f g₁ g₂ : R[X]} (hf : f.Monic)
    (hcop : IsCoprime (g₁.map (residue R)) (g₂.map (residue R))) :
    ∃ c d h : R[X], c * g₁ + d * g₂ = 1 + f * h := by
  have : Module.Finite R (AdjoinRoot f) := hf.finite_adjoinRoot
  obtain ⟨cb, db, hcd⟩ := hcop
  obtain ⟨c, hc⟩ := Polynomial.map_surjective (residue R) Ideal.Quotient.mk_surjective cb
  obtain ⟨d, hd⟩ := Polynomial.map_surjective (residue R) Ideal.Quotient.mk_surjective db
  have hw : (c * g₁ + d * g₂ - 1).map (residue R) = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, hc, hd,
      Polynomial.map_one, hcd, sub_self]
  have hJ : Ideal.span {AdjoinRoot.mk f g₁, AdjoinRoot.mk f g₂} = ⊤ := by
    refine eq_top_of_sup_map_maximalIdeal_eq_top (R := R) ((Ideal.eq_top_iff_one _).2 ?_)
    have h1 : (1 : AdjoinRoot f) = (AdjoinRoot.mk f (c * g₁) + AdjoinRoot.mk f (d * g₂))
        - AdjoinRoot.mk f (c * g₁ + d * g₂ - 1) := by rw [map_sub, map_add, map_one]; ring
    rw [h1]
    refine sub_mem (Submodule.mem_sup_left (add_mem ?_ ?_))
      (Submodule.mem_sup_right (mk_mem_map_maximalIdeal hw)) <;>
    · rw [map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  obtain ⟨c', d', hcd'⟩ := Ideal.mem_span_pair.1 ((Ideal.eq_top_iff_one _).1 hJ)
  obtain ⟨C', hC'⟩ := AdjoinRoot.mk_surjective (g := f) c'
  obtain ⟨D', hD'⟩ := AdjoinRoot.mk_surjective (g := f) d'
  obtain ⟨h, hh⟩ := AdjoinRoot.mk_eq_zero.1 (show AdjoinRoot.mk f (C' * g₁ + D' * g₂ - 1) = 0 by
    rw [map_sub, map_add, map_mul, map_mul, map_one, hC', hD', hcd', sub_self])
  exact ⟨C', D', h, by linear_combination hh⟩

end Bezout

/-! ### The splitting -/

/-- Over a henselian local ring, a monic `p` factors as `p = q₂ q₁` with `q₁(1)` a unit and with
`T q₁` and `q₂` generating the unit ideal modulo `T p`. -/
private lemma exists_factorization_bezout {R : Type u} [CommRing R] [HenselianLocalRing R]
    {p : R[X]} (hp : p.Monic) :
    ∃ q₁ q₂ c d h : R[X], p = q₂ * q₁ ∧ IsUnit (q₁.eval 1) ∧
      c * ((X : R[X]) * q₁) + d * q₂ = 1 + (X : R[X]) * p * h := by
  have : IsLocalRing R := HenselianLocalRing.toIsLocalRing
  have hpbm : (p.map (residue R)).Monic := hp.map _
  set e : ℕ := (p.map (residue R)).rootMultiplicity 1 with he
  set r : (ResidueField R)[X] := (p.map (residue R)) /ₘ (X - C (1 : ResidueField R)) ^ e with hr
  have hfact : (X - C (1 : ResidueField R)) ^ e * r = p.map (residue R) :=
    pow_mul_divByMonic_rootMultiplicity_eq _ 1
  have hr1 : r.eval 1 ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero 1 hpbm.ne_zero
  have hcop : IsCoprime ((X - C (1 : ResidueField R)) ^ e) r :=
    (((Polynomial.irreducible_X_sub_C (1 : ResidueField R)).coprime_iff_not_dvd).2
      fun hdvd => hr1 (Polynomial.dvd_iff_isRoot.1 hdvd)).pow_left
  have hg₀mon : ((X - C (1 : ResidueField R)) ^ e).Monic := (monic_X_sub_C _).pow e
  have hrmon : r.Monic := hg₀mon.of_mul_monic_left (by rwa [hfact])
  obtain ⟨q₂, q₁, _, _, hpq, hq₂, hq₁r⟩ :=
    hensel_factorization_over_R R p hp ((X - C (1 : ResidueField R)) ^ e) r hg₀mon hrmon
      hfact.symm hcop
  have hq₁ : IsUnit (q₁.eval 1) := by
    refine (residue_ne_zero_iff_isUnit _).1 ?_
    have hev : (q₁.map (residue R)).eval 1 = residue R (q₁.eval 1) := by
      rw [Polynomial.eval_map, ← map_one (residue R), Polynomial.eval₂_at_apply]
    rwa [← hev, hq₁r]
  obtain ⟨c, d, h, hcd⟩ := exists_bezout (f := (X : R[X]) * p) (g₁ := (X : R[X]) * q₁) (g₂ := q₂)
    (monic_X.mul hp) (by
      have hXone : IsCoprime (X : (ResidueField R)[X]) (X - C (1 : ResidueField R)) :=
        ⟨1, -1, by simp⟩
      rw [Polynomial.map_mul, Polynomial.map_X, hq₁r, hq₂]
      exact IsCoprime.mul_left hXone.pow_right hcop.symm)
  exact ⟨q₁, q₂, c, d, h, hpq, hq₁, hcd⟩

/-- **The splitting.** Let `R` be a henselian local ring and let `α` be an endomorphism of an
`R`-module `M` with `α · p(α) = 0` for some monic `p ∈ R[T]`. Then `α` splits a direct summand off
`M` through any vector it fixes: there is an idempotent `E` with `x ∈ Im E ⊆ Im α`, so that `Im E`
is a summand of `M` containing `x` with complement `Ker E`.

This is the technical heart of Stacks 05D6, and the only place where the hypotheses on `R` are
used: the factorization of `p` lifted along the henselian hypothesis produces `E` as
`(c · T q₁)(α)`, whose image is that of `α q₁(α)`. -/
private lemma exists_isIdempotentElem_mem_range_le_range {R : Type u} [CommRing R]
    [HenselianLocalRing R] {M : Type v} [AddCommGroup M] [Module R M] (α : Module.End R M)
    {p : R[X]} (hp : p.Monic) (hpα : α * aeval α p = 0) {x : M} (hx : α x = x) :
    ∃ E : Module.End R M, IsIdempotentElem E ∧ x ∈ LinearMap.range E ∧
      LinearMap.range E ≤ LinearMap.range α := by
  obtain ⟨q₁, q₂, c, d, h, hpq, hq₁, hbez⟩ := exists_factorization_bezout hp
  have hXp : aeval α ((X : R[X]) * p) = 0 := by rwa [map_mul, aeval_X]
  set E : Module.End R M := aeval α (c * ((X : R[X]) * q₁)) with hE
  set F : Module.End R M := aeval α (d * q₂) with hF
  set β : Module.End R M := aeval α ((X : R[X]) * q₁) with hβ
  have hEF1 : E + F = 1 := by
    rw [hE, hF, ← map_add, hbez, map_add, map_one, map_mul, hXp, zero_mul, add_zero]
  have hF0 : ∀ a : R[X], aeval α (a * ((X : R[X]) * q₁)) * F = 0 := fun a => by
    rw [hF, ← map_mul, show a * ((X : R[X]) * q₁) * (d * q₂) = a * d * ((X : R[X]) * p) by
      rw [hpq]; ring, map_mul, hXp, mul_zero]
  have hEF0 : E * F = 0 := hF0 c
  have hidem : IsIdempotentElem E := by
    have h1 : E * E + E * F = E := by rw [← mul_add, hEF1, mul_one]
    rwa [hEF0, add_zero] at h1
  have hrange : LinearMap.range E = LinearMap.range β := by
    refine le_antisymm ?_ ?_
    · rw [hE, hβ, mul_comm c ((X : R[X]) * q₁), map_mul, Module.End.mul_eq_comp]
      exact LinearMap.range_comp_le_range _ _
    · have hβF : β * F = 0 := by simpa [hβ] using hF0 1
      have hβE : β = E * β := by
        calc β = β * (E + F) := by rw [hEF1, mul_one]
          _ = β * E := by rw [mul_add, hβF, add_zero]
          _ = E * β := by rw [hβ, hE, ← map_mul, ← map_mul, mul_comm]
      rw [hβE, Module.End.mul_eq_comp]
      exact LinearMap.range_comp_le_range _ _
  refine ⟨E, hidem, hrange ▸ mem_range_aeval_of_apply_eq_self hx (by simpa using hq₁), ?_⟩
  rw [hrange, hβ, map_mul, aeval_X, Module.End.mul_eq_comp]
  exact LinearMap.range_comp_le_range _ _

/-! ### The claim: splitting off a finitely presented summand through a given element -/

/-- The claim of the source's proof of Stacks 05D6: over a henselian local ring, a countably
generated Mittag-Leffler module `M` decomposes, for every `x ∈ M`, as `M = N ⊕ K` with `x ∈ N`, the
summand `N` finitely presented and the summand `K` again countably generated and Mittag-Leffler. -/
private lemma exists_isCompl_finitePresentation (R : Type u) [CommRing R] [HenselianLocalRing R]
    [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M] (hM : IsMLCG R M) (x : M) :
    ∃ N K : Submodule R M, IsCompl N K ∧ x ∈ N ∧ Module.FinitePresentation R ↥N ∧ IsMLCG R ↥K := by
  -- an endomorphism fixing `x` and factoring through a finitely presented module (05D2)
  obtain ⟨α, ⟨Q, _, _, _, u, v, hα⟩, hαf⟩ :=
    Module.exists_end_factorization_finitePresentation_of_countable_span_of_mittagLeffler
      R M hM.countable_span hM.mittagLeffler (LinearMap.toSpanSingleton R M x)
  have hαx : α x = x := by simpa using LinearMap.congr_fun hαf (1 : R)
  -- a monic polynomial killing `u ∘ v` (05BT), whence `α · p(α) = 0`
  obtain ⟨p, hpm, hp⟩ := LinearMap.exists_monic_and_aeval_eq_zero R (u ∘ₗ v : Module.End R Q)
  have hpα : (α : Module.End R M) * aeval (α : Module.End R M) p = 0 := by
    rw [hα]; exact mul_aeval_eq_zero u v hp
  have hαv : LinearMap.range α ≤ LinearMap.range v := by
    rw [hα]; exact LinearMap.range_comp_le_range u v
  obtain ⟨E, hidem, hxE, hEα⟩ := exists_isIdempotentElem_mem_range_le_range α hpm hpα hαx
  have hcompl : IsCompl (LinearMap.range E) (LinearMap.ker E) :=
    LinearMap.IsIdempotentElem.isCompl hidem
  have : Module.Finite R ↥(LinearMap.range E) :=
    finite_range_of_isIdempotentElem hidem v (hEα.trans hαv)
  exact ⟨LinearMap.range E, LinearMap.ker E, hcompl, hxE,
    (Module.mittagLeffler_iff_finitePresentation R _).1 (hM.of_isCompl hcompl).mittagLeffler,
    hM.of_isCompl hcompl.symm⟩

/-- The claim, for a submodule `K₀` of `M` in place of `M`: the decomposition of `K₀` is read as a
pair of disjoint submodules of `M` with supremum `K₀`. -/
private lemma exists_disjoint_sup_eq_finitePresentation (R : Type u) [CommRing R]
    [HenselianLocalRing R] [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M]
    (K₀ : Submodule R M) (hK₀ : IsMLCG R ↥K₀) {y : M} (hy : y ∈ K₀) :
    ∃ N K : Submodule R M, Disjoint N K ∧ N ⊔ K = K₀ ∧ y ∈ N ∧
      Module.FinitePresentation R ↥N ∧ IsMLCG R ↥K := by
  obtain ⟨N, K, hcompl, hyN, hfp, hK⟩ :=
    exists_isCompl_finitePresentation R ↥K₀ hK₀ ⟨y, hy⟩
  have hinj := K₀.injective_subtype
  refine ⟨N.map K₀.subtype, K.map K₀.subtype, ?_, ?_, ⟨⟨y, hy⟩, hyN, rfl⟩, ?_, ?_⟩
  · rw [disjoint_iff, ← Submodule.map_inf K₀.subtype hinj, hcompl.inf_eq_bot, Submodule.map_bot]
  · rw [← Submodule.map_sup, hcompl.sup_eq_top, Submodule.map_top, Submodule.range_subtype]
  · have := hfp
    exact Module.FinitePresentation.of_equiv (Submodule.equivMapOfInjective K₀.subtype hinj N)
  · exact hK.of_linearEquiv (Submodule.equivMapOfInjective K₀.subtype hinj K)

/-- Given `M = A ⊕ K` with `K` countably generated Mittag-Leffler and given `z : M`, there is a
finitely presented `N ≤ K` and a submodule `K'` with `M = (A ⊔ N) ⊕ K'`, `z ∈ A ⊔ N`, and `K'`
again countably generated Mittag-Leffler. -/
private lemma exists_isCompl_sup_finitePresentation (R : Type u) [CommRing R]
    [HenselianLocalRing R] [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M]
    {A K : Submodule R M} (hAK : IsCompl A K) (hK : IsMLCG R ↥K) (z : M) :
    ∃ N K' : Submodule R M, IsCompl (A ⊔ N) K' ∧ N ≤ K ∧ z ∈ A ⊔ N ∧
      Module.FinitePresentation R ↥N ∧ IsMLCG R ↥K' := by
  obtain ⟨a, ha, y, hy, hz⟩ :=
    Submodule.mem_sup.1 (show z ∈ A ⊔ K by simp [hAK.sup_eq_top])
  obtain ⟨N, K', hdisj, hsup, hyN, hfp, hK'⟩ :=
    exists_disjoint_sup_eq_finitePresentation R M K hK hy
  exact ⟨N, K', isCompl_sup_left_of_disjoint hAK hdisj hsup, hsup ▸ le_sup_left,
    hz ▸ Submodule.add_mem_sup ha hyN, hfp, hK'⟩

/-! ### The theorem -/

/-- **Stacks 05D6.** A countably generated Mittag-Leffler module over a henselian local ring is a
direct sum of finitely presented modules. -/
public theorem solution (R : Type u) [CommRing R] [HenselianLocalRing R] [Small.{v} R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (hcg : ∃ s : Set M, s.Countable ∧ Submodule.span R s = ⊤)
    (hML : ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
      (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
        (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (T : Type v) [AddCommGroup T]
          [Module R T], LinearMap.ker (f.rTensor T) = LinearMap.ker (g.rTensor T)) :
    ∃ S : Set (Submodule R M), sSupIndep S ∧ sSup S = ⊤ ∧
      ∀ N ∈ S, Module.FinitePresentation R N := by
  classical
  -- a generating sequence
  obtain ⟨s, hs, hspan⟩ := hcg
  obtain ⟨xs, hxs⟩ := (hs.insert 0).exists_eq_range (Set.insert_nonempty 0 s)
  have hxspan : span R (Set.range xs) = ⊤ := by rw [← hxs, Submodule.span_insert_zero, hspan]
  have hM : IsMLCG R M := ⟨⟨s, hs, hspan⟩, hML⟩
  -- the summand split off at each step, and what is left of `M` after it
  choose! Nf Kf hcp hle hmem hfp hmlcg using
    fun (A K : Submodule R M) (z : M) (hAK : IsCompl A K) (hK : IsMLCG R ↥K) =>
      exists_isCompl_sup_finitePresentation R M hAK hK z
  -- iterate it along the generating sequence
  let st : ℕ → Submodule R M × Submodule R M := fun n =>
    n.rec (⊥, ⊤) fun k p => (p.1 ⊔ Nf p.1 p.2 (xs k), Kf p.1 p.2 (xs k))
  let A : ℕ → Submodule R M := fun n => (st n).1
  let K : ℕ → Submodule R M := fun n => (st n).2
  have hAsucc : ∀ n, A (n + 1) = A n ⊔ Nf (A n) (K n) (xs n) := fun _ => rfl
  have hKsucc : ∀ n, K (n + 1) = Kf (A n) (K n) (xs n) := fun _ => rfl
  have hinv : ∀ n, IsCompl (A n) (K n) ∧ IsMLCG R ↥(K n) := by
    intro n
    induction n with
    | zero =>
      exact ⟨isCompl_bot_top, IsMLCG.of_linearEquiv hM Submodule.topEquiv.symm⟩
    | succ n ih =>
      rw [hAsucc n, hKsucc n]
      exact ⟨hcp _ _ _ ih.1 ih.2, hmlcg _ _ _ ih.1 ih.2⟩
  obtain ⟨hindep, hsup⟩ := iSupIndep_and_iSup_eq_iSup_of_succ_eq_sup (A := A)
    (N := fun n => Nf (A n) (K n) (xs n)) rfl hAsucc
    fun n => (hinv n).1.disjoint.mono_right (hle _ _ _ (hinv n).1 (hinv n).2)
  -- the generators are absorbed, so the partial sums exhaust `M`
  have hAtop : (⨆ n, A n) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hxspan, Submodule.span_le]
    rintro y ⟨n, rfl⟩
    exact le_iSup A (n + 1) ((hAsucc n) ▸ hmem (A n) (K n) (xs n) (hinv n).1 (hinv n).2)
  refine ⟨Set.range fun n => Nf (A n) (K n) (xs n), hindep.sSupIndep_range, ?_, ?_⟩
  · rw [sSup_range, hsup, hAtop]
  · rintro N ⟨n, rfl⟩
    exact hfp _ _ _ (hinv n).1 (hinv n).2

end Stacks.MittagLeffler.OverHenselianRing

/-!
# Countably generated Mittag-Leffler modules over a henselian local ring

Let `R` be a henselian local ring and let `M` be a countably generated Mittag-Leffler `R`-module.
Then `M` is a direct sum of finitely presented `R`-modules (Stacks 05D6).

The source's proof shows the following claim: for every `x ∈ M` there is a direct sum
decomposition `M = N ⊕ K` with `x ∈ N`, the summand `N` finitely presented and `K` again
Mittag-Leffler. Granting the claim, a countable generating set `x₁, x₂, …` of `M` is absorbed one
element at a time into a growing finite direct sum `N₁ ⊕ ⋯ ⊕ Nₙ` of finitely presented summands
with Mittag-Leffler complement, and in the limit `M = ⨁ Nᵢ`. The claim itself is where the
henselian hypothesis enters: by Stacks 05D2 there is an endomorphism `α : M → M` fixing `x` and
factoring through a finitely presented module `P` as `α = i ∘ π`, the induced endomorphism
`a = π ∘ α ∘ i` of `P` satisfies a monic polynomial `p ∈ R[T]` (Stacks 05BT), so `α² p(α) = 0` and
`M` becomes a module over `R[T]/(T²p)`; the annihilator of `x` lies in the maximal ideal, so `1` is
a root of `p` mod `𝔪`, and henselianness factors `T²p = (T²q₁)q₂` with `q₂ ≡ (T - 1)ᵉ` and
`q₁(1)` a unit (Stacks 04GG). Then `N = Im(α²q₁(α))` and `K = Im(q₂(α))` are complementary,
`x ∈ N` since `α²q₁(α)x = q₁(1)x`, both are Mittag-Leffler (Stacks 059P), and the finitely
generated Mittag-Leffler module `N` is finitely presented (Stacks 059R (1)).

## Main results

* `Module.exists_sSupIndep_finitePresentation_of_countable_span_of_mittagLeffler`: a countably
  generated Mittag-Leffler module over a henselian local ring is a direct sum of finitely presented
  modules.

## Implementation notes

Mittag-Leffler is spelled out inline as condition (1) of Stacks 059E — every map `f : P → M` from a
finitely presented module dominates and is dominated by a map `g : P → Q` into a finitely presented
module, domination meaning `Ker(f ⊗ id_T) = Ker(g ⊗ id_T)` for every `R`-module `T` — as in
Stacks 059M, 059N, 059P, 059R, 05CQ and 0AS7, Mathlib having no predicate for it. Test data lives
in the universe `v` of `M`, whence `Small.{v} R`: without it a finitely presented `R`-module need
not be isomorphic to one in `Type v`, the condition as written is not the source's, and the
hypothesis degenerates. This is the hypothesis carried by Stacks 059M, 059R, 05CQ and 0AS7 for the
same reason, and it holds automatically when `R` and `M` share a universe.

Countable generation is written as the existence of a countable spanning set,
`∃ s : Set M, s.Countable ∧ Submodule.span R s = ⊤`, the spelling used for it throughout this
development (Stacks 058U, 058W, 0590).

The direct sum decomposition is stated *internally*, as an independent set `S` of submodules of `M`
with supremum `⊤`, exactly as in Stacks 058W. By `sSupIndep_iff` and
`DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top` this says that the canonical map
`⨁ N : S, N → M` is an isomorphism, so it implies the external form `M ≃ₗ[R] ⨁ i, Pᵢ` with each
`Pᵢ` finitely presented, and it is what the source's proof produces: each summand is the image of
an endomorphism of `M`, hence a submodule of `M`. Stating it internally also keeps the statement
free of an existentially quantified index type and its universe.

The source's proof yields a *countable* such `S`, but the source's statement does not assert this
and neither of its applications (Stacks 059U (5) and Flatness Lemma 05IV) uses it, so it is not
claimed here; it is in any case automatic once the zero submodule is discarded, a countable
spanning set of `M` meeting only countably many members of an independent set.

Faithfulness. (1) No hypothesis is dead, each being consumed where the source's proof consumes it:
`HenselianLocalRing R` produces the factorization `T²p = (T²q₁)q₂` (Stacks 04GG) that splits one
finitely presented summand off, countable generation is what makes the one-element-at-a-time
exhaustion of a generating sequence terminate in `M = ⨁ Nᵢ`, and Mittag-Leffler supplies at each
step both the endomorphism fixing `x` and factoring through a finitely presented module
(Stacks 05D2) and the Mittag-Leffler complement that lets the step repeat (Stacks 059P). Nothing is
assumed that the source does not assume, and nothing it assumes is dropped. Nor is the conclusion
automatic for a countably generated module over a henselian local ring: over the Artinian local —
hence henselian — ring `k[a, b]/(a², ab, b²)` the module `R[t]/(at - b)` is countably generated and
indecomposable, and not finitely presented (a finitely presented module is Mittag-Leffler by
Stacks 059R (1)), hence not a direct sum of finitely presented modules, which is exactly how
Stacks 059U (5) concludes that it is not Mittag-Leffler.
(2) The scalars and the base are the source's throughout: `M` is an `R`-module, the test maps and
tensor products are `R`-linear over `R`, the spanning set spans over `R`, and `S` consists of
`R`-submodules of `M`; nothing is localized or base changed, and no auxiliary algebra intervenes.
(3) The source names no canonical map; what is pinned instead is stronger than bare existence of an
abstract isomorphism, namely the decomposition of `M` itself into an independent family of
submodules with supremum `⊤`. (4) The instantiation is not degenerate: for `R = ℤ_[p]`, henselian
local since complete local, and `M = ⨁ (_ : ℕ), R`, both hypotheses hold — `M` is countably
generated and free, hence Mittag-Leffler by Stacks 059R (2) — while `M` is not itself finitely
generated, and the conclusion holds with `S` the set of coordinate lines.

## References

* [StacksProject 05D6](https://stacks.math.columbia.edu/tag/05D6)
-/



@[expose] public section

/-- **Stacks 05D6.** Let `R` be a henselian local ring and let `M` be an `R`-module which is
countably generated — it admits a countable spanning set — and Mittag-Leffler, the latter in the
intrinsic form 059E (1): every map `f : P → M` from a finitely presented module dominates and is
dominated by a map `g : P → Q` into a finitely presented module, domination meaning
`Ker(f ⊗ id_T) = Ker(g ⊗ id_T)` for every `R`-module `T`. Then `M` is a direct sum of finitely
presented `R`-modules, in the internal form: there is an independent set of finitely presented
submodules of `M` whose supremum is `⊤`. -/
@[stacks 05D6 "Mittag-Leffler is spelled out inline as condition (1) of 059E, as in 059M, 059N,
059P, 059R, 05CQ and 0AS7; countable generation as a countable spanning set, as in 0590; and the
direct sum decomposition internally, as an independent set of submodules of `M` with supremum `⊤`,
as in 058W. Test data in the universe of `M`, whence `Small.{v} R`. See the module docstring."]
public theorem Module.exists_sSupIndep_finitePresentation_of_countable_span_of_mittagLeffler
    (R : Type u) [CommRing R] [HenselianLocalRing R] [Small.{v} R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (hcg : ∃ s : Set M, s.Countable ∧ Submodule.span R s = ⊤)
    (hML : ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
      (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
        (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (T : Type v) [AddCommGroup T]
          [Module R T], LinearMap.ker (f.rTensor T) = LinearMap.ker (g.rTensor T)) :
    ∃ S : Set (Submodule R M), sSupIndep S ∧ sSup S = ⊤ ∧
      ∀ N ∈ S, Module.FinitePresentation R N :=
  Stacks.MittagLeffler.OverHenselianRing.solution R M hcg hML

end
