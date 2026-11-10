module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CoordinateOperatorsInfinite
public import StacksFrontier.AlgebraicGeometry.Crystalline.TaylorConvergence

/-!
# The Taylor series of [Stacks, Tag 07JH] over a base in which `p` is not nilpotent

`Crystalline.exists_hasTaylorSum` of
`StacksFrontier/AlgebraicGeometry/Crystalline/TaylorConvergence.lean` sums the Taylor series

`∑_K ξ^{[K]} ⊗ θ_K(m)`

of the proof of [Stacks, Proposition 60.17.4, Tag 07JH] in `B ⊗_D M` for a ring `B` in which `p`
is **nilpotent**: the quasi-nilpotence condition (07JE) of [Stacks, Tag 07JE] leaves only finitely
many terms outside `p^N M`, and `p^N = 0` in `B` kills those, so the series is a finite sum.  That
is the situation at an object of `Cris(X/S)`, where nilpotence of `p` is part of the definition of
a divided power thickening in [Stacks, Tag 07HM].

**It is not the situation the proof of [Stacks, Lemma 60.21.4, Tag 07LH] applies the series in.**
There the base is `E = D⟨ξ_i⟩^∧`, a `p`-adically *complete* ring, and `p` is only topologically
nilpotent: no power of it vanishes, every term of the series is nonzero, and the sum is a genuine
infinite one.  The module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/EnvelopeRetract.lean` records that as the second of
the three pieces of theory the direction `G ∘ F ≅ id` of [Stacks, Tag 07L5] asks for: "A Taylor
summation over a `p`-adically complete base in which `p` is not nilpotent."

**This module is that summation.**  The series is summed not in `E ⊗_D M` — where it does not
converge, and where `Crystalline.not_isPrecomplete_finsupp_of_forall_pow_ne_zero` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedTensorFreeFinite.lean` exhibits partial sums
of exactly such a series as a Cauchy family with no limit — but in the `p`-adic completion

`M ⊗̂_{D} E = AdicCompletion (p E) (E ⊗_D M)`,

which is `p`-adically complete because the `p`-adic ideal is principal, hence finitely generated.

## What the summation runs on

Nothing about `p` in `E`, and nothing about `E` beyond its divided powers.  The two inputs are:

* the quasi-nilpotence condition (07JE), in the form `Crystalline.finite_thetaPow_notMem_pPowSmul`
  proves from it: at every level `n` only finitely many composite coordinate operators take `m`
  outside `p^n M`.  That is the hypothesis `hfin` below, and it is the source's own "the sum is
  finite!" read at each level instead of once;
* `Crystalline.taylorTerm_mem_pPowSmul_tensor` — a term whose operator lands in `p^n M` lies in
  the `n`-th step of the `p`-adic filtration of `E ⊗_D M`.  This replaces
  `Crystalline.taylorTerm_eq_zero_of_mem_pPowSmul`, which concludes that the term is `0` and needs
  `p^N = 0` in `E` to do it.  The weakening is the whole difference between the two summations: a
  term that is merely small still contributes to a limit, and only the completion has one.

So the truncations `∑_{K ∈ s} ξ^{[K]} ⊗ θ_K(m)` form a `p`-adic Cauchy family, and the sum is the
element of the completion they converge to.

## Main definitions

Everything is in the namespace `Crystalline`.

* `Crystalline.CompletedBaseChange` — the completed base change `M ⊗̂_D E`, that is
  `AdicCompletion (p E) (E ⊗_D M)`, with `Crystalline.toCompletedBaseChange` the canonical map
  from `E ⊗_D M`.
* `Crystalline.taylorTrunc` — the truncation `∑_{K ∈ s} ξ^{[K]} ⊗ θ_K(m)` of the series to a finite
  set of multi-indices.
* `Crystalline.IsCompletedTaylorSum` — **the working form of the sum**: `t` is represented at every
  level `n` by every truncation large enough that the omitted operators land in `p^n M`.  This is
  a levelwise condition, so it is manifestly unique, and every identity the series satisfies is
  proved at a level.
* `Crystalline.HasCompletedTaylorSum` — **the honest form**: a `HasSum` for the `p`-adic topology
  of the completion, the same shape `Crystalline.HasTaylorSum` has in the nilpotent case.

## Main results

* `Crystalline.taylorTerm_mem_pPowSmul_tensor` — the replacement for the vanishing of a term.
* `Crystalline.taylorTrunc_sub_mem_pPowSmul` — two truncations differ by an element of `p^n`, as
  soon as the larger one only adds terms whose operators land in `p^n M`.
* `Crystalline.exists_isCompletedTaylorSum` — **the series converges over a base in which `p` is
  not nilpotent**, the content of this module.  The sum is assembled from the truncations as an
  `AdicCompletion.mk` of an adic Cauchy sequence.
* `Crystalline.isCompletedTaylorSum_unique` — the sum is unique, because the condition prescribes
  every level of it.
* `Crystalline.hasCompletedTaylorSum_of_isCompletedTaylorSum` — the levelwise condition implies the
  `HasSum`, by `Crystalline.hasSum_adicCompletion_of_eval_eventually_eq` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/CoordinateOperatorsInfinite.lean`.  That criterion
  runs on `AdicCompletion.pow_smul_top_eq_ker_eval`, which needs the ideal finitely generated, and
  `Crystalline.fg_pAdicIdeal` supplies it.
* `Crystalline.exists_hasCompletedTaylorSum` — the two together: the series has a sum in the
  `p`-adic topology of `M ⊗̂_D E`.

## What is and is not proved

**[Stacks, Tag 07JH] is `...SmallSite.crystalPairFunctor_isEquivalence`; no `@[stacks 07JH]`
attribute is placed in this module.**
Nothing here is about crystals in quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)`; the subject is
one series in one module.

**Hypotheses carried.**  One, `hfin`, and it is the source's own: at every level only finitely many
composite coordinate operators take `m` outside `p^n M`.  It is what
`Crystalline.finite_thetaPow_notMem_pPowSmul` proves from the quasi-nilpotence condition (07JE) of
[Stacks, Tag 07JE] together with the convergence of the coordinate expansion, and it is carried
here rather than re-derived because nothing in this module mentions a connection.  Nothing is
assumed about `p` in `E`: in particular `Crystalline.exists_isCompletedTaylorSum` has no
`IsNilpotent (p : E)`, which is exactly what `Crystalline.exists_hasTaylorSum` has and cannot drop.

## References

* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Lemma 60.21.4, Tag 07LH](https://stacks.math.columbia.edu/tag/07LH)
* [Stacks Project, Lemma 60.17.5, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
* [Stacks Project, Tag 07JE](https://stacks.math.columbia.edu/tag/07JE)
* [Stacks Project, Tag 07HM](https://stacks.math.columbia.edu/tag/07HM)
-/

@[expose] public section

open scoped TensorProduct

universe u uI v w

namespace Crystalline

/-! ### Monotonicity of the `p`-adic filtration -/

section Mono

/-- **The `p`-adic filtration of a module decreases.**  The submodule `p^n M` of
`Crystalline.pPowSmul` shrinks as `n` grows, because the powers of the `p`-adic ideal do. -/
theorem pPowSmul_mono (p : ℕ) (R : Type u) [CommRing R] (N : Type w) [AddCommGroup N]
    [Module R N] {a b : ℕ} (hab : a ≤ b) : pPowSmul p R N b ≤ pPowSmul p R N a :=
  Submodule.smul_mono (Ideal.pow_le_pow_right hab) le_rfl

end Mono

/-! ### The completed base change and the truncations of the series -/

section Trunc

variable (p : ℕ) (D : DividedPowerRing.{u}) (E : DividedPowerRing.{u})
  [Algebra (D : Type u) (E : Type u)] (M : Type u) [AddCommGroup M]
  [Module (D : Type u) M] {ι : Type uI} (thetaPow : (ι →₀ ℕ) → (M → M))

/-- **The completed base change `M ⊗̂_D E`**, the `p`-adic completion of `E ⊗_D M` for the `p`-adic
ideal of `E`.  This is where the Taylor series of [Stacks, Tag 07JH] converges when `p` is not
nilpotent in `E`; the ideal is principal, hence finitely generated, so the completion is itself
`p`-adically complete by `AdicCompletion.isAdicComplete`. -/
abbrev CompletedBaseChange : Type u :=
  AdicCompletion (DividedPowers.pAdicIdeal (A := (E : Type u)) p)
    ((E : Type u) ⊗[(D : Type u)] M)

/-- The canonical `E`-linear map `E ⊗_D M → M ⊗̂_D E`. -/
noncomputable abbrev toCompletedBaseChange :
    ((E : Type u) ⊗[(D : Type u)] M) →ₗ[(E : Type u)] CompletedBaseChange p D E M :=
  AdicCompletion.of (DividedPowers.pAdicIdeal (A := (E : Type u)) p)
    ((E : Type u) ⊗[(D : Type u)] M)

/-- **A Taylor term whose coefficient operator lands in `p^n M` lies in the `n`-th step of the
`p`-adic filtration of `E ⊗_D M`.**

This is the replacement for `Crystalline.taylorTerm_eq_zero_of_mem_pPowSmul`, which concludes that
the term is `0` and spends `p^N = 0` in `E` to do it.  Here nothing is assumed about `p` in `E`:
the divisibility is moved across the tensor product exactly as there, but it is kept as
divisibility instead of being turned into vanishing.  That is the whole difference between a
Taylor series which is a finite sum and one which converges. -/
theorem taylorTerm_mem_pPowSmul_tensor {n : ℕ} (xi : ι → (E : Type u)) {K : ι →₀ ℕ} {m : M}
    (hK : thetaPow K m ∈ pPowSmul p (D : Type u) M n) :
    taylorMonomial E xi K ⊗ₜ[(D : Type u)] thetaPow K m ∈
      pPowSmul p (E : Type u) ((E : Type u) ⊗[(D : Type u)] M) n := by
  obtain ⟨y, hy⟩ := (mem_pPowSmul_iff p (D : Type u) M).mp hK
  refine (mem_pPowSmul_iff p (E : Type u) ((E : Type u) ⊗[(D : Type u)] M)).mpr
    ⟨taylorMonomial E xi K ⊗ₜ[(D : Type u)] y, ?_⟩
  have hsm : ((p : (E : Type u)) ^ n) • taylorMonomial E xi K =
      ((p : (D : Type u)) ^ n) • taylorMonomial E xi K := by
    rw [Algebra.smul_def, map_pow, map_natCast, Algebra.smul_def, map_pow, map_natCast]
  rw [TensorProduct.smul_tmul', hsm, TensorProduct.smul_tmul, hy]

/-- **The truncation of the Taylor series of [Stacks, Tag 07JH] to a finite set of
multi-indices**, `∑_{K ∈ s} ξ^{[K]} ⊗ θ_K(m)` in the uncompleted `E ⊗_D M`.  In the nilpotent case
one such truncation *is* the sum; here they are the partial sums of a convergent series, and
`Crystalline.taylorTrunc_sub_mem_pPowSmul` is the statement that they form a Cauchy family. -/
noncomputable def taylorTrunc (xi : ι → (E : Type u)) (m : M) (s : Finset (ι →₀ ℕ)) :
    (E : Type u) ⊗[(D : Type u)] M :=
  ∑ K ∈ s, taylorMonomial E xi K ⊗ₜ[(D : Type u)] thetaPow K m

/-- The truncation of the Taylor series to the empty set of multi-indices is zero. -/
@[simp] theorem taylorTrunc_empty (xi : ι → (E : Type u)) (m : M) :
    taylorTrunc D E M thetaPow xi m ∅ = 0 := by
  rw [taylorTrunc, Finset.sum_empty]

/-- **Enlarging a truncation by terms whose operators land in `p^n M` does not move it modulo
`p^n`.**  This is the Cauchy property of the partial sums of the Taylor series, and it is
`Crystalline.taylorTerm_mem_pPowSmul_tensor` summed over the added multi-indices. -/
theorem taylorTrunc_sub_mem_pPowSmul {n : ℕ} (xi : ι → (E : Type u)) (m : M)
    {s s' : Finset (ι →₀ ℕ)} (hsub : s ⊆ s')
    (hs : ∀ K ∈ s', K ∉ s → thetaPow K m ∈ pPowSmul p (D : Type u) M n) :
    taylorTrunc D E M thetaPow xi m s' - taylorTrunc D E M thetaPow xi m s ∈
      pPowSmul p (E : Type u) ((E : Type u) ⊗[(D : Type u)] M) n := by
  classical
  rw [taylorTrunc, taylorTrunc, ← Finset.sum_sdiff hsub, add_sub_cancel_right]
  refine Submodule.sum_mem _ fun K hK ↦ ?_
  obtain ⟨hKs', hKs⟩ := Finset.mem_sdiff.mp hK
  exact taylorTerm_mem_pPowSmul_tensor p D E M thetaPow xi (hs K hKs' hKs)

/-- **Two truncations large enough for level `n` agree at level `n`.** -/
theorem mkQ_taylorTrunc_eq {n : ℕ} (xi : ι → (E : Type u)) (m : M) (s s' : Finset (ι →₀ ℕ))
    (hs : ∀ K ∉ s, thetaPow K m ∈ pPowSmul p (D : Type u) M n)
    (hs' : ∀ K ∉ s', thetaPow K m ∈ pPowSmul p (D : Type u) M n) :
    Submodule.mkQ (pPowSmul p (E : Type u) ((E : Type u) ⊗[(D : Type u)] M) n)
        (taylorTrunc D E M thetaPow xi m s) =
      Submodule.mkQ (pPowSmul p (E : Type u) ((E : Type u) ⊗[(D : Type u)] M) n)
        (taylorTrunc D E M thetaPow xi m s') := by
  classical
  have hdiff : ∀ t : Finset (ι →₀ ℕ), t ⊆ s ∪ s' →
      (∀ K ∉ t, thetaPow K m ∈ pPowSmul p (D : Type u) M n) →
      Submodule.mkQ (pPowSmul p (E : Type u) ((E : Type u) ⊗[(D : Type u)] M) n)
          (taylorTrunc D E M thetaPow xi m (s ∪ s')) =
        Submodule.mkQ (pPowSmul p (E : Type u) ((E : Type u) ⊗[(D : Type u)] M) n)
          (taylorTrunc D E M thetaPow xi m t) := by
    intro t htsub ht
    rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact taylorTrunc_sub_mem_pPowSmul p D E M thetaPow xi m htsub fun K _ hKt ↦ ht K hKt
  exact (hdiff s Finset.subset_union_left hs).symm.trans
    (hdiff s' Finset.subset_union_right hs')

end Trunc

/-! ### The sum of the series -/

section Sum

variable (p : ℕ) (D : DividedPowerRing.{u}) (E : DividedPowerRing.{u})
  [Algebra (D : Type u) (E : Type u)] (M : Type u) [AddCommGroup M]
  [Module (D : Type u) M] {ι : Type uI} (thetaPow : (ι →₀ ℕ) → (M → M))

/-- **The Taylor series of [Stacks, Tag 07JH] has sum `t`, levelwise.**  At every level `n` of the
`p`-adic filtration, `t` is represented by every truncation of the series large enough that the
omitted terms have their operators in `p^n M`.

This is the form every statement about the series is proved in: all the identities the series
satisfies — semilinearity, the cocycle, horizontality — are identities between *finite* sums
modulo `p^n`, so a levelwise condition is what they discharge.  It is also manifestly unique, by
`Crystalline.isCompletedTaylorSum_unique`, since it prescribes every level; the topological form
`Crystalline.HasCompletedTaylorSum` follows from it by
`Crystalline.hasCompletedTaylorSum_of_isCompletedTaylorSum`. -/
def IsCompletedTaylorSum (xi : ι → (E : Type u)) (m : M) (t : CompletedBaseChange p D E M) :
    Prop :=
  ∀ (n : ℕ) (s : Finset (ι →₀ ℕ)), (∀ K ∉ s, thetaPow K m ∈ pPowSmul p (D : Type u) M n) →
    AdicCompletion.eval (DividedPowers.pAdicIdeal (A := (E : Type u)) p)
        ((E : Type u) ⊗[(D : Type u)] M) n t =
      Submodule.mkQ (pPowSmul p (E : Type u) ((E : Type u) ⊗[(D : Type u)] M) n)
        (taylorTrunc D E M thetaPow xi m s)

/-- **The Taylor series of [Stacks, Tag 07JH] converges to `t` in the `p`-adic topology of
`M ⊗̂_D E`.**  This is `Crystalline.HasTaylorSum` with the uncompleted base change replaced by its
completion: the same series of the same terms, summed where it has a limit. -/
def HasCompletedTaylorSum (xi : ι → (E : Type u)) (m : M) (t : CompletedBaseChange p D E M) :
    Prop :=
  letI := Ideal.adicModuleTopology (DividedPowers.pAdicIdeal (A := (E : Type u)) p)
    (CompletedBaseChange p D E M)
  HasSum (fun K : ι →₀ ℕ ↦ toCompletedBaseChange p D E M
    (taylorMonomial E xi K ⊗ₜ[(D : Type u)] thetaPow K m)) t

/-- Outside the finite set of exceptions, the property holds. -/
private theorem prop_of_notMem_toFinset {α : Type*} {P : α → Prop} (h : {a | ¬ P a}.Finite) :
    ∀ a ∉ h.toFinset, P a :=
  fun _ ha ↦ not_not.mp fun hc ↦ ha (h.mem_toFinset.mpr hc)

/-- **The levelwise sum is unique.**  Two elements of an adic completion agreeing at every level
are equal, and the condition prescribes every level. -/
theorem isCompletedTaylorSum_unique (xi : ι → (E : Type u)) (m : M)
    (hfin : ∀ n : ℕ, {K : ι →₀ ℕ | thetaPow K m ∉ pPowSmul p (D : Type u) M n}.Finite)
    {t t' : CompletedBaseChange p D E M} (ht : IsCompletedTaylorSum p D E M thetaPow xi m t)
    (ht' : IsCompletedTaylorSum p D E M thetaPow xi m t') : t = t' := by
  classical
  refine AdicCompletion.ext fun n ↦ ?_
  have hs := prop_of_notMem_toFinset (hfin n)
  simpa only [AdicCompletion.eval_apply] using (ht n _ hs).trans (ht' n _ hs).symm

/-- **The Taylor series of [Stacks, Tag 07JH] converges over a base in which `p` is not
nilpotent.**

This is the summation the module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/EnvelopeRetract.lean` names as the second piece of
theory the direction `G ∘ F ≅ id` of [Stacks, Lemma 60.17.5, Tag 07L5] asks for, and which
`Crystalline.exists_hasTaylorSum` does not supply: that theorem gets its convergence from
`IsNilpotent (p : B)`, which kills all but finitely many terms, and over `E = D⟨ξ_i⟩^∧` no power
of `p` vanishes.

The only hypothesis is `hfin`, the source's own "the sum is finite!" read at each level: at level
`n` only finitely many composite coordinate operators take `m` outside `p^n M`.  The truncations
over those finite sets form a `p`-adic Cauchy sequence, by
`Crystalline.taylorTrunc_sub_mem_pPowSmul`, and the sum is the element of the completion they
define. -/
theorem exists_isCompletedTaylorSum (xi : ι → (E : Type u)) (m : M)
    (hfin : ∀ n : ℕ, {K : ι →₀ ℕ | thetaPow K m ∉ pPowSmul p (D : Type u) M n}.Finite) :
    ∃ t : CompletedBaseChange p D E M, IsCompletedTaylorSum p D E M thetaPow xi m t := by
  classical
  have hs := fun n ↦ prop_of_notMem_toFinset (hfin n)
  have hmono : ∀ {a b : ℕ}, a ≤ b → (hfin a).toFinset ⊆ (hfin b).toFinset := by
    intro a b hab K hK
    rw [Set.Finite.mem_toFinset] at hK ⊢
    exact fun hc ↦ hK (pPowSmul_mono p (D : Type u) M hab hc)
  have hcauchy : ∀ n : ℕ,
      taylorTrunc D E M thetaPow xi m (hfin n).toFinset ≡
        taylorTrunc D E M thetaPow xi m (hfin (n + 1)).toFinset
        [SMOD (DividedPowers.pAdicIdeal (A := (E : Type u)) p ^ n •
          (⊤ : Submodule (E : Type u) ((E : Type u) ⊗[(D : Type u)] M)))] := by
    intro n
    rw [SModEq.sub_mem, ← neg_sub, neg_mem_iff]
    exact taylorTrunc_sub_mem_pPowSmul p D E M thetaPow xi m (hmono (Nat.le_succ n))
      fun K _ hK ↦ hs n K hK
  refine ⟨AdicCompletion.mk (DividedPowers.pAdicIdeal (A := (E : Type u)) p)
      ((E : Type u) ⊗[(D : Type u)] M)
      (AdicCompletion.AdicCauchySequence.mk (DividedPowers.pAdicIdeal (A := (E : Type u)) p)
        ((E : Type u) ⊗[(D : Type u)] M)
        (fun n ↦ taylorTrunc D E M thetaPow xi m (hfin n).toFinset) hcauchy),
    fun n s hsn ↦ ?_⟩
  rw [AdicCompletion.eval_apply, AdicCompletion.mk_apply_coe]
  exact mkQ_taylorTrunc_eq p D E M thetaPow xi m _ s (hs n) hsn

/-- **The levelwise sum of the series is its sum in the `p`-adic topology of the completion.**

The criterion is `Crystalline.hasSum_adicCompletion_of_eval_eventually_eq` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CoordinateOperatorsInfinite.lean`: at every level all
partial sums over large enough finite sets have the same image as the proposed sum.  That is what
`Crystalline.IsCompletedTaylorSum` says, once the image of a partial sum is identified with the
class of the truncation.  The finite generation of the `p`-adic ideal, which the criterion needs
through `AdicCompletion.pow_smul_top_eq_ker_eval`, is `Crystalline.fg_pAdicIdeal`. -/
theorem hasCompletedTaylorSum_of_isCompletedTaylorSum (xi : ι → (E : Type u)) (m : M)
    (hfin : ∀ n : ℕ, {K : ι →₀ ℕ | thetaPow K m ∉ pPowSmul p (D : Type u) M n}.Finite)
    {t : CompletedBaseChange p D E M} (ht : IsCompletedTaylorSum p D E M thetaPow xi m t) :
    HasCompletedTaylorSum p D E M thetaPow xi m t := by
  classical
  refine hasSum_adicCompletion_of_eval_eventually_eq
    (DividedPowers.pAdicIdeal (A := (E : Type u)) p) (fg_pAdicIdeal p (E : Type u)) _ _ fun n ↦ ?_
  refine ⟨(hfin n).toFinset, fun s hsub ↦ ?_⟩
  rw [ht n s fun K hK ↦ prop_of_notMem_toFinset (hfin n) K (hK <| hsub ·), map_sum, taylorTrunc,
    map_sum]
  exact Finset.sum_congr rfl fun K _ ↦ AdicCompletion.eval_of _ _ n _

/-- **The Taylor series of [Stacks, Tag 07JH] has a sum in the `p`-adic topology of `M ⊗̂_D E`**,
with no nilpotence of `p` in `E`.  This is `Crystalline.exists_isCompletedTaylorSum` read through
`Crystalline.hasCompletedTaylorSum_of_isCompletedTaylorSum`, and it is the statement
`Crystalline.exists_hasTaylorSum` makes in the nilpotent case. -/
theorem exists_hasCompletedTaylorSum (xi : ι → (E : Type u)) (m : M)
    (hfin : ∀ n : ℕ, {K : ι →₀ ℕ | thetaPow K m ∉ pPowSmul p (D : Type u) M n}.Finite) :
    ∃ t : CompletedBaseChange p D E M, HasCompletedTaylorSum p D E M thetaPow xi m t :=
  (exists_isCompletedTaylorSum p D E M thetaPow xi m hfin).imp fun _ ↦
    hasCompletedTaylorSum_of_isCompletedTaylorSum p D E M thetaPow xi m hfin

end Sum

end Crystalline

end
