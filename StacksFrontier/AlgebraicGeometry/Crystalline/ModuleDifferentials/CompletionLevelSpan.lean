module

public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.CompletionLevel
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.DeRhamExterior

/-!
# The differentials of a completion modulo `pᵏ` are spanned by the uncompleted ones

Let `A → B` be a ring map, let an ideal `J` of `B` carry divided powers `δ`, let `p` be nilpotent
modulo `J` and write `B̂` for the `p`-adic completion of `B`.  The universal divided power
differentials `Ω_{B̂/A,γ̂}` of the completion are spanned over `B̂` by the differentials `d x` of
*all* `x : B̂`; this file says that **modulo `pᵏ` the `x` may be taken in the uncompleted `B`**:

`Ω_{B̂/A,γ̂} / pᵏ`  is spanned over `B̂` by the classes of `d (of b)` for `b : B`.

## Why it is true

Two elements of `B̂` congruent modulo `pᵏ` have the same differential modulo `pᵏ`.  Indeed if
`x - y = pᵏ · w` then `d x - d y = d (pᵏ · w) = pᵏ · d w + w · d (pᵏ)`, and `d (pᵏ)` vanishes
because `pᵏ` is the image of a natural number and `d` kills those — this is
`Crystalline.dividedPowerDifferential_natCast`, which follows from additivity and `d 1 = 0`.  So
`d x - d y` lies in `pᵏ · Ω` and the two classes agree.  Every `x : B̂` is congruent modulo `pᵏ`
to some `of b`, because `AdicCompletion.evalₐ` at level `k` is surjective onto `B / pᵏ` and its
kernel is `pᵏ` by `Crystalline.pAdicIdeal_eq_ker_eval`.

## Main results

* `Crystalline.dividedPowerDifferential_natCast` — the universal divided power differential kills
  the image of a natural number.
* `Crystalline.mk_dividedPowerDifferential_eq_of_sub_mem` — elements congruent modulo `pᵏ` have
  the same differential modulo `pᵏ`, for any divided power ring.
* `Crystalline.exists_sub_mem_pAdicIdeal_pow_of` — every element of the completion is congruent
  modulo `pᵏ` to one coming from `B`.
* `Crystalline.span_completedDifferentialsModPow_mk_d_of` — **the spanning statement**: the
  classes of `d (of b)`, for `b` in the uncompleted `B`, span `Ω_{B̂/A,γ̂} / pᵏ` over `B̂`.
* `Crystalline.completedDifferentialsModPow_ext` and
  `...completedDifferentialsModPow_ext_addMonoidHom` — two `B̂`-linear maps, respectively two
  additive maps that are semilinear over a fixed ring map, out of `Ω_{B̂/A,γ̂} / pᵏ` agreeing on
  those classes are equal.

## What is and is not proved

Nothing here mentions `Crystalline.DifferentialsCompletionComparison`, and no tag attribute is
placed.  The purpose of the file is that
`Crystalline.completedDifferentialsLevelEquiv_d` of
`ModuleDifferentials/CompletionLevel.lean` pins the level identification of [Stacks, Tag 07KK]
precisely on the classes named here, so the ext lemmas turn that pinning into a *determination*:
any two `B̂`-linear maps out of `Ω_{B̂/A,γ̂} / pᵏ` agreeing on `d (of b)` for every `b : B`
coincide.  This is what makes the cosimplicial naturality of the level identification derivable
rather than extra data on the comparison.  **[Stacks, Tag 07LF] is not proved here**, and the
naturality itself is not stated here either.

## References

* [Stacks Project, Lemma 60.20.1, Tag 07KK](https://stacks.math.columbia.edu/tag/07KK)
* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
-/

@[expose] public section

universe u v

namespace Crystalline

/-! ### The universal divided power differential kills the integers -/

section NatCast

variable {A : Type u} {R : Type v} [CommRing A] [CommRing R] [Algebra A R]
variable {K : Ideal R} (gamma : DividedPowers K)

/-- The universal divided power differential kills `0`. -/
@[simp]
public theorem dividedPowerDifferential_zero :
    dividedPowerDifferential (A := A) gamma 0 = 0 := by
  have h := dividedPowerDifferential_sub (A := A) gamma 1 1
  rw [sub_self, sub_self] at h
  exact h

/-- **The universal divided power differential kills the image of a natural number.**  It is
additive and kills `1`, so it kills every `n • 1`.  This is what makes `d (pᵏ)` vanish, and hence
what makes congruence modulo `pᵏ` enough to identify differentials modulo `pᵏ`. -/
public theorem dividedPowerDifferential_natCast (n : ℕ) :
    dividedPowerDifferential (A := A) gamma (n : R) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcast : ((n + 1 : ℕ) : R) = (n : R) + 1 := by push_cast; ring
    rw [hcast, dividedPowerDifferential_add, ih, dividedPowerDifferential_one, add_zero]

end NatCast

/-! ### Congruence modulo `pᵏ` identifies differentials modulo `pᵏ` -/

section Congruence

variable {A : Type u} {R : Type v} [CommRing A] [CommRing R] [Algebra A R]
variable {K : Ideal R} (gamma : DividedPowers K) (p k : ℕ)

/-- `pᵏ` is a member of the `k`-th power of the `p`-adic ideal. -/
public theorem pow_mem_pAdicIdeal_pow :
    ((p : R)) ^ k ∈ DividedPowers.pAdicIdeal (A := R) p ^ k := by
  rw [DividedPowers.pAdicIdeal, Ideal.span_singleton_pow]
  exact Ideal.mem_span_singleton_self _

/-- **Elements of a divided power ring congruent modulo `pᵏ` have the same universal divided power
differential modulo `pᵏ`.**  If `x - y = pᵏ · w` then the Leibniz rule gives
`d x - d y = pᵏ · d w + w · d (pᵏ)`, and `d (pᵏ) = 0` by
`Crystalline.dividedPowerDifferential_natCast`. -/
public theorem mk_dividedPowerDifferential_eq_of_sub_mem {x y : R}
    (h : x - y ∈ DividedPowers.pAdicIdeal (A := R) p ^ k) :
    (Submodule.Quotient.mk (dividedPowerDifferential (A := A) gamma x) :
        dividedPowerDifferentials (A := A) gamma ⧸
          (DividedPowers.pAdicIdeal (A := R) p ^ k •
            (⊤ : Submodule R (dividedPowerDifferentials (A := A) gamma)))) =
      Submodule.Quotient.mk (dividedPowerDifferential (A := A) gamma y) := by
  rw [Submodule.Quotient.eq, ← dividedPowerDifferential_sub]
  rw [DividedPowers.pAdicIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  obtain ⟨w, hw⟩ := h
  have hd : dividedPowerDifferential (A := A) gamma (x - y) =
      ((p : R)) ^ k • dividedPowerDifferential (A := A) gamma w := by
    have hcast : ((p : R)) ^ k = ((p ^ k : ℕ) : R) := by push_cast; ring
    rw [hw, dividedPowerDifferential_mul, hcast, dividedPowerDifferential_natCast, smul_zero,
      add_zero]
  rw [hd]
  exact Submodule.smul_mem_smul (pow_mem_pAdicIdeal_pow p k) Submodule.mem_top

end Congruence

/-! ### The spanning statement at a level of the completion -/

section Level

/-- **Every element of the `p`-adic completion is congruent modulo `pᵏ` to one coming from `B`.**
Evaluation at level `k` is onto the quotient `B / pᵏ` and its kernel is the `k`-th power of the
`p`-adic ideal of the completion, by `Crystalline.pAdicIdeal_eq_ker_eval`. -/
public theorem exists_sub_mem_pAdicIdeal_pow_of {B : Type v} [CommRing B] (p k : ℕ)
    (x : AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) :
    ∃ b : B, x - AdicCompletion.of (DividedPowers.pAdicIdeal (A := B) p) B b ∈
      DividedPowers.pAdicIdeal
        (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p ^ k := by
  refine Exists.elim (Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (DividedPowers.pAdicIdeal (A := B) p) k x)) fun b hb ↦ ⟨b, ?_⟩
  rw [pAdicIdeal_eq_ker_eval (B := B) p k, RingHom.mem_ker]
  change (AdicCompletion.evalₐ (DividedPowers.pAdicIdeal (A := B) p) k) _ = 0
  rw [map_sub, AdicCompletion.evalₐ_of, ← hb, sub_self]

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (J : Ideal B) (delta : DividedPowers J) (p : ℕ)
variable (hp : IsNilpotent (Ideal.Quotient.mk J (p : B)))

/-- **The differential of an element of `B̂` is, modulo `pᵏ`, the differential of an element of
`B`.**  This is `Crystalline.mk_dividedPowerDifferential_eq_of_sub_mem` for the completed divided
powers, fed with `Crystalline.exists_sub_mem_pAdicIdeal_pow_of`. -/
public theorem exists_mk_dividedPowerDifferential_eq_of (k : ℕ)
    (x : AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) :
    ∃ b : B,
      (Submodule.Quotient.mk (dividedPowerDifferential (A := A)
          (DividedPowers.completedDividedPowers J delta p hp).1 x) :
        completedDifferentialsModPow (A := A) J delta p hp k) =
      Submodule.Quotient.mk (dividedPowerDifferential (A := A)
        (DividedPowers.completedDividedPowers J delta p hp).1
        (AdicCompletion.of (DividedPowers.pAdicIdeal (A := B) p) B b)) :=
  Exists.elim (exists_sub_mem_pAdicIdeal_pow_of (B := B) p k x) fun b hb ↦
    ⟨b, mk_dividedPowerDifferential_eq_of_sub_mem (A := A)
      (DividedPowers.completedDividedPowers J delta p hp).1 p k hb⟩

/-- **The classes of the differentials of elements of the uncompleted `B` span
`Ω_{B̂/A,γ̂} / pᵏ` over `B̂`.**

The differentials `d x` for `x : B̂` span `Ω_{B̂/A,γ̂}` over `B̂` by
`Crystalline.dividedPowerDifferentials_span`, so their classes span the quotient; and modulo `pᵏ`
each of those classes is the class of `d (of b)` for some `b : B`, by
`Crystalline.exists_mk_dividedPowerDifferential_eq_of`. -/
public theorem span_completedDifferentialsModPow_mk_d_of (k : ℕ) :
    Submodule.span (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B)
        (Set.range fun b : B ↦
          (Submodule.Quotient.mk (dividedPowerDifferential (A := A)
              (DividedPowers.completedDividedPowers J delta p hp).1
              (AdicCompletion.of (DividedPowers.pAdicIdeal (A := B) p) B b)) :
            completedDifferentialsModPow (A := A) J delta p hp k)) = ⊤ := by
  have htop : Submodule.span (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B)
      (Set.range fun x : AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B ↦
        (Submodule.Quotient.mk (dividedPowerDifferential (A := A)
            (DividedPowers.completedDividedPowers J delta p hp).1 x) :
          completedDifferentialsModPow (A := A) J delta p hp k)) = ⊤ := by
    have h := congrArg (Submodule.map (DividedPowers.pAdicIdeal
          (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p ^ k •
        (⊤ : Submodule (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B)
          (dividedPowerDifferentials (A := A)
            (DividedPowers.completedDividedPowers J delta p hp).1))).mkQ)
      (dividedPowerDifferentials_span (A := A)
        (DividedPowers.completedDividedPowers J delta p hp).1)
    simpa only [Submodule.map_span, ← Set.range_comp, Function.comp_def, Submodule.map_top,
      Submodule.range_mkQ, Submodule.mkQ_apply] using h
  refine eq_top_iff.mpr (Eq.subst (motive := fun S ↦ S ≤ _) htop ?_)
  refine Submodule.span_le.mpr (Set.range_subset_iff.mpr fun x ↦ ?_)
  exact Exists.elim (exists_mk_dividedPowerDifferential_eq_of J delta p hp k x) fun b hb ↦
    Eq.subst (motive := fun w ↦ w ∈ _) hb.symm (Submodule.subset_span (Set.mem_range_self b))

/-- **Two `B̂`-linear maps out of `Ω_{B̂/A,γ̂} / pᵏ` agreeing on the differentials of the elements
of the uncompleted `B` are equal.**  This is
`Crystalline.span_completedDifferentialsModPow_mk_d_of` read through `LinearMap.ext_on_range`, and
it is what turns `Crystalline.completedDifferentialsLevelEquiv_d` from a computation into a
determination of the level identification of [Stacks, Tag 07KK]. -/
public theorem completedDifferentialsModPow_ext (k : ℕ) {N : Type*} [AddCommGroup N]
    [Module (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) N]
    {f g : completedDifferentialsModPow (A := A) J delta p hp k →ₗ[AdicCompletion
        (DividedPowers.pAdicIdeal (A := B) p) B] N}
    (h : ∀ b : B, f (Submodule.Quotient.mk (dividedPowerDifferential (A := A)
        (DividedPowers.completedDividedPowers J delta p hp).1
        (AdicCompletion.of (DividedPowers.pAdicIdeal (A := B) p) B b))) =
      g (Submodule.Quotient.mk (dividedPowerDifferential (A := A)
        (DividedPowers.completedDividedPowers J delta p hp).1
        (AdicCompletion.of (DividedPowers.pAdicIdeal (A := B) p) B b)))) :
    f = g :=
  LinearMap.ext_on_range (span_completedDifferentialsModPow_mk_d_of J delta p hp k) h

/-- **Two additive maps out of `Ω_{B̂/A,γ̂} / pᵏ` that are semilinear along a fixed ring map and
agree on the differentials of the elements of the uncompleted `B` are equal.**  This is the form
the cosimplicial direction needs, where source and target are modules over different rings: the
hypothesis `hsmul` on each map is its semilinearity along `sigma`. -/
public theorem completedDifferentialsModPow_ext_addMonoidHom (k : ℕ) {C : Type*} [CommRing C]
    (sigma : AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B →+* C)
    {N : Type*} [AddCommGroup N] [Module C N]
    {f g : completedDifferentialsModPow (A := A) J delta p hp k →+ N}
    (hf : ∀ (r : AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B)
      (w : completedDifferentialsModPow (A := A) J delta p hp k),
      f (r • w) = sigma r • f w)
    (hg : ∀ (r : AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B)
      (w : completedDifferentialsModPow (A := A) J delta p hp k),
      g (r • w) = sigma r • g w)
    (h : ∀ b : B, f (Submodule.Quotient.mk (dividedPowerDifferential (A := A)
        (DividedPowers.completedDividedPowers J delta p hp).1
        (AdicCompletion.of (DividedPowers.pAdicIdeal (A := B) p) B b))) =
      g (Submodule.Quotient.mk (dividedPowerDifferential (A := A)
        (DividedPowers.completedDividedPowers J delta p hp).1
        (AdicCompletion.of (DividedPowers.pAdicIdeal (A := B) p) B b)))) :
    f = g := by
  let : Module (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) N :=
    Module.compHom N sigma
  have hfg := completedDifferentialsModPow_ext J delta p hp k
    (f := { f with map_smul' := hf }) (g := { g with map_smul' := hg }) h
  exact DFunLike.ext _ _ fun w ↦ congrFun (congrArg DFunLike.coe hfg) w

end Level

end Crystalline

end
