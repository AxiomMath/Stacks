module

public import StacksFrontier.RingTheory.AdicCompletion.AdditiveFunctoriality

/-!
# The levels of a `p`-adically complete tower are its quotients by `p^{N+e}`

Let `M` be a module over a commutative ring `R` presented as the limit of a tower of modules
`M_0 ← M_1 ← M_2 ← ⋯` through reduction maps `ρ_e : M → M_e`, in the situation of
[Stacks, Lemma 60.17.3, Tag 07JG]:

* the level `e` is annihilated by `p^{N+e}` for a uniform shift `N`;
* the one-step restriction `M_{e+1} → M_e` is surjective with kernel `p^{N+e} M_{e+1}` — this is
  the **crystal property** of [Stacks, Proposition 60.21.3, Tag 07LG], which
  [Stacks, Lemma 60.19.3, Tag 07LF] does not have;
* `M` is `p`-adically precomplete and separated for the tower.

Then the reduction `ρ_e` identifies `M_e` with `M / p^{N+e} M`.

**This is the statement the library did not have and that every base change over a level needs.**
`p`-adic completeness of `M` is item (07JB) and is already proved — by
`Crystalline.isPAdicallyComplete_invLimit_of_shift` algebraically and by
`...SmallSite.isPAdicallyComplete_wholeSpaceLevelScalars_sections` at the site — but completeness
says only that `M` is the limit of *its own* quotients `M / p^k M`, and says nothing about the
tower the limit was taken over.  Identifying the two is what turns a statement about the levels,
such as the base change of the sections of a crystal over a single object of `Cris(X/S)`, into a
statement about `M`.

## Why the naive argument fails and what replaces it

The kernel `ker(ρ_e)` is visibly the limit of the submodules `p^{N+e} M_{e'}`, and the tempting
move is to lift a compatible family of `p^{N+e}`-th roots one level at a time.  That fails: a
root `w ∈ M_{e'+1}` of `x_{e'+1}` restricts to a root of `x_{e'}`, but not to the chosen one, and
correcting it asks for a `p^{N+e}`-torsion element of `M_{e'+1}` lifting a `p^{N+e}`-torsion
element of `M_{e'}`, which the hypotheses do not give.

What works instead is a **successive approximation** whose increments are forced to shrink.  The
point is the arithmetic of the shift: the kernel of the one-step restriction at level `e + j` is
`p^{N+e+j} M_{e+j+1}`, and `p^{N+e+j} = p^{N+e} · p^j`, so a root found at depth `j` may be taken
in `p^j M`.  The resulting sequence is `p`-adically Cauchy, precompleteness produces its limit,
and separatedness identifies the limit's `p^{N+e}`-th multiple with `x`.  Precompleteness of `M`
is therefore used, and it is used for exactly this.

## Main results

Everything is in the namespace `Crystalline.PAdicCompletion`.

* `Crystalline.PAdicCompletion.exists_nsmul_of_towerLevel_eq_zero` — **the kernel of `ρ_e` is
  `p^{N+e} M`**, the half that is not formal.
* `Crystalline.PAdicCompletion.mem_pow_smul_top_iff_towerLevel_eq_zero` — the same as an
  identification of the level of the `p`-adic filtration with the kernel of `ρ_e`.
* `Crystalline.PAdicCompletion.towerLevelEquiv` — **`M / p^{N+e} M ≅ M_e`**, as an `R`-linear
  equivalence, and `Crystalline.PAdicCompletion.towerLevelEquiv_mk` its formula.
* `Crystalline.PAdicCompletion.towerLevelEquiv_transitionMap` — the identifications commute with
  the transition maps of the `p`-adic tower of `M`, which is what makes them comparable as
  inverse systems.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07JB](https://stacks.math.columbia.edu/tag/07JB)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.19.3, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
-/

@[expose] public section

open DividedPowers

universe u w w'

namespace Crystalline

namespace PAdicCompletion

section Tower

variable (p : ℕ) {R : Type u} [CommRing R] {M : Type w} [AddCommGroup M] [Module R M]
  {P : ℕ → Type w'} [∀ e, AddCommGroup (P e)] [∀ e, Module R (P e)]
  (rho : (e : ℕ) → M →ₗ[R] P e) (N : ℕ)

/-- Iterated multiples by powers of `p` add their exponents. -/
private theorem pow_nsmul_pow_nsmul {G : Type*} [AddCommMonoid G] (p a b : ℕ) (w : G) :
    (p ^ a : ℕ) • (p ^ b : ℕ) • w = (p ^ (a + b) : ℕ) • w := by
  rw [smul_smul, ← pow_add]

/-- **The kernel of the reduction to the level `e` is `p^{N+e} M`.**

The hypotheses are the ones of [Stacks, Lemma 60.17.3, Tag 07JG]: `hmono` says that a section
dying at a level dies at every lower level, `hstep` is the crystal property — the one-step
restriction is surjective with kernel `p^{N+e}` times the sections of the higher level, read
through `ρ` — `hann` is the annihilation of the level by `p^{N+e}`, and `hsep` is separatedness
of `M` for the tower.  Precompleteness is the Cauchy hypothesis of the approximation.

See the module documentation for why the levelwise lifting argument does not work and what
replaces it. -/
public theorem exists_nsmul_of_towerLevel_eq_zero
    (hmono : ∀ {a b : ℕ}, a ≤ b → ∀ x : M, rho b x = 0 → rho a x = 0)
    (hstep : ∀ (e : ℕ) (x : M), rho e x = 0 →
      ∃ u : M, rho (e + 1) x = (p ^ (N + e) : ℕ) • rho (e + 1) u)
    (hann : ∀ (e : ℕ) (z : P e), (p ^ (N + e) : ℕ) • z = 0)
    (hsep : ∀ x : M, (∀ e : ℕ, rho e x = 0) → x = 0)
    [IsPrecomplete (pAdicIdeal (A := R) p) M]
    (e : ℕ) (x : M) (hx : rho e x = 0) :
    ∃ y : M, x = (p ^ (N + e) : ℕ) • y := by
  classical
  -- An additive map kills every multiple of `p^{N+a}` landing in the level `a`.
  have hkill : ∀ (a j : ℕ) (w : M), N + a ≤ j → rho a ((p ^ j : ℕ) • w) = 0 := by
    intro a j w hj
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hj
    rw [map_nsmul, ht, ← pow_nsmul_pow_nsmul]
    exact hann a _
  -- One step of the approximation: an increment in `p^j M` improves the depth by one.
  have hnext : ∀ (j : ℕ) (y : M),
      rho (e + j) (x - (p ^ (N + e) : ℕ) • y) = 0 →
      ∃ u : M, rho (e + j + 1)
        (x - (p ^ (N + e) : ℕ) • (y + (p ^ j : ℕ) • u)) = 0 := by
    intro j y hy
    obtain ⟨u, hu⟩ := hstep (e + j) (x - (p ^ (N + e) : ℕ) • y) hy
    refine ⟨u, ?_⟩
    have hrw : x - (p ^ (N + e) : ℕ) • (y + (p ^ j : ℕ) • u) =
        (x - (p ^ (N + e) : ℕ) • y) - (p ^ (N + (e + j)) : ℕ) • u := by
      rw [smul_add, pow_nsmul_pow_nsmul, add_assoc, sub_add_eq_sub_sub]
    rw [hrw, map_sub, hu, map_nsmul, sub_self]
  -- The approximating sequence.
  set c : ℕ := p ^ (N + e) with hc
  set g : ℕ → M → M := fun j y =>
    if h : rho (e + j) (x - c • y) = 0 then (hnext j y h).choose else 0 with hgdef
  have hg : ∀ (j : ℕ) (y : M) (h : rho (e + j) (x - c • y) = 0),
      rho (e + j + 1) (x - c • (y + (p ^ j : ℕ) • g j y)) = 0 := by
    intro j y h
    rw [hgdef]
    simp only [dif_pos h]
    exact (hnext j y h).choose_spec
  set Y : ℕ → M := fun j => Nat.rec (0 : M) (fun j yj => yj + (p ^ j : ℕ) • g j yj) j with hYdef
  have hYsucc : ∀ j : ℕ, Y (j + 1) = Y j + (p ^ j : ℕ) • g j (Y j) := fun _ => rfl
  have hYinv : ∀ j : ℕ, rho (e + j) (x - c • Y j) = 0 := by
    intro j
    induction j with
    | zero =>
        have h0 : Y 0 = 0 := rfl
        rw [h0, smul_zero, sub_zero]
        exact hx
    | succ j ih =>
        show rho (e + j + 1) (x - c • Y (j + 1)) = 0
        rw [hYsucc j]
        exact hg j (Y j) ih
  -- The increments shrink, so the sequence is `p`-adically Cauchy.
  have hdiff : ∀ j k : ℕ, ∃ w : M, Y (j + k) - Y j = (p ^ j : ℕ) • w := by
    intro j k
    induction k with
    | zero => exact ⟨0, by rw [Nat.add_zero, sub_self, smul_zero]⟩
    | succ k ih =>
        obtain ⟨w, hw⟩ := ih
        refine ⟨w + (p ^ k : ℕ) • g (j + k) (Y (j + k)), ?_⟩
        have hstep' : Y (j + (k + 1)) = Y (j + k) + (p ^ (j + k) : ℕ) • g (j + k) (Y (j + k)) :=
          hYsucc (j + k)
        rw [hstep', add_sub_right_comm, hw, smul_add, pow_nsmul_pow_nsmul]
  have hcauchy : ∀ {m n : ℕ}, m ≤ n →
      Y m ≡ Y n [SMOD (pAdicIdeal (A := R) p ^ m • (⊤ : Submodule R M))] := by
    intro m n hmn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [SModEq.sub_mem]
    obtain ⟨w, hw⟩ := hdiff m k
    refine (mem_pow_smul_top_iff p R m _).mpr ⟨-w, ?_⟩
    rw [smul_neg, ← hw, neg_sub]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := pAdicIdeal (A := R) p) Y hcauchy
  refine ⟨L, sub_eq_zero.mp (hsep (x - c • L) fun a => ?_)⟩
  obtain ⟨w, hw⟩ := (mem_pow_smul_top_iff p R (N + a + a) _).mp
    (SModEq.sub_mem.mp (hL (N + a + a)))
  have hsplit : x - c • L =
      (x - c • Y (N + a + a)) + c • (Y (N + a + a) - L) := by
    rw [smul_sub]
    abel
  have h1 : rho a (x - c • Y (N + a + a)) = 0 :=
    hmono (by omega) _ (hYinv (N + a + a))
  have h2 : rho a (c • (Y (N + a + a) - L)) = 0 := by
    rw [hw, hc, pow_nsmul_pow_nsmul]
    exact hkill a (N + e + (N + a + a)) w (by omega)
  rw [hsplit, map_add, h1, h2, add_zero]

/-- **The level `N + e` of the `p`-adic filtration of `M` is the kernel of the reduction to the
level `e` of the tower.**  One inclusion is the annihilation `hann`; the other is
`Crystalline.PAdicCompletion.exists_nsmul_of_towerLevel_eq_zero`. -/
public theorem mem_pow_smul_top_iff_towerLevel_eq_zero
    (hmono : ∀ {a b : ℕ}, a ≤ b → ∀ x : M, rho b x = 0 → rho a x = 0)
    (hstep : ∀ (e : ℕ) (x : M), rho e x = 0 →
      ∃ u : M, rho (e + 1) x = (p ^ (N + e) : ℕ) • rho (e + 1) u)
    (hann : ∀ (e : ℕ) (z : P e), (p ^ (N + e) : ℕ) • z = 0)
    (hsep : ∀ x : M, (∀ e : ℕ, rho e x = 0) → x = 0)
    [IsPrecomplete (pAdicIdeal (A := R) p) M]
    (e : ℕ) (x : M) :
    x ∈ (pAdicIdeal (A := R) p ^ (N + e) • (⊤ : Submodule R M)) ↔ rho e x = 0 := by
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨y, rfl⟩ := (mem_pow_smul_top_iff p R (N + e) x).mp hx
    rw [map_nsmul, hann e (rho e y)]
  · exact (mem_pow_smul_top_iff p R (N + e) x).mpr
      (exists_nsmul_of_towerLevel_eq_zero p rho N hmono hstep hann hsep e x hx)

/-- **The level `e` of the tower is `M / p^{N+e} M`**, as an `R`-linear equivalence: the
reduction `ρ_e` is surjective and its kernel is the level `N + e` of the `p`-adic filtration, by
`Crystalline.PAdicCompletion.mem_pow_smul_top_iff_towerLevel_eq_zero`. -/
public noncomputable def towerLevelEquiv
    (hmono : ∀ {a b : ℕ}, a ≤ b → ∀ x : M, rho b x = 0 → rho a x = 0)
    (hstep : ∀ (e : ℕ) (x : M), rho e x = 0 →
      ∃ u : M, rho (e + 1) x = (p ^ (N + e) : ℕ) • rho (e + 1) u)
    (hann : ∀ (e : ℕ) (z : P e), (p ^ (N + e) : ℕ) • z = 0)
    (hsep : ∀ x : M, (∀ e : ℕ, rho e x = 0) → x = 0)
    (hsurj : ∀ e : ℕ, Function.Surjective (rho e))
    [IsPrecomplete (pAdicIdeal (A := R) p) M] (e : ℕ) :
    (M ⧸ (pAdicIdeal (A := R) p ^ (N + e) • (⊤ : Submodule R M))) ≃ₗ[R] P e :=
  (Submodule.quotEquivOfEq _ (LinearMap.ker (rho e))
      (Submodule.ext fun z =>
        mem_pow_smul_top_iff_towerLevel_eq_zero p rho N hmono hstep hann hsep e z)).trans
    ((rho e).quotKerEquivOfSurjective (hsurj e))

/-- The equivalence `towerLevelEquiv` sends the class of `x` in `M / p^{N+e} M` to `ρ_e(x)`. -/
@[simp] public theorem towerLevelEquiv_mk
    (hmono : ∀ {a b : ℕ}, a ≤ b → ∀ x : M, rho b x = 0 → rho a x = 0)
    (hstep : ∀ (e : ℕ) (x : M), rho e x = 0 →
      ∃ u : M, rho (e + 1) x = (p ^ (N + e) : ℕ) • rho (e + 1) u)
    (hann : ∀ (e : ℕ) (z : P e), (p ^ (N + e) : ℕ) • z = 0)
    (hsep : ∀ x : M, (∀ e : ℕ, rho e x = 0) → x = 0)
    (hsurj : ∀ e : ℕ, Function.Surjective (rho e))
    [IsPrecomplete (pAdicIdeal (A := R) p) M] (e : ℕ) (x : M) :
    towerLevelEquiv p rho N hmono hstep hann hsep hsurj e (Submodule.Quotient.mk x) =
      rho e x := rfl

/-- **The identifications of the levels commute with the transition maps of the `p`-adic tower of
`M`**: both sides send the class of `x` to the restriction of `ρ_{e'}(x)`, by `hmono` read as an
equality rather than as an implication. -/
public theorem towerLevelEquiv_transitionMap
    (hmono : ∀ {a b : ℕ}, a ≤ b → ∀ x : M, rho b x = 0 → rho a x = 0)
    (hstep : ∀ (e : ℕ) (x : M), rho e x = 0 →
      ∃ u : M, rho (e + 1) x = (p ^ (N + e) : ℕ) • rho (e + 1) u)
    (hann : ∀ (e : ℕ) (z : P e), (p ^ (N + e) : ℕ) • z = 0)
    (hsep : ∀ x : M, (∀ e : ℕ, rho e x = 0) → x = 0)
    (hsurj : ∀ e : ℕ, Function.Surjective (rho e))
    [IsPrecomplete (pAdicIdeal (A := R) p) M] {a b : ℕ} (hab : a ≤ b)
    (pi : P b →ₗ[R] P a) (hpi : ∀ x : M, pi (rho b x) = rho a x)
    (z : M ⧸ (pAdicIdeal (A := R) p ^ (N + b) • (⊤ : Submodule R M))) :
    pi (towerLevelEquiv p rho N hmono hstep hann hsep hsurj b z) =
      towerLevelEquiv p rho N hmono hstep hann hsep hsurj a
        (AdicCompletion.transitionMap (pAdicIdeal (A := R) p) M
          (Nat.add_le_add_left hab N) z) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [towerLevelEquiv_mk, transitionMap_mk, towerLevelEquiv_mk, hpi]

end Tower

end PAdicCompletion

end Crystalline

end
