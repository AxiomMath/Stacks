module

public import StacksFrontier.RingTheory.AdicCompletion.HomCompletion

/-!
# The completion of a module of homomorphisms, level by level

Let `I` be an ideal of a Noetherian ring `A` and let `P`, `Q` be finite `A`-modules.  For every
`n` reduction modulo `Iⁿ` gives a map

`κₙ : Hom_A(P, Q) / Iⁿ Hom_A(P, Q) ⟶ Hom_A(P, Q / Iⁿ Q)`,

and these are compatible in `n`.  None of them need be bijective, but their inverse limit is:
a compatible family `(cₙ)` of maps `cₙ : P ⟶ Q / Iⁿ Q` comes from a unique element of the
completion of `Hom_A(P, Q)`.  This is Stacks 00MB read on the levels, and it is the algebraic
input of the Stacks 0882 computation on an affine chart.

## Main results

* `AdicCompletion.C1573.homQuotientMap`: the map `κₙ`.
* `AdicCompletion.C1573.homCompletionEquiv_apply_val`: the equivalence
  `AdicCompletion.homCompletionEquiv` of Stacks 00MB is `κₙ` on the level `n`.
* `AdicCompletion.C1573.existsUnique_homQuotientMap_eq`: **a compatible family of maps
  `P ⟶ Q / Iⁿ Q` comes from a unique element of `Hom_A(P, Q)^∧`.**

## References

* [Stacks Project, Tag 00MB](https://stacks.math.columbia.edu/tag/00MB)
-/

@[expose] public noncomputable section

namespace AdicCompletion.C1573

universe u

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- A module killed by `Iⁿ` is `I`-adically Hausdorff. -/
theorem isHausdorff_quotient_pow_smul_top {Q : Type*} [AddCommGroup Q] [Module A Q] (n : ℕ) :
    IsHausdorff I (Q ⧸ (I ^ n • ⊤ : Submodule A Q)) := by
  refine ⟨fun x hx => ?_⟩
  have h := hx n
  rw [SModEq.zero] at h
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hle : I ^ n • (⊤ : Submodule A (Q ⧸ (I ^ n • ⊤ : Submodule A Q))) ≤ ⊥ := by
    rw [Submodule.smul_le]
    intro r hr z _
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [← Submodule.Quotient.mk_smul, Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  exact (Submodule.mem_bot A).1 (hle h)

variable {P Q : Type u} [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]

/-- The reduction map `κₙ : Hom_A(P, Q) / Iⁿ Hom_A(P, Q) ⟶ Hom_A(P, Q / Iⁿ Q)`. -/
def homQuotientMap (n : ℕ) :
    (P →ₗ[A] Q) ⧸ (I ^ n • ⊤ : Submodule A (P →ₗ[A] Q)) →ₗ[A]
      (P →ₗ[A] Q ⧸ (I ^ n • ⊤ : Submodule A Q)) :=
  Submodule.liftQ _ (LinearMap.compRight _ (Submodule.mkQ _)) (by
    rw [Submodule.smul_le]
    intro r hr f _
    refine LinearMap.ext fun p => ?_
    change (Submodule.mkQ _) ((r • f) p) = 0
    rw [LinearMap.smul_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hr Submodule.mem_top)

/-- `κₙ` sends the class of `f` to the map `p ↦ f p mod Iⁿ Q`. -/
@[simp]
theorem homQuotientMap_mk (n : ℕ) (f : P →ₗ[A] Q) (p : P) :
    homQuotientMap I n (Submodule.Quotient.mk f) p = Submodule.Quotient.mk (f p) :=
  rfl

variable [IsNoetherianRing A] [Module.Finite A P] [Module.Finite A Q]

/-- **The equivalence of Stacks 00MB, level by level**: the level-`n` component of the image of
`w ∈ Hom_A(P, Q)^∧` at `p` is `κₙ` of the level-`n` component of `w`, applied to `p`. -/
theorem homCompletionEquiv_apply_val (w : AdicCompletion I (P →ₗ[A] Q)) (p : P) (n : ℕ) :
    (homCompletionEquiv I w p).val n = homQuotientMap I n (w.val n) p := by
  have : IsHausdorff I (Q ⧸ (I ^ n • ⊤ : Submodule A Q)) := isHausdorff_quotient_pow_smul_top I n
  have h := linearMap_ext_of (I.fg_of_isNoetherianRing)
    ((eval I Q n).comp ((LinearMap.applyₗ p).comp (homCompletionEquiv I).toLinearMap))
    ((LinearMap.applyₗ p).comp ((homQuotientMap I n).comp (eval I (P →ₗ[A] Q) n)))
    (fun f => by
      show (homCompletionEquiv I (of I _ f) p).val n = homQuotientMap I n ((of I _ f).val n) p
      rw [homCompletionEquiv_of_apply]
      rfl)
  exact LinearMap.congr_fun h w

/-- **A compatible family of maps `P ⟶ Q / Iⁿ Q` comes from a unique element of the completion
of `Hom_A(P, Q)`.** -/
theorem existsUnique_homQuotientMap_eq
    (c : ∀ n : ℕ, P →ₗ[A] Q ⧸ (I ^ n • ⊤ : Submodule A Q))
    (hc : ∀ {m n : ℕ} (hle : m ≤ n), transitionMap I Q hle ∘ₗ c n = c m) :
    ∃! w : AdicCompletion I (P →ₗ[A] Q), ∀ n, homQuotientMap I n (w.val n) = c n := by
  refine ⟨(homCompletionEquiv I).symm (lift I c hc), fun n => LinearMap.ext fun p => ?_,
    fun w hw => (homCompletionEquiv I).injective (LinearMap.ext fun p => ext fun n => ?_)⟩
  · rw [← homCompletionEquiv_apply_val, LinearEquiv.apply_symm_apply]
    rfl
  · rw [homCompletionEquiv_apply_val, hw n, LinearEquiv.apply_symm_apply]
    rfl

/-- **A level-by-level injectivity statement for `Hom_A(P, Q)^∧`**: an element of the completion
of `Hom_A(P, Q)` is determined by the maps `P ⟶ Q / Iⁿ Q` it induces on the levels. -/
theorem eq_of_homQuotientMap_eq {w w' : AdicCompletion I (P →ₗ[A] Q)}
    (h : ∀ n, homQuotientMap I n (w.val n) = homQuotientMap I n (w'.val n)) : w = w' :=
  (homCompletionEquiv I).injective (LinearMap.ext fun p => ext fun n => by
    rw [homCompletionEquiv_apply_val, homCompletionEquiv_apply_val, h n])

omit [IsNoetherianRing A] [Module.Finite A P] [Module.Finite A Q] in
/-- The transition maps of the levels compose. -/
theorem transitionMap_trans_apply {M : Type*} [AddCommGroup M] [Module A M] {k m n : ℕ}
    (hkm : k ≤ m) (hmn : m ≤ n) (z : M ⧸ (I ^ n • ⊤ : Submodule A M)) :
    transitionMap I M (hkm.trans hmn) z = transitionMap I M hkm (transitionMap I M hmn z) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rfl

omit [IsNoetherianRing A] [Module.Finite A P] [Module.Finite A Q] in
/-- A family of maps into the levels which is compatible with the successive transition maps
is compatible with all of them. -/
theorem transitionMap_comp_of_succ (c : ∀ n : ℕ, P →ₗ[A] Q ⧸ (I ^ n • ⊤ : Submodule A Q))
    (hc : ∀ n, transitionMap I Q (Nat.le_succ n) ∘ₗ c (n + 1) = c n) {m n : ℕ} (hle : m ≤ n) :
    transitionMap I Q hle ∘ₗ c n = c m := by
  induction n, hle using Nat.le_induction with
  | base =>
    refine LinearMap.ext fun p => ?_
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (c m p)
    rw [LinearMap.comp_apply, ← hx]
    rfl
  | succ n hmn ih =>
    refine LinearMap.ext fun p => ?_
    rw [LinearMap.comp_apply, transitionMap_trans_apply I hmn (Nat.le_succ n), ← ih,
      ← hc n]
    rfl

omit [IsNoetherianRing A] [Module.Finite A P] [Module.Finite A Q] in
/-- A linear equivalence preserves membership in `J • ⊤`. -/
theorem linearEquiv_mem_smul_top_iff {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N) (J : Ideal A) (x : M) :
    e x ∈ J • (⊤ : Submodule A N) ↔ x ∈ J • (⊤ : Submodule A M) := by
  have h : Submodule.map e.toLinearMap (J • (⊤ : Submodule A M)) = J • ⊤ := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  rw [← h, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

/-- **Stacks 0882 on the sections over an affine, in the abstract.**  Let `A` be Noetherian,
`I ⊆ A` an ideal and `P`, `Q` finite `A`-modules.  Let `H` be an `A`-module identified with
`Hom_A(P, Q)` by `ε`, let `π n : H ⟶ X n` be surjections with kernel `I ^ (n + 1) H`, compatible
with transition maps of the `X n`, and let `ψ n` embed sets `Y n`, with transition maps, into
`Hom_A(P, Q / I ^ (n + 1) Q)`, compatibly with the transitions.  Then maps `c n : X n → Y n`
with `ψ n (c n (π n h)) = (ε h mod I ^ (n + 1))` induce a bijection of the inverse limits.

On an affine chart, `H` is `Hom(M, N)`, `X n` its quotient by `𝓘 ^ (n + 1)`, `Y n` the
morphisms `M ⟶ N / 𝓘 ^ (n + 1) N` and `c n` the comparison. -/
theorem bijective_limit_of_homQuotient {H : Type*} [AddCommGroup H] [Module A H]
    (ε : H ≃ₗ[A] (P →ₗ[A] Q)) {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Module A (X n)]
    (trX : ∀ n, X (n + 1) → X n) (π : ∀ n, H →ₗ[A] X n)
    (hπs : ∀ n, Function.Surjective (π n))
    (hπk : ∀ n, LinearMap.ker (π n) = I ^ (n + 1) • (⊤ : Submodule A H))
    (hπtr : ∀ n h, trX n (π (n + 1) h) = π n h)
    {Y : ℕ → Type*} (trY : ∀ n, Y (n + 1) → Y n)
    (ψ : ∀ n, Y n → (P →ₗ[A] Q ⧸ (I ^ (n + 1) • ⊤ : Submodule A Q)))
    (hψ : ∀ n, Function.Injective (ψ n))
    (hψtr : ∀ n y, ψ n (trY n y) = transitionMap I Q (Nat.le_succ (n + 1)) ∘ₗ ψ (n + 1) y)
    (c : ∀ n, X n → Y n)
    (hc : ∀ n h, ψ n (c n (π n h)) = (Submodule.mkQ _) ∘ₗ ε h)
    (Φ : { t : ∀ n, X n // ∀ n, trX n (t (n + 1)) = t n } →
      { y : ∀ n, Y n // ∀ n, trY n (y (n + 1)) = y n })
    (hΦ : ∀ t n, (Φ t).1 n = c n (t.1 n)) :
    Function.Bijective Φ := by
  have hK : ∀ n (h h' : H), π n h = π n h' ↔
      (Submodule.Quotient.mk (ε h) : (P →ₗ[A] Q) ⧸ (I ^ (n + 1) • ⊤ : Submodule A _)) =
        Submodule.Quotient.mk (ε h') := by
    intro n h h'
    rw [Submodule.Quotient.eq, ← map_sub, linearEquiv_mem_smul_top_iff, ← hπk n,
      LinearMap.mem_ker, map_sub, sub_eq_zero]
  have hlift : ∀ t : { t : ∀ n, X n // ∀ n, trX n (t (n + 1)) = t n }, ∃ h : ℕ → H,
      ∀ n, π n (h n) = t.1 n := fun t => ⟨fun n => (hπs n (t.1 n)).choose,
        fun n => (hπs n (t.1 n)).choose_spec⟩
  have hcauchy : ∀ (t : { t : ∀ n, X n // ∀ n, trX n (t (n + 1)) = t n }) (h : ℕ → H),
      (∀ n, π n (h n) = t.1 n) → ∀ n,
        (Submodule.Quotient.mk (ε (h (n + 1))) :
          (P →ₗ[A] Q) ⧸ (I ^ (n + 1) • ⊤ : Submodule A _)) = Submodule.Quotient.mk (ε (h n)) := by
    intro t h hh n
    rw [← hK, ← hπtr, hh, hh, t.2 n]
  let mkC : (t : { t : ∀ n, X n // ∀ n, trX n (t (n + 1)) = t n }) → (h : ℕ → H) →
      (∀ n, π n (h n) = t.1 n) → AdicCompletion I (P →ₗ[A] Q) := fun t h hh =>
    AdicCompletion.mk I _ (AdicCauchySequence.mk I _ (fun n => ε (h n)) fun n =>
      (SModEq.mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n)))
        (hcauchy t h hh n)).symm)
  have hmkC : ∀ t h hh (n : ℕ), homQuotientMap I n ((mkC t h hh).val n) =
      (Submodule.mkQ (I ^ n • ⊤ : Submodule A Q)) ∘ₗ ε (h n) := fun _ _ _ _ => rfl
  refine ⟨fun t t' htt => ?_, fun y => ?_⟩
  · obtain ⟨h, hh⟩ := hlift t
    obtain ⟨h', hh'⟩ := hlift t'
    have hagree : ∀ n, (Submodule.mkQ _) ∘ₗ ε (h n) =
        (Submodule.mkQ (I ^ (n + 1) • ⊤ : Submodule A Q)) ∘ₗ ε (h' n) := by
      intro n
      rw [← hc, ← hc, hh, hh', ← hΦ, ← hΦ, htt]
    have hw := eq_of_homQuotientMap_eq I (w := mkC t h hh) (w' := mkC t' h' hh') fun m => by
        rw [hmkC t h hh, hmkC t' h' hh']
        refine LinearMap.ext fun p => ?_
        exact congrArg (transitionMap I Q (Nat.le_succ m)) (LinearMap.congr_fun (hagree m) p)
    refine Subtype.ext (funext fun n => ?_)
    rw [← hh, ← hh', hK]
    have h1 := congrArg (fun w : AdicCompletion I (P →ₗ[A] Q) => w.val (n + 1)) hw
    exact ((hcauchy t h hh n).symm.trans h1).trans (hcauchy t' h' hh' n)
  · let cc : ∀ n : ℕ, P →ₗ[A] Q ⧸ (I ^ n • ⊤ : Submodule A Q)
      | 0 => transitionMap I Q (Nat.zero_le 1) ∘ₗ ψ 0 (y.1 0)
      | n + 1 => ψ n (y.1 n)
    have hsucc : ∀ n, transitionMap I Q (Nat.le_succ n) ∘ₗ cc (n + 1) = cc n := by
      intro n
      cases n with
      | zero => rfl
      | succ n => exact (hψtr n _).symm.trans (congrArg (ψ n) (y.2 n))
    obtain ⟨w, hw, -⟩ := existsUnique_homQuotientMap_eq I cc
      (transitionMap_comp_of_succ I cc hsucc)
    have hg : ∀ n, ∃ g : P →ₗ[A] Q, Submodule.Quotient.mk g = w.val (n + 1) := fun n =>
      Submodule.Quotient.mk_surjective _ _
    choose g hg using hg
    have hgc : ∀ n, (Submodule.Quotient.mk (g (n + 1)) :
        (P →ₗ[A] Q) ⧸ (I ^ (n + 1) • ⊤ : Submodule A _)) = Submodule.Quotient.mk (g n) := by
      intro n
      rw [hg n, ← w.2 (Nat.le_succ (n + 1)), ← hg (n + 1)]
      rfl
    refine ⟨⟨fun n => π n (ε.symm (g n)), fun n => ?_⟩, ?_⟩
    · rw [hπtr, hK, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      exact hgc n
    · refine Subtype.ext (funext fun n => ?_)
      rw [hΦ]
      refine hψ n ?_
      rw [hc, LinearEquiv.apply_symm_apply]
      show _ = cc (n + 1)
      rw [← hw (n + 1), ← hg n]
      rfl

end AdicCompletion.C1573

end
