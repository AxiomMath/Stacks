module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedBaseChangeCancel
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedFormsUnitZero
public import StacksFrontier.AlgebraicGeometry.Crystalline.EnvelopeCompletionFormsBasis
public import StacksFrontier.RingTheory.DividedPowers.CompletionUniversalProperty

/-!
# The completed divided power forms of a ring and of its `p`-adic completion

Let `(B, J, δ)` be a divided power ring which is an `A`-algebra, with `p` nilpotent modulo `J`,
and let `B̂` be its `p`-adic completion with the completed divided powers `δ̂` of
[Stacks, Tag 07KD].  There are two candidates for the completed de Rham complex of `B̂`:

* the `p`-adic completion `Ω̂^i_B` of the divided power forms `Ω^i_{B/A,δ}` of `B`, which is the
  family [Stacks, Tag 07J9] defines `Ω_D` by and the one [Stacks, Tag 07LG] is stated with;
* the `p`-adic completion `Ω̂^i_{B̂}` of the divided power forms `Ω^i_{B̂/A,δ̂}` of `B̂` itself,
  which is functorial in divided power morphisms between *complete* rings.

This module proves that the comparison `Ω̂^i_B → Ω̂^i_{B̂}` induced by `B → B̂`
(`Crystalline.completedMapDifferentialForms`) is bijective in every degree.  The inverse is built
from the universal property of `Ω_{B̂/A,δ̂}`: the universal differential of `Ω̂^1_B` is a divided
power derivation of `(B̂, Ĵ, δ̂)` (`Crystalline.completedFormsDifferential_dpow`), and its lift is
extended to the exterior powers by the completed wedge of one-forms
(`Crystalline.completedIotaMulti`).

## Main definitions

* `Crystalline.completedIotaMulti` — the `p`-adic completion of `exteriorPower.ιMulti`, an
  alternating map over the completed ring.
* `Crystalline.completedFormsDPDerivationOfCompletion` — the universal differential
  `B̂ → Ω̂^1_B` as a divided power derivation of the completed divided power ring.
* `Crystalline.completedFormsOfCompletionEquiv` — **`Ω̂^i_B ≃ Ω̂^i_{B̂}`**.

## References

* [Stacks Project, Tag 07KD](https://stacks.math.columbia.edu/tag/07KD)
* [Stacks Project, Tag 07J9](https://stacks.math.columbia.edu/tag/07J9)
* [Stacks Project, Lemma 60.21.4, Tag 07LH](https://stacks.math.columbia.edu/tag/07LH)
-/

@[expose] public noncomputable section

open DividedPowers

universe u v w

namespace Crystalline

/-! ### The completion of `exteriorPower.ιMulti` -/

section CompletedIotaMulti

variable (p : ℕ) (R : Type u) [CommRing R] (X : Type v) [AddCommGroup X] [Module R X] (i : ℕ)

local notation "Ip" => pAdicIdeal (A := R) p

/-- **A wedge vanishes modulo `(p)ⁿ` as soon as one factor lies in `(p)ⁿ X`.** -/
theorem mk_ιMulti_eq_zero_of_mem {n : ℕ} (x : Fin i → X) (j : Fin i)
    (hx : x j ∈ (Ip ^ n • ⊤ : Submodule R X)) :
    (Submodule.Quotient.mk (exteriorPower.ιMulti R i x) :
      ⋀[R]^i X ⧸ (Ip ^ n • ⊤ : Submodule R (⋀[R]^i X))) = 0 := by
  classical
  suffices h : ∀ z ∈ (Ip ^ n • ⊤ : Submodule R X),
      (Submodule.Quotient.mk (exteriorPower.ιMulti R i (Function.update x j z)) :
        ⋀[R]^i X ⧸ (Ip ^ n • ⊤ : Submodule R (⋀[R]^i X))) = 0 by
    simpa [Function.update_eq_self] using h (x j) hx
  intro z hz
  refine Submodule.smul_induction_on hz (fun r hr y _ ↦ ?_) (fun y y' hy hy' ↦ ?_)
  · rw [AlternatingMap.map_update_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · rw [AlternatingMap.map_update_add, Submodule.Quotient.mk_add, hy, hy', add_zero]

/-- **A wedge modulo `(p)ⁿ` only depends on its factors modulo `(p)ⁿ`.** -/
theorem mk_ιMulti_eq_of_sub_mem {n : ℕ} (x y : Fin i → X)
    (h : ∀ j, x j - y j ∈ (Ip ^ n • ⊤ : Submodule R X)) :
    (Submodule.Quotient.mk (exteriorPower.ιMulti R i x) :
      ⋀[R]^i X ⧸ (Ip ^ n • ⊤ : Submodule R (⋀[R]^i X))) =
      Submodule.Quotient.mk (exteriorPower.ιMulti R i y) := by
  classical
  have hxy : x = (x - y) + y := by simp
  have hsum := (exteriorPower.ιMulti R i).toMultilinearMap.map_add_univ (x - y) y
  rw [← hxy] at hsum
  show (Submodule.mkQ _) (exteriorPower.ιMulti R i x) =
    (Submodule.mkQ _) (exteriorPower.ιMulti R i y)
  rw [show (exteriorPower.ιMulti R i x) = (exteriorPower.ιMulti R i).toMultilinearMap x from rfl,
    hsum, map_sum, Finset.sum_eq_single (∅ : Finset (Fin i))]
  · simp
  · intro s _ hs
    obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    refine mk_ιMulti_eq_zero_of_mem p R X i _ j ?_
    rw [Finset.piecewise_eq_of_mem _ _ _ hj]
    exact h j
  · intro h'
    exact absurd (Finset.mem_univ _) h'

/-- The level-`pⁿ` value of the completed wedge, computed on chosen representatives. -/
def levelIotaMulti (n : ℕ) (v : Fin i → X ⧸ (Ip ^ n • ⊤ : Submodule R X)) :
    ⋀[R]^i X ⧸ (Ip ^ n • ⊤ : Submodule R (⋀[R]^i X)) :=
  Submodule.Quotient.mk (exteriorPower.ιMulti R i fun j ↦
    Function.surjInv (Submodule.mkQ_surjective (Ip ^ n • ⊤ : Submodule R X)) (v j))

/-- The level value of the completed wedge does not depend on the representatives. -/
theorem levelIotaMulti_mk (n : ℕ) (x : Fin i → X) :
    levelIotaMulti p R X i n (fun j ↦ Submodule.Quotient.mk (x j)) =
      Submodule.Quotient.mk (exteriorPower.ιMulti R i x) := by
  refine mk_ιMulti_eq_of_sub_mem p R X i _ _ fun j ↦ ?_
  rw [← Submodule.Quotient.eq]
  exact Function.surjInv_eq (Submodule.mkQ_surjective (Ip ^ n • ⊤ : Submodule R X)) _

/-- The underlying function of `Crystalline.completedIotaMulti`. -/
def completedIotaMultiFun (v : Fin i → AdicCompletion Ip X) :
    AdicCompletion Ip (⋀[R]^i X) :=
  ⟨fun n ↦ levelIotaMulti p R X i n (fun j ↦ (v j).val n), by
    intro m n hmn
    choose x hx using fun j ↦ Submodule.Quotient.mk_surjective
      (Ip ^ n • ⊤ : Submodule R X) ((v j).val n)
    have hm : (fun j ↦ (v j).val m) = fun j ↦ Submodule.Quotient.mk (x j) := by
      funext j
      rw [← (v j).property hmn, ← hx j, PAdicCompletion.transitionMap_mk p R hmn]
    have hn : (fun j ↦ (v j).val n) = fun j ↦ Submodule.Quotient.mk (x j) := by
      funext j
      rw [hx j]
    change AdicCompletion.transitionMap Ip (⋀[R]^i X) hmn
        (levelIotaMulti p R X i n (fun j ↦ (v j).val n)) =
      levelIotaMulti p R X i m (fun j ↦ (v j).val m)
    rw [hm, hn, levelIotaMulti_mk, levelIotaMulti_mk, PAdicCompletion.transitionMap_mk p R hmn]⟩

/-- The level value of the completed wedge, on any representatives. -/
theorem completedIotaMultiFun_val (v : Fin i → AdicCompletion Ip X) (n : ℕ) (x : Fin i → X)
    (hx : ∀ j, (v j).val n = Submodule.Quotient.mk (x j)) :
    (completedIotaMultiFun p R X i v).val n =
      Submodule.Quotient.mk (exteriorPower.ιMulti R i x) := by
  show levelIotaMulti p R X i n (fun j ↦ (v j).val n) = _
  rw [show (fun j ↦ (v j).val n) = fun j ↦ Submodule.Quotient.mk (x j) from funext hx,
    levelIotaMulti_mk]

/-- **The completed wedge `Ω̂ × ⋯ × Ω̂ → (⋀ⁱ Ω)^∧`**, the `p`-adic completion of
`exteriorPower.ιMulti`, alternating over the completed ring.  It is built level by level, like
`Crystalline.PAdicCompletion.mapBilinear`. -/
def completedIotaMulti :
    AdicCompletion Ip X [⋀^Fin i]→ₗ[AdicCompletion Ip R] AdicCompletion Ip (⋀[R]^i X) where
  toFun := completedIotaMultiFun p R X i
  map_update_add' := by
    classical
    intro _ v j a b
    refine AdicCompletion.ext fun n ↦ ?_
    choose x hx using fun k ↦ Submodule.Quotient.mk_surjective
      (Ip ^ n • ⊤ : Submodule R X) ((v k).val n)
    obtain ⟨ra, hra⟩ := Submodule.Quotient.mk_surjective (Ip ^ n • ⊤ : Submodule R X) (a.val n)
    obtain ⟨rb, hrb⟩ := Submodule.Quotient.mk_surjective (Ip ^ n • ⊤ : Submodule R X) (b.val n)
    have key : ∀ (z : AdicCompletion Ip X) (rz : X),
        z.val n = Submodule.Quotient.mk rz →
          (completedIotaMultiFun p R X i (Function.update v j z)).val n =
            Submodule.Quotient.mk (exteriorPower.ιMulti R i (Function.update x j rz)) := by
      intro z rz hz
      refine completedIotaMultiFun_val p R X i _ n _ fun k ↦ ?_
      by_cases hk : k = j
      · subst hk
        simp only [Function.update_self]
        exact hz
      · simp only [Function.update_of_ne hk]
        exact (hx k).symm
    rw [AdicCompletion.val_add_apply, key (a + b) (ra + rb)
      (by rw [AdicCompletion.val_add_apply, ← hra, ← hrb, Submodule.Quotient.mk_add]),
      key a ra hra.symm, key b rb hrb.symm, AlternatingMap.map_update_add,
      Submodule.Quotient.mk_add]
  map_update_smul' := by
    classical
    intro _ v j c a
    refine AdicCompletion.ext fun n ↦ ?_
    choose x hx using fun k ↦ Submodule.Quotient.mk_surjective
      (Ip ^ n • ⊤ : Submodule R X) ((v k).val n)
    obtain ⟨ra, hra⟩ := Submodule.Quotient.mk_surjective (Ip ^ n • ⊤ : Submodule R X) (a.val n)
    obtain ⟨rc, hrc⟩ := Submodule.Quotient.mk_surjective (Ip ^ n • ⊤ : Submodule R R) (c.val n)
    have key : ∀ (z : AdicCompletion Ip X) (rz : X),
        z.val n = Submodule.Quotient.mk rz →
          (completedIotaMultiFun p R X i (Function.update v j z)).val n =
            Submodule.Quotient.mk (exteriorPower.ιMulti R i (Function.update x j rz)) := by
      intro z rz hz
      refine completedIotaMultiFun_val p R X i _ n _ fun k ↦ ?_
      by_cases hk : k = j
      · subst hk
        simp only [Function.update_self]
        exact hz
      · simp only [Function.update_of_ne hk]
        exact (hx k).symm
    have hca : (c • a).val n = Submodule.Quotient.mk (rc • ra) := by
      rw [AdicCompletion.smul_eval, ← hra, ← hrc]
      rfl
    rw [AdicCompletion.smul_eval, key (c • a) (rc • ra) hca, key a ra hra.symm,
      AlternatingMap.map_update_smul, ← hrc]
    rfl
  map_eq_zero_of_eq' := by
    intro v j k hjk hne
    refine AdicCompletion.ext fun n ↦ ?_
    change levelIotaMulti p R X i n (fun l ↦ (v l).val n) = 0
    exact congrArg Submodule.Quotient.mk
      ((exteriorPower.ιMulti R i).map_eq_zero_of_eq _ (by simp only [hjk]) hne) |>.trans
        (Submodule.Quotient.mk_zero _)

/-- The completed wedge at a level, on any representatives. -/
theorem completedIotaMulti_val (v : Fin i → AdicCompletion Ip X) (n : ℕ) (x : Fin i → X)
    (hx : ∀ j, (v j).val n = Submodule.Quotient.mk (x j)) :
    (completedIotaMulti p R X i v).val n = Submodule.Quotient.mk (exteriorPower.ιMulti R i x) :=
  completedIotaMultiFun_val p R X i v n x hx

/-- **The completed wedge extends the wedge.** -/
@[simp] theorem completedIotaMulti_of (x : Fin i → X) :
    completedIotaMulti p R X i (fun j ↦ AdicCompletion.of Ip X (x j)) =
      AdicCompletion.of Ip (⋀[R]^i X) (exteriorPower.ιMulti R i x) :=
  AdicCompletion.ext fun n ↦ completedIotaMulti_val p R X i _ n x fun _ ↦ rfl

end CompletedIotaMulti

/-! ### The completed divided power ring and its universal differential -/

section Completion

variable (p : ℕ) (A : Type u) [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
  {J : Ideal B} (hJ : DividedPowers J) (hp : IsNilpotent (Ideal.Quotient.mk J (p : B)))

local notation "Ip" => pAdicIdeal (A := B) p

/-- **The completed divided powers `δ̂`** on the completed divided power ideal of `B̂`,
[Stacks, Tag 07KD] part (3). -/
abbrev completionDividedPowers : DividedPowers (completionIdeal J p hp) :=
  (completedDividedPowers J hJ p hp).1

/-- **The completion `(B̂, Ĵ, δ̂)` as a divided power ring.** -/
abbrev completionDPRing : DividedPowerRing.{v} :=
  DividedPowerRing.of (AdicCompletion Ip B) (completionIdeal J p hp)
    (completionDividedPowers p hJ hp)

/-- The structure map `B → B̂` as a map of `A`-algebras. -/
abbrev completionAlgHom : B →ₐ[A] AdicCompletion Ip B :=
  IsScalarTower.toAlgHom A B (AdicCompletion Ip B)

/-- The structure map `B → B̂` is a divided power morphism. -/
theorem isDPMorphism_completionAlgHom :
    IsDPMorphism hJ (completionDividedPowers p hJ hp) (completionAlgHom p A).toRingHom :=
  (completionDPMorphism J hJ p hp).isDPMorphism

/-- **The divided power chain rule for the universal differential of `Ω̂¹_B` on the completed
ring**: `d (δ̂_n x) = δ̂_{n-1}(x) d x` for `x` in the completed divided power ideal.  At the
level `pᵉ` both sides are computed from a representative of `x` in `J`, where this is the chain
rule of the uncompleted differential. -/
theorem completedFormsDifferential_dpow {n : ℕ} (hn : 0 < n) {x : AdicCompletion Ip B}
    (hx : x ∈ completionIdeal J p hp) :
    completedFormsDifferential p A hJ ((completionDividedPowers p hJ hp).dpow n x) =
      (completionDividedPowers p hJ hp).dpow (n - 1) x • completedFormsDifferential p A hJ x := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set c := completionIdealRepSequence J p hp ⟨x, hx⟩ with hc
  have hxc : x = AdicCompletion.map Ip J.subtype (AdicCompletion.mk Ip J c) :=
    (completionIdealRepSequence_map_eq J p hp ⟨x, hx⟩).symm
  have hdp : ∀ k, (completionDividedPowers p hJ hp).dpow k x =
      AdicCompletion.mk Ip B (dividedPowerSequence J hJ p k c) := by
    intro k
    rw [hxc]
    exact completedDpowAux_of_rep J hJ p hp k c
  refine AdicCompletion.ext fun e ↦ ?_
  have hxe : x.val e = Submodule.Quotient.mk (c e : B) := by
    rw [hxc, AdicCompletion.map_mk]
    rfl
  have hde : ∀ k, ((completionDividedPowers p hJ hp).dpow k x).val e =
      Submodule.Quotient.mk (hJ.dpow k (c e : B)) := by
    intro k
    rw [hdp k]
    rfl
  rw [completedFormsDifferential_val p A hJ e _ _ (hde (m + 1)), AdicCompletion.smul_eval,
    completedFormsDifferential_val p A hJ e _ _ hxe, Nat.add_sub_cancel, hde m,
    dividedPowerOneForm_apply, dividedPowerOneForm_apply,
    dividedPowerDifferential_dpow (A := A) hJ (c e) m, map_smul]
  rfl

/-- **The universal differential of `Ω̂¹_B` as a divided power derivation of the completed
divided power ring `(B̂, Ĵ, δ̂)`.** -/
def completedFormsDPDerivationOfCompletion :
    DividedPowerDerivation A (completionDPRing p hJ hp)
      (algebraMap A (AdicCompletion Ip B)) (completedDividedPowerForms p A hJ 1) where
  toDerivation := Derivation.mk'
    (AddMonoidHom.toIntLinearMap (AddMonoidHom.mk' (completedFormsDifferential p A hJ)
      (completedFormsDifferential_add p A hJ)))
    (fun b c ↦ completedFormsDifferential_mul p A hJ b c)
  map_ringHom' a := by
    change completedFormsDifferential p A hJ (algebraMap A (AdicCompletion Ip B) a) = 0
    rw [IsScalarTower.algebraMap_apply A B (AdicCompletion Ip B), AdicCompletion.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, completedFormsDifferential_of,
      dividedPowerOneForm_apply]
    change AdicCompletion.of _ _ ((exteriorPower.oneEquiv B
      (dividedPowerDifferentials (A := A) hJ)).symm
      ((dividedPowerDifferentialRelations (A := A) hJ).mkQ
        (KaehlerDifferential.D A B (algebraMap A B a)))) = 0
    rw [Derivation.map_algebraMap, map_zero, map_zero, map_zero]
  map_dpow' n hn x hx := completedFormsDifferential_dpow p A hJ hp hn hx

/-- The divided power derivation `B̂ → Ω̂¹_B` is the universal differential of `Ω̂¹_B`. -/
@[simp] theorem completedFormsDPDerivationOfCompletion_apply (x : AdicCompletion Ip B) :
    completedFormsDPDerivationOfCompletion p A hJ hp x = completedFormsDifferential p A hJ x :=
  rfl

end Completion

/-! ### A completion of a module is complete over the completed ring -/

section CompleteOverCompletion

variable (p : ℕ) {B : Type v} [CommRing B] (Y : Type w) [AddCommGroup Y] [Module B Y]

/-- **The `p`-adic completion of a `B`-module is `p`-adically complete over `B̂`.**  The two
filtrations `(p)ⁿ_{B̂} · Ŷ` and `(p)ⁿ_B · Ŷ` are both the subgroup `pⁿ Ŷ`
(`Crystalline.PAdicCompletion.mem_pow_smul_top_iff`), and `Ŷ` is complete for the second. -/
theorem isAdicComplete_adicCompletion_completion :
    IsAdicComplete (pAdicIdeal (A := AdicCompletion (pAdicIdeal (A := B) p) B) p)
      (AdicCompletion (pAdicIdeal (A := B) p) Y) := by
  have hmem : ∀ (n : ℕ) (z : AdicCompletion (pAdicIdeal (A := B) p) Y),
      z ∈ (pAdicIdeal (A := AdicCompletion (pAdicIdeal (A := B) p) B) p ^ n • ⊤ :
        Submodule (AdicCompletion (pAdicIdeal (A := B) p) B) _) ↔
      z ∈ (pAdicIdeal (A := B) p ^ n • ⊤ : Submodule B _) := fun n z ↦ by
    rw [PAdicCompletion.mem_pow_smul_top_iff, PAdicCompletion.mem_pow_smul_top_iff]
  have hsmod : ∀ (n : ℕ) (x y : AdicCompletion (pAdicIdeal (A := B) p) Y),
      x ≡ y [SMOD (pAdicIdeal (A := AdicCompletion (pAdicIdeal (A := B) p) B) p ^ n • ⊤ :
        Submodule (AdicCompletion (pAdicIdeal (A := B) p) B) _)] ↔
      x ≡ y [SMOD (pAdicIdeal (A := B) p ^ n • ⊤ : Submodule B _)] := fun n x y ↦ by
    rw [SModEq.sub_mem, SModEq.sub_mem, hmem]
  have hB : IsAdicComplete (pAdicIdeal (A := B) p) (AdicCompletion (pAdicIdeal (A := B) p) Y) :=
    AdicCompletion.isAdicComplete (pAdicIdeal_fg (R := B) p)
  let haus : IsHausdorff (pAdicIdeal (A := AdicCompletion (pAdicIdeal (A := B) p) B) p)
      (AdicCompletion (pAdicIdeal (A := B) p) Y) :=
    ⟨fun x hx ↦ IsHausdorff.haus hB.toIsHausdorff x fun n ↦ (hsmod n x 0).1 (hx n)⟩
  let prec : IsPrecomplete (pAdicIdeal (A := AdicCompletion (pAdicIdeal (A := B) p) B) p)
      (AdicCompletion (pAdicIdeal (A := B) p) Y) :=
    ⟨fun f hf ↦ by
      obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := pAdicIdeal (A := B) p) f
        fun {m n} hmn ↦ (hsmod m _ _).1 (hf hmn)
      exact ⟨L, fun n ↦ (hsmod n _ _).2 (hL n)⟩⟩
  constructor

end CompleteOverCompletion

/-! ### The comparison `Ω̂ⁱ_B → Ω̂ⁱ_{B̂}` and its inverse -/

section Comparison

variable (p : ℕ) (A : Type u) [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
  {J : Ideal B} (hJ : DividedPowers J) (hp : IsNilpotent (Ideal.Quotient.mk J (p : B)))

local notation "Ip" => pAdicIdeal (A := B) p
local notation "Bh" => AdicCompletion (pAdicIdeal (A := B) p) B
local notation "Iph" => pAdicIdeal (A := AdicCompletion (pAdicIdeal (A := B) p) B) p

/-- `Ω̂¹_B`, read as the completion of `Ω_B` rather than of `⋀¹ Ω_B`. -/
abbrev completedOneFormsEquiv :
    completedDividedPowerForms p A hJ 1 ≃ₗ[Bh]
      AdicCompletion Ip (dividedPowerDifferentials (A := A) hJ) :=
  AdicCompletion.congr Ip (exteriorPower.oneEquiv B (dividedPowerDifferentials (A := A) hJ))

/-- Two additive maps between `p`-adic completions that agree on the image of the module agree
at every point. -/
private theorem adicCompletion_addMonoidHom_apply_eq_of_of (p : ℕ) {R : Type*} [CommRing R]
    {X : Type*} [AddCommGroup X] [Module R X] {S : Type*} [CommRing S] {Y : Type*}
    [AddCommGroup Y] [Module S Y]
    {f g : AdicCompletion (pAdicIdeal (A := R) p) X →+ AdicCompletion (pAdicIdeal (A := S) p) Y}
    {x : AdicCompletion (pAdicIdeal (A := R) p) X}
    (h : ∀ t : X, f (AdicCompletion.of _ X t) = g (AdicCompletion.of _ X t)) : f x = g x :=
  DFunLike.congr_fun (adicCompletion_addMonoidHom_ext_of_of p h) x

/-- **The universal differential of `Ω̂¹_B`, read in the completion of `Ω_B`**, is the
completion of the universal differential `d : B → Ω_B`. -/
theorem completedOneFormsEquiv_completedFormsDifferential (x : Bh) :
    completedOneFormsEquiv p A hJ (completedFormsDifferential p A hJ x) =
      PAdicCompletion.mapAddHom p B B
        (AddMonoidHom.mk' (dividedPowerDifferential (A := A) hJ)
          (dividedPowerDifferential_add hJ)) x := by
  refine adicCompletion_addMonoidHom_apply_eq_of_of p (x := x)
    (f := (completedOneFormsEquiv p A hJ).toLinearMap.toAddMonoidHom.comp
      (PAdicCompletion.mapAddHom p B B (dividedPowerOneForm A hJ)))
    (g := PAdicCompletion.mapAddHom p B B
        (AddMonoidHom.mk' (dividedPowerDifferential (A := A) hJ)
          (dividedPowerDifferential_add hJ))) fun b ↦ by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, PAdicCompletion.mapAddHom_of]
      show AdicCompletion.map Ip _ (AdicCompletion.of _ _ _) = _
      rw [AdicCompletion.map_of, dividedPowerOneForm_apply]
      simp

/-- The lift `Ω_{B̂/A,δ̂} → Ω̂¹_B` of the divided power derivation `B̂ → Ω̂¹_B`, by the universal
property of [Stacks, Tag 07HZ]. -/
def completedFormsLiftOne :
    dividedPowerDifferentials (A := A) (completionDividedPowers p hJ hp) →ₗ[Bh]
      completedDividedPowerForms p A hJ 1 :=
  (dividedPowerDifferentials_lift (A := A) (completionDPRing p hJ hp)
    (completedFormsDPDerivationOfCompletion p A hJ hp)).exists.choose

/-- The lift sends `d b` to `d b`. -/
theorem completedFormsLiftOne_d (b : Bh) :
    completedFormsLiftOne p A hJ hp (dividedPowerDifferential (A := A)
        (completionDividedPowers p hJ hp) b) = completedFormsDifferential p A hJ b :=
  (dividedPowerDifferentials_lift (A := A) (completionDPRing p hJ hp)
    (completedFormsDPDerivationOfCompletion p A hJ hp)).exists.choose_spec b

/-- **The inverse comparison on the uncompleted forms of `B̂`**:
`⋀ⁱ_{B̂} Ω_{B̂/A,δ̂} → Ω̂ⁱ_B`, `d b₁ ∧ ⋯ ∧ d bᵢ ↦ d b₁ ∧ ⋯ ∧ d bᵢ`, through the completed wedge. -/
def completedFormsInvAux (i : ℕ) :
    dividedPowerDifferentialForms (A := A) (completionDividedPowers p hJ hp) i →ₗ[Bh]
      completedDividedPowerForms p A hJ i :=
  exteriorPower.alternatingMapLinearEquiv
    ((completedIotaMulti p B (dividedPowerDifferentials (A := A) hJ) i).compLinearMap
      ((completedOneFormsEquiv p A hJ).toLinearMap ∘ₗ completedFormsLiftOne p A hJ hp))

/-- The inverse comparison on a wedge. -/
theorem completedFormsInvAux_ιMulti (i : ℕ)
    (w : Fin i → dividedPowerDifferentials (A := A) (completionDividedPowers p hJ hp)) :
    completedFormsInvAux p A hJ hp i (exteriorPower.ιMulti Bh i w) =
      completedIotaMulti p B (dividedPowerDifferentials (A := A) hJ) i
        (fun j ↦ completedOneFormsEquiv p A hJ (completedFormsLiftOne p A hJ hp (w j))) :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

/-- **The inverse comparison `Ω̂ⁱ_{B̂} → Ω̂ⁱ_B`**, the extension of
`Crystalline.completedFormsInvAux` to the completion, `Ω̂ⁱ_B` being complete over `B̂`. -/
def completedFormsInv (i : ℕ) :
    completedDividedPowerForms p A (completionDividedPowers p hJ hp) i →ₗ[Bh]
      completedDividedPowerForms p A hJ i :=
  letI := isAdicComplete_adicCompletion_completion p (B := B)
    (dividedPowerDifferentialForms (A := A) hJ i)
  (AdicCompletion.ofLinearEquiv Iph (completedDividedPowerForms p A hJ i)).symm.toLinearMap ∘ₗ
    (AdicCompletion.map Iph (completedFormsInvAux p A hJ hp i)).restrictScalars Bh

/-- The inverse comparison extends `Crystalline.completedFormsInvAux`. -/
theorem completedFormsInv_of (i : ℕ)
    (y : dividedPowerDifferentialForms (A := A) (completionDividedPowers p hJ hp) i) :
    completedFormsInv p A hJ hp i (AdicCompletion.of Iph _ y) =
      completedFormsInvAux p A hJ hp i y := by
  let := isAdicComplete_adicCompletion_completion p (B := B)
    (dividedPowerDifferentialForms (A := A) hJ i)
  show (AdicCompletion.ofLinearEquiv Iph (completedDividedPowerForms p A hJ i)).symm
    (AdicCompletion.map Iph (completedFormsInvAux p A hJ hp i) (AdicCompletion.of Iph _ y)) = _
  rw [AdicCompletion.map_of, AdicCompletion.ofLinearEquiv_symm_of]

/-- **The comparison `Ω̂ⁱ_B → Ω̂ⁱ_{B̂}`** induced by the divided power morphism `B → B̂`, as a
`B̂`-linear map.  It is `Crystalline.completedMapDifferentialForms`; its linearity over the
completed ring, and not only over `B`, holds because both sides are additive and continuous in the
scalar, and agree on the dense image of `B`. -/
def completedFormsOfCompletionMap (i : ℕ) :
    completedDividedPowerForms p A hJ i →ₗ[Bh]
      completedDividedPowerForms p A (completionDividedPowers p hJ hp) i where
  toFun := completedMapDifferentialForms p A hJ (completionDividedPowers p hJ hp)
    (completionAlgHom p A) (isDPMorphism_completionAlgHom p A hJ hp) i
  map_add' := map_add _
  map_smul' c x := by
    have h := adicCompletion_addMonoidHom_ext_of_of p
      (f := (completedMapDifferentialForms p A hJ (completionDividedPowers p hJ hp)
          (completionAlgHom p A) (isDPMorphism_completionAlgHom p A hJ hp) i).toAddMonoidHom.comp
        ((LinearMap.toSpanSingleton Bh _ x).toAddMonoidHom))
      (g := (LinearMap.toSpanSingleton Bh _
        (completedMapDifferentialForms p A hJ (completionDividedPowers p hJ hp)
          (completionAlgHom p A) (isDPMorphism_completionAlgHom p A hJ hp) i x)).toAddMonoidHom)
      fun b ↦ by
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
          LinearMap.toSpanSingleton_apply]
        rw [show AdicCompletion.of Ip B b = algebraMap B Bh b by
          rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply],
          algebraMap_smul, map_smulₛₗ]
        rfl
    exact DFunLike.congr_fun h c

/-- `completedFormsOfCompletionMap` is the comparison `completedMapDifferentialForms` along the
completion morphism `B → B̂`. -/
@[simp] theorem completedFormsOfCompletionMap_apply (i : ℕ)
    (x : completedDividedPowerForms p A hJ i) :
    completedFormsOfCompletionMap p A hJ hp i x =
      completedMapDifferentialForms p A hJ (completionDividedPowers p hJ hp)
        (completionAlgHom p A) (isDPMorphism_completionAlgHom p A hJ hp) i x :=
  rfl

end Comparison

/-! ### The comparison is an isomorphism -/

section Equiv

variable (p : ℕ) (A : Type u) [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
  {J : Ideal B} (hJ : DividedPowers J) (hp : IsNilpotent (Ideal.Quotient.mk J (p : B)))

local notation "Ip" => pAdicIdeal (A := B) p
local notation "Bh" => AdicCompletion (pAdicIdeal (A := B) p) B
local notation "Iph" => pAdicIdeal (A := AdicCompletion (pAdicIdeal (A := B) p) B) p

/-- The completion of the degree-one comparison `Ω_B → Ω_{B̂}`, as a map of completions. -/
abbrev completedOneFormsMap :
    AdicCompletion Ip (dividedPowerDifferentials (A := A) hJ)
      →ₛₗ[(completionAlgHom p A (B := B)).toRingHom]
      AdicCompletion Iph (dividedPowerDifferentials (A := A) (completionDividedPowers p hJ hp)) :=
  adicCompletionMapₛₗ (mapDifferentialsOfDPMorphismₛₗ (A := A) (J := J) (delta := hJ)
    (completionDividedPowers p hJ hp) (completionAlgHom p A)
    (isDPMorphism_completionAlgHom p A hJ hp))
    (pAdicIdeal_map_ringHom_le p (completionAlgHom p A (B := B)).toRingHom)

/-- `(algebraMap B B̂) b = of b`. -/
theorem completionAlgHom_apply (b : B) :
    (completionAlgHom p A) b = AdicCompletion.of Ip B b := by
  show algebraMap B Bh b = _
  rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

/-- The completed degree-one comparison is linear over `B̂`. -/
theorem completedOneFormsMap_smul (c : Bh)
    (z : AdicCompletion Ip (dividedPowerDifferentials (A := A) hJ)) :
    completedOneFormsMap p A hJ hp (c • z) = c • completedOneFormsMap p A hJ hp z := by
  refine adicCompletion_addMonoidHom_apply_eq_of_of p (x := c)
    (f := (completedOneFormsMap p A hJ hp).toAddMonoidHom.comp
      (LinearMap.toSpanSingleton Bh _ z).toAddMonoidHom)
    (g := (LinearMap.toSpanSingleton Bh _ (completedOneFormsMap p A hJ hp z)).toAddMonoidHom)
    fun b ↦ by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
        LinearMap.toSpanSingleton_apply]
      rw [← completionAlgHom_apply p A]
      exact map_smulₛₗ _ b z

/-- **The completed degree-one comparison carries `d x` to `d x`**, for `x ∈ B̂`. -/
theorem completedOneFormsMap_mapAddHom (x : Bh) :
    completedOneFormsMap p A hJ hp (PAdicCompletion.mapAddHom p B B
        (AddMonoidHom.mk' (dividedPowerDifferential (A := A) hJ)
          (dividedPowerDifferential_add hJ)) x) =
      AdicCompletion.of Iph _ (dividedPowerDifferential (A := A)
        (completionDividedPowers p hJ hp) x) := by
  refine adicCompletion_addMonoidHom_apply_eq_of_of p (x := x)
    (f := (completedOneFormsMap p A hJ hp).toAddMonoidHom.comp (PAdicCompletion.mapAddHom p B B
        (AddMonoidHom.mk' (dividedPowerDifferential (A := A) hJ)
          (dividedPowerDifferential_add hJ))))
    (g := (AdicCompletion.of Iph (dividedPowerDifferentials (A := A)
        (completionDividedPowers p hJ hp))).toAddMonoidHom.comp
      (AddMonoidHom.mk' (dividedPowerDifferential (A := A) (completionDividedPowers p hJ hp))
        (dividedPowerDifferential_add _)))
    fun b ↦ by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, PAdicCompletion.mapAddHom_of,
        LinearMap.toAddMonoidHom_coe, AddMonoidHom.mk'_apply]
      rw [adicCompletionMapₛₗ_of, mapDifferentialsOfDPMorphismₛₗ_apply,
        mapDifferentialsOfDPMorphism_d, completionAlgHom_apply]

/-- The lift of `Crystalline.completedFormsLiftOne`, composed with the comparison, is the
completion map. -/
theorem completedOneFormsEquiv_liftOne_map (w : dividedPowerDifferentials (A := A) hJ) :
    completedOneFormsEquiv p A hJ (completedFormsLiftOne p A hJ hp
        (mapDifferentialsOfDPMorphism (A := A) (J := J) (delta := hJ)
          (completionDividedPowers p hJ hp) (completionAlgHom p A)
          (isDPMorphism_completionAlgHom p A hJ hp) w)) =
      AdicCompletion.of Ip _ w := by
  have hw : w ∈ (⊤ : Submodule B (dividedPowerDifferentials (A := A) hJ)) := Submodule.mem_top
  rw [← dividedPowerDifferentials_span (A := A) hJ] at hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    rw [mapDifferentialsOfDPMorphism_d, completedFormsLiftOne_d,
      completedOneFormsEquiv_completedFormsDifferential, completionAlgHom_apply,
      PAdicCompletion.mapAddHom_of]
    rfl
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]
  | smul b x _ hx =>
    rw [mapDifferentialsOfDPMorphism_smul, map_smul, map_smul, hx,
      show (completionAlgHom p A) b = algebraMap B Bh b from rfl, algebraMap_smul, map_smul]

/-- On the side of `B̂`: the comparison of the lift is the completion map. -/
theorem completedOneFormsMap_equiv_liftOne
    (w : dividedPowerDifferentials (A := A) (completionDividedPowers p hJ hp)) :
    completedOneFormsMap p A hJ hp (completedOneFormsEquiv p A hJ
        (completedFormsLiftOne p A hJ hp w)) = AdicCompletion.of Iph _ w := by
  have hw : w ∈ (⊤ : Submodule Bh
      (dividedPowerDifferentials (A := A) (completionDividedPowers p hJ hp))) := Submodule.mem_top
  rw [← dividedPowerDifferentials_span (A := A) (completionDividedPowers p hJ hp)] at hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    rw [completedFormsLiftOne_d, completedOneFormsEquiv_completedFormsDifferential,
      completedOneFormsMap_mapAddHom]
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add x y _ _ hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]
  | smul b x _ hx => rw [map_smul, map_smul, completedOneFormsMap_smul, hx, map_smul]

/-- **The comparison is multiplicative on wedges of one-forms.** -/
theorem completedMapDifferentialForms_completedIotaMulti (i : ℕ)
    (v : Fin i → AdicCompletion Ip (dividedPowerDifferentials (A := A) hJ)) :
    completedMapDifferentialForms p A hJ (completionDividedPowers p hJ hp)
        (completionAlgHom p A) (isDPMorphism_completionAlgHom p A hJ hp) i
        (completedIotaMulti p B (dividedPowerDifferentials (A := A) hJ) i v) =
      completedIotaMulti p Bh (dividedPowerDifferentials (A := A)
        (completionDividedPowers p hJ hp)) i (fun j ↦ completedOneFormsMap p A hJ hp (v j)) := by
  refine AdicCompletion.ext fun n ↦ ?_
  choose x hx using fun j ↦ Submodule.Quotient.mk_surjective
    (Ip ^ n • ⊤ : Submodule B (dividedPowerDifferentials (A := A) hJ)) ((v j).val n)
  rw [completedMapDifferentialForms_val p A hJ _ _ _ i n _ _
      (completedIotaMulti_val p B _ i v n x fun j ↦ (hx j).symm),
    mapDifferentialFormsOfDPMorphism_ιMulti,
    completedIotaMulti_val p Bh _ i _ n (fun j ↦ mapDifferentialsOfDPMorphism (A := A) (J := J)
      (delta := hJ) (completionDividedPowers p hJ hp) (completionAlgHom p A)
      (isDPMorphism_completionAlgHom p A hJ hp) (x j))]
  intro j
  show adicQuotientMap _ _ n ((v j).val n) = _
  rw [← hx j]
  rfl

/-- **The inverse comparison is a left inverse.** -/
theorem completedFormsInv_completedFormsOfCompletionMap (i : ℕ)
    (x : completedDividedPowerForms p A hJ i) :
    completedFormsInv p A hJ hp i (completedFormsOfCompletionMap p A hJ hp i x) = x := by
  have hof : ∀ ω : dividedPowerDifferentialForms (A := A) hJ i,
      completedFormsInvAux p A hJ hp i (mapDifferentialFormsOfDPMorphism (A := A) (J := J)
        (delta := hJ) (completionDividedPowers p hJ hp) (completionAlgHom p A)
        (isDPMorphism_completionAlgHom p A hJ hp) i ω) = AdicCompletion.of Ip _ ω := by
    intro ω
    have hω : ω ∈ (⊤ : Submodule B (dividedPowerDifferentialForms (A := A) hJ i)) :=
      Submodule.mem_top
    rw [← exteriorPower.ιMulti_span] at hω
    induction hω using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      rw [mapDifferentialFormsOfDPMorphism_ιMulti, completedFormsInvAux_ιMulti]
      simp only [completedOneFormsEquiv_liftOne_map]
      exact completedIotaMulti_of p B _ i v
    | zero => rw [map_zero, map_zero, map_zero]
    | add y z _ _ hy hz => rw [map_add, map_add, hy, hz, map_add]
    | smul b y _ hy =>
      rw [map_smulₛₗ, map_smul, hy,
        show (completionAlgHom p A).toRingHom b = algebraMap B Bh b from rfl,
        algebraMap_smul, map_smul]
  refine adicCompletion_addMonoidHom_apply_eq_of_of p (x := x)
    (f := ((completedFormsInv p A hJ hp i).restrictScalars B ∘ₗ
      (completedFormsOfCompletionMap p A hJ hp i).restrictScalars B).toAddMonoidHom)
    (g := AddMonoidHom.id _) fun ω ↦ by
      simp only [LinearMap.toAddMonoidHom_coe, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.coe_restrictScalars, completedFormsOfCompletionMap_apply,
        completedMapDifferentialForms_of, completedFormsInv_of, AddMonoidHom.id_apply]
      exact hof ω

/-- **The inverse comparison is a right inverse.** -/
theorem completedFormsOfCompletionMap_completedFormsInv (i : ℕ)
    (z : completedDividedPowerForms p A (completionDividedPowers p hJ hp) i) :
    completedFormsOfCompletionMap p A hJ hp i (completedFormsInv p A hJ hp i z) = z := by
  have hof : (completedFormsOfCompletionMap p A hJ hp i) ∘ₗ completedFormsInvAux p A hJ hp i =
      (AdicCompletion.of Iph (dividedPowerDifferentialForms (A := A)
        (completionDividedPowers p hJ hp) i)) := by
    refine exteriorPower.linearMap_ext (AlternatingMap.ext fun w ↦ ?_)
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
      completedFormsInvAux_ιMulti, completedFormsOfCompletionMap_apply,
      completedMapDifferentialForms_completedIotaMulti, completedOneFormsMap_equiv_liftOne]
    exact completedIotaMulti_of p Bh _ i w
  refine adicCompletion_addMonoidHom_apply_eq_of_of p (x := z)
    (f := ((completedFormsOfCompletionMap p A hJ hp i) ∘ₗ
      completedFormsInv p A hJ hp i).toAddMonoidHom)
    (g := AddMonoidHom.id _) fun y ↦ by
      simp only [LinearMap.toAddMonoidHom_coe, LinearMap.coe_comp, Function.comp_apply,
        completedFormsInv_of, AddMonoidHom.id_apply]
      exact LinearMap.congr_fun hof y

/-- **The completed divided power forms of `B` and of its `p`-adic completion agree**:
`Ω̂ⁱ_B ≃ Ω̂ⁱ_{B̂}`, by the comparison along the divided power morphism `B → B̂`. -/
def completedFormsOfCompletionEquiv (i : ℕ) :
    completedDividedPowerForms p A hJ i ≃ₗ[Bh]
      completedDividedPowerForms p A (completionDividedPowers p hJ hp) i :=
  LinearEquiv.ofLinear (completedFormsOfCompletionMap p A hJ hp i) (completedFormsInv p A hJ hp i)
    (LinearMap.ext fun z ↦ completedFormsOfCompletionMap_completedFormsInv p A hJ hp i z)
    (LinearMap.ext fun x ↦ completedFormsInv_completedFormsOfCompletionMap p A hJ hp i x)

/-- The forward map of `completedFormsOfCompletionEquiv` is the comparison
`completedMapDifferentialForms` along the completion morphism `B → B̂`. -/
@[simp] theorem completedFormsOfCompletionEquiv_apply (i : ℕ)
    (x : completedDividedPowerForms p A hJ i) :
    completedFormsOfCompletionEquiv p A hJ hp i x =
      completedMapDifferentialForms p A hJ (completionDividedPowers p hJ hp)
        (completionAlgHom p A) (isDPMorphism_completionAlgHom p A hJ hp) i x :=
  rfl

/-- **The comparison carries the universal differential of `Ω̂¹_B` to that of `B̂` itself.** -/
theorem completedFormsOfCompletionEquiv_completedFormsDifferential (x : Bh) :
    completedFormsOfCompletionEquiv p A hJ hp 1 (completedFormsDifferential p A hJ x) =
      completedDividedPowerDifferentialOnRing p A (completionDividedPowers p hJ hp) x := by
  refine adicCompletion_addMonoidHom_apply_eq_of_of p (x := x)
    (f := (completedFormsOfCompletionEquiv p A hJ hp 1).toLinearMap.toAddMonoidHom.comp
      (PAdicCompletion.mapAddHom p B B (dividedPowerOneForm A hJ)))
    (g := (AdicCompletion.of Iph _).toAddMonoidHom.comp
      (dividedPowerOneForm A (completionDividedPowers p hJ hp)))
    fun b ↦ by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
        LinearEquiv.coe_coe]
      show completedFormsOfCompletionEquiv p A hJ hp 1
          (completedFormsDifferential p A hJ (AdicCompletion.of Ip B b)) = _
      rw [completedFormsOfCompletionEquiv_apply,
        completedMapDifferentialForms_completedFormsDifferential_of, completedFormsDifferential_of,
        completionAlgHom_apply]

end Equiv

/-! ### The comparison of completed forms along a morphism of completed rings -/

/-- The comparison of completed forms only depends on the algebra map. -/
theorem completedMapDifferentialForms_congr' (p : ℕ) (A : Type u) [CommRing A] {B : Type v}
    [CommRing B] [Algebra A B] {C : Type w} [CommRing C] [Algebra A C] {J : Ideal B}
    {K : Ideal C} (delta : DividedPowers J) (epsilon : DividedPowers K) {f g : B →ₐ[A] C}
    (h : f = g) (hf : IsDPMorphism delta epsilon f.toRingHom)
    (hg : IsDPMorphism delta epsilon g.toRingHom) (i : ℕ)
    (x : completedDividedPowerForms p A delta i) :
    completedMapDifferentialForms p A delta epsilon f hf i x =
      completedMapDifferentialForms p A delta epsilon g hg i x := by
  subst h
  rfl

section CompletedMap

variable (p : ℕ) (A : Type u) [CommRing A]
  {B₁ : Type v} [CommRing B₁] [Algebra A B₁] {J₁ : Ideal B₁} (h₁ : DividedPowers J₁)
  (hp₁ : IsNilpotent (Ideal.Quotient.mk J₁ (p : B₁)))
  {B₂ : Type w} [CommRing B₂] [Algebra A B₂] {J₂ : Ideal B₂} (h₂ : DividedPowers J₂)
  (hp₂ : IsNilpotent (Ideal.Quotient.mk J₂ (p : B₂)))
  (φ : AdicCompletion (pAdicIdeal (A := B₁) p) B₁ →ₐ[A] AdicCompletion (pAdicIdeal (A := B₂) p) B₂)
  (hφ : IsDPMorphism (completionDividedPowers p h₁ hp₁) (completionDividedPowers p h₂ hp₂)
    φ.toRingHom)

/-- **The comparison `Ω̂ⁱ_{B₁} → Ω̂ⁱ_{B₂}` along a divided power morphism `φ : B̂₁ → B̂₂` of the
completions.**  It is the comparison of the completed forms of the complete rings themselves,
read through `Crystalline.completedFormsOfCompletionEquiv` on both sides; for the completion of a
morphism of the uncompleted rings it is the comparison along that morphism
(`Crystalline.completedFormsMapOfCompletion_eq`). -/
def completedFormsMapOfCompletion (i : ℕ) :
    completedDividedPowerForms p A h₁ i →ₛₗ[φ.toRingHom] completedDividedPowerForms p A h₂ i :=
  ((completedFormsOfCompletionEquiv p A h₂ hp₂ i).symm.toLinearMap.comp
    (completedMapDifferentialForms p A (completionDividedPowers p h₁ hp₁)
      (completionDividedPowers p h₂ hp₂) φ hφ i)).comp
    (completedFormsOfCompletionEquiv p A h₁ hp₁ i).toLinearMap

/-- `completedFormsMapOfCompletion` is the comparison `completedMapDifferentialForms` along `φ`,
read through `completedFormsOfCompletionEquiv` on both sides. -/
theorem completedFormsMapOfCompletion_apply (i : ℕ) (x : completedDividedPowerForms p A h₁ i) :
    completedFormsMapOfCompletion p A h₁ hp₁ h₂ hp₂ φ hφ i x =
      (completedFormsOfCompletionEquiv p A h₂ hp₂ i).symm
        (completedMapDifferentialForms p A (completionDividedPowers p h₁ hp₁)
          (completionDividedPowers p h₂ hp₂) φ hφ i
          (completedFormsOfCompletionEquiv p A h₁ hp₁ i x)) :=
  rfl

/-- The comparison along `φ`, read on the forms of the complete rings. -/
theorem completedFormsOfCompletionEquiv_completedFormsMapOfCompletion (i : ℕ)
    (x : completedDividedPowerForms p A h₁ i) :
    completedFormsOfCompletionEquiv p A h₂ hp₂ i
        (completedFormsMapOfCompletion p A h₁ hp₁ h₂ hp₂ φ hφ i x) =
      completedMapDifferentialForms p A (completionDividedPowers p h₁ hp₁)
        (completionDividedPowers p h₂ hp₂) φ hφ i
        (completedFormsOfCompletionEquiv p A h₁ hp₁ i x) :=
  LinearEquiv.apply_symm_apply _ _

/-- **The comparison along the completion of a morphism of the uncompleted rings is the
comparison along that morphism.** -/
theorem completedFormsMapOfCompletion_eq (g : B₁ →ₐ[A] B₂) (hg : IsDPMorphism h₁ h₂ g.toRingHom)
    (hφg : ∀ b, φ (AdicCompletion.of _ B₁ b) = AdicCompletion.of _ B₂ (g b)) (i : ℕ)
    (x : completedDividedPowerForms p A h₁ i) :
    completedFormsMapOfCompletion p A h₁ hp₁ h₂ hp₂ φ hφ i x =
      completedMapDifferentialForms p A h₁ h₂ g hg i x := by
  rw [completedFormsMapOfCompletion_apply, LinearEquiv.symm_apply_eq,
    completedFormsOfCompletionEquiv_apply, completedFormsOfCompletionEquiv_apply,
    ← completedMapDifferentialForms_comp p A h₁ (completionDividedPowers p h₁ hp₁)
      (completionAlgHom p A) (isDPMorphism_completionAlgHom p A h₁ hp₁)
      (completionDividedPowers p h₂ hp₂) φ hφ
      (hφ.comp _ (isDPMorphism_completionAlgHom p A h₁ hp₁)),
    ← completedMapDifferentialForms_comp p A h₁ h₂ g hg (completionDividedPowers p h₂ hp₂)
      (completionAlgHom p A) (isDPMorphism_completionAlgHom p A h₂ hp₂)
      ((isDPMorphism_completionAlgHom p A h₂ hp₂).comp _ hg)]
  refine completedMapDifferentialForms_congr' p A h₁ _ (AlgHom.ext fun b ↦ ?_) _ _ i x
  rw [AlgHom.comp_apply, AlgHom.comp_apply, completionAlgHom_apply, completionAlgHom_apply, hφg]

/-- The comparison along `φ` respects the wedge product. -/
theorem completedFormsMapOfCompletion_wedge (i : ℕ) (x : completedDividedPowerForms p A h₁ i)
    (y : completedDividedPowerForms p A h₁ 1) :
    completedFormsMapOfCompletion p A h₁ hp₁ h₂ hp₂ φ hφ (i + 1)
        (completedDividedPowerWedge p A h₁ i x y) =
      completedDividedPowerWedge p A h₂ i
        (completedFormsMapOfCompletion p A h₁ hp₁ h₂ hp₂ φ hφ i x)
        (completedFormsMapOfCompletion p A h₁ hp₁ h₂ hp₂ φ hφ 1 y) := by
  refine (completedFormsOfCompletionEquiv p A h₂ hp₂ (i + 1)).injective ?_
  rw [completedFormsOfCompletionEquiv_completedFormsMapOfCompletion,
    completedFormsOfCompletionEquiv_apply, completedFormsOfCompletionEquiv_apply,
    completedMapDifferentialForms_wedge, completedMapDifferentialForms_wedge,
    completedMapDifferentialForms_wedge]
  rw [← completedFormsOfCompletionEquiv_apply, ← completedFormsOfCompletionEquiv_apply,
    ← completedFormsOfCompletionEquiv_completedFormsMapOfCompletion,
    ← completedFormsOfCompletionEquiv_completedFormsMapOfCompletion]
  rfl

/-- The comparison along `φ` respects the de Rham differential. -/
theorem completedFormsMapOfCompletion_deRham (i : ℕ) (x : completedDividedPowerForms p A h₁ i) :
    completedFormsMapOfCompletion p A h₁ hp₁ h₂ hp₂ φ hφ (i + 1)
        (completedDividedPowerDeRham p A h₁ i x) =
      completedDividedPowerDeRham p A h₂ i
        (completedFormsMapOfCompletion p A h₁ hp₁ h₂ hp₂ φ hφ i x) := by
  refine (completedFormsOfCompletionEquiv p A h₂ hp₂ (i + 1)).injective ?_
  rw [completedFormsOfCompletionEquiv_completedFormsMapOfCompletion,
    completedFormsOfCompletionEquiv_apply, completedFormsOfCompletionEquiv_apply,
    completedMapDifferentialForms_deRham, completedMapDifferentialForms_deRham,
    completedMapDifferentialForms_deRham]
  rw [← completedFormsOfCompletionEquiv_apply,
    ← completedFormsOfCompletionEquiv_completedFormsMapOfCompletion]
  rfl

/-- The comparison along `φ` carries `d x` to `d (φ x)`. -/
theorem completedFormsMapOfCompletion_differential
    (x : AdicCompletion (pAdicIdeal (A := B₁) p) B₁) :
    completedFormsMapOfCompletion p A h₁ hp₁ h₂ hp₂ φ hφ 1 (completedFormsDifferential p A h₁ x) =
      completedFormsDifferential p A h₂ (φ x) := by
  rw [completedFormsMapOfCompletion_apply, LinearEquiv.symm_apply_eq,
    completedFormsOfCompletionEquiv_completedFormsDifferential,
    completedFormsOfCompletionEquiv_completedFormsDifferential,
    completedMapDifferentialForms_differentialOnRing]

end CompletedMap

/-! ### Functoriality of the comparison along morphisms of completed rings -/

section CompletedMapComp

variable (p : ℕ) (A : Type u) [CommRing A]
  {B₁ : Type v} [CommRing B₁] [Algebra A B₁] {J₁ : Ideal B₁} (h₁ : DividedPowers J₁)
  (hp₁ : IsNilpotent (Ideal.Quotient.mk J₁ (p : B₁)))
  {B₂ : Type w} [CommRing B₂] [Algebra A B₂] {J₂ : Ideal B₂} (h₂ : DividedPowers J₂)
  (hp₂ : IsNilpotent (Ideal.Quotient.mk J₂ (p : B₂)))
  {B₃ : Type*} [CommRing B₃] [Algebra A B₃] {J₃ : Ideal B₃} (h₃ : DividedPowers J₃)
  (hp₃ : IsNilpotent (Ideal.Quotient.mk J₃ (p : B₃)))
  (φ : AdicCompletion (pAdicIdeal (A := B₁) p) B₁ →ₐ[A] AdicCompletion (pAdicIdeal (A := B₂) p) B₂)
  (hφ : IsDPMorphism (completionDividedPowers p h₁ hp₁) (completionDividedPowers p h₂ hp₂)
    φ.toRingHom)
  (ψ : AdicCompletion (pAdicIdeal (A := B₂) p) B₂ →ₐ[A] AdicCompletion (pAdicIdeal (A := B₃) p) B₃)
  (hψ : IsDPMorphism (completionDividedPowers p h₂ hp₂) (completionDividedPowers p h₃ hp₃)
    ψ.toRingHom)

/-- **The comparisons along morphisms of completed rings compose.** -/
theorem completedFormsMapOfCompletion_comp (hψφ : IsDPMorphism (completionDividedPowers p h₁ hp₁)
      (completionDividedPowers p h₃ hp₃) (ψ.comp φ).toRingHom) (i : ℕ)
    (x : completedDividedPowerForms p A h₁ i) :
    completedFormsMapOfCompletion p A h₂ hp₂ h₃ hp₃ ψ hψ i
        (completedFormsMapOfCompletion p A h₁ hp₁ h₂ hp₂ φ hφ i x) =
      completedFormsMapOfCompletion p A h₁ hp₁ h₃ hp₃ (ψ.comp φ) hψφ i x := by
  rw [completedFormsMapOfCompletion_apply, completedFormsMapOfCompletion_apply,
    completedFormsMapOfCompletion_apply, LinearEquiv.apply_symm_apply,
    completedMapDifferentialForms_comp p A (completionDividedPowers p h₁ hp₁)
      (completionDividedPowers p h₂ hp₂) φ hφ (completionDividedPowers p h₃ hp₃) ψ hψ hψφ]

/-- **The comparison along the identity is the identity.** -/
theorem completedFormsMapOfCompletion_id
    (hid : IsDPMorphism (completionDividedPowers p h₁ hp₁) (completionDividedPowers p h₁ hp₁)
      (AlgHom.id A _).toRingHom) (i : ℕ) (x : completedDividedPowerForms p A h₁ i) :
    completedFormsMapOfCompletion p A h₁ hp₁ h₁ hp₁ (AlgHom.id A _) hid i x = x := by
  rw [completedFormsMapOfCompletion_apply, completedMapDifferentialForms_id,
    LinearEquiv.symm_apply_apply]

end CompletedMapComp

end Crystalline

end
