module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import StacksFrontier.RingTheory.AdicCompletion.InverseLimit

/-!
# The `I`-adic completion as the limit of a tower of shifted quotients

Let `X` be an `A`-module, `I ⊆ A` an ideal and `(Pₙ, sₙ)` a tower of `A`-modules together with
surjections `rₙ : X ⟶ Pₙ`, compatible with the tower, whose kernels are the steps
`I^{N+n} X` of the `I`-adic filtration shifted by a fixed `N`.  Then

`X^∧ = lim_n Pₙ`,

the `I`-adic completion of `X` being read off the tower: `Pₙ = X / I^{N+n} X` and the shifted
filtration is cofinal with the unshifted one.

**This is the statement that replaces the interchange of a base change with a limit** in the
construction of the comparison datum of [Stacks, Lemma 60.17.3, Tag 07JG].  The uncompleted
interchange `(D ⊕ Ω) ⊗_D M ≅ lim_e ((D ⊕ Ω) ⊗_D M_e)` is false for `Ω` of infinite rank — the
support of a compatible family may grow with the level — while the completed one holds with no
finiteness at all, because a base change along *any* module turns a tower of shifted quotients
into another tower of shifted quotients.

## Main definitions

* `Crystalline.shiftedLevelQuot` — the map `X / I^{N+n} X ⟶ Pₙ` induced by `rₙ`, and
  `Crystalline.shiftedLevelEquiv` the linear equivalence it is.
* `Crystalline.completionLevel` — the level-`n` readout `X^∧ ⟶ Pₙ` of the completion.
* `Crystalline.completionLevelMap` — those readouts assembled into `X^∧ ⟶ lim_n Pₙ`, and
  `Crystalline.completionLevelEquiv` the linear equivalence it is.

## Main results

* `Crystalline.completionLevel_of` — on the image of `X` the readout is `rₙ`.
* `Crystalline.completionLevel_transition` — the readouts are compatible with the tower.
* `Crystalline.completionLevel_injective` — the readouts separate the points of `X^∧`.
* `Crystalline.completionLevelMap_bijective` — **the completion is the limit of the tower.**
* `Crystalline.completionLevel_map` — **the readouts are natural**: a linear map of the modules
  compatible with the two towers commutes with them.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 09B8](https://stacks.math.columbia.edu/tag/09B8)
-/

@[expose] public section

universe u w w'

namespace Crystalline

noncomputable section

section Levels

variable {A : Type u} [CommRing A] (I : Ideal A) (X : Type w) [AddCommGroup X] [Module A X]
  (P : ℕ → Type w) [∀ n, AddCommGroup (P n)] [∀ n, Module A (P n)]
  (s : ∀ n, P (n + 1) →ₗ[A] P n) (N : ℕ) (r : ∀ n, X →ₗ[A] P n)
  (hker : ∀ n, LinearMap.ker (r n) = I ^ (N + n) • (⊤ : Submodule A X))

/-- **The map `X / I^{N+n} X ⟶ Pₙ` induced by `rₙ`**, whose kernel is `I^{N+n} X`. -/
def shiftedLevelQuot (n : ℕ) :
    (X ⧸ (I ^ (N + n) • (⊤ : Submodule A X))) →ₗ[A] P n :=
  Submodule.liftQ _ (r n) (hker n).ge

/-- The induced map `X / I^{N+n} X ⟶ Pₙ` sends the class of `x` to `rₙ x`. -/
@[simp] theorem shiftedLevelQuot_mk (n : ℕ) (x : X) :
    shiftedLevelQuot I X P N r hker n (Submodule.Quotient.mk x) = r n x :=
  rfl

variable (hsurj : ∀ n, Function.Surjective (r n))

include hsurj in
/-- **The induced map `X / I^{N+n} X ⟶ Pₙ` is bijective**: surjective because `rₙ` is, injective
because the kernel of `rₙ` is the submodule divided out. -/
theorem shiftedLevelQuot_bijective (n : ℕ) :
    Function.Bijective (shiftedLevelQuot I X P N r hker n) := by
  refine ⟨?_, fun y ↦ ?_⟩
  · rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ (hker n).le
  · obtain ⟨x, rfl⟩ := hsurj n y
    exact ⟨Submodule.Quotient.mk x, rfl⟩

/-- The identification `X / I^{N+n} X ≅ Pₙ`. -/
def shiftedLevelEquiv (n : ℕ) :
    (X ⧸ (I ^ (N + n) • (⊤ : Submodule A X))) ≃ₗ[A] P n :=
  LinearEquiv.ofBijective _ (shiftedLevelQuot_bijective I X P N r hker hsurj n)

/-- The identification `X / I^{N+n} X ≅ Pₙ` is the induced map `Crystalline.shiftedLevelQuot`. -/
@[simp] theorem shiftedLevelEquiv_apply (n : ℕ)
    (z : X ⧸ (I ^ (N + n) • (⊤ : Submodule A X))) :
    shiftedLevelEquiv I X P N r hker hsurj n z = shiftedLevelQuot I X P N r hker n z :=
  rfl

/-! ### The level readout of the completion -/

/-- **The level-`n` readout of the `I`-adic completion of `X`**: evaluate at the level `N + n` of
the filtration and identify that quotient with `Pₙ`. -/
def completionLevel (n : ℕ) : AdicCompletion I X →ₗ[A] P n :=
  shiftedLevelQuot I X P N r hker n ∘ₗ AdicCompletion.eval I X (N + n)

/-- The level-`n` readout of `w` is the image under `Crystalline.shiftedLevelQuot` of the
component of `w` at level `N + n`. -/
@[simp] theorem completionLevel_apply (n : ℕ) (w : AdicCompletion I X) :
    completionLevel I X P N r hker n w =
      shiftedLevelQuot I X P N r hker n (w.val (N + n)) :=
  rfl

/-- On the image of `x : X` in the completion, the level-`n` readout is `rₙ x`. -/
@[simp] theorem completionLevel_of (n : ℕ) (x : X) :
    completionLevel I X P N r hker n (AdicCompletion.of I X x) = r n x :=
  rfl

variable (hcomp : ∀ n, s n ∘ₗ r (n + 1) = r n)

include hcomp in
/-- Descending one level of the filtration and identifying with `Pₙ` is identifying with
`P_{n+1}` and applying the transition map. -/
theorem comp_shiftedLevelQuot_succ (n : ℕ) :
    s n ∘ₗ shiftedLevelQuot I X P N r hker (n + 1) =
      shiftedLevelQuot I X P N r hker n ∘ₗ
        AdicCompletion.transitionMap I X (Nat.add_le_add_left n.le_succ N) := by
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ z
  change s n (r (n + 1) x) = shiftedLevelQuot I X P N r hker n (Submodule.Quotient.mk x)
  rw [shiftedLevelQuot_mk, ← LinearMap.comp_apply, hcomp n]

include hcomp in
/-- **The level readouts are compatible with the tower.** -/
theorem completionLevel_transition (n : ℕ) (w : AdicCompletion I X) :
    s n (completionLevel I X P N r hker (n + 1) w) =
      completionLevel I X P N r hker n w := by
  rw [completionLevel_apply, completionLevel_apply, ← LinearMap.comp_apply,
    comp_shiftedLevelQuot_succ I X P s N r hker hcomp n, LinearMap.comp_apply,
    AdicCompletion.transitionMap_comp_eval_apply]

include hsurj in
/-- **The level readouts separate the points of the completion.**  The readout at `n` determines
the evaluation at `N + n`, and the evaluations at the levels `N + n` determine all of them,
`n ≤ N + n`. -/
theorem completionLevel_injective {w w' : AdicCompletion I X}
    (h : ∀ n, completionLevel I X P N r hker n w = completionLevel I X P N r hker n w') :
    w = w' := by
  refine AdicCompletion.ext fun m ↦ ?_
  have hm : w.val (N + m) = w'.val (N + m) :=
    (shiftedLevelQuot_bijective I X P N r hker hsurj m).1 (h m)
  rw [← AdicCompletion.transitionMap_comp_eval_apply I X (Nat.le_add_left m N) w,
    ← AdicCompletion.transitionMap_comp_eval_apply I X (Nat.le_add_left m N) w', hm]

/-! ### The completion is the limit of the tower -/

include hcomp in
/-- **The level readouts assembled into a map to the limit of the tower.** -/
def completionLevelMap : AdicCompletion I X →ₗ[A] ↥(invLimit P s) :=
  LinearMap.codRestrict _ (LinearMap.pi fun n ↦ completionLevel I X P N r hker n)
    fun w n ↦ completionLevel_transition I X P s N r hker hcomp n w

/-- The component at level `n` of `Crystalline.completionLevelMap` is the level-`n` readout. -/
@[simp] theorem completionLevelMap_val (w : AdicCompletion I X) (n : ℕ) :
    (completionLevelMap I X P s N r hker hcomp w).val n =
      completionLevel I X P N r hker n w :=
  rfl

include hsurj hcomp in
/-- **The `I`-adic completion of `X` is the limit of the tower.**

Injectivity is `Crystalline.completionLevel_injective`.  For surjectivity a compatible family
`(yₙ)` is pulled back to the shifted quotients, `uₙ ∈ X / I^{N+n} X`; those classes are compatible
because the identifications are, and the family `m ↦ u_m` read at the *unshifted* level `m`, which
is the image of `u_m` under `X / I^{N+m} X ⟶ X / I^m X`, is a point of the completion whose
readouts are the `yₙ`. -/
theorem completionLevelMap_bijective :
    Function.Bijective (completionLevelMap I X P s N r hker hcomp) := by
  refine ⟨fun w w' hww ↦ completionLevel_injective I X P N r hker hsurj fun n ↦
      congrFun (congrArg Subtype.val hww) n, fun y ↦ ?_⟩
  set u : ∀ n, X ⧸ (I ^ (N + n) • (⊤ : Submodule A X)) := fun n ↦
    (shiftedLevelEquiv I X P N r hker hsurj n).symm (y.val n) with hu
  have hquot : ∀ n, shiftedLevelQuot I X P N r hker n (u n) = y.val n := fun n ↦
    (shiftedLevelEquiv I X P N r hker hsurj n).apply_symm_apply (y.val n)
  have hstep : ∀ n, AdicCompletion.transitionMap I X (Nat.add_le_add_left n.le_succ N)
      (u (n + 1)) = u n := by
    intro n
    refine (shiftedLevelQuot_bijective I X P N r hker hsurj n).1 ?_
    rw [← LinearMap.comp_apply, ← comp_shiftedLevelQuot_succ I X P s N r hker hcomp n,
      LinearMap.comp_apply, hquot, hquot]
    exact y.property n
  have hkey : ∀ (m m' : ℕ) (h : m ≤ m'),
      AdicCompletion.transitionMap I X (Nat.add_le_add_left h N) (u m') = u m := by
    intro m m' h
    induction m', h using Nat.le_induction with
    | base =>
        obtain ⟨x, hx⟩ := Submodule.mkQ_surjective (I ^ (N + m) • (⊤ : Submodule A X)) (u m)
        rw [← hx]
        rfl
    | succ m' h ih =>
        rw [← hstep m'] at ih
        rw [← ih]
        simp only [Submodule.factor_comp_apply]
  have hwc : ∀ {m m' : ℕ} (h : m ≤ m'),
      AdicCompletion.transitionMap I X h
          (AdicCompletion.transitionMap I X (Nat.le_add_left m' N) (u m')) =
        AdicCompletion.transitionMap I X (Nat.le_add_left m N) (u m) := by
    intro m m' h
    rw [← hkey m m' h]
    simp only [Submodule.factor_comp_apply]
  let W : AdicCompletion I X :=
    ⟨fun m ↦ AdicCompletion.transitionMap I X (Nat.le_add_left m N) (u m),
      fun {_ _} h ↦ hwc h⟩
  refine ⟨W, Subtype.ext (funext fun n ↦ ?_)⟩
  · rw [completionLevelMap_val, completionLevel_apply]
    change shiftedLevelQuot I X P N r hker n
      (AdicCompletion.transitionMap I X (Nat.le_add_left (N + n) N) (u (N + n))) = _
    rw [show AdicCompletion.transitionMap I X (Nat.le_add_left (N + n) N) (u (N + n)) = u n from
      hkey n (N + n) (Nat.le_add_left n N), hquot]

include hsurj hcomp in
/-- **The identification `X^∧ ≅ lim_n Pₙ`.** -/
def completionLevelEquiv : AdicCompletion I X ≃ₗ[A] ↥(invLimit P s) :=
  LinearEquiv.ofBijective _ (completionLevelMap_bijective I X P s N r hker hsurj hcomp)

/-- The component at level `n` of `Crystalline.completionLevelEquiv` is the level-`n`
readout. -/
@[simp] theorem completionLevelEquiv_val (w : AdicCompletion I X) (n : ℕ) :
    (completionLevelEquiv I X P s N r hker hsurj hcomp w).val n =
      completionLevel I X P N r hker n w :=
  rfl

end Levels

/-! ### Naturality of the level readout -/

section Naturality

variable {A : Type u} [CommRing A] (I : Ideal A) (X : Type w) [AddCommGroup X] [Module A X]
  (P : ℕ → Type w) [∀ n, AddCommGroup (P n)] [∀ n, Module A (P n)] (N : ℕ)
  (r : ∀ n, X →ₗ[A] P n)
  (hker : ∀ n, LinearMap.ker (r n) = I ^ (N + n) • (⊤ : Submodule A X))
  (X' : Type w') [AddCommGroup X'] [Module A X']
  (P' : ℕ → Type w') [∀ n, AddCommGroup (P' n)] [∀ n, Module A (P' n)]
  (r' : ∀ n, X' →ₗ[A] P' n)
  (hker' : ∀ n, LinearMap.ker (r' n) = I ^ (N + n) • (⊤ : Submodule A X'))

/-- **The level readout is natural.**  A linear map `φ : X ⟶ X'` carried by maps
`ψₙ : Pₙ ⟶ P'ₙ` of the towers commutes with the readouts of the completions. -/
theorem completionLevel_map (phi : X →ₗ[A] X') (psi : ∀ n, P n →ₗ[A] P' n)
    (hpsi : ∀ n, psi n ∘ₗ r n = r' n ∘ₗ phi) (n : ℕ) (w : AdicCompletion I X) :
    completionLevel I X' P' N r' hker' n (AdicCompletion.map I phi w) =
      psi n (completionLevel I X P N r hker n w) := by
  rw [completionLevel_apply, completionLevel_apply, AdicCompletion.map_val_apply]
  obtain ⟨x, hx⟩ := Submodule.mkQ_surjective (I ^ (N + n) • (⊤ : Submodule A X)) (w.val (N + n))
  rw [← hx]
  change shiftedLevelQuot I X' P' N r' hker' n (Submodule.Quotient.mk (phi x)) =
    psi n (shiftedLevelQuot I X P N r hker n (Submodule.Quotient.mk x))
  rw [shiftedLevelQuot_mk, shiftedLevelQuot_mk]
  exact (LinearMap.congr_fun (hpsi n) x).symm

end Naturality

end

end Crystalline

end
