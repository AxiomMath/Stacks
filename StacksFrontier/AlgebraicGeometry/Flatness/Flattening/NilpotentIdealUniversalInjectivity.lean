module

public import Mathlib.RingTheory.Flat.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.MaximalIdealInjectivity
public import StacksFrontier.RingTheory.Flat.UniversallyInjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Universal injectivity from universal injectivity modulo a nilpotent ideal

Let `f : M → M'` be a map of modules over a commutative ring `R` with `M'` flat, and let
`I ⊆ R` be a nilpotent ideal. If `f ⊗ id_P` is injective for every `R`-module `P` killed by
`I`, then `f` is universally injective.

This is the last paragraph of the proof of Stacks 05U9, which reduces universal injectivity of
the map of Situation 0AT0 to universal injectivity of its reduction modulo a finitely generated
nilpotent ideal `I₀ ⊆ A` ("in a similar way the universal injectivity of `u` can be reduced
(even without proving flatness of `N` first) to the one modulo `I₀`"). The reduction is proved
here in full; what is left of Stacks 05U9 is the production of `I₀` together with universal
injectivity modulo `I₀`, which in the source rests on Claim 1 and Claim 2 of that proof and
hence on Stacks 05PG, 0ASY, 0ATC, 0AT8 and 05U7.

## Main definitions

No new definitions are introduced.

## Main results

* `Module.Flat.rTensor_injective_of_annihilated_pow`: if `f ⊗ id_P` is injective for every
  module `P` killed by `I`, then it is injective for every module killed by `I ^ n`.
* `Module.Flat.universallyInjectivePoly_of_annihilated_of_isNilpotent`: the same hypothesis for
  a nilpotent `I` gives universal injectivity of `f`.
* `AlgebraicGeometry.universallyInjective_of_annihilated_of_isNilpotent`: the conclusion of
  Stacks 05U9 on universal injectivity, in Situation 0AT0, granted universal injectivity
  modulo some nilpotent ideal of the base.
* `AlgebraicGeometry.universallyInjective_of_isNoetherianRing'` discharges that hypothesis over
  a Noetherian base with `I = ⊥`, so the hypothesis is reachable and the statement reproves the
  universal-injectivity clause of Stacks 0AT1.

## Implementation notes

"`P` is killed by `I`" is spelled pointwise as `∀ a ∈ I, ∀ x : P, a • x = 0`, which is
`I • (⊤ : Submodule R P) = ⊥` (`Submodule.smul_top_eq_bot_iff`) and says exactly that the
`R`-module `P` is an `R ⧸ I`-module. So the hypothesis of the main results is universal
injectivity of the reduction `M/IM → M'/IM'` over `R ⧸ I`, read through the identification
`M ⊗[R] P = (M/IM) ⊗[R ⧸ I] P` for such `P`; the pointwise form avoids transporting the
tensor products across that identification.

The induction over `n` runs along the filtration of a module `Q` killed by `I ^ (n + 1)` by
`K = I • ⊤`, whose subobject is killed by `I ^ n` and whose quotient is killed by `I`.  The
step is a four-lemma chase in the diagram with rows `M ⊗ K → M ⊗ Q → M ⊗ Q/K` and
`M' ⊗ K → M' ⊗ Q → M' ⊗ Q/K`: the top row is exact at `M ⊗ Q` by right exactness of the tensor
product, and flatness of `M'` is used once, for injectivity of `M' ⊗ K → M' ⊗ Q`. Flatness of
`M` is not assumed and would not help: the injectivity that is needed is the one on the flat
side.

The test module `P` of the hypothesis and the test module of the conclusion live in the same
universe, which is the universe-polymorphic `UniversallyInjectivePoly`'s free universe; the
hypothesis is therefore not required in universes other than the one in which the conclusion is
being used.

## References

* [Stacks Project, Tag 0AT0](https://stacks.math.columbia.edu/tag/0AT0)
* [Stacks Project, Tag 05U9](https://stacks.math.columbia.edu/tag/05U9)
-/

@[expose] public section

universe u₁ u₂ u₃ u₄ u₅

open TensorProduct

/-- A module is killed by an ideal exactly when the ideal's action on it is pointwise zero. -/
theorem Submodule.smul_top_eq_bot_iff {R : Type*} [CommRing R] (I : Ideal R) (P : Type*)
    [AddCommGroup P] [Module R P] :
    I • (⊤ : Submodule R P) = ⊥ ↔ ∀ a ∈ I, ∀ x : P, a • x = 0 :=
  ⟨fun h _ ha _ => (Submodule.mem_bot R).mp (h ▸ Submodule.smul_mem_smul ha Submodule.mem_top),
    fun h => le_bot_iff.mp <| Submodule.smul_le.mpr fun a ha x _ =>
      (Submodule.mem_bot R).mpr (h a ha x)⟩

namespace Module.Flat

/-- If `f ⊗ id_P` is injective for every module `P` killed by the ideal `I`, and the flat side
`M'` of `f` is flat, then `f ⊗ id_Q` is injective for every module `Q` killed by `I ^ n`.

The induction is along the filtration of `Q` by the submodules `I ^ k • ⊤`; the step is the
four lemma applied to `0 → I • ⊤ → Q → Q/(I • ⊤) → 0` tensored with `f`. -/
@[sga "1 IV 5.3" "(i) ⇒ (iii)"]
theorem rTensor_injective_of_annihilated_pow {R : Type u₁} [CommRing R]
    {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [Module.Flat R M'] (f : M →ₗ[R] M') (I : Ideal R)
    (hkill : ∀ (P : Type u₅) [AddCommGroup P] [Module R P],
      (∀ a ∈ I, ∀ x : P, a • x = 0) → Function.Injective (f.rTensor P))
    (n : ℕ) {Q : Type u₅} [AddCommGroup Q] [Module R Q]
    (hn : ∀ a ∈ I ^ n, ∀ x : Q, a • x = 0) :
    Function.Injective (f.rTensor Q) := by
  induction n generalizing Q with
  | zero =>
    have hzero : ∀ x : Q, x = 0 := fun x => by simpa using hn 1 (by simp) x
    have : Subsingleton Q := ⟨fun x y => (hzero x).trans (hzero y).symm⟩
    exact Function.injective_of_subsingleton _
  | succ n ih =>
    let K : Submodule R Q := I • ⊤
    have hK : ∀ a ∈ I ^ n, ∀ x : K, a • x = 0 := by
      intro a ha x
      refine Subtype.ext ?_
      change a • (x : Q) = 0
      refine Submodule.smul_induction_on x.2 ?_ ?_
      · intro b hb y _
        rw [smul_smul]
        exact hn (a * b) (by rw [pow_succ]; exact Ideal.mul_mem_mul ha hb) y
      · intro y z hy hz
        rw [smul_add, hy, hz, add_zero]
    have hquot : Function.Injective (f.rTensor (Q ⧸ K)) := by
      refine hkill _ fun a ha x => ?_
      obtain ⟨y, rfl⟩ := K.mkQ_surjective x
      change K.mkQ (a • y) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul ha Submodule.mem_top
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hx₂ : LinearMap.lTensor M K.mkQ x = 0 := by
      refine (injective_iff_map_eq_zero _).mp hquot _ ?_
      rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
        ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, hx, map_zero]
    obtain ⟨y, rfl⟩ := (_root_.lTensor_exact M (LinearMap.exact_subtype_mkQ K)
      (Submodule.mkQ_surjective _) x).mp hx₂
    have hy : f.rTensor K y = 0 := by
      refine (injective_iff_map_eq_zero _).mp
        (Module.Flat.lTensor_preserves_injective_linearMap (M := M') K.subtype
          K.injective_subtype) _ ?_
      rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
        ← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply, hx]
    rw [(injective_iff_map_eq_zero _).mp (ih hK) y hy, map_zero]

/-- **Universal injectivity modulo a nilpotent ideal.** Let `f : M →ₗ[R] M'` with `M'` flat and
let `I ⊆ R` be a nilpotent ideal. If `f ⊗ id_P` is injective for every `R`-module `P` killed by
`I`, then `f` is universally injective.

This is the reduction step that closes the proof of Stacks 05U9. -/
@[ega "IV 11.9.15" "special case"]
theorem universallyInjectivePoly_of_annihilated_of_isNilpotent {R : Type u₁} [CommRing R]
    {M M' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [Module.Flat R M'] (f : M →ₗ[R] M') {I : Ideal R} (hI : IsNilpotent I)
    (hkill : ∀ (P : Type u₅) [AddCommGroup P] [Module R P],
      (∀ a ∈ I, ∀ x : P, a • x = 0) → Function.Injective (f.rTensor P)) :
    UniversallyInjectivePoly.{_, u₅} f := by
  obtain ⟨n, hn⟩ := hI
  intro Q _ _
  refine rTensor_injective_of_annihilated_pow f I hkill n fun a ha x => ?_
  rw [hn] at ha
  rw [show a = 0 by simpa using ha, zero_smul]

end Module.Flat

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 05U9 (universal injectivity), granted the nilpotent-ideal case.**
In Situation 0AT0 — a local homomorphism `A → B` of local rings essentially of finite type, a
flat `A`-module `M`, a finite `B`-module `N` and an `A`-linear `u : N → M` injective modulo the
maximal ideal of `A` — the map `u` is `A`-universally injective as soon as there is a nilpotent
ideal `I ⊆ A` such that `u` is universally injective modulo `I`, that is, such that `u ⊗ id_P`
is injective for every `A`-module `P` killed by `I`.

The hypothesis is the conclusion of the first two thirds of the proof of Stacks 05U9 (Claim 1
and Claim 2 there, fed into Stacks 0AT9); this statement is its last paragraph. It is
dischargeable: `universallyInjective_of_isNoetherianRing'` discharges it with `I = ⊥` over a
Noetherian base. -/
theorem universallyInjective_of_annihilated_of_isNilpotent
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    {I : Ideal S.A} (hI : IsNilpotent I)
    (hmod : ∀ (P : Type u₅) [AddCommGroup P] [Module S.A P],
      (∀ a ∈ I, ∀ x : P, a • x = 0) → Function.Injective (S.u.rTensor P)) :
    UniversallyInjectivePoly.{_, u₅} S.u :=
  Module.Flat.universallyInjectivePoly_of_annihilated_of_isNilpotent S.u hI hmod

/-- The hypothesis of `universallyInjective_of_annihilated_of_isNilpotent` is reachable: over a
Noetherian base it holds with `I = ⊥`, by the universal-injectivity clause of Stacks 0AT1, and
the reduction then reproves that clause. -/
theorem universallyInjective_of_isNoetherianRing'
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄}) [IsNoetherianRing S.A] :
    UniversallyInjectivePoly.{_, u₅} S.u :=
  universallyInjective_of_annihilated_of_isNilpotent S (I := ⊥) ⟨1, by simp⟩
    fun P _ _ _ => universallyInjective_of_isNoetherianRing S P

end AlgebraicGeometry

end
