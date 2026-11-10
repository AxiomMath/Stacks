module

public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.CompletionLevel
public import StacksFrontier.RingTheory.AdicCompletion.BaseChangeLevelwise
public import StacksFrontier.RingTheory.AdicCompletion.LevelMapBijective
public import StacksFrontier.RingTheory.DividedPowers.CompletionUniversalProperty

/-!
# The differentials of a ring and of its completion agree at every deep level

Let `A → B` be a ring map, let the ideal `J` of `B` carry divided powers `δ`, let `p` be nilpotent
modulo `J`, and write `B̂` for the `p`-adic completion of `B` with its divided powers `γ̂` of
[Stacks, Lemma 60.19.1, Tag 07KD].  The structure map `B → B̂` is a divided power morphism
(`DividedPowers.completionDPMorphism`), so it induces a comparison

`ν : Ω_{B/A,δ} ⟶ Ω_{B̂/A,γ̂}`

semilinear over `B → B̂`.  This file proves that `ν` is **bijective modulo `pᵏ`** for every `k`
beyond the cutoff of a comparison of [Stacks, Lemma 60.20.1, Tag 07KK].

The proof is a one-line consequence of the identification already available: the composite

`Ω_{B/A,δ} / pᵏ --ν--> Ω_{B̂/A,γ̂} / pᵏ --≃--> Ω̂_{B/A,δ} / pᵏ --≃--> Ω_{B/A,δ} / pᵏ`

of `ν` with `Crystalline.completedDifferentialsLevelEquiv` and with [Stacks, Tag 05GG] is the
identity.  Both the composite and the identity are `B`-linear and carry the class of `d b` to the
class of `d b` — the first because `ν (d b) = d (b mod pᵏ)` and the level identification carries
`d` to `d`, the second trivially — and the classes of the `d b` generate, so
`Crystalline.differentials_hom_ext` identifies them.  Since the two equivalences are bijective, so
is `ν` modulo `pᵏ`.

Why this is the statement wanted: `Crystalline.PAdicCompletion.bijective_mapAddHom_of_levelMap`
turns bijectivity at the deep levels into bijectivity of the `p`-adic completion of `ν`, and
`Crystalline.bijective_reduceModIdeal_exteriorPowerMap` and
`Crystalline.bijective_reduceModIdeal_lTensor` carry it up the exterior powers and across a tensor
factor.  That is what identifies the completed de Rham complex built from the differentials of `B̂`
with the one built from the differentials of `B`, in every degree, which is the form
[Stacks, Lemma 60.25.3, Tag 07N1] states its target in.

## Main definitions

* `Crystalline.completionDPAlgHom` — the structure map `B → B̂` as a morphism of `A`-algebras.
* `Crystalline.completionDifferentialsMap` — the comparison `ν : Ω_{B/A,δ} ⟶ Ω_{B̂/A,γ̂}`.

## Main results

* `Crystalline.completionDifferentialsMap_d` and `Crystalline.completionDifferentialsMap_smul` —
  the defining formula and the semilinearity of `ν`.
* `Crystalline.bijective_levelMap_completionDifferentialsMap` — `ν` is bijective modulo
  `p ^ (cutoff + e)`.
* `Crystalline.exists_bijective_levelMap_completionDifferentialsMap` — the same, stated with a
  cutoff.

## References

* [Stacks Project, Lemma 60.19.1, Tag 07KD](https://stacks.math.columbia.edu/tag/07KD)
* [Stacks Project, Lemma 60.20.1, Tag 07KK](https://stacks.math.columbia.edu/tag/07KK)
* [Stacks Project, Tag 05GG](https://stacks.math.columbia.edu/tag/05GG)
-/

@[expose] public section

open DividedPowers

open scoped TensorProduct

universe u v

namespace Crystalline

section Comparison

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (J : Ideal B) (delta : DividedPowers J) (p : ℕ)
  (hp : IsNilpotent (Ideal.Quotient.mk J (p : B)))

/-- The `p`-adic completion of `B` is an `A`-algebra through `B`. -/
instance instIsScalarTowerAdicCompletionCompletion :
    IsScalarTower A B (AdicCompletion (pAdicIdeal (A := B) p) B) :=
  IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [AdicCompletion.algebraMap_apply (S := A), AdicCompletion.algebraMap_apply (S := B)]
    simp

/-- The algebra map `B → B̂` is the canonical map of the completion. -/
theorem algebraMap_pAdicCompletion_eq_of (b : B) :
    algebraMap B (AdicCompletion (pAdicIdeal (A := B) p) B) b =
      AdicCompletion.of (pAdicIdeal (A := B) p) B b := by
  rw [AdicCompletion.algebraMap_apply (S := B)]
  simp

/-- **The structure map `B → B̂` as a morphism of `A`-algebras.** -/
noncomputable def completionDPAlgHom : B →ₐ[A] AdicCompletion (pAdicIdeal (A := B) p) B :=
  IsScalarTower.toAlgHom A B (AdicCompletion (pAdicIdeal (A := B) p) B)

/-- The map to the completion on an element. -/
@[simp]
theorem completionDPAlgHom_apply (b : B) :
    completionDPAlgHom (A := A) p b =
      AdicCompletion.of (pAdicIdeal (A := B) p) B b :=
  (AdicCompletion.algebraMap_apply (S := B) (pAdicIdeal (A := B) p) b).trans (by simp)

/-- The structure map `B → B̂` is a divided power morphism onto the completed divided powers. -/
theorem completionDPAlgHom_isDPMorphism :
    delta.IsDPMorphism (DividedPowers.completedDividedPowers J delta p hp).1
      (completionDPAlgHom (A := A) p).toRingHom :=
  (DividedPowers.completionDPMorphism J delta p hp).isDPMorphism

/-- **The comparison `ν : Ω_{B/A,δ} ⟶ Ω_{B̂/A,γ̂}`** induced by the structure map `B → B̂`. -/
noncomputable def completionDifferentialsMap :
    dividedPowerDifferentials (A := A) delta →+
      dividedPowerDifferentials (A := A)
        (DividedPowers.completedDividedPowers J delta p hp).1 :=
  mapDifferentialsOfDPMorphism (A := A) (J := J) (delta := delta)
    (DividedPowers.completedDividedPowers J delta p hp).1 (completionDPAlgHom (A := A) p)
    (completionDPAlgHom_isDPMorphism J delta p hp)

/-- `ν` carries `d b` to `d` of the image of `b`. -/
theorem completionDifferentialsMap_d (b : B) :
    completionDifferentialsMap (A := A) J delta p hp
        (dividedPowerDifferential (A := A) delta b) =
      dividedPowerDifferential (A := A)
        (DividedPowers.completedDividedPowers J delta p hp).1
        (AdicCompletion.of (pAdicIdeal (A := B) p) B b) := by
  rw [completionDifferentialsMap, mapDifferentialsOfDPMorphism_d,
    completionDPAlgHom_apply]

/-- `ν` is semilinear over the structure map `B → B̂`. -/
theorem completionDifferentialsMap_smul (b : B)
    (omega : dividedPowerDifferentials (A := A) delta) :
    completionDifferentialsMap (A := A) J delta p hp (b • omega) =
      AdicCompletion.of (pAdicIdeal (A := B) p) B b •
        completionDifferentialsMap (A := A) J delta p hp omega := by
  have h := mapDifferentialsOfDPMorphism_smul (A := A) (J := J) (delta := delta)
    (DividedPowers.completedDividedPowers J delta p hp).1 (completionDPAlgHom (A := A) p)
    (completionDPAlgHom_isDPMorphism J delta p hp) b omega
  rw [completionDifferentialsMap, h, completionDPAlgHom_apply]

end Comparison

section Levelwise

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (J : Ideal B) (delta : DividedPowers J) (p : ℕ)
  (hp : IsNilpotent (Ideal.Quotient.mk J (p : B)))

/-- **The comparison `ν` is bijective modulo `p ^ (cutoff + e)`.**  Composing it with
`Crystalline.completedDifferentialsLevelEquiv` and with [Stacks, Tag 05GG] gives a `B`-linear
endomorphism of `Ω_{B/A,δ} / pᵏ` fixing the classes of the universal differentials, hence the
identity; the two equivalences being bijective, so is `ν` modulo `pᵏ`. -/
theorem bijective_levelMap_completionDifferentialsMap
    (cmp : DifferentialsCompletionComparison (A := A) J delta p hp) (e : ℕ) :
    Function.Bijective (PAdicCompletion.levelMap p B
      (AdicCompletion (pAdicIdeal (A := B) p) B)
      (completionDifferentialsMap (A := A) J delta p hp)
      (cmp.quotientSystem.cutoff + e)) := by
  set k := cmp.quotientSystem.cutoff + e with hk
  -- the identification of the two shapes, followed by [Stacks, Tag 05GG]
  set G : completedDifferentialsModPow (A := A) J delta p hp k ≃+
      differentialsModPow (A := A) J delta p k :=
    (completedDifferentialsLevelEquiv (A := A) J delta p hp cmp e).trans
      (completionDifferentialsModPowEquiv (A := A) J delta p k).toAddEquiv with hG
  have hGapp : ∀ y, G y =
      (completionDifferentialsModPowEquiv (A := A) J delta p k)
        (completedDifferentialsLevelEquiv (A := A) J delta p hp cmp e y) := fun _ ↦ rfl
  have hGd : ∀ b : B, G (Submodule.Quotient.mk (dividedPowerDifferential (A := A)
        (DividedPowers.completedDividedPowers J delta p hp).1
        (AdicCompletion.of (pAdicIdeal (A := B) p) B b))) =
      Submodule.Quotient.mk (dividedPowerDifferential (A := A) delta b) := fun b ↦ by
    rw [hGapp, completedDifferentialsLevelEquiv_d, completionDifferentialsModPowEquiv_mk_of]
  have hGsmul : ∀ (b : B) (y : completedDifferentialsModPow (A := A) J delta p hp k),
      G (AdicCompletion.of (pAdicIdeal (A := B) p) B b • y) = b • G y := fun b y ↦ by
    rw [hGapp, completedDifferentialsLevelEquiv_smul, ← algebraMap_pAdicCompletion_eq_of p b,
      IsScalarTower.algebraMap_smul (AdicCompletion (pAdicIdeal (A := B) p) B), map_smul]
    rfl
  -- the composite with `ν` is the identity
  have hid : ∀ omega : dividedPowerDifferentials (A := A) delta,
      G (PAdicCompletion.levelMap p B (AdicCompletion (pAdicIdeal (A := B) p) B)
          (completionDifferentialsMap (A := A) J delta p hp) k
          (Submodule.Quotient.mk omega)) =
        Submodule.Quotient.mk omega := by
    intro omega
    have hx : omega ∈ Submodule.span B
        (Set.range (dividedPowerDifferential (A := A) delta)) := by
      rw [dividedPowerDifferentials_span (A := A) delta]
      trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      rw [PAdicCompletion.levelMap_mk, completionDifferentialsMap_d]
      exact hGd b
    | zero => simp
    | add x y _ _ ex ey =>
      rw [Submodule.Quotient.mk_add, map_add, map_add, ex, ey]
    | smul b x _ ex =>
      rw [PAdicCompletion.levelMap_mk] at ex
      rw [PAdicCompletion.levelMap_mk, completionDifferentialsMap_smul,
        Submodule.Quotient.mk_smul, hGsmul, ex, Submodule.Quotient.mk_smul]
  have hid' : ∀ y, G (PAdicCompletion.levelMap p B
      (AdicCompletion (pAdicIdeal (A := B) p) B)
      (completionDifferentialsMap (A := A) J delta p hp) k y) = y := by
    intro y
    induction y using Submodule.Quotient.induction_on with
    | _ omega => exact hid omega
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ⟨G y, G.injective (hid' (G y))⟩⟩
  rw [← hid' x, ← hid' y, hxy]

/-- **The comparison `ν` is bijective at all levels beyond a cutoff.** -/
theorem exists_bijective_levelMap_completionDifferentialsMap [Fact p.Prime]
    [Algebra (DividedPowers.IntegersAtPrime p) A] :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Function.Bijective (PAdicCompletion.levelMap p B
        (AdicCompletion (pAdicIdeal (A := B) p) B)
        (completionDifferentialsMap (A := A) J delta p hp) n) := by
  let cmp := dividedPowerDifferentialsCompletionComparison (A := A) J delta p hp
  refine ⟨cmp.quotientSystem.cutoff, fun n hn ↦ ?_⟩
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact bijective_levelMap_completionDifferentialsMap J delta p hp cmp e

end Levelwise

/-! ### The comparison as a map out of the base change -/

section BaseChange

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (J : Ideal B) (delta : DividedPowers J) (p : ℕ)
  (hp : IsNilpotent (Ideal.Quotient.mk J (p : B)))

/-- **The comparison `ν` read as a `B̂`-linear map out of the base change** `B̂ ⊗_B Ω_{B/A,δ}`.

To lift `ν` across the base change one reads `Ω_{B̂/A,γ̂}` as a `B`-module through the structure
map `B → B̂`, in which reading `ν` is `B`-linear by
`Crystalline.completionDifferentialsMap_smul`.  That module structure is local to the
construction: it is not part of the resulting map's type, which is `B̂`-linear. -/
noncomputable def completionDifferentialsBaseChange :
    AdicCompletion (pAdicIdeal (A := B) p) B ⊗[B] (dividedPowerDifferentials (A := A) delta)
      →ₗ[AdicCompletion (pAdicIdeal (A := B) p) B]
        dividedPowerDifferentials (A := A)
          (DividedPowers.completedDividedPowers J delta p hp).1 :=
  letI mb : Module B (dividedPowerDifferentials (A := A)
      (DividedPowers.completedDividedPowers J delta p hp).1) :=
    Module.compHom _ (algebraMap B (AdicCompletion (pAdicIdeal (A := B) p) B))
  letI mt : IsScalarTower B (AdicCompletion (pAdicIdeal (A := B) p) B)
      (dividedPowerDifferentials (A := A)
        (DividedPowers.completedDividedPowers J delta p hp).1) :=
    ⟨fun b c z ↦ by
      rw [Algebra.smul_def b c, mul_smul]
      rfl⟩
  @LinearMap.liftBaseChange B (dividedPowerDifferentials (A := A) delta)
    (dividedPowerDifferentials (A := A)
      (DividedPowers.completedDividedPowers J delta p hp).1)
    (AdicCompletion (pAdicIdeal (A := B) p) B) _ _ _ _ _ _ mb _ mt
    { toFun := completionDifferentialsMap (A := A) J delta p hp
      map_add' := (completionDifferentialsMap (A := A) J delta p hp).map_add
      map_smul' := fun b omega ↦ by
        rw [RingHom.id_apply]
        exact (completionDifferentialsMap_smul J delta p hp b omega).trans
          (congrArg (fun c ↦ c • completionDifferentialsMap (A := A) J delta p hp omega)
            (algebraMap_pAdicCompletion_eq_of p b)).symm }

/-- The comparison out of the base change on a pure tensor. -/
@[simp]
theorem completionDifferentialsBaseChange_tmul
    (c : AdicCompletion (pAdicIdeal (A := B) p) B)
    (omega : dividedPowerDifferentials (A := A) delta) :
    completionDifferentialsBaseChange (A := A) J delta p hp (c ⊗ₜ[B] omega) =
      c • completionDifferentialsMap (A := A) J delta p hp omega :=
  rfl

/-- Composing the base-changed comparison with the unit of the base change gives `ν` back. -/
theorem completionDifferentialsBaseChange_comp_tensorUnit :
    (completionDifferentialsBaseChange (A := A) J delta p hp).toAddMonoidHom.comp
        (tensorUnit (pAdicIdeal (A := B) p)
          (X := dividedPowerDifferentials (A := A) delta)).toAddMonoidHom =
      completionDifferentialsMap (A := A) J delta p hp := by
  refine AddMonoidHom.ext fun omega ↦ ?_
  change completionDifferentialsBaseChange (A := A) J delta p hp
    (tensorUnit (pAdicIdeal (A := B) p) omega) = _
  rw [tensorUnit_apply, completionDifferentialsBaseChange_tmul, one_smul]

/-- **The base-changed comparison is bijective modulo `pⁿ` at every deep level.**  The unit of the
base change is bijective at every level (`Crystalline.bijective_reduceModIdeal_tensorUnit`) and so
is the composite, which is `ν`; cancelling the unit gives the statement. -/
theorem bijective_levelMap_completionDifferentialsBaseChange [Fact p.Prime]
    [Algebra (DividedPowers.IntegersAtPrime p) A] :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Function.Bijective (PAdicCompletion.levelMap p
        (AdicCompletion (pAdicIdeal (A := B) p) B)
        (AdicCompletion (pAdicIdeal (A := B) p) B)
        (completionDifferentialsBaseChange (A := A) J delta p hp).toAddMonoidHom n) := by
  obtain ⟨N, hN⟩ := exists_bijective_levelMap_completionDifferentialsMap (A := A) J delta p hp
  refine ⟨N, fun n hn ↦ ?_⟩
  have hunit : Function.Bijective (PAdicCompletion.levelMap p B
      (AdicCompletion (pAdicIdeal (A := B) p) B)
      (tensorUnit (pAdicIdeal (A := B) p)
        (X := dividedPowerDifferentials (A := A) delta)).toAddMonoidHom n) :=
    PAdicCompletion.bijective_levelMap_of_reduceModIdeal p B _ n
      (bijective_reduceModIdeal_tensorUnit (pAdicIdeal (A := B) p)
        (Submodule.fg_span_singleton _) n) _
  have hcomp : Function.Bijective (PAdicCompletion.levelMap p B
      (AdicCompletion (pAdicIdeal (A := B) p) B)
      ((completionDifferentialsBaseChange (A := A) J delta p hp).toAddMonoidHom.comp
        (tensorUnit (pAdicIdeal (A := B) p)
          (X := dividedPowerDifferentials (A := A) delta)).toAddMonoidHom) n) := by
    rw [completionDifferentialsBaseChange_comp_tensorUnit]
    exact hN n hn
  exact PAdicCompletion.bijective_levelMap_of_comp_left p B
    (AdicCompletion (pAdicIdeal (A := B) p) B)
    (AdicCompletion (pAdicIdeal (A := B) p) B) _ _ n hunit hcomp

end BaseChange

end Crystalline

end
