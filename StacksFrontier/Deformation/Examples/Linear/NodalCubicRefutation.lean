module

public import StacksFrontier.Deformation.FlatAlgebraLiftCompletion
public import StacksFrontier.Deformation.Examples.Linear.NodalCubicNoLift

/-!
# Stacks 0DZ2 is false

We instantiate `Deformation.FlatModuleLiftBaseChangeStatement` at an explicit counterexample,
check every hypothesis of Stacks 0DZ2 for it, and derive a contradiction.

`NC = 𝔽₂[Y, Z]/(Z² + Y·Z + Y³)` the affine nodal cubic, `ω = Y`,
`A' = NC[t]/t³`, `A = NC`, `P' = A'[x]/(x² − t·x − t²·Y)`, `P = P'/t·P'`,
`Q₁ = P'[z]/(z² + z − Y)`, `Q' = (Q₁)_{z+1}`, `Q = Q'/t·Q'`,
`M = NC` with its `P`-structure through the map killing `x`, `J' = Y·P'`.

## The hypotheses of 0DZ2

| 0DZ2 hypothesis | discharged by |
|---|---|
| Noetherian ×6 | automatic (`AdjoinRoot`/`Ideal.Quotient`/`Localization` composing) |
| `A' → A` surj., nilpotent kernel | `redA_surjective`, `ker_redA`, `isNilpotent_ker_redA` |
| `P' → P` surj., `hkerP` | `surjective_PBase_PRed`, `ker_PBase_PRed_eq_map` |
| `Q' → Q` surj., `hkerQ` | `surjective_QBase_QRed`, `ker_QBase_QRed_eq_map` |
| `Flat A' P'` | `flat_PBase` |
| `Flat P' Q'` | `flat_QBase_PBase` |
| `Flat A' Q'` | `flat_QBase_ABase` |
| `Flat P Q` | `flat_QRed_PRed`, via `Q = P ⊗_{P'} Q'` |
| towers ×7 | 5 automatic; `isScalarTower_NC_PRed_QRed`, `algebraMap_ABase_PRed_eq` |
| `IsScalarTower A P M` | `isScalarTower_NC_PRed_NC` |
| `Module.Finite P M` | `finite_NC` |
| `Module.Flat A M` | `flat_NC_NC` (self-flatness) |
| `hquot` | `bijective_quotientMap_omegaP` |
| `hlocal` | `hlocal_nodal` |
| `hN` | free: `N := Q/(x)·Q`, identified with `Q ⊗_P M` by `ncTensorComparison` |
| conclusion fails | `flat_QLift` lifts, `not_flat_lift_of_reduction` does not |

`hquot` is proved through `map_span_omegaP`, `qOneToQuotOmega` and `ker_qOneToQuotOmega`;
`hlocal` through `exists_isASSol_away`, `pBaseToAY` and `flat_LocalModule`.

## Implementation notes

* For `hlocal`, the local lift is `L_g = (P')_g ⧸ (Y·x − t·Z)`. Adjoining the Artin–Schreier
  root, as on the `Q'` side, would give a module free of rank two over `A'`, while `M_g` is free
  of rank one: on the local side `Y` is a unit and the root `Z/Y` is already present.
* Presenting both `L_g` and `M` as quotients makes
  `Algebra.TensorProduct.quotIdealMapEquivTensorQuot` — linear over the left factor, which is the
  linearity the statement asks for — reduce the comparison to an identity of two ideals.
* **`M` is finite and cyclic** (`finite_NC`, from surjectivity of `P → M`). So this refutes
  `FlatModuleLiftBaseChangeStatement`, which is 0DZ2 *with* `Module.Finite P M` added, and not
  merely the unrestricted tag.
* **`I³ = 0` with `I² ≠ 0`** for `I = ker(A' → A) = (t)` in `A' = NC[t]/t³`. The instance
  therefore sits exactly where the square-zero form of 0DZ2
  (`StacksFrontier.Deformation.FlatModuleLiftBaseChange`) stops applying, and contradicts nothing
  proved there. `I² ≠ 0` is what `cst_add_tau_eq_zero_iff` records: `1, t, t²` is an `NC`-basis
  of `A'`.
* **Six Noetherian hypotheses and five of the seven scalar towers resolve automatically**, from
  `AdjoinRoot`, `Ideal.Quotient` and `Localization` composing. Of the seven, the two that are
  proved are `IsScalarTower A P Q` and `IsScalarTower A' A P`; the latter needs the basis
  `1, t, t²` of `A'` because `A' → A` is not a quotient map that Mathlib's instances recognise.
  The tower `IsScalarTower A P M` in the module block is `isScalarTower_NC_PRed_NC`.

## Why the statement fails

With `A' = 𝔽₂[t]/t³`, the nodal ring `R = {f ∈ 𝔽₂[s] : f(0) = f(1)}` and
`ω = s² + s`, the finite cyclic module `M = P/(x)` over `P = R[x]/(x²)` has no `A'`-flat lift to
`P' = R[t, x]/(t³, x² − t·x − t²·ω)`, because liftability there is exactly solvability of the
Artin–Schreier equation `α² − α = ω`, and `ω` is not an Artin–Schreier value of `R`. Yet `M` does
lift after inverting every `g` of `J' = ω·P'`, and it lifts over the `Q'` built from the étale
cover `R[z]/(z² + z − ω)`. So both sides of 0DZ2's biconditional are determined and they
disagree, and the finiteness restriction that `FlatModuleLiftBaseChangeStatement` adds does not
save the statement, because `M` is finite and cyclic.

## Universe scope

The term below refutes `Deformation.FlatModuleLiftBaseChangeStatement.{0}`, because the
counterexample's rings are built from `ZMod 2` and so live in `Type`. The statement is false at
*every* universe, and that is also proved:
`Deformation.Examples.ArtinSchreier.not_flatModuleLiftBaseChangeStatement_ulift` of
`StacksFrontier.Deformation.Examples.Linear.NodalCubicRefutationUniverse` instantiates 0DZ2 at the
`ULift`s of these six rings and derives the contradiction there.

Transporting the statement itself, `Statement.{u} → Statement.{0}`, is obstructed: the
conclusion of 0DZ2 is an existential over a module in `Type u`, and nothing in 0DZ2's hypotheses
makes such a module the `ULift` of a `Type 0` one — that would need the lift to be finitely
generated over `P'`, i.e. Nakayama. What is transported is the counterexample, and the
contradiction is taken upstairs, which is possible only because `not_flat_lift_of_reduction` is
stated in terms of a bare reduction function `M' → NC` and is therefore already polymorphic in
the lift's type.

## Main results

* `Deformation.Examples.ArtinSchreier.exists_flat_lift_QLift`: **clause (2) of 0DZ2 holds** for
  the counterexample — `N = Q ⊗_P M` has the `A'`-flat `Q'`-module lift `QLift`.
* `Deformation.Examples.ArtinSchreier.not_lift_of_tensorEquiv`: **clause (1) of 0DZ2 fails**,
  for a lift in *any* universe. Together with the previous item this is the refutation of the
  source's biconditional, with no universe caveat attached to either half.
* `Deformation.Examples.ArtinSchreier.not_flatModuleLiftBaseChangeStatement`:
  **`¬ Deformation.FlatModuleLiftBaseChangeStatement.{0}`.** The universe-general form is
  `Deformation.Examples.ArtinSchreier.not_flatModuleLiftBaseChangeStatement_ulift` of
  `StacksFrontier.Deformation.Examples.Linear.NodalCubicRefutationUniverse`; the form at the
  statement carrying the source's `Module.Flat A P` as well is
  `Deformation.Examples.ArtinSchreier.not_flatModuleLiftBaseChangeStatementFaithful` of
  `StacksFrontier.Deformation.Examples.Linear.NodalCubicRefutationFaithful`.

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
-/

@[expose] public noncomputable section

open Polynomial
open Deformation.Examples.MaurerCartanWindow
open scoped TensorProduct

universe u

namespace Deformation.Examples.ArtinSchreier

/-! ### The tower `A' → A → P` -/

/-- **`IsScalarTower A' A P`**, one of the two towers of Stacks 0DZ2 that are not automatic. It
needs the basis `1, t, t²` of `A' = NC[t]/t³`: `t` dies in `P = P'/t·P'`, so only the
constant coefficient survives, and that is exactly `redA`. -/
theorem algebraMap_ABase_PRed_eq (a : ABase) :
    algebraMap ABase PRed a = algebraMap NC PRed (redA a) := by
  obtain ⟨b, c, d, rfl⟩ := exists_cst_add_tau (R := NC) a
  have htau : algebraMap ABase PRed (tau NC) = 0 := by
    rw [IsScalarTower.algebraMap_apply ABase PBase PRed]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have hred : redA (cst NC b + tau NC * cst NC c + tau NC * tau NC * cst NC d) = b := by
    simp
  rw [hred]
  simp only [map_add, map_mul, htau, zero_mul, mul_zero, add_zero]
  rw [← algebraMap_NC_ABase b, ← IsScalarTower.algebraMap_apply NC ABase PRed]

/-! ### The two comparison equivalences, with their types inferred -/

/-- `Q/(x)·Q ≅ Q ⊗_P M`, the identification that makes `hN` free. Its type is left inferred for
the reason `qRedComparison` records: the `Algebra.toModule` instance path is the one
`Deformation.FlatModuleLiftBaseChangeStatement` can use, and writing `QRed ⊗[PRed] NC` out loud
picks the other one. -/
def ncTensorComparison :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot QRed (Ideal.span {xRed})).trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : QRed ≃ₐ[QRed] QRed) ncAlgEquivQuotXRed)

/-- `Q ⊗_{Q'} N' ≅ Q/(x)·Q` for `N' = Q' ⧸ (x − t·z)`, which is the `Q'`-side half of the
conclusion. Type inferred, for the same reason. -/
def qLiftComparison :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot QRed vIdeal).symm.trans
    (Ideal.quotientEquivAlgOfEq QRed map_vIdeal_eq)

/-! ### The two halves of the failing biconditional, each on its own -/

/-- **Clause (2) of Stacks 0DZ2 holds for the counterexample**: `N = Q ⊗_P M` has the `A'`-flat
`Q'`-module lift `N' = Q' ⧸ (x − t·z)`, which is `QLift`. `N` is presented as
`Q/(x)·Q`, the presentation `ncTensorComparison` identifies with `Q ⊗_P M`. -/
theorem exists_flat_lift_QLift :
    ∃ (N' : Type) (_ : AddCommGroup N') (_ : Module QBase N') (_ : Module ABase N')
      (_ : IsScalarTower ABase QBase N'), Module.Flat ABase N' ∧
      Nonempty ((QRed ⊗[QBase] N') ≃ₗ[QRed]
        ((QRed : Type) ⧸ (Ideal.span {xRed}).map (algebraMap PRed QRed))) :=
  ⟨QLift, inferInstance, inferInstance, inferInstance, inferInstance, flat_QLift,
    ⟨qLiftComparison.toLinearEquiv⟩⟩

/-- **Clause (1) of Stacks 0DZ2 fails for the counterexample, at every universe**: there is no
`A'`-flat `P'`-module `M'` with `P ⊗_{P'} M' ≅ M`, in any universe `u`.

The reduction map `y ↦ e (1 ⊗ y)` of a putative lift satisfies the four hypotheses of
`Deformation.Examples.ArtinSchreier.not_flat_lift_of_reduction`: additivity and semilinearity
come from `e`, surjectivity from the surjectivity of `P' → P` — every element of `P ⊗_{P'} M'`
is `1 ⊗ y` — and the kernel condition from `TensorProduct.quotTensorEquivQuotSMul`.

The universe polymorphism is free: `not_flat_lift_of_reduction` asks only for a bare function
`M' → NC`, so nothing here constrains `M'` to live where `P'` does. This makes the refutation a
refutation of the source, whose clause (1) puts no bound on the universe of a lift. -/
theorem not_lift_of_tensorEquiv {M' : Type u} [AddCommGroup M'] [Module PBase M']
    [Module ABase M'] [IsScalarTower ABase PBase M'] [Module.Flat ABase M']
    (e : (PRed ⊗[PBase] M') ≃ₗ[PRed] NC) : False := by
  -- every element of `P ⊗_{P'} M'` is `1 ⊗ y`, because `P' → P` is surjective
  have htmul : ∀ w : PRed ⊗[PBase] M', ∃ y : M', w = 1 ⊗ₜ[PBase] y := by
    refine fun w => TensorProduct.induction_on w ?_ ?_ ?_
    · exact ⟨0, (TensorProduct.tmul_zero _ _).symm⟩
    · intro r y
      obtain ⟨p, rfl⟩ := surjective_PBase_PRed r
      refine ⟨p • y, ?_⟩
      rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    · rintro w₁ w₂ ⟨y₁, rfl⟩ ⟨y₂, rfl⟩
      exact ⟨y₁ + y₂, (TensorProduct.tmul_add _ _ _).symm⟩
  -- the reduction map of the putative lift, as a bare function
  refine not_flat_lift_of_reduction (fun y => e (1 ⊗ₜ[PBase] y)) ?_ ?_ ?_ ?_
  · intro y z
    show e ((1 : PRed) ⊗ₜ[PBase] (y + z)) = e ((1 : PRed) ⊗ₜ[PBase] y) + e (1 ⊗ₜ[PBase] z)
    rw [TensorProduct.tmul_add, map_add]
  · intro p y
    show e ((1 : PRed) ⊗ₜ[PBase] (p • y)) = pBaseToNC p * e ((1 : PRed) ⊗ₜ[PBase] y)
    have h1 := e.map_smul (algebraMap PBase PRed p) ((1 : PRed) ⊗ₜ[PBase] y)
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
      TensorProduct.tmul_eq_smul_one_tmul, h1, Algebra.smul_def, algebraMap_pRed_NC]
  · intro n
    obtain ⟨y, hy⟩ := htmul (e.symm n)
    refine ⟨y, ?_⟩
    change e ((1 : PRed) ⊗ₜ[PBase] y) = n
    rw [← hy, e.apply_symm_apply]
  · intro y hy
    have hy' : e ((1 : PRed) ⊗ₜ[PBase] y) = 0 := hy
    have h0 : (1 : PRed) ⊗ₜ[PBase] y = 0 :=
      e.injective (hy'.trans (map_zero e).symm)
    have hq := congrArg (TensorProduct.quotTensorEquivQuotSMul M' (Ideal.span {tauP})) h0
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero,
      Submodule.Quotient.mk_eq_zero] at hq
    refine Submodule.smul_induction_on hq ?_ ?_
    · intro r hr n _
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 hr
      exact ⟨c • n, by rw [mul_smul]⟩
    · rintro a b ⟨wa, rfl⟩ ⟨wb, rfl⟩
      exact ⟨wa + wb, (smul_add _ _ _).symm⟩

/-! ### The refutation -/

/-- **Stacks 0DZ2, at the source's hypotheses and restricted to a finite module, is false.**

Every hypothesis is discharged by the results tabulated in this file's module documentation; the
conclusion fails because `N = Q ⊗_P M` lifts over `Q'` (`flat_QLift`) while `M` does not lift
over `P'` (`not_flat_lift_of_reduction`, the Artin–Schreier obstruction). The kernel of `A' → A`
is `(t)` with `t³ = 0` and `t² ≠ 0`, so the instance is nilpotent and not square-zero, which is
where the square-zero form of 0DZ2 stops.

`M = NC` is finite and cyclic over `P`, so the finiteness restriction in
`Deformation.FlatModuleLiftBaseChangeStatement` does not save the statement. -/
theorem not_flatModuleLiftBaseChangeStatement :
    ¬ Deformation.FlatModuleLiftBaseChangeStatement.{0} := by
  intro h
  let : Algebra ABase NC := redA.toAlgebra
  have := IsScalarTower.of_algebraMap_eq (R := ABase) (S := NC) (A := PRed)
    (fun a => algebraMap_ABase_PRed_eq a)
  have := finite_NC
  have := flat_NC_NC
  have := isScalarTower_NC_PRed_QRed
  have key := h ABase NC PBase PRed QBase QRed
    redA_surjective isNilpotent_ker_redA
    surjective_PBase_PRed ker_PBase_PRed_eq_map
    surjective_QBase_QRed ker_QBase_QRed_eq_map
    flat_PBase flat_QBase_ABase flat_QBase_PBase flat_QRed_PRed
    (Ideal.span {omegaP}) bijective_quotientMap_omegaP
    NC ((QRed : Type) ⧸ (Ideal.span {xRed}).map (algebraMap PRed QRed))
    ⟨ncTensorComparison.symm.toLinearEquiv⟩
    (fun g hg => hlocal_nodal hg)
  obtain ⟨M', _, _, _, _, hflatM, ⟨e⟩⟩ := key.2 exists_flat_lift_QLift
  have := hflatM
  exact not_lift_of_tensorEquiv e

end Deformation.Examples.ArtinSchreier

end
