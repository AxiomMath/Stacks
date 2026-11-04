module

public import StacksFrontier.Deformation.Examples.Linear.NodalArtinSchreierLift
public import StacksFrontier.Deformation.Examples.Linear.NodalCubicBase

/-!
# The left column of the Stacks 0DZ2 counterexample: `A' → P' → P` over `A`

Second layer of the instantiation of `Deformation.FlatModuleLiftBaseChangeStatement`. The
counterexample's left column is built here, over the nodal cubic `NC` of
`StacksFrontier.Deformation.Examples.Linear.NodalCubicBase`:

`A' = NC[t]/t³`,  `A = NC`,  `P' = A'[x]/(x² − t·x − t²·Y)`,  `P = P'/t·P'`.

The two choices that make this cheap are the ones recorded in
`StacksFrontier.Deformation.Examples.Linear.NodalArtinSchreierLift`:

* taking `A' = NC[t]/t³` and hence `A = NC` — rather than `A' = 𝔽₂[t]/t³` with the nodal cubic
  inside `P` — makes `P'` **free of rank two** over `A'`, by `AdjoinRoot.powerBasis'`, with no
  further argument. Flatness of `P'` over `A'` is then immediate, which is one of the four
  flatness hypotheses of Stacks 0DZ2;
* taking `P` to be the literal quotient `P'/t·P'` makes `Function.Surjective (algebraMap P' P)`,
  the kernel computation and `hkerP` nearly free, and lets `TensorProduct.quotTensorEquivQuotSMul`
  compute `P ⊗_{P'} M'` later without a transport.

`A' = NC[t]/t³` is the repo's `Deformation.Examples.MaurerCartanWindow.Trunc3 NC`, so the basis
`1, t, t²` is already available (`cst_add_tau_eq_zero_iff`, `exists_cst_add_tau`) and is what the
kernel computation uses.

## Main definitions

* `Deformation.Examples.ArtinSchreier.ABase`: `A' = NC[t]/t³`.
* `Deformation.Examples.ArtinSchreier.redA`: the reduction `A' → NC`, i.e. `t ↦ 0`.
* `Deformation.Examples.ArtinSchreier.pPoly`: the monic quadratic `x² − t·x − t²·Y` over `A'`.
* `Deformation.Examples.ArtinSchreier.PBase`: `P' = A'[x]/(x² − t·x − t²·Y)`.
* `Deformation.Examples.ArtinSchreier.PRed`: `P = P'/t·P'`.

## Main results

* `Deformation.Examples.ArtinSchreier.redA_surjective`,
  `Deformation.Examples.ArtinSchreier.ker_redA`,
  `Deformation.Examples.ArtinSchreier.isNilpotent_ker_redA`: the vertical map `A' → A` is
  surjective with kernel `(t)`, which is nilpotent. These are the first two hypotheses of
  Stacks 0DZ2.
* `Deformation.Examples.ArtinSchreier.pPoly_monic`,
  `Deformation.Examples.ArtinSchreier.free_PBase`,
  `Deformation.Examples.ArtinSchreier.flat_PBase`: `P'` is free of rank two over `A'`, hence
  flat — the hypothesis `Module.Flat A' P'`.
* `Deformation.Examples.ArtinSchreier.pRelation`: the defining relation `x² = t·x + t²·Y` of
  `P'`, which is what the lifting problem of the counterexample's module reduces to.

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
-/

@[expose] public noncomputable section

open Polynomial
open Deformation.Examples.MaurerCartanWindow

universe u

namespace Deformation.Examples.ArtinSchreier

/-! ### Nontriviality -/

/-- The nodal cubic is not the zero ring: the normalisation `NC → 𝔽₂[s]` sends `1` to `1`. -/
instance : Nontrivial NC :=
  ⟨⟨1, 0, fun h => by
    have hmap := congrArg ncToAmb h
    simp at hmap⟩⟩

/-! ### `A' = NC[t]/t³` and its reduction to `A = NC` -/

/-- `A' = NC[t]/t³`, the base of the counterexample's thickening. -/
abbrev ABase : Type := Trunc3 NC

/-- The reduction `A' → NC`, `t ↦ 0`. Its kernel is `(t)`, which is nilpotent, so this is the
surjection with nilpotent kernel that Stacks 0DZ2 starts from. -/
def redA : ABase →+* NC :=
  Ideal.Quotient.lift _ (Polynomial.evalRingHom (0 : NC)) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 ha
    simp)

/-- The reduction `A' → NC` sends the constant `a` to `a`. -/
@[simp] theorem redA_cst (a : NC) : redA (cst NC a) = a := by
  show Polynomial.eval 0 (Polynomial.C a) = a
  simp

/-- The reduction `A' → NC` sends `t` to `0`. -/
@[simp] theorem redA_tau : redA (tau NC) = 0 := by
  show Polynomial.eval 0 (Polynomial.X : Polynomial NC) = 0
  simp

/-- The reduction `A' → NC` is surjective. -/
theorem redA_surjective : Function.Surjective redA := fun a => ⟨cst NC a, redA_cst a⟩

/-- **The kernel of `A' → NC` is `(t)`.** One inclusion is `redA_tau`; the other uses that
`1, t, t²` is an `NC`-basis of `A'`, so an element with vanishing constant coefficient is
`t·(b + t·c)`. -/
theorem ker_redA : RingHom.ker redA = Ideal.span {tau NC} := by
  refine le_antisymm ?_ ?_
  · intro z hz
    obtain ⟨a, b, c, rfl⟩ := exists_cst_add_tau (R := NC) z
    rw [RingHom.mem_ker] at hz
    simp only [map_add, map_mul, redA_cst, redA_tau, zero_mul, mul_zero, add_zero] at hz
    subst hz
    refine Ideal.mem_span_singleton.2 ⟨cst NC b + tau NC * cst NC c, ?_⟩
    rw [map_zero]
    ring
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    exact redA_tau

/-- `(t)` is nilpotent in `A' = NC[t]/t³`: its cube is `(t³) = 0`. -/
theorem isNilpotent_ker_redA : IsNilpotent (RingHom.ker redA) := by
  refine ⟨3, ?_⟩
  rw [ker_redA, Ideal.span_singleton_pow]
  refine le_antisymm ?_ bot_le
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
  have h : (tau NC) ^ 3 = 0 := by
    rw [show (tau NC) ^ 3 = tau NC * tau NC * tau NC by ring]
    exact tau_cube (R := NC)
  rw [h]
  exact Submodule.zero_mem _

/-! ### `P' = A'[x]/(x² − t·x − t²·Y)` -/

/-- The monic quadratic `x² − t·x − t²·Y` over `A' = NC[t]/t³`. Its root is the `x` of the
counterexample's `P'`; reducing modulo `t` gives `x² = 0`, so `P` is `NC[x]/(x²)`. -/
def pPoly : Polynomial ABase :=
  X ^ 2 + -(C (tau NC) * X + C (tau NC * tau NC * cst NC ncY))

/-- `x² − t·x − t²·Y` is monic: it is `X²` plus something of degree at most one. -/
theorem pPoly_monic : pPoly.Monic := by
  have hnt : Nontrivial ABase := redA.domain_nontrivial
  refine (Polynomial.monic_X_pow (R := ABase) 2).add_of_left ?_
  rw [Polynomial.degree_X_pow]
  have hle : (-(C (tau NC) * X + C (tau NC * tau NC * cst NC ncY)) :
      Polynomial ABase).degree ≤ 1 := by
    rw [Polynomial.degree_neg]
    exact Polynomial.degree_linear_le
  exact lt_of_le_of_lt hle (by norm_num)

/-- `P' = A'[x]/(x² − t·x − t²·Y)`, the counterexample's upper-left thickening. -/
abbrev PBase : Type := AdjoinRoot pPoly

/-- **`P'` is free of rank two over `A'`**, on `{1, x}`, because `x² − t·x − t²·Y` is monic of
degree two. This is what makes `Module.Flat A' P'` free of charge. -/
theorem free_PBase : Module.Free ABase PBase :=
  Module.Free.of_basis (AdjoinRoot.powerBasis' pPoly_monic).basis

/-- **`P'` is flat over `A'`**, one of the four flatness hypotheses of Stacks 0DZ2. -/
theorem flat_PBase : Module.Flat ABase PBase :=
  have := free_PBase
  Module.Flat.of_free

/-- **The defining relation of `P'`**: `x² = t·x + t²·Y`. This is the relation whose coefficient
analysis is `Deformation.Examples.ArtinSchreier.twisted_lift_iff`, and therefore the reason the
lifting problem of the counterexample's module is the Artin–Schreier equation for `Y`. -/
theorem pRelation :
    AdjoinRoot.root pPoly * AdjoinRoot.root pPoly =
      algebraMap ABase PBase (tau NC) * AdjoinRoot.root pPoly +
        algebraMap ABase PBase (tau NC * tau NC * cst NC ncY) := by
  have h0 : AdjoinRoot.mk pPoly
      (X ^ 2 + -(C (tau NC) * X + C (tau NC * tau NC * cst NC ncY))) = 0 := by
    rw [show (X ^ 2 + -(C (tau NC) * X + C (tau NC * tau NC * cst NC ncY)) :
      Polynomial ABase) = pPoly from rfl]
    exact AdjoinRoot.mk_self
  rw [map_add, map_neg, map_add, map_pow, map_mul] at h0
  have hX : AdjoinRoot.mk pPoly (X : Polynomial ABase) = AdjoinRoot.root pPoly := rfl
  have hC1 : AdjoinRoot.mk pPoly (C (tau NC)) = algebraMap ABase PBase (tau NC) := rfl
  have hC2 : AdjoinRoot.mk pPoly (C (tau NC * tau NC * cst NC ncY)) =
      algebraMap ABase PBase (tau NC * tau NC * cst NC ncY) := rfl
  rw [hX, hC1, hC2] at h0
  linear_combination h0

/-! ### `P = P'/t·P'` -/

/-- The image of `t` in `P'`. -/
def tauP : PBase := algebraMap ABase PBase (tau NC)

/-- `P = P'/t·P'`, the counterexample's lower-left ring. Taking it as a literal quotient makes
the surjectivity, the kernel and `hkerP` of Stacks 0DZ2 nearly free, and lets
`TensorProduct.quotTensorEquivQuotSMul` compute `P ⊗_{P'} M'` with no transport. -/
abbrev PRed : Type := PBase ⧸ Ideal.span {tauP}

/-- `P' → P` is surjective. -/
theorem surjective_PBase_PRed :
    Function.Surjective (algebraMap PBase PRed) :=
  Ideal.Quotient.mk_surjective

/-- The kernel of `P' → P` is `(t·P')`. -/
theorem ker_PBase_PRed :
    RingHom.ker (algebraMap PBase PRed) = Ideal.span {tauP} :=
  Ideal.mk_ker

/-- **`hkerP` of Stacks 0DZ2**: the kernel of `P' → P` is the ideal generated by the image of the
kernel of `A' → A`. Both sides are `(t·P')`, the right one by `Ideal.map_span`. -/
theorem ker_PBase_PRed_eq_map :
    RingHom.ker (algebraMap PBase PRed) =
      (RingHom.ker redA).map (algebraMap ABase PBase) := by
  rw [ker_PBase_PRed, ker_redA, Ideal.map_span]
  simp [tauP]

end Deformation.Examples.ArtinSchreier

end
