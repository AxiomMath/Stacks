module

public import StacksFrontier.LinearAlgebra.ExteriorPower.Wedge
public import StacksFrontier.RingTheory.DeRham.PolynomialQuasiIso

/-!
# The graded Leibniz rule for the de Rham complex of a ring map

Let `A → R` be a commutative ring map.  Together with the graded commutativity and associativity
of `exteriorPower.wedgeMul`, this file completes the differential graded algebra structure on the
exterior powers `⋀^p (Ω[R⁄A])` of the module of relative differentials: it proves

* **the full Leibniz rule** `d(ω ∧ η) = dω ∧ η + (-1)^{deg ω} ω ∧ dη`

for the de Rham differential `KaehlerDifferential.deRhamDifferential`.  Before this file the
library had the Leibniz rule only for wedging with a one-form,
`KaehlerDifferential.deRhamDifferential_wedgeLeft_D`, and the de Rham differential graded algebra
only at the sheaf level.

## Main results

* `KaehlerDifferential.coe_deRhamDifferential_wedgeMul`: **the full Leibniz rule**
  `d(ω ∧ η) = dω ∧ η + (-1)^p ω ∧ dη`, as an identity in the exterior algebra;
  `KaehlerDifferential.deRhamDifferential_wedgeMul` is the version stated inside a single
  exterior power.

## Implementation notes

**Why the identity is stated in the exterior algebra.**  The three terms of the Leibniz rule
live a priori in three different types: `d(ω ∧ η)` in `⋀^{(p+q)+1}`, `dω ∧ η` in `⋀^{(p+1)+q}`
and `ω ∧ dη` in `⋀^{p+(q+1)}`.  The first and the third are the same type — `Nat.add` recurses on
its second argument — but `(p+1)+q = (p+q)+1` holds only propositionally, so a statement purely
inside the exterior powers needs a transport.  Since `⋀^n M` is by definition a *submodule* of
`ExteriorAlgebra R M`, every one of these elements is literally an element of the exterior
algebra, and the identity between them there is the identity with no transport in it; that is the
form proved first, and `exteriorPower.degCongr` then packages the transport for the
exterior-power form.  The same device, `KaehlerDifferential.coe_deRhamDifferential_congr`, is
what keeps the induction free of `HEq`.

**The induction.**  The Leibniz rule is an induction on `p`.  Over `A` the module `⋀^p (Ω[R⁄A])`
is spanned by the elements `b₀ · d b₁ ∧ ⋯ ∧ d b_p`
(`Crystalline.span_range_smul_ιMulti_eq_top`), and both sides of the rule are `A`-linear in `ω`,
so it is enough to treat those.  In degree zero the rule is the Leibniz rule
`KaehlerDifferential.deRhamDifferential_smul` for a scalar, and the inductive step peels off the
leading `d b₁ ∧ ·`, where `KaehlerDifferential.deRhamDifferential_wedgeLeft_D` applies and the
sign flips.

## References

* [Stacks Project, Tag 0FKG](https://stacks.math.columbia.edu/tag/0FKG), the de Rham complex
* [Stacks Project, Tag 0FU6](https://stacks.math.columbia.edu/tag/0FU6), the same structure for a
  morphism of schemes
-/

@[expose] public noncomputable section

open CategoryTheory KaehlerDifferential

universe u

namespace KaehlerDifferential

variable {A R : Type u} [CommRing A] [CommRing R] [Algebra A R]

/-! ### Transporting the de Rham differential across an equality of degrees -/

/-- The de Rham differential of two forms with the same underlying element of the exterior
algebra, in two degrees that are equal, agree in the exterior algebra.  This is the transport
that keeps the Leibniz induction free of `HEq`. -/
theorem coe_deRhamDifferential_congr {m n : ℕ} (h : m = n)
    {x : ⋀[R]^m (Ω[R⁄A])} {y : ⋀[R]^n (Ω[R⁄A])}
    (hxy : (x : ExteriorAlgebra R (Ω[R⁄A])) = (y : ExteriorAlgebra R (Ω[R⁄A]))) :
    ((deRhamDifferential (A := A) m x : ⋀[R]^(m + 1) (Ω[R⁄A])) :
        ExteriorAlgebra R (Ω[R⁄A])) =
      ((deRhamDifferential (A := A) n y : ⋀[R]^(n + 1) (Ω[R⁄A])) :
        ExteriorAlgebra R (Ω[R⁄A])) := by
  subst h
  rw [Subtype.coe_injective hxy]

/-! ### The full Leibniz rule -/

/-- **The full Leibniz rule for the de Rham differential**,
`d(ω ∧ η) = dω ∧ η + (-1)^{deg ω} ω ∧ dη`, read in the exterior algebra: the three products are
the multiplication of `ExteriorAlgebra R (Ω[R⁄A])`, in which the degree bookkeeping disappears.

The library had this only for `ω` a one-form `d b`
(`KaehlerDifferential.deRhamDifferential_wedgeLeft_D`); the proof here is the induction on the
degree of `ω` described in the implementation notes of this file. -/
theorem coe_deRhamDifferential_wedgeMul (p q : ℕ) (ω : ⋀[R]^p (Ω[R⁄A]))
    (η : ⋀[R]^q (Ω[R⁄A])) :
    ((deRhamDifferential (A := A) (p + q) (exteriorPower.wedgeMul p q ω η) :
          ⋀[R]^(p + q + 1) (Ω[R⁄A])) : ExteriorAlgebra R (Ω[R⁄A])) =
      ((deRhamDifferential (A := A) p ω : ⋀[R]^(p + 1) (Ω[R⁄A])) :
          ExteriorAlgebra R (Ω[R⁄A])) * (η : ExteriorAlgebra R (Ω[R⁄A])) +
        (-1) ^ p * ((ω : ExteriorAlgebra R (Ω[R⁄A])) *
          ((deRhamDifferential (A := A) q η : ⋀[R]^(q + 1) (Ω[R⁄A])) :
            ExteriorAlgebra R (Ω[R⁄A]))) := by
  induction p generalizing q with
  | zero =>
      have hω : ω ∈ (⊤ : Submodule A (⋀[R]^0 (Ω[R⁄A]))) := Submodule.mem_top
      rw [← Crystalline.span_range_smul_ιMulti_eq_top (R := A) (KaehlerDifferential.D A R)
        (span_range_derivation A R) 0] at hω
      induction hω using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨b, rfl⟩ := hx
          dsimp only
          have hone : ((exteriorPower.ιMulti R 0 fun i : Fin 0 ↦ D A R (b i.succ) :
              ⋀[R]^0 (Ω[R⁄A])) : ExteriorAlgebra R (Ω[R⁄A])) = 1 := by
            rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_zero_apply]
          have hcoe : ((b 0 • exteriorPower.ιMulti R 0 fun i : Fin 0 ↦ D A R (b i.succ) :
                ⋀[R]^0 (Ω[R⁄A])) : ExteriorAlgebra R (Ω[R⁄A])) =
              algebraMap R (ExteriorAlgebra R (Ω[R⁄A])) (b 0) := by
            rw [SetLike.val_smul, hone, Algebra.smul_def, mul_one]
          have hd : ((deRhamDifferential (A := A) 0
                (b 0 • exteriorPower.ιMulti R 0 fun i : Fin 0 ↦ D A R (b i.succ)) :
              ⋀[R]^1 (Ω[R⁄A])) : ExteriorAlgebra R (Ω[R⁄A])) =
              ExteriorAlgebra.ι R (D A R (b 0)) := by
            rw [deRhamDifferential_smul_ιMulti_D 0 b, exteriorPower.ιMulti_apply_coe,
              ExteriorAlgebra.ιMulti_succ_apply]
            simp
          have hleft := coe_deRhamDifferential_congr (A := A) (Nat.zero_add q)
            (x := exteriorPower.wedgeMul 0 q
              (b 0 • exteriorPower.ιMulti R 0 fun i : Fin 0 ↦ D A R (b i.succ)) η)
            (y := b 0 • η)
            (by rw [exteriorPower.wedgeMul_apply_coe, hcoe, SetLike.val_smul, Algebra.smul_def])
          rw [hleft, deRhamDifferential_smul, Submodule.coe_add, exteriorPower.coe_wedgeLeft,
            SetLike.val_smul, hd, hcoe, pow_zero, one_mul, Algebra.smul_def]
      | zero => simp
      | add x y _ _ hx hy =>
          rw [map_add, LinearMap.add_apply, map_add, map_add, Submodule.coe_add,
            Submodule.coe_add, Submodule.coe_add, hx, hy]
          simp only [add_mul, mul_add]
          abel
      | smul c x _ hx =>
          have hws : exteriorPower.wedgeMul 0 q (c • x) η =
              c • exteriorPower.wedgeMul 0 q x η := by
            rw [← algebraMap_smul R c x, map_smul, LinearMap.smul_apply,
              algebraMap_smul]
          rw [hws, map_smul, map_smul, Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower,
            Submodule.coe_smul_of_tower, hx, smul_mul_assoc, smul_add, smul_mul_assoc,
            mul_smul_comm]
  | succ p ih =>
      have hω : ω ∈ (⊤ : Submodule A (⋀[R]^(p + 1) (Ω[R⁄A]))) := Submodule.mem_top
      rw [← Crystalline.span_range_smul_ιMulti_eq_top (R := A) (KaehlerDifferential.D A R)
        (span_range_derivation A R) (p + 1)] at hω
      induction hω using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨b, rfl⟩ := hx
          dsimp only
          -- peel off the leading one-form `d (b 1)`
          set ξ : ⋀[R]^p (Ω[R⁄A]) :=
            b 0 • exteriorPower.ιMulti R p fun i : Fin p ↦ D A R (b i.succ.succ) with hξ
          have hpeel : b 0 • (exteriorPower.ιMulti R (p + 1)
                fun i : Fin (p + 1) ↦ D A R (b i.succ)) =
              exteriorPower.wedgeLeft (D A R (b 1)) p ξ := by
            rw [hξ, map_smul, exteriorPower.wedgeLeft_ιMulti]
            congr 1
            refine (exteriorPower.ιMulti R (p + 1)).congr_arg ?_
            funext i
            refine Fin.cases ?_ ?_ i
            · rfl
            · intro j; rfl
          rw [hpeel]
          have hassoc : ((exteriorPower.wedgeMul (p + 1) q
                  (exteriorPower.wedgeLeft (D A R (b 1)) p ξ) η :
                ⋀[R]^(p + 1 + q) (Ω[R⁄A])) : ExteriorAlgebra R (Ω[R⁄A])) =
              ((exteriorPower.wedgeLeft (D A R (b 1)) (p + q)
                  (exteriorPower.wedgeMul p q ξ η) :
                ⋀[R]^(p + q + 1) (Ω[R⁄A])) : ExteriorAlgebra R (Ω[R⁄A])) := by
            rw [exteriorPower.wedgeMul_apply_coe, exteriorPower.coe_wedgeLeft,
              exteriorPower.coe_wedgeLeft, exteriorPower.wedgeMul_apply_coe, mul_assoc]
          rw [coe_deRhamDifferential_congr (A := A) (Nat.succ_add p q) hassoc,
            deRhamDifferential_wedgeLeft_D, Submodule.coe_neg, exteriorPower.coe_wedgeLeft,
            ih q ξ η, deRhamDifferential_wedgeLeft_D, Submodule.coe_neg,
            exteriorPower.coe_wedgeLeft, exteriorPower.coe_wedgeLeft, pow_succ]
          have hcen (z : ExteriorAlgebra R (Ω[R⁄A])) :
              ExteriorAlgebra.ι R (D A R (b 1)) * ((-1 : ExteriorAlgebra R (Ω[R⁄A])) ^ p * z) =
                (-1 : ExteriorAlgebra R (Ω[R⁄A])) ^ p *
                  (ExteriorAlgebra.ι R (D A R (b 1)) * z) := by
            rw [← mul_assoc, ← ((Commute.neg_one_left
              (ExteriorAlgebra.ι R (D A R (b 1)))).pow_left p).eq, mul_assoc]
          simp only [mul_add, mul_assoc, hcen, neg_mul, mul_neg, mul_one]
          abel
      | zero => simp
      | add x y _ _ hx hy =>
          rw [map_add, LinearMap.add_apply, map_add, map_add, Submodule.coe_add,
            Submodule.coe_add, Submodule.coe_add, hx, hy]
          simp only [add_mul, mul_add]
          abel
      | smul c x _ hx =>
          have hws : exteriorPower.wedgeMul (p + 1) q (c • x) η =
              c • exteriorPower.wedgeMul (p + 1) q x η := by
            rw [← algebraMap_smul R c x, map_smul, LinearMap.smul_apply,
              algebraMap_smul]
          rw [hws, map_smul, map_smul, Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower,
            Submodule.coe_smul_of_tower, hx, smul_mul_assoc, smul_add, smul_mul_assoc,
            mul_smul_comm]

/-- **The full Leibniz rule for the de Rham differential**,
`d(ω ∧ η) = dω ∧ η + (-1)^{deg ω} ω ∧ dη`, with all three terms transported into the single
exterior power `⋀^{p+q+1} (Ω[R⁄A])`.  Only `dω ∧ η` needs a transport: it is built in degree
`(p+1)+q`, which is the degree `(p+q)+1` of the other two but not by definitional unfolding. -/
theorem deRhamDifferential_wedgeMul (p q : ℕ) (ω : ⋀[R]^p (Ω[R⁄A]))
    (η : ⋀[R]^q (Ω[R⁄A])) :
    deRhamDifferential (A := A) (p + q) (exteriorPower.wedgeMul p q ω η) =
      exteriorPower.degCongr (Nat.succ_add p q)
          (exteriorPower.wedgeMul (p + 1) q (deRhamDifferential (A := A) p ω) η) +
        (-1 : R) ^ p • exteriorPower.wedgeMul p (q + 1) ω
          (deRhamDifferential (A := A) q η) := by
  refine Subtype.ext ?_
  rw [Submodule.coe_add, exteriorPower.coe_degCongr, exteriorPower.wedgeMul_apply_coe,
    SetLike.val_smul, exteriorPower.wedgeMul_apply_coe, Algebra.smul_def,
    coe_deRhamDifferential_wedgeMul p q ω η]
  simp

end KaehlerDifferential

end
