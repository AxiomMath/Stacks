module

public import Mathlib.RingTheory.DividedPowers.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.Connection
public import StacksFrontier.RingTheory.DeRham.Complex

/-!
# The de Rham complex of an integrable connection, and the divided power de Rham complex

Two de Rham complexes attached to the crystalline setting are built here.

The first is the complex of an integrable connection.  Let `π : Ω[B⁄A] → Ω` be a surjection along
which the de Rham differential descends and let `∇` be a connection on a `B`-module `M`.  Its
extensions `M ⊗[B] ⋀^p Ω → M ⊗[B] ⋀^{p+1} Ω` compose to zero as soon as `∇` is integrable.  The
proof rests on the graded Leibniz rule in degrees `(1, q)`,

`d (ω ∧ ζ) = (d ω) ∧ ζ − ω ∧ (d ζ)` for `ω` of degree `1`,

first for the de Rham differential of `B` over `A` and then, by surjectivity of `π`, for the
descended differential.  Given that rule, the composite of the two extensions on `m ⊗ ω` splits
into the curvature term — which vanishes by integrability — and the term `m ⊗ d (d ω)`, which
vanishes because the descended differential is itself a complex.  The graded Leibniz rule is
proved by reducing to the generators `ω = c · d e` and `ζ = b₀ · (d b₁ ∧ ⋯ ∧ d b_q)`, where the
defining rule of the differential computes all three terms and what remains is the antisymmetry
`d b₀ ∧ d e = − d e ∧ d b₀` of the exterior algebra.

The second is the divided power de Rham complex.  For divided powers `δ` on an ideal `J ⊆ B`, the
module of divided power differentials `Ω¹_{B/A,δ}` is the quotient of `Ω[B⁄A]` by the relations
`d (δ_{n+1} x) = δ_n x · d x`, and `Ωⁱ_{B/A,δ}` is its `i`-th exterior power.  The de Rham
differential descends along this quotient, because the differential of each defining relation
already vanishes in the second exterior power of the quotient, and the resulting complex is
unique.

## Main definitions

* `Crystalline.dividedPowerDifferentials` — `Ω¹_{B/A,δ}`.
* `Crystalline.dividedPowerDifferential` — the universal divided-power-compatible differential.
* `Crystalline.dividedPowerDifferentialForms` — `Ωⁱ_{B/A,δ}`.
* `Crystalline.DividedPowerDeRhamComplex` — the differential and its square-zero property.
* `Crystalline.dividedPowerDeRhamComplex` — the canonical such complex.

## Main results

* `Crystalline.extendedConnection_comp_self_eq_zero` — consecutive extended differentials of an
  integrable connection compose to zero.
* `Crystalline.DividedPowerDeRhamComplex.unique` — the generator rule determines the divided
  power de Rham complex.
* `Crystalline.generationHypothesis_of_ker_eq_relations` — a surjection whose kernel is the
  submodule of divided power relations satisfies the generation hypothesis of Tag 07HY, so the
  de Rham differential descends along it.

## Implementation notes

The differentials are `A`-linear and not `B`-linear, so the terms of both complexes are `A`-modules
by restriction of scalars along `A → B`, i.e. the `RestrictScalars` synonyms
`Stacks.DeRham.DifferentialDescent.SrcA` and `Stacks.DeRham.DifferentialDescent.TgtA`. The
computations below never identify a synonym with the exterior power it abbreviates; instead
`Crystalline.sourceDifferential` and `Crystalline.descendedDifferential` transport the
differentials to the exterior powers once and for all, as additive maps, and every rewrite is
performed on those. Accordingly `DividedPowerDeRhamComplex` records its maps on the fixed
synonyms rather than on an abstract family of modules; in particular its degree-zero term is
Mathlib's canonical `⋀[B]^0`, not `B` itself.

## References

* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
* [Stacks Project, Tag 07I0](https://stacks.math.columbia.edu/tag/07I0)
-/

@[expose] public section

namespace Crystalline

/-! ### The de Rham complex of an integrable connection -/

section ConnectionDeRham

open scoped TensorProduct

open Stacks.DeRham.DifferentialDescent

universe u v

variable {A B Omega : Type u} {M : Type v}
  [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup Omega] [Module B Omega]
  [AddCommGroup M] [Module B M]

section ExteriorAlgebraAux

variable {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]

/-- Prefixing a vector to a wedge multiplies by it, read in the exterior algebra. -/
private lemma coe_ιMulti_cons (n : ℕ) (x : N) (v : Fin n → N) :
    (exteriorPower.ιMulti R (n + 1) (Fin.cons x v) : ExteriorAlgebra R N)
      = ExteriorAlgebra.ι R x * (exteriorPower.ιMulti R n v : ExteriorAlgebra R N) := by
  rw [coe_ιMulti_succ, Fin.cons_zero]
  simp

/-- A wedge of length one is additive in its entry, read in the exterior algebra. -/
private lemma coe_ιMulti_one_add (x y : N) :
    (exteriorPower.ιMulti R 1 (fun _ ↦ x + y) : ExteriorAlgebra R N)
      = (exteriorPower.ιMulti R 1 (fun _ ↦ x) : ExteriorAlgebra R N)
        + (exteriorPower.ιMulti R 1 (fun _ ↦ y) : ExteriorAlgebra R N) := by
  rw [coe_ιMulti_one, coe_ιMulti_one, coe_ιMulti_one, map_add]

/-- A wedge of length one is homogeneous in its entry, read in the exterior algebra. -/
private lemma coe_ιMulti_one_smul (c : R) (x : N) :
    (exteriorPower.ιMulti R 1 (fun _ ↦ c • x) : ExteriorAlgebra R N)
      = c • (exteriorPower.ιMulti R 1 (fun _ ↦ x) : ExteriorAlgebra R N) := by
  rw [coe_ιMulti_one, coe_ιMulti_one, map_smul]

end ExteriorAlgebraAux

/-- The de Rham differential of the one-form `c • d b` is the wedge `d c ∧ d b`. -/
private lemma sourceDifferential_one_smul_D (S : SourceDeRham A B) (c b : B) :
    sourceDifferential S 1 ((exteriorPower.oneEquiv B Ω[B⁄A]).symm
        (c • KaehlerDifferential.D A B b)) =
      exteriorPower.ιMulti B 2 ![KaehlerDifferential.D A B c, KaehlerDifferential.D A B b] := by
  have hsrc : (exteriorPower.oneEquiv B Ω[B⁄A]).symm (c • KaehlerDifferential.D A B b) =
      srcGen 1 ![c, b] := by
    rw [srcGen, map_smul, exteriorPower.oneEquiv_symm_apply]
    simp only [Matrix.cons_val_zero]
    rfl
  rw [hsrc, sourceDifferential_srcGen, srcGenRes]
  congr 1
  funext j
  fin_cases j <;> rfl

/-- The failure of the graded Leibniz rule in degrees `(1, q)`, measured inside the exterior
algebra of `Ω_{B/A}`, where no degree coercion intervenes. -/
private noncomputable def leibnizDefect (S : SourceDeRham A B) (q : ℕ) (a : Ω[B⁄A])
    (y : ⋀[B]^q (Ω[B⁄A])) : ExteriorAlgebra B (Ω[B⁄A]) :=
  (sourceDifferential S (q + 1) (leftWedge q a y) : ExteriorAlgebra B (Ω[B⁄A]))
    - ((sourceDifferential S 1 ((exteriorPower.oneEquiv B (Ω[B⁄A])).symm a) :
            ExteriorAlgebra B (Ω[B⁄A])) * (y : ExteriorAlgebra B (Ω[B⁄A]))
      - (exteriorPower.ιMulti B 1 (fun _ => a) : ExteriorAlgebra B (Ω[B⁄A]))
          * (sourceDifferential S q y : ExteriorAlgebra B (Ω[B⁄A])))

private lemma leibnizDefect_zero_right (S : SourceDeRham A B) (q : ℕ) (a : Ω[B⁄A]) :
    leibnizDefect S q a 0 = 0 := by
  simp [leibnizDefect]

private lemma leibnizDefect_zero_left (S : SourceDeRham A B) (q : ℕ)
    (y : ⋀[B]^q (Ω[B⁄A])) : leibnizDefect S q 0 y = 0 := by
  have h0 : (exteriorPower.ιMulti B 1 (fun _ => (0 : Ω[B⁄A])) : ExteriorAlgebra B (Ω[B⁄A]))
      = 0 := by rw [coe_ιMulti_one, map_zero]
  simp [leibnizDefect, h0]

private lemma leibnizDefect_add_left (S : SourceDeRham A B) (q : ℕ) (a₁ a₂ : Ω[B⁄A])
    (y : ⋀[B]^q (Ω[B⁄A])) :
    leibnizDefect S q (a₁ + a₂) y = leibnizDefect S q a₁ y + leibnizDefect S q a₂ y := by
  simp only [leibnizDefect, map_add, LinearMap.add_apply, Submodule.coe_add,
    coe_ιMulti_one_add, add_mul]
  abel

private lemma leibnizDefect_add_right (S : SourceDeRham A B) (q : ℕ) (a : Ω[B⁄A])
    (y₁ y₂ : ⋀[B]^q (Ω[B⁄A])) :
    leibnizDefect S q a (y₁ + y₂) = leibnizDefect S q a y₁ + leibnizDefect S q a y₂ := by
  simp only [leibnizDefect, map_add, Submodule.coe_add, mul_add]
  abel

/-- The graded Leibniz rule holds on generators: for `a = c · d e₀` and
`y = b₀ · (d b₁ ∧ ⋯ ∧ d b_q)` the defining rule of `S.d` computes all three differentials, the
Leibniz rule for `D (c · b₀)` matches the two leading scalars, and what is left of the identity is
the antisymmetry `d b₀ ∧ d e₀ ∧ ⋯ = - d e₀ ∧ d b₀ ∧ ⋯` of the exterior algebra. -/
private lemma leibnizDefect_smul_D_smul_ιMulti_D (S : SourceDeRham A B) (q : ℕ) (c e0 b0 : B)
    (b : Fin q → B) :
    leibnizDefect S q (c • KaehlerDifferential.D A B e0)
      (b0 • exteriorPower.ιMulti B q fun i => KaehlerDifferential.D A B (b i)) = 0 := by
  set D := KaehlerDifferential.D A B with hD
  set e := exteriorPower.oneEquiv B (Ω[B⁄A]) with he
  have consD : ∀ (n : ℕ) (k : Ω[B⁄A]) (v : Fin n → Ω[B⁄A]),
      (ExteriorAlgebra.ι B k) * (exteriorPower.ιMulti B n v : ExteriorAlgebra B (Ω[B⁄A]))
        = (exteriorPower.ιMulti B (n + 1) (Fin.cons k v) : ExteriorAlgebra B (Ω[B⁄A])) :=
    fun n k v => (coe_ιMulti_cons n k v).symm
  set W := exteriorPower.ιMulti B q (fun i => D (b i)) with hW
  have hT2 : sourceDifferential S q (b0 • W)
      = exteriorPower.ιMulti B (q + 1) (fun i => D ((Fin.cons b0 b : Fin (q + 1) → B) i)) :=
    sourceDifferential_srcGen S q (Fin.cons b0 b)
  have hT1 : sourceDifferential S 1 (e.symm (c • D e0))
      = exteriorPower.ιMulti B 2 ![D c, D e0] := sourceDifferential_one_smul_D S c e0
  have hLHS : sourceDifferential S (q + 1)
      ((c * b0) • exteriorPower.ιMulti B (q + 1)
        (fun i => D ((Fin.cons e0 b : Fin (q + 1) → B) i)))
      = exteriorPower.ιMulti B (q + 2)
          (fun i => D ((Fin.cons (c * b0) (Fin.cons e0 b) : Fin (q + 2) → B) i)) :=
    sourceDifferential_srcGen S (q + 1) (Fin.cons (c * b0) (Fin.cons e0 b))
  have hDcons : ∀ (x : B) (n : ℕ) (v : Fin n → B),
      (fun i => D ((Fin.cons x v : Fin (n + 1) → B) i)) =
        Fin.cons (D x) (fun i => D (v i)) := by
    intro x n v; funext i; refine Fin.cases ?_ ?_ i <;> simp
  have hwedeq : leftWedge q (c • D e0) (b0 • W)
      = (c * b0) • exteriorPower.ιMulti B (q + 1)
          (fun i => D ((Fin.cons e0 b : Fin (q + 1) → B) i)) := by
    refine Subtype.ext ?_
    rw [leftWedge_coe, map_smul, hW]
    push_cast
    rw [smul_mul_assoc, mul_smul_comm, consD q (D e0) (fun i => D (b i)), hDcons e0 q b,
      smul_smul]
  set Ta := (exteriorPower.ιMulti B (q + 2)
    (Fin.cons (D b0) (Fin.cons (D e0) (fun i => D (b i)))) :
      ExteriorAlgebra B (Ω[B⁄A])) with hTa
  set Tb := (exteriorPower.ιMulti B (q + 2)
    (Fin.cons (D c) (Fin.cons (D e0) (fun i => D (b i)))) :
      ExteriorAlgebra B (Ω[B⁄A])) with hTb
  set Td := (exteriorPower.ιMulti B (q + 2)
    (Fin.cons (D e0) (Fin.cons (D b0) (fun i => D (b i)))) :
      ExteriorAlgebra B (Ω[B⁄A])) with hTd
  have hLHSexp : (exteriorPower.ιMulti B (q + 2)
      (fun i => D ((Fin.cons (c * b0) (Fin.cons e0 b) : Fin (q + 2) → B) i))
        : ExteriorAlgebra B (Ω[B⁄A]))
      = c • Ta + b0 • Tb := by
    rw [hDcons (c * b0) (q + 1) (Fin.cons e0 b)]
    rw [← consD (q + 1) (D (c * b0)) (fun i => D ((Fin.cons e0 b : Fin (q + 1) → B) i))]
    rw [hD, Derivation.leibniz, map_add, map_smul, map_smul]
    rw [add_mul, smul_mul_assoc, smul_mul_assoc]
    rw [consD (q + 1) (D b0) (fun i => D ((Fin.cons e0 b : Fin (q + 1) → B) i)),
        consD (q + 1) (D c) (fun i => D ((Fin.cons e0 b : Fin (q + 1) → B) i))]
    rw [hTa, hTb, hDcons e0 q b]
  have hT1prod : (exteriorPower.ιMulti B 2 ![D c, D e0] : ExteriorAlgebra B (Ω[B⁄A]))
      * ((b0 • W : ⋀[B]^q (Ω[B⁄A])) : ExteriorAlgebra B (Ω[B⁄A])) = b0 • Tb := by
    rw [hW]
    rw [show ((b0 • exteriorPower.ιMulti B q (fun i => D (b i)) : ⋀[B]^q (Ω[B⁄A]))
          : ExteriorAlgebra B (Ω[B⁄A]))
        = b0 • (exteriorPower.ιMulti B q (fun i => D (b i)) : ExteriorAlgebra B (Ω[B⁄A]))
            by push_cast; ring_nf]
    rw [show (exteriorPower.ιMulti B 2 ![D c, D e0] : ExteriorAlgebra B (Ω[B⁄A]))
        = ExteriorAlgebra.ι B (D c) * ExteriorAlgebra.ι B (D e0) by
      rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply, List.ofFn_succ,
        List.ofFn_succ, List.ofFn_zero]; simp]
    rw [mul_smul_comm, mul_assoc, consD q (D e0) (fun i => D (b i)),
      consD (q + 1) (D c) (Fin.cons (D e0) (fun i => D (b i)))]
  have hT2prod : (exteriorPower.ιMulti B 1 (fun _ => c • D e0) : ExteriorAlgebra B (Ω[B⁄A]))
      * (exteriorPower.ιMulti B (q + 1) (fun i => D ((Fin.cons b0 b : Fin (q + 1) → B) i))
          : ExteriorAlgebra B (Ω[B⁄A])) = c • Td := by
    rw [coe_ιMulti_one_smul, coe_ιMulti_one, smul_mul_assoc, hDcons b0 q b,
      consD (q + 1) (D e0) (Fin.cons (D b0) (fun i => D (b i)))]
  have hTaTd : Ta = - Td := by
    rw [hTa, hTd]
    rw [exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe]
    have h01 : (0 : Fin (q + 2)) ≠ 1 := by
      rw [Ne, Fin.ext_iff]; simp
    have hswap := (ExteriorAlgebra.ιMulti B (q + 2)).map_swap
      (Fin.cons (D e0) (Fin.cons (D b0) (fun i => D (b i)))) (i := 0) (j := 1) h01
    rw [← hswap]
    congr 1
    funext i
    refine Fin.cases ?_ ?_ i
    · simp [Equiv.swap_apply_left]
    · intro j
      refine Fin.cases ?_ ?_ j
      · simp [Equiv.swap_apply_right]
      · intro k
        rw [Function.comp_apply]
        rw [show Equiv.swap (0 : Fin (q + 2)) 1 k.succ.succ = k.succ.succ from
          Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])]
        simp
  show (sourceDifferential S (q + 1) (leftWedge q (c • D e0) (b0 • W)) :
        ExteriorAlgebra B (Ω[B⁄A]))
      - ((sourceDifferential S 1 (e.symm (c • D e0)) : ExteriorAlgebra B (Ω[B⁄A]))
          * ((b0 • W : ⋀[B]^q (Ω[B⁄A])) : ExteriorAlgebra B (Ω[B⁄A]))
        - (exteriorPower.ιMulti B 1 (fun _ => c • D e0) : ExteriorAlgebra B (Ω[B⁄A]))
            * (sourceDifferential S q (b0 • W) : ExteriorAlgebra B (Ω[B⁄A]))) = 0
  rw [hwedeq, hLHS, hT1, hT2, hLHSexp, hT1prod, hT2prod, hTaTd]
  rw [smul_neg]; abel

/-- The graded Leibniz rule in degrees `(1, q)`, in the form that the defect vanishes: it is
additive in each argument, and the `B`-module generators of `Ω_{B/A}` and of `⋀^q_B Ω_{B/A}` are
the pairs settled by `leibnizDefect_smul_D_smul_ιMulti_D`.  A scalar is absorbed into a generator
rather than pulled out, since the defect is additive but not homogeneous. -/
private lemma leibnizDefect_eq_zero (S : SourceDeRham A B) (q : ℕ) (a : Ω[B⁄A])
    (y : ⋀[B]^q (Ω[B⁄A])) : leibnizDefect S q a y = 0 := by
  set D := KaehlerDifferential.D A B with hD
  have Dwedge_span : Submodule.span B (Set.range (fun b : Fin q → B =>
      exteriorPower.ιMulti B q (fun i => D (b i)))) = (⊤ : Submodule B (⋀[B]^q (Ω[B⁄A]))) := by
    rw [hD]
    exact span_range_ιMulti_eq_top (KaehlerDifferential.D A B)
      (KaehlerDifferential.span_range_derivation A B) q
  have mainζ : ∀ (c : B) (e0 : B) (y : ⋀[B]^q (Ω[B⁄A])),
      leibnizDefect S q (c • D e0) y = 0 := by
    intro c e0 y
    have hspan : y ∈ Submodule.span B (Set.range (fun b : Fin q → B =>
        exteriorPower.ιMulti B q (fun i => D (b i)))) := by
      rw [Dwedge_span]; exact Submodule.mem_top
    suffices H : ∀ y' ∈ Submodule.span B (Set.range (fun b : Fin q → B =>
        exteriorPower.ιMulti B q (fun i => D (b i)))),
        ∀ (b0 : B), leibnizDefect S q (c • D e0) (b0 • y') = 0 by
      have := H y hspan 1; rwa [one_smul] at this
    intro y' hy'
    induction hy' using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨b, rfl⟩ := hv
        intro b0; exact leibnizDefect_smul_D_smul_ιMulti_D S q c e0 b0 b
    | zero => intro b0; rw [smul_zero, leibnizDefect_zero_right S]
    | add v w hv hw ihv ihw =>
        intro b0; rw [smul_add, leibnizDefect_add_right S, ihv b0, ihw b0, add_zero]
    | smul d v hv ih =>
        intro b0; rw [smul_smul, ih (b0 * d)]
  have hspan : a ∈ Submodule.span B (Set.range D) := by
    rw [KaehlerDifferential.span_range_derivation]; exact Submodule.mem_top
  suffices H : ∀ a' ∈ Submodule.span B (Set.range D),
      ∀ (c : B) (y : ⋀[B]^q (Ω[B⁄A])), leibnizDefect S q (c • a') y = 0 by
    have := H a hspan 1 y; rwa [one_smul] at this
  intro a' ha'
  induction ha' using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨e0, rfl⟩ := hv
      intro c y; exact mainζ c e0 y
  | zero => intro c y; rw [smul_zero, leibnizDefect_zero_left S]
  | add v w hv hw ihv ihw =>
      intro c y; rw [smul_add, leibnizDefect_add_left S, ihv c y, ihw c y, add_zero]
  | smul d v hv ih =>
      intro c y; rw [smul_smul, ih (c * d) y]

/-- The graded Leibniz rule in degrees `(1, q)`: for `ω : Ω_{B/A}`, seen in degree `1` via
`oneEquiv.symm`, and `ζ : ⋀^q`, with `z : ⋀^{q+1}` the wedge `ω ∧ ζ`,
`d_{B/A}(ω ∧ ζ) = (d_{B/A} ω) ∧ ζ − ω ∧ (d_{B/A} ζ)`, the sign being `(-1)^{deg ω} = -1`.
Both the hypothesis on `z` and the conclusion are stated inside `ExteriorAlgebra B Ω_{B/A}`,
where no degree coercion intervenes; the coercion `↑ : ⋀^n → ExteriorAlgebra` is
`Submodule.subtype`, hence injective, so this is equivalent to the graded equation. -/
private theorem coe_d_wedge_one (S : SourceDeRham A B) (q : ℕ) (ω : Ω[B⁄A])
    (ζ : ⋀[B]^q (Ω[B⁄A])) (z : ⋀[B]^(q + 1) (Ω[B⁄A]))
    (hz : (z : ExteriorAlgebra B (Ω[B⁄A]))
      = (exteriorPower.ιMulti B 1 (fun _ => ω) : ExteriorAlgebra B (Ω[B⁄A]))
          * (ζ : ExteriorAlgebra B (Ω[B⁄A]))) :
    (sourceDifferential S (q + 1) z : ExteriorAlgebra B (Ω[B⁄A]))
      = (sourceDifferential S 1 ((exteriorPower.oneEquiv B (Ω[B⁄A])).symm ω) :
            ExteriorAlgebra B (Ω[B⁄A])) * (ζ : ExteriorAlgebra B (Ω[B⁄A]))
        - (exteriorPower.ιMulti B 1 (fun _ => ω) : ExteriorAlgebra B (Ω[B⁄A]))
            * (sourceDifferential S q ζ : ExteriorAlgebra B (Ω[B⁄A])) := by
  have hzeq : z = leftWedge q ω ζ := by
    refine Subtype.ext ?_
    rw [hz, leftWedge_coe, coe_ιMulti_one]
  rw [hzeq]
  exact eq_of_sub_eq_zero (leibnizDefect_eq_zero S q ω ζ)

private lemma target_leftWedge_map
    (pi : Ω[B⁄A] →ₗ[B] Omega) (q : ℕ)
    (a : Ω[B⁄A]) (z : ⋀[B]^q (Ω[B⁄A])) :
    exteriorPower.map (q + 1) pi (leftWedge q a z) =
      leftWedge q (pi a) (exteriorPower.map q pi z) := by
  apply Subtype.ext
  rw [leftWedge_coe, exteriorPower.coe_map, leftWedge_coe]
  simp only [map_mul, ExteriorAlgebra.map_apply_ι]
  rw [← exteriorPower.coe_map pi z]

/-- Right exterior multiplication of a two-form by a fixed `p`-form. -/
private noncomputable def twoFormRightMul (p : ℕ) (omega : ⋀[B]^p Omega) :
    (⋀[B]^2 Omega) →ₗ[B] ⋀[B]^(p + 2) Omega :=
  { toFun := fun x => ⟨(x : ExteriorAlgebra B Omega) * (omega : ExteriorAlgebra B Omega), by
      have hm := SetLike.mul_mem_graded x.2 omega.2
      simpa [Nat.add_comm] using hm⟩
    map_add' := by
      intro x y
      apply Subtype.ext
      simp only [Submodule.coe_add, add_mul]
    map_smul' := by
      intro c x
      apply Subtype.ext
      change (c • (x : ExteriorAlgebra B Omega)) * (omega : ExteriorAlgebra B Omega) =
        c • ((x : ExteriorAlgebra B Omega) * (omega : ExteriorAlgebra B Omega))
      rw [smul_mul_assoc] }

private theorem twoFormRightMul_coe (p : ℕ) (omega : ⋀[B]^p Omega)
    (x : ⋀[B]^2 Omega) :
    (twoFormRightMul p omega x : ExteriorAlgebra B Omega) =
      (x : ExteriorAlgebra B Omega) * (omega : ExteriorAlgebra B Omega) := rfl

private theorem twoFormRightMul_leftWedge (p : ℕ) (omega : ⋀[B]^p Omega)
    (eta xi : Omega) :
    twoFormRightMul p omega
        (leftWedge 1 eta ((exteriorPower.oneEquiv B Omega).symm xi)) =
      leftWedge (p + 1) eta (leftWedge p xi omega) := by
  apply Subtype.ext
  rw [twoFormRightMul_coe, leftWedge_coe, leftWedge_coe, leftWedge_coe]
  simp [exteriorPower.oneEquiv_symm_apply, mul_assoc]

/-- The graded Leibniz rule for the descended differential, on forms coming from `Ω_{B/A}`: it is
the rule for `d_{B/A}` pushed through `⋀^p π`, which intertwines the two differentials. -/
private theorem descended_leftWedge_leibniz
    (S : SourceDeRham A B) (pi : Ω[B⁄A] →ₗ[B] Omega)
    (d : ∀ p, TgtA A B Omega p →ₗ[A] TgtA A B Omega (p + 1))
    (hcomm : S.Commutes pi d) (q : ℕ)
    (a : Ω[B⁄A]) (z : ⋀[B]^q (Ω[B⁄A])) :
    (descendedDifferential d (q + 1) (leftWedge q (pi a) (exteriorPower.map q pi z)) :
        ExteriorAlgebra B Omega) =
      (descendedDifferential d 1 ((exteriorPower.oneEquiv B Omega).symm (pi a)) :
            ExteriorAlgebra B Omega)
          * ((exteriorPower.map q pi z : ⋀[B]^q Omega) : ExteriorAlgebra B Omega) -
        ExteriorAlgebra.ι B (pi a) *
          (descendedDifferential d q (exteriorPower.map q pi z) : ExteriorAlgebra B Omega) := by
  have hC0 := descendedDifferential_commutes S pi d hcomm (q + 1) (leftWedge q a z)
  rw [target_leftWedge_map pi q a z] at hC0
  have hOne : exteriorPower.map 1 pi ((exteriorPower.oneEquiv B (Ω[B⁄A])).symm a) =
      (exteriorPower.oneEquiv B Omega).symm (pi a) := by
    apply (exteriorPower.oneEquiv B Omega).injective
    have h := LinearMap.congr_fun (exteriorPower.oneEquiv_naturality pi)
      ((exteriorPower.oneEquiv B (Ω[B⁄A])).symm a)
    simpa using h
  have hD1 := descendedDifferential_commutes S pi d hcomm 1
    ((exteriorPower.oneEquiv B (Ω[B⁄A])).symm a)
  rw [hOne] at hD1
  have hDq := descendedDifferential_commutes S pi d hcomm q z
  have hz : (leftWedge q a z : ExteriorAlgebra B (Ω[B⁄A])) =
      (exteriorPower.ιMulti B 1 (fun _ => a) : ExteriorAlgebra B (Ω[B⁄A])) *
        (z : ExteriorAlgebra B (Ω[B⁄A])) := by
    rw [leftWedge_coe, coe_ιMulti_one]
  have hsrcmap := congrArg (ExteriorAlgebra.map pi) (coe_d_wedge_one S q a z (leftWedge q a z) hz)
  rw [map_sub, map_mul, map_mul, coe_ιMulti_one, ExteriorAlgebra.map_apply_ι,
    ← exteriorPower.coe_map pi (sourceDifferential S (q + 1) (leftWedge q a z)),
    ← exteriorPower.coe_map pi z,
    ← exteriorPower.coe_map pi
      (sourceDifferential S 1 ((exteriorPower.oneEquiv B (Ω[B⁄A])).symm a)),
    ← exteriorPower.coe_map pi (sourceDifferential S q z)] at hsrcmap
  rw [hC0, hD1, hDq]
  exact hsrcmap

/-- The graded Leibniz rule for the descended differential, on all forms: `π` is surjective, hence
so is each `⋀^p π`. -/
private theorem target_deRham_leftWedge_leibniz
    (S : SourceDeRham A B) (pi : Ω[B⁄A] →ₗ[B] Omega)
    (hpi : Function.Surjective pi)
    (d : ∀ p, TgtA A B Omega p →ₗ[A] TgtA A B Omega (p + 1))
    (hcomm : S.Commutes pi d) (q : ℕ) (a : Omega) (z : ⋀[B]^q Omega) :
    (descendedDifferential d (q + 1) (leftWedge q a z) : ExteriorAlgebra B Omega) =
      (descendedDifferential d 1 ((exteriorPower.oneEquiv B Omega).symm a) :
            ExteriorAlgebra B Omega)
          * (z : ExteriorAlgebra B Omega) -
        ExteriorAlgebra.ι B a * (descendedDifferential d q z : ExteriorAlgebra B Omega) := by
  obtain ⟨a₀, rfl⟩ := hpi a
  obtain ⟨z₀, rfl⟩ := exteriorPower.map_surjective hpi z
  exact descended_leftWedge_leibniz S pi d hcomm q a₀ z₀

/-- The descended differential is a complex, because the de Rham differential of `B` over `A` is
and the two are intertwined by the surjections `⋀^p π`. -/
private theorem target_deRham_d_squared_eq_zero
    (S : SourceDeRham A B) (pi : Ω[B⁄A] →ₗ[B] Omega)
    (hpi : Function.Surjective pi)
    (d : ∀ p, TgtA A B Omega p →ₗ[A] TgtA A B Omega (p + 1))
    (hcomm : S.Commutes pi d) (q : ℕ) (z : ⋀[B]^q Omega) :
    descendedDifferential d (q + 1) (descendedDifferential d q z) = 0 := by
  obtain ⟨z₀, rfl⟩ := exteriorPower.map_surjective hpi z
  rw [descendedDifferential_commutes S pi d hcomm q z₀,
    descendedDifferential_commutes S pi d hcomm (q + 1) (sourceDifferential S q z₀),
    sourceDifferential_comp_self, map_zero]

private theorem tensor_twoFormRightMul_comp_leftWedge
    (p : ℕ) (omega : ⋀[B]^p Omega) (eta : ⋀[B]^1 Omega)
    (T : M ⊗[B] Omega) :
    TensorProduct.map LinearMap.id (twoFormRightMul p omega)
        (TensorProduct.map LinearMap.id ((leftWedge 1).flip eta) T) =
      TensorProduct.map LinearMap.id
        ((leftWedge (p + 1)).flip
          (leftWedge p (exteriorPower.oneEquiv B Omega eta) omega)) T := by
  induction T using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul x y =>
      simp only [TensorProduct.map_tmul]
      have h := twoFormRightMul_leftWedge p omega y (exteriorPower.oneEquiv B Omega eta)
      simpa using congrArg (fun z => x ⊗ₜ[B] z) h

/-- One step of the computation of the composite of two extended differentials: on a pure tensor
`m ⊗ (η ∧ ω)` the graded Leibniz rule turns the extension in degree `p + 1` into right
multiplication by `ω` applied to the extension in degree `1`. -/
private theorem extendedConnection_wedge_step
    (S : SourceDeRham A B) (pi : Ω[B⁄A] →ₗ[B] Omega)
    (nabla : Connection A B pi M)
    (E : ExtendedConnection S pi nabla)
    (hleibniz : ∀ q (a : Omega) (z : ⋀[B]^q Omega),
      (descendedDifferential E.deRhamDifferential (q + 1) (leftWedge q a z) :
            ExteriorAlgebra B Omega) =
        (descendedDifferential E.deRhamDifferential 1 ((exteriorPower.oneEquiv B Omega).symm a) :
              ExteriorAlgebra B Omega) * (z : ExteriorAlgebra B Omega) -
          ExteriorAlgebra.ι B a *
            (descendedDifferential E.deRhamDifferential q z : ExteriorAlgebra B Omega))
    (p : ℕ) (omega : ⋀[B]^p Omega) (T : M ⊗[B] Omega) :
    RestrictScalars.addEquiv A B (M ⊗[B] ⋀[B]^(p + 1 + 1) Omega)
        (E.toLinearMap (p + 1)
          ((RestrictScalars.addEquiv A B (M ⊗[B] ⋀[B]^(p + 1) Omega)).symm
            (TensorProduct.map LinearMap.id ((leftWedge p).flip omega) T))) +
      TensorProduct.map LinearMap.id
        ((leftWedge (p + 1)).flip (descendedDifferential E.deRhamDifferential p omega)) T =
    TensorProduct.map LinearMap.id (twoFormRightMul p omega)
      (RestrictScalars.addEquiv A B (M ⊗[B] ⋀[B]^2 Omega)
        (E.toLinearMap 1
          ((RestrictScalars.addEquiv A B (M ⊗[B] ⋀[B]^1 Omega)).symm
            (TensorProduct.map LinearMap.id
              (exteriorPower.oneEquiv B Omega).symm.toLinearMap T)))) := by
  let L : M ⊗[B] Omega →ₗ[B] M ⊗[B] ⋀[B]^(p + 1) Omega :=
    TensorProduct.map LinearMap.id ((leftWedge p).flip omega)
  let R : M ⊗[B] Omega →ₗ[B] M ⊗[B] ⋀[B]^(p + 1 + 1) Omega :=
    TensorProduct.map LinearMap.id
      ((leftWedge (p + 1)).flip (descendedDifferential E.deRhamDifferential p omega))
  let U : M ⊗[B] Omega →ₗ[B] M ⊗[B] ⋀[B]^1 Omega :=
    TensorProduct.map LinearMap.id
    (exteriorPower.oneEquiv B Omega).symm.toLinearMap
  let V : M ⊗[B] ⋀[B]^2 Omega →ₗ[B] M ⊗[B] ⋀[B]^(p + 2) Omega :=
    TensorProduct.map LinearMap.id (twoFormRightMul p omega)
  let inL := RestrictScalars.addEquiv A B (M ⊗[B] ⋀[B]^(p + 1) Omega)
  let inU := RestrictScalars.addEquiv A B (M ⊗[B] ⋀[B]^1 Omega)
  let out2 := RestrictScalars.addEquiv A B (M ⊗[B] ⋀[B]^2 Omega)
  let out := RestrictScalars.addEquiv A B (M ⊗[B] ⋀[B]^(p + 1 + 1) Omega)
  show out (E.toLinearMap (p + 1) (inL.symm (L T))) + R T =
    V (out2 (E.toLinearMap 1 (inU.symm (U T))))
  induction T using TensorProduct.induction_on with
  | zero =>
      rw [L.map_zero, R.map_zero, U.map_zero,
        inL.symm.map_zero, (E.toLinearMap (p + 1)).map_zero, out.map_zero,
        inU.symm.map_zero, (E.toLinearMap 1).map_zero, out2.map_zero,
        V.map_zero]
      simp
  | add x y hx hy =>
      rw [L.map_add, R.map_add, U.map_add,
        inL.symm.map_add, inU.symm.map_add,
        (E.toLinearMap (p + 1)).map_add, out.map_add,
        (E.toLinearMap 1).map_add, out2.map_add, V.map_add]
      calc
        _ = (out (E.toLinearMap (p + 1) (inL.symm (L x))) + R x) +
            (out (E.toLinearMap (p + 1) (inL.symm (L y))) + R y) := by abel
        _ = V (out2 (E.toLinearMap 1 (inU.symm (U x)))) +
            V (out2 (E.toLinearMap 1 (inU.symm (U y)))) := by rw [hx, hy]
  | tmul m eta =>
      dsimp only [L, R, U, V, inL, inU, out2, out]
      let e1 := (exteriorPower.oneEquiv B Omega).symm eta
      have hFirst :
          RestrictScalars.addEquiv A B
              (M ⊗[B] ⋀[B]^(p + 1 + 1) Omega)
              (E.toLinearMap (p + 1) (m ⊗ₜ[B] leftWedge p eta omega)) =
            TensorProduct.map LinearMap.id
                ((leftWedge (p + 1)).flip (leftWedge p eta omega)) (nabla m) +
              m ⊗ₜ[B]
                descendedDifferential E.deRhamDifferential (p + 1) (leftWedge p eta omega) :=
        E.map_tmul (p + 1) m (leftWedge p eta omega)
      have hDegreeOne :
          RestrictScalars.addEquiv A B (M ⊗[B] ⋀[B]^(1 + 1) Omega)
              (E.toLinearMap 1 (m ⊗ₜ[B] e1)) =
            TensorProduct.map LinearMap.id ((leftWedge 1).flip e1) (nabla m) +
              m ⊗ₜ[B] descendedDifferential E.deRhamDifferential 1 e1 :=
        E.map_tmul 1 m e1
      have hForms :
          descendedDifferential E.deRhamDifferential (p + 1) (leftWedge p eta omega) +
              leftWedge (p + 1) eta (descendedDifferential E.deRhamDifferential p omega) =
            twoFormRightMul p omega (descendedDifferential E.deRhamDifferential 1 e1) := by
        apply Subtype.ext
        rw [Submodule.coe_add, hleibniz p eta omega, leftWedge_coe, twoFormRightMul_coe,
          sub_add_cancel]
      have hInputFirst :
          (RestrictScalars.addEquiv A B
            (M ⊗[B] ⋀[B]^(p + 1) Omega)).symm
            (m ⊗ₜ[B] leftWedge p eta omega) =
          m ⊗ₜ[B] leftWedge p eta omega := rfl
      have hInputOne :
          (RestrictScalars.addEquiv A B (M ⊗[B] ⋀[B]^1 Omega)).symm
            (TensorProduct.map LinearMap.id
              (exteriorPower.oneEquiv B Omega).symm.toLinearMap
              (m ⊗ₜ[B] eta)) = m ⊗ₜ[B] e1 := rfl
      rw [show TensorProduct.map LinearMap.id ((leftWedge p).flip omega) (m ⊗ₜ[B] eta) =
            m ⊗ₜ[B] leftWedge p eta omega from rfl]
      rw [hInputFirst, hInputOne, hFirst]
      simp only [TensorProduct.map_tmul, LinearMap.id_apply]
      rw [hDegreeOne, map_add,
        tensor_twoFormRightMul_comp_leftWedge p omega e1 (nabla m)]
      simp only [TensorProduct.map_tmul, LinearMap.id_apply]
      have hTensor :
          m ⊗ₜ[B] descendedDifferential E.deRhamDifferential (p + 1) (leftWedge p eta omega) +
              m ⊗ₜ[B] leftWedge (p + 1) eta (descendedDifferential E.deRhamDifferential p omega) =
            m ⊗ₜ[B] twoFormRightMul p omega (descendedDifferential E.deRhamDifferential 1 e1) := by
        rw [← TensorProduct.tmul_add]
        exact congrArg (fun z => m ⊗ₜ[B] z) hForms
      calc
        _ = (TensorProduct.map LinearMap.id
                ((leftWedge (p + 1)).flip (leftWedge p eta omega)) (nabla m)) +
              (m ⊗ₜ[B] descendedDifferential E.deRhamDifferential (p + 1) (leftWedge p eta omega) +
                m ⊗ₜ[B] leftWedge (p + 1) eta
                  (descendedDifferential E.deRhamDifferential p omega)) := by
          abel
        _ = (TensorProduct.map LinearMap.id
                ((leftWedge (p + 1)).flip
                  (leftWedge p ((exteriorPower.oneEquiv B Omega) e1) omega)) (nabla m)) +
              m ⊗ₜ[B] twoFormRightMul p omega
                (descendedDifferential E.deRhamDifferential 1 e1) := by
          have hc := congrArg (fun z =>
            (TensorProduct.map LinearMap.id
                ((leftWedge (p + 1)).flip (leftWedge p eta omega)) (nabla m)) + z)
            hTensor
          simpa [e1] using hc

/-- The consecutive extended differentials of an integrable connection compose to zero, so an
integrable connection makes `M ⊗_B Ω^•` a complex.

`S` is not de Rham data: it can only be `Stacks.DeRham.DifferentialDescent.sourceDeRham A B`, the
de Rham complex of [Stacks, Tag 0FKF], by
`Stacks.DeRham.DifferentialDescent.SourceDeRham.eq_sourceDeRham`. -/
@[stacks 07I0 "connection_de_rham_complex. The last clause of the tag: for an integrable \
connection the extended differentials compose to zero, so M ⊗ Ω^• is a complex. The de Rham \
differentials of B over A are constructed in Stacks.DeRham.DifferentialDescent.sourceDeRham and \
SourceDeRham.eq_sourceDeRham proves the binder S admits that term alone"]
public theorem extendedConnection_comp_self_eq_zero
    (S : SourceDeRham A B) (pi : Ω[B⁄A] →ₗ[B] Omega)
    (hpi : Function.Surjective pi) (hgen : S.GenerationHypothesis pi)
    (nabla : Connection A B pi M)
    (hintegrable : Connection.IsIntegrable S pi hpi hgen nabla) (p : ℕ) :
    ((extendedConnection S pi hpi hgen nabla).toLinearMap (p + 1)).comp
      ((extendedConnection S pi hpi hgen nabla).toLinearMap p) = 0 := by
  let E := extendedConnection S pi hpi hgen nabla
  apply LinearMap.ext
  intro x
  let ei := RestrictScalars.addEquiv A B (M ⊗[B] ⋀[B]^p Omega)
  let eo := RestrictScalars.addEquiv A B (M ⊗[B] (⋀[B]^(p + 1 + 1) Omega))
  apply eo.injective
  have hbody : ∀ y : M ⊗[B] ⋀[B]^p Omega,
      eo (E.toLinearMap (p + 1) (E.toLinearMap p (ei.symm y))) = 0 := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz =>
        simp only [map_add]
        rw [hy, hz]
        simp
    | tmul m omega =>
        show eo (E.toLinearMap (p + 1) (E.toLinearMap p (m ⊗ₜ[B] omega))) = 0
        let em := RestrictScalars.addEquiv A B (M ⊗[B] (⋀[B]^(p + 1) Omega))
        let omega1 := descendedDifferential E.deRhamDifferential p omega
        have hfirst : E.toLinearMap p (m ⊗ₜ[B] omega) = em.symm
            (TensorProduct.map LinearMap.id ((leftWedge p).flip omega) (nabla m) +
              m ⊗ₜ[B] omega1) :=
          em.injective (E.map_tmul p m omega)
        rw [hfirst]
        simp only [em, map_add]
        have hsecond : E.toLinearMap (p + 1) (em.symm (m ⊗ₜ[B] omega1)) = eo.symm
              (TensorProduct.map LinearMap.id
                  ((leftWedge (p + 1)).flip omega1) (nabla m) +
                m ⊗ₜ[B] descendedDifferential E.deRhamDifferential (p + 1) omega1) :=
          eo.injective (E.map_tmul (p + 1) m omega1)
        rw [hsecond]
        simp only [eo, AddEquiv.apply_symm_apply, map_add]
        have hleibniz := target_deRham_leftWedge_leibniz S pi hpi
          E.deRhamDifferential E.commutes
        have hstep := extendedConnection_wedge_step S pi nabla E hleibniz p omega
          (nabla m)
        have hD2 := target_deRham_d_squared_eq_zero S pi hpi
          E.deRhamDifferential E.commutes p omega
        have hcurv := hintegrable.comp_eq_zero m
        have hcurv' :
            RestrictScalars.addEquiv A B (M ⊗[B] ⋀[B]^2 Omega)
              (E.toLinearMap 1
                ((RestrictScalars.addEquiv A B (M ⊗[B] ⋀[B]^1 Omega)).symm
                  (TensorProduct.map LinearMap.id
                    (exteriorPower.oneEquiv B Omega).symm.toLinearMap (nabla m)))) = 0 := by
          convert congrArg
            (RestrictScalars.addEquiv A B (M ⊗[B] ⋀[B]^2 Omega)) hcurv using 1 <;> rfl
        have hcurvMul := congrArg
          (TensorProduct.map LinearMap.id (twoFormRightMul p omega)) hcurv'
        rw [hD2]
        simp only [TensorProduct.tmul_zero, add_zero]
        rw [hstep, hcurvMul]
        simp
  exact hbody x

end ConnectionDeRham

/-! ### The divided power de Rham complex -/

section DividedPowerDeRham

universe u v

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable {J : Ideal B} (hJ : DividedPowers J)

/-- The relation `d(δ_{n+1}(x)) - δ_n(x) · dx` imposed on Kähler differentials. -/
public noncomputable def dividedPowerDifferentialRelation (x : J) (n : ℕ) : Ω[B⁄A] :=
  KaehlerDifferential.D A B (hJ.dpow (n + 1) x) -
    hJ.dpow n x • KaehlerDifferential.D A B x

/-- The submodule of Kähler differentials generated by the divided power relations. -/
public noncomputable def dividedPowerDifferentialRelations : Submodule B Ω[B⁄A] :=
  Submodule.span B (Set.range fun z : J × ℕ ↦
    dividedPowerDifferentialRelation hJ z.1 z.2)

/-- The module `Ω¹_{B/A,δ}` of divided power differentials. -/
@[stacks 07HZ "divided_power_de_rham_complex"]
public abbrev dividedPowerDifferentials : Type v :=
  Ω[B⁄A] ⧸ dividedPowerDifferentialRelations (A := A) hJ

/-- The universal divided-power-compatible differential `B → Ω¹_{B/A,δ}`. -/
public noncomputable def dividedPowerDifferential (b : B) :
    dividedPowerDifferentials (A := A) hJ :=
  (dividedPowerDifferentialRelations (A := A) hJ).mkQ (KaehlerDifferential.D A B b)

/-- The universal differential satisfies the divided power relation. -/
@[simp]
public lemma dividedPowerDifferential_dpow (x : J) (n : ℕ) :
    dividedPowerDifferential (A := A) hJ (hJ.dpow (n + 1) x) =
      hJ.dpow n x • dividedPowerDifferential (A := A) hJ x := by
  unfold dividedPowerDifferential
  rw [← sub_eq_zero, ← LinearMap.map_smul]
  show (dividedPowerDifferentialRelations (A := A) hJ).mkQ
    (dividedPowerDifferentialRelation hJ x n) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span (Set.mem_range_self (x, n))

/-- The universal divided power differentials span `Ω¹_{B/A,δ}` over `B`, because the Kähler
differentials `d b` span `Ω[B⁄A]` and the quotient map is surjective. -/
public lemma dividedPowerDifferentials_span :
    Submodule.span B (Set.range (dividedPowerDifferential (A := A) hJ)) = ⊤ := by
  show Submodule.span B (Set.range fun b : B ↦
    (dividedPowerDifferentialRelations (A := A) hJ).mkQ (KaehlerDifferential.D A B b)) = ⊤
  have h := congrArg (Submodule.map (dividedPowerDifferentialRelations (A := A) hJ).mkQ)
    (KaehlerDifferential.span_range_derivation A B)
  simpa only [LinearMap.map_span, ← Set.range_comp, Function.comp_def,
    Submodule.map_top, Submodule.range_mkQ] using h

/-- The module `Ωⁱ_{B/A,δ}`, the `i`-th exterior power of the module of divided
power differentials. -/
@[stacks 07HZ "divided_power_de_rham_complex"]
public abbrev dividedPowerDifferentialForms (i : ℕ) : Type v :=
  ⋀[B]^i (dividedPowerDifferentials (A := A) hJ)

/-- The divided power de Rham complex.  Its differential is characterized on the standard
generators by
`d(f₀ df₁ ∧ ⋯ ∧ dfᵢ) = df₀ ∧ ⋯ ∧ dfᵢ`, and consecutive differentials
compose to zero. -/
@[ext]
public structure DividedPowerDeRhamComplex where
  /-- The differential in degree `i`. -/
  differential : ∀ i,
    RestrictScalars A B (dividedPowerDifferentialForms (A := A) hJ i) →ₗ[A]
      RestrictScalars A B (dividedPowerDifferentialForms (A := A) hJ (i + 1))
  /-- The formula defining the differential on standard generators. -/
  differential_generator : ∀ i (f : Fin (i + 1) → B),
    differential i
        (f 0 • exteriorPower.ιMulti B i
          (fun j ↦ dividedPowerDifferential (A := A) hJ (f j.succ))) =
      exteriorPower.ιMulti B (i + 1)
        (fun j ↦ dividedPowerDifferential (A := A) hJ (f j))
  /-- Consecutive differentials compose to zero. -/
  differential_squared : ∀ i,
    (differential (i + 1)).comp (differential i) = 0


/-- The de Rham complex of `S` over `R` exists: it is
`Stacks.DeRham.DifferentialDescent.sourceDeRham`, the construction of [Stacks, Tag 0FKF]. -/
private lemma source_exists (R S : Type v) [CommRing R] [CommRing S] [Algebra R S] :
    Nonempty (Stacks.DeRham.DifferentialDescent.SourceDeRham R S) :=
  ⟨Stacks.DeRham.DifferentialDescent.sourceDeRham R S⟩

/-- A surjection of `B`-modules out of `Ω[B⁄A]` whose kernel is exactly the submodule of divided
power relations satisfies the generation hypothesis of Tag 07HY: each relation
`d(δ_{n+1} x) - δ_n x · dx` is killed by the map, and its de Rham differential is killed by the
second exterior power of the map. -/
public theorem generationHypothesis_of_ker_eq_relations {R : Type v} [CommRing R] [Algebra R B]
    (S : Stacks.DeRham.DifferentialDescent.SourceDeRham R B) {M : Type v} [AddCommGroup M] [Module B
      M]
    (π : Ω[B⁄R] →ₗ[B] M)
    (hker : LinearMap.ker π = dividedPowerDifferentialRelations (A := R) hJ) :
    S.GenerationHypothesis π := by
  have hpow (x : J) (n : ℕ) :
      π (KaehlerDifferential.D R B (hJ.dpow (n + 1) x)) =
        hJ.dpow n x • π (KaehlerDifferential.D R B x) := by
    have hm : dividedPowerDifferentialRelation (A := R) hJ x n ∈ LinearMap.ker π :=
      hker ▸ Submodule.subset_span (Set.mem_range_self (x, n))
    simpa only [LinearMap.mem_ker, dividedPowerDifferentialRelation, map_sub,
      map_smul, sub_eq_zero] using hm
  have hexact (b : B) :
      sourceDifferential S 1 ((exteriorPower.oneEquiv B Ω[B⁄R]).symm
          (KaehlerDifferential.D R B b)) = 0 := by
    have h := sourceDifferential_one_smul_D S 1 b
    simp only [one_smul, Derivation.map_one_eq_zero] at h
    rw [h]
    exact (exteriorPower.ιMulti B 2).map_coord_zero (i := 0) (by simp)
  apply le_antisymm
  · rw [hker]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, n⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨?_, ?_⟩
    · simp only [dividedPowerDifferentialRelation, map_sub, map_smul, hpow, sub_self]
    · show exteriorPower.map 2 π (sourceDifferential S 1 ((exteriorPower.oneEquiv B Ω[B⁄R]).symm
        (dividedPowerDifferentialRelation (A := R) hJ x n))) = 0
      rw [dividedPowerDifferentialRelation, map_sub, map_sub, hexact, sourceDifferential_one_smul_D,
        map_sub, map_zero, zero_sub, neg_eq_zero, exteriorPower.map_apply_ιMulti]
      have heq : (fun j ↦ π (![KaehlerDifferential.D R B (hJ.dpow n x),
          KaehlerDifferential.D R B x] j)) =
          ![π (KaehlerDifferential.D R B (hJ.dpow n x)),
            π (KaehlerDifferential.D R B x)] := by funext j; fin_cases j <;> rfl
      simp only [Function.comp_def]
      rw [heq]
      show exteriorPower.ιMulti B 2
        ![π (KaehlerDifferential.D R B (hJ.dpow n x)),
          π (KaehlerDifferential.D R B x)] = 0
      cases n with
      | zero =>
          apply (exteriorPower.ιMulti B 2).map_coord_zero (i := 0)
          simp [hJ.dpow_zero x.property]
      | succ n =>
          rw [hpow]
          apply Subtype.ext
          simp [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply]
  · exact Submodule.span_le.mpr (fun _ hω ↦ hω.1)

/-- Replacing the base ring by its image preserves Kähler differentials.  The image lies in
the universe of `B`, allowing us to use descent without equating the universes of `A` and `B`. -/
private lemma image_differentials_equiv :
    ∃ e : Ω[B⁄(algebraMap A B).range] ≃ₗ[B] Ω[B⁄A],
      ∀ b : B, e (KaehlerDifferential.D (algebraMap A B).range B b) =
        KaehlerDifferential.D A B b := by
  let R := (algebraMap A B).range
  let dR : Derivation R B Ω[B⁄A] :=
    { toFun := KaehlerDifferential.D A B
      map_add' := map_add _
      map_smul' := by
        intro c b
        obtain ⟨a, ha⟩ := c.property
        show KaehlerDifferential.D A B ((c : B) * b) =
          (c : B) • KaehlerDifferential.D A B b
        rw [← ha, ← Algebra.smul_def, Derivation.map_smul,
          IsScalarTower.algebraMap_smul]
      map_one_eq_zero' := Derivation.map_one_eq_zero _
      leibniz' := Derivation.leibniz _ }
  let dA : Derivation A B Ω[B⁄R] :=
    { toFun := KaehlerDifferential.D R B
      map_add' := map_add _
      map_smul' := by
        intro a b
        have hz : KaehlerDifferential.D R B (algebraMap A B a) = 0 :=
          (KaehlerDifferential.D R B).map_algebraMap ⟨_, ⟨a, rfl⟩⟩
        rw [Algebra.smul_def, Derivation.leibniz, hz, smul_zero, add_zero,
          IsScalarTower.algebraMap_smul, RingHom.id_apply]
      map_one_eq_zero' := Derivation.map_one_eq_zero _
      leibniz' := Derivation.leibniz _ }
  let f := dR.liftKaehlerDifferential
  let g := dA.liftKaehlerDifferential
  have hf (b : B) : f (KaehlerDifferential.D R B b) = KaehlerDifferential.D A B b :=
    dR.liftKaehlerDifferential_comp_D b
  have hg (b : B) : g (KaehlerDifferential.D A B b) = KaehlerDifferential.D R B b :=
    dA.liftKaehlerDifferential_comp_D b
  have hfg : f.comp g = LinearMap.id := by
    apply LinearMap.ext_on (KaehlerDifferential.span_range_derivation A B)
    rintro _ ⟨b, rfl⟩
    simp only [LinearMap.comp_apply, LinearMap.id_apply, hg, hf]
  have hgf : g.comp f = LinearMap.id := by
    apply LinearMap.ext_on (KaehlerDifferential.span_range_derivation R B)
    rintro _ ⟨b, rfl⟩
    simp only [LinearMap.comp_apply, LinearMap.id_apply, hg, hf]
  exact ⟨LinearEquiv.ofLinearMap f g hfg hgf, hf⟩

/-- Descend the ordinary de Rham complex along the divided-power quotient. -/
private lemma complex_exists : Nonempty (DividedPowerDeRhamComplex (A := A) hJ) := by
  let R := (algebraMap A B).range
  obtain ⟨e, he⟩ := image_differentials_equiv (A := A) (B := B)
  have he' (b : B) : e.symm (KaehlerDifferential.D A B b) =
      KaehlerDifferential.D R B b := by
    apply e.injective
    rw [e.apply_symm_apply, he]
  let π : Ω[B⁄R] →ₗ[B] dividedPowerDifferentials (A := A) hJ :=
    (dividedPowerDifferentialRelations (A := A) hJ).mkQ.comp e.toLinearMap
  have hπ (b : B) : π (KaehlerDifferential.D R B b) =
      dividedPowerDifferential (A := A) hJ b :=
    congrArg (dividedPowerDifferentialRelations (A := A) hJ).mkQ (he b)
  have hsurj : Function.Surjective π :=
    (Submodule.mkQ_surjective _).comp e.surjective
  have hker : LinearMap.ker π = dividedPowerDifferentialRelations (A := R) hJ := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.comap_equiv_eq_map_symm]
    simp only [dividedPowerDifferentialRelations, LinearMap.map_span, ← Set.range_comp,
      Function.comp_def, dividedPowerDifferentialRelation, map_sub, map_smul,
      LinearEquiv.coe_coe]
    congr 2
    funext z
    exact congrArg₂ (fun x y ↦ x - hJ.dpow z.2 z.1 • y)
      (he' (hJ.dpow (z.2 + 1) z.1)) (he' z.1)
  obtain ⟨S⟩ := source_exists R B
  obtain ⟨d, -, hd, -, hsquare⟩ := exists_unique_quotient_deRhamDifferential S π hsurj
    (generationHypothesis_of_ker_eq_relations hJ S π hker)
  let dA : ∀ i, RestrictScalars A B (dividedPowerDifferentialForms (A := A) hJ i) →ₗ[A]
      RestrictScalars A B (dividedPowerDifferentialForms (A := A) hJ (i + 1)) := fun i ↦
    { toFun := d i
      map_add' := (d i).map_add
      map_smul' := by
        intro a ω
        let c : R := ⟨algebraMap A B a, ⟨a, rfl⟩⟩
        exact (d i).map_smul c ω }
  refine ⟨{ differential := dA, differential_generator := ?_, differential_squared := ?_ }⟩
  · intro i f
    show d i (f 0 • exteriorPower.ιMulti B i
      (fun j ↦ dividedPowerDifferential (A := A) hJ (f j.succ))) = _
    simpa only [Stacks.DeRham.DifferentialDescent.SourceDeRham.tgtGen,
      Stacks.DeRham.DifferentialDescent.SourceDeRham.tgtGenRes,
      Stacks.DeRham.DifferentialDescent.SourceDeRham.targetD, hπ] using hd i f
  · intro i
    ext ω
    exact LinearMap.congr_fun (hsquare i) ω

/-- The canonical divided power de Rham complex. -/
@[stacks 07HZ "divided_power_de_rham_complex"]
public noncomputable def dividedPowerDeRhamComplex :
    DividedPowerDeRhamComplex (A := A) hJ := Classical.choice (by exact complex_exists hJ)

/-- The canonical differential has the defining value on standard generators. -/
@[simp]
public theorem dividedPowerDeRhamComplex_differential_generator
    (i : ℕ) (f : Fin (i + 1) → B) :
    (dividedPowerDeRhamComplex (A := A) hJ).differential i
        (f 0 • exteriorPower.ιMulti B i
          (fun j ↦ dividedPowerDifferential (A := A) hJ (f j.succ))) =
      exteriorPower.ιMulti B (i + 1)
        (fun j ↦ dividedPowerDifferential (A := A) hJ (f j)) :=
  (dividedPowerDeRhamComplex (A := A) hJ).differential_generator i f

/-- Consecutive differentials in the canonical divided power de Rham complex compose to zero. -/
@[simp]
public theorem dividedPowerDeRhamComplex_differential_squared (i : ℕ) :
    ((dividedPowerDeRhamComplex (A := A) hJ).differential (i + 1)).comp
      ((dividedPowerDeRhamComplex (A := A) hJ).differential i) = 0 :=
  (dividedPowerDeRhamComplex (A := A) hJ).differential_squared i

/-- The generator formula uniquely determines the divided power de Rham complex. -/
@[stacks 07HZ "divided_power_de_rham_complex"]
public theorem DividedPowerDeRhamComplex.unique
    (C : DividedPowerDeRhamComplex (A := A) hJ) :
    C = dividedPowerDeRhamComplex (A := A) hJ := by
  apply DividedPowerDeRhamComplex.ext
  funext i
  apply LinearMap.ext_on (span_range_smul_ιMulti_eq_top (R := A)
    (dividedPowerDifferential (A := A) hJ) (dividedPowerDifferentials_span hJ) i)
  rintro _ ⟨f, rfl⟩
  exact (C.differential_generator i f).trans
    (dividedPowerDeRhamComplex_differential_generator hJ i f).symm

/-- Any two divided power de Rham complexes with the defining generator rule agree. -/
public instance : Subsingleton (DividedPowerDeRhamComplex (A := A) hJ) where
  allEq C D := C.unique.trans D.unique.symm

end DividedPowerDeRham

end Crystalline

end
