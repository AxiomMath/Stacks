module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Ring.PUnit
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring
public import StacksCore.Tactic.StacksAttribute

/-!
# Weil's trace formula for an endomorphism of a curve

Let `C` be a nonsingular projective curve over an algebraically closed field `k` with a base
point `c₀`, let `J = Pic⁰_{C/k}` be its jacobian, and let `φ : C → C` be a `k`-endomorphism of
`C` distinct from the identity. Write `V(φ) = Δ_C · Γ_φ` for the intersection number on `C × C`
of the diagonal with the graph of `φ`, and `φ^* : J → J` for the action of `φ` on `J` by
pullback. Weil's theorem is the formula

  `V(φ) = 1 - Tr_J(φ^*) + deg φ`.

The source proves it from the correspondence between a curve and its jacobian: the group
`A¹(C × C)` of codimension-one divisor classes decomposes as
`pr₁^* A¹(C) ⊕ pr₂^* A¹(C) ⊕ R`, the summand `R` is canonically isomorphic to `End(J)`, the
trace form of `End(J)` is `Tr(α β) = - ∫_{C × C} α · σ^* β` for the switch `σ` of the two
factors, the class of `id_J` is `Δ_C - {c₀} × C - C × {c₀}`, and the class of `φ^*` is
`Γ_φ - C × {φ(c₀)} - ∑_{φ(c) = c₀} {c} × C`. This file records that correspondence as
`Stacks.EtaleCohomology.JacobianCorrespondence` together with
`Stacks.EtaleCohomology.JacobianCorrespondence.EndomorphismData`, and derives the formula from
it exactly as the source does.

## Main definitions

* `Stacks.EtaleCohomology.JacobianCorrespondence` — the correspondence between `A¹(C × C)` with
  its intersection pairing and `End(J)` with its trace form.
* `Stacks.EtaleCohomology.JacobianCorrespondence.EndomorphismData` — the divisor classes and
  numbers attached to a single endomorphism `φ`: its graph, its degree and the class of `φ^*`.
* `Stacks.EtaleCohomology.JacobianCorrespondence.fixedPointNumber` — the number
  `V(φ) = Δ_C · Γ_φ`.

## Main results

* `Stacks.EtaleCohomology.JacobianCorrespondence.fixedPointNumber_eq` — Weil's formula
  `V(φ) = 1 - Tr_J(φ^*) + deg φ`.
* `Stacks.EtaleCohomology.JacobianCorrespondence.EndomorphismData.degree_eq` — the degree of `φ`
  is determined by the correspondence, namely `deg φ = Γ_φ · ({c₀} × C + C × {c₀}) - 1`.
* `Stacks.EtaleCohomology.projectiveLineJacobianCorrespondence` and
  `Stacks.EtaleCohomology.projectiveLineEndomorphismData` — the correspondence and an
  endomorphism datum of every degree, realised on `P¹ × P¹`, whose jacobian is trivial.

## Implementation notes

The geometric input enters as data, as it does in the sibling definition
`Stacks.EtaleCohomology.FrobeniusActionOnCohomology` for the global Lefschetz number: the group
`A¹(C × C)`, the intersection pairing, the ring `End(J)` and its trace form, and the divisor
classes of the diagonal, of the two axes through the base point and of the graph of `φ` are all
carried as fields, subject to exactly the identities the source states for them. This is the
level at which the source works, since it states the correspondence between a curve and its
jacobian without proof and then derives the formula from it; the formula itself is proved here,
and no field of either structure asserts it.

The subgroup `axis` is `pr₁^* A¹(C) ⊕ pr₂^* A¹(C)`, the classes pulled back from the two
factors. The two fields `exists_axis_add_endoDivisor` and `eq_zero_of_endoDivisor_mem_axis`,
together with the injectivity of `endoDivisor`, say that `A¹(C × C)` is the direct sum of `axis`
and the image `R` of `End(J)`; the orthogonality of `R` and `axis` under the intersection
pairing is the input the source uses to replace `Γ_φ` by the class of `φ^*`.

The universe of the divisor classes and the universe of `End(J)` are independent. No
commutativity is imposed on `End(J)`, since none is used and none holds in general.

## References

* [Stacks Project, Tag 03U1](https://stacks.math.columbia.edu/tag/03U1)
-/

@[expose] public noncomputable section

universe u v

namespace Stacks.EtaleCohomology

/-- The correspondence between a nonsingular projective curve `C` over an algebraically closed
field, with a base point `c₀`, and its jacobian `J`: the group `A` of codimension-one divisor
classes on `C × C` with its intersection pairing, and the ring `E = End(J)` with its trace
form, related as in Section 64.14 of the source.

See [Stacks Project, Tag 03U1](https://stacks.math.columbia.edu/tag/03U1). -/
public structure JacobianCorrespondence (A : Type u) [AddCommGroup A] (E : Type v) [Ring E] where
  /-- The intersection number `∫_{C × C} : A¹(C × C) × A¹(C × C) → ℤ`. -/
  intersection : A →+ A →+ ℤ
  /-- The intersection pairing is symmetric. -/
  intersection_comm : ∀ a b : A, intersection a b = intersection b a
  /-- The map `σ^*` induced by the automorphism `σ` of `C × C` switching the two factors. -/
  switch : A →+ A
  /-- The canonical isomorphism of `End(J)` onto the summand `R` of `A¹(C × C)`, viewed as a
  map to `A¹(C × C)`: it sends an endomorphism to the divisor class inducing it. -/
  endoDivisor : E →+ A
  /-- The trace `Tr_J : End(J) → ℤ`. -/
  trace : E →+ ℤ
  /-- The class `Δ_C` of the diagonal. -/
  diagonal : A
  /-- The class `{c₀} × C` of the fibre of the first projection over the base point. -/
  fibreFst : A
  /-- The class `C × {c₀}` of the fibre of the second projection over the base point. -/
  fibreSnd : A
  /-- The subgroup `pr₁^* A¹(C) ⊕ pr₂^* A¹(C)` of classes pulled back from the two factors. -/
  axis : AddSubgroup A
  /-- The fibre `{c₀} × C` is pulled back from the first factor. -/
  fibreFst_mem : fibreFst ∈ axis
  /-- The fibre `C × {c₀}` is pulled back from the second factor. -/
  fibreSnd_mem : fibreSnd ∈ axis
  /-- The switch fixes the class of the diagonal. -/
  switch_diagonal : switch diagonal = diagonal
  /-- The switch exchanges the two fibres through the base point. -/
  switch_fibreFst : switch fibreFst = fibreSnd
  /-- The switch exchanges the two fibres through the base point. -/
  switch_fibreSnd : switch fibreSnd = fibreFst
  /-- The class of the identity of `J` is `Δ_C - {c₀} × C - C × {c₀}`. -/
  endoDivisor_one : endoDivisor 1 = diagonal - fibreFst - fibreSnd
  /-- The trace form of `End(J)` is `Tr(α β) = - ∫_{C × C} α · σ^* β`. -/
  trace_mul : ∀ α β : E, trace (α * β) = -intersection (endoDivisor α) (switch (endoDivisor β))
  /-- The summand `R` is orthogonal to the classes pulled back from the two factors. -/
  intersection_endoDivisor_axis : ∀ (α : E) (z : A), z ∈ axis → intersection (endoDivisor α) z = 0
  /-- `End(J)` maps isomorphically onto the summand `R`. -/
  endoDivisor_injective : Function.Injective endoDivisor
  /-- Every divisor class on `C × C` is the sum of one pulled back from the two factors and one
  in the summand `R`. -/
  exists_axis_add_endoDivisor : ∀ a : A, ∃ z ∈ axis, ∃ α : E, a = z + endoDivisor α
  /-- The summand `R` meets the classes pulled back from the two factors only in zero. -/
  eq_zero_of_endoDivisor_mem_axis : ∀ α : E, endoDivisor α ∈ axis → α = 0

namespace JacobianCorrespondence

variable {A : Type u} [AddCommGroup A] {E : Type v} [Ring E] (W : JacobianCorrespondence A E)

/-- The class of the diagonal is the class of `id_J` plus the two fibres through the base
point. -/
public theorem diagonal_eq : W.diagonal = W.endoDivisor 1 + (W.fibreFst + W.fibreSnd) := by
  rw [W.endoDivisor_one]
  abel

/-- The switch fixes the class of `id_J`, because it fixes the diagonal and exchanges the two
fibres through the base point. -/
public theorem switch_endoDivisor_one : W.switch (W.endoDivisor 1) = W.endoDivisor 1 := by
  rw [W.endoDivisor_one, map_sub, map_sub, W.switch_diagonal, W.switch_fibreFst,
    W.switch_fibreSnd]
  abel

/-- The data attached to a `k`-endomorphism `φ` of `C`: the class `Γ_φ` of its graph, its degree
`deg φ`, the induced endomorphism `φ^*` of the jacobian, and the class
`C × {φ(c₀)} + ∑_{φ(c) = c₀} {c} × C` by which `Γ_φ` differs from the class of `φ^*`.

See [Stacks Project, Tag 03U1](https://stacks.math.columbia.edu/tag/03U1). -/
public structure EndomorphismData where
  /-- The endomorphism `φ^* : J → J` induced by `φ` by taking pullbacks. -/
  pullback : E
  /-- The degree `deg φ`. -/
  degree : ℤ
  /-- The class `Γ_φ` of the graph of `φ`. -/
  graph : A
  /-- The class `C × {φ(c₀)} + ∑_{φ(c) = c₀} {c} × C` pulled back from the two factors. -/
  correction : A
  /-- The correcting class is pulled back from the two factors. -/
  correction_mem : correction ∈ W.axis
  /-- The class of `φ^*` is `Γ_φ - C × {φ(c₀)} - ∑_{φ(c) = c₀} {c} × C`. -/
  endoDivisor_pullback : W.endoDivisor pullback = graph - correction
  /-- The graph meets the ample class `{c₀} × C + C × {c₀}` in `1 + deg φ` points. -/
  intersection_graph_fibres : W.intersection graph (W.fibreFst + W.fibreSnd) = 1 + degree

/-- The number `V(φ) = Δ_C · Γ_φ`: the intersection number on `C × C` of the diagonal with the
graph of `φ`. -/
public def fixedPointNumber (D : W.EndomorphismData) : ℤ :=
  W.intersection W.diagonal D.graph

/-- The degree of `φ` is determined by the correspondence: it is the intersection number of the
graph of `φ` with the ample class `{c₀} × C + C × {c₀}`, minus one. -/
public theorem EndomorphismData.degree_eq (D : W.EndomorphismData) :
    D.degree = W.intersection D.graph (W.fibreFst + W.fibreSnd) - 1 := by
  rw [D.intersection_graph_fibres]
  ring

/-- **Weil's trace formula (Stacks 03U1).** Let `C` be a nonsingular projective curve over an
algebraically closed field `k` and `φ : C → C` a `k`-endomorphism of `C` distinct from the
identity. Let `V(φ) = Δ_C · Γ_φ`, the intersection number on `C × C` of the diagonal with the
graph of `φ`, let `J = Pic⁰_{C/k}` be the jacobian of `C` and `φ^* : J → J` the action induced
by `φ` by taking pullbacks. Then `V(φ) = 1 - Tr_J(φ^*) + deg φ`. -/
@[stacks 03U1]
public theorem fixedPointNumber_eq (D : W.EndomorphismData) :
    W.fixedPointNumber D = 1 - W.trace D.pullback + D.degree := by
  have hgraph : D.graph = W.endoDivisor D.pullback + D.correction := by
    rw [D.endoDivisor_pullback]
    abel
  have htrace : W.intersection (W.endoDivisor D.pullback) (W.endoDivisor 1) =
      -W.trace D.pullback := by
    have h := W.trace_mul D.pullback 1
    rw [mul_one, W.switch_endoDivisor_one] at h
    rw [h, neg_neg]
  have hsplit : W.intersection W.diagonal D.graph =
      W.intersection (W.endoDivisor 1) D.graph +
        W.intersection (W.fibreFst + W.fibreSnd) D.graph := by
    rw [W.diagonal_eq, map_add, AddMonoidHom.add_apply]
  have hR : W.intersection (W.endoDivisor 1) D.graph = -W.trace D.pullback := by
    rw [hgraph, map_add,
      W.intersection_endoDivisor_axis 1 D.correction D.correction_mem, add_zero,
      W.intersection_comm (W.endoDivisor 1) (W.endoDivisor D.pullback), htrace]
  have hample : W.intersection (W.fibreFst + W.fibreSnd) D.graph = 1 + D.degree := by
    rw [W.intersection_comm (W.fibreFst + W.fibreSnd) D.graph, D.intersection_graph_fibres]
  rw [fixedPointNumber, hsplit, hR, hample]
  ring

end JacobianCorrespondence

/-- The intersection pairing on the group `ℤ × ℤ` of divisor classes of `P¹ × P¹`, written in
the basis of the two fibres through the base point: `(a₁, a₂) · (b₁, b₂) = a₁ b₂ + a₂ b₁`,
because each of the two fibres has self-intersection zero and they meet in one point. -/
public def hyperbolicPairing : (ℤ × ℤ) →+ (ℤ × ℤ) →+ ℤ where
  toFun a :=
    { toFun := fun b => a.1 * b.2 + a.2 * b.1
      map_zero' := by
        change a.1 * 0 + a.2 * 0 = 0
        ring
      map_add' := fun b c => by
        change a.1 * (b.2 + c.2) + a.2 * (b.1 + c.1) =
          a.1 * b.2 + a.2 * b.1 + (a.1 * c.2 + a.2 * c.1)
        ring }
  map_zero' := by
    ext b
    change (0 : ℤ) * b.2 + (0 : ℤ) * b.1 = 0
    ring
  map_add' a b := by
    ext c
    change (a.1 + b.1) * c.2 + (a.2 + b.2) * c.1 =
      a.1 * c.2 + a.2 * c.1 + (b.1 * c.2 + b.2 * c.1)
    ring

/-- The switch of the two factors of `P¹ × P¹` exchanges the two fibres through the base
point, so it exchanges the two coordinates of a divisor class. -/
public def coordinateSwitch : (ℤ × ℤ) →+ (ℤ × ℤ) :=
  AddMonoidHom.mk' (fun a => (a.2, a.1)) (fun _ _ => rfl)

/-- The correspondence realised on `C = P¹`: the divisor classes of `P¹ × P¹` are
`ℤ · ({c₀} × C) ⊕ ℤ · (C × {c₀})` with the hyperbolic intersection pairing, the diagonal is the
sum of the two fibres through the base point, and the jacobian is trivial, so `End(J)` is the
zero ring. This exhibits the hypotheses of
`Stacks.EtaleCohomology.JacobianCorrespondence` as consistent. -/
public def projectiveLineJacobianCorrespondence :
    JacobianCorrespondence (ℤ × ℤ) PUnit where
  intersection := hyperbolicPairing
  intersection_comm a b := by
    change a.1 * b.2 + a.2 * b.1 = b.1 * a.2 + b.2 * a.1
    ring
  switch := coordinateSwitch
  endoDivisor := (0 : PUnit →+ ℤ × ℤ)
  trace := (0 : PUnit →+ ℤ)
  diagonal := (1, 1)
  fibreFst := (1, 0)
  fibreSnd := (0, 1)
  axis := ⊤
  fibreFst_mem := AddSubgroup.mem_top _
  fibreSnd_mem := AddSubgroup.mem_top _
  switch_diagonal := rfl
  switch_fibreFst := rfl
  switch_fibreSnd := rfl
  endoDivisor_one := by
    change (0 : ℤ × ℤ) = ((1, 1) : ℤ × ℤ) - (1, 0) - (0, 1)
    decide
  trace_mul α β := by simp
  intersection_endoDivisor_axis α z _ := by simp
  endoDivisor_injective _ _ _ := Subsingleton.elim _ _
  exists_axis_add_endoDivisor a := ⟨a, AddSubgroup.mem_top _, PUnit.unit, by simp⟩
  eq_zero_of_endoDivisor_mem_axis α _ := Subsingleton.elim _ _

/-- An endomorphism datum of every degree `d` for
`Stacks.EtaleCohomology.projectiveLineJacobianCorrespondence`: a degree-`d` endomorphism of
`P¹` has graph of class `d · ({c₀} × C) + C × {c₀}`. Together with
`Stacks.EtaleCohomology.JacobianCorrespondence.fixedPointNumber_eq` this gives `V(φ) = 1 + d`,
the genus-zero case of Weil's formula. -/
public def projectiveLineEndomorphismData (d : ℤ) :
    projectiveLineJacobianCorrespondence.EndomorphismData where
  pullback := PUnit.unit
  degree := d
  graph := (d, 1)
  correction := (d, 1)
  correction_mem := AddSubgroup.mem_top _
  endoDivisor_pullback := (sub_self _).symm
  intersection_graph_fibres := by
    change d * (0 + 1) + 1 * (1 + 0) = 1 + d
    ring

/-- The genus-zero case of Weil's formula: a degree-`d` endomorphism of `P¹` meets the diagonal
in `1 + d` points. -/
public theorem projectiveLine_fixedPointNumber (d : ℤ) :
    projectiveLineJacobianCorrespondence.fixedPointNumber
      (projectiveLineEndomorphismData d) = 1 + d := by
  rw [projectiveLineJacobianCorrespondence.fixedPointNumber_eq]
  show 1 - (0 : ℤ) + d = 1 + d
  ring

end Stacks.EtaleCohomology

end
