module

public import StacksFrontier.AlgebraicGeometry.SmoothAtJacobian.Conditions

/-!
# The numerical conditions of Tag 01V9, and base change of a bound on the generators

Conditions (3) and (4) of Stacks Tag 01V9 bound the number of generators of the same module,
the stalk of the sheaf of relative differentials: condition (3) over the local ring of the
source, condition (4) over its residue field. Condition (3) implies condition (4).

## Main results

* `Stacks.SmoothAtJacobian.GeneratedByAtMost.baseChange`: a bound on the number of generators
  of a module survives base change along any algebra map.
* `Stacks.SmoothAtJacobian.condition3_imp_condition4`: condition (3) of Tag 01V9 implies
  condition (4).

## References

* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u v w

namespace Stacks.SmoothAtJacobian

/-- **A bound on the number of generators survives base change.** If `M` is generated over `B`
by at most `d` elements, then `k ⊗[B] M` is generated over `k` by at most `d` elements, for any
`B`-algebra `k`. -/
public theorem GeneratedByAtMost.baseChange {B : Type u} [CommRing B] {M : Type v}
    [AddCommMonoid M] [Module B M] (k : Type w) [CommRing k] [Algebra B k] {d : WithBot ℕ∞}
    (h : GeneratedByAtMost B M d) : GeneratedByAtMost k (k ⊗[B] M) d := by
  classical
  obtain ⟨s, hspan, hcard⟩ := h
  refine ⟨s.image (fun m => (1 : k) ⊗ₜ[B] m), ?_, le_trans ?_ hcard⟩
  · have hbase := Submodule.baseChange_span (R := B) (M := M) k (s : Set M)
    rw [hspan, Submodule.baseChange_top] at hbase
    rw [Finset.coe_image]
    exact hbase.symm
  · exact_mod_cast Finset.card_image_le

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

/-- **Condition (3) of Tag 01V9 implies condition (4).** If the stalk of the sheaf of relative
differentials is generated over the local ring at `x` by at most `dim_x` elements, then its
residue-field fibre is generated over the residue field by at most `dim_x` elements. -/
public theorem condition3_imp_condition4 (h : Condition3 f x) : Condition4 f x := by
  let := relativeDifferentialStalkModule f x
  let : Algebra (X.presheaf.stalk x) (X.residueField x) := (X.residue x).hom.toAlgebra
  exact ⟨h.1, h.2.baseChange (X.residueField x)⟩

end Stacks.SmoothAtJacobian

end
