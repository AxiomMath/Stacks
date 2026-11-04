module

public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Torsion is invisible to a homomorphism to the integers

Let `G` be an abelian group and let `d : G →+ ℤ`.  Since `ℤ` is torsion free, every element of
`G` killed by a nonzero integer `m` is killed by `d` as well.  So the `m`-torsion subgroup of `G`
is already contained in `ker d`, and the `m`-torsion subgroups of `G` and of `ker d` agree.

This is the group-theoretic content of the first step of the proof of
[Stacks, Tag 0C1Z](https://stacks.math.columbia.edu/tag/0C1Z): the source writes down the short
exact sequence `0 → Pic⁰(X) → Pic(X) --deg--> ℤ → 0` and then works with `Pic⁰(X)`, which is
legitimate because `Pic(X)[m] ⊆ Pic⁰(X)`.  Note that only the *left exactness* of that sequence is
used — surjectivity of the degree plays no role, which is why the statement below asks for nothing
but a homomorphism to `ℤ`.

## Main results

* `AddCommGroup.mem_ker_of_mem_torsionBy`: an `m`-torsion element, `m ≠ 0`, lies in the kernel of
  every homomorphism to `ℤ`.
* `AddCommGroup.torsionByIntKerAddEquiv`: the `m`-torsion subgroup of `G` is the `m`-torsion
  subgroup of `ker d`, by the identity on underlying elements.

## Implementation notes

The torsion subgroup is `Submodule.torsionBy ℤ` rather than the reducible abbreviation
`AddSubgroup.torsionBy`.
-/

@[expose] public section

namespace AddCommGroup

variable {G : Type*} [AddCommGroup G]

/-- An element killed by a nonzero integer `m` is killed by every homomorphism `d : G →+ ℤ`. -/
theorem mem_ker_of_mem_torsionBy (d : G →+ ℤ) {m : ℤ} (hm : m ≠ 0) {x : G}
    (hx : x ∈ Submodule.torsionBy ℤ G m) : x ∈ d.ker := by
  have h : m • x = 0 := (Submodule.mem_torsionBy_iff m x).mp hx
  have h' : m • d x = 0 := by rw [← map_zsmul, h, map_zero]
  rw [AddMonoidHom.mem_ker]
  exact (smul_eq_zero.mp h').resolve_left hm

/-- **The `m`-torsion of `G` is the `m`-torsion of the kernel of any `d : G →+ ℤ`**, for `m ≠ 0`,
by the identity on underlying elements of `G`. -/
def torsionByIntKerAddEquiv (d : G →+ ℤ) {m : ℤ} (hm : m ≠ 0) :
    Submodule.torsionBy ℤ G m ≃+ Submodule.torsionBy ℤ d.ker m where
  toFun x := ⟨⟨x.1, mem_ker_of_mem_torsionBy d hm x.2⟩, by
    refine (Submodule.mem_torsionBy_iff m _).mpr (Subtype.ext ?_)
    simp⟩
  invFun y := ⟨y.1.1, by
    refine (Submodule.mem_torsionBy_iff m _).mpr ?_
    exact congrArg Subtype.val ((Submodule.mem_torsionBy_iff m y.1).mp y.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The image of `x` under `torsionByIntKerAddEquiv d hm` has the same underlying element of `G`
as `x`. -/
@[simp]
theorem torsionByIntKerAddEquiv_apply_coe (d : G →+ ℤ) {m : ℤ} (hm : m ≠ 0)
    (x : Submodule.torsionBy ℤ G m) :
    ((torsionByIntKerAddEquiv d hm x : Submodule.torsionBy ℤ d.ker m) : G) = (x : G) := rfl

/-- The image of `y` under the inverse of `torsionByIntKerAddEquiv d hm` has the same underlying
element of `G` as `y`. -/
@[simp]
theorem torsionByIntKerAddEquiv_symm_apply_coe (d : G →+ ℤ) {m : ℤ} (hm : m ≠ 0)
    (y : Submodule.torsionBy ℤ d.ker m) :
    (((torsionByIntKerAddEquiv d hm).symm y : Submodule.torsionBy ℤ G m) : G) = (y : G) := rfl

end AddCommGroup

end
