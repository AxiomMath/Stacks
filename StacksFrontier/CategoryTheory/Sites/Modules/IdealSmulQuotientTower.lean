module

public import StacksFrontier.CategoryTheory.Sites.Modules.IdealPowerTensorQuotient
public import Mathlib.CategoryTheory.Functor.OfSequence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The tower of quotients `ℱ/ℐⁿℱ` on a ringed site

Let `(𝒞, 𝒪)` be a ringed site, `ℐ ⊂ 𝒪` a sheaf of ideals and `ℱ` an arbitrary sheaf of
`𝒪`-modules. The quotients `ℱ/ℐℱ` (`Stacks.Sites.idealSmulQuotient`), with their projections from
`ℱ` and the transition maps `ℱ/𝒥ℱ ⟶ ℱ/ℐℱ` attached to inclusions `𝒥 ⊆ ℐ`, assemble at the powers
of `ℐ` into the inverse system

`n ↦ ℱ/ℐⁿℱ`

indexed by `ℕᵒᵖ`, together with the compatibility of the quotient projections out of `ℱ` with
its transition maps. The tower is indexed by `n` itself, not shifted by one.

## Main definitions

* `Stacks.Sites.idealSmulQuotientTower` — the inverse system `n ↦ ℱ/ℐⁿℱ`.

## Main results

* `Stacks.Sites.idealSmulQuotientTower_map_succ` — the successive transition map of the tower is
  the transition map of the quotients.
* `Stacks.Sites.idealSmulQuotientπ_comp_idealSmulQuotientTower_map_succ` — the quotient
  projections out of `ℱ` are compatible with it.

## References

* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v w

namespace Stacks.Sites

open AlgebraicGeometry.RingedSite

variable {X : RingedSite.{u, v, w}}

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
  Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorObj

variable [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (F : Modules.{u, v, w} X) (I : IdealSubsheaf.{v, u, w} X.O)

/-- The tower `n ↦ ℱ/ℐⁿℱ` of quotients of a sheaf of modules by the powers of a sheaf of
ideals, as an inverse system indexed by `ℕᵒᵖ`. -/
@[sga "2 VI 2.2" "more general"]
def idealSmulQuotientTower : ℕᵒᵖ ⥤ Modules.{u, v, w} X :=
  Functor.ofOpSequence
    (X := fun n : ℕ => idealSmulQuotient F (idealPow (O := X.O) I n))
    fun n : ℕ => idealSmulQuotientMap F (idealPow_antitone (O := X.O) I (Nat.le_succ n))

/-- The `n`-th term of the tower is the quotient by the `n`-th power. -/
theorem idealSmulQuotientTower_obj (n : ℕ) :
    (idealSmulQuotientTower F I).obj ⟨n⟩ =
      idealSmulQuotient F (idealPow (O := X.O) I n) :=
  rfl

/-- The successive transition map of the tower is the transition map of the quotients. -/
theorem idealSmulQuotientTower_map_succ (n : ℕ) :
    (idealSmulQuotientTower F I).map (homOfLE (Nat.le_succ n)).op =
      idealSmulQuotientMap F (idealPow_antitone (O := X.O) I (Nat.le_succ n)) :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- The quotient projections out of `ℱ` are compatible with the successive transition maps of the
tower. -/
@[reassoc]
theorem idealSmulQuotientπ_comp_idealSmulQuotientTower_map_succ (n : ℕ) :
    idealSmulQuotientπ F (idealPow (O := X.O) I (n + 1)) ≫
        (idealSmulQuotientTower F I).map (homOfLE (Nat.le_succ n)).op =
      idealSmulQuotientπ F (idealPow (O := X.O) I n) :=
  idealSmulQuotientTower_map_succ F I n ▸
    idealSmulQuotientπ_comp_idealSmulQuotientMap F (idealPow_antitone (O := X.O) I (Nat.le_succ n))

end Stacks.Sites

end
