module

public import Mathlib.Data.Set.PowersetCard
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSheafStalkBasis
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.TrivialDividedPowers
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.ExteriorPowerFiniteFree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Exterior powers of a finite free sheaf of modules vanish above the rank

Let `(C, O)` be a ringed site and let `F` be a sheaf of `O`-modules isomorphic to the free
module on a finite index type `ι`. The degree-`n` exterior power of `F` is then free on the
`n`-element subsets of `ι`, and there are no such subsets once `n` exceeds the cardinality of
`ι`: the exterior power is a zero object in every degree above the rank.

Together with the vanishing in negative degrees, which is part of the data of a package of
exterior, symmetric and tensor algebras, this confines the nonvanishing exterior powers of `F`
to the finitely many degrees `0, …, #ι`. That is the boundedness half of strict perfectness for
a complex built out of the exterior powers of a finite free module — a Koszul complex, in
particular — and the termwise half is recorded here as well, in the `ℤ`-indexed form such a
complex uses.

## Main results

* `AlgebraicGeometry.RingedSite.isZero_exteriorPiece_of_card_lt`: **the exterior powers of a
  finite free sheaf of modules vanish above the rank.**
* `AlgebraicGeometry.RingedSite.isFiniteFreeSummand_exteriorPiece`: **every homogeneous piece
  of the exterior algebra of a finite free sheaf of modules, in any integer degree, is a direct
  summand of a finite free module.**

## Implementation notes

That the free module on an empty index type is a zero object is
`SheafOfModules.isZero_free_of_isEmpty`, which is stated for an arbitrary sheaf of rings and is
used here at the structure sheaf of the ringed site.

The index type produced by the free description of the exterior power is `Set.powersetCard ι n`,
the `n`-element finite subsets of `ι`; `Set.powersetCard.eq_empty_iff` is what turns the
numerical hypothesis `#ι < n` into emptiness of that type. The linear order Mathlib's exterior
basis needs is supplied by well-ordering `ι` inside the proof, so it does not appear in the
statements.

The termwise statement is given in integer degrees rather than natural ones because the Koszul
complex is a `ℤ`-indexed complex: the negative degrees are settled by the vanishing which is
part of the package of algebras, and the nonnegative ones reduce to the statement about
`exteriorPower`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {F : SheafOfModules.{u} (toRingCat X.J X.O)}

/-- **The exterior powers of a finite free sheaf of modules vanish above the rank.** If `F` is
isomorphic to the free module on a finite index type `ι`, then `⋀ⁿF` is a zero object for every
integer `n` exceeding the cardinality of `ι`: the exterior power is free on the `n`-element
subsets of `ι`, and there are none. -/
@[sga "6 VII 4.1" "special case"]
theorem isZero_exteriorPiece_of_card_lt
    (A : SheafOfModules.TensorExteriorSymmetricAlgebras X.J F) (ι : Type u) [Finite ι]
    (e : F ≅ SheafOfModules.free (R := toRingCat X.J X.O) ι) (n : ℤ)
    (hn : (Nat.card ι : ℤ) < n) :
    IsZero (A.exterior.piece n) := by
  classical
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (a := n) (by omega)
  let _ : LinearOrder ι := IsWellOrder.linearOrder WellOrderingRel
  have : IsEmpty ↥(Set.powersetCard ι m) :=
    Set.isEmpty_coe_sort.2 (Set.powersetCard.eq_empty_iff.2 (by exact_mod_cast hn))
  exact IsZero.of_iso
    (_root_.SheafOfModules.isZero_free_of_isEmpty (R := toRingCat X.J X.O)
      ↥(Set.powersetCard ι m))
    (Stacks.SheafOfModules.exteriorPowerFreeIsoOfIso X.J m A e)

/-- **Every homogeneous piece of the exterior algebra of a finite free sheaf of modules is a
direct summand of a finite free module.** In negative degrees the piece vanishes, and in
nonnegative degrees it is the exterior power, which is itself free of finite rank. -/
theorem isFiniteFreeSummand_exteriorPiece
    (A : SheafOfModules.TensorExteriorSymmetricAlgebras X.J F) (ι : Type u) [Finite ι]
    (e : F ≅ SheafOfModules.free (R := toRingCat X.J X.O) ι) (n : ℤ) :
    IsFiniteFreeSummand X (A.exterior.piece n) := by
  rcases lt_or_ge n 0 with hn | hn
  · exact IsFiniteFreeSummand.of_isZero X
      (Stacks.SheafOfModules.isZero_exteriorPiece_of_neg A hn)
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (a := n) (by omega)
    exact isFiniteFreeSummand_exteriorPower X A ι e m

end AlgebraicGeometry.RingedSite

end
