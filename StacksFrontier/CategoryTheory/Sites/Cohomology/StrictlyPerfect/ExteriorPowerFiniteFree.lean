module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerSheafify
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomFiniteFree

/-!
# Exterior and symmetric powers of a finite free module are finite free summands

Let `(C, O)` be a ringed site and let `F` be a sheaf of `O`-modules isomorphic to a finite free
one. Every exterior power and every symmetric power of `F` is then again free of finite rank,
hence in particular a direct summand of a finite free module in the sense of
`AlgebraicGeometry.RingedSite.IsFiniteFreeSummand`.

That predicate is the termwise hypothesis of the representation of the derived internal Hom by
the ordinary internal Hom complex, so these are the statements which make a complex built out
of exterior powers of a finite free module — a Koszul complex, for instance — strictly perfect
in the sense that representation requires.

## Main results

* `AlgebraicGeometry.RingedSite.isFiniteFreeSummand_exteriorPower`
* `AlgebraicGeometry.RingedSite.isFiniteFreeSummand_symmetricPower`

## Implementation notes

The index type of the basis is discarded: the exterior power of a free module on `ι` is free on
the `n`-element subsets of `ι` and the symmetric power is free on the monomials of degree `n`,
but `IsFiniteFreeSummand` asserts only the existence of a retraction onto some `O^{⊕r}`, so the
statements below quantify over the isomorphism to a finite free module rather than naming its
basis. The linear order and the decidable equality which the two bases need are supplied inside
the existence results used here and so do not appear in these statements.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {F : SheafOfModules.{u} (CategoryTheory.Sheaf.toRingCat X.J X.O)}

/-- **Every exterior power of a sheaf of modules isomorphic to a finite free one is a direct
summand of a finite free module.** -/
theorem isFiniteFreeSummand_exteriorPower
    (A : SheafOfModules.TensorExteriorSymmetricAlgebras X.J F)
    (ι : Type u) [Finite ι]
    (e : F ≅ SheafOfModules.free (R := CategoryTheory.Sheaf.toRingCat X.J X.O) ι) (n : ℕ) :
    IsFiniteFreeSummand X (A.exteriorPower n) := by
  obtain ⟨K, _, ⟨f⟩⟩ :=
    Stacks.SheafOfModules.exists_finite_nonempty_iso_free_exteriorPower X.J n A ι e
  exact isFiniteFreeSummand_of_retract_free X K (Retract.ofIso f)

/-- **Every symmetric power of a sheaf of modules isomorphic to a finite free one is a direct
summand of a finite free module.** -/
theorem isFiniteFreeSummand_symmetricPower
    (A : SheafOfModules.TensorExteriorSymmetricAlgebras X.J F)
    (ι : Type u) [Finite ι]
    (e : F ≅ SheafOfModules.free (R := CategoryTheory.Sheaf.toRingCat X.J X.O) ι) (n : ℕ) :
    IsFiniteFreeSummand X (A.symmetricPower n) := by
  obtain ⟨K, _, ⟨f⟩⟩ :=
    Stacks.SheafOfModules.exists_finite_nonempty_iso_free_symmetricPower X.J n A ι e
  exact isFiniteFreeSummand_of_retract_free X K (Retract.ofIso f)

end AlgebraicGeometry.RingedSite

end
