module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransfer
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeHorizontalMate
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.DegreeZeroRestriction
public import StacksFrontier.CategoryTheory.Adjunction.MatesChangeOfCategories
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence

/-!
# Finite base change for abelian sheaves on Mathlib's small étale site (Stacks Tag 0959)

For a cartesian square
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
of schemes with `f` finite, the base change comparison `g⁻¹ f_* G ⟶ f'_* g'⁻¹ G` of
`Stacks.EtaleCohomology.etaleAbelianBaseChange` is an isomorphism for every abelian sheaf `G` on
Mathlib's small étale site of `X`.

The library has this for sheaves of sets on Mathlib's small étale site, as
`AlgebraicGeometry.SmallEtale.isIso_mateEquiv_symm_unboundedBaseChangeMate`. Passing to the
underlying sheaf of sets commutes with direct images on the nose and with inverse images up to the
isomorphism `Stacks.EtaleCohomology.inverseImageForgetComparison` (Tag 00YT), and it reflects
isomorphisms, so `Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms` moves the
invertibility from sets to abelian groups.

## Main results

* `Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isFinite_of_isPullback_succUniverse`:
  Tag 0959 for abelian sheaves, for any cartesian square of schemes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- **Stacks Tag 0959 for abelian sheaves on Mathlib's small étale site**, for an arbitrary
cartesian square of schemes with `f` finite: the base change comparison `g⁻¹ f_* ⟶ f'_* g'⁻¹` is
an isomorphism. This is `Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isFinite`, stated
there for a square of a big étale site, applied to a big étale site containing the four schemes. -/
theorem isIso_etaleAbelianBaseChange_of_isFinite_of_isPullback_succUniverse {X X' Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y') (sq : IsPullback g' f' f g)
    [IsFinite f] : IsIso (etaleAbelianBaseChange.{u, u + 1} f g g' f' sq.w) := by
  obtain ⟨B, hB⟩ := BigEtaleSite.exists_contains_of_small ({X, X', Y, Y'} : Set Scheme.{u})
  have hX := hB X (by simp)
  have hX' := hB X' (by simp)
  have hY := hB Y (by simp)
  have hY' := hB Y' (by simp)
  let fB : B.obj X hX ⟶ B.obj Y hY := ObjectProperty.homMk f
  let gB : B.obj Y' hY' ⟶ B.obj Y hY := ObjectProperty.homMk g
  let g'B : B.obj X' hX' ⟶ B.obj X hX := ObjectProperty.homMk g'
  let f'B : B.obj X' hX' ⟶ B.obj Y' hY' := ObjectProperty.homMk f'
  have : IsFinite (B.inclusion.map fB) := ‹IsFinite f›
  exact isIso_etaleAbelianBaseChange_of_isFinite B (f := fB) (g := gB) (g' := g'B) (f' := f'B) sq

end Stacks.EtaleCohomology

end
