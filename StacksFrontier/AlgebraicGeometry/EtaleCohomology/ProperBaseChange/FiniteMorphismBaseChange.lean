module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeCommutation
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence

/-!
# Cohomology commutes with base change for a finite morphism

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a cartesian square of schemes with `f` finite. The underived comparison
`g^{-1} f_* ⟶ f'_* (g')^{-1}` of abelian sheaves on the small étale sites is invertible, and so
therefore is the derived base change map `g^{-1} R f_* F ⟶ R f'_* (g')^{-1} F` for every abelian
sheaf `F`. This is [Stacks, Tag 0A4E].

## Main results

* `Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isPullback_of_isFinite` — the underived
  comparison is invertible, for an arbitrary cartesian square of schemes.
* `Stacks.EtaleCohomology.isIso_etaleAbelianSheafDerivedBaseChange_of_isPullback_of_isFinite` —
  the derived base change map is invertible at every abelian sheaf.
* `Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isFinite` — **Stacks 0A4E**.

## Implementation notes

`Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isFinite` proves the underived statement
for a square drawn from the underlying category of a big étale site. The four schemes of any
square form a small set, so by `AlgebraicGeometry.BigEtaleSite.exists_contains_of_small` they all
lie in one big étale site. That site is a full subcategory of schemes, so the square, its
cartesianness and the comparison map are the same there as among schemes.

The coefficients are `AddCommGrpCat.{u + 1}`, which is `AddCommGrpCat.{max (u + 1) v}` at
`v = 0`. They are bounded by the input Stacks 0959, which this library proves for sheaves of sets
in `Type (u + 1)` only.

## References

* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
* [Stacks Project, Tag 0A4E](https://stacks.math.columbia.edu/tag/0A4E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')

/-- **The underived base change comparison `g^{-1} f_* ⟶ f'_* (g')^{-1}` of abelian sheaves is
invertible** for every cartesian square of schemes with `f` finite. The four schemes lie in one
big étale site, where this is `Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isFinite`. -/
public theorem isIso_etaleAbelianBaseChange_of_isPullback_of_isFinite
    (sq : IsPullback g' f' f g) [IsFinite f] :
    IsIso (etaleAbelianBaseChange.{u, 0} f g g' f' sq.w) := by
  obtain ⟨B, hB⟩ := BigEtaleSite.exists_contains_of_small ({X, X', Y, Y'} : Set Scheme.{u})
  have hX : B.Contains X := hB X (by simp)
  have hX' : B.Contains X' := hB X' (by simp)
  have hY : B.Contains Y := hB Y (by simp)
  have hY' : B.Contains Y' := hB Y' (by simp)
  have : IsFinite (B.inclusion.map (X := B.obj X hX) (Y := B.obj Y hY)
      (ObjectProperty.homMk f)) := ‹IsFinite f›
  exact isIso_etaleAbelianBaseChange_of_isFinite B
    (X := B.obj X hX) (X' := B.obj X' hX') (Y := B.obj Y hY) (Y' := B.obj Y' hY')
    (ObjectProperty.homMk f) (ObjectProperty.homMk g) (ObjectProperty.homMk g')
    (ObjectProperty.homMk f') sq

/-- **The derived base change map `g^{-1} R f_* F ⟶ R f'_* (g')^{-1} F` is invertible** for every
cartesian square of schemes with `f` finite and every abelian sheaf `F` on `X_étale`; no torsion
condition on `F` is needed. -/
public theorem isIso_etaleAbelianSheafDerivedBaseChange_of_isPullback_of_isFinite
    (sq : IsPullback g' f' f g) [IsFinite f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso (etaleAbelianSheafDerivedBaseChange.{u, 0} f g g' f' sq.w F) :=
  isIso_etaleAbelianSheafDerivedBaseChange_of_isFinite_of_isIso.{u, 0} f g g' f' sq
    (isIso_etaleAbelianBaseChange_of_isPullback_of_isFinite f g g' f' sq) F

/-- **[Stacks, Tag 0A4E].** Cohomology commutes with base change for a finite morphism of
schemes. -/
public theorem cohomologyCommutesWithBaseChange_of_isFinite (hf : IsFinite f) :
    CohomologyCommutesWithBaseChange.{u, 0} f := fun _ _ g g' f' sq F _ =>
  isIso_etaleAbelianSheafDerivedBaseChange_of_isPullback_of_isFinite f g g' f' sq F

end Stacks.EtaleCohomology

end
