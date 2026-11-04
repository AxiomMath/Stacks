module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafIsos

/-!
# The affine associated sheaf is tensor sheafification

Let `R` be a commutative ring and `M` an `R`-module. Two constructions produce a sheaf of
`𝒪_{Spec R}`-modules out of `M`: the affine construction `M̃`, whose sections on a standard open
`D(f)` are `M_f`, and the general construction attached to the ring map `R → Γ(Spec R, 𝒪)`,
namely the sheafification of `U ↦ 𝒪(U) ⊗_R M`. This file identifies the two, naturally in `M`.

## Main definitions

* `AlgebraicGeometry.tilde.associatedSheafFunctorSpec`: tensor sheafification on `Spec R`, read
  as a functor into `(Spec R).Modules`.
* `AlgebraicGeometry.tilde.associatedSheafNatIso`: the canonical natural isomorphism between
  the two constructions.

## Implementation notes

Both constructions are left adjoints of the same functor — global sections with scalars
restricted along `R → Γ(Spec R, 𝒪)` — so they are canonically isomorphic by uniqueness of left
adjoints. The two adjunctions are `AlgebraicGeometry.tilde.adjunction` and
`Stacks.AssociatedSheaf.associatedSheafAdjunction`, and their common right adjoint is
`AlgebraicGeometry.moduleSpecΓFunctor`, which the latter's `globalSectionsFunctor` is
definitionally.

`AlgebraicGeometry.tilde.functor` lands in `(Spec R).Modules`, a non-reducible definition
wrapping `SheafOfModules (Spec R).ringCatSheaf`, whereas tensor sheafification is built on
`Stacks.AssociatedSheaf`'s `structureSheafRing`. The two agree at default
transparency but not at the transparency instance search uses, so the reducible
`associatedSheafFunctorSpec` is introduced once, to place the comparison in the category the
affine construction lives in.

`AssociatedSheafIsos` is imported for `Stacks.AssociatedSheaf.tensorUnitSection`, the canonical
section `m ↦ 1 ⊗ m`, in terms of which the comparison is characterized on global sections
(`AlgebraicGeometry.tildeAssociatedSheafNatIso`).

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
* [Stacks Project, Tag 01I7](https://stacks.math.columbia.edu/tag/01I7)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.tilde

open Stacks.AssociatedSheaf

/-- Tensor sheafification on `Spec R` along `R → Γ(Spec R, 𝒪)`, read as a functor into
`(Spec R).Modules`. -/
abbrev associatedSheafFunctorSpec (R : CommRingCat.{u}) :
    ModuleCat.{u} R ⥤ (Spec R).Modules :=
  associatedSheafFunctor (Spec R).toRingedSpace (Scheme.ΓSpecIso R).inv.hom

/-- The canonical comparison between the affine associated-sheaf construction `M ↦ M̃` on
`Spec R` and tensor sheafification along `R → Γ(Spec R, 𝒪)`, natural in the module. -/
def associatedSheafNatIso (R : CommRingCat.{u}) :
    tilde.functor R ≅ associatedSheafFunctorSpec R :=
  (tilde.adjunction (R := R)).leftAdjointUniq
    (associatedSheafAdjunction (Spec R).toRingedSpace (Scheme.ΓSpecIso R).inv.hom)

end AlgebraicGeometry.tilde
