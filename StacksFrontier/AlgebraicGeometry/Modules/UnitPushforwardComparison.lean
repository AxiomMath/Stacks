module

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.UniversalDirectImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomSlice

/-!
# The structure-sheaf comparison as a morphism of modules

A morphism of schemes `g : W ⟶ Z` has two comparisons of structure sheaves, and they are the
same map on sections over each open of `Z`:

* `g.c`, the comorphism `𝒪_Z ⟶ g_* 𝒪_W` of sheaves of *rings*, whose invertibility is
  `AlgebraicGeometry.Scheme.Hom.app` being invertible over every open
  (`Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff`);
* `AlgebraicGeometry.Scheme.Modules.unitToPushforwardUnit g`, the comparison
  `𝒪_Z ⟶ g_* 𝒪_W` of sheaves of `𝒪_Z`-*modules*.

`AlgebraicGeometry.Scheme.isIso_app_of_isIso_unitToPushforwardUnit` reads invertibility of the
second off as invertibility of `g.app`; this file supplies the converse, which is what a
construction producing `IsIso g.c` owes a consumer stated in the module category — for instance
quasi-coherence of `g_* 𝒪_W`, which is a statement about `Z.Modules` and is got by transporting
it from `𝒪_Z` along the comparison.

## Main results

* `AlgebraicGeometry.Scheme.isIso_unitToPushforwardUnit_of_isIso_c`: `IsIso g.c` gives
  invertibility of the comparison of structure sheaves in `Z.Modules`.

## Implementation notes

The two comparisons have the same underlying map on sections over an open — `g.app U` in one
spelling and `(Scheme.Modules.unitToPushforwardUnit g).val.app (op U)` in the other — so
bijectivity transports with no computation, and
`Stacks.SheafOfModules.isIso_of_bijective_app` turns bijectivity over every open into
invertibility.  This is the same identification that the forward direction uses, read backwards.

The `IsIso` is stated with `(C := Z.Modules)` pinned: `AlgebraicGeometry.Scheme.Modules` carries
its own `Category` instance on a type definitionally equal to `SheafOfModules _`, and instance
search does not cross between the two.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

/-- **A morphism of schemes whose comorphism of structure sheaves is invertible has invertible
comparison of structure sheaves in the module category.**  The two comparisons agree on sections
over every open, so this is `Stacks.SheafOfModules.isIso_of_bijective_app` applied to the
bijectivity `Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff` provides.

This is the converse of `AlgebraicGeometry.Scheme.isIso_app_of_isIso_unitToPushforwardUnit`
together with `AlgebraicGeometry.Scheme.isIso_c_of_isIso_app`. -/
theorem Scheme.isIso_unitToPushforwardUnit_of_isIso_c {W Z : Scheme.{u}} (g : W ⟶ Z)
    (h : IsIso g.c) :
    IsIso (C := Z.Modules) (Scheme.Modules.unitToPushforwardUnit g) := by
  refine Stacks.SheafOfModules.isIso_of_bijective_app _ fun V => ?_
  have hb : Function.Bijective (g.app V.unop) :=
    (Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff g).mp h V.unop
  exact ⟨hb.1, hb.2⟩

end AlgebraicGeometry

end
