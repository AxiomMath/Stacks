module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsCoextension
public import StacksFrontier.Topology.Sheaves.Functors.Module.HomSheaf

/-!
# Coextension of scalars for sheaves of modules *is* the internal Hom sheaf

`Stacks.SheafOfModules.CoextendScalars.coextendScalars` (Stacks Tag 0932, built directly from the
explicit slice-wise internal-hom presheaf `coextObj`) and
`RingedSpaceModuleAdjunction.homSheaf` (Stacks Tag 0A6F, built from the very same `coextObj`, but
packaged as the internal-Hom-sheaf functor `SheafHom_{𝒪₁}(𝒪₂, -)` together with its adjunction
with restriction of scalars) are, by construction, the same functor on underlying presheaves of
modules. `CoextendScalarsKInjective.lean` flagged this explicitly: its K-injectivity criterion
for `coextendScalars` is re-derived rather than transported from the analogous
`isKInjective_homSheaf`, "since the two internal-Hom functors are... not themselves identified in
this file." This file supplies that missing identification.

## Main results

* `Stacks.SheafOfModules.CoextendScalars.coextendScalarsIsoHomSheaf`: the natural isomorphism
  `coextendScalars φ ≅ RingedSpaceModuleAdjunction.homSheaf φ`.

## Implementation notes

Both functors are right adjoint to the *same* left adjoint `SheafOfModules.restrictScalars φ`
(`restrictScalars_coextendScalars_adjunction` and
`RingedSpaceModuleAdjunction.restrictScalarsHomAdjunction`), so the comparison is immediate from
`Adjunction.rightAdjointUniq`, the standard uniqueness-of-adjoints lemma: it needs no new
unwinding of either construction, only the observation that they share a left adjoint.

## References

* [Stacks Project, Tag 0996](https://stacks.math.columbia.edu/tag/0996), Lemma 20.26.1 part (2).
* [Stacks Project, Tag 0932](https://stacks.math.columbia.edu/tag/0932)
* [Stacks Project, Tag 0A6F](https://stacks.math.columbia.edu/tag/0A6F)
-/

@[expose] public section

open CategoryTheory

universe u

namespace Stacks.SheafOfModules.CoextendScalars

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {O O' : Sheaf J RingCat.{u}}

/-- **The internal-Hom-sheaf identification.** `coextendScalars φ`, Stacks Tag 0932's explicit
sheaf-level coextension-of-scalars functor, is naturally isomorphic to
`RingedSpaceModuleAdjunction.homSheaf φ`, Stacks Tag 0A6F's internal-Hom-sheaf functor
`SheafHom_O(O', -)`: both are right adjoint to the same functor `SheafOfModules.restrictScalars
φ`, so `Adjunction.rightAdjointUniq` identifies them. -/
noncomputable def coextendScalarsIsoHomSheaf (φ : O ⟶ O') :
    coextendScalars φ ≅ RingedSpaceModuleAdjunction.homSheaf φ :=
  Adjunction.rightAdjointUniq (restrictScalars_coextendScalars_adjunction φ)
    (RingedSpaceModuleAdjunction.restrictScalarsHomAdjunction φ)

end Stacks.SheafOfModules.CoextendScalars

end
