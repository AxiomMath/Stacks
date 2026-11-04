module

public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections

/-!
# `A`-linear global sections, at the sheaf-of-modules spelling

`AlgebraicGeometry.globalSectionsOver`
(`StacksFrontier/AlgebraicGeometry/DerivedGlobalSections.lean:118`) is stated with source
`X.Modules`. This module states the same functor with its source written
`SheafOfModules X.ringCatSheaf`.

## Main definitions

* `AlgebraicGeometry.secsOver`: `A`-linear global sections of a scheme over `A`, with source
  spelled `SheafOfModules X.ringCatSheaf`.

## Implementation notes

The two spellings are definitionally equal — `X.Modules` is the scheme API's alias for
`SheafOfModules X.ringCatSheaf` — but they carry separately declared `Category` and `Preadditive`
instances, and instance search does not cross between them. `DerivedGlobalSections.lean` records
that at its line 65 and deliberately keeps every declaration in the `X.Modules` view, so a
consumer working in the other view gets no instances from it.

Two consumers each wrote that view out for themselves — `secsOver` in
`StacksFrontier/AlgebraicGeometry/AffineVanishingQuasicoherentComplex.lean` and
`globalSectionsOverBase` in
`StacksFrontier/AlgebraicGeometry/ResolutionOfSurfaces/Vanishing/PuncturedBaseCohomology.lean`, the
latter with a body character-identical to `globalSectionsOver`'s. It is declared once here
instead, in a module whose only import is the one carrying `globalSectionsOver`, so that either
consumer reaches it without acquiring the other's machinery.

It is a `def` rather than an `abbrev` deliberately: the consumers' instances are re-exposed by
`inferInstanceAs` across the spelling, which is the behaviour a semireducible definition gives.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry

open CategoryTheory Opposite

universe u

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **`A`-linear global sections at the sheaf-of-modules spelling.** Global sections of a sheaf of
`𝒪_X`-modules regarded as an `A`-module by restriction of scalars along
`A ≅ Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)`, with the source written `SheafOfModules X.ringCatSheaf` rather
than `X.Modules`. -/
def secsOver : SheafOfModules.{u} X.ringCatSheaf ⥤ ModuleCat.{u} A := globalSectionsOver f

/-- `A`-linear global sections is additive at this spelling too; addition of sections of a sheaf
of modules is computed open by open. -/
instance secsOver_additive : (secsOver f).Additive :=
  inferInstanceAs ((globalSectionsOver f).Additive)

end AlgebraicGeometry

end
