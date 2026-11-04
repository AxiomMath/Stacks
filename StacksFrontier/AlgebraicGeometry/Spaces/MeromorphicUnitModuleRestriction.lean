module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicCodimensionZeroProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSections

/-!
# The sheaf of meromorphic functions as a `𝒦_X`-module and as an `𝒪_X`-module

Let `X` be an algebraic space over a scheme `S` of a big fppf site `B`.  Two readings of the
sheaf of meromorphic functions occur in this development and they live in different categories:

* `AlgebraicGeometry.Space.meromorphicModule` reads `𝒦_X` as an **`𝒪_X`-module** with sections
  lifted to the universe `u + 1`, and it is the source of the comparison
  `AlgebraicGeometry.Space.CodimensionZeroPresentation.genericPointModuleComparisonPi` with the
  product over the codimension-zero points;
* `AlgebraicGeometry.Space.meromorphicUnitModule` reads `𝒦_X` as a **`𝒦_X`-module** in the same
  module universe, and it is the source of the comparison with the sheaf
  `AlgebraicGeometry.Space.meromorphicSectionSheaf` of meromorphic sections of a module.

This file supplies the passage from the second reading to the first: restriction of scalars along
the structure map `𝒪_X ⟶ 𝒦_X` at module universe `u + 1`, and the identification of the
restriction of the `𝒦_X`-reading with the `𝒪_X`-reading.

## Main definitions

* `AlgebraicGeometry.Space.meromorphicStructureRingMap` is the structure map `𝒪_X ⟶ 𝒦_X` read
  between the two sheaves of (not necessarily commutative) rings over which the sheaves of
  modules are indexed.
* `AlgebraicGeometry.Space.meromorphicRestrictScalars` is restriction of scalars along it, from
  `𝒦_X`-modules to `𝒪_X`-modules, at the module universe `u + 1` of the sheaves of meromorphic
  sections.
* `AlgebraicGeometry.Space.meromorphicSectionSheafAsModule` is the sheaf of meromorphic sections
  of an `𝒪_X`-module, read as an `𝒪_X`-module through that restriction.

## Main results

* `AlgebraicGeometry.Space.meromorphicRestrictScalars_obj_uliftUnit`: **the `𝒦_X`-reading of
  `𝒦_X` restricts to the `𝒪_X`-reading**, and it does so by `Eq.refl`: the two differ only in
  which sheaf of rings acts, the presheaf of abelian groups and the universe lift being the same
  in both.

## Implementation notes

The module universe has to be ascribed before `SheafOfModules.restrictScalars` is applied.
Elaborating `(SheafOfModules.restrictScalars α).obj M` with the module universe left to
unification fails: the `CategoryTheory.Category` instance on the source category is sought while
that universe is still a metavariable, and the search reports
`failed to synthesize Category.{u + 1, u + 2} (SheafOfModules …)` even though the instance is
found at once when the universe is written.  That is why
`AlgebraicGeometry.Space.meromorphicRestrictScalars` is given as a functor with its type written
out, rather than applied inline at each use.

What this file does **not** supply is the converse passage: that a morphism of `𝒦_X`-modules
whose restriction of scalars is an isomorphism is itself an isomorphism.  The two underlying
objects are presheaves of modules over *different* sheaves of rings, so the inverse cannot be
transported by `SheafOfModules.hom_ext` on the underlying morphisms; what it needs is that
`SheafOfModules.restrictScalars` reflects isomorphisms, through
`PresheafOfModules.restrictScalarsIsoToPresheaf` and the linearity of the inverse of a morphism
of presheaves of modules whose underlying morphism of presheaves of abelian groups is invertible.

## References

* [Stacks Project, Tag 0EN3](https://stacks.math.columbia.edu/tag/0EN3)
* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The structure map `𝒪_X ⟶ 𝒦_X` of Stacks 0EN3, read between the two sheaves of rings over
which the sheaves of modules of this development are indexed: commutativity is forgotten, which
is the form `SheafOfModules.restrictScalars` consumes. -/
noncomputable def meromorphicStructureRingMap :
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS F hF).O) :=
  (sheafCompose (SmallEtale.topology B S hS F)
    (forget₂ CommRingCat.{u} RingCat.{u})).map (toMeromorphicFunctionSheaf B S hS F hF)

/-- **Restriction of scalars from `𝒦_X`-modules to `𝒪_X`-modules**, at the module universe
`u + 1` of the sheaves of meromorphic sections. -/
noncomputable def meromorphicRestrictScalars :
    SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS F hF).O) ⥤
      Modules.{u, u + 1} B S hS F hF :=
  SheafOfModules.restrictScalars (meromorphicStructureRingMap B S hS F hF)

/-- **`𝒦_X` read as a `𝒦_X`-module restricts to `𝒦_X` read as an `𝒪_X`-module.**  Both are the
universe lift of the same presheaf of abelian groups; only the acting sheaf of rings differs, and
restriction of scalars changes nothing else.

The source is `AlgebraicGeometry.Space.meromorphicUnitModule` written out, and the target is
`AlgebraicGeometry.Space.meromorphicModule`, the source of the comparison of the first conclusion
of Stacks 0ENA. -/
theorem meromorphicRestrictScalars_obj_uliftUnit :
    (meromorphicRestrictScalars B S hS F hF).obj
        (SheafOfModules.uliftObj.{_, _, _, _, u + 1}
          (SheafOfModules.unit
            (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS F hF).O))) =
      meromorphicModule B S hS ⟨F, hF⟩ :=
  rfl

/-- The sheaf of meromorphic sections `𝒦_X(M)` of Stacks 0EN5 of an `𝒪_X`-module `M`, read as an
`𝒪_X`-module in the module universe `u + 1` through restriction of scalars. -/
noncomputable def meromorphicSectionSheafAsModule (M : Modules.{u, u} B S hS F hF) :
    Modules.{u, u + 1} B S hS F hF :=
  (meromorphicRestrictScalars B S hS F hF).obj
    (meromorphicSectionSheaf.{u, u} B S hS F hF M)

end AlgebraicGeometry.Space

end
