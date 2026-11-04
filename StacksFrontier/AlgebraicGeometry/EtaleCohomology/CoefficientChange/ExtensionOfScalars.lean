module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Sites.Adjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RestrictionOfScalars

/-!
# Extension of coefficients for sheaves of modules on the small étale site

Let `φ : Λ₁ → Λ₂` be a homomorphism of commutative rings and let `X` be a scheme.  Restriction
of coefficients `Stacks.EtaleCohomology.etaleModuleRestrictScalarsUniv` has a left adjoint,
obtained by tensoring the sections with `Λ₂` over `Λ₁` and sheafifying.  This file records that
functor and the adjunction.

The adjunction is the engine of the proof of [Stacks, Tag 0GL6]: restriction of coefficients
does *not* preserve K-injective complexes — its left adjoint is not exact unless `Λ₂` is flat
over `Λ₁`, as `ℤ/2 ⊗ (0 → ℤ → ℤ → 0)` already shows — so the comparison of the two derived
direct images cannot be read off from a K-injective resolution.  What replaces that is the
adjunction below, through which morphisms out of a complex on which extension of coefficients is
exact are computed in the homotopy category rather than the derived category.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleExtendScalarsUniv`: the functor `L`, sheafification of the
  sectionwise `- ⊗_{Λ₁} Λ₂`.
* `Stacks.EtaleCohomology.etaleModuleExtendRestrictAdj`: the adjunction `L ⊣ res`.

## Implementation notes

`L` is Mathlib's `CategoryTheory.Sheaf.composeAndSheafify` of `ModuleCat.extendScalars φ`, and
the adjunction is `CategoryTheory.Sheaf.adjunction` applied to
`ModuleCat.extendRestrictScalarsAdj φ`; no sheaf-level work is needed, the sheafification of
module-valued presheaves on the small étale site being
`Stacks.EtaleCohomology.etaleModules_hasSheafify`.

Mathlib constructs extension of scalars for commutative rings only, which is why the
coefficient rings here are commutative.  The source states Tag 0GL6 for torsion rings, and rings
are commutative under the conventions of the Stacks project, so this is the generality of the
tag.

`L` is *not* recorded as preserving sheafification or anything else exactness-like, and must not
be: it is right exact and nothing more, and that is the whole difficulty of the tag.

## References

* [Stacks Project, Tag 0GL6](https://stacks.math.columbia.edu/tag/0GL6)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

variable {Λ₁ Λ₂ : Type r} [CommRing Λ₁] [CommRing Λ₂] (φ : Λ₁ →+* Λ₂)

/-- **Extension of coefficients.**  The left adjoint of restriction of coefficients: tensor the
sections with `Λ₂` over `Λ₁`, then sheafify. -/
abbrev etaleModuleExtendScalarsUniv (X : Scheme.{u}) :
    EtaleModules.{u, r} Λ₁ X ⥤ EtaleModules.{u, r} Λ₂ X :=
  Sheaf.composeAndSheafify X.smallEtaleTopology
    (ModuleCat.extendScalars.{r, r, max (u + 1) r} φ)

/-- **Extension of coefficients is left adjoint to restriction of coefficients.**  This is
`ModuleCat.extendRestrictScalarsAdj` carried to sheaves. -/
def etaleModuleExtendRestrictAdj (X : Scheme.{u}) :
    etaleModuleExtendScalarsUniv.{u, r} φ X ⊣ etaleModuleRestrictScalarsUniv.{u, r} φ X :=
  Sheaf.adjunction X.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{max (u + 1) r, r, r} φ)

end Stacks.EtaleCohomology

end
