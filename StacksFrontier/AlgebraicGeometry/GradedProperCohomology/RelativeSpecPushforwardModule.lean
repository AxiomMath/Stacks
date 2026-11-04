module

public import StacksFrontier.AlgebraicGeometry.RelativeSpecQcohEquivalence.Basic

/-!
# The equivalence of Tag 01SB is the direct image of modules

Let `S` be a scheme and `A` a quasi-coherent sheaf of commutative `𝒪_S`-algebras, with relative
spectrum `π : Spec_S A ⟶ S`.  [Stacks, Tag 01SB] is recorded as the equivalence
`Stacks.AffineAlgebraEquivalence.relativeSpecQcohEquivalence` from the quasi-coherent modules on
`Spec_S A` to the quasi-coherent `A`-modules, and
`relativeSpecQcohEquivalence_functor_obj_obj` describes its value as the direct image over
`π_* 𝒪`, with scalars transported along the isomorphism `π_* 𝒪 ≅ A` of [Stacks, Tag 01LX] (3).

This file shows that, read as an `𝒪_S`-module with the `A`-action forgotten, that value is the
direct image `π_* ℱ` of `𝒪_S`-modules.

## Main results

* `Stacks.AffineAlgebraEquivalence.restrictScalars_relativeSpecQcohEquivalence_functor_obj`:
  restricting the scalars of `(relativeSpecQcohEquivalence A).functor.obj ℱ` along the structure
  map of `A` gives `(Scheme.Modules.pushforward π).obj ℱ`.

## References

* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.AffineQcohPushforward
open Stacks.RelativeSpec (AlgebraSheaf)

universe u

namespace Stacks.AffineAlgebraEquivalence

variable {S : Scheme.{u}} (A : Stacks.RelativeSpec.AlgebraSheaf S)
  [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A]

/-- **The functor of [Stacks, Tag 01SB] at the relative spectrum is the direct image of
`𝒪_S`-modules, once the `A`-action is forgotten.** For a quasi-coherent module `ℱ` on
`Spec_S A`, restricting the scalars of `(relativeSpecQcohEquivalence A).functor.obj ℱ` along the
structure map of `A` gives `π_* ℱ`. -/
public theorem restrictScalars_relativeSpecQcohEquivalence_functor_obj
    (M : (SheafOfModules.isQuasicoherent (relativeSpec A).ringCatSheaf).FullSubcategory) :
    (SheafOfModules.restrictScalars.{u} (AlgebraSheaf.structureMap A)).obj
        ((relativeSpecQcohEquivalence A).functor.obj M).obj =
      (Scheme.Modules.pushforward (relativeSpecToBase A)).obj M.obj := by
  have hcomp : AlgebraSheaf.structureMap A ≫ (pushforwardRingIso A).inv =
      (relativeSpecToBase A).toRingCatSheafHom :=
    (Iso.comp_inv_eq (pushforwardRingIso A)).2
      (structureMap_comp_pushforwardRingIso A).symm
  rw [relativeSpecQcohEquivalence_functor_obj_obj,
    ← restrictScalars_pushforwardModules (relativeSpecToBase A), ← hcomp]
  rfl

end Stacks.AffineAlgebraEquivalence

end
