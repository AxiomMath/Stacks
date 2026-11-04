module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.CoherentModuleFunctors.EquivalenceOverBase
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Equivalence
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.HmulProjectionScalar

/-!
# Multiplication by a global function, and its cohomology

Conclusion (c) of [Stacks, Tag 0EX3] needs multiplication by a function to be pushed through the
whole computation of the right-hand end of its comparison map, and the computation passes through
several categories of module sheaves. Two operators for that multiplication are already in the
library: `AlgebraicGeometry.baseScalar`, multiplication by an element of the base ring of a
scheme over `Spec R`, and `AlgebraicGeometry.IntegralTransformQcoh.sectionScalar`, multiplication
by a global function on the scheme itself. The first carries the linearity of the derived
functors; the second is the one whose compatibility with the pullback of the structure sheaf and
with the unitors of the tensor product is proved.

This file identifies them, and draws the consequence the computation actually consumes: **the
degree-`n` cohomology of multiplication by a global function `c` is multiplication by `c`** —
with no morphism and no base ring in the statement, because `sectionScalar` needs neither.

## Main results

* `…TopDegreeBaseChange.sectionScalar_eq_baseScalar`: **multiplication by the image of a base
  scalar in the global functions is multiplication by that base scalar.** Both are the scalar
  action of the `R`-linear structure on module sheaves, which is how they are compared.
* `…TopDegreeBaseChange.rightDerived_moduleGlobalSections_map_sectionScalar` and
  `…TopDegreeBaseChange.rightDerivedPlus_moduleGlobalSections_map_sectionScalar`: **the
  degree-`n` cohomology of multiplication by a global function is multiplication by that
  function**, for Mathlib's `ℕ`-indexed and for the `ℤ`-indexed right derived functors.

## Implementation notes

*Why the cohomology statement needs no morphism.* Its `baseScalar` ancestor
`…TopDegreeBaseChange.rightDerived_moduleGlobalSections_map_baseScalar` is about a scheme over
`Spec R` and an element of `R`. Every scheme is canonically a scheme over the spectrum of its own
global functions, by `AlgebraicGeometry.Scheme.toSpecΓ`, and over that structure morphism the
image of a global function in the global functions is itself; so the general statement
specialises to one that mentions only the scheme and the function.

*The image of a global function in itself.* That specialisation is
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.baseRingToSections_toSpecΓ` at the top open,
where the restriction map it produces is the identity — the step of
`…TopDegreeBaseChange.baseRingToSections_comp_toSpecΓ_top`.

*Why `CategoryTheory.HasDerivedCategory.standard` is given a raised local priority.* The module
that carries `sectionScalar` brings a second `HasDerivedCategory` instance into scope, and under
it `CategoryTheory.Functor.rightDerivedPlus` elaborates at a different universe — a *different*
functor from the one the library's statements about the derived pushforward are about, so that the
two cannot be composed. Raising the priority of the standard instance fixes the choice. Any
module importing this one inherits the second instance and needs the same line.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.CoherentModuleFunctors
open AlgebraicGeometry.IntegralTransformQcoh
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 100000] HasDerivedCategory.standard

/-- **Multiplication by the image of a base scalar in the global functions is multiplication by
that base scalar.** For a scheme `X` over `Spec R`, an `r : R` and a module `M` on `X`,
multiplication by the image of `r` in `Γ(X, ⊤)` is `AlgebraicGeometry.baseScalar` at `r`.

Both are the action of `r` from the `R`-linear structure
`AlgebraicGeometry.modulesLinear` on module sheaves: for the left-hand side that is
`AlgebraicGeometry.IntegralTransformQcoh.sectionScalar_base`, for the right-hand side
`AlgebraicGeometry.CoherentModuleFunctors.smul_id_eq_baseScalar`. -/
theorem sectionScalar_eq_baseScalar (R : Type u) [CommRing R]
    (X : Over (Spec (CommRingCat.of R))) (r : R) (M : X.left.Modules) :
    sectionScalar X.left (AlgebraicGeometry.baseRingToSections R X (op ⊤) r) M =
      (AlgebraicGeometry.baseScalar R X r).app M := by
  let : Linear R (_root_.SheafOfModules.{u} X.left.ringCatSheaf) :=
    AlgebraicGeometry.modulesLinear R X
  refine Eq.trans
    (congrArg (fun z => sectionScalar X.left z M) (baseRingToSections_top R X r)) ?_
  exact Eq.trans (sectionScalar_base R X r M) (smul_id_eq_baseScalar R X r M)

/-- **The image of a global function in the global functions, over the canonical structure
morphism, is the function itself.** This is
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.baseRingToSections_toSpecΓ` at the top open,
where the restriction map it produces is the identity. -/
theorem baseRingToSections_toSpecΓ_top (Z : Scheme.{u}) (c : Γ(Z, ⊤)) :
    AlgebraicGeometry.baseRingToSections ↑Γ(Z, ⊤)
        (Over.mk Z.toSpecΓ : Over (Spec (CommRingCat.of ↑Γ(Z, ⊤)))) (op ⊤) c = c := by
  refine Eq.trans (SchemeHigherDirectImage.baseRingToSections_toSpecΓ Z (op ⊤) c) ?_
  rw [show ((⊤ : Z.Opens)).leTop = 𝟙 (⊤ : Z.Opens) from rfl, op_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- **Multiplication by a global function is a base scalar, over the canonical structure
morphism.** This is `sectionScalar_eq_baseScalar` for the scheme read over the spectrum of its
own global functions, where the image of `c` is `c` itself. -/
theorem sectionScalar_eq_baseScalar_toSpecΓ (Z : Scheme.{u}) (c : Γ(Z, ⊤)) (M : Z.Modules) :
    sectionScalar Z c M =
      (AlgebraicGeometry.baseScalar ↑Γ(Z, ⊤)
        (Over.mk Z.toSpecΓ : Over (Spec (CommRingCat.of ↑Γ(Z, ⊤)))) c).app M :=
  Eq.trans
    (congrArg (fun z => sectionScalar Z z M) (baseRingToSections_toSpecΓ_top Z c).symm)
    (sectionScalar_eq_baseScalar ↑Γ(Z, ⊤) (Over.mk Z.toSpecΓ) c M)

/-- **The degree-`n` cohomology of multiplication by a global function is multiplication by that
function.** For a scheme `Z`, a global function `c` on it and a module `M`, the degree-`n`
cohomology of the endomorphism "multiply by `c`" of `M` is multiplication by `c` on
`H^n(Z, M)`.

This is `…TopDegreeBaseChange.rightDerived_moduleGlobalSections_map_baseScalar` for `Z` read over
the spectrum of its own global functions. -/
theorem rightDerived_moduleGlobalSections_map_sectionScalar (Z : Scheme.{u}) (n : ℕ)
    (c : Γ(Z, ⊤)) (M : Z.Modules) :
    ((moduleGlobalSections Z).rightDerived n).map (sectionScalar Z c M) =
      c • 𝟙 (((moduleGlobalSections Z).rightDerived n).obj M) :=
  Eq.trans
    (congrArg (fun z => ((moduleGlobalSections Z).rightDerived n).map z)
      (sectionScalar_eq_baseScalar_toSpecΓ Z c M))
    (rightDerived_moduleGlobalSections_map_baseScalar ↑Γ(Z, ⊤)
      (Over.mk Z.toSpecΓ : Over (Spec (CommRingCat.of ↑Γ(Z, ⊤)))) n c M c
      (baseRingToSections_toSpecΓ_top Z c))

/-- **The `ℤ`-indexed form of `rightDerived_moduleGlobalSections_map_sectionScalar`.** -/
theorem rightDerivedPlus_moduleGlobalSections_map_sectionScalar (Z : Scheme.{u}) (n : ℕ)
    (c : Γ(Z, ⊤)) (M : Z.Modules) :
    ((moduleGlobalSections Z).rightDerivedPlus (n : ℤ)).map (sectionScalar Z c M) =
      c • 𝟙 (((moduleGlobalSections Z).rightDerivedPlus (n : ℤ)).obj M) :=
  Eq.trans
    (congrArg (fun z => ((moduleGlobalSections Z).rightDerivedPlus (n : ℤ)).map z)
      (sectionScalar_eq_baseScalar_toSpecΓ Z c M))
    (rightDerivedPlus_moduleGlobalSections_map_baseScalar ↑Γ(Z, ⊤)
      (Over.mk Z.toSpecΓ : Over (Spec (CommRingCat.of ↑Γ(Z, ⊤)))) n c M c
      (baseRingToSections_toSpecΓ_top Z c))

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
