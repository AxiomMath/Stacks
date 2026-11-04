module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceDifferentials
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningChartRing
import StacksCore.Tactic.StacksAttribute

/-!
# Differentials of a universal first-order thickening of algebraic spaces

Let `Z ⊂ Z'` be a universal first-order thickening of algebraic spaces over `S`, with structure
morphism `h' : Z' ⟶ X`, let `ι : Z ⟶ Z'` be the inclusion and `h = ι ≫ h'`, and let `p : X ⟶ Y`
be a morphism to a base algebraic space.  Stacks 060E says that the canonical map
`c_{h'} : (h')^*Ω_{X/Y} ⟶ Ω_{Z'/Y}` of Stacks 04CX induces an isomorphism
`h^*Ω_{X/Y} ⟶ Ω_{Z'/Y} ⊗ 𝒪_Z`, that is, that `ι^*c_{h'}` is an isomorphism.

By `AlgebraicGeometry.Space.isIso_restrict_iff_bijective_pushforwardDerivationRestriction` this
holds exactly when, for every `𝒪_Z`-module `F`, restriction along `(h')^♯` is a bijection from
the `Y`-derivations of `𝒪_{Z'}` with values in `ι_*F` onto the `Y`-derivations of `𝒪_X` with
values in `h_*F`.  The module `ι_*F` is killed by the ideal of `Z`
(`AlgebraicGeometry.Space.definingIdealAt_smul_modulePushforward_eq_zero`); on affine squares of
charts the thickening is a universal first-order thickening of rings
(`AlgebraicGeometry.Space.isUniversalFirstOrderThickening_chartDiagramFunctionMap`, through the
étale localization of Stacks 060D); and under those two conditions restriction of derivations is
bijective (`AlgebraicGeometry.Space.injective_pushforwardUniversalDerivation_postcomp` and
`AlgebraicGeometry.Space.surjective_pushforwardUniversalDerivation_postcomp`).

## Main definitions

* `AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.thickeningSheafOfDifferentialsIso`:
  the isomorphism `ι^*(h')^*Ω_{X/Y} ≅ ι^*Ω_{Z'/Y}` of Stacks 060E.

## Main results

* `IsUniversalFirstOrderThickening.isIso_restrict_of_isSheafOfDifferentialsMap`, in the
  namespace `AlgebraicGeometry.Space`: Stacks 060E, for any realization of the comparison map of
  Stacks 04CX.
* `IsUniversalFirstOrderThickening.isIso_thickeningSheafOfDifferentialsMap`, in the same
  namespace: Stacks 060E, for the comparison map as Stacks 04CX constructs it.

## Implementation notes

Formal unramifiedness of `h` is not a hypothesis: a universal first-order thickening is given,
and formal unramifiedness of `h` follows from it by Stacks 0609.  The source takes the spaces over
a base algebraic space `B` and differentials relative to `B`; here the base is the algebraic space
`Y` with structure morphism `p : X ⟶ Y`, and `Z'` lies over `Y` through `h' ≫ p`.

## References

* [Stacks Project, Tag 060E](https://stacks.math.columbia.edu/tag/060E)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z' : AlgebraicSpaces B S hS} {Z : Subfunctor Z'.obj} {h' : Z' ⟶ X}

namespace IsUniversalFirstOrderThickening

/-- For a universal first-order thickening `Z ⊂ Z'` over `X` with structure morphism `h'`, and a
morphism `p : X ⟶ Y`, the restriction along the inclusion `ι : Z ⟶ Z'` of any realization `c` of
the comparison map `(h')^*Ω_{X/Y} ⟶ Ω_{Z'/Y}` is an isomorphism `h^*Ω_{X/Y} ≅ Ω_{Z'/Y} ⊗ 𝒪_Z`. -/
@[stacks 060E]
theorem isIso_restrict_of_isSheafOfDifferentialsMap
    (hZ : IsUniversalFirstOrderThickening B S hS Z h') (p : X ⟶ Y)
    {c : (modulePullback B S hS h').obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS (h' ≫ p)}
    (hc : IsSheafOfDifferentialsMap B S hS h' p (h' ≫ p) c) :
    IsIso ((modulePullback B S hS (universalThickeningInclusion B S hS hZ)).map c) := by
  refine (isIso_restrict_iff_bijective_pushforwardDerivationRestriction B S hS hZ p hc).2
    fun F => ?_
  have hG : ∀ (U : SmallEtale B S hS Z'.1) (x : chartFunctionRing B S hS U),
      x ∈ definingIdealAt B S hS Z' (hZ.closedSub B S hS) (op U) →
      ∀ m : ((modulePushforward B S hS (universalThickeningInclusion B S hS hZ)).obj F).val.obj
        (op U), x • m = 0 :=
    fun U x hx m => definingIdealAt_smul_modulePushforward_eq_zero B S hS
      (hZ.closedSub B S hS) F (op U) x hx m
  have hKL := fun d hU hV =>
    isUniversalFirstOrderThickening_chartDiagramFunctionMap B S hS hZ d hU hV
  exact ⟨injective_pushforwardUniversalDerivation_postcomp B S hS h' _ p
      (hZ.closedSub B S hS) hKL,
    surjective_pushforwardUniversalDerivation_postcomp B S hS h' _ p
      (hZ.closedSub B S hS) hG hKL⟩

/-- For a universal first-order thickening `Z ⊂ Z'` and a morphism `p : X ⟶ Y`, the comparison
map `AlgebraicGeometry.Space.thickeningSheafOfDifferentialsMap` is an isomorphism. -/
@[stacks 060E]
theorem isIso_thickeningSheafOfDifferentialsMap
    (hZ : IsUniversalFirstOrderThickening B S hS Z h') (p : X ⟶ Y) :
    IsIso (thickeningSheafOfDifferentialsMap B S hS hZ p) :=
  hZ.isIso_restrict_of_isSheafOfDifferentialsMap B S hS p
    (isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS h' p (h' ≫ p) (𝟙 Y)
      (Category.comp_id (h' ≫ p)).symm)

/-- The isomorphism `h^*Ω_{X/Y} ≅ Ω_{Z'/Y} ⊗ 𝒪_Z`, written
`ι^*(h')^*Ω_{X/Y} ≅ ι^*Ω_{Z'/Y}` along the inclusion `ι : Z ⟶ Z'`. -/
noncomputable def thickeningSheafOfDifferentialsIso
    (hZ : IsUniversalFirstOrderThickening B S hS Z h') (p : X ⟶ Y) :
    (modulePullback B S hS (universalThickeningInclusion B S hS hZ)).obj
        ((modulePullback B S hS h').obj (sheafOfDifferentials B S hS p)) ≅
      (modulePullback B S hS (universalThickeningInclusion B S hS hZ)).obj
        (sheafOfDifferentials B S hS (h' ≫ p)) :=
  haveI := hZ.isIso_thickeningSheafOfDifferentialsMap B S hS p
  asIso (thickeningSheafOfDifferentialsMap B S hS hZ p)

/-- The forward map of `thickeningSheafOfDifferentialsIso` is
`AlgebraicGeometry.Space.thickeningSheafOfDifferentialsMap`. -/
@[simp]
theorem thickeningSheafOfDifferentialsIso_hom
    (hZ : IsUniversalFirstOrderThickening B S hS Z h') (p : X ⟶ Y) :
    (hZ.thickeningSheafOfDifferentialsIso B S hS p).hom =
      thickeningSheafOfDifferentialsMap B S hS hZ p :=
  rfl

end IsUniversalFirstOrderThickening

end AlgebraicGeometry.Space

end
