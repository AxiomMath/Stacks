module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.RestrictPullbackTopDegreeBridge
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorComparisonScalar
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.HmulProjectionPaste

/-!
# Multiplication crosses the two spellings of the cohomology upstairs

The last factor of
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDegreeFunctorObjIsoCohomologyUpstairs` is
`…TopDegreeBaseChange.restrictPullbackRightDerivedPlusIso`, which reconciles the two spellings of
the degree-`d` cohomology of the pullback of `F'` over `f''⁻¹(W)`: the `ℤ`-indexed derived
functor of the restriction of the pullback along the whole of `h'`, and the `ℕ`-indexed derived
functor of the pullback along the restricted `h'` of the restriction of `F'`.

This file proves that multiplication by a function on `W` crosses it. Nothing geometric is
involved: the factor is built from two isomorphisms that are natural in the module —
`Stacks.DerivedIndexing.rightDerivedIso` and `Stacks.Modules.restrictPullbackIso` — and
multiplication by a function on `W`, being `AlgebraicGeometry.baseScalar` for the structure
morphism `(f'' ∣_ W) ≫ W.toSpecΓ`, is an element of the centre of the category of module sheaves
on `f''⁻¹(W)` and therefore commutes with every morphism there.

## Main results

* `…TopDegreeBaseChange.preimageScalar_comp_restrictPullbackRightDerivedPlusIso_inv`:
  **multiplication by a function on `W` crosses the comparison of the two spellings of the
  cohomology upstairs.**

## Implementation notes

*The two halves come from different mechanisms, and neither is new.* The commutation of
multiplication with the restriction-pullback crossing is the centrality of
`AlgebraicGeometry.baseScalar`, used as in
`…TopDegreeBaseChange.conjugateRestrict_scalar`; the commutation with the change of indexing is
the naturality of `Stacks.DerivedIndexing.rightDerivedIso`, which is a natural isomorphism of
functors. The degree-`d` cohomology functor then carries the first square along, by
`…TopDegreeBaseChange.map_comp_square`.

*Why the statement is about the inverse.* The comparison appears in
`topDegreeFunctorObjIsoCohomologyUpstairs` through its `symm`, so the square the composite needs
is the one across the inverse; the inverse of an `Iso.trans` is the reversed composite, which is
why the factors below are pasted in the opposite order to the definition.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **Multiplication by a function on `W` crosses the comparison of the two spellings of the
cohomology upstairs.** For a morphism `h' : X'' ⟶ X'` over opens `V` of `Y'` and `W` of `Y''`
with `f''⁻¹(W) ≤ (h')⁻¹(f'⁻¹(V))`, a module `F'` on `X'`, a degree `d` and a function `r` on
`W`, multiplication by `r` commutes with the inverse of
`…TopDegreeBaseChange.restrictPullbackRightDerivedPlusIso`.

Multiplication by `r` is `AlgebraicGeometry.baseScalar` for the structure morphism of `f''⁻¹(W)`
over `Γ(W, ⊤)`, hence central, which crosses the restriction-pullback comparison; the change of
indexing is crossed by the naturality of `Stacks.DerivedIndexing.rightDerivedIso`. -/
theorem preimageScalar_comp_restrictPullbackRightDerivedPlusIso_inv
    {X' Y' X'' Y'' : Scheme.{u}} {f' : X' ⟶ Y'} (h' : X'' ⟶ X') {f'' : X'' ⟶ Y''}
    {h : Y'' ⟶ Y'} {V : Y'.Opens} {W : Y''.Opens}
    (hle : f'' ⁻¹ᵁ W ≤ h' ⁻¹ᵁ (f' ⁻¹ᵁ V)) (F' : X'.Modules) (d : ℕ)
    (r : Γ((W : Scheme), ⊤)) :
    ((moduleGlobalSections (f'' ⁻¹ᵁ W : Scheme)).rightDerived d).map
          (preimageScalar f'' W r
            ((Scheme.Modules.pullback (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle)).obj
              ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F'))) ≫
        (restrictPullbackRightDerivedPlusIso (h := h) h' hle F' d).inv =
      (restrictPullbackRightDerivedPlusIso (h := h) h' hle F' d).inv ≫
        ((moduleGlobalSections (f'' ⁻¹ᵁ W : Scheme)).rightDerivedPlus (d : ℤ)).map
          (preimageScalar f'' W r
            ((Scheme.Modules.restrictFunctor (f'' ⁻¹ᵁ W).ι).obj
              ((Scheme.Modules.pullback h').obj F'))) :=
  comp_two_squares
    (map_comp_square ((moduleGlobalSections (f'' ⁻¹ᵁ W : Scheme)).rightDerived d)
      ((AlgebraicGeometry.baseScalar ↑Γ((W : Scheme), ⊤)
          (Over.mk ((f'' ∣_ W) ≫ (W : Scheme).toSpecΓ) :
            Over (Spec (CommRingCat.of ↑Γ((W : Scheme), ⊤)))) r).naturality
        (Stacks.Modules.restrictPullbackObjIso h' hle F').inv).symm)
    ((Stacks.DerivedIndexing.rightDerivedIso
          (moduleGlobalSections (f'' ⁻¹ᵁ W : Scheme)) d).hom.naturality
      (preimageScalar f'' W r
        ((Scheme.Modules.restrictFunctor (f'' ⁻¹ᵁ W).ι).obj
          ((Scheme.Modules.pullback h').obj F'))))

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
