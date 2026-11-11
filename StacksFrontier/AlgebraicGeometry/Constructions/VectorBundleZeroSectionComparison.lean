module

public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundlePoints
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleZeroSectionConormal
public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.Basis

/-!
# The two zero sections of a vector bundle agree

Let `S` be a scheme, `ℰ` a quasi-coherent `𝒪_S`-module and `𝐕(ℰ) = Spec_S(Sym(ℰ))` its vector
bundle. The repository carries two zero sections `S ⟶ 𝐕(ℰ)`:

* `AlgebraicGeometry.Scheme.Modules.vectorBundleZeroSection`, the section of the relative
  spectrum cut out by the augmentation `Sym(ℰ) ⟶ 𝒪_S` (the definition of [EGA II, 1.7.9]);
* `AlgebraicGeometry.Scheme.Modules.vectorBundleOverZeroSection`, the point of `𝐕(ℰ)` over `𝟙 S`
  whose module morphism `ℰ ⟶ 𝒪_S` under the functor of points
  `AlgebraicGeometry.Scheme.Modules.vectorBundleHomEquiv` is zero.

This file proves that they are the same morphism: the morphism of algebras `Sym(ℰ) ⟶ 𝒪_S` that
the first induces on pushed-forward structure sheaves is the augmentation, and the augmentation
kills the degree-one summand `ℰ`, so the module morphism of the first is zero.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.vectorBundleZeroSectionOver`: the zero section
  `vectorBundleZeroSection`, as a morphism of schemes over `S`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.vectorBundleHomEquiv_vectorBundleZeroSectionOver`: the module
  morphism of the zero section cut out by the augmentation is zero.
* `AlgebraicGeometry.Scheme.Modules.vectorBundleOverZeroSection_left`: **the two zero sections
  agree.**

## References

* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]

/-- **The zero section `S ⟶ 𝐕(ℰ)` cut out by the augmentation, as a morphism over `S`.** -/
def vectorBundleZeroSectionOver : Over.mk (𝟙 S) ⟶ vectorBundleOver S (F := E) :=
  Over.homMk (vectorBundleZeroSection S E) (vectorBundleZeroSection_comp_vectorBundleToBase S E)

/-- **The module morphism of the zero section cut out by the augmentation is zero**: on a local
section of `ℰ` over an affine open, it is the augmentation evaluated on the corresponding
degree-one section of `Sym(ℰ)`, which vanishes. -/
theorem vectorBundleHomEquiv_vectorBundleZeroSectionOver :
    vectorBundleHomEquiv E _ (vectorBundleZeroSectionOver E) =
      (0 : E ⟶ structurePushforward (𝟙 S)) := by
  have hB : Opens.IsBasis (Set.range fun U : S.affineOpens => U.1) := by
    simpa using S.isBasis_affineOpens
  refine Stacks.AlgebraicGeometry.ModuleHomGlue.hom_ext_of_isBasis hB fun U s => ?_
  have := isAffineHom_vectorBundleOver S (F := E)
  have hf := vectorBundleHomEquiv_apply E (Over.mk (𝟙 S)) (vectorBundleZeroSectionOver E)
  refine (congrArg (fun φ : E ⟶ structurePushforward (𝟙 S) => (φ.app U.1).hom s) hf).trans ?_
  change (((symmetricAlgebraSheafComparison E).hom ≫ (vectorBundlePushforwardIso S (F := E)).inv ≫
      pushforwardAlgebraMap (vectorBundleZeroSectionOver E)).right.hom.app (op U.1)).hom
        (ungradedAlgebraSheafIncl S (symmetricAlgebra S E) (symmetricAlgebra_mul_comm S E) 1 U.1
          ((symmetricAlgebraGen S E).val.app (op U.1) s)) = 0
  set x := (symmetricAlgebraGen S E).val.app (op U.1) s
  change ((pushforwardAlgebraMap (vectorBundleZeroSectionOver E)).right.hom.app (op U.1)).hom
      (((vectorBundlePushforwardIso S (F := E)).inv.right.hom.app (op U.1)).hom
        (((ungradedToGradedRight S (symmetricAlgebra S E) (symmetricAlgebra_mul_comm S E)).hom.app
          (op U.1)).hom (ungradedAlgebraSheafIncl S (symmetricAlgebra S E)
            (symmetricAlgebra_mul_comm S E) 1 U.1 x))) = 0
  rw [ungradedToGradedRight_ungradedAlgebraSheafIncl,
    pushforwardAlgebraMap_app _ _ (preimage_le_preimage_preimage _ U.1)]
  have h := pairToHom_appLE (retractionPair (vectorBundleSituation S E)
    (symmetricAlgebraSheafAugmentation S E) (hom_comp_symmetricAlgebraSheafAugmentation S E)) U
    (preimage_le_preimage_preimage (vectorBundleZeroSectionOver E) U.1)
  refine (ConcreteCategory.congr_hom h ((symmetricAlgebra S E).ungradedIncl 1 x)).trans ?_
  refine (Stacks.SymAlgSections.symmetricAlgebraSheafAugmentation_app_totalUnit E (op U.1)
    ((Stacks.SymAlgSections.symPresheafAlgebra E).incl 1 x)).trans ?_
  exact Stacks.SymAlgSections.symmetricAlgebraTotalAugmentation_app_incl_of_ne E one_ne_zero
    (op U.1) x

/-- **The two zero sections of `𝐕(ℰ)` agree, as morphisms over `S`**: the point of `𝐕(ℰ)` whose
module morphism is zero is the section cut out by the augmentation `Sym(ℰ) ⟶ 𝒪_S`. -/
theorem vectorBundleOverZeroSection_eq_vectorBundleZeroSectionOver :
    vectorBundleOverZeroSection E = vectorBundleZeroSectionOver E :=
  (vectorBundleHomEquiv E _).injective
    ((vectorBundleHomEquiv_vectorBundleOverZeroSection E).trans
      (vectorBundleHomEquiv_vectorBundleZeroSectionOver E).symm)

/-- **The two zero sections of `𝐕(ℰ)` agree**: the morphism of schemes underlying the point of
`𝐕(ℰ)` whose module morphism is zero is the zero section `vectorBundleZeroSection`, the section
of the relative spectrum cut out by the augmentation `Sym(ℰ) ⟶ 𝒪_S`. -/
theorem vectorBundleOverZeroSection_left :
    (vectorBundleOverZeroSection E).left = vectorBundleZeroSection S E :=
  congrArg (fun h => h.left) (vectorBundleOverZeroSection_eq_vectorBundleZeroSectionOver E)

end AlgebraicGeometry.Scheme.Modules

end
