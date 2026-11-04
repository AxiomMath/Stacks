module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonBraided
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerMapMultiplication
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerPullback

/-!
# Pullback commutes with the multiplication of the integral tensor powers

Let `f : X ⟶ Y` be a morphism of ringed spaces and `L` an invertible sheaf of `𝒪_Y`-modules.
`Stacks.TensorPowerPullback.pullbackIntPowIso` compares the integral tensor powers of Tag 01CU,
`f^*(L^{⊗ n}) ≅ (f^*L)^{⊗ n}`. This file proves that the comparison is **multiplicative**: it
carries the coherent multiplication `L^{⊗ n} ⊗ L^{⊗ m} ≅ L^{⊗ (n + m)}` of Tag 01CU for `L` to
the one for `f^*L`, in every pair of integer degrees.

## Main results

* `Stacks.TensorPowerPullback.isLeftUnital_pullback`,
  `isRightUnital_pullback`, `isNaturalLeft_pullback`, `isNaturalRight_pullback`,
  `isAssociative_pullback` and `isSymmetric_pullback`: the six compatibilities of the comparison
  of Tag 01CD that the multiplicativity statement takes as inputs, supplied for the pullback.
* `Stacks.TensorPowerPullback.pullbackIntPowIso_coherentMulIso`: **the comparison of integral
  tensor powers is multiplicative.**

## Implementation notes

The work is done abstractly in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerMapMultiplication`, for any functor
compatible with the tensor product of Tag 01CA; this file only supplies the six compatibilities.
Each is the corresponding lemma of `Stacks.PullbackTensorCoherence`, retyped from the whiskering
and unitor vocabulary of the monoidal structure to the
`Stacks.SheafOfModules.TensorPower.tensorSheafMapIso` and
`Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso` vocabulary of the coherence structure of
Tag 01CU.

**No `@[stacks]` attribute.** Tag 01CD is carried by `Stacks.RingedSpace.comparisonIso` and
Tag 01CU by the integral tensor powers with their coherent multiplication; the compatibility
below is a consequence of those, not a further assertion of the source.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry

open Stacks.RingedSpace Stacks.PullbackTensorCoherence

open Stacks.SheafOfModules.TensorPower

universe u

namespace Stacks.TensorPowerPullback

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
  Stacks.PullbackTensorCoherence.braidedCategory

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The comparison of Tag 01CD as a tensorator in both slots**, `f^*(M ⊗ N) ≅ f^*M ⊗ f^*N`.
`Stacks.TensorPowerPullback.pullbackTensorFactorIso` is its restriction to a fixed second
factor, which is what the comparison of tensor powers consumes. -/
def pullbackTensorator (M N : SheafOfModules.{u} (structureRingSheaf Y)) :
    (pullbackFunctor f).obj (M ⊗ N) ≅
      (pullbackFunctor f).obj M ⊗ (pullbackFunctor f).obj N :=
  asIso (pullbackTensorComparison f M N)

variable (L : SheafOfModules.{u} (structureRingSheaf Y))
  [Stacks.SheafOfModules.IsInvertible Y.presheaf (isSheafStructure Y) L]

omit [Stacks.SheafOfModules.IsInvertible Y.presheaf (isSheafStructure Y) L] in
/-- The tensorator restricted to the second factor `L` is the tensor comparison the comparison
of tensor powers is built from. -/
theorem pullbackTensorator_eq_tensorFactorComparison :
    (fun M => pullbackTensorator f M L) = tensorFactorComparison f L := rfl

/-- The comparison of tensor powers determined by the tensorator is
`Stacks.TensorPowerPullback.pullbackIntPowIso`. -/
theorem tensorPowerComparison_eq_pullbackIntPowIso (n : ℤ) :
    tensorPowerComparison Y.presheaf (isSheafStructure Y) X.presheaf (isSheafStructure X)
        (pullbackFunctor f) L (pullbackTensorator f) (pullbackUnitSheafIso f) n =
      pullbackIntPowIso f L n := rfl

/-! ### The six compatibilities of the comparison of Tag 01CD -/

/-- The comparison of Tag 01CD is natural in the first variable. -/
theorem isNaturalLeft_pullback :
    IsNaturalLeft Y.presheaf (isSheafStructure Y) X.presheaf (isSheafStructure X)
      (pullbackFunctor f) (pullbackTensorator f) :=
  fun u => pullbackTensorComparison_naturality_left f u

/-- The comparison of Tag 01CD is natural in the second variable. -/
theorem isNaturalRight_pullback :
    IsNaturalRight Y.presheaf (isSheafStructure Y) X.presheaf (isSheafStructure X)
      (pullbackFunctor f) (pullbackTensorator f) :=
  fun v => pullbackTensorComparison_naturality_right f v

/-- The comparison of Tag 01CD is compatible with the associativity constraint of Tag 01CA. -/
theorem isAssociative_pullback :
    IsAssociative Y.presheaf (isSheafStructure Y) X.presheaf (isSheafStructure X)
      (pullbackFunctor f) (pullbackTensorator f) :=
  fun A N P => pullbackTensorComparison_associator f A N P

/-- The comparison of Tag 01CD is compatible with the symmetry constraint of Tag 01CA. -/
theorem isSymmetric_pullback :
    IsSymmetric Y.presheaf (isSheafStructure Y) X.presheaf (isSheafStructure X)
      (pullbackFunctor f) (pullbackTensorator f) :=
  fun A N => pullbackTensorComparison_braiding f A N

/-- The comparison of Tag 01CD is compatible with the left unit constraints of Tag 01CA. -/
theorem isLeftUnital_pullback :
    IsLeftUnital Y.presheaf (isSheafStructure Y) X.presheaf (isSheafStructure X)
      (pullbackFunctor f) (pullbackTensorator f) (pullbackUnitSheafIso f) :=
  fun M => pullbackTensorComparison_leftUnitor f M

/-- The comparison of Tag 01CD is compatible with the right unit constraints of Tag 01CA. -/
theorem isRightUnital_pullback :
    IsRightUnital Y.presheaf (isSheafStructure Y) X.presheaf (isSheafStructure X)
      (pullbackFunctor f) (pullbackTensorator f) (pullbackUnitSheafIso f) := by
  intro M
  rw [tensorSheafMapIso_refl_left X.presheaf (isSheafStructure X)
      ((pullbackFunctor f).obj M) (pullbackUnitSheafIso f),
    ← Stacks.SheafOfModules.rightUnitor_eq_tensorSheafRightUnitor X.presheaf (isSheafStructure X),
    ← Stacks.SheafOfModules.rightUnitor_eq_tensorSheafRightUnitor Y.presheaf (isSheafStructure Y)]
  exact pullbackTensorComparison_rightUnitor f M

/-! ### Multiplicativity -/

/-- **Pullback commutes with the multiplication of the integral tensor powers**: the comparison
`f^*(L^{⊗ n}) ≅ (f^*L)^{⊗ n}` carries the coherent multiplication of Tag 01CU for `L` to the one
for `f^*L`, in every pair of integer degrees. -/
theorem pullbackIntPowIso_coherentMulIso (n m : ℤ) :
    (pullbackFunctor f).map
          (coherentMulIso Y.presheaf (isSheafStructure Y) L n m).hom ≫
        (pullbackIntPowIso f L (n + m)).hom =
      (pullbackTensorator f (tensorPower Y.presheaf (isSheafStructure Y) L n)
          (tensorPower Y.presheaf (isSheafStructure Y) L m)).hom ≫
        (tensorSheafMapIso X.presheaf (isSheafStructure X) (pullbackIntPowIso f L n)
          (pullbackIntPowIso f L m)).hom ≫
        (coherentMulIso X.presheaf (isSheafStructure X)
          ((pullbackFunctor f).obj L) n m).hom :=
  map_coherentMulIso_tensorPowerComparison Y.presheaf (isSheafStructure Y) X.presheaf
    (isSheafStructure X) (pullbackFunctor f) L (pullbackTensorator f)
    (pullbackUnitSheafIso f) (isLeftUnital_pullback f) (isRightUnital_pullback f)
    (isNaturalLeft_pullback f) (isNaturalRight_pullback f) (isAssociative_pullback f)
    (isSymmetric_pullback f) n m

end Stacks.TensorPowerPullback

end
