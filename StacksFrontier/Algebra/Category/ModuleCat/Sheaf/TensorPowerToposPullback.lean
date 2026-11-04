module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackInvertible.RingedTopos
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackBraiding
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerMapMultiplication

/-!
# Pullback along a morphism of ringed topoi commutes with the integral tensor powers

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi and `L` an invertible
`O_D`-module. The integral tensor powers `L^{⊗ n}`, `n : ℤ`, of Tag 01CU are carried by the
pullback of modules of Stacks 03D6 to the integral tensor powers of the invertible module `f^*L`
(Stacks 0B8P), and the comparison

`f^*(L^{⊗ n}) ≅ (f^*L)^{⊗ n}`

is **multiplicative**: it carries the coherent multiplication `L^{⊗ n} ⊗ L^{⊗ m} ≅ L^{⊗ (n + m)}`
of Tag 01CU for `L` to the one for `f^*L`, through the comparison of Tag 03EL. This is the
ringed-topos form of `Stacks.TensorPowerPullback.pullbackIntPowIso_coherentMulIso`, which says the
same for a morphism of ringed spaces; it is what reads the Laurent algebra `⨁_n L^{⊗ n}` of an
invertible module on an algebraic space at a scheme point (the étale pullback is a pullback along
a morphism of small étale ringed topoi), as the setup of Stacks 0D2Z requires.

## Main definitions

* `Stacks.SheafOfModules.RingedToposPullback.pullbackIntPowIso`: **the comparison
  `f^*(L^{⊗ n}) ≅ (f^*L)^{⊗ n}`, for every `n : ℤ`**, built from the comparison of Tag 03EL and
  the comparison `f^*O_D ≅ O_C` of the structure sheaves.

## Main results

* `…isNaturalLeft_pullbackModules`, `…isNaturalRight_pullbackModules`,
  `…isAssociative_pullbackModules`, `…isLeftUnital_pullbackModules`,
  `…isRightUnital_pullbackModules`, `…isSymmetric_pullbackModules`: the six normalisations of
  the comparison of Tag 03EL that the multiplicativity of the comparison of tensor powers takes as
  inputs. The associativity and the two unit laws are the three coherences of Tag 03EL
  (`Stacks.SheafOfModules.RingedToposPullback.pullbackCoherence`), the symmetry is the braided
  coherence `Stacks.SheafOfModules.RingedToposPullback.braiding`.
* `…pullbackIntPowIso_coherentMulIso`: **the comparison of integral tensor powers is
  multiplicative.**

## Implementation notes

The work is the abstract statement
`Stacks.SheafOfModules.TensorPower.map_coherentMulIso_tensorPowerComparison`, for any functor
with a tensorator satisfying the six normalisations; this file supplies them for the pullback
along a morphism of ringed topoi, at the sheaf of rings `X.O.obj` with the sheaf condition of
`Stacks.SheafOfModules.Tensor.ringSheaf X.O`, the spelling at which Stacks 0B8P
(`Stacks.SheafOfModules.isInvertible_pullbackModules_obj`) is stated.

**No `@[stacks]` attribute.** Tag 03EL is carried by
`Stacks.SheafOfModules.RingedToposPullback.pullbackCoherence`, Tag 01CU by the integral tensor
powers and Tag 0B8P by `Stacks.SheafOfModules.isInvertible_pullbackModules_obj`; the comparison
below is a compatibility of those, not a further result of the source.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0B8P](https://stacks.math.columbia.edu/tag/0B8P)
* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open Stacks.Sheaves.RingedToposModules Stacks.SheafOfModules.TensorPower

universe w v u v' u'

namespace Stacks.SheafOfModules.RingedToposPullback

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalCategory
  Stacks.SheafOfModules.Strict.braidedCategory

variable {X : AlgebraicGeometry.RingedTopos.{v, u, w}}
  {Y : AlgebraicGeometry.RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y)

/-! ### The six normalisations of the comparison of Tag 03EL -/

/-- The comparison of Tag 03EL is natural in the first variable. -/
theorem isNaturalLeft_pullbackModules :
    IsNaturalLeft Y.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property f.pullbackModules
      (pullbackTensorComparisonIso f) :=
  fun u => (pullbackTensorComparison_naturality_left f u _).symm

/-- The comparison of Tag 03EL is natural in the second variable. -/
theorem isNaturalRight_pullbackModules :
    IsNaturalRight Y.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property f.pullbackModules
      (pullbackTensorComparisonIso f) :=
  fun v => (pullbackTensorComparison_naturality_right f _ v).symm

/-- The comparison of Tag 03EL is compatible with the associativity constraint of Tag 01CA. -/
theorem isAssociative_pullbackModules :
    IsAssociative Y.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property f.pullbackModules
      (pullbackTensorComparisonIso f) :=
  (pullbackCoherence f).associativity

/-- The comparison of Tag 03EL is compatible with the left unit constraints of Tag 01CA. -/
theorem isLeftUnital_pullbackModules :
    IsLeftUnital Y.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property f.pullbackModules
      (pullbackTensorComparisonIso f) (pullbackUnitComparison f) :=
  (pullbackCoherence f).leftUnitality

/-- The comparison of Tag 03EL is compatible with the right unit constraints of Tag 01CA. -/
theorem isRightUnital_pullbackModules :
    IsRightUnital Y.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property f.pullbackModules
      (pullbackTensorComparisonIso f) (pullbackUnitComparison f) := by
  intro M
  rw [tensorSheafMapIso_refl_left X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
      (f.pullbackModules.obj M) (pullbackUnitComparison f),
    ← Stacks.SheafOfModules.rightUnitor_eq_tensorSheafRightUnitor _
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property,
    ← Stacks.SheafOfModules.rightUnitor_eq_tensorSheafRightUnitor _
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property]
  exact (pullbackCoherence f).rightUnitality M

/-- The comparison of Tag 03EL is compatible with the symmetry constraint of Tag 01CA. -/
theorem isSymmetric_pullbackModules :
    IsSymmetric Y.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property f.pullbackModules
      (pullbackTensorComparisonIso f) :=
  fun M N => Stacks.SheafOfModules.RingedToposPullback.braiding f M N

/-! ### The comparison of integral tensor powers, and its multiplicativity -/

variable (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  [IsInvertible Y.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property L]

/-- Tensoring on the right by an invertible module is an equivalence, the datum the integral
tensor powers of Tag 01CU are indexed by. -/
instance instIsEquivalenceTensorRightInvertibleTopos :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨Y.O.obj, Presheaf.isSheaf_of_isSheaf_comp _ Y.O.obj (forget₂ CommRingCat RingCat)
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property⟩).flip.obj L).IsEquivalence :=
  isEquivalence_tensorRightFunctor Y.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property L

/-- The pullback of an invertible module along a morphism of ringed topoi is invertible
(Stacks 0B8P), in the spelling the integral tensor powers are indexed by. -/
instance instIsEquivalenceTensorRightPullbackModules :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.O.obj, Presheaf.isSheaf_of_isSheaf_comp _ X.O.obj (forget₂ CommRingCat RingCat)
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property⟩).flip.obj
          (f.pullbackModules.obj L)).IsEquivalence :=
  isEquivalence_tensorRightFunctor X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
    (f.pullbackModules.obj L)

/-- **Pullback along a morphism of ringed topoi commutes with the integral tensor powers of an
invertible module**: `f^*(L^{⊗ n}) ≅ (f^*L)^{⊗ n}` for every `n : ℤ`, the comparison determined
by the comparison of Tag 03EL and the comparison `f^*O_D ≅ O_C` of the structure sheaves. -/
def pullbackIntPowIso (n : ℤ) :
    f.pullbackModules.obj
        (tensorPower Y.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property L n) ≅
      tensorPower X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
        (f.pullbackModules.obj L) n :=
  tensorPowerComparison Y.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property X.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property f.pullbackModules L
    (pullbackTensorComparisonIso f) (pullbackUnitComparison f) n

/-- In degree zero the comparison of tensor powers is the comparison of the structure sheaves. -/
theorem pullbackIntPowIso_zero : pullbackIntPowIso f L 0 = pullbackUnitComparison f :=
  tensorPowerComparison_zero _ _ _ _ _ L _ _

/-- **Pullback along a morphism of ringed topoi commutes with the multiplication of the integral
tensor powers**: the comparison `f^*(L^{⊗ n}) ≅ (f^*L)^{⊗ n}` carries the coherent
multiplication of Tag 01CU for `L` to the one for `f^*L`, in every pair of integer degrees. -/
theorem pullbackIntPowIso_coherentMulIso (n m : ℤ) :
    f.pullbackModules.map
          (coherentMulIso Y.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property L n m).hom ≫
        (pullbackIntPowIso f L (n + m)).hom =
      (pullbackTensorComparisonIso f
          (tensorPower Y.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property L n)
          (tensorPower Y.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property L m)).hom ≫
        (tensorSheafMapIso X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
          (pullbackIntPowIso f L n) (pullbackIntPowIso f L m)).hom ≫
        (coherentMulIso X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
          (f.pullbackModules.obj L) n m).hom :=
  map_coherentMulIso_tensorPowerComparison _ _ _ _ f.pullbackModules L
    (pullbackTensorComparisonIso f) (pullbackUnitComparison f)
    (isLeftUnital_pullbackModules f) (isRightUnital_pullbackModules f)
    (isNaturalLeft_pullbackModules f) (isNaturalRight_pullbackModules f)
    (isAssociative_pullbackModules f) (isSymmetric_pullbackModules f) n m

end Stacks.SheafOfModules.RingedToposPullback

end
