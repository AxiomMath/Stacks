module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackMonoidalSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerRestriction

/-!
# Pullback commutes with the integral tensor powers of an invertible sheaf of modules

Let `f : X ⟶ Y` be a morphism of ringed spaces and `L` an invertible sheaf of `𝒪_Y`-modules in
the sense of Tag 01CS. The integral tensor powers `L^{⊗ n}`, `n : ℤ`, of Tag 01CU are the images
of the structure sheaf under the powers of the autoequivalence `- ⊗ L`, so for `n < 0` they are
given by a *chosen* quasi-inverse and have no description in terms of objects. This file produces
the comparison

`f^*(L^{⊗ n}) ≅ (f^*L)^{⊗ n}`

for **every** integer `n`, from the comparison `f^*(M ⊗ L) ≅ f^*M ⊗ f^*L` of Tag 01CD and the
comparison `f^*𝒪_Y ≅ 𝒪_X` of the structure sheaves.

## Main definitions

* `Stacks.TensorPowerPullback.pullbackTensorFactorIso` and
  `Stacks.TensorPowerPullback.tensorFactorComparison`: the comparison of Tag 01CD,
  `f^*(M ⊗ L) ≅ f^*M ⊗ f^*L`, as an isomorphism and packaged as the
  `Stacks.SheafOfModules.TensorPower.TensorComparison` that the transport of tensor powers
  consumes.
* `Stacks.TensorPowerPullback.pullbackUnitSheafIso`: the comparison `f^*𝒪_Y ≅ 𝒪_X`
  (`Stacks.PullbackAlgebra.pullbackUnitIso`), retyped at the monoidal unit of Tag 01CA.
* `Stacks.TensorPowerPullback.pullbackIntPowIso`: **the comparison
  `f^*(L^{⊗ n}) ≅ (f^*L)^{⊗ n}`, for every `n : ℤ`.**

## Main results

* `Stacks.TensorPowerPullback.pullbackIntPowIso_zero`: in degree zero the comparison is the
  comparison of the structure sheaves.
* `Stacks.TensorPowerPullback.pullbackIntPowIso_one`: in degree one it is the comparison of
  Tag 01CD at the structure sheaf, followed by the comparison of the structure sheaves tensored
  on the right by `f^*L`.
* `Stacks.TensorPowerPullback.isInvertible_pullback_intPow`: every integral tensor power of
  `f^*L` is invertible, as is the pullback of every integral tensor power of `L`.

## Implementation notes

The construction is `Stacks.SheafOfModules.TensorPower.mapTensorPowerIso` — "integer tensor
powers are carried along by any functor compatible with the tensor product" — instantiated at the
pullback functor. That is the only available route: a negative tensor power is an iterate of a
chosen quasi-inverse, so the comparison in negative degree cannot be assembled from the
comparison of Tag 01CD by a formula on objects, and has to be manufactured from the unit and the
counit of the autoequivalence `- ⊗ L`, which is what
`Stacks.Equivalence.inverseIntertwineObj` does.

Everything is spelled in the canonical tensor product `Stacks.SheafOfModules.Tensor.sheafTensor`
and unit `SheafOfModules.unit`. The comparisons of Tag 01CD and of the structure sheaves are
stated in the monoidal structure `Stacks.PullbackGradedAlgebra.monoidalCategory` of Tag 01CA,
whose tensor product and unit object are these on the nose; that is what lets the comparison of
Tag 01CD be read as a `TensorComparison` and the comparison of the structure sheaves as the
identification of the two units.

Two instances are rebound with declared types rather than left to instance resolution,
`instIsEquivalenceTensorRightInvertible` and `instIsEquivalenceTensorRightPullback`, because
`Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor` (tensoring on the right by
`L`, the functor `(Stacks.SheafOfModules.Tensor.sheafTensor _).flip.obj L`) is not found by
instance search at the spelling `Stacks.RingedSpace.structureRingSheaf` of the structure sheaf
while the same instance applied is accepted. The `IsIso` instances of the two comparisons are
found at their own monoidal spelling, so `pullbackTensorFactorIso` elaborates `asIso` without
the expected type and only then retypes the result.

**No `@[stacks]` attribute.** Tag 01CD is carried by `Stacks.RingedSpace.comparisonIso`, Tag 01CU
by the integral tensor powers and Tag 0B8L by
`Stacks.RingedSpace.modulePullback_isInvertible`; the comparison below is a compatibility of
those, not a new result of the Stacks Project, so tagging it would register a result twice. This
is the convention of
`StacksFrontier/AlgebraicGeometry/RelativeVeryAmple/TensorPowerPullbackMul.lean`, which proves the
nonnegative-degree statement.

## Not done here

**Multiplicativity is not proved here.** The comparison is not shown to carry the coherent
multiplication `L^{⊗ n} ⊗ L^{⊗ m} ≅ L^{⊗ (n + m)}` of Tag 01CU to the one of `f^*L`, so it is not
shown to be an isomorphism of the Laurent algebras of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LaurentAlgebra`. Two things are missing for that.
The multiplication `Stacks.SheafOfModules.TensorPower.coherentMulIso` is the multiplication of a
*chosen* coherence datum, so a statement about it can only be reached by proving that the
normalisations of `Stacks.SheafOfModules.TensorPower.TensorPowerCoherence` determine `mulIso`
uniquely; and the one normalisation that anchors the induction is the one in degree `(n, 1)`,
which asks how the comparison above behaves under
`Stacks.SheafOfModules.TensorPower.tensorPowerSuccIso` — the successor applied *outermost*,
whereas `Stacks.Equivalence.powIntertwineObj` recurses on the successor applied *innermost*.
Reconciling the two is the uniform successor recursion that
`CategoryTheory.Equivalence.powAdd_succ` is for the addition law, and it needs the comparison of
Tag 01CD as a *natural* isomorphism, which `TensorComparison` deliberately does not require.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD) — pullback commutes with
  the tensor product of sheaves of modules.
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU) — the integral tensor
  powers of an invertible module.
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS) — invertible sheaves of
  modules.
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L) — the pullback of an
  invertible module is invertible.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry

open Stacks.RingedSpace Stacks.PullbackTensorCoherence

open Stacks.SheafOfModules.TensorPower

universe u

namespace Stacks.TensorPowerPullback

/-- The sheaf condition on the structure presheaf of a ringed space, in the form the monoidal
structure of Tag 01CA and the integral tensor powers of Tag 01CU take as an argument. -/
abbrev isSheafStructure (Z : RingedSpace.{u, u}) :=
  (structureSheafRing Z).property

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (L : SheafOfModules.{u} (structureRingSheaf Y))
  [Stacks.SheafOfModules.IsInvertible Y.presheaf (isSheafStructure Y) L]

/-- Tensoring on the right by an invertible sheaf of modules is an equivalence, which is the
datum the integral tensor powers of Tag 01CU are indexed by. -/
instance instIsEquivalenceTensorRightInvertible :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨Y.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ Y.presheaf (forget₂ CommRingCat RingCat)
        (isSheafStructure Y)⟩).flip.obj L).IsEquivalence :=
  isEquivalence_tensorRightFunctor Y.presheaf (isSheafStructure Y) L

/-- The pullback of an invertible sheaf of modules is invertible, in the spelling the integral
tensor powers are indexed by. This is Tag 0B8L together with Tag 01CS. -/
instance instIsEquivalenceTensorRightPullback :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)
        (isSheafStructure X)⟩).flip.obj ((pullbackFunctor f).obj L)).IsEquivalence :=
  isEquivalence_tensorRightFunctor X.presheaf (isSheafStructure X) ((pullbackFunctor f).obj L)

/-- **The comparison of Tag 01CD as an isomorphism**, `f^*(M ⊗ L) ≅ f^*M ⊗ f^*L`. -/
def pullbackTensorFactorIso (M : SheafOfModules.{u} (structureRingSheaf Y)) :
    (pullbackFunctor f).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨Y.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ Y.presheaf (forget₂ CommRingCat RingCat)
            (isSheafStructure Y)⟩).obj M).obj L) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)
          (isSheafStructure X)⟩).obj ((pullbackFunctor f).obj M)).obj ((pullbackFunctor f).obj L) :=
  (asIso (pullbackTensorComparison f M L) :)

/-- **The comparison of Tag 01CD as a tensor comparison for the pullback functor**: the
isomorphism `f^*(M ⊗ L) ≅ f^*M ⊗ f^*L`, for every sheaf of `𝒪_Y`-modules `M`. -/
def tensorFactorComparison :
    TensorComparison Y.presheaf (isSheafStructure Y) X.presheaf (isSheafStructure X)
      (pullbackFunctor f) L :=
  fun M => pullbackTensorFactorIso f L M

/-- **The comparison `f^*𝒪_Y ≅ 𝒪_X` of the structure sheaves**, retyped at
`SheafOfModules.unit`, which is the monoidal unit of the tensor product of Tag 01CA on the
nose. -/
def pullbackUnitSheafIso :
    (pullbackFunctor f).obj
        (SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf Y.presheaf
            (isSheafStructure Y))) ≅
      SheafOfModules.unit
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf
          (isSheafStructure X)) :=
  Stacks.PullbackAlgebra.pullbackUnitIso f

/-- **Pullback commutes with the integral tensor powers of an invertible sheaf of modules**:
`f^*(L^{⊗ n}) ≅ (f^*L)^{⊗ n}` for every `n : ℤ`.

In degree zero this is the comparison of the structure sheaves and in degree one the comparison
of Tag 01CD; in a negative degree both sides are iterates of a chosen quasi-inverse of
`- ⊗ L`, and the comparison is the one manufactured from the unit and the counit of that
equivalence. -/
def pullbackIntPowIso (n : ℤ) :
    (pullbackFunctor f).obj (tensorPower Y.presheaf (isSheafStructure Y) L n) ≅
      tensorPower X.presheaf (isSheafStructure X) ((pullbackFunctor f).obj L) n :=
  mapTensorPowerIso Y.presheaf (isSheafStructure Y) X.presheaf (isSheafStructure X)
    (pullbackFunctor f) L (tensorFactorComparison f L) (pullbackUnitSheafIso f) n

/-- In degree zero the comparison of the tensor powers is the comparison of the structure
sheaves. -/
theorem pullbackIntPowIso_zero : pullbackIntPowIso f L 0 = pullbackUnitSheafIso f :=
  mapTensorPowerIso_zero Y.presheaf (isSheafStructure Y) X.presheaf (isSheafStructure X)
    (pullbackFunctor f) L (tensorFactorComparison f L) (pullbackUnitSheafIso f)

/-- In degree one the comparison of the tensor powers is the comparison of Tag 01CD at the
structure sheaf, followed by the comparison of the structure sheaves tensored on the right by
`f^*L`. -/
theorem pullbackIntPowIso_one :
    pullbackIntPowIso f L 1 =
      tensorFactorComparison f L
          (SheafOfModules.unit
            (Stacks.SheafOfModules.TensorSheafification.structureSheaf Y.presheaf
              (isSheafStructure Y))) ≪≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)
            (isSheafStructure X)⟩).flip.obj ((pullbackFunctor f).obj L)).mapIso
          (pullbackUnitSheafIso f) :=
  mapTensorPowerIso_one Y.presheaf (isSheafStructure Y) X.presheaf (isSheafStructure X)
    (pullbackFunctor f) L (tensorFactorComparison f L) (pullbackUnitSheafIso f)

/-- Every integral tensor power of the pullback of an invertible sheaf of modules is invertible,
and so, through the comparison, is the pullback of every integral tensor power. This is Tag
01CU for `f^*L`, which is invertible by Tag 0B8L. -/
theorem isInvertible_pullback_intPow (n : ℤ) :
    Stacks.SheafOfModules.IsInvertible X.presheaf (isSheafStructure X)
      ((pullbackFunctor f).obj (tensorPower Y.presheaf (isSheafStructure Y) L n)) :=
  let := isInvertible_tensorPower X.presheaf (isSheafStructure X) ((pullbackFunctor f).obj L) n
  Stacks.SheafOfModules.isInvertible_of_iso X.presheaf (isSheafStructure X)
    (pullbackIntPowIso f L n).symm

end Stacks.TensorPowerPullback

end
