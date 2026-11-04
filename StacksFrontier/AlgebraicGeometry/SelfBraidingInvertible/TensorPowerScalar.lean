module

public import StacksFrontier.AlgebraicGeometry.SelfBraidingInvertible.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence

/-!
# The braiding scalar of a tensor power is the identity

`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorPowerCoherence.lean` reduces the
commutativity constraint of Stacks Tag 01CU, in degrees `(n, n)`, to a single scalar identity:
`Stacks.SheafOfModules.TensorPower.braidingScalar O hO L n = 𝟙`, the scalar by which the braiding
acts on `L ^⊗ n ⊗ L ^⊗ n`.

This file proves that identity in every degree, from
`Stacks.SelfBraidingInvertible.hasLocallySymmetricSquare_of_isInvertible`: a tensor power of an
invertible sheaf of modules is invertible
(`Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower`), hence has locally symmetric
tensor square, hence its self-braiding dies under sheafification — and
`Stacks.SheafOfModules.tensorSheafBraiding` *is* the sheafification of that presheaf braiding, by
construction.

## Main results

* `Stacks.SelfBraidingInvertible.tensorSheafBraiding_self_eq_refl`: the braiding of a tensor
  power of an invertible sheaf of modules with itself is the identity, in the
  `Stacks.SheafOfModules.TensorSheafification.tensorSheaf` spelling.
* `Stacks.SelfBraidingInvertible.braidingScalar_eq_id`: the braiding scalar is the identity, in
  every degree. With `tensorSheafBraiding_self_eq_refl_iff` this is the commutativity
  constraint of Tag 01CU in degrees `(n, n)`.

## Implementation notes

`Stacks.SheafOfModules.braidingVal O hO M N` is by definition `β_ N.val M.val` for the monoidal
structure on presheaves of modules, and `tensorSheafBraiding` is
  `(Stacks.SheafOfModules.TensorSheafification.sheafify O hO)`
applied to it; so the statement here is exactly what
`Stacks.SelfBraidingInvertible.braiding_comp_toSheafify` and
`Stacks.SectionRingGeometric.map_eq_of_unit_comp_eq` produce, and no identification of the
braiding on `SheafOfModules` with the localized one
(`Stacks.SheafInternalHom.braidedCategory`) is needed.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public section

open CategoryTheory Category MonoidalCategory Stacks.SheafOfModules.TensorSheafification

universe v u w

namespace Stacks.SelfBraidingInvertible

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {𝒪 : Cᵒᵖ ⥤ CommRingCat.{w}}
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules

variable (L : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))
  [Stacks.SheafOfModules.IsInvertible 𝒪 h𝒪 L]

/-- **The braiding of a tensor power of an invertible sheaf of modules with itself is the
identity.** The tensor power is again invertible, hence has locally symmetric tensor square, and
`Stacks.SheafOfModules.tensorSheafBraiding` is the sheafification of the presheaf braiding. -/
theorem tensorSheafBraiding_self_eq_refl (n : ℤ) :
    Stacks.SheafOfModules.tensorSheafBraiding 𝒪 h𝒪
        (Stacks.SheafOfModules.TensorPower.tensorPower 𝒪 h𝒪 L n)
        (Stacks.SheafOfModules.TensorPower.tensorPower 𝒪 h𝒪 L n) =
      Iso.refl _ := by
  set K := Stacks.SheafOfModules.TensorPower.tensorPower 𝒪 h𝒪 L n
  have hK : HasLocallySymmetricSquare 𝒪 J K.val :=
    hasLocallySymmetricSquare_of_isInvertible h𝒪 K
  refine Iso.ext ?_
  exact (Stacks.SectionRingGeometric.map_eq_of_unit_comp_eq (sheafifyAdjunction 𝒪 h𝒪)
        (β_ K.val K.val).hom (𝟙 (K.val ⊗ K.val))
        ((braiding_comp_toSheafify h𝒪 K.val hK).trans (id_comp _).symm)).trans
      ((sheafify 𝒪 h𝒪).map_id _)

/-- **The braiding scalar of a tensor power of an invertible sheaf of modules is the identity**,
in every degree. By `Stacks.SheafOfModules.TensorPower.tensorSheafBraiding_self_eq_refl_iff` this
is the commutativity constraint of Stacks Tag 01CU in degrees `(n, n)`. -/
@[stacks 01CU "canonical multiplication and coherence"]
theorem braidingScalar_eq_id (n : ℤ) :
    Stacks.SheafOfModules.TensorPower.braidingScalar 𝒪 h𝒪 L n = 𝟙 _ :=
  (Stacks.SheafOfModules.TensorPower.tensorSheafBraiding_self_eq_refl_iff 𝒪 h𝒪 L n).mp
    (tensorSheafBraiding_self_eq_refl h𝒪 L n)

end Stacks.SelfBraidingInvertible

end
