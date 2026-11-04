module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerIntegerCoherence
public import StacksFrontier.AlgebraicGeometry.TensorPowerCoherence.Comparison

/-!
# The coherent multiplication of the integer tensor powers, in the monoidal spelling

`Stacks.SheafOfModules.TensorPower.coherentMulIso` is the multiplication
`L ^⊗ n ⊗ L ^⊗ m ≅ L ^⊗ (n + m)` of [Stacks, Tag 01CU] for an invertible sheaf of modules, and it
carries the five coherence laws whose formulation the source omits. It is stated against the
tensor product **sheaf** `Stacks.SheafOfModules.TensorSheafification.tensorSheaf` and its four
fixed structure maps `Stacks.SheafOfModules.Invertible.tensorProduct…`.

This file restates it, with its associativity law, against the **monoidal** structure
`Stacks.SheafOfModules.monoidalCategory` — that is, against `⊗`, `▷`, `◁` and `α_`. That is the
spelling in which the general monoidal-category API applies, and in particular the spelling in
which a section of a tensor power acts on another tensor power by whiskering, which is what the
stalkwise arguments about multiplication by a section are written in. The consumer is
`StacksFrontier/AlgebraicGeometry/TensorPowerDivision/Integer.lean`, where multiplication by a
section of `L ^⊗ k` is shown to be bijective on sections over the nonvanishing open of the
section, and where the associativity below is what makes the cancellation
`(u · a) / (u · t) = a / t` available in every integer degree.

## Main definitions

* `Stacks.SheafOfModules.TensorPower.monoidalMulIso`: the multiplication
  `L ^⊗ n ⊗ L ^⊗ m ≅ L ^⊗ (n + m)`, with `⊗` the monoidal tensor product.

## Main results

* `Stacks.SheafOfModules.TensorPower.monoidalMulIso_assoc`: **its associativity law**, for the
  monoidal associator, in **every** integer degree. Compare
  `Stacks.TensorPowers.TensorInverse.addIso_assoc_natCast`, which is the corresponding law for the
  addition isomorphism of the repository's other construction of the integer powers and holds only
  when all three exponents are nonnegative.
* `Stacks.SheafOfModules.TensorPower.tensorObjIso_tensorProductIso`: the naturality of
  `Stacks.SheafOfModules.tensorObjIso` in the shape the proof uses, namely with the two morphisms
  packaged as isomorphisms.

## The route

`Stacks.SheafOfModules.tensorObjIso` identifies the monoidal tensor product with the tensor
product sheaf, and `StacksFrontier/AlgebraicGeometry/TensorPowerCoherence/Comparison.lean` proves
that it identifies the structure maps too. Only two of those comparisons are needed:
`Stacks.SheafOfModules.Invertible.tensorObjIso_naturality`, to move a whiskering across it, and
`Stacks.SheafOfModules.Invertible.tensorObjIso_associativity`, to move the associator across it.
With them the associativity law below is the associativity law of `coherentMulIso` conjugated,
with no further computation.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe v u w

namespace Stacks.SheafOfModules.TensorPower

section Monoidal

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafOfModules.monoidalCategory Stacks.SheafOfModules.braidedCategory
  Stacks.SheafOfModules.symmetricCategory

attribute [local instance_reducible] TensorSheafification.structureSheaf
  Stacks.SheafOfModules.Tensor.ringSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **The naturality of `Stacks.SheafOfModules.tensorObjIso`, with the two morphisms packaged as
isomorphisms.** `Stacks.SheafOfModules.Invertible.tensorObjIso_naturality` states the right-hand
side as the sheafification of the presheaf tensor product of the underlying morphisms;
`Stacks.SheafOfModules.Invertible.tensorProductIso` is that morphism, so the two statements are
the same term. -/
theorem tensorObjIso_tensorProductIso
    {A A' B B' : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)}
    (e : A ≅ A') (f : B ≅ B') :
    (e.hom ⊗ₘ f.hom) ≫ (Stacks.SheafOfModules.tensorObjIso O hO A' B').hom =
      (Stacks.SheafOfModules.tensorObjIso O hO A B).hom ≫
        (Invertible.tensorProductIso O hO e f).hom :=
  Invertible.tensorObjIso_naturality O hO e.hom f.hom

variable (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)) [IsInvertible O hO L]

/-- **The coherent multiplication of the integer tensor powers, for the monoidal tensor
product.** This is `Stacks.SheafOfModules.TensorPower.coherentMulIso` read through
`Stacks.SheafOfModules.tensorObjIso`. -/
def monoidalMulIso (n m : ℤ) :
    tensorPower O hO L n ⊗ tensorPower O hO L m ≅ tensorPower O hO L (n + m) :=
  Stacks.SheafOfModules.tensorObjIso O hO (tensorPower O hO L n) (tensorPower O hO L m) ≪≫
    coherentMulIso O hO L n m

/-- **Associativity of the multiplication, for the monoidal associator, in every integer
degree.** -/
theorem monoidalMulIso_assoc (n m k : ℤ) :
    (monoidalMulIso O hO L n m).hom ▷ tensorPower O hO L k ≫
        (monoidalMulIso O hO L (n + m) k).hom =
      (α_ (tensorPower O hO L n) (tensorPower O hO L m) (tensorPower O hO L k)).hom ≫
        tensorPower O hO L n ◁ (monoidalMulIso O hO L m k).hom ≫
          (monoidalMulIso O hO L n (m + k)).hom ≫
            (tensorPowerReindex O hO L (Int.add_assoc n m k).symm).hom := by
  have hassoc := congrArg Iso.hom (coherentMulIso_assoc O hO L n m k)
  simp only [Iso.trans_hom] at hassoc
  have hnat₁ := tensorObjIso_tensorProductIso O hO (coherentMulIso O hO L n m)
    (Iso.refl (tensorPower O hO L k))
  have hnat₂ := tensorObjIso_tensorProductIso O hO (Iso.refl (tensorPower O hO L n))
    (coherentMulIso O hO L m k)
  have hα := Invertible.tensorObjIso_associativity O hO
    (tensorPower O hO L n) (tensorPower O hO L m) (tensorPower O hO L k)
  simp only [Iso.refl_hom, tensorHom_id, id_tensorHom] at hnat₁ hnat₂
  simp only [monoidalMulIso, Iso.trans_hom, comp_whiskerRight, whiskerLeft_comp,
    Category.assoc]
  slice_lhs 2 3 => rw [hnat₁]
  slice_lhs 3 4 => rw [hassoc]
  slice_lhs 1 3 => rw [hα]
  slice_lhs 3 4 => rw [← hnat₂]
  simp only [Category.assoc]

end Monoidal

end Stacks.SheafOfModules.TensorPower

end
