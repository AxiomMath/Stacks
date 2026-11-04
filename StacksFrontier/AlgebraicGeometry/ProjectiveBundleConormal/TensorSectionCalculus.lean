module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.CanonicalMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TwistSectionRing

/-!
# The tensor product of the conormal construction, read on sections

`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.CanonicalMap` builds the canonical map of
[Stacks, Tag 0B3V] clause 3 out of three things that touch the tensor product: the comparison
`Stacks.ProjectiveBundleConormal.pullbackTensorComparison` of [Stacks, Tag 01CD], the whiskering
`v ▷ 𝒪(-1)` of the tautological map, and the evaluation pairing
`Stacks.ProjectiveBundleConormal.invertibleEvaluation`. Every statement there is an equation of
*morphisms*. **This file reads those three on a section**, namely on the section
`Stacks.SheafOfModules.tensorSectionsAt` of a tensor product determined by a section of each
factor.

That is what the chart computation of the clause needs. Both halves of the clause's chart
identification land on `(ker p)^~`, whose sections are generated, so the equation that remains is
read on a generator; and a generator of the source is a section `k ⊗ s̄^{⊗ -1}` of a tensor
product. Nothing above this file can say what the clause's map does to such a section, because
nothing above it says what *any* of the three maps does to one.

## Main results

* `Stacks.ProjectiveBundleConormal.pullbackTensorComparison_unit_tensorSectionsAt`: **[Stacks,
  Tag 01CD] on sections.** The comparison carries the pullback of a product section to the
  product of the pullbacks.
* `Stacks.ProjectiveBundleConormal.tensorSectionsAt_whiskerRight`: a whiskering acts on a product
  section through its first factor alone.
* `Stacks.ProjectiveBundleConormal.invertibleEvaluation_tensorSectionsAt`: the evaluation pairing
  `L ⊗ L^{⊗ -1} ≅ 𝒪_X` on a product section is
  `Stacks.SheafOfModules.Invertible.sectionMulNegOne`.

## Implementation notes

**None of the three is proved here.** Each is a restatement, at the ascribed spelling used
here, of a formula the library already carries:

* `Stacks.RingedSpace.comparison_pullbackUnit_tmul`
  (`StacksFrontier.AlgebraicGeometry.PullbackTensor.Basic`) is the comparison of [Stacks, Tag 01CD]
  on a product section already, stated over the sheaves of modules of the underlying *ringed
  space* and with the unit of `f^* ⊣ f_*` spelled `Stacks.RingedSpace.pullbackUnit` and the
  sheafification unit spelled `tensorSheafUnit`; `pullbackTensorComparison`,
  `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction` and
  `Stacks.SheafOfModules.tensorSectionsAt` are those three at the scheme spelling, and the
  crossing is a `rfl`.
* `Stacks.SheafOfModules.tensorSections_tensorMapAt` is the action of `f ⊗ₘ g` on a product
  section; a whiskering is that at `g = 𝟙`.
* `Stacks.SheafOfModules.Invertible.mulNegOneIso_toSheafify` is the evaluation pairing on a
  product section, `tensorSectionsAt` being the sheafification unit on a pure tensor by
  definition.

So the whole file is three `exact`s, and the only work in it is choosing the ascription. See the
implementation notes of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.CanonicalMap` for why the ascription is
not optional: a composite mixing the ringed-space and scheme spellings of the sheaves of modules
is not type-correct at `implicit` transparency, so a goal containing one cannot be rewritten.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite

universe u

namespace Stacks.ProjectiveBundleConormal

attribute [local instance] monoidalSheafTensor

/-- **The comparison of [Stacks, Tag 01CD] on a product section.** The section of `A ⊗ B` over
`U` determined by sections `a` of `A` and `b` of `B`, pulled back along `f` by the unit of
`f^* ⊣ f_*` and carried across the comparison, is the section of `f^*A ⊗ f^*B` determined by the
pullbacks of `a` and of `b`.

Since the products generate the tensor product sheaf, this determines the comparison; it is
`Stacks.RingedSpace.comparison_pullbackUnit_tmul` at the scheme spelling. -/
theorem pullbackTensorComparison_unit_tensorSectionsAt {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : Y.Modules) (U : Y.Opens) (a : A.val.obj (op U)) (b : B.val.obj (op U)) :
    (pullbackTensorComparison f A B).val.app (op (f ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (A ⊗ B)).val.app (op U)
          (Stacks.SheafOfModules.tensorSectionsAt Y.presheaf Y.ringCatSheaf.2 (op U) A B a b)) =
      Stacks.SheafOfModules.tensorSectionsAt X.presheaf X.ringCatSheaf.2 (op (f ⁻¹ᵁ U))
        ((Scheme.Modules.pullback f).obj A) ((Scheme.Modules.pullback f).obj B)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app A).val.app (op U) a)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app B).val.app (op U) b) :=
  Stacks.RingedSpace.comparison_pullbackUnit_tmul f.toLRSHom.toShHom A B (op U) a b

/-- **A whiskering acts on a product section through its first factor alone.** This is
`Stacks.SheafOfModules.tensorSections_tensorMapAt` at `g = 𝟙 B`, the whiskering of the re-seated
monoidal structure being the action of the tensor product sheaf on `(v, 𝟙)`. -/
theorem tensorSectionsAt_whiskerRight {X : Scheme.{u}} {A A' : X.Modules} (v : A ⟶ A')
    (B : X.Modules) (V : X.Opens) (z : A.val.obj (op V)) (w : B.val.obj (op V)) :
    (v ▷ B).val.app (op V)
        (Stacks.SheafOfModules.tensorSectionsAt X.presheaf X.ringCatSheaf.2 (op V) A B z w) =
      Stacks.SheafOfModules.tensorSectionsAt X.presheaf X.ringCatSheaf.2 (op V) A' B
        (v.val.app (op V) z) w :=
  Stacks.SheafOfModules.tensorSections_tensorMapAt X.presheaf X.ringCatSheaf.2 (op V)
    A A' B B v (𝟙 B) z w

/-- **The evaluation pairing `L ⊗ L^{⊗ -1} ≅ 𝒪_X` on a product section** is the multiplication of
sections `Stacks.SheafOfModules.Invertible.sectionMulNegOne`. This is
`Stacks.SheafOfModules.Invertible.mulNegOneIso_toSheafify`, the section determined by a pair
being the sheafification unit on a pure tensor by definition. -/
theorem invertibleEvaluation_tensorSectionsAt {X : Scheme.{u}} (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (V : X.Opens) (s : L.val.obj (op V))
    (t : (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L (-1)).val.obj
      (op V)) :
    (invertibleEvaluation L).hom.val.app (op V)
        (Stacks.SheafOfModules.tensorSectionsAt X.presheaf X.ringCatSheaf.2 (op V) L
          (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L (-1))
          s t) =
      Stacks.SheafOfModules.Invertible.sectionMulNegOne X.presheaf X.ringCatSheaf.2 L (op V) s t :=
  Stacks.SheafOfModules.Invertible.mulNegOneIso_toSheafify X.presheaf X.ringCatSheaf.2 L
    (op V) s t

end Stacks.ProjectiveBundleConormal

end
