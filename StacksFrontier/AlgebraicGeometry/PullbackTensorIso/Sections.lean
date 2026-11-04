module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TwistSectionRing
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemeBaseChange.PullbackSections
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible
public import StacksFrontier.AlgebraicGeometry.ProjBundleInverseBaseChange.Basic

/-!
# Tag 01CD on sections, and the inverse of an inverse

Two facts about the sheafified tensor product
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf` that a construction writing equations in
the fibre coordinates of a line bundle needs, and that are not available.

The first is that the comparison of [Stacks, Tag 01CD] takes products of sections to products of
sections. For a morphism of schemes `f : X ⟶ Y`, modules `A`, `B` on `Y` and global sections `a`
of `A` and `b` of `B`, the product `a ⊗ b` is the global section
`Stacks.SheafOfModules.tensorSectionsAt` of `A ⊗ B`, and the claim is

`f^*(a ⊗ b) = f^*a ⊗ f^*b`

once the left-hand side is read in `f^*A ⊗ f^*B` through
`Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso`. Nothing stated this. The one input is
the canonicality clause of Tag 01CD, `Stacks.RingedSpace.comparison_pullbackUnit_unit_tmul`,
which is exactly this statement for the ringed-space spellings of the pullback map on sections
and of the product of two sections; the content here is that those spellings agree with the
scheme-level ones.

The second is that the `(-1)`st tensor power of Tag 01CU is an involution:
`L ≅ (L^{⊗ -1})^{⊗ -1}`. The library has the base change of the inverse
(`Stacks.ProjBundleInverseBaseChange.pullbackTensorPowerNegOneIso`) but not its involutivity, and
a fibre coordinate on the total space of `L^{⊗ -1}` is a section of `(L^{⊗ -1})^{⊗ -1}` and has to
be read as a section of `L`.

## Main results

* `Stacks.PullbackTensorIso.pullbackGlobalSections_tensorSectionsAt`: **the comparison of Tag
  01CD carries the pullback of a product of two global sections to the product of their
  pullbacks.**

## Main definitions

* `Stacks.PullbackTensorIso.negOneTensorInverseSelf`: `L` is a two-sided tensor inverse of
  `L^{⊗ -1}`.
* `Stacks.PullbackTensorIso.tensorPowerNegOneNegOneIso`: **`L ≅ (L^{⊗ -1})^{⊗ -1}`**, the
  involutivity of the inverse.

## Implementation notes

The three identifications the first result passes through are all definitional, and each was
checked rather than assumed: the scheme-level pullback map on global sections
`AlgebraicGeometry.pullbackGlobalSections` is the ringed-space `Stacks.RingedSpace.pullbackUnit`
at the top open, once the transport along `f ⁻¹ᵁ ⊤ = ⊤` in its definition is removed by
`AlgebraicGeometry.pullbackGlobalSections_eq_unit`; the product of two sections
`Stacks.SheafOfModules.tensorSectionsAt` is the ringed-space sheafification unit
`Stacks.RingedSpace.tensorSheafUnit` on a pure tensor; and
`Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso` has
`Stacks.RingedSpace.comparison` as its forward map. The transport cannot be removed by `rw`
inside the application, because the motive that `rw` builds is not type-correct at the implicit
transparency level; it is removed by `congrArg` on the section instead, whose type is checked at
default transparency, which is the device `Chow/ZeroSchemePullback/Factorization.lean` already
uses for the same reason.

Involutivity is not an induction on the exponent and does not unfold the tensor powers: both `L`
and `(L^{⊗ -1})^{⊗ -1}` are the inverse object of a two-sided tensor inverse of `L^{⊗ -1}` — the
first because the two trivializations of `Stacks.ProjBundleInverseBaseChange.negOneTensorInverse`
read in the other order are trivializations of the other factor — so
`Stacks.TensorPowers.TensorInverse.invIso` identifies them.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite
open Stacks.SheafOfModules.TensorSheafification (structureRingPresheaf structureSheaf)
open Stacks.SheafOfModules.TensorPower (tensorPower)
open Stacks.TensorPowers (TensorInverse)
open Stacks.ProjBundleInverseBaseChange (negOneMulIso negOneMulIso' negOneTensorInverse)
open Stacks.SheafInternalHom (isSheaf_structureRingPresheaf)

universe v u w

namespace Stacks.PullbackTensorIso

/-! ### The comparison of Tag 01CD on products of sections -/

/-- **The comparison of [Stacks, Tag 01CD] carries the pullback of a product of two global
sections to the product of their pullbacks**: for `f : X ⟶ Y` and global sections `a` of `A` and
`b` of `B`, the pullback of `a ⊗ b` is `f^*a ⊗ f^*b`, read in `f^*A ⊗ f^*B` through
`Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso`. -/
theorem pullbackGlobalSections_tensorSectionsAt {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : Y.Modules) (a : Γ(A, ⊤)) (b : Γ(B, ⊤)) :
    PresheafOfModules.Hom.app
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f A B).hom.val (op ⊤)
        (pullbackGlobalSections f ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨Y.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ (Y.sheaf.obj)
              (forget₂ CommRingCat RingCat) (Y.ringCatSheaf.property)⟩).obj (A)).obj (B)))
          (Stacks.SheafOfModules.tensorSectionsAt Y.sheaf.obj Y.ringCatSheaf.property
            (op ⊤) A B a b)) =
      Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op ⊤)
        ((Scheme.Modules.pullback f).obj A) ((Scheme.Modules.pullback f).obj B)
        (pullbackGlobalSections f A a) (pullbackGlobalSections f B b) := by
  have key : ∀ (M : Y.Modules) (x : Γ(M, ⊤)),
      pullbackGlobalSections f M x =
        Stacks.RingedSpace.pullbackUnit f.toLRSHom.toShHom M (op ⊤) x := fun M x =>
    congrArg (fun φ : Γ(M, ⊤) ⟶ Γ((Scheme.Modules.pullback f).obj M, ⊤) => φ x)
      (pullbackGlobalSections_eq_unit f M)
  refine (congrArg _ (key _ _)).trans ?_
  rw [key, key]
  exact Stacks.RingedSpace.comparison_pullbackUnit_unit_tmul f.toLRSHom.toShHom A B (op ⊤) a b

/-! ### The inverse of the inverse -/

section Site

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w}) (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (L : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) [Stacks.SheafOfModules.IsInvertible 𝒪 h𝒪 L]

/-- **`L` is a two-sided tensor inverse of `L^{⊗ -1}`.** The two trivializations are those of
`Stacks.ProjBundleInverseBaseChange.negOneTensorInverse` read in the other order. -/
def negOneTensorInverseSelf : TensorInverse (tensorPower 𝒪 h𝒪 L (-1)) where
  inv := L
  mulIso := negOneMulIso 𝒪 h𝒪 L
  mulIso' := negOneMulIso' 𝒪 h𝒪 L

/-- **The `(-1)`st tensor power of [Stacks, Tag 01CU] is an involution**: `L ≅ (L^{⊗ -1})^{⊗ -1}`.
Both sides are the inverse object of a two-sided tensor inverse of `L^{⊗ -1}`, so
`Stacks.TensorPowers.TensorInverse.invIso` identifies them. -/
def tensorPowerNegOneNegOneIso :
    L ≅ tensorPower 𝒪 h𝒪 (tensorPower 𝒪 h𝒪 L (-1)) (-1) :=
  haveI : Stacks.SheafOfModules.IsInvertible 𝒪 h𝒪 (tensorPower 𝒪 h𝒪 L (-1)) :=
    Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower 𝒪 h𝒪 L (-1)
  TensorInverse.invIso (negOneTensorInverseSelf 𝒪 h𝒪 L)
    (negOneTensorInverse 𝒪 h𝒪 (tensorPower 𝒪 h𝒪 L (-1)))

end Site

end Stacks.PullbackTensorIso

end
