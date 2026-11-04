module

public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionClassInvariance
public import StacksFrontier.Deformation.RingedSpaceThickening.SquareZeroAlgebraExtensionClassification

/-!
# The class of a square-zero extension through an arbitrary presentation (Stacks 0GQ0)

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` be a morphism of ringed spaces, `𝒢` an `𝒪_X`-module and
`0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` an extension of `f⁻¹𝒪_S`-algebras with `𝒢` an ideal of square
zero. **Stacks 0GQ0** chooses an arbitrary sheaf of sets `ℰ` with a commutative diagram
`α' : ℰ ⟶ 𝒪_{X'}`, `α : ℰ ⟶ 𝒪_X` such that `f⁻¹𝒪_S[ℰ] ⟶ 𝒪_X` is surjective, and reads off
the class of `𝒪_{X'}` from the map `𝒥/𝒥² ⟶ 𝒢` that `α'` induces.

This file attaches to such a datum the presented extension `withGenerators` and proves that its
class in `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` does not depend on the choice: it is the class of the
presentation by the sheaf of sets underlying `𝒪_{X'}` itself.

## Main definitions

* `AlgebraSquareZeroExtension.withGenerators`: the extension `𝒪_{X'}` presented by
  `(ℰ, α, α')`.

## Main results

* `AlgebraSquareZeroExtension.extClass_withGenerators`: the class attached to `(ℰ, α, α')`
  equals the class attached to the canonical presentation `toPresented`.
* `SquareZeroAlgebraExtension.isomorphismClassesEquivExt_mk_eq_presented`: **Stacks 0GQ0**, the
  class attached to `(ℰ, α, α')` is the image of the class of `𝒪_{X'}` under the canonical
  bijection `isomorphismClassesEquivExt` of **Stacks 0GPZ**.

## References

* [Stacks Project, Tag 0GQ0](https://stacks.math.columbia.edu/tag/0GQ0)
* [Stacks Project, Tag 0GPZ](https://stacks.math.columbia.edu/tag/0GPZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Sites.FreeAlgebra (underlyingPresheaf)

universe u

attribute [local instance 5000] _root_.SheafOfModules.instAbelian

namespace AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension

variable {X S : RingedSpace.{u, u}} {f : X ⟶ S}
  {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}
  (P : AlgebraSquareZeroExtension f G)

/-- The extension `𝒪_{X'}` presented by a sheaf of sets `ℰ` and a commutative diagram
`α' : ℰ ⟶ 𝒪_{X'}`, `α : ℰ ⟶ 𝒪_X` over the reduction `𝒪_{X'} ⟶ 𝒪_X`. -/
@[simps]
def withGenerators (E : Functor (Opens X.carrier)ᵒᵖ (Type u))
    (α : E ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf)
    (α' : E ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier) P.sheaf)
    (hα : α' ≫ P.generatorsMap = α) : PresentedSquareZeroExtension f G E α where
  sheaf := P.sheaf
  base := P.base
  reduction := P.reduction
  base_comp_reduction := P.base_comp_reduction
  liftGen := α'
  liftGen_comp := hα
  ideal := P.ideal

section Derived

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The class does not depend on the presentation.** For an arbitrary sheaf of sets `ℰ` with a
commutative diagram `α' : ℰ ⟶ 𝒪_{X'}`, `α : ℰ ⟶ 𝒪_X` such that `f⁻¹𝒪_S[ℰ] ⟶ 𝒪_X` is
surjective, the class in `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` of the map `𝒥/𝒥² ⟶ 𝒢` determined by `α'`
is the class of the canonical presentation by the sheaf of sets underlying `𝒪_{X'}`. -/
theorem extClass_withGenerators (E : Functor (Opens X.carrier)ᵒᵖ (Type u))
    (α : E ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf)
    (α' : E ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier) P.sheaf)
    (hα : α' ≫ P.generatorsMap = α)
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      (generatorsPresentation f E α).hom] :
    (P.withGenerators E α α' hα).extClass = P.toPresented.extClass :=
  PresentedSquareZeroExtension.extClass_eq_of_hom (P.withGenerators E α α' hα) P.toPresented
    α' hα (𝟙 _) (Category.id_comp _) (Category.comp_id _) rfl (fun _ _ ↦ rfl)

end Derived

end AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension

namespace AlgebraicGeometry.RingedSpaceThickening.SquareZeroAlgebraExtension

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S : RingedSpace.{u, u}} {f : X ⟶ S}
  {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}

/-- **Stacks Project, Tag 0GQ0.** Let `0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` be an extension of
`f⁻¹𝒪_S`-algebras with `𝒢` an ideal of square zero, and let `ℰ` be any (pre)sheaf of sets with a
commutative diagram `α' : ℰ ⟶ 𝒪_{X'}`, `α : ℰ ⟶ 𝒪_X` over the reduction (`hα`) such that
`f⁻¹𝒪_S[ℰ] ⟶ 𝒪_X` is surjective, with kernel `𝒥`. The map `f⁻¹𝒪_S[ℰ] ⟶ 𝒪_{X'}` determined by
`α'` induces `𝒥/𝒥² ⟶ 𝒢` (`conormalToIdeal`); its class in `Ext¹_{𝒪_X}(𝖭𝖫(α), 𝒢)`
(`conormalExtClass` on `𝖭𝖫(α) = (𝒥/𝒥² ⟶ Ω ⊗ 𝒪_X)`), carried to `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` along
the identification `𝖭𝖫(α) ≅ 𝖭𝖫_{X/S}` of **Stacks 08TL** (`naiveCotangentIso`), is the element
the canonical bijection of **Stacks 0GPZ** attaches to the class of `𝒪_{X'}`. -/
@[stacks 0GQ0]
theorem isomorphismClassesEquivExt_mk_eq_presented (P : SquareZeroAlgebraExtension f G)
    (E : Functor (Opens X.carrier)ᵒᵖ (Type u))
    (α : E ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf)
    (α' : E ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier) P.sheaf)
    (hα : α' ≫ P.generatorsMap = α)
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      (generatorsPresentation f E α).hom] :
    (PresentedSquareZeroExtension.naiveCotangentIso f E α).inv ≫
        (PresentedSquareZeroExtension.twoTerm f E α).conormalExtClass G
          (P.withGenerators E α α' hα).conormalToIdeal =
      isomorphismClassesEquivExt f G ⟦P⟧ :=
  P.extClass_withGenerators E α α' hα

end AlgebraicGeometry.RingedSpaceThickening.SquareZeroAlgebraExtension

end
