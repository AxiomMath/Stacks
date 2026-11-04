module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FirstOrderProjectionFormulaIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderStructureTopSplitting

/-!
# The projection-formula map at the second-order universal thickening

Let `(T, J, δ)` be a divided power scheme over a scheme `Y`, let `T''` be the second-order
universal thickening of [Stacks, Remark 60.14.5, Tag 07J3] with `q₀ : T'' ⟶ T`, and let `M` be a
sheaf of `𝒪_T`-modules. This module defines the canonical comparison morphism

`Ψ_M : M ⊗_{𝒪_T} q₀_* 𝒪_{T''} ⟶ q₀_* (q₀^* M)`,

the projection-formula map of `Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap` at
`q₀` and the structure sheaf of `T''`, with the two tensor factors swapped by the braiding and the
unit factor `𝒪_{T''} ⊗_{𝒪_{T''}} q₀^* M` collapsed by the left unitor, and proves it invertible for
every `M`, with no hypothesis on `T`.

## Main definitions

* `Crystalline.secondOrderThickeningTensorUnitRestriction`: `M ⊗_{𝒪_T} q₀_* 𝒪_{T''}`.
* `Crystalline.secondOrderThickeningTensorSecondExterior`: `M ⊗_{𝒪_T} Ω²_{T/Y,δ}`.
* `Crystalline.secondOrderThickeningTensorTopInr`: `M` tensored with the inclusion of the top
  summand.
* `Crystalline.secondOrderThickeningProjectionFormulaMap`: the morphism `Ψ_M` above.

## Main results

* `Crystalline.isSplitMono_secondOrderThickeningTensorTopInr`: `M ⊗ Ω²_{T/Y,δ}` is a direct summand
  of `M ⊗ q₀_* 𝒪_{T''}`.
* `Crystalline.isAffineHom_secondOrderThickeningQ₀Hom`: `q₀ : T'' ⟶ T` is an affine morphism, for
  every divided power scheme `T`.
* `Crystalline.isClosedEmbedding_secondOrderThickeningQ₀Hom_base`: `q₀` is the identity on
  underlying topological spaces, hence a closed embedding.
* `Crystalline.isIso_secondOrderThickeningProjectionFormulaMap`: `Ψ_M` is an isomorphism for every
  `M`.

## References

* [Stacks Project, Tag 07J3](https://stacks.math.columbia.edu/tag/07J3)
* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

universe u

noncomputable section

namespace Crystalline

attribute [local instance] monoidalCategorySchemeModules

attribute [local instance] monoidalPreadditiveSchemeModules

attribute [local instance] braidedCategorySchemeModules

variable (T : DividedPowerScheme.{u}) (Y : Scheme.{u}) (f : T.scheme ⟶ Y)

/-! ### `q₀` is an affine morphism -/

/-- `q₀ : T'' ⟶ T` is an affine morphism of schemes, for every divided power scheme `T`. -/
instance isAffineHom_secondOrderThickeningQ₀Hom :
    IsAffineHom (secondOrderThickeningQ₀Hom T Y f) :=
  Stacks.Thickenings.isAffineHom_of_isThickening_section _ (secondOrderThickeningιT T Y f)
    (secondOrderThickeningιT_isThickening T Y f) (secondOrderThickeningιT_comp_Q₀Hom T Y f)

variable (M : T.scheme.Modules)

/-! ### The two tensor products -/

/-- `M ⊗_{𝒪_T} q₀_* 𝒪_{T''}`: the structure sheaf of the second-order universal thickening, read as
a sheaf of `𝒪_T`-modules through `q₀` and tensored with `M`. -/
def secondOrderThickeningTensorUnitRestriction : T.scheme.Modules :=
  M ⊗ secondOrderThickeningUnitRestriction T Y f

/-- The `𝒪_T`-module `M ⊗_{𝒪_T} Ω²_{T/Y,δ}`. -/
def secondOrderThickeningTensorSecondExterior : T.scheme.Modules :=
  M ⊗ dpSecondExteriorPower T Y f

/-- `M` tensored with the inclusion `η ↦ (0, 0, 0, η)` of the top summand of `𝒪_{T''}`. -/
def secondOrderThickeningTensorTopInr :
    secondOrderThickeningTensorSecondExterior T Y f M ⟶
      secondOrderThickeningTensorUnitRestriction T Y f M :=
  M ◁ secondOrderThickeningTopInrSheaf T Y f

/-- `M` tensored with the top coordinate of `𝒪_{T''}`, the retraction of
`Crystalline.secondOrderThickeningTensorTopInr`. -/
def secondOrderThickeningTensorTop :
    secondOrderThickeningTensorUnitRestriction T Y f M ⟶
      secondOrderThickeningTensorSecondExterior T Y f M :=
  M ◁ secondOrderThickeningTopSheaf T Y f

/-- `M` tensored with the top coordinate of `𝒪_{T''}` is a retraction of `M` tensored with the
inclusion of the top summand. -/
theorem secondOrderThickeningTensorTopInr_comp_top :
    secondOrderThickeningTensorTopInr T Y f M ≫ secondOrderThickeningTensorTop T Y f M =
      𝟙 (secondOrderThickeningTensorSecondExterior T Y f M) := by
  show (tensorLeft M).map (secondOrderThickeningTopInrSheaf T Y f) ≫
    (tensorLeft M).map (secondOrderThickeningTopSheaf T Y f) = _
  rw [← (tensorLeft M).map_comp, secondOrderThickeningTopInrSheaf_comp_topSheaf]
  exact (tensorLeft M).map_id _

/-- `M` tensored with the inclusion of the top summand is a split monomorphism. -/
theorem isSplitMono_secondOrderThickeningTensorTopInr :
    IsSplitMono (secondOrderThickeningTensorTopInr T Y f M) :=
  ⟨⟨⟨secondOrderThickeningTensorTop T Y f M,
    secondOrderThickeningTensorTopInr_comp_top T Y f M⟩⟩⟩

/-! ### The projection-formula map and its invertibility -/

/-- The projection-formula map `M ⊗_{𝒪_T} q₀_* 𝒪_{T''} ⟶ q₀_*(q₀^* M)` at the second-order
universal thickening: it is `Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap` at
`q₀ : T'' ⟶ T` and `G = 𝒪_{T''}`, whose shape is `q₀_* 𝒪_{T''} ⊗ M ⟶ q₀_*(𝒪_{T''} ⊗ q₀^* M)`,
preceded by the braiding and followed by the pushforward of the left unitor. -/
def secondOrderThickeningProjectionFormulaMap :
    secondOrderThickeningTensorUnitRestriction T Y f M ⟶
      (Scheme.Modules.pushforward (secondOrderThickeningQ₀Hom T Y f)).obj
        ((Scheme.Modules.pullback (secondOrderThickeningQ₀Hom T Y f)).obj M) :=
  (β_ M (secondOrderThickeningUnitRestriction T Y f)).hom ≫
    Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap
        (secondOrderThickeningQ₀Hom T Y f)
        (SheafOfModules.unit (secondOrderThickeningScheme T Y f).ringCatSheaf) M ≫
      (Scheme.Modules.pushforward (secondOrderThickeningQ₀Hom T Y f)).map
        (λ_ ((Scheme.Modules.pullback (secondOrderThickeningQ₀Hom T Y f)).obj M)).hom

/-- The underlying continuous map of `q₀ : T'' ⟶ T` is a closed embedding: it is the identity of
the underlying topological space of `T`. -/
theorem isClosedEmbedding_secondOrderThickeningQ₀Hom_base :
    Topology.IsClosedEmbedding
      (ConcreteCategory.hom (secondOrderThickeningQ₀Hom T Y f).toLRSHom.toShHom.hom.base) :=
  Topology.IsClosedEmbedding.id

/-- For every divided power scheme `T` over `Y` and every sheaf of `𝒪_T`-modules `M`, the
projection-formula map

`Ψ_M : M ⊗_{𝒪_T} q₀_* 𝒪_{T''} ⟶ q₀_* (q₀^* M)`

of `Crystalline.secondOrderThickeningProjectionFormulaMap` is an isomorphism. -/
theorem isIso_secondOrderThickeningProjectionFormulaMap :
    IsIso (secondOrderThickeningProjectionFormulaMap T Y f M) := by
  have h₀ : IsIso (Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap
      (secondOrderThickeningQ₀Hom T Y f)
      (SheafOfModules.unit (secondOrderThickeningScheme T Y f).ringCatSheaf :
        (secondOrderThickeningScheme T Y f).Modules) M) :=
    Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap_of_isClosedEmbedding
      _ _ _ (isClosedEmbedding_secondOrderThickeningQ₀Hom_base T Y f)
  rw [secondOrderThickeningProjectionFormulaMap]
  refine IsIso.comp_isIso' (Iso.isIso_hom _) (IsIso.comp_isIso' h₀ ?_)
  exact Iso.isIso_hom
    ((Scheme.Modules.pushforward (secondOrderThickeningQ₀Hom T Y f)).mapIso (λ_ _))

end Crystalline

end

end
