module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FirstOrderStructureTensorSplitting
public import StacksFrontier.AlgebraicGeometry.Duality.AffineProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Modules.ProjectionFormula

/-!
# The projection-formula map at the first-order universal thickening

Let `(T, J, δ)` be a divided power scheme over a scheme `Y`, let `T'` be the first-order
universal thickening of [Stacks, Tag 07J2] with `p₀ : T' ⟶ T`, and let `M` be a sheaf of
`𝒪_T`-modules. This file defines the comparison morphism

`Φ_M : M ⊗_{𝒪_T} p₀_* 𝒪_{T'} ⟶ p₀_* (p₀^* M)`,

the projection-formula map `Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap` at
`p₀` and the structure sheaf of `T'`, with the two tensor factors swapped by the braiding and the
unit factor `𝒪_{T'} ⊗_{𝒪_{T'}} p₀^* M` collapsed by the left unitor.

## Main definitions

* `Crystalline.firstOrderThickeningProjectionFormulaMap`: the morphism `Φ_M`.

## References

* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

universe u

noncomputable section

namespace Crystalline

attribute [local instance] monoidalCategorySchemeModules

/-- The monoidal product of `Mod(𝒪_X)` is braided; `Crystalline.monoidalCategorySchemeModules`
is `SheafOfModules.symmetricCategorySheafTensor` forgetting the symmetry. -/
local instance braidedCategorySchemeModules (X : Scheme.{u}) :
    BraidedCategory X.Modules :=
  (SheafOfModules.symmetricCategorySheafTensor X.sheaf).toBraidedCategory

variable (T : DividedPowerScheme.{u}) (Y : Scheme.{u}) (f : T.scheme ⟶ Y) (M : T.scheme.Modules)

/-- The projection-formula map `M ⊗_{𝒪_T} p₀_* 𝒪_{T'} ⟶ p₀_*(p₀^* M)` at the first-order
universal thickening: `Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap` at
`p₀ : T' ⟶ T` and `G = 𝒪_{T'}`, of shape `p₀_* 𝒪_{T'} ⊗ M ⟶ p₀_*(𝒪_{T'} ⊗ p₀^* M)`, preceded
by the braiding and followed by the pushforward of the left unitor. -/
def firstOrderThickeningProjectionFormulaMap :
    firstOrderThickeningTensorUnitRestriction T Y f M ⟶
      (Scheme.Modules.pushforward (firstOrderThickeningProjHom T Y f)).obj
        ((Scheme.Modules.pullback (firstOrderThickeningProjHom T Y f)).obj M) :=
  (β_ M (firstOrderThickeningUnitRestriction T Y f)).hom ≫
    Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap
        (firstOrderThickeningProjHom T Y f)
        (SheafOfModules.unit (firstOrderThickeningScheme T Y f).ringCatSheaf) M ≫
      (Scheme.Modules.pushforward (firstOrderThickeningProjHom T Y f)).map
        (λ_ ((Scheme.Modules.pullback (firstOrderThickeningProjHom T Y f)).obj M)).hom

end Crystalline

end

end
