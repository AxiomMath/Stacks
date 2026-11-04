module

public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.NormGroupTensorChart

/-!
# The norm-group product identity for an identity morphism

`Stacks.Divisors.hasNormGroupProductTensor_of_app_norm_eq_prod` derives
`Stacks.Divisors.HasNormGroupProductTensor`, the hint of Stacks 0FH9, from two hypotheses: the
side condition `∀ σ, a σ ≫ π = π`, and the identity

  `π^♯ (Norm_π s) = ∏_{σ ∈ G} (a σ)^♯ s`

on functions. This file verifies both for `π = 𝟙 X` with the identity norm of degree `1`
(`Stacks.Divisors.idMorphismNorm`), the index type `PUnit` and the constant family
`a = fun _ => 𝟙 X`, so that `Stacks.Divisors.HasNormGroupProductTensor` and its Picard-class form
`Stacks.Divisors.HasNormGroupProductPullback` hold there for every scheme `X`.

## Main results

* `Stacks.Divisors.appLE_id_eq_map`: `AlgebraicGeometry.Scheme.Hom.appLE` of the identity
  morphism is the restriction map of the structure sheaf.
* `Stacks.Divisors.idMorphismNorm`: the identity morphism's norm of degree one.
* `Stacks.Divisors.idMorphismNorm_app_norm_eq_prod`: the identity on functions, for that norm and
  a one-element index type.
* `Stacks.Divisors.hasNormGroupProductTensor_id`: `Stacks.Divisors.HasNormGroupProductTensor` for
  the identity morphism.
* `Stacks.Divisors.hasNormGroupProductPullback_id`: the same for the Picard-class form.

## References

* Stacks Project, Tag 0FH9: https://stacks.math.columbia.edu/tag/0FH9
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.Norm (MorphismNorm)

universe u

namespace Stacks.Divisors

/-- **`AlgebraicGeometry.Scheme.Hom.appLE` of an identity morphism is a restriction map.** For
opens `V ≤ (𝟙 X) ⁻¹ᵁ U`, `(𝟙 X).appLE U V` is the restriction `Γ(X, U) ⟶ Γ(X, V)` of the
structure sheaf. -/
theorem appLE_id_eq_map {X : Scheme.{u}} (U V : X.Opens) (h : V ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U) :
    (𝟙 X : X ⟶ X).appLE U V h = X.presheaf.map (homOfLE h).op :=
  Category.id_comp _

/-- **The norm of degree one carried by an identity morphism.** On every open `U` the norm is the
identity of `Γ(X, U)`. -/
def idMorphismNorm (X : Scheme.{u}) : MorphismNorm (𝟙 X) 1 where
  app U := MonoidHom.id Γ(X, U)
  naturality _ _ := rfl
  app_eq_zero_at_image _ _ _ hs := hs
  app_pullback _ g := (pow_one g).symm

/-- **The identity on functions of Stacks 0FH9, for the identity morphism and a one-element index
type.** With `π = 𝟙 X`, the norm `Stacks.Divisors.idMorphismNorm` and the constant family
`fun _ : PUnit => 𝟙 X`, `π^♯ (Norm_π s) = ∏_{σ ∈ PUnit} (a σ)^♯ s`. -/
theorem idMorphismNorm_app_norm_eq_prod (X : Scheme.{u}) (V : X.Opens)
    (s : Γ(X, (𝟙 X : X ⟶ X) ⁻¹ᵁ V)) :
    ((𝟙 X : X ⟶ X).app V).hom ((idMorphismNorm X).app V s) =
      ∏ σ : PUnit.{u + 1}, (((fun _ : PUnit.{u + 1} => (𝟙 X : X ⟶ X)) σ).appLE
          ((𝟙 X : X ⟶ X) ⁻¹ᵁ V) ((𝟙 X : X ⟶ X) ⁻¹ᵁ V)
          (le_of_eq (preimage_preimage_of_comp_eq
            (Category.comp_id (𝟙 X : X ⟶ X)) V).symm)).hom s :=
  ((Fintype.prod_unique _).trans
    (congrArg (fun f : Γ(X, (𝟙 X : X ⟶ X) ⁻¹ᵁ V) ⟶ Γ(X, (𝟙 X : X ⟶ X) ⁻¹ᵁ V) =>
        (CommRingCat.Hom.hom f) s)
      ((appLE_id_eq_map ((𝟙 X : X ⟶ X) ⁻¹ᵁ V) ((𝟙 X : X ⟶ X) ⁻¹ᵁ V) _).trans
        (X.presheaf.map_id (op ((𝟙 X : X ⟶ X) ⁻¹ᵁ V)))))).symm

/-- **The hint of Stacks 0FH9 for an identity morphism.**
`Stacks.Divisors.HasNormGroupProductTensor` holds at `π = 𝟙 X`, the norm
`Stacks.Divisors.idMorphismNorm X` of degree `1`, `G = PUnit` and `a = fun _ => 𝟙 X`. -/
theorem hasNormGroupProductTensor_id (X : Scheme.{u}) :
    HasNormGroupProductTensor (𝟙 X) (idMorphismNorm X) (fun _ : PUnit.{u + 1} => 𝟙 X) :=
  hasNormGroupProductTensor_of_app_norm_eq_prod (𝟙 X) (idMorphismNorm X)
    (fun _ : PUnit.{u + 1} => 𝟙 X) (fun _ => Category.comp_id _)
    (idMorphismNorm_app_norm_eq_prod X)

/-- **The Picard-class form of the hint for an identity morphism.**
`Stacks.Divisors.HasNormGroupProductPullback` holds at `π = 𝟙 X`, the norm
`Stacks.Divisors.idMorphismNorm X`, `G = PUnit` and `a = fun _ => 𝟙 X`. -/
theorem hasNormGroupProductPullback_id (X : Scheme.{u}) :
    HasNormGroupProductPullback (𝟙 X) (idMorphismNorm X) (fun _ : PUnit.{u + 1} => 𝟙 X) :=
  hasNormGroupProductPullback_of_hasNormGroupProductTensor (𝟙 X) (idMorphismNorm X)
    (fun _ : PUnit.{u + 1} => 𝟙 X) (hasNormGroupProductTensor_id X)

end Stacks.Divisors

end
