module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FirstOrderProjectionFormulaMap
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaIdentityBase
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaLocal
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine

/-!
# The projection-formula map at the first-order universal thickening is invertible

Let `(T, J, δ)` be a divided power scheme over a scheme `Y`, let `T'` be the first-order
universal thickening of [Stacks, Tag 07J2] with `p₀ : T' ⟶ T`, and let `M` be a sheaf of
`𝒪_T`-modules. `Crystalline.firstOrderThickeningProjectionFormulaMap` is the comparison
morphism

`Φ_M : M ⊗_{𝒪_T} p₀_* 𝒪_{T'} ⟶ p₀_* (p₀^* M)`.

This module proves `Φ_M` invertible for every `M`, with no hypothesis on `T`: `T` need not be
affine and `M` need not be quasi-coherent. It also proves that `p₀` is affine.

## Main results

* `Stacks.Thickenings.isAffineHom_of_isThickening_section`: a morphism of schemes admitting a
  thickening as a section is affine.
* `Crystalline.isAffineHom_firstOrderThickeningProjHom`: `p₀ : T' ⟶ T` is an affine morphism,
  for every divided power scheme `T`.
* `Crystalline.isClosedEmbedding_firstOrderThickeningProjHom_base`: `p₀` is the identity on
  underlying topological spaces, hence a closed embedding.
* `Crystalline.isIso_firstOrderThickeningProjectionFormulaMap`: `Φ_M` is an isomorphism for
  every `M`.

## References

* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory TopologicalSpace

universe u

noncomputable section

namespace Stacks.Thickenings

/-- A morphism of schemes `g : X' ⟶ X` admitting a thickening `s : X ⟶ X'` as a section,
`s ≫ g = 𝟙 X`, is affine. -/
theorem isAffineHom_of_isThickening_section {X X' : Scheme.{u}} (g : X' ⟶ X) (s : X ⟶ X')
    (hs : IsThickening s) (hsg : s ≫ g = 𝟙 X) : IsAffineHom g := by
  refine ⟨fun U hU => ?_⟩
  have hpre : s ⁻¹ᵁ (g ⁻¹ᵁ U) = U := by
    have h : (s ≫ g) ⁻¹ᵁ U = s ⁻¹ᵁ (g ⁻¹ᵁ U) := by
      rw [Scheme.Hom.comp_base, Opens.map_comp_obj]
    rw [← h, hsg]
    rfl
  have : IsAffine (s ⁻¹ᵁ (g ⁻¹ᵁ U)).toScheme := by rw [hpre]; exact hU
  have : IsClosedImmersion s := hs.1
  have : AlgebraicGeometry.Surjective s := ⟨hs.2⟩
  have hci : IsClosedImmersion (s ∣_ (g ⁻¹ᵁ U)) :=
    IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion) inferInstance _
  have hsu : AlgebraicGeometry.Surjective (s ∣_ (g ⁻¹ᵁ U)) :=
    IsZariskiLocalAtTarget.restrict (P := @AlgebraicGeometry.Surjective) inferInstance _
  exact isAffine_of_isThickening (i := s ∣_ (g ⁻¹ᵁ U)) ⟨hci, hsu.surj⟩

end Stacks.Thickenings

namespace Crystalline

attribute [local instance] monoidalCategorySchemeModules

attribute [local instance] braidedCategorySchemeModules

variable (T : DividedPowerScheme.{u}) (Y : Scheme.{u}) (f : T.scheme ⟶ Y)

/-- The projection `p₀ : T' ⟶ T` from the first-order universal thickening is an affine
morphism of schemes, for every divided power scheme `T`. -/
instance isAffineHom_firstOrderThickeningProjHom :
    IsAffineHom (firstOrderThickeningProjHom T Y f) :=
  Stacks.Thickenings.isAffineHom_of_isThickening_section _ (firstOrderThickeningι T Y f)
    (firstOrderThickeningι_isThickening T Y f) (firstOrderThickeningι_comp_projHom T Y f)

/-- The projection `p₀ : T' ⟶ T` is the identity on underlying topological spaces, hence a
closed embedding. -/
theorem isClosedEmbedding_firstOrderThickeningProjHom_base :
    Topology.IsClosedEmbedding
      (ConcreteCategory.hom (firstOrderThickeningProjHom T Y f).toLRSHom.toShHom.hom.base) :=
  Topology.IsClosedEmbedding.id

variable (M : T.scheme.Modules)

/-- For every divided power scheme `T` over `Y` and every sheaf of `𝒪_T`-modules `M`, the
comparison morphism

`Φ_M : M ⊗_{𝒪_T} p₀_* 𝒪_{T'} ⟶ p₀_* (p₀^* M)`

of `Crystalline.firstOrderThickeningProjectionFormulaMap` is an isomorphism. -/
theorem isIso_firstOrderThickeningProjectionFormulaMap :
    IsIso (firstOrderThickeningProjectionFormulaMap T Y f M) := by
  have h₀ : IsIso (Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap
      (firstOrderThickeningProjHom T Y f)
      (SheafOfModules.unit (firstOrderThickeningScheme T Y f).ringCatSheaf :
        (firstOrderThickeningScheme T Y f).Modules) M) :=
    Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap_of_isClosedEmbedding
      _ _ _ (isClosedEmbedding_firstOrderThickeningProjHom_base T Y f)
  rw [firstOrderThickeningProjectionFormulaMap]
  exact IsIso.comp_isIso' (Iso.isIso_hom _) (IsIso.comp_isIso' h₀ (Iso.isIso_hom
    ((Scheme.Modules.pushforward (firstOrderThickeningProjHom T Y f)).mapIso (λ_ _))))

end Crystalline

end

end
