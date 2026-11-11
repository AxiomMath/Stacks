module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatPredeformationFiniteTangent
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatPredeformationUnobstructed
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatVersalPowerSeries

/-!
# The versal deformation of an unobstructed point of `Spaces'_{fp, flat, proper}`

Let `x₀ = (X₀ ⟶ Spec k)` be an object of `𝒳 = Spaces'_{fp, flat, proper}` over a field `k` of
finite type over the base, presented over an affine chart `Spec Λ ⟶ S` with `Λ` a Noetherian
complete local ring with residue field `k`. If the obstruction groups
`T²(I) = Ext²_{𝒪_X}(L_{X/A}, 𝒪_X ⊗_A I)` of all deformations `X ⟶ Spec A` of `x₀` vanish, the
predeformation category `𝓕_{𝒳,k,x₀}` is unobstructed, its tangent space is finite dimensional,
and it has a minimal versal formal object over a power series ring `Λ[[x_1, …, x_n]]` whose
differential (the Kodaira–Spencer map) is bijective on `Der_Λ(k, k)`-orbits. Read over the big
fppf site this is a formal object of `𝒳` in the sense of Stacks 07X4, over the complete local
base `Λ[[x_1, …, x_n]]`.

For a K3 surface over `k = 𝐂` this is the universal deformation over `𝐂[[x_1, …, x_{20}]]` used in
the proof of Stacks 0D1R.

## Main results

* `exists_minimalVersal_powerSeries_of_obstructionGroupsVanish`:
  the minimal versal formal object of `𝓕_{𝒳,k,x₀}` over a power series ring.
* `exists_formalObject_powerSeries_of_obstructionGroupsVanish`:
  the formal object of `𝒳` over the big fppf site that it gives.

## References

* [Stacks Project, Tag 06IW](https://stacks.math.columbia.edu/tag/06IW)
* [Stacks Project, Tag 0DZK](https://stacks.math.columbia.edu/tag/0DZK)
* [Stacks Project, Tag 07X4](https://stacks.math.columbia.edu/tag/07X4)
* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
-/

@[expose] public noncomputable section

open CategoryTheory Deformation Deformation.Artin

namespace AlgebraicGeometry.ProperFlatSpaceDeformation

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
  (x₀ : CartesianProperFlatSpaces B S hS)
  (hx₀ : (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
    QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))

attribute [local instance] PredeformationConstruction.category

include hfinite in
/-- **The minimal versal deformation of a point of `Spaces'_{fp, flat, proper}` with vanishing
obstruction groups.** In the classical case, if the obstruction groups of all deformations of
`x₀` vanish, the predeformation category `𝓕_{𝒳,k,x₀}` has a minimal versal formal object `ξ`
over a power series ring `Λ[[x_1, …, x_n]]` whose differential — the Kodaira–Spencer map from
`Der_Λ(ξ.base, k)` to the tangent space of `𝓕_{𝒳,k,x₀}` — is bijective on
`Der_Λ(k, k)`-orbits. -/
theorem exists_minimalVersal_powerSeries_of_obstructionGroupsVanish (hΛ : IsClassical Λ k)
    (h : DeformationObstructionGroupsVanish (B := B) (S := S) (hS := hS) (iΛ := iΛ) (x₀ := x₀)
      (hx₀ := hx₀)) :
    ∃ (ξ : Deformation.FormalObject (predeformationCat B S hS iΛ x₀ hx₀).projection) (n : ℕ),
      Nonempty (ξ.base ≃ₐ[Λ] MvPowerSeries (Fin n) Λ) ∧
      IsMinimalVersal (isDeformationCategory_predeformationCat B S hS iΛ x₀ hx₀
        hfinite).predeformation.cofibered ξ ∧
      HasBijectiveDifferentialOnDerivationOrbits (predeformationCat B S hS iΛ x₀ hx₀).projection
        (isDeformationCategory_predeformationCat B S hS iΛ x₀ hx₀ hfinite).predeformation ξ :=
  exists_minimalVersal_powerSeries_of_isSmooth B S hS iΛ x₀ hx₀ hfinite hΛ
    (finiteDimensional_tangentSpaceArtinian_predeformation B S hS iΛ x₀ hx₀)
    (isSmooth_baseProjection_predeformationCat_of_obstructionGroupsVanish B S hS iΛ x₀ hx₀ h)

/-- **The formal deformation of a point of `Spaces'_{fp, flat, proper}` with vanishing
obstruction groups, over the big fppf site.** In the classical case, if the obstruction groups
of all deformations of `x₀` vanish, there is a formal object of `Spaces'_{fp, flat, proper}`
(Stacks 07X4) which is the image (Stacks 0CXH), with the same complete local base
`ξ.base.R = η.base ≅ Λ[[x_1, …, x_n]]`, of a minimal versal formal object `η` of
`𝓕_{𝒳,k,x₀}` with bijective Kodaira–Spencer map on `Der_Λ(k, k)`-orbits. -/
theorem exists_formalObject_powerSeries_of_obstructionGroupsVanish (hΛ : IsClassical Λ k)
    (h : DeformationObstructionGroupsVanish (B := B) (S := S) (hS := hS) (iΛ := iΛ) (x₀ := x₀)
      (hx₀ := hx₀)) :
    ∃ (ξ : Deformation.Artin.FormalObject B S hS (cartesianProperFlatProjection B S hS))
      (η : Deformation.FormalObject (predeformationCat B S hS iΛ x₀ hx₀).projection) (n : ℕ),
      ξ = FormalObject.ofPredeformation B S hS iΛ (cartesianProperFlatProjection B S hS) x₀ hx₀
        hfinite η ∧
      Nonempty (η.base ≃ₐ[Λ] MvPowerSeries (Fin n) Λ) ∧
      IsMinimalVersal (isDeformationCategory_predeformationCat B S hS iΛ x₀ hx₀
        hfinite).predeformation.cofibered η ∧
      HasBijectiveDifferentialOnDerivationOrbits (predeformationCat B S hS iΛ x₀ hx₀).projection
        (isDeformationCategory_predeformationCat B S hS iΛ x₀ hx₀ hfinite).predeformation η := by
  obtain ⟨η, n, ⟨e⟩, hmin, hdiff⟩ :=
    exists_minimalVersal_powerSeries_of_obstructionGroupsVanish B S hS iΛ x₀ hx₀ hfinite hΛ h
  exact ⟨_, η, n, rfl, ⟨e⟩, hmin, hdiff⟩

end AlgebraicGeometry.ProperFlatSpaceDeformation

end
