module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatObstructionBaseChangeVanishing
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatVersalDeformation

/-!
# The versal deformation of a point of `Spaces'_{fp, flat, proper}` with `T² = 0`

Let `x₀ = (X₀ ⟶ Spec k)` be an object of `𝒳 = Spaces'_{fp, flat, proper}` over a field `k` of
finite type over the base, presented over an affine chart `Spec Λ ⟶ S` with `Λ` a Noetherian
complete local ring with residue field `k`. If `T²_{X₀/k}(k) = Ext²_{𝒪_{X₀}}(L_{X₀/k}, 𝒪_{X₀})`
vanishes — for `X₀` smooth over `k` this is `H²(X₀, T_{X₀}) = 0` — then the obstruction groups of
all deformations of `x₀` vanish, and `𝒳` has a formal object over a power series ring
`Λ[[x_1, …, x_n]]` which is a minimal versal formal object of `𝓕_{𝒳,k,x₀}` with bijective
Kodaira–Spencer map on `Der_Λ(k, k)`-orbits.

For a K3 surface `X₀` over `k = 𝐂` (where `H²(T_{X₀}) = H⁰(Ω_{X₀})^∨ = 0`) this is the formal
deformation over `𝐂[[x_1, …, x_{20}]]` used in the proof of Stacks 0D1R. All directions are
needed there: the Kodaira–Spencer map must be surjective onto `H¹(T_{X₀})`, a one-parameter
deformation does not suffice.

## Main results

* `exists_formalObject_powerSeries_of_subsingleton_cotangentExtTwo` (in the namespace
  `AlgebraicGeometry.ProperFlatSpaceDeformation`).

## References

* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
* [Stacks Project, Tag 0DZK](https://stacks.math.columbia.edu/tag/0DZK)
-/

@[expose] public noncomputable section

open CategoryTheory Deformation Deformation.Artin

attribute [-instance] AlgebraicGeometry.Space.modelHasSheafifyULift
  AlgebraicGeometry.Space.modelWEqualsLocallyBijectiveULift

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
attribute [local instance 10000] HasDerivedCategory.standard

/-- **The formal deformation of a point of `Spaces'_{fp, flat, proper}` with
`Ext²(L_{X₀/k}, 𝒪_{X₀}) = 0`.** In the classical case, if `T²_{X₀/k}(k) = 0`, there is a formal
object `ξ` of `Spaces'_{fp, flat, proper}` over the big fppf site (Stacks 07X4) which is the
image (Stacks 0CXH), with the same complete local base `ξ.base.R = η.base ≅ Λ[[x_1, …, x_n]]`,
of a minimal versal formal object `η` of `𝓕_{𝒳,k,x₀}` whose Kodaira–Spencer map is bijective on
`Der_Λ(k, k)`-orbits. -/
theorem exists_formalObject_powerSeries_of_subsingleton_cotangentExtTwo (hΛ : IsClassical Λ k)
    (hT2 : Subsingleton
      ((Space.cotangentExtTwo (Space.ProperFlatLift.chartStructureMap x₀
          (obj_eq_specialFibre x₀ hx₀))
        (Space.ProperFlatLift.chartBaseRingHom x₀ (obj_eq_specialFibre x₀ hx₀))).obj
          (ModuleCat.of k k))) :
    ∃ (ξ : Deformation.Artin.FormalObject B S hS (cartesianProperFlatProjection B S hS))
      (η : Deformation.FormalObject (predeformationCat B S hS iΛ x₀ hx₀).projection) (n : ℕ),
      ξ = FormalObject.ofPredeformation B S hS iΛ (cartesianProperFlatProjection B S hS) x₀ hx₀
        hfinite η ∧
      Nonempty (η.base ≃ₐ[Λ] MvPowerSeries (Fin n) Λ) ∧
      IsMinimalVersal (isDeformationCategory_predeformationCat B S hS iΛ x₀ hx₀
        hfinite).predeformation.cofibered η ∧
      HasBijectiveDifferentialOnDerivationOrbits (predeformationCat B S hS iΛ x₀ hx₀).projection
        (isDeformationCategory_predeformationCat B S hS iΛ x₀ hx₀ hfinite).predeformation η :=
  exists_formalObject_powerSeries_of_obstructionGroupsVanish B S hS iΛ x₀ hx₀ hfinite hΛ
    (deformationObstructionGroupsVanish_of_subsingleton hT2)

end AlgebraicGeometry.ProperFlatSpaceDeformation

end
