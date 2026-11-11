module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatRimSchlessingerStarUnconditional
public import StacksFrontier.Deformation.Artin.FormalObject.OfPredeformation
public import StacksFrontier.Deformation.ClassicalCase
public import StacksFrontier.Deformation.Schlessinger.MiniversalExistence
public import StacksFrontier.Deformation.Smooth.Unobstructed

/-!
# Versal formal objects of `Spaces'_{fp, flat, proper}` over power series rings

Let `x₀ = (X ⟶ Spec k)` be an object of `𝒳 = Spaces'_{fp, flat, proper}` over a field `k` of
finite type over the base, presented over an affine chart `Spec Λ ⟶ S` with `Λ` a Noetherian
complete local ring with residue field `k` (the classical case of `𝒞_Λ`). The predeformation
category `𝓕_{𝒳,k,x₀}` is a deformation category (Stacks 07Y8, the stack satisfying (RS*) by
Stacks 0D1J). If its tangent space is finite dimensional and it is unobstructed, it has a minimal
versal formal object (Stacks 06IW, 06IX) whose complete local base is a power series ring
`Λ[[x_1, …, x_n]]` (Stacks 0DZK) and whose differential is bijective on `Der_Λ(k, k)`-orbits
(Stacks 06T8). Read over the big fppf site (Stacks 0CXH) this is a formal object of `𝒳` in the
sense of Stacks 07X4.

This is the shape of the formal object used in the proof of Stacks 0D1R: the universal deformation
of a K3 surface over `𝐂[[x_1, …, x_{20}]]`.

## Main results

* `AlgebraicGeometry.ProperFlatSpaceDeformation.exists_minimalVersal_powerSeries_of_isSmooth`.

## References

* [Stacks Project, Tag 06IW](https://stacks.math.columbia.edu/tag/06IW)
* [Stacks Project, Tag 06IX](https://stacks.math.columbia.edu/tag/06IX)
* [Stacks Project, Tag 0DZK](https://stacks.math.columbia.edu/tag/0DZK)
* [Stacks Project, Tag 07Y8](https://stacks.math.columbia.edu/tag/07Y8)
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

/-- The predeformation category `𝓕_{𝒳,k,x₀}` of a point of `Spaces'_{fp, flat, proper}`. -/
abbrev predeformationCat : PredeformationConstruction iΛ
    (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) x₀ hx₀ :=
  predeformationCategory iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) x₀ hx₀

attribute [local instance] PredeformationConstruction.category

/-- A field is the classical case of `𝒞_k` over itself: it is a Noetherian complete local ring
(its maximal ideal is zero) whose residue field is itself. -/
theorem _root_.Deformation.isClassical_self (K : Type u) [Field K] : IsClassical K K :=
  ⟨⟨inferInstance, inferInstance, by
      simpa only [IsLocalRing.maximalIdeal_eq_bot] using IsAdicComplete.bot K⟩,
    ⟨(AlgEquiv.ofBijective (Algebra.ofId K (IsLocalRing.ResidueField K))
      ⟨(algebraMap K _).injective, IsLocalRing.residue_surjective⟩).symm⟩⟩

include hfinite in
/-- `𝓕_{𝒳,k,x₀}` is a deformation category: `Spaces'_{fp, flat, proper}` satisfies (RS*)
(Stacks 0D1J), so Stacks 07Y8 applies. -/
theorem isDeformationCategory_predeformationCat :
    IsDeformationCategory (predeformationCat B S hS iΛ x₀ hx₀).projection :=
  isDeformationCategory_predeformationCategory_of_satisfiesRSStar B S hS _
    (cartesianProperFlatProjection_isFiberedInGroupoids B S hS)
    (satisfiesRSStar_cartesianProperFlat_unconditional B S hS) iΛ x₀ hx₀ hfinite.1 hfinite.2

include hfinite in
/-- **A versal formal object of an unobstructed point of `Spaces'_{fp, flat, proper}` lives over
a power series ring.** In the classical case, if the tangent space of `𝓕_{𝒳,k,x₀}` is finite
dimensional and `𝓕_{𝒳,k,x₀}` is unobstructed (its structure morphism over `𝒞_Λ` is smooth), then
`𝓕_{𝒳,k,x₀}` has a minimal versal formal object `ξ` (Stacks 06IW, 06IX) whose differential is
bijective on `Der_Λ(k, k)`-orbits (Stacks 06T8) and whose complete local base is a power series
ring `Λ[[x_1, …, x_n]]` (Stacks 0DZK). -/
theorem exists_minimalVersal_powerSeries_of_isSmooth
    (hΛ : IsClassical Λ k)
    (htangent :
      ∀ hD : IsDeformationCategory (predeformationCat B S hS iΛ x₀ hx₀).projection,
        letI : Fact (IsPredeformationCategory (BasedCategory.ofFunctor
            (predeformationCat B S hS iΛ x₀ hx₀).projection).p) := ⟨hD.predeformation⟩
        letI : Fact (SchlessingerConditionS2 (Functor.Elements.π (isomorphismClasses
            (BasedCategory.ofFunctor (predeformationCat B S hS iΛ x₀ hx₀).projection)
            hD.predeformation.cofibered))) := ⟨tangentConditionS2 hD⟩
        FiniteDimensional k (tangentSpaceArtinian Λ k (isomorphismClasses
          (BasedCategory.ofFunctor (predeformationCat B S hS iΛ x₀ hx₀).projection)
          hD.predeformation.cofibered)))
    (hsmooth : IsSmooth (baseProjection (predeformationCat B S hS iΛ x₀ hx₀).projection)) :
    ∃ (ξ : Deformation.FormalObject (predeformationCat B S hS iΛ x₀ hx₀).projection) (n : ℕ),
      Nonempty (ξ.base ≃ₐ[Λ] MvPowerSeries (Fin n) Λ) ∧
      IsMinimalVersal (isDeformationCategory_predeformationCat B S hS iΛ x₀ hx₀
        hfinite).predeformation.cofibered ξ ∧
      HasBijectiveDifferentialOnDerivationOrbits (predeformationCat B S hS iΛ x₀ hx₀).projection
        (isDeformationCategory_predeformationCat B S hS iΛ x₀ hx₀ hfinite).predeformation ξ := by
  have : IsNoetherianRing Λ := hΛ.isNoetherianRing
  have : Module.Finite Λ k := hΛ.moduleFinite
  have hD := isDeformationCategory_predeformationCat B S hS iΛ x₀ hx₀ hfinite
  obtain ⟨ξ, hmin, hdiff⟩ := exists_minimalVersal_hasBijectiveDifferentialOnDerivationOrbits Λ k
    (BasedCategory.ofFunctor (predeformationCat B S hS iΛ x₀ hx₀).projection) hD.predeformation
    (schlessingerConditionS1_of_satisfiesRS hD.satisfiesRS)
    (schlessingerConditionS2_of_satisfiesRS hD.satisfiesRS) (htangent hD)
  obtain ⟨n, ⟨e⟩⟩ :=
    (isSmooth_baseProjection_iff_powerSeries hD.predeformation ξ hmin.1 hΛ).mp hsmooth
  exact ⟨ξ, n, ⟨e⟩, hmin, hdiff⟩

end AlgebraicGeometry.ProperFlatSpaceDeformation

end
