module

public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.ImageIdealSupport
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealCoveringResolutionNoetherian

/-!
# The Noetherian case of Stacks 0F89 from morphisms out of finite locally free modules

The Noetherian case of the substantial direction of [Stacks, Tag 0F89], for a finite affine open
covering whose members are the nonvanishing loci of morphisms `θ j : 𝓔 j ⟶ 𝒪_X` out of finite
locally free modules: the sheaf of ideals attached to `U j` is the image of `θ j`.

## Main results

* `AlgebraicGeometry.hasResolutionProperty_of_isNoetherian_of_support_idealSheafDataOfHom`:
  a Noetherian scheme with a finite affine open covering whose members are the nonvanishing loci
  of morphisms out of finite locally free modules into the structure sheaf has the resolution
  property.
* `AlgebraicGeometry.hasResolutionProperty_of_isNoetherian_of_coe_support_idealSheafDataOfHom`:
  the same with the condition on the vanishing loci read as an equality of sets.

## Implementation notes

Quasi-coherence of the `𝓔 j` is an explicit hypothesis rather than derived inside the statement
from finite local freeness, because `AlgebraicGeometry.idealSheafDataOfHom` takes it as an
instance and so it has to be in scope already in the *type* of the condition on the vanishing
loci.  It is redundant:
`Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree` supplies it
from `hE`.

The set-level form is stated separately because the two spellings of the condition — an equality
of opens and an equality of their underlying sets — are not interchangeable by `rw`.

## References

* [Stacks Project, Tag 0F89](https://stacks.math.columbia.edu/tag/0F89)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPowerColimit

universe u

noncomputable section

namespace AlgebraicGeometry

/-- **The Noetherian case of the substantial direction of [Stacks, Tag 0F89], for morphisms out
of finite locally free modules.** Let `X` be a Noetherian scheme with a finite affine open
covering `U`, and for each `j` let `θ j : 𝓔 j ⟶ 𝒪_X` be a morphism out of a finite locally free
module whose image is a sheaf of ideals cutting out the complement of `U j`.  Then `X` has the
resolution property. -/
theorem hasResolutionProperty_of_isNoetherian_of_support_idealSheafDataOfHom
    {X : Scheme.{u}} [IsNoetherian X] {m : ℕ} (U : Fin m → X.Opens) (E : Fin m → X.Modules)
    (hE : ∀ j, SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) (E j))
    (θ : ∀ j, E j ⟶ structureModule X) (hqc : ∀ j, (E j).IsQuasicoherent)
    (hU : ∀ j, IsAffineOpen (U j)) (hcov : ⨆ j, U j = ⊤)
    (hsupp : ∀ j,
      (((@idealSheafDataOfHom X (E j) (hqc j) (θ j)).support.compl : X.Opens)) = U j) :
    HasResolutionProperty X :=
  hasResolutionProperty_of_epi_idealPow_of_isNoetherian U
    (fun j => @idealSheafDataOfHom X (E j) (hqc j) (θ j)) hU hcov hsupp E hE
    (fun j => @toIdealPowOfHom X (E j) (hqc j) (θ j))
    (fun j => @epi_toIdealPowOfHom X (E j) (hqc j) (θ j))

/-- The same as `hasResolutionProperty_of_isNoetherian_of_support_idealSheafDataOfHom` with the
condition on the vanishing loci read as an equality of sets. -/
theorem hasResolutionProperty_of_isNoetherian_of_coe_support_idealSheafDataOfHom
    {X : Scheme.{u}} [IsNoetherian X] {m : ℕ} (U : Fin m → X.Opens) (E : Fin m → X.Modules)
    (hE : ∀ j, SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) (E j))
    (θ : ∀ j, E j ⟶ structureModule X) (hqc : ∀ j, (E j).IsQuasicoherent)
    (hU : ∀ j, IsAffineOpen (U j)) (hcov : ⨆ j, U j = ⊤)
    (hsupp : ∀ j,
      (((@idealSheafDataOfHom X (E j) (hqc j) (θ j)).support : Set X)) = ((U j : Set X))ᶜ) :
    HasResolutionProperty X := by
  refine hasResolutionProperty_of_isNoetherian_of_support_idealSheafDataOfHom U E hE θ hqc hU
    hcov fun j => ?_
  refine Opens.ext ?_
  change (((@idealSheafDataOfHom X (E j) (hqc j) (θ j)).support : Set X))ᶜ = (U j : Set X)
  rw [hsupp j, compl_compl]

end AlgebraicGeometry

end

end
