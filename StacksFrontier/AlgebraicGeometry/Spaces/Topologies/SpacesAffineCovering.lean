module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesAffineDensity
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite
public import StacksFrontier.CategoryTheory.Sites.Pretopology.CombinatorialEquivalence

/-!
# Affine coverings in the spaces-étale site

Every object of the spaces-étale site of an algebraic space `X` has a covering family by affine
schemes, and every covering family is refined by one whose members are affine schemes.

## Main results

* `exists_isCovering_isAffineScheme_spacesAffineCovering`: every object of the spaces-étale site
  has a covering family by affine schemes.
* `exists_isCovering_isAffineScheme_refinement_spacesAffineCovering`: every covering family is
  refined by a covering family by affine schemes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace SpacesEtale

variable (X : AlgebraicSpaces B S hS)

/-- Every object of the spaces-étale site of `X` admits a covering family whose members are
representable by affine schemes. -/
theorem exists_isCovering_isAffineScheme_spacesAffineCovering (U : SpacesEtale B S hS X) :
    ∃ E : PreZeroHypercover.{u + 1} U, IsCovering B S hS X ⟨U, E⟩ ∧
      ∀ i, IsAffineScheme B S hS X (E.X i) := by
  obtain ⟨W, b, hWaff, hbEt, hbpt, -⟩ := exists_isEtaleCovering_affine B S hS
    ((toSpaces B S hS X).obj U).1 ((toSpaces B S hS X).obj U).2
  let c := fun x ↦ Over.mk ((ObjectProperty.homMk (b x) :
    (schemeSpaceFunctor B S hS).obj (W x) ⟶ (toSpaces B S hS X).obj U) ≫ U.obj.hom)
  have hcEt : ∀ x, IsEtaleOver B S hS X (c x) := fun x ↦ by
    change IsEtale B S hS (b x ≫ U.obj.hom.hom)
    exact isEtale_of_presheaf_etale B S hS
      (U.property (W x) (b x) (presheaf_etale_of_isEtale B S hS (hbEt x)))
  let E : PreZeroHypercover.{u + 1} U :=
    { I₀ := points B S hS ((toSpaces B S hS X).obj U).1
      X := fun x ↦ ⟨c x, hcEt x⟩
      f := fun x ↦ ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk (b x)) rfl) }
  exact ⟨E, fun x ↦ ⟨x, hbpt x⟩, fun x ↦ ⟨W x, hWaff x, ⟨Iso.refl _⟩⟩⟩

/-- A jointly point-surjective family of the spaces-étale site of `X` is refined by a jointly
point-surjective family whose members are representable by affine schemes. -/
theorem exists_isCovering_isAffineScheme_refinement_spacesAffineCovering {V : SpacesEtale B S hS X}
    (E : PreZeroHypercover.{u + 1} V) (hE : IsCovering B S hS X ⟨V, E⟩) :
    ∃ F : PreZeroHypercover.{u + 1} V, IsCovering B S hS X ⟨V, F⟩ ∧
      (∀ j, IsAffineScheme B S hS X (F.X j)) ∧
        ∀ j, ∃ i, ∃ a : F.X j ⟶ E.X i, a ≫ E.f i = F.f j := by
  choose G hG hGa using fun i ↦
    exists_isCovering_isAffineScheme_spacesAffineCovering B S hS X (E.X i)
  refine ⟨E.bind fun i ↦ (G i).pushforward (eqToHom rfl),
    (isSite B S hS X).2.1 ⟨V, E⟩ hE (fun i ↦ ⟨E.X i, G i⟩) hG (fun _ ↦ rfl),
    fun j ↦ hGa j.1 j.2, fun j ↦ ⟨j.1, (G j.1).f j.2 ≫ eqToHom rfl, rfl⟩⟩

end SpacesEtale

end Space

end AlgebraicGeometry

end
