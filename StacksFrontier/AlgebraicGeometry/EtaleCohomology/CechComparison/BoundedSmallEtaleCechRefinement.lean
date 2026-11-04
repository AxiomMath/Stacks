module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.BoundedSmallEtaleAssociatedSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.BoundedSmallEtaleDisjointUnion

/-!
# Čech-acyclic refinements of a covering sieve on the size-bounded small étale site

`AlgebraicGeometry.SmallEtale.isZero_cechCohomology_succ_associatedModule` gives the
positive-degree Čech vanishing of `Fᵃ` on the size-bounded small étale site of `S` for a family
whose image in Mathlib's small étale site is a small-étale-standard covering, and
`AlgebraicGeometry.SmallEtale.exists_isSmallEtaleStandardCovering_map_sieve₀_le` says such families
are cofinal among the covering sieves of an object with affine total space.  Together they turn the
vanishing into a statement about covering sieves.

The second statement adds the disjoint union of the refining family, by
`AlgebraicGeometry.SmallEtale.exists_affine_sigma_refinement`: the family then sits inside a
single affine object of the site, and all of the hypothesis `hdet` of
`SheafOfModules.surjective_val_app_of_epi_of_detectsRange` is present except its
`SheafOfModules.DetectsRange` clause.

## Main results

Both in the namespace `AlgebraicGeometry.SmallEtale`:

* `exists_sieve₀_le_isZero_cechCohomology_succ_associatedModule`: every covering sieve of an object
  with affine total space contains a family along which the positive-degree Čech cohomology of `Fᵃ`
  vanishes.
* `exists_sigma_sieve₀_le_isZero_cechCohomology_succ_associatedModule`: the same with the disjoint
  union of the family, its inclusions and their disjointness.

## Implementation notes

Neither statement is a clause of a tag and neither carries a `@[stacks]` attribute.  Tag 03DW on
this site needs, beyond them, the comparison of the Čech complex of the family with the Amitsur
complex of the single morphism out of the disjoint union, and the identification of the kernel of
the epimorphism at issue with an associated module, which on this site is the essential
surjectivity of `AlgebraicGeometry.SmallEtale.associatedModuleQcohOnSite`, the proposition
`AlgebraicGeometry.SmallEtale.QuasicoherentIsEssImageAssociatedModule`.

## References

* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 03XA](https://stacks.math.columbia.edu/tag/03XA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (F : S.Modules)
  [F.IsQuasicoherent]

/-- **Every covering sieve of an object of the size-bounded small étale site with affine total
space contains a family along which the positive-degree Čech cohomology of `Fᵃ` vanishes.** -/
public theorem exists_sieve₀_le_isZero_cechCohomology_succ_associatedModule
    (T : SmallEtale B S hS) (hT : _root_.AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T))
    {R : Sieve T} (hR : R ∈ topology B S hS T) :
    ∃ 𝒱 : PreZeroHypercover.{u} T, 𝒱.sieve₀ ≤ R ∧ ∀ p : ℕ, 0 < p →
      IsZero (Stacks.CechSite.cechCohomology 𝒱
        ((associatedModule B S hS).obj F).val.presheaf p) := by
  obtain ⟨𝒱, h𝒱, hle⟩ :=
    exists_isSmallEtaleStandardCovering_map_sieve₀_le B S hS T hT hR
  exact ⟨𝒱, hle, fun p hp ↦ isZero_cechCohomology_succ_associatedModule B S hS F 𝒱 h𝒱 p hp⟩

/-- **The Čech-acyclic refinement of a covering sieve, inside a single affine object of the
site.**  Everything `SheafOfModules.surjective_val_app_of_epi_of_detectsRange` asks of a covering
sieve except the `SheafOfModules.DetectsRange` clause for the morphism `h`, together with the
positive-degree Čech vanishing of `Fᵃ` along the family. -/
public theorem exists_sigma_sieve₀_le_isZero_cechCohomology_succ_associatedModule
    (T : SmallEtale B S hS) (hT : _root_.AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T))
    {R : Sieve T} (hR : R ∈ topology B S hS T) :
    ∃ (𝒱 : PreZeroHypercover.{u} T) (W : SmallEtale B S hS) (h : W ⟶ T)
      (a : ∀ i, 𝒱.X i ⟶ W),
      (∀ i, R (𝒱.f i)) ∧
      _root_.AlgebraicGeometry.IsAffine ((toScheme B S hS).obj W) ∧
      (∀ i, a i ≫ h = 𝒱.f i) ∧
      Sieve.ofArrows 𝒱.X a ∈ topology B S hS W ∧
      (∀ i, Mono (a i)) ∧
      (∀ ⦃Z : SmallEtale B S hS⦄ ⦃i j : 𝒱.I₀⦄ (gi : Z ⟶ 𝒱.X i) (gj : Z ⟶ 𝒱.X j), i ≠ j →
        gi ≫ a i = gj ≫ a j → (⊥ : Sieve Z) ∈ topology B S hS Z) ∧
      ∀ p : ℕ, 0 < p → IsZero (Stacks.CechSite.cechCohomology 𝒱
        ((associatedModule B S hS).obj F).val.presheaf p) := by
  obtain ⟨𝒱, W, h, a, h𝒱, hR𝒱, hWaff, hfac, hcov, hmono, hdisj⟩ :=
    exists_affine_sigma_refinement B S hS T hT hR
  exact ⟨𝒱, W, h, a, hR𝒱, hWaff, hfac, hcov, hmono, hdisj,
    fun p hp ↦ isZero_cechCohomology_succ_associatedModule B S hS F 𝒱 h𝒱 p hp⟩

end AlgebraicGeometry.SmallEtale

end
