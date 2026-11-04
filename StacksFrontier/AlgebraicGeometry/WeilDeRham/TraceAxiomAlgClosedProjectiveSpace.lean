module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.NontrivialPoint
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.ProjectiveSpacePointClassChernCharacter

/-!
# Projective space as a smooth projective scheme over `k`

This file makes `ℙ^d_k` an object of the category of smooth projective schemes over `k`, in the
polynomial model `Proj k[T₀, …, T_d]` over
`Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff`, and identifies it with the projective
bundle `𝐏(𝒪^{d+1})` over `Spec(k)` of axiom (A3), along Tag 01OE.

## Main definitions

* `Stacks.WeilDeRham.projectiveSpaceModule`: the free module `𝒪^{d+1}` on `Spec(k)`.
* `Stacks.WeilDeRham.projectiveSpaceBundleIso`: `𝐏(𝒪^{d+1}) ≅ Proj k[T₀, …, T_d]`, over `k`
  (`Stacks.WeilDeRham.projectiveSpaceBundleIso_hom_projToSpecCoeff`).
* `Stacks.WeilDeRham.projectiveSpace`: `ℙ^d_k = Proj k[T₀, …, T_d]` as a smooth projective scheme
  over `k`.
* `Stacks.WeilDeRham.projectiveSpaceTwistClass`: the class of `𝒪(1)` in `K₀(Vect(ℙ^d_k))`.

## References

* [Stacks Project, Tag 0FWD](https://stacks.math.columbia.edu/tag/0FWD)
* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme Stacks.SymGraded
open Stacks.AlgebraicGeometry.ProjPolyChart

universe u

namespace Stacks.WeilDeRham

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] (d : ℕ)

/-- The free module `𝒪^{d+1}` on `Spec(k)`. -/
abbrev projectiveSpaceModule : ((toScheme k).obj (point k)).Modules :=
  freeModule (X := Spec (.of k)) (coordIndex.{u} d)

/-- The free module `𝒪^{d+1}` is finite locally free of rank `d + 1`. -/
instance isFiniteLocallyFreeOfRank_projectiveSpaceModule :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (projectiveSpaceModule k d) (d + 1) :=
  AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_free_of_equiv _ (d + 1) Equiv.ulift

/-- **`𝐏(𝒪^{d+1}) ≅ Proj k[T₀, …, T_d]`**, the isomorphism of Tag 01OE between the projective
bundle of the free module and `ℙ^d_{Spec k}`, in the polynomial model. -/
def projectiveSpaceBundleIso : (toScheme k).obj (bundle (point k) (projectiveSpaceModule k d) d) ≅
    AlgebraicGeometry.Proj (polyGrading k d) :=
  projectiveBundleIsoProjectiveSpace (X := Spec (.of k)) d ≪≫
    (Stacks.ProjectiveCohomology.projModelIso k d).symm

/-- The identification `𝐏(𝒪^{d+1}) ≅ Proj k[T₀, …, T_d]` is one over `k`. -/
theorem projectiveSpaceBundleIso_hom_projToSpecCoeff :
    (projectiveSpaceBundleIso k d).hom ≫ projToSpecCoeff k d =
      (bundle (point k) (projectiveSpaceModule k d) d).obj.hom := by
  rw [Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.projToSpecCoeff_eq_projModelToSpec]
  have h1 : (Stacks.ProjectiveCohomology.projModelIso k d).inv ≫
      Stacks.ProjectiveCohomology.projModelToSpec k d = pullback.fst _ _ :=
    (Iso.inv_comp_eq _).mpr
      (Stacks.ProjectiveCohomology.projModelIso_hom_structureMorphism k d).symm
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h1).trans
    (projectiveBundleIsoProjectiveSpace_hom_comp_fst (X := Spec (.of k)) d))

/-- `Proj k[T₀, …, T_d] ⟶ Spec(k)` is projective. -/
theorem isProjective_projToSpecCoeff : IsProjective (projToSpecCoeff k d) := by
  have h := IsProjective.comp_iso (projectiveSpaceBundleIso k d).symm
    (isProjective (bundle (point k) (projectiveSpaceModule k d) d))
  rwa [Iso.symm_hom, ← projectiveSpaceBundleIso_hom_projToSpecCoeff, Iso.inv_hom_id_assoc] at h

/-- **`ℙ^d_k = Proj k[T₀, …, T_d]` as a smooth projective scheme over `k`.** -/
def projectiveSpace : (SmoothProjectiveScheme k).FullSubcategory :=
  mk (projToSpecCoeff k d)
    (haveI := smoothOfRelativeDimension_projToSpecCoeff k d
     SmoothOfRelativeDimension.smooth d _)
    (isProjective_projToSpecCoeff k d)

/-- `ℙ^d_k` is equidimensional of dimension `d`: its structure morphism has relative dimension
`d`. -/
theorem relativeDimension_projectiveSpace : RelativeDimension (projectiveSpace k d).obj.hom d :=
  relativeDimension_projToSpecCoeff k d

/-- `𝐏(𝒪^{d+1}) ≅ ℙ^d_k` in the category of smooth projective schemes. -/
def projectiveSpaceBundleHom :
    bundle (point k) (projectiveSpaceModule k d) d ⟶ projectiveSpace k d :=
  homMk (projectiveSpaceBundleIso k d).hom (projectiveSpaceBundleIso_hom_projToSpecCoeff k d)

/-- The inverse of `Stacks.WeilDeRham.projectiveSpaceBundleHom`. -/
def projectiveSpaceBundleInv :
    projectiveSpace k d ⟶ bundle (point k) (projectiveSpaceModule k d) d :=
  homMk (projectiveSpaceBundleIso k d).inv
    ((Iso.inv_comp_eq _).2 (projectiveSpaceBundleIso_hom_projToSpecCoeff k d).symm)

/-- `Stacks.WeilDeRham.projectiveSpaceBundleInv` is a left inverse of
`Stacks.WeilDeRham.projectiveSpaceBundleHom`. -/
@[simp]
theorem projectiveSpaceBundleHom_inv :
    projectiveSpaceBundleHom k d ≫ projectiveSpaceBundleInv k d = 𝟙 _ :=
  hom_ext' (projectiveSpaceBundleIso k d).hom_inv_id

/-- `Stacks.WeilDeRham.projectiveSpaceBundleInv` is a right inverse of
`Stacks.WeilDeRham.projectiveSpaceBundleHom`. -/
@[simp]
theorem projectiveSpaceBundleInv_hom :
    projectiveSpaceBundleInv k d ≫ projectiveSpaceBundleHom k d = 𝟙 _ :=
  hom_ext' (projectiveSpaceBundleIso k d).inv_hom_id

/-- **The class of `𝒪(1)` in `K₀(Vect(ℙ^d_k))`**, `𝒪(1)` the Serre twist of the polynomial
model. -/
def projectiveSpaceTwistClass : VectorBundleKZero ((toScheme k).obj (projectiveSpace k d)) :=
  haveI := Stacks.Chow.isFiniteLocallyFreeOfRank_one_of_isInvertible
    (X := AlgebraicGeometry.Proj (polyGrading k d))
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k d) 1)
  haveI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    (R := (AlgebraicGeometry.Proj (polyGrading k d)).ringCatSheaf)
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k d) 1) 1
  VectorBundleKZero.classOf _ (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k d) 1)

end Stacks.WeilDeRham

end
