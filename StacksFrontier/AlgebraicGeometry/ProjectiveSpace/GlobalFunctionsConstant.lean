module

public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.GlobalFunctions
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.KoszulRegularSmoothCover

/-!
# A morphism from projective space to an affine scheme is constant

The global functions on `ℙⁿ_R` are the coefficients: the structure morphism `ℙⁿ_R ⟶ Spec R`
induces an isomorphism `R ≅ Γ(ℙⁿ_R, 𝒪)`.  For the polynomial model `Proj R[T₀, …, Tₙ]` this is
`Stacks.ProjectiveSpace.Cohomology.bijective_coeffToGlobalSections`; this file carries it over
to the library's base-change model `AlgebraicGeometry.projectiveSpaceOverRing` along the
coordinate-pinned comparison, which commutes with the structure morphism by construction.

The consequence is the geometric input of every rigidity argument: a morphism from `ℙⁿ_R` to an
affine scheme factors through `Spec R`, that is, it is *constant* along the fibres of
`ℙⁿ_R ⟶ Spec R`.  A morphism to an affine scheme is the same thing as a ring homomorphism into
the global functions, and those are just `R`.

## Main results

* `AlgebraicGeometry.isIso_ΓSpecIso_inv_comp_appTop_projectiveSpaceOverRing`: **`Γ(ℙⁿ_R) = R`**
  for the base-change model.
* `AlgebraicGeometry.exists_comp_eq_of_isIso_ΓSpecIso_inv_comp_appTop`: a morphism to an affine
  scheme out of a scheme whose global functions are `R` through `p : X ⟶ Spec R` factors
  through `p`.
* `AlgebraicGeometry.exists_comp_eq_Spec_map_of_projectiveSpaceOverRing`: **a morphism from
  `ℙⁿ_R` to an affine scheme is constant.**

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- An isomorphism of schemes is an isomorphism on global functions: the global functions of the
inverse are a two-sided inverse. -/
private alias isIso_appTop_of_isIso' := Stacks.AlgebraicGeometry.isIso_appTop_of_isIso

/-- **The global functions on projective space over a ring are the coefficients.** The
structure morphism of the base-change model `ℙⁿ_R` induces an isomorphism `R ≅ Γ(ℙⁿ_R, 𝒪)`.

The coordinate-pinned comparison identifies the base-change model with the polynomial model
`Proj R[T₀, …, Tₙ]` compatibly with the structure morphisms, and on the polynomial model the
statement is Serre's computation of `H⁰(ℙⁿ_R, 𝒪)`. -/
theorem isIso_ΓSpecIso_inv_comp_appTop_projectiveSpaceOverRing (R : Type u) [CommRing R]
    (n : ℕ) :
    IsIso ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (projectiveSpaceOverRing n (CommRingCat.of R) ↘ Spec (CommRingCat.of R)).appTop) := by
  let C := Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison R n
  have hbase : C.iso.hom ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff R n =
      projectiveSpaceOverRing n (CommRingCat.of R) ↘ Spec (CommRingCat.of R) := C.toBase
  have hiso : IsIso C.iso.hom.appTop := isIso_appTop_of_isIso' C.iso.hom
  have hcoeff : IsIso ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff R n).appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (Stacks.ProjectiveSpace.Cohomology.bijective_coeffToGlobalSections R n)
  rw [← hbase, Scheme.Hom.comp_appTop, ← Category.assoc]
  infer_instance

/-- A morphism to an affine scheme is the ring homomorphism it induces on global functions. -/
private theorem eq_toSpecΓ_comp_Spec_map {X : Scheme.{u}} {A : CommRingCat.{u}}
    (u : X ⟶ Spec A) :
    u = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso A).inv ≫ u.appTop) :=
  calc u = u ≫ (Spec A).toSpecΓ ≫ Spec.map (Scheme.ΓSpecIso A).inv := by
        rw [toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    _ = (u ≫ (Spec A).toSpecΓ) ≫ Spec.map (Scheme.ΓSpecIso A).inv :=
        (Category.assoc _ _ _).symm
    _ = (X.toSpecΓ ≫ Spec.map u.appTop) ≫ Spec.map (Scheme.ΓSpecIso A).inv := by
        rw [Scheme.toSpecΓ_naturality]
    _ = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso A).inv ≫ u.appTop) := by
        rw [Spec.map_comp, Category.assoc]

/-- **Constancy from the global functions.** Let `p : X ⟶ Spec R` induce an isomorphism
`R ≅ Γ(X, 𝒪)`.  Then every morphism from `X` to an affine scheme factors through `p`, by a ring
homomorphism into `R`.

A morphism `X ⟶ Spec A` is the same thing as a ring homomorphism `A ⟶ Γ(X, 𝒪)`, and `p`
identifies `Γ(X, 𝒪)` with `R`. -/
theorem exists_comp_eq_of_isIso_ΓSpecIso_inv_comp_appTop {X : Scheme.{u}} {R : CommRingCat.{u}}
    (p : X ⟶ Spec R) (hp : IsIso ((Scheme.ΓSpecIso R).inv ≫ p.appTop))
    {A : CommRingCat.{u}} (u : X ⟶ Spec A) :
    ∃ ψ : A ⟶ R, u = p ≫ Spec.map ψ := by
  set α := (Scheme.ΓSpecIso R).inv ≫ p.appTop with hα
  set β := (Scheme.ΓSpecIso A).inv ≫ u.appTop with hβ
  refine ⟨β ≫ inv α, ?_⟩
  calc u = X.toSpecΓ ≫ Spec.map β := eq_toSpecΓ_comp_Spec_map u
    _ = (X.toSpecΓ ≫ Spec.map α) ≫ Spec.map (inv α) ≫ Spec.map β := by
        rw [Category.assoc, ← Category.assoc (Spec.map α), ← Spec.map_comp, IsIso.inv_hom_id,
          Spec.map_id, Category.id_comp]
    _ = p ≫ Spec.map (β ≫ inv α) := by
        rw [Spec.map_comp β (inv α), ← eq_toSpecΓ_comp_Spec_map p]

/-- **A morphism from projective space over a ring to an affine scheme is constant**: it
factors through the structure morphism `ℙⁿ_R ⟶ Spec R`.

This is the geometric input of a rigidity argument: a complete fibre has no nonconstant
functions, so it cannot map nontrivially to anything affine. -/
theorem exists_comp_eq_Spec_map_of_projectiveSpaceOverRing (R : Type u) [CommRing R] (n : ℕ)
    {A : CommRingCat.{u}} (u : projectiveSpaceOverRing n (CommRingCat.of R) ⟶ Spec A) :
    ∃ ψ : A ⟶ CommRingCat.of R,
      u = (projectiveSpaceOverRing n (CommRingCat.of R) ↘ Spec (CommRingCat.of R)) ≫
        Spec.map ψ :=
  exists_comp_eq_of_isIso_ΓSpecIso_inv_comp_appTop _
    (isIso_ΓSpecIso_inv_comp_appTop_projectiveSpaceOverRing R n) u

end AlgebraicGeometry

end
