module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedCoherator
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AlgebraExtensionEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FirstOrderAlgebraExtension

/-!
# The extension of a first order thickening, on a space isomorphic to the closed subspace

Let `Z ⊆ X` be a closed subspace which is a first order thickening, and `ρ : U ≅ Z` an
isomorphism of algebraic spaces. On the small étale site of `U` the inverse image `(ρ ≫ ι)⁻¹𝒪_X`
is a square-zero extension

`0 → 𝒞_{Z/X} → (ρ ≫ ι)⁻¹𝒪_X → 𝒪_U → 0`

of `𝒪_U` by the restricted conormal module. This file presents it as a
`Deformation.AlgebraExtension`: it is the extension `firstOrderAlgebraExtension` of `Z ⊆ X`,
restricted to `U` along `ρ`, and its middle term is identified with `(ρ ≫ ι)⁻¹𝒪_X` compatibly with
the reductions.

## Main definitions

* `AlgebraicGeometry.Space.restrictedConormalModule`: the conormal module of `Z ⊆ X` on `U`.
* `AlgebraicGeometry.Space.restrictedFirstOrderExtension`: the extension of
  `(ρ ≫ ι ≫ h)⁻¹𝒪_Y`-algebras of `𝒪_U` by it, for any `h : X ⟶ Y`.
* `AlgebraicGeometry.Space.restrictedFirstOrderExtensionIso`: its middle term is `(ρ ≫ ι)⁻¹𝒪_X`,
  compatibly with the reductions (`restrictedFirstOrderExtensionIso_hom_comp_reduction`).

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y U : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (hZ : IsFirstOrderThickening B S hS X Z.1)
  (ρ : U ≅ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) (h : X ⟶ Y)

/-- **The conormal module of a closed subspace `Z ⊆ X`, on `U ≅ Z`.** -/
abbrev restrictedConormalModule :
    SheafOfModules.{u} ((sheafCompose (SmallEtale.topology B S hS U.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (smallEtaleRingedTopos B S hS U).O) :=
  (etaleRestrictionModule B S hS ρ.hom (isEtale_hom_of_iso B S hS _)).obj
    (conormalModule B S hS X Z)

/-- **The extension `0 → 𝒞_{Z/X} → ι⁻¹𝒪_X → 𝒪_Z → 0` of a first order thickening, on `U ≅ Z`**,
as an extension of `(ρ ≫ ι ≫ h)⁻¹𝒪_Y`-algebras of `𝒪_U`, `ι : Z ⟶ X` the inclusion. -/
abbrev restrictedFirstOrderExtension :
    Deformation.AlgebraExtension (J := SmallEtale.topology B S hS U.1)
      (structureSharpInverseImage B S hS (ρ.hom ≫ subspaceInclusion B S hS X Z ≫ h))
      (restrictedConormalModule B S hS Z ρ) :=
  (etaleRestrictionFunctor B S hS ρ.hom (isEtale_hom_of_iso B S hS _) _ _).obj
    (firstOrderAlgebraExtension B S hS Z hZ h)

/-- Postcomposition with `U ≅ Z` is continuous for the small étale topologies of `U` and `Z`
(Stacks 03LP). -/
theorem restrictedFirstOrderExtension_isContinuous :
    (smallEtalePostcomp B S hS ρ.hom (isEtale_hom_of_iso B S hS _)).IsContinuous
      (SmallEtale.topology B S hS U.1)
      (SmallEtale.topology B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1) :=
  smallEtalePostcomp_isContinuous B S hS _ _

attribute [local instance] restrictedFirstOrderExtension_isContinuous

/-- The reduction of `restrictedFirstOrderExtension` is the restriction of the structure map of the
closed subspace, read through `ρ⁻¹𝒪_Z ≅ 𝒪_U`. -/
theorem restrictedFirstOrderExtension_reduction :
    (restrictedFirstOrderExtension B S hS Z hZ ρ h).reduction =
        (Deformation.AlgebraExtension.ringRes (SmallEtale.topology B S hS U.1)
          (J := SmallEtale.topology B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
          (smallEtalePostcomp B S hS ρ.hom (isEtale_hom_of_iso B S hS _))).map
          (structureSharpInverseImage B S hS (subspaceInclusion B S hS X Z)) ≫
        (etaleRestrictionRingComparison B S hS ρ.hom (isEtale_hom_of_iso B S hS _)
          (subspaceInclusion B S hS X Z)).ω.inv := by
  rfl

/-- **The middle term of the extension is `(ρ ≫ ι)⁻¹𝒪_X`** (Stacks 03G8): the restriction of
`ι⁻¹𝒪_X` along `U ≅ Z` is the inverse image along the composite. -/
def restrictedFirstOrderExtensionIso :
    inverseImageStructureSheaf B S hS (ρ.hom ≫ subspaceInclusion B S hS X Z) ≅
      (restrictedFirstOrderExtension B S hS Z hZ ρ h).extension :=
  (etaleRestrictionRingComparison B S hS ρ.hom (isEtale_hom_of_iso B S hS _)
    (subspaceInclusion B S hS X Z)).α

/-- The identification of `(ρ ≫ ι)⁻¹𝒪_X` with the middle term of the extension carries the
reduction of the extension to the structure map `(ρ ≫ ι)^♯`. -/
@[reassoc (attr := simp)]
theorem restrictedFirstOrderExtensionIso_hom_comp_reduction :
    (restrictedFirstOrderExtensionIso B S hS Z hZ ρ h).hom ≫
        (restrictedFirstOrderExtension B S hS Z hZ ρ h).reduction =
      structureSharpInverseImage B S hS (ρ.hom ≫ subspaceInclusion B S hS X Z) :=
  (Category.assoc _ _ _).symm.trans ((Iso.comp_inv_eq _).mpr
    (etaleRestrictionRingComparison B S hS ρ.hom (isEtale_hom_of_iso B S hS _)
      (subspaceInclusion B S hS X Z)).comm.symm)

end AlgebraicGeometry.Space

end
