module

public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv

/-!
# Two-step lifts and direct lifts in a category fibred in groupoids

Let `p : 𝒮 ⥤ 𝒞` be a category fibred in groupoids (Stacks 003S) and let `g : W ⟶ V` and
`f : V ⟶ U` be morphisms of `𝒞`. Given `x` over `U`, one may lift `f` to `φ : y ⟶ x` and then
lift `g` to `ψ : z ⟶ y`, or lift the composite `g ∘ f` directly to `γ : z' ⟶ x`. The diagram of
Stacks 03WP compares the two: the second condition of Stacks 003T, applied to the two lifts
`ψ ∘ φ` and `γ` of `g ∘ f` and to `id_W`, produces a unique `χ : z ⟶ z'` in the fibre `𝒮_W` with
`γ ∘ χ = φ ∘ ψ`, and uniqueness forces `χ` to be an isomorphism.

## Main results

* `CategoryTheory.Functor.IsFiberedInGroupoids.existsUnique_vertical_factorisation`, Stacks 03WP:
  the dotted arrow `χ : z ⟶ z'` exists and is unique;
* `CategoryTheory.Functor.IsFiberedInGroupoids.twoStepLiftIso`, Stacks 03WP: it is an isomorphism,
  produced here as the canonical isomorphism `z ≅ z'` between the domains of two cartesian lifts
  of one morphism;
* `CategoryTheory.Functor.IsFiberedInGroupoids.isIso_of_vertical_comp_eq`, Stacks 03WP: *every*
  vertical `χ` filling the diagram is an isomorphism, which by uniqueness is the same statement.

## Implementation notes

In a category fibred in groupoids every lift is strongly cartesian
(`CategoryTheory.Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift`, Stacks 003V), so both
`ψ ∘ φ` and `γ` are cartesian lifts of `g ∘ f` with target `x`, and the source's conclusions are
the universal property of `γ` (`CategoryTheory.Functor.IsStronglyCartesian.universal_property`)
and the canonical comparison of two cartesian lifts
(`CategoryTheory.Functor.IsCartesian.domainUniqueUpToIso`).
-/

@[expose] public section

namespace CategoryTheory.Functor.IsFiberedInGroupoids

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮] {p : 𝒮 ⥤ 𝒞}
  (hp : p.IsFiberedInGroupoids) {W V U : 𝒞} (g : W ⟶ V) (f : V ⟶ U) {x y z z' : 𝒮}
  (φ : y ⟶ x) (ψ : z ⟶ y) (γ : z' ⟶ x)
  [hφ : p.IsHomLift f φ] [hψ : p.IsHomLift g ψ] [hγ : p.IsHomLift (g ≫ f) γ]

include hp hφ hψ hγ

/-- **Stacks 03WP.**
The two-step lift `ψ ∘ φ : z ⟶ x` of `g ∘ f` factors through the direct lift `γ : z' ⟶ x` by a
unique morphism `χ : z ⟶ z'` of the fibre over `W`, i.e. a unique `χ` lying over `id_W`. -/
@[stacks 03WP]
theorem existsUnique_vertical_factorisation :
    ∃! χ : z ⟶ z', p.IsHomLift (𝟙 W) χ ∧ χ ≫ γ = ψ ≫ φ :=
  have := hp.isStronglyCartesian_homLift (g ≫ f) γ
  IsStronglyCartesian.universal_property p (g ≫ f) γ (𝟙 W) (g ≫ f) (by simp) (ψ ≫ φ)

/-- **Stacks 03WP.**
The comparison isomorphism `z ≅ z'` between the domain of the two-step lift of `g ∘ f` and the
domain of a direct lift of `g ∘ f`. Both lifts are cartesian, so this is the canonical
isomorphism between the domains of two cartesian lifts of one morphism of the base. -/
@[stacks 03WP]
noncomputable def twoStepLiftIso : z ≅ z' :=
  have : p.IsStronglyCartesian (g ≫ f) γ := hp.isStronglyCartesian_homLift (g ≫ f) γ
  have : p.IsStronglyCartesian (g ≫ f) (ψ ≫ φ) := hp.isStronglyCartesian_homLift (g ≫ f) (ψ ≫ φ)
  IsCartesian.domainUniqueUpToIso p (g ≫ f) γ (ψ ≫ φ)

/-- The comparison isomorphism lies over `id_W`, i.e. it is a morphism of the fibre `𝒮_W`. -/
lemma isHomLift_twoStepLiftIso_hom : p.IsHomLift (𝟙 W) (hp.twoStepLiftIso g f φ ψ γ).hom :=
  have := hp.isStronglyCartesian_homLift (g ≫ f) γ
  have : p.IsStronglyCartesian (g ≫ f) (ψ ≫ φ) := hp.isStronglyCartesian_homLift (g ≫ f) (ψ ≫ φ)
  IsCartesian.domainUniqueUpToIso_inv_isHomLift p (g ≫ f) γ (ψ ≫ φ)

/-- The comparison isomorphism fills the diagram of Stacks 03WP: `γ ∘ χ = φ ∘ ψ`. -/
@[reassoc]
lemma twoStepLiftIso_hom_comp : (hp.twoStepLiftIso g f φ ψ γ).hom ≫ γ = ψ ≫ φ :=
  have := hp.isStronglyCartesian_homLift (g ≫ f) γ
  IsCartesian.fac p (g ≫ f) γ (ψ ≫ φ)

/-- **Stacks 03WP.**
Every morphism `χ : z ⟶ z'` of the fibre over `W` filling the diagram is an isomorphism: by
uniqueness it is the comparison isomorphism `CategoryTheory.Functor.twoStepLiftIso`. -/
@[stacks 03WP]
lemma isIso_of_vertical_comp_eq (χ : z ⟶ z') [p.IsHomLift (𝟙 W) χ] (hχ : χ ≫ γ = ψ ≫ φ) :
    IsIso χ :=
  have := hp.isStronglyCartesian_homLift (g ≫ f) γ
  have : χ = (hp.twoStepLiftIso g f φ ψ γ).hom :=
    IsCartesian.map_uniq p (g ≫ f) γ (ψ ≫ φ) χ hχ
  this ▸ (hp.twoStepLiftIso g f φ ψ γ).isIso_hom

end CategoryTheory.Functor.IsFiberedInGroupoids
