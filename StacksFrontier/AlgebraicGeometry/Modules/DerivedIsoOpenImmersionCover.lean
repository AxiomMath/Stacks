module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange
public import StacksFrontier.Homology.PseudoCoherent.Locality

/-!
# Invertibility in `D(𝒪_Y)` is local for open immersions

Let `Y` be a scheme and `jᵢ : Yᵢ ⟶ Y` a family of open immersions whose images cover `Y`. A
morphism `φ` of `D(𝒪_Y)` is an isomorphism as soon as each derived pullback `Ljᵢ^*φ` is. The same
holds for a morphism of sheaves of `𝒪_Y`-modules and its restrictions along the `jᵢ`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_restrict_openImmersion`: the statement for
  sheaves of modules.
* `AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_derivedPullback_openImmersion`: the statement
  in `D(𝒪_Y)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **Invertibility of a morphism of sheaves of modules is local for open immersions.** If the
images of the open immersions `jᵢ : Yᵢ ⟶ Y` cover `Y` and the restriction of `φ` along each `jᵢ`
is invertible, then `φ` is invertible. -/
theorem isIso_of_isIso_restrict_openImmersion {Y : Scheme.{u}} {M N : Y.Modules} (φ : M ⟶ N)
    {I : Type*} {Z : I → Scheme.{u}} (j : ∀ i, Z i ⟶ Y) [∀ i, IsOpenImmersion (j i)]
    (hj : ∀ y : Y, ∃ i, y ∈ Set.range (j i).base)
    (h : ∀ i, IsIso ((restrictFunctor (j i)).map φ)) : IsIso φ := by
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_stalk φ fun y => ?_
  obtain ⟨i, z, rfl⟩ := hj y
  have : IsIso ((restrictFunctor (j i)).map φ) := h i
  have h₃ : IsIso ((restrictFunctor (j i) ⋙ toPresheaf _ ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} z).map φ) :=
    Functor.map_isIso (toPresheaf _ ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} z) _
  have h₂ : IsIso ((restrictStalkNatIso (j i) z).hom.app M ≫
      (toPresheaf Y ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} ((j i).base z)).map φ) := by
    rw [← (restrictStalkNatIso (j i) z).hom.naturality φ]
    infer_instance
  exact IsIso.of_isIso_comp_left ((restrictStalkNatIso (j i) z).hom.app M)
    ((toPresheaf Y ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} ((j i).base z)).map φ)

section Derived

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Invertibility in `D(𝒪_Y)` is local for open immersions.** If the images of the open
immersions `jᵢ : Yᵢ ⟶ Y` cover `Y` and the derived pullback of `φ` along each `jᵢ` is invertible,
then `φ` is invertible. -/
theorem isIso_of_isIso_derivedPullback_openImmersion {Y : Scheme.{u}}
    {A B : DerivedCategory Y.Modules} (φ : A ⟶ B)
    {I : Type*} {Z : I → Scheme.{u}} (j : ∀ i, Z i ⟶ Y) [∀ i, IsOpenImmersion (j i)]
    (hj : ∀ y : Y, ∃ i, y ∈ Set.range (j i).base)
    (h : ∀ i, IsIso ((derivedPullback (j i).toLRSHom.toShHom).map φ)) : IsIso φ := by
  rw [DerivedCategory.isIso_iff]
  intro n
  refine isIso_of_isIso_restrict_openImmersion _ j hj fun i => ?_
  have h₁ : IsIso ((restrictFunctor (j i)).mapDerivedCategory.map φ) :=
    (NatIso.isIso_map_iff (derivedRestrictIsoDerivedPullback (j i)) φ).2 (h i)
  have h₂ : IsIso ((DerivedCategory.homologyFunctor _ n).map
      ((restrictFunctor (j i)).mapDerivedCategory.map φ)) := inferInstance
  exact (NatIso.isIso_map_iff
    (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (restrictFunctor (j i)) n) φ).1 h₂

end Derived

end AlgebraicGeometry.Scheme.Modules

end
