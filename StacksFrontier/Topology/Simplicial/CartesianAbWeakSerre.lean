module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianWeakSerre
public import StacksFrontier.Topology.Sheaves.Spectral.ConstructibleSheaves
public import StacksFrontier.Topology.Simplicial.ComponentSite
public import StacksFrontier.Topology.Simplicial.ProperHypercovering.QcTotalSite
public import StacksFrontier.Topology.Simplicial.ProperHypercoveringDescent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cartesian abelian sheaves on a simplicial space form a weak Serre subcategory

Let `Z` be a simplicial topological space and `Z_Zar` its site of simplicial opens. An abelian
sheaf `G` on `Z_Zar` is cartesian (`Stacks.Topology.Simplicial.ProperHypercovering.IsCartesianAb`)
when for every `φ : [m] ⟶ [n]` the canonical map `Z(φ)⁻¹G_n ⟶ G_m` of its underlying sheaves of
sets is an isomorphism. This file proves **Stacks 0D7J (1)** for `Z_Zar`: the cartesian abelian
sheaves form a weak Serre subcategory of `Ab(Z_Zar)`. This is the weak Serre subcategory `𝒜` of
Stacks 0DAH.

## The argument

The comparison maps are the components of a natural transformation between two inverse image
functors of morphisms of topoi `Sh(Z_m) ⟶ Sh(Z_Zar)`: restriction to degree `n` followed by
`Z(φ)⁻¹`, and restriction to degree `m`. On abelian sheaves the inverse image of a morphism of
topoi is the functor induced on commutative group objects, so a natural transformation `η`
between inverse images induces one between the abelian inverse images, whose underlying maps of
sheaves of sets are those of `η` (`CategoryTheory.Sites.abelianInverseImageNatTrans`). The
abelian inverse images are exact (Stacks 04JC), so the four lemma shows that the objects at
which such a transformation is invertible on underlying sheaves of sets form a weak Serre
subcategory (`CategoryTheory.Sites.isWeakSerreClass_isIso_app_forget`), and so do intersections of
weak Serre subcategories (`CategoryTheory.ObjectProperty.isWeakSerreClass_forall`).

## Main results

* `CategoryTheory.Sites.abelianInverseImageNatTrans` and
  `.sheafCompose_forget_map_abelianInverseImageNatTrans_app`: the abelian reading of a natural
  transformation between inverse images.
* `CategoryTheory.Sites.isWeakSerreClass_isIso_app_forget`: the weak Serre property of the locus
  where such a transformation is invertible.
* `CategoryTheory.ObjectProperty.isWeakSerreClass_forall`: intersections of weak Serre
  subcategories.
* `Stacks.Topology.Simplicial.ProperHypercovering.isCartesianAb_isWeakSerreClass`:
  **Stacks 0D7J (1)** for the site of a simplicial space.

## References

* [Stacks Project, Tag 0D7J](https://stacks.math.columbia.edu/tag/0D7J)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 0DAH](https://stacks.math.columbia.edu/tag/0DAH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped ZeroObject

universe w w' v v' u u'

namespace CategoryTheory.ObjectProperty

/-- **An intersection of weak Serre subcategories is a weak Serre subcategory.** -/
theorem isWeakSerreClass_forall {𝒞 : Type u} [Category.{v} 𝒞] [Abelian 𝒞] {ι : Type*}
    (P : ι → ObjectProperty 𝒞) [∀ i, (P i).IsWeakSerreClass] :
    ObjectProperty.IsWeakSerreClass (fun X ↦ ∀ i, P i X) := by
  refine (isWeakSerreClass_iff_prop_obj₂_of_exact _).2 ⟨⟨0, fun i ↦ ?_⟩,
    fun S hS h₀ h₁ h₃ h₄ i ↦ (P i).prop_obj₂_of_exact S hS (h₀ i) (h₁ i) (h₃ i) (h₄ i)⟩
  obtain ⟨Z, hZ, hPZ⟩ := (P i).exists_prop_of_containsZero
  exact (P i).prop_of_iso (hZ.iso (isZero_zero 𝒞)) hPZ

end CategoryTheory.ObjectProperty

namespace CategoryTheory.Sites

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- The cartesian monoidal structure on sheaves of sets given by finite products. -/
noncomputable local instance : CartesianMonoidalCategory (Sheaf J (Type w)) :=
  .ofHasFiniteProducts
/-- The braiding of the cartesian monoidal structure on sheaves of sets. -/
noncomputable local instance : BraidedCategory (Sheaf J (Type w)) :=
  .ofCartesianMonoidalCategory

section NatTrans

variable (f g : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))

/-- The inverse image of a morphism of topoi preserves finite limits. -/
noncomputable local instance (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w'))) :
    PreservesFiniteLimits f.inverseImage :=
  f.preservesFiniteLimits
/-- The inverse image of a morphism of topoi is a braided functor for the cartesian monoidal
structures. -/
noncomputable local instance (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w'))) :
    f.inverseImage.Braided := .ofChosenFiniteProducts _

/-- The abelian reading of a natural transformation between the inverse images of two morphisms
of topoi: the transformation induced on commutative group objects, read on abelian sheaves. -/
noncomputable def abelianInverseImageNatTrans (η : f.inverseImage ⟶ g.inverseImage) :
    abelianInverseImage f ⟶ abelianInverseImage g :=
  Functor.whiskerLeft (AbelianSheaf.internalSheaf K)
    (Functor.whiskerRight (Functor.mapCommGrpNatTrans η) (AbelianSheaf.externalSheaf J))

/-- Forgetting the group operations turns the abelian reading of `η` back into `η`. -/
theorem sheafCompose_forget_map_abelianInverseImageNatTrans_app
    (η : f.inverseImage ⟶ g.inverseImage) (F : Sheaf K AddCommGrpCat.{w'}) :
    (sheafCompose J (forget AddCommGrpCat.{w})).map
        ((abelianInverseImageNatTrans f g η).app F) =
      η.app ((sheafCompose K (forget AddCommGrpCat.{w'})).obj F) :=
  rfl

end NatTrans

variable [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w'}]

/-- **The locus where a transformation between inverse images is invertible is a weak Serre
subcategory.** Let `f, g` be morphisms of topoi with common source and target and
`η : f⁻¹ ⟶ g⁻¹`. The abelian sheaves `F` on the target such that `η` is invertible at the
underlying sheaf of sets of `F` form a weak Serre subcategory: the abelian reading of `η`
compares two exact functors (Stacks 04JC), and the four lemma applies. -/
theorem isWeakSerreClass_isIso_app_forget
    (f g : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
    (η : f.inverseImage ⟶ g.inverseImage) :
    ObjectProperty.IsWeakSerreClass (fun F : Sheaf K AddCommGrpCat.{w'} ↦
      IsIso (η.app ((sheafCompose K (forget AddCommGrpCat.{w'})).obj F))) := by
  have key : ∀ F : Sheaf K AddCommGrpCat.{w'},
      IsIso (η.app ((sheafCompose K (forget AddCommGrpCat.{w'})).obj F)) ↔
        IsIso ((abelianInverseImageNatTrans f g η).app F) := fun F ↦ by
    rw [← sheafCompose_forget_map_abelianInverseImageNatTrans_app]
    exact isIso_iff_of_reflects_iso _ (sheafCompose J (forget AddCommGrpCat.{w}))
  refine (ObjectProperty.isWeakSerreClass_iff_prop_obj₂_of_exact _).2 ⟨⟨0, ?_⟩, ?_⟩
  · rw [key]
    exact IsZero.isIso (Functor.map_isZero _ (isZero_zero _))
      (Functor.map_isZero _ (isZero_zero _)) _
  · intro T hT h₀ h₁ h₃ h₄
    rw [key] at h₀ h₁ h₃ h₄ ⊢
    exact SimplicialSiteSituation.isIso_app_obj'_two_of_exact _ _
      (abelianInverseImageNatTrans f g η) T hT inferInstance h₁ h₃ inferInstance

end CategoryTheory.Sites

namespace Stacks.Topology.Simplicial.ProperHypercovering

open Stacks.Topology Stacks.Topology.Simplicial Stacks.Topology.Simplicial.Augmentation

variable (Z : SimplicialObject TopCat.{u})

/-- The morphism of topoi `Sh(A) ⟶ Sh(B)` of a continuous map `f : A ⟶ B`: inverse image and
direct image of sheaves of sets. -/
@[sga "4 IV 4.1.1"]
def continuousMapTopoi {A B : TopCat.{u}} (f : A ⟶ B) : MorphismOfTopoi (sh A) (sh B) where
  pushforward := pf f
  inverseImage := pb f
  adj := adj f
  preservesFiniteLimits := Stacks.pullbackPreservesFiniteLimits f

/-- Restriction of sheaves of sets on `Z_Zar` to the opens of `Z_n` is the degree-`n` component
of the sheaf-system description of Stacks 09VM. -/
def componentSheafFunctorIso (n : SimplexCategoryᵒᵖ) :
    componentSheafFunctor Z (Type u) n ≅
      (sheafEquivalenceSimplicialSheafSystem Z (Type u)).toEquivalence.functor ⋙
        SimplicialSheafSystem.componentFunctor Z (Type u) n :=
  have := levelFunctor_isContinuous Z n
  have := levelFunctor_isCocontinuous Z n
  ((levelFunctor Z n).sheafPullbackCocontinuousIsoSheafPushforwardContinuous (Type u)
      (Opens.grothendieckTopology (Z.obj n)) (SimplicialOpen.grothendieckTopology Z)).symm ≪≫
    inverseImageIsoComponent Z n.unop.len

/-- The morphism of topoi `Sh(Z_n) ⟶ Sh(Z_Zar)` of the inclusion of the opens of `Z_n` into the
site of simplicial opens. Its inverse image is restriction to degree `n`, read as the
degree-`n` component of the sheaf-system description. -/
def componentTopoi (n : SimplexCategoryᵒᵖ) :
    MorphismOfTopoi (sh (Z.obj n)) (Sheaf (SimplicialOpen.grothendieckTopology Z) (Type u)) :=
  have := levelFunctor_isContinuous Z n
  have := levelFunctor_isCocontinuous Z n
  { inverseImage := (sheafEquivalenceSimplicialSheafSystem Z (Type u)).toEquivalence.functor ⋙
      SimplicialSheafSystem.componentFunctor Z (Type u) n
    pushforward := (levelFunctor Z n).sheafPushforwardCocontinuous (Type u) _ _
    adj := ((levelFunctor Z n).sheafAdjunctionCocontinuous (Type u) _ _).ofNatIsoLeft
      (componentSheafFunctorIso Z n)
    preservesFiniteLimits := by
      have : PreservesFiniteLimits (componentSheafFunctor Z (Type u) n) :=
        LocallyQuasiCompactZariskiSituation.preservesFiniteLimits_sheafPushforwardContinuous_type
          (levelFunctor Z n) (Opens.grothendieckTopology (Z.obj n))
          (SimplicialOpen.grothendieckTopology Z)
      exact preservesFiniteLimits_of_natIso (componentSheafFunctorIso Z n) }

/-- For `φ : n ⟶ m` in `Δᵒᵖ`, the canonical inverse-image transitions `Z(φ)⁻¹G_m ⟶ G_n` of the
sheaves of sets `G` on `Z_Zar`, as a natural transformation between the inverse images of the
morphisms of topoi `Sh(Z_n) ⟶ Sh(Z_m) ⟶ Sh(Z_Zar)` and `Sh(Z_n) ⟶ Sh(Z_Zar)`. -/
def cartesianTransitionNatTrans {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    ((componentTopoi Z m).comp (continuousMapTopoi (Z.map φ))).inverseImage ⟶
      (componentTopoi Z n).inverseImage where
  app G := cartesianTransition Z G φ
  naturality _ _ f :=
    systemCartesianTransition_naturality Z
      ((sheafEquivalenceSimplicialSheafSystem Z (Type u)).toEquivalence.functor.map f) φ

/-- **Stacks 0D7J (1) for the site of a simplicial space.** The cartesian abelian sheaves on
`Z_Zar` form a weak Serre subcategory of `Ab(Z_Zar)`. -/
instance isCartesianAb_isWeakSerreClass : ObjectProperty.IsWeakSerreClass (IsCartesianAb Z) := by
  have h := @ObjectProperty.isWeakSerreClass_forall _ _ _ (Σ n m : SimplexCategoryᵒᵖ, n ⟶ m)
    (fun i G ↦ IsIso ((cartesianTransitionNatTrans Z i.2.2).app
      ((sheafCompose _ (forget AddCommGrpCat.{u})).obj G)))
    (fun i ↦ CategoryTheory.Sites.isWeakSerreClass_isIso_app_forget
      ((componentTopoi Z i.2.1).comp (continuousMapTopoi (Z.map i.2.2))) (componentTopoi Z i.1)
      (cartesianTransitionNatTrans Z i.2.2))
  convert h using 2 with G
  exact ⟨fun hG i ↦ hG i.2.2, fun hG n m φ ↦ hG ⟨n, m, φ⟩⟩

end Stacks.Topology.Simplicial.ProperHypercovering

end
