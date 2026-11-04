module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Reduced
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.MeromorphicGenericPointDecomposition.Basic
public import StacksFrontier.AlgebraicGeometry.MeromorphicQuasicoherent.Product

/-!
# Restriction of a product of modules to an open subscheme

Restriction along an open immersion is objectwise, so it commutes with products of
`𝒪_X`-modules: the comparison map out of the restriction of a product is an isomorphism, because
on sections both sides are the families of sections of the factors over the image open.

A product may equally be taken over the subtype of those indices whose factors admit more than
one morphism into them: the factors discarded admit a unique morphism from any object, so the
projections to them carry no information.

Also recorded here: at a generic point `η` of an irreducible component the canonical morphism
`j_η : Spec 𝒪_{X, η} ⟶ X` is an affine morphism, the preimage of an open set being everything
when it contains `η` and empty otherwise.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The canonical morphism from the spectrum of the local ring at a generic point of an
irreducible component is an affine morphism: the preimage of an open set is everything if the
generic point lies in it, and empty otherwise. -/
instance isAffineHom_fromSpecStalk_of_mem_genericPoints (η : genericPoints X) :
    IsAffineHom (X.fromSpecStalk η.1) :=
  Stacks.AlgebraicGeometry.MeromorphicQuasicoherent.isAffineHom_fromSpecStalk η.2

/-! ### Restriction to an open commutes with products -/

/-- The comparison map from the restriction of a product to the product of the restrictions. -/
noncomputable def restrictPiComparison {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    {ι : Type u} (N : ι → X.Modules) :
    (∏ᶜ N).restrict f ⟶ ∏ᶜ fun i ↦ (N i).restrict f :=
  Pi.lift fun i ↦ (Scheme.Modules.restrictFunctor f).map (Pi.π N i)

/-- On sections over `U`, the `i`-th component of the image of a section `x` of the restricted
product under `restrictPiComparison` is the `i`-th component of `x`, viewed as a section of the
product over the image open `f ''ᵁ U`. -/
lemma modulesSectionsPiEquiv_restrictPiComparison {Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] {ι : Type u} (N : ι → X.Modules) (U : Y.Opens)
    (x : ToType ((modulesSectionsFunctor Y U).obj ((∏ᶜ N).restrict f))) (i : ι) :
    modulesSectionsPiEquiv (fun i ↦ (N i).restrict f) U
        (((restrictPiComparison f N).app U) x) i =
      modulesSectionsPiEquiv N (f ''ᵁ U) x i := by
  refine (modulesSectionsPiEquiv_apply _ _ _ i).trans ?_
  refine Eq.trans ?_ (modulesSectionsPiEquiv_apply N (f ''ᵁ U) x i).symm
  have h : (modulesSectionsFunctor Y U).map (restrictPiComparison f N) ≫
      (modulesSectionsFunctor Y U).map (Pi.π (fun i ↦ (N i).restrict f) i) =
      (modulesSectionsFunctor Y U).map
        ((Scheme.Modules.restrictFunctor f).map (Pi.π N i)) := by
    rw [← Functor.map_comp]
    exact congrArg (modulesSectionsFunctor Y U).map
      (Pi.lift_π (fun i ↦ (Scheme.Modules.restrictFunctor f).map (Pi.π N i)) i)
  exact ConcreteCategory.congr_hom h x

/-- Restriction to an open subscheme commutes with products: the comparison map is an
isomorphism, because on sections both sides are the families of sections of the factors over
the image open. -/
lemma isIso_restrictPiComparison {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    {ι : Type u} (N : ι → X.Modules) : IsIso (restrictPiComparison f N) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  set e := modulesSectionsPiEquiv (fun i ↦ (N i).restrict f) U with he
  set d := modulesSectionsPiEquiv N (f ''ᵁ U) with hd
  have hcomp : ∀ x, e (((restrictPiComparison f N).app U) x) = d x := fun x ↦
    funext fun i ↦ modulesSectionsPiEquiv_restrictPiComparison f N U x i
  refine ⟨fun a b hab ↦ d.injective (((hcomp a).symm.trans (congrArg e hab)).trans (hcomp b)),
    fun t ↦ ?_⟩
  obtain ⟨a, ha⟩ := d.surjective (e t)
  exact ⟨a, e.injective ((hcomp a).trans ha)⟩

/-- Restriction to an open subscheme commutes with products. -/
noncomputable def restrictPiIso {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    {ι : Type u} (N : ι → X.Modules) :
    (∏ᶜ N).restrict f ≅ ∏ᶜ fun i ↦ (N i).restrict f :=
  @asIso _ _ _ _ _ (isIso_restrictPiComparison f N)

/-! ### Discarding the factors with no sections -/

/-- A product may be taken over the subtype of indices whose factors admit more than one
morphism into them: the factors discarded admit a unique morphism from anything, so the
projections to them carry no information. -/
noncomputable def piSubtypeIsoOfSubsingletonHom {C : Type*} [Category C] [HasZeroMorphisms C]
    {ι : Type*} (P : ι → C) (p : ι → Prop) [HasProductsOfShape ι C]
    [HasProductsOfShape {i // p i} C]
    (hz : ∀ i, ¬ p i → ∀ W : C, Subsingleton (W ⟶ P i)) :
    ∏ᶜ P ≅ ∏ᶜ fun s : {i // p i} ↦ P s.1 :=
  letI : DecidablePred p := Classical.decPred p
  { hom := Pi.lift fun s ↦ Pi.π P s.1
    inv := Pi.lift fun i ↦ if h : p i then Pi.π (fun s : {i // p i} ↦ P s.1) ⟨i, h⟩ else 0
    hom_inv_id := by
      refine Pi.hom_ext _ _ fun i ↦ ?_
      rw [Category.assoc, Pi.lift_π, Category.id_comp]
      by_cases h : p i
      · rw [dite_eq_left_of_eq_true (eq_true h), Pi.lift_π]
      · rw [dite_eq_right_of_eq_false (eq_false h), Limits.comp_zero]
        exact (hz i h (∏ᶜ P)).elim _ _
    inv_hom_id := by
      refine Pi.hom_ext _ _ fun s ↦ ?_
      rw [Category.assoc, Pi.lift_π, Pi.lift_π, dite_eq_left_of_eq_true (eq_true s.2),
        Category.id_comp] }

end AlgebraicGeometry
