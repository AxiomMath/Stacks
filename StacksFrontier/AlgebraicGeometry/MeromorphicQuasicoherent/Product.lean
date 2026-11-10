module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import StacksFrontier.AlgebraicGeometry.GenericPointSheaf.ProductSections
public import StacksFrontier.AlgebraicGeometry.MeromorphicQuasicoherent.Basic

/-!
# Quasi-coherence of the generic-point product

The generic-point product of Stacks Tags 0EMF, 02OW and 0EMH is quasi-coherent as soon as each
quasi-compact open of the scheme has finitely many irreducible components. Quasi-coherence is local
on the base, and on an affine open only the finitely many generic points lying in that open
contribute, so the restriction of the product there is a finite product of quasi-coherent modules.

## Main results

* `Stacks.AlgebraicGeometry.MeromorphicQuasicoherent.isQuasicoherent_pi`: a product of
  quasi-coherent modules indexed by a finite type is quasi-coherent.
* `Stacks.AlgebraicGeometry.MeromorphicQuasicoherent.isIso_restrictPiLift`: the restriction of a
  product of modules to an open set is the product of the restrictions of the factors which do not
  restrict to zero there.
* `Stacks.AlgebraicGeometry.MeromorphicQuasicoherent.isQuasicoherent_piGenericPointStalkModule`:
  the generic-point product is quasi-coherent.

## Implementation notes

The sections of a product of `𝒪_X`-modules over an open set are the product of the sections of the
factors, through `Stacks.AlgebraicGeometry.GenericPointSheaf.productSectionsIso`; this is what
makes the comparison morphism out of the restricted product checkable on sections, by exactly the
argument of `Stacks.AlgebraicGeometry.GenericPointProduct.isIso_decomposition`. Dropping the
factors which vanish on the open set loses nothing, because a product of modules over a
subsingleton index-subfamily is a subsingleton.

A finite product is a finite coproduct through the biproduct, and coproducts of quasi-coherent
modules are quasi-coherent for an arbitrary index type. `HasFiniteBiproducts` is not an instance
in Mathlib — `CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts` is kept a theorem —
so it is supplied here as a local instance.

## References

* [Stacks Project, Tag 02OW](https://stacks.math.columbia.edu/tag/02OW)
* [Stacks Project, Tag 0EMH](https://stacks.math.columbia.edu/tag/0EMH)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.MeromorphicQuasicoherent

open Stacks.AlgebraicGeometry.GenericPointDecomposition
open Stacks.AlgebraicGeometry.GenericPointGluing
open Stacks.AlgebraicGeometry.GenericPointSheaf

/-! ### Sections of a product -/

variable {Y : Scheme.{u}} {ι : Type u}

/-- The sections, over an open set, of a product of `𝒪_Y`-modules, as the dependent function type
of the sections of the factors. -/
noncomputable def sectionsPi (G : ι → Y.Modules) (U : Y.Opens) :
    (sectionsFunctor Y U).obj (∏ᶜ G) ≅
      ModuleCat.of (Y.ringCatSheaf.obj.obj (op U))
        (∀ i : ι, (sectionsFunctor Y U).obj (G i)) :=
  productSectionsIso G U ≪≫ ModuleCat.piIsoPi _

/-- The `i`-th component of the image of a section of a product under `sectionsPi` is the image
of that section under the `i`-th projection. -/
theorem sectionsPi_hom_apply (G : ι → Y.Modules) (U : Y.Opens)
    (x : (sectionsFunctor Y U).obj (∏ᶜ G)) (i : ι) :
    (sectionsPi G U).hom x i = (sectionsFunctor Y U).map (Pi.π G i) x := by
  have h1 : (ModuleCat.piIsoPi fun i ↦ (sectionsFunctor Y U).obj (G i)).hom
      ((productSectionsIso G U).hom x) i =
      (Pi.π (fun i ↦ (sectionsFunctor Y U).obj (G i)) i) ((productSectionsIso G U).hom x) :=
    ConcreteCategory.congr_hom
      (ModuleCat.piIsoPi_hom_ker_subtype (fun i ↦ (sectionsFunctor Y U).obj (G i)) i)
      ((productSectionsIso G U).hom x)
  have h2 : (productSectionsIso G U).hom ≫
      Pi.π (fun i ↦ (sectionsFunctor Y U).obj (G i)) i =
      (sectionsFunctor Y U).map (Pi.π G i) := by
    rw [productSectionsIso, PreservesProduct.iso_hom, piComparison, Pi.lift_comp_π]
  exact h1.trans (by rw [← ConcreteCategory.comp_apply, h2])

/-- Evaluation on an open set, as a functor to modules over the ring of sections, agrees on
elements with the application of a morphism to sections. -/
theorem sectionsFunctor_map_apply {M N : Y.Modules} (φ : M ⟶ N) (U : Y.Opens)
    (x : (sectionsFunctor Y U).obj M) : (sectionsFunctor Y U).map φ x = φ.app U x := rfl

/-- A section of a product of `𝒪_Y`-modules over an open set is determined by its family of
components, and any family of components arises from one. -/
theorem bijective_piApp (G : ι → Y.Modules) (U : Y.Opens) :
    Function.Bijective (fun (x : Γ(∏ᶜ G, U)) (i : ι) ↦ (Pi.π G i).app U x) := by
  have h := ConcreteCategory.bijective_of_isIso (sectionsPi G U).hom
  have key : ∀ x, (fun i ↦ (Pi.π G i).app U x) = (sectionsPi G U).hom x := fun x ↦
    funext fun i ↦ ((sectionsPi_hom_apply G U x i).trans
      (sectionsFunctor_map_apply (Pi.π G i) U x)).symm
  exact ⟨fun a b hab ↦ h.1 ((key a).symm.trans (hab.trans (key b))),
    fun v ↦ (h.2 v).imp fun a ha ↦ (key a).trans ha⟩

/-! ### A product of quasi-coherent modules indexed by a finite type -/

/-- A product of quasi-coherent modules indexed by a finite type is quasi-coherent: it is the
biproduct, hence the coproduct, of the same family. -/
theorem isQuasicoherent_pi [Finite ι] (G : ι → Y.Modules)
    (hG : ∀ i, (G i).IsQuasicoherent) : (∏ᶜ G).IsQuasicoherent :=
  let : Fintype ι := Fintype.ofFinite ι
  let : HasFiniteBiproducts Y.Modules := HasFiniteBiproducts.of_hasFiniteProducts
  let : ∀ i, (G i).IsQuasicoherent := hG
  (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    ((biproduct.isoCoproduct G).symm ≪≫ biproduct.isoProduct G)
    (QuasicoherentColimits.isQuasicoherent_sigma G)

/-! ### Dropping the factors which vanish on an open set -/

variable {X : Scheme.{u}}

/-- The contribution of a generic point has no sections on an open set missing that point: the
preimage of such an open set in the local scheme is empty. -/
theorem subsingleton_genericPointStalkModule_sections {η : genericPoints X} {U : X.Opens}
    (hη : (η : X) ∉ U) : Subsingleton Γ(genericPointStalkModule X η, U) := by
  have h : (X.fromSpecStalk η.1) ⁻¹ᵁ U = ⊥ := fromSpecStalk_preimage_eq_bot η.2 hη
  change Subsingleton
    Γ(SheafOfModules.unit (Spec (X.presheaf.stalk η.1)).ringCatSheaf,
      (X.fromSpecStalk η.1) ⁻¹ᵁ U)
  rw [h]
  change Subsingleton ((Spec (X.presheaf.stalk η.1)).presheaf.obj (op ⊥))
  infer_instance

/-- Restricting a family of modules to the sub-index-type on which it may have sections loses
nothing: the comparison of the two products of sections is bijective. -/
theorem bijective_piRestrictIndex {A : ι → Type*} [∀ i, Zero (A i)] (p : ι → Prop)
    (h : ∀ i, ¬ p i → Subsingleton (A i)) :
    Function.Bijective (fun (v : ∀ i, A i) (i : {i : ι // p i}) ↦ v i.1) := by
  classical
  refine ⟨fun a b hab ↦ funext fun i ↦ ?_, fun w ↦ ?_⟩
  · by_cases hi : p i
    · exact congrFun hab ⟨i, hi⟩
    · exact (h i hi).elim _ _
  · refine ⟨fun i ↦ if hi : p i then w ⟨i, hi⟩ else 0, funext fun i ↦ ?_⟩
    simp only [i.2, dite_true]

/-! ### The restriction of a product to an open set -/

/-- The restriction to an open set of a product of `𝒪_X`-modules, compared with the product of the
restrictions of the factors whose index satisfies `p`. -/
noncomputable def restrictPiLift (V : X.Opens) (F : ι → X.Modules) (p : ι → Prop) :
    (Scheme.Modules.restrictFunctor V.ι).obj (∏ᶜ F) ⟶
      ∏ᶜ fun i : {i : ι // p i} ↦ (Scheme.Modules.restrictFunctor V.ι).obj (F i.1) :=
  Pi.lift fun i ↦ (Scheme.Modules.restrictFunctor V.ι).map (Pi.π F i.1)

/-- The restriction of a morphism of modules along an open immersion `f`, evaluated on an open
set `W`, is the original morphism evaluated on the image `f ''ᵁ W`. -/
theorem restrictFunctor_map_app {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f]
    {M N : Z.Modules} (φ : M ⟶ N) (W : Y.Opens) :
    ((Scheme.Modules.restrictFunctor f).map φ).app W = φ.app (f ''ᵁ W) := rfl

/-- Applying two morphisms of `𝒪_Y`-modules in turn to a section over `U` is applying their
composite. -/
theorem comp_app_apply {M N K : Y.Modules} (φ : M ⟶ N) (ψ : N ⟶ K) (U : Y.Opens)
    (x : Γ(M, U)) : ψ.app U (φ.app U x) = (φ ≫ ψ).app U x := rfl

/-- The restriction of a product of modules to an open set is the product of the restrictions of
the factors which can have sections there. The factors dropped are the ones with no sections on
any open subset of `V`, so no section is lost and none is added. -/
theorem isIso_restrictPiLift (V : X.Opens) (F : ι → X.Modules) (p : ι → Prop)
    (hsub : ∀ i, ¬ p i → ∀ W : V.toScheme.Opens, Subsingleton Γ(F i, V.ι ''ᵁ W)) :
    IsIso (restrictPiLift V F p) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  rw [ConcreteCategory.isIso_iff_bijective]
  have hL := bijective_piApp F (V.ι ''ᵁ W)
  have hR := bijective_piApp
    (fun i : {i : ι // p i} ↦ (Scheme.Modules.restrictFunctor V.ι).obj (F i.1)) W
  have hI : Function.Bijective
      (fun (v : ∀ i, Γ(F i, V.ι ''ᵁ W)) (i : {i : ι // p i}) ↦ v i.1) :=
    bijective_piRestrictIndex p fun i hi ↦ hsub i hi W
  refine (Function.Bijective.of_comp_iff' hR _).1 ?_
  have key : ∀ (x : Γ((Scheme.Modules.restrictFunctor V.ι).obj (∏ᶜ F), W)) (i : {i : ι // p i}),
      (Pi.π (fun j : {j : ι // p j} ↦
        (Scheme.Modules.restrictFunctor V.ι).obj (F j.1)) i).app W
          ((restrictPiLift V F p).app W x) = (Pi.π F i.1).app (V.ι ''ᵁ W) x := by
    intro x i
    rw [comp_app_apply, restrictPiLift, Pi.lift_comp_π, restrictFunctor_map_app]
    rfl
  refine Eq.mp (congrArg Function.Bijective (funext fun x ↦ funext fun i ↦ (key x i).symm))
    (hI.comp hL)

/-! ### Quasi-coherence of the generic-point product -/

/-- **The generic-point product is quasi-coherent.** On an affine open only the finitely many
generic points lying in that open have sections, so the restriction of the product there is a
finite product of quasi-coherent modules, and quasi-coherence is local on the base. No hypothesis
on the weakly associated points is needed; only the local finiteness of the irreducible
components. -/
theorem isQuasicoherent_piGenericPointStalkModule (X : Scheme.{u})
    (hfin : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents (V : Set X)).Finite) :
    (∏ᶜ fun η : genericPoints X ↦ genericPointStalkModule X η).IsQuasicoherent := by
  refine QuasicoherentColimits.isQuasicoherent_of_restrict_affineOpens _ fun V ↦ ?_
  have hsub : ∀ η : genericPoints X, ¬ ((η : X) ∈ (V : X.Opens)) →
      ∀ W : (V : X.Opens).toScheme.Opens,
        Subsingleton Γ(genericPointStalkModule X η, (V : X.Opens).ι ''ᵁ W) := fun η hη W ↦
    subsingleton_genericPointStalkModule_sections
      fun h ↦ hη (Scheme.Opens.ι_image_le (V : X.Opens) W h)
  have hiso : IsIso (restrictPiLift (V : X.Opens)
      (fun η : genericPoints X ↦ genericPointStalkModule X η)
      fun η ↦ (η : X) ∈ (V : X.Opens)) :=
    isIso_restrictPiLift _ _ _ hsub
  have hfinite : Finite {η : genericPoints X // (η : X) ∈ (V : X.Opens)} :=
    finite_genericPoints_subtype X (hfin (V : X.Opens) V.2.isCompact)
  exact (SheafOfModules.isQuasicoherent (V : X.Opens).toScheme.ringCatSheaf).prop_of_iso
    (@asIso _ _ _ _ _ hiso).symm
    (@isQuasicoherent_pi _ _ hfinite _ fun i ↦
      Scheme.Modules.isQuasicoherent_restrictFunctor (V : X.Opens).ι
        (genericPointStalkModule X i.1))

end Stacks.AlgebraicGeometry.MeromorphicQuasicoherent
