module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.KunnethPullbackLeg
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.KunnethFieldCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeCupProductOnCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupPairingNaturality

/-!
# The global Künneth map on cohomology is the cup product of the two pullbacks

Let `a : X ⟶ S`, `b : Y ⟶ S`, `p : W ⟶ X`, `q : W ⟶ Y` and `f : W ⟶ S` be morphisms of ringed
spaces with `p ≫ a = f = q ≫ b`, and set `A = Γ(S, 𝒪_S)`. The global Künneth map of
[Stacks, Tag 0G7V]

`RΓ(X, K) ⊗^𝐋_A RΓ(Y, M) ⟶ RΓ(W, Lp^*K ⊗^𝐋 Lq^*M)`

(`Stacks.Cohomology.GlobalKunneth.kunnethGlobalMap`), formed with the global cup product
`Stacks.Cohomology.DerivedGlobalCupProduct.cupProductOnSpace` of [Stacks, Section 0FKU] on the
base, carries the tensor product `ξ ⊗ η` of two cohomology classes, formed by the cohomology
product of [Stacks, Tag 068H], to the cup product on `W` of their pullbacks:

`ξ ⊗ η ↦ p^*ξ ∪ q^*η`.

This is the description of the Künneth map that the source uses (Cohomology, Section 0FLP), and it
is what turns [Stacks, Tag 0FMB] into the Künneth formula of axiom (A5) of
[Stacks, Section 0FID] for de Rham cohomology.

## Main definitions

* `Stacks.WeilDeRham.sectionsOverBaseHomologyLerayIso`: `Hⁿ(RΓ(V, T))`, `RΓ(V, -)` the derived
  global sections over the base of `c : V ⟶ S`, is `Hⁿ(V, T)` with its scalars restricted along
  `c^♯`.

## Main results

* `Stacks.WeilDeRham.kunnethGlobalMap_crossProduct`: **the global Künneth map on cohomology is
  `ξ ⊗ η ↦ p^*ξ ∪ q^*η`**, when `Γ(S, 𝒪_S)` is a field.

## The argument

The Künneth map is the global cup product on the base, at the two derived direct images, followed
by `RΓ(S, -)` of the relative Künneth map and the Leray identifications. The relative map is the
two pullback legs followed by the relative cup product of `f`
(`Stacks.Cohomology.KunnethCupWithClass.kunnethMap_eq_relativeCupProduct`). The cohomology
product and the cup product are natural; the relative cup product induces the cup product on `W`
through the Leray identification
(`Stacks.Cohomology.LerayCupPairing.lerayCohomologyIso_relativeCupProduct_cupPairing`); and on
cohomology the pullback legs are the pullbacks of classes
(`Stacks.WeilDeRham.lerayCohomologyIso_pullbackLeg_of_eq`). The field hypothesis is used only
for the naturality of the cohomology product along the Leray isomorphisms.

## References

* [Stacks Project, Tag 0G7V](https://stacks.math.columbia.edu/tag/0G7V)
* [Stacks Project, Tag 068H](https://stacks.math.columbia.edu/tag/068H)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Stacks.Cohomology.DerivedGlobalCupProduct Stacks.Cohomology.LerayCupPairing
open Stacks.Cohomology.GlobalKunneth Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite
open scoped TensorProduct CategoryTheory.Prod

universe u


namespace Stacks.WeilDeRham

section Sections

variable {S V : RingedSpace.{u, u}} (c : V ⟶ S)

/-- **`Hⁿ(RΓ(V, T))` over the base is `Hⁿ(V, T)`** with its scalars restricted along `c^♯`: the
inverse of the Leray isomorphism of [Stacks, Tag 0D5W] over the base, followed by the Leray
identification on cohomology. -/
def sectionsOverBaseHomologyLerayIso
    (T : letI := @HasDerivedCategory.standard.{u, u + 1};
        DerivedCategory (SheafOfModules.{u} (structureSheafRing V))) (n : ℤ) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n).obj
        ((sectionsOverBase c).obj T) ≅
      (restrictGlobal c).obj (cohomologyModule T n) :=
  letI := @HasDerivedCategory.standard.{u, u + 1}
  (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n).mapIso
      ((lerayIso c).app T).symm ≪≫ lerayCohomologyIso c T n

/-- The identification of `sectionsOverBaseHomologyLerayIso`, after the Leray isomorphism, is the
Leray identification on cohomology. -/
theorem sectionsOverBaseHomologyLerayIso_hom_lerayIso
    (T : letI := @HasDerivedCategory.standard.{u, u + 1};
        DerivedCategory (SheafOfModules.{u} (structureSheafRing V))) (n : ℤ)
    (z : letI := @HasDerivedCategory.standard.{u, u + 1};
        cohomologyModule ((derivedPushforward c).obj T) n) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    (sectionsOverBaseHomologyLerayIso c T n).hom
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n).map
          ((lerayIso c).hom.app T)).hom z) =
      (lerayCohomologyIso c T n).hom z := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  change (lerayCohomologyIso c T n).hom
    (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n).map
      ((lerayIso c).inv.app T)).hom
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n).map
          ((lerayIso c).hom.app T)).hom z)) = _
  congr 1
  rw [← ModuleCat.comp_apply, ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    ModuleCat.id_apply]

/-- The inverse of `sectionsOverBaseHomologyLerayIso`, followed by the inverse Leray isomorphism,
is the inverse Leray identification on cohomology. -/
theorem lerayIso_inv_sectionsOverBaseHomologyLerayIso_inv
    (T : letI := @HasDerivedCategory.standard.{u, u + 1};
        DerivedCategory (SheafOfModules.{u} (structureSheafRing V))) (n : ℤ)
    (x : letI := @HasDerivedCategory.standard.{u, u + 1}; cohomologyModule T n) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n).map
        ((lerayIso c).inv.app T)).hom ((sectionsOverBaseHomologyLerayIso c T n).inv x) =
      (lerayCohomologyIso c T n).inv x := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  change ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n).map
      ((lerayIso c).inv.app T)).hom
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) n).map
          ((lerayIso c).hom.app T)).hom ((lerayCohomologyIso c T n).inv x)) = _
  rw [← ModuleCat.comp_apply, ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    ModuleCat.id_apply]

end Sections

section Kunneth

/-- A functor to modules on a fourfold composite, on an element. -/
theorem map_comp₄_apply {C : Type*} [Category* C] {R : Type u} [Ring R] (F : C ⥤ ModuleCat.{u} R)
    {x₀ x₁ x₂ x₃ x₄ : C} (f₁ : x₀ ⟶ x₁) (f₂ : x₁ ⟶ x₂) (f₃ : x₂ ⟶ x₃) (f₄ : x₃ ⟶ x₄)
    (z : F.obj x₀) :
    (F.map (f₁ ≫ f₂ ≫ f₃ ≫ f₄)).hom z =
      (F.map f₄).hom ((F.map f₃).hom ((F.map f₂).hom ((F.map f₁).hom z))) := by
  simp only [Functor.map_comp, ModuleCat.comp_apply]

variable {S X Y W : RingedSpace.{u, u}} (a : X ⟶ S) (b : Y ⟶ S) (p : W ⟶ X) (q : W ⟶ Y)
  (f : W ⟶ S) (hp : p ≫ a = f) (hq : q ≫ b = f)

/-- Steps (2) to (4): the relative Künneth map of [Stacks, Tag 0FLP], applied after the cup
product of the base and read on `W` through the Leray identification, sends the cup product of the
classes `ξ` and `η` read on the base to the cup product of their pullbacks. -/
theorem lerayCohomologyIso_kunnethMap_cupPairing
    (K : letI := @HasDerivedCategory.standard.{u, u + 1};
        DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (M : letI := @HasDerivedCategory.standard.{u, u + 1};
        DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) (i j : ℤ)
    (ξ : letI := @HasDerivedCategory.standard.{u, u + 1};
        cohomologyModule K i) (η : letI := @HasDerivedCategory.standard.{u, u + 1};
            cohomologyModule M j) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    (lerayCohomologyIso f (((derivedTensorProductFunctor W.sheaf).obj
        ((derivedPullback p).obj K)).obj ((derivedPullback q).obj M)) (i + j)).hom
      (((DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections S).map
        (Stacks.Cohomology.DerivedKunneth.kunnethMap a b p q f hp hq K M))).hom
        ((cupPairing (cupProductOnSpace S) ((derivedPushforward a).obj K)
          ((derivedPushforward b).obj M) i j).hom
          ((lerayCohomologyIso a K i).inv ξ ⊗ₜ (lerayCohomologyIso b M j).inv η))) =
      (cupPairing (cupProductOnSpace W) ((derivedPullback p).obj K) ((derivedPullback q).obj M)
        i j).hom
        (Stacks.Cohomology.HomologyPullback.homologyPullback p K i ξ ⊗ₜ
          Stacks.Cohomology.HomologyPullback.homologyPullback q M j η) := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  have h₂ := cupPairing_naturality_apply (cupProductOnSpace S)
    (Stacks.Cohomology.KunnethCupWithClass.pullbackLeg a p f hp K)
    (Stacks.Cohomology.KunnethCupWithClass.pullbackLeg b q f hq M) i j
    ((lerayCohomologyIso a K i).inv ξ) ((lerayCohomologyIso b M j).inv η)
  have h₃ := lerayCohomologyIso_relativeCupProduct_cupPairing f ((derivedPullback p).obj K)
    ((derivedPullback q).obj M) i j
    (((DerivedCategory.homologyFunctor _ i).map ((baseSections S).map
      (Stacks.Cohomology.KunnethCupWithClass.pullbackLeg a p f hp K))).hom
        ((lerayCohomologyIso a K i).inv ξ))
    (((DerivedCategory.homologyFunctor _ j).map ((baseSections S).map
      (Stacks.Cohomology.KunnethCupWithClass.pullbackLeg b q f hq M))).hom
        ((lerayCohomologyIso b M j).inv η))
  have h₄ := lerayCohomologyIso_pullbackLeg_of_eq a p f hp K i ξ
  have h₅ := lerayCohomologyIso_pullbackLeg_of_eq b q f hq M j η
  have hk := congrArg (fun t => ((DerivedCategory.homologyFunctor _ (i + j)).map
      ((baseSections S).map t)).hom
        ((cupPairing (cupProductOnSpace S) ((derivedPushforward a).obj K)
          ((derivedPushforward b).obj M) i j).hom
          ((lerayCohomologyIso a K i).inv ξ ⊗ₜ (lerayCohomologyIso b M j).inv η)))
    (Stacks.Cohomology.KunnethCupWithClass.kunnethMap_eq_relativeCupProduct a b p q f hp hq K M)
  refine (congrArg (lerayCohomologyIso f _ (i + j)).hom (hk.trans
    ((Stacks.Cohomology.HomologyPullback.map_map_comp_apply _ _ _ _ _).trans
      (congrArg _ h₂.symm)))).trans (h₃.trans ?_)
  exact congrArg₂ (fun x y => (cupPairing (cupProductOnSpace W) _ _ i j).hom (x ⊗ₜ y)) h₄ h₅

/-- Step (1): the cohomology product of two classes over the base, carried along the inverse Leray
isomorphisms, is the cohomology product of their Leray images, when the base ring is a field. -/
theorem crossProductCast_lerayIso_inv (hS : IsField (baseRing S))
    (K : letI := @HasDerivedCategory.standard.{u, u + 1};
        DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (M : letI := @HasDerivedCategory.standard.{u, u + 1};
        DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) (i j : ℤ)
    (ξ : letI := @HasDerivedCategory.standard.{u, u + 1};
        cohomologyModule K i) (η : letI := @HasDerivedCategory.standard.{u, u + 1};
            cohomologyModule M j) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
        ((Functor.uncurry.obj (tensorBase S)).map
          ((lerayIso a).inv.app K ×ₘ (lerayIso b).inv.app M))).hom
      ((crossProductCast ((sectionsOverBase a).obj K) ((sectionsOverBase b).obj M) i j (i + j)
          rfl).hom
        ((sectionsOverBaseHomologyLerayIso a K i).inv ξ ⊗ₜ
          (sectionsOverBaseHomologyLerayIso b M j).inv η)) =
      (RingTheory.TorProducts.cohomologyTensorProduct ((baseSections S).obj
          ((derivedPushforward a).obj K)) ((baseSections S).obj
          ((derivedPushforward b).obj M)) i j).map.hom
        ((lerayCohomologyIso a K i).inv ξ ⊗ₜ (lerayCohomologyIso b M j).inv η) := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  have h₁ := ConcreteCategory.congr_hom (crossProductCast_naturality_of_isField hS
    ((lerayIso a).inv.app K)
    ((lerayIso b).inv.app M) i j (i + j) rfl)
    ((sectionsOverBaseHomologyLerayIso a K i).inv ξ ⊗ₜ
      (sectionsOverBaseHomologyLerayIso b M j).inv η)
  refine h₁.symm.trans ?_
  rw [crossProductCast_rfl]
  exact congrArg₂ (fun x y =>
      (RingTheory.TorProducts.cohomologyTensorProduct ((baseSections S).obj
        ((derivedPushforward a).obj K)) ((baseSections S).obj
        ((derivedPushforward b).obj M)) i j).map.hom (x ⊗ₜ y))
    (lerayIso_inv_sectionsOverBaseHomologyLerayIso_inv a K i ξ)
    (lerayIso_inv_sectionsOverBaseHomologyLerayIso_inv b M j η)

/-- **The global Künneth map on cohomology is the cup product of the pullbacks**: for
`ξ ∈ Hⁱ(X, K)` and `η ∈ Hʲ(Y, M)`, read over `A = Γ(S, 𝒪_S)`, the Künneth map of
[Stacks, Tag 0G7V] built from the cup product of [Stacks, Section 0FKU] sends the cohomology
product of [Stacks, Tag 068H] of the two classes to `p^*ξ ∪ q^*η`, the cup product on `W` of
their pullbacks. The base ring is assumed to be a field. -/
theorem kunnethGlobalMap_crossProduct (hS : IsField (baseRing S))
    (K : letI := @HasDerivedCategory.standard.{u, u + 1};
        DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (M : letI := @HasDerivedCategory.standard.{u, u + 1};
        DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) (i j : ℤ)
    (ξ : letI := @HasDerivedCategory.standard.{u, u + 1};
        cohomologyModule K i) (η : letI := @HasDerivedCategory.standard.{u, u + 1};
            cohomologyModule M j) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    (sectionsOverBaseHomologyLerayIso f
        (((derivedTensorProductFunctor W.sheaf).obj ((derivedPullback p).obj K)).obj
          ((derivedPullback q).obj M)) (i + j)).hom
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
          (kunnethGlobalMap a b p q f hp hq (cupProductOnSpace S) K M)).hom
        ((crossProductCast ((sectionsOverBase a).obj K) ((sectionsOverBase b).obj M) i j (i + j)
          rfl).hom
          ((sectionsOverBaseHomologyLerayIso a K i).inv ξ ⊗ₜ
            (sectionsOverBaseHomologyLerayIso b M j).inv η))) =
      (cupPairing (cupProductOnSpace W) ((derivedPullback p).obj K) ((derivedPullback q).obj M)
        i j).hom
        (Stacks.Cohomology.HomologyPullback.homologyPullback p K i ξ ⊗ₜ
          Stacks.Cohomology.HomologyPullback.homologyPullback q M j η) := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  have h₁ := crossProductCast_lerayIso_inv a b hS K M i j ξ η
  have h₂ := lerayCohomologyIso_kunnethMap_cupPairing a b p q f hp hq K M i j ξ η
  have hK := congrArg (fun t => ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing S)) (i + j)).map t).hom
        ((crossProductCast ((sectionsOverBase a).obj K) ((sectionsOverBase b).obj M) i j (i + j)
          rfl).hom ((sectionsOverBaseHomologyLerayIso a K i).inv ξ ⊗ₜ
            (sectionsOverBaseHomologyLerayIso b M j).inv η)))
    (kunnethGlobalMap_eq a b p q f hp hq (cupProductOnSpace S) K M)
  refine (congrArg (sectionsOverBaseHomologyLerayIso f _ (i + j)).hom
    (hK.trans (map_comp₄_apply _ _ _ _ _ _))).trans ?_
  refine (sectionsOverBaseHomologyLerayIso_hom_lerayIso f _ (i + j) _).trans (Eq.trans ?_ h₂)
  refine congrArg (fun t => (lerayCohomologyIso f _ (i + j)).hom
    (((DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections S).map
      (Stacks.Cohomology.DerivedKunneth.kunnethMap a b p q f hp hq K M))).hom t)) ?_
  exact (congrArg (fun t => ((DerivedCategory.homologyFunctor _ (i + j)).map
    ((cupProductOnSpace S).app ((derivedPushforward a).obj K, (derivedPushforward b).obj M))).hom t)
    h₁).trans (ModuleCat.comp_apply _ _ _).symm

end Kunneth

end Stacks.WeilDeRham

end
