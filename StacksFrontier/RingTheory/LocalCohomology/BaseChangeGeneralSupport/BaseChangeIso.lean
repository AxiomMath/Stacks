module

public import StacksFrontier.RingTheory.LocalCohomology.BaseChangeGeneralSupport.ComparisonMap
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flat base change for local cohomology with general support

For Noetherian rings the canonical comparison
`RΓ_T(K) ⊗ᴸ_A B ⟶ RΓ_{T'}(K ⊗ᴸ_A B)` is invertible: first for a closed support `T = V(I)`,
from the universal property of the augmentation, and then for every specialization-stable `T`
by the filtered colimit of Tag 0EF1 over closed supports, along the final functor `J ↦ JB` of
closed-support indices. For a flat map this gives Tag 0EF5.

## Main results

* `Stacks.LocalCohomology.isIso_derivedSectionsWithSupportInBaseChangeMap_closed` — the closed
  support case.
* `Stacks.LocalCohomology.isIso_derivedSectionsWithSupportInBaseChangeMap` — invertibility of
  the canonical comparison for every specialization-stable support.
* `Stacks.LocalCohomology.derivedSectionsWithSupportInPlusBaseChangeIso` — Tag 0EF5, the
  bounded-below case.
* `Stacks.LocalCohomology.derivedSectionsWithSupportInBaseChangeIso` — Tag 0EF5, the unbounded
  case.

## References

* [Stacks Project, Tag 0EF5](https://stacks.math.columbia.edu/tag/0EF5)
* [Stacks Project, Tag 0EF1](https://stacks.math.columbia.edu/tag/0EF1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v uB w

namespace Stacks.LocalCohomology

section BaseChange

open CochainComplex.DerivedExtensionScalars
open scoped ChangeOfRings

variable {A : Type u} {B : Type uB} [CommRing A] [CommRing B]

section Closed

/-- Having `I`-power-torsion cohomology is invariant under isomorphism in the derived
category. -/
private lemma derivedPowerTorsionProperty_of_iso.{w', v'} {C : Type w'} [CommRing C]
    (J : Ideal C) (hJ : J.FG) {X Y : DerivedCategory (ModuleCat.{max w' v'} C)} (e : X ≅ Y)
    (hX : Dualizing.derivedPowerTorsionProperty C J hJ X) :
    Dualizing.derivedPowerTorsionProperty C J hJ Y := fun i ↦
  (Dualizing.powerTorsionModuleProperty C J hJ).prop_of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat.{max w' v'} C) i).mapIso e) (hX i)

/-- Postcomposition with an isomorphism is bijective on morphisms. -/
private lemma bijective_comp_iso {C : Type*} [Category C] {W X Y : C} (φ : X ⟶ Y) [IsIso φ] :
    Function.Bijective (fun g : W ⟶ X ↦ g ≫ φ) := by
  refine ⟨fun a b h ↦ (cancel_mono φ).1 h, fun h ↦ ⟨h ≫ CategoryTheory.inv φ, ?_⟩⟩
  show (h ≫ CategoryTheory.inv φ) ≫ φ = h
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

variable [IsNoetherianRing A] [IsNoetherianRing B]

/-- **Base change for local cohomology with closed support.** For Noetherian rings the canonical
comparison `RΓ_{V(I)}(K) ⊗ᴸ_A B ⟶ RΓ_{V(IB)}(K ⊗ᴸ_A B)` is an isomorphism, for every `K` in
`D(A)`. -/
theorem isIso_derivedSectionsWithSupportInBaseChangeMap_closed (f : A →+* B)
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, uB, max u uB v} f)]
    (I : Ideal A) (K : DerivedCategory (ModuleCat.{max u uB v} A)) :
    IsIso ((derivedSectionsWithSupportInBaseChangeMap.{u, v, uB} f
      (PrimeSpectrum.zeroLocus (I : Set A))).app K) := by
  have hI := Ideal.fg_of_isNoetherianRing (R := A) I
  have hJ : (I.map f).FG := hI.map f
  have hset := comap_preimage_zeroLocus_eq_map.{u, uB} f I
  have hθ : IsIso ((compareSectionsWithSupportLocalCohomology.{u, max uB v} A I hI).app K) :=
    isIso_compareSectionsWithSupportLocalCohomology_app.{u, max uB v} A I hI K
  have hεθ : (compareSectionsWithSupportLocalCohomology.{u, max uB v} A I hI).app K ≫
      (Dualizing.localCohomologyAdjunction.{u, max u uB v} A I hI).counit.app K =
      (derivedSectionsWithSupportInAugmentation.{u, max uB v} A
        (PrimeSpectrum.zeroLocus (I : Set A))).app K :=
    congrArg (fun α ↦ NatTrans.app α K)
      (compareSectionsWithSupportLocalCohomology_comp_counit.{u, max uB v} A I hI)
  obtain ⟨htors, huniv⟩ := universal_baseChange.{u, uB, v} f I hI K
  have hEθ : IsIso ((derivedExtensionScalarsGeneral.{u, v, uB} f).functor.map
      ((compareSectionsWithSupportLocalCohomology.{u, max uB v} A I hI).app K)) :=
    inferInstance
  have hEQ : Dualizing.derivedPowerTorsionProperty B (I.map f) hJ
      ((derivedExtensionScalarsGeneral.{u, v, uB} f).functor.obj
        ((derivedSectionsWithSupportIn.{u, max uB v} A
          (PrimeSpectrum.zeroLocus (I : Set A))).obj K)) :=
    derivedPowerTorsionProperty_of_iso.{uB, max u v} (I.map f) hJ
      ((derivedExtensionScalarsGeneral.{u, v, uB} f).functor.mapIso
        (@asIso _ _ _ _ _ hθ)).symm htors
  have hmapε : (derivedExtensionScalarsGeneral.{u, v, uB} f).functor.map
        ((derivedSectionsWithSupportInAugmentation.{u, max uB v} A
          (PrimeSpectrum.zeroLocus (I : Set A))).app K) =
      (derivedExtensionScalarsGeneral.{u, v, uB} f).functor.map
          ((compareSectionsWithSupportLocalCohomology.{u, max uB v} A I hI).app K) ≫
        (derivedExtensionScalarsGeneral.{u, v, uB} f).functor.map
          ((Dualizing.localCohomologyAdjunction.{u, max u uB v} A I hI).counit.app K) :=
    (congrArg (derivedExtensionScalarsGeneral.{u, v, uB} f).functor.map hεθ).symm.trans
      ((derivedExtensionScalarsGeneral.{u, v, uB} f).functor.map_comp _ _)
  have univC : ∀ W, Dualizing.derivedPowerTorsionProperty B (I.map f) hJ W →
      Function.Bijective (fun g : W ⟶ (derivedExtensionScalarsGeneral.{u, v, uB} f).functor.obj
          ((derivedSectionsWithSupportIn.{u, max uB v} A
            (PrimeSpectrum.zeroLocus (I : Set A))).obj K) ↦
        g ≫ (derivedExtensionScalarsGeneral.{u, v, uB} f).functor.map
          ((derivedSectionsWithSupportInAugmentation.{u, max uB v} A
            (PrimeSpectrum.zeroLocus (I : Set A))).app K)) := by
    intro W hW
    rw [hmapε]
    simp only [← Category.assoc]
    exact (huniv W hW).comp (bijective_comp_iso
      ((derivedExtensionScalarsGeneral.{u, v, uB} f).functor.map
        ((compareSectionsWithSupportLocalCohomology.{u, max uB v} A I hI).app K)))
  have hREK : Dualizing.derivedPowerTorsionProperty B (I.map f) hJ
      ((derivedSectionsWithSupportIn.{uB, max u v} B
          ((PrimeSpectrum.comap f) ⁻¹' PrimeSpectrum.zeroLocus (I : Set A))).obj
        ((derivedExtensionScalarsGeneral.{u, v, uB} f).functor.obj K)) := by
    rw [hset]
    exact derivedPowerTorsionProperty_derivedSectionsWithSupportIn.{uB, max u v} B
      (I.map f) hJ _
  have univD : ∀ W, Dualizing.derivedPowerTorsionProperty B (I.map f) hJ W →
      Function.Bijective (fun g : W ⟶ (derivedSectionsWithSupportIn.{uB, max u v} B
            ((PrimeSpectrum.comap f) ⁻¹' PrimeSpectrum.zeroLocus (I : Set A))).obj
            ((derivedExtensionScalarsGeneral.{u, v, uB} f).functor.obj K) ↦
        g ≫ (derivedSectionsWithSupportInAugmentation.{uB, max u v} B
          ((PrimeSpectrum.comap f) ⁻¹' PrimeSpectrum.zeroLocus (I : Set A))).app
          ((derivedExtensionScalarsGeneral.{u, v, uB} f).functor.obj K)) := by
    rw [hset]
    exact fun W hW ↦ bijective_comp_derivedSectionsWithSupportInAugmentation.{uB, max u v} B
      (I.map f) ((derivedExtensionScalarsGeneral.{u, v, uB} f).functor.obj K) W hW
  exact isIso_of_universal _ _ _
    (derivedSectionsWithSupportInBaseChangeMap_augmentation.{u, v, uB} f
      (PrimeSpectrum.zeroLocus (I : Set A)) K)
    (univC _ hREK) (univC _ hEQ).1 (univD _ hREK).1

end Closed

section Index

/-- **Pull a closed support back to a closed support.** The extension of an ideal whose zero
locus lies in `T` has zero locus inside the preimage of `T`. -/
def closedSupportIdealMapObject (f : A →+* B) (T : Set (PrimeSpectrum A))
    (J : ClosedSupportIdeal A T) :
    ClosedSupportIdeal B ((PrimeSpectrum.comap f) ⁻¹' T) :=
  OrderDual.toDual ⟨((OrderDual.ofDual J).1).map f, by
    rw [← comap_preimage_zeroLocus_eq_map]
    exact Set.preimage_mono (OrderDual.ofDual J).2⟩

/-- Extension of ideals is a functor on closed-support indices: it reverses inclusion of ideals,
hence preserves the induced inclusions of supports. -/
def closedSupportIdealMapFunctor (f : A →+* B) (T : Set (PrimeSpectrum A)) :
    ClosedSupportIdeal A T ⥤ ClosedSupportIdeal B ((PrimeSpectrum.comap f) ⁻¹' T) where
  obj := closedSupportIdealMapObject f T
  map {J J'} g := homOfLE
    (Ideal.map_mono (show (OrderDual.ofDual J').1 ≤ (OrderDual.ofDual J).1 from leOfHom g))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- **Contracting a closed support keeps it inside a specialization-stable subset.** If
`V(J) ⊆ (Spec f)⁻¹(T)` for a specialization-stable `T`, then `V(f⁻¹(J)) ⊆ T`. -/
theorem closedSupportIdeal_comap_mem (f : A →+* B) (T : Set (PrimeSpectrum A))
    (hT : StableUnderSpecialization T) (J : Ideal B)
    (hJ : PrimeSpectrum.zeroLocus (J : Set B) ⊆ (PrimeSpectrum.comap f) ⁻¹' T) :
    PrimeSpectrum.zeroLocus (J.comap f : Set A) ⊆ T := by
  intro p hp
  have hI : J.comap f ≤ p.asIdeal := by
    rw [← SetLike.coe_subset_coe]
    exact (PrimeSpectrum.mem_zeroLocus p (J.comap f : Set A)).1 hp
  obtain ⟨Q, hJQ, hQ, hQp⟩ := Ideal.exists_ideal_comap_le_prime (f := f) p.asIdeal J hI
  have hqT : PrimeSpectrum.comap f ⟨Q, hQ⟩ ∈ T :=
    hJ (Set.mem_preimage.mpr ((PrimeSpectrum.mem_zeroLocus _ _).2 hJQ))
  have hqp : PrimeSpectrum.comap f ⟨Q, hQ⟩ ≤ p := by
    rw [← PrimeSpectrum.asIdeal_le_asIdeal, PrimeSpectrum.comap_asIdeal]
    exact hQp
  exact hT ((PrimeSpectrum.le_iff_specializes _ _).mp hqp) hqT

/-- Contract a closed-support index on `Spec B` back to one on `Spec A`. -/
def closedSupportIdealComapObject (f : A →+* B) (T : Set (PrimeSpectrum A))
    (hT : StableUnderSpecialization T)
    (J : ClosedSupportIdeal B ((PrimeSpectrum.comap f) ⁻¹' T)) : ClosedSupportIdeal A T :=
  OrderDual.toDual ⟨(OrderDual.ofDual J).1.comap f,
    closedSupportIdeal_comap_mem f T hT (OrderDual.ofDual J).1 (OrderDual.ofDual J).2⟩

/-- **Extension of closed-support indices is final.** For `T` stable under specialization,
extension of ideals from closed supports inside `T` to closed supports inside the preimage of `T`
is a final functor. -/
theorem closedSupportIdealMap_final (f : A →+* B) (T : Set (PrimeSpectrum A))
    (hT : StableUnderSpecialization T) :
    Functor.Final (closedSupportIdealMapFunctor.{u, uB} f T) := by
  apply Functor.final_of_exists_of_isFiltered
  · intro J
    exact ⟨closedSupportIdealComapObject f T hT J,
      ⟨homOfLE (Ideal.map_comap_le :
        (OrderDual.ofDual ((closedSupportIdealMapFunctor.{u, uB} f T).obj
          (closedSupportIdealComapObject f T hT J))).1 ≤ (OrderDual.ofDual J).1)⟩⟩
  · intro _ I _ _
    exact ⟨I, 𝟙 I, Subsingleton.elim _ _⟩

end Index

section General

/-- The base-change comparison on `i`-th cohomology, read through the flat identification of the
cohomology of a base change with the base change of the cohomology. -/
private def bcHomologyMap (f : A →+* B)
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, uB, max u uB v} f)]
    (T : Set (PrimeSpectrum A)) (K : DerivedCategory (ModuleCat.{max u uB v} A)) (i : ℤ) :
    (ModuleCat.extendScalars.{u, uB, max u uB v} f).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u uB v} A) i).obj
          ((derivedSectionsWithSupportIn.{u, max uB v} A T).obj K)) ⟶
      (DerivedCategory.homologyFunctor (ModuleCat.{max u uB v} B) i).obj
        ((derivedSectionsWithSupportIn.{uB, max u v} B ((PrimeSpectrum.comap f) ⁻¹' T)).obj
          ((derivedExtensionScalarsGeneral.{u, v, uB} f).functor.obj K)) :=
  (derivedExtensionScalarsHomologyNatIso.{u, v, uB} f i).inv.app
      ((derivedSectionsWithSupportIn.{u, max uB v} A T).obj K) ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{max u uB v} B) i).map
      ((derivedSectionsWithSupportInBaseChangeMap.{u, v, uB} f T).app K)

/-- The cohomology comparison is natural in the support. -/
private lemma bcHomologyMap_support (f : A →+* B)
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, uB, max u uB v} f)]
    {S T : Set (PrimeSpectrum A)} (h : S ⊆ T)
    (K : DerivedCategory (ModuleCat.{max u uB v} A)) (i : ℤ) :
    (ModuleCat.extendScalars.{u, uB, max u uB v} f).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{max u uB v} A) i).map
            ((derivedSectionsWithSupportInInclusion.{u, max uB v} A h).app K)) ≫
        bcHomologyMap.{u, v, uB} f T K i =
      bcHomologyMap.{u, v, uB} f S K i ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{max u uB v} B) i).map
          ((derivedSectionsWithSupportInInclusion.{uB, max u v} B
            (Set.preimage_mono h)).app
            ((derivedExtensionScalarsGeneral.{u, v, uB} f).functor.obj K)) := by
  have hnat := (derivedExtensionScalarsHomologyNatIso.{u, v, uB} f i).inv.naturality
    ((derivedSectionsWithSupportInInclusion.{u, max uB v} A h).app K)
  have hsq := derivedSectionsWithSupportInBaseChangeMap_support.{u, v, uB} f h K
  simp only [bcHomologyMap, Category.assoc]
  rw [reassoc_of% hnat, ← Functor.map_comp, hsq, Functor.map_comp]

/-- Derived sections with support in equal subsets are compatible with the inclusion maps. The
two spellings of the pulled-back closed support, `(Spec f)⁻¹(V(I))` and `V(IB)`, are equal but
not identical, and this is the bookkeeping that equality entails. -/
private lemma derivedSectionsWithSupportInInclusion_eqToHom.{w₁, w₂} (C : Type w₁) [CommRing C]
    {S₁ S₂ S₁' S₂' : Set (PrimeSpectrum C)} (e₁ : S₁ = S₁') (e₂ : S₂ = S₂')
    (h : S₁ ⊆ S₂) (h' : S₁' ⊆ S₂') (X : DerivedCategory (ModuleCat.{max w₁ w₂} C)) :
    (derivedSectionsWithSupportInInclusion.{w₁, w₂} C h).app X ≫
        eqToHom (congrArg (fun S ↦ (derivedSectionsWithSupportIn.{w₁, w₂} C S).obj X) e₂) =
      eqToHom (congrArg (fun S ↦ (derivedSectionsWithSupportIn.{w₁, w₂} C S).obj X) e₁) ≫
        (derivedSectionsWithSupportInInclusion.{w₁, w₂} C h').app X := by
  subst e₁
  subst e₂
  simp

/-- The square relating the cohomology comparison at a smaller support to the one at a larger
support, in the presence of the two spellings of the pulled-back supports. -/
private lemma bcHomologyMap_square (f : A →+* B)
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, uB, max u uB v} f)]
    {S T : Set (PrimeSpectrum A)} (h : S ⊆ T)
    {S' T' : Set (PrimeSpectrum B)} (eS : (PrimeSpectrum.comap f) ⁻¹' S = S')
    (eT : (PrimeSpectrum.comap f) ⁻¹' T = T') (h' : S' ⊆ T')
    (K : DerivedCategory (ModuleCat.{max u uB v} A)) (i : ℤ) :
    (ModuleCat.extendScalars.{u, uB, max u uB v} f).map
          ((DerivedCategory.homologyFunctor (ModuleCat.{max u uB v} A) i).map
            ((derivedSectionsWithSupportInInclusion.{u, max uB v} A h).app K)) ≫
        (bcHomologyMap.{u, v, uB} f T K i ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{max u uB v} B) i).map
            (eqToHom (congrArg (fun R ↦ (derivedSectionsWithSupportIn.{uB, max u v} B R).obj
              ((derivedExtensionScalarsGeneral.{u, v, uB} f).functor.obj K)) eT))) =
      (bcHomologyMap.{u, v, uB} f S K i ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{max u uB v} B) i).map
            (eqToHom (congrArg (fun R ↦ (derivedSectionsWithSupportIn.{uB, max u v} B R).obj
              ((derivedExtensionScalarsGeneral.{u, v, uB} f).functor.obj K)) eS))) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{max u uB v} B) i).map
          ((derivedSectionsWithSupportInInclusion.{uB, max u v} B h').app
            ((derivedExtensionScalarsGeneral.{u, v, uB} f).functor.obj K)) := by
  have hcompat := derivedSectionsWithSupportInInclusion_eqToHom.{uB, max u v} B eS eT
    (Set.preimage_mono h) h'
    ((derivedExtensionScalarsGeneral.{u, v, uB} f).functor.obj K)
  rw [← Category.assoc, bcHomologyMap_support.{u, v, uB} f h K i, Category.assoc,
    ← Functor.map_comp, hcompat, Functor.map_comp, Category.assoc]

variable [IsNoetherianRing A] [IsNoetherianRing B]

/-- Over Noetherian rings the cohomology comparison is invertible at a closed support. -/
private lemma isIso_bcHomologyMap_closed (f : A →+* B)
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, uB, max u uB v} f)]
    (I : Ideal A) (K : DerivedCategory (ModuleCat.{max u uB v} A)) (i : ℤ) :
    IsIso (bcHomologyMap.{u, v, uB} f (PrimeSpectrum.zeroLocus (I : Set A)) K i) := by
  have := isIso_derivedSectionsWithSupportInBaseChangeMap_closed.{u, v, uB} f I K
  rw [bcHomologyMap]
  infer_instance

/-- **Stacks Project, Tag 0EF1, in cocone form.** Over a Noetherian ring the canonical cocone
from the closed-support stages to cohomology with support in a specialization-stable subset is a
colimit cocone. -/
def isColimit_closedSupportCocone.{w₁, w₂} (C : Type w₁) [CommRing C]
    [IsNoetherianRing C] (T : Set (PrimeSpectrum C)) (hT : StableUnderSpecialization T) (i : ℤ)
    (K : DerivedCategory (ModuleCat.{max w₁ w₂} C)) :
    IsColimit (closedSupportCocone.{w₁, w₂} C T i K) := by
  have := colimitClosedSupportComparison_isIso.{w₁, w₂} C T hT i
  have : IsIso ((colimit.isColimit ((closedSupportDiagram.{w₁, w₂} C T i).obj K)).desc
      (closedSupportCocone.{w₁, w₂} C T i K)) :=
    inferInstanceAs (IsIso ((colimitClosedSupportComparison.{w₁, w₂} C T i).app K))
  exact IsColimit.ofPointIso (colimit.isColimit _)

/-- A comparison of two colimit cocones over isomorphic diagrams is invertible as soon as it is
compatible with the coprojections. -/
private lemma isIso_of_colimit_comparison {J C : Type*} [Category* J] [Category* C]
    {F G : J ⥤ C} {c : Cocone F} {d : Cocone G} (hc : IsColimit c) (hd : IsColimit d)
    (e : F ≅ G) (m : c.pt ⟶ d.pt)
    (hm : ∀ j, c.ι.app j ≫ m = e.hom.app j ≫ d.ι.app j) : IsIso m := by
  refine ⟨⟨hd.desc ⟨c.pt, e.inv ≫ c.ι⟩, ?_, ?_⟩⟩
  · refine hc.hom_ext fun j ↦ ?_
    rw [← Category.assoc, hm j, Category.assoc, hd.fac ⟨c.pt, e.inv ≫ c.ι⟩ j]
    simp
  · refine hd.hom_ext fun j ↦ ?_
    rw [← Category.assoc, hd.fac ⟨c.pt, e.inv ≫ c.ι⟩ j]
    simp only [NatTrans.comp_app, Category.assoc]
    rw [hm j]
    simp

/-- **Base change for local cohomology with specialization-stable support.** For a flat map of
Noetherian rings the canonical comparison `RΓ_T(K) ⊗ᴸ_A B ⟶ RΓ_{T'}(K ⊗ᴸ_A B)` is invertible for
every `K` in `D(A)`, where `T' = (Spec f)⁻¹(T)`. Neither boundedness of `K` nor finiteness of
the Krull dimensions is needed: the closed-support case is Tag 0ALZ read through the comparison
of Tag 0955, and the general case is the filtered colimit of Tag 0EF1. -/
theorem isIso_derivedSectionsWithSupportInBaseChangeMap (f : A →+* B)
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, uB, max u uB v} f)]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (K : DerivedCategory (ModuleCat.{max u uB v} A)) :
    IsIso ((derivedSectionsWithSupportInBaseChangeMap.{u, v, uB} f T).app K) := by
  have hT' : StableUnderSpecialization ((PrimeSpectrum.comap f) ⁻¹' T) :=
    hT.preimage (PrimeSpectrum.continuous_comap f)
  have := closedSupportIdealMap_final.{u, uB} f T hT
  rw [DerivedCategory.isIso_iff]
  intro i
  have hbc : IsIso (bcHomologyMap.{u, v, uB} f T K i) := by
    refine isIso_of_colimit_comparison
      (isColimitOfPreserves (ModuleCat.extendScalars.{u, uB, max u uB v} f)
        (isColimit_closedSupportCocone.{u, max uB v} A T hT i K))
      ((Functor.Final.isColimitWhiskerEquiv (closedSupportIdealMapFunctor.{u, uB} f T) _).symm
        (isColimit_closedSupportCocone.{uB, max u v} B ((PrimeSpectrum.comap f) ⁻¹' T) hT' i
          ((derivedExtensionScalarsGeneral.{u, v, uB} f).functor.obj K)))
      (NatIso.ofComponents (fun J ↦
        have := isIso_bcHomologyMap_closed.{u, v, uB} f (OrderDual.ofDual J).1 K i
        asIso (bcHomologyMap.{u, v, uB} f (ClosedSupportIdeal.support A J) K i) ≪≫
          (DerivedCategory.homologyFunctor (ModuleCat.{max u uB v} B) i).mapIso
            (eqToIso (congrArg (fun R ↦ (derivedSectionsWithSupportIn.{uB, max u v} B R).obj
                ((derivedExtensionScalarsGeneral.{u, v, uB} f).functor.obj K))
              (comap_preimage_zeroLocus_eq_map.{u, uB} f (OrderDual.ofDual J).1))))
        (fun {J J'} g ↦ by
          have hle : (OrderDual.ofDual J').1 ≤ (OrderDual.ofDual J).1 := leOfHom g
          exact bcHomologyMap_square.{u, v, uB} f (PrimeSpectrum.zeroLocus_anti_mono_ideal hle)
            (comap_preimage_zeroLocus_eq_map.{u, uB} f (OrderDual.ofDual J).1)
            (comap_preimage_zeroLocus_eq_map.{u, uB} f (OrderDual.ofDual J').1)
            (PrimeSpectrum.zeroLocus_anti_mono_ideal (Ideal.map_mono hle)) K i))
      (bcHomologyMap.{u, v, uB} f T K i) (fun J ↦ ?_)
    have hsq := bcHomologyMap_square.{u, v, uB} f (OrderDual.ofDual J).2
      (comap_preimage_zeroLocus_eq_map.{u, uB} f (OrderDual.ofDual J).1) rfl
      (OrderDual.ofDual (closedSupportIdealMapObject.{u, uB} f T J)).2 K i
    rw [eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id] at hsq
    exact hsq
  rw [bcHomologyMap] at hbc
  have := hbc
  exact IsIso.of_isIso_comp_left
    ((derivedExtensionScalarsHomologyNatIso.{u, v, uB} f i).inv.app
      ((derivedSectionsWithSupportIn.{u, max uB v} A T).obj K)) _

end General

section Main

variable [IsNoetherianRing A] [IsNoetherianRing B]

/-- **Stacks Project, Tag 0EF5, the bounded-below case.** Let `f : A →+* B` be a flat
homomorphism of Noetherian rings, let `T ⊆ Spec A` be stable under specialization and put
`T' = (Spec f)⁻¹(T)`. Then local cohomology with support in `T` of a bounded-below complex
commutes with derived extension of scalars along `f`:
`RΓ_T(K) ⊗ᴸ_A B ≅ RΓ_{T'}(K ⊗ᴸ_A B)`, naturally in `K ∈ D⁺(A)` and compatibly with the
augmentations to the identity. No hypothesis on the Krull dimensions is needed. -/
@[stacks 0EF5 "bounded-below case", no_expose, ega "IV 5.9.4" "affine case"]
def derivedSectionsWithSupportInPlusBaseChangeIso (f : A →+* B) (hf : f.Flat)
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T) :
    { e : derivedSectionsWithSupportInPlus.{u, max uB v} A T ⋙ DerivedCategory.Plus.ι ⋙
          (derivedExtensionScalarsGeneral.{u, v, uB} f).functor ≅
        DerivedCategory.Plus.ι ⋙ (derivedExtensionScalarsGeneral.{u, v, uB} f).functor ⋙
          derivedSectionsWithSupportIn.{uB, max u v} B ((PrimeSpectrum.comap f) ⁻¹' T) //
      ∀ K : DerivedCategory.Plus (ModuleCat.{max u uB v} A),
        e.hom.app K ≫
            (derivedSectionsWithSupportInAugmentation.{uB, max u v} B
              ((PrimeSpectrum.comap f) ⁻¹' T)).app
              ((derivedExtensionScalarsGeneral.{u, v, uB} f).functor.obj
                (DerivedCategory.Plus.ι.obj K)) =
          (derivedExtensionScalarsGeneral.{u, v, uB} f).functor.map
            (DerivedCategory.Plus.ι.map
              ((derivedSectionsWithSupportInPlusAugmentation.{u, max uB v} A T).app K)) } :=
  letI := preservesFiniteLimits_extendScalars_of_flat.{u, v, uB} f hf
  have happ : ∀ K, IsIso ((derivedSectionsWithSupportInBaseChangeMap.{u, v, uB} f T).app K) :=
    fun K ↦ isIso_derivedSectionsWithSupportInBaseChangeMap.{u, v, uB} f T hT K
  have hiso : IsIso (derivedSectionsWithSupportInBaseChangeMap.{u, v, uB} f T) :=
    NatIso.isIso_of_isIso_app _
  ⟨Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (derivedSectionsWithSupportInPlusIso.{u, max uB v} A T)
        (derivedExtensionScalarsGeneral.{u, v, uB} f).functor)
      (𝟭 _) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft DerivedCategory.Plus.ι
      (asIso (derivedSectionsWithSupportInBaseChangeMap.{u, v, uB} f T)),
   fun K ↦ by
     have haug := congrArg (fun α ↦ NatTrans.app α K)
       (derivedSectionsWithSupportInPlusIso_augmentation.{u, max uB v} A T)
     simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] at haug
     simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
       Functor.isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app, Functor.id_map,
       Functor.associator_hom_app, Category.id_comp, Category.assoc, asIso_hom]
     rw [derivedSectionsWithSupportInBaseChangeMap_augmentation.{u, v, uB} f T
       (DerivedCategory.Plus.ι.obj K), ← Functor.map_comp, haug]⟩

/-- **Stacks Project, Tag 0EF5, the unbounded case.** Let `f : A →+* B` be a flat homomorphism
of Noetherian rings of finite Krull dimension, let `T ⊆ Spec A` be stable under specialization
and put `T' = (Spec f)⁻¹(T)`. Then local cohomology with support in `T` of an arbitrary complex
commutes with derived extension of scalars along `f`:
`RΓ_T(K) ⊗ᴸ_A B ≅ RΓ_{T'}(K ⊗ᴸ_A B)`, naturally in `K ∈ D(A)` and compatibly with the
augmentations to the identity. -/
@[stacks 0EF5 "unbounded case", no_expose, ega "IV 5.9.4" "affine, finite dim"]
def derivedSectionsWithSupportInBaseChangeIso (f : A →+* B) (hf : f.Flat)
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (_hA : ringKrullDim A < ⊤) (_hB : ringKrullDim B < ⊤) :
    { e : derivedSectionsWithSupportIn.{u, max uB v} A T ⋙
          (derivedExtensionScalarsGeneral.{u, v, uB} f).functor ≅
        (derivedExtensionScalarsGeneral.{u, v, uB} f).functor ⋙
          derivedSectionsWithSupportIn.{uB, max u v} B ((PrimeSpectrum.comap f) ⁻¹' T) //
      ∀ K : DerivedCategory (ModuleCat.{max u uB v} A),
        e.hom.app K ≫
            (derivedSectionsWithSupportInAugmentation.{uB, max u v} B
              ((PrimeSpectrum.comap f) ⁻¹' T)).app
              ((derivedExtensionScalarsGeneral.{u, v, uB} f).functor.obj K) =
          (derivedExtensionScalarsGeneral.{u, v, uB} f).functor.map
            ((derivedSectionsWithSupportInAugmentation.{u, max uB v} A T).app K) } :=
  letI := preservesFiniteLimits_extendScalars_of_flat.{u, v, uB} f hf
  have _happ : ∀ K, IsIso ((derivedSectionsWithSupportInBaseChangeMap.{u, v, uB} f T).app K) :=
    fun K ↦ isIso_derivedSectionsWithSupportInBaseChangeMap.{u, v, uB} f T hT K
  have _hiso : IsIso (derivedSectionsWithSupportInBaseChangeMap.{u, v, uB} f T) :=
    NatIso.isIso_of_isIso_app _
  ⟨asIso (derivedSectionsWithSupportInBaseChangeMap.{u, v, uB} f T),
   derivedSectionsWithSupportInBaseChangeMap_augmentation.{u, v, uB} f T⟩

end Main

end BaseChange

end Stacks.LocalCohomology

end
