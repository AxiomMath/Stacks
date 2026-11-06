module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.ProperVanishing
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonCoherence
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowTransformationDevissage
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology

/-!
# `Rf_!` along a morphism of compactifications

Let `f : X ⟶ Y` be a morphism of schemes and `g : j ⟶ k` a morphism of compactifications of `X`
over `Y`, with ambient morphism `ḡ : X̄_j ⟶ X̄_k`. This file constructs the canonical
isomorphism `Rf_!^k ≅ Rf_!^j` of the two derived lower shriek functors on `D⁺_tors(X_étale, Λ)`
of the proof of [Stacks, Tag 0F7I],

`R(k̄)_* ∘ Rk_! ≅ R(k̄)_* ∘ Rḡ_* ∘ Rj_! ≅ R(j̄)_* ∘ Rj_!`,

whose first step is the map `Rk_! ⟶ Rḡ_* ∘ Rj_!` of [Stacks, Tag 0F7G] (the descent along the
derived-functor units of the underived identification `θ_g : k_! ≅ ḡ_* j_!`), and whose second
step is the composition comparison of derived direct images. It proves that these isomorphisms
turn composition of morphisms of compactifications into composition.

## Main definitions

* `Stacks.EtaleCohomology.derivedRefinementComparison`: the map of Tag 0F7G.
* `Stacks.EtaleCohomology.derivedBaseComparison`: `R(j̄)_* ≅ Rḡ_* ⋙ R(k̄)_*`.
* `Stacks.EtaleCohomology.derivedLowerShriekHomIso`: `Rf_!^k ≅ Rf_!^j` on `D⁺_tors`.

## Main results

* `Stacks.EtaleCohomology.isIso_derivedRefinementComparison_app`: **Tag 0F7G, case (a)**: the
  map is invertible on `D⁺_tors`, for an arbitrary ring `Λ`.
* `Stacks.EtaleCohomology.derivedLowerShriekHomIso_comp`: the cocycle law.

## Implementation notes

The functors `Rf_!` are those of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology`, which live in the
standard model of the derived category; the local instance below is confined to this file's
statements about them. The coherence lemmas consumed are stated for an arbitrary model.

## References

* [Stacks Project, Tag 0F7G](https://stacks.math.columbia.edu/tag/0F7G)
* [Stacks Project, Tag 0F7I](https://stacks.math.columbia.edu/tag/0F7I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

/-! ### Morphisms of compactifications -/

namespace AlgebraicGeometry.CompactificationOf

variable {S : Scheme.{u}} {Z : Over S}

/-- A morphism of compactifications commutes with the two open immersions. -/
lemma immersion_comp_map {j k : CompactificationOf Z} (g : j ⟶ k) :
    j.immersion ≫ Hom.map g = k.immersion :=
  congrArg CommaMorphism.left (StructuredArrow.w g.hom)

/-- The ambient morphism of a morphism of compactifications lies over the base. -/
lemma map_comp_toBase {j k : CompactificationOf Z} (g : j ⟶ k) :
    Hom.map g ≫ k.toBase = j.toBase :=
  Over.w g.hom.right

/-- The ambient morphism of a morphism of compactifications is proper. -/
instance isProper_map {j k : CompactificationOf Z} (g : j ⟶ k) : IsProper (Hom.map g) := by
  have : IsProper (Hom.map g ≫ k.toBase) := by
    rw [map_comp_toBase]
    infer_instance
  exact IsProper.of_comp _ k.toBase

end AlgebraicGeometry.CompactificationOf

namespace Stacks.EtaleCohomology

open CategoryTheory.Functor

attribute [local instance] HasDerivedCategory.standard commShiftRightDerivedFunctorPlus
  natTransCommShiftRightDerivedFunctorPlusUnit

variable (Λ : Type) [Ring Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}

/-! ### The comparisons attached to a morphism of compactifications -/

section Comparisons

variable {j k : CompactificationOf (Over.mk f)} (g : j ⟶ k)

/-- The underived identification `θ_g : k_! ≅ ḡ_* j_!` (Tags 0F79 and 0F51). -/
def refinementIso :
    etaleModuleExtensionByZero.{u, 0} Λ k.immersion ≅
      etaleModuleExtensionByZero.{u, 0} Λ j.immersion ⋙
        etaleModuleDirectImage.{u, 0} Λ (CompactificationOf.Hom.map g) :=
  haveI := isIso_etaleModuleRefinementComparison Λ (CompactificationOf.immersion_comp_map g)
  asIso (etaleModuleRefinementComparison Λ (CompactificationOf.immersion_comp_map g))

/-- **The map `Rk_! ⟶ Rḡ_* ∘ Rj_!` of [Stacks, Tag 0F7G]**: the invariance comparison of `θ_g`
followed by the composition comparison of [Stacks, Tag 05T2]. -/
def derivedRefinementComparison :
    etaleModuleDerivedExtensionByZero.{u, 0} Λ k.immersion ⟶
      etaleModuleDerivedExtensionByZero.{u, 0} Λ j.immersion ⋙
        etaleModuleDerivedDirectImage.{u, 0} Λ (CompactificationOf.Hom.map g) :=
  (rightDerivedFunctorPlusNatIso (refinementIso Λ g)).hom ≫ rightDerivedFunctorPlusComp _ _

/-- The composition comparison `R(j̄)_* ⟶ Rḡ_* ⋙ R(k̄)_*` of derived direct images. -/
def derivedBaseComparison :
    etaleModuleDerivedDirectImage.{u, 0} Λ j.toBase ⟶
      etaleModuleDerivedDirectImage.{u, 0} Λ (CompactificationOf.Hom.map g) ⋙
        etaleModuleDerivedDirectImage.{u, 0} Λ k.toBase :=
  (rightDerivedFunctorPlusNatIso (etaleModuleDirectImageComp.{u, 0} Λ
      (CompactificationOf.Hom.map g) k.toBase j.toBase
      (CompactificationOf.map_comp_toBase g).symm)).inv ≫ rightDerivedFunctorPlusComp _ _

/-- The composition comparison `R(j̄)_* ⟶ Rḡ_* ⋙ R(k̄)_*` is an isomorphism. -/
instance isIso_derivedBaseComparison : IsIso (derivedBaseComparison Λ g) := by
  dsimp only [derivedBaseComparison]
  infer_instance

end Comparisons

/-! ### Tag 0F7G, case (a) -/

section Invertibility

/-- The unit `rightDerivedFunctorPlusUnith` (whose definition is not exposed) followed by the
comparison with the `totalRightDerived` presentation is the unit of `totalRightDerived`. -/
private lemma totalRightDerivedUnit_app_eq_compIndepDerived {D E : Type*} [Category* D]
    [Category* E] [Abelian D] [Abelian E] [HasDerivedCategory D] [HasDerivedCategory E]
    [EnoughInjectives D] (G : D ⥤ E) [G.Additive] (Y : HomotopyCategory.Plus D) :
    ((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso D)).app Y =
      G.rightDerivedFunctorPlusUnith.app Y ≫
        (G.rightDerivedFunctorPlus.rightDerivedDesc G.rightDerivedFunctorPlusUnith
          (HomotopyCategory.Plus.quasiIso D) _
          ((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
            DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso D))).app
          (DerivedCategory.Plus.Qh.obj Y) :=
  (Functor.rightDerived_fac_app G.rightDerivedFunctorPlus G.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso D) _ _ Y).symm

/-- An object is right acyclic for `G` exactly when the unit `rightDerivedFunctorPlusUnith` is
invertible at the single complex on it in degree zero. -/
private lemma rightAcyclic_iff_isIso_unith_app_compIndepDerived {D E : Type*}
    [Category* D] [Category* E] [Abelian D] [Abelian E] [HasDerivedCategory D]
    [HasDerivedCategory E] [EnoughInjectives D] (G : D ⥤ E) [G.Additive] (X : D) :
    G.rightAcyclic X ↔ IsIso (G.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.singleFunctor D 0).obj X)) := by
  have : IsIso (G.rightDerivedFunctorPlus.rightDerivedDesc G.rightDerivedFunctorPlusUnith
      (HomotopyCategory.Plus.quasiIso D) _
      ((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso D))) :=
    (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc _ _ _ _ _).1 inferInstance
  change IsIso (((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
    DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso D)).app _) ↔ _
  rw [totalRightDerivedUnit_app_eq_compIndepDerived]
  exact isIso_comp_right_iff _ _

variable {j k : CompactificationOf (Over.mk f)} (g : j ⟶ k)

/-- The composition comparison `R(ḡ_* ∘ j_!) ⟶ Rj_! ⋙ Rḡ_*` is invertible at a torsion sheaf
placed in degree zero: there `j_! M` is acyclic for `ḡ_*`. -/
lemma isIso_rightDerivedFunctorPlusComp_app_single (M : EtaleModules.{u, 0} Λ X)
    (hM : IsTorsionEtaleModule.{u, 0} Λ X M) :
    IsIso ((rightDerivedFunctorPlusComp (etaleModuleExtensionByZero.{u, 0} Λ j.immersion)
      (etaleModuleDirectImage.{u, 0} Λ (CompactificationOf.Hom.map g))).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M)) := by
  let F := etaleModuleExtensionByZero.{u, 0} Λ j.immersion
  let H := etaleModuleDirectImage.{u, 0} Λ (CompactificationOf.Hom.map g)
  let Xs := (HomotopyCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ X) 0).obj M
  have hF : IsIso (F.rightDerivedFunctorPlusUnith.app Xs) :=
    (rightAcyclic_iff_isIso_unith_app_compIndepDerived F M).1 (rightAcyclic_of_exact F M)
  have hK : IsIso
      ((etaleModuleExtensionByZero.{u, 0} Λ k.immersion).rightDerivedFunctorPlusUnith.app Xs) :=
    (rightAcyclic_iff_isIso_unith_app_compIndepDerived _ M).1 (rightAcyclic_of_exact _ M)
  have hFH : IsIso ((F ⋙ H).rightDerivedFunctorPlusUnith.app Xs) :=
    IsIso.of_isIso_fac_left (rightDerivedFunctorPlusNatIso_hom_fac_app (refinementIso Λ g) Xs).symm
  have hac : H.rightAcyclic (F.obj M) :=
    (Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived H (F.obj M)).2
      fun p hp => isZero_rightDerived_etaleModuleDirectImage_extensionByZero Λ
        (CompactificationOf.immersion_comp_map g) M hM p hp
  have hH : IsIso (H.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj Xs)) := by
    let e := Stacks.Cohomology.LerayDegreewise.mapHomotopyCategoryPlusSingleObjIso F 0 M
    have hn := H.rightDerivedFunctorPlusUnith.naturality e.hom
    have : IsIso (H.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.singleFunctor _ 0).obj (F.obj M))) :=
      (rightAcyclic_iff_isIso_unith_app_compIndepDerived H (F.obj M)).1 hac
    exact IsIso.of_isIso_fac_right hn.symm
  have key : IsIso ((F ⋙ H).rightDerivedFunctorPlusUnith.app Xs ≫
      (rightDerivedFunctorPlusComp F H).app (DerivedCategory.Plus.Qh.obj Xs)) := by
    rw [unit_comp_rightDerivedFunctorPlusComp_app F H Xs]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hH (Functor.map_isIso _ _)
  have ht : IsIso ((rightDerivedFunctorPlusComp F H).app (DerivedCategory.Plus.Qh.obj Xs)) :=
    IsIso.of_isIso_comp_left ((F ⋙ H).rightDerivedFunctorPlusUnith.app Xs) _
  exact (NatTrans.isIso_app_iff_of_iso _
    ((DerivedCategory.Plus.singleFunctorIsoCompQh (EtaleModules.{u, 0} Λ X) 0).app M)).2 ht

/-- **[Stacks, Tag 0F7G], case (a), for compactifications**: the map `Rk_! ⟶ Rḡ_* ∘ Rj_!` is
invertible on bounded below complexes with torsion cohomology sheaves, for an arbitrary
coefficient ring. The composition comparison is a shift-compatible transformation of exact
functors preserving lower bounds, so it suffices to treat torsion sheaves in degree zero. -/
theorem isIso_derivedRefinementComparison_app (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X))
    (hK : isTorsionPlus.{u, 0} Λ X K) : IsIso ((derivedRefinementComparison Λ g).app K) := by
  let F := etaleModuleExtensionByZero.{u, 0} Λ j.immersion
  let H := etaleModuleDirectImage.{u, 0} Λ (CompactificationOf.Hom.map g)
  have := isTriangulated_rightDerivedFunctorPlus (F ⋙ H)
  have := isTriangulated_rightDerivedFunctorPlus F
  have := isTriangulated_rightDerivedFunctorPlus H
  have := natTransCommShift_rightDerivedFunctorPlusComp F H
  obtain ⟨a, ha⟩ := K.property
  have ht : IsIso ((rightDerivedFunctorPlusComp F H).app K) := by
    refine DerivedCategory.Plus.isIso_app_of_bounded_below_of_isGE (rightDerivedFunctorPlusComp F H)
      (fun L m _ => isGE_rightDerivedFunctorPlus_obj (F ⋙ H) L m) (fun L m _ => ?_) K a
      ((DerivedCategory.Plus.isGE_ι_obj_iff K a).1 ha)
      (fun q => isIso_rightDerivedFunctorPlusComp_app_single Λ g _ (hK q))
    have := isGE_rightDerivedFunctorPlus_obj F L m
    exact isGE_rightDerivedFunctorPlus_obj H _ m
  rw [derivedRefinementComparison, NatTrans.comp_app]
  infer_instance

end Invertibility

/-! ### The isomorphism `Rf_!^k ≅ Rf_!^j` -/

section HomIso

variable {j k : CompactificationOf (Over.mk f)} (g : j ⟶ k)

/-- The comparison `Rf_!^k ⟶ Rf_!^j` on `D⁺(X_étale, Λ)` attached to a morphism of
compactifications: the map of Tag 0F7G followed by the inverse of the composition comparison
`R(j̄)_* ≅ Rḡ_* ⋙ R(k̄)_*`. -/
def derivedLowerShriekHom :
    derivedLowerShriek.{u, 0} f k Λ ⟶ derivedLowerShriek.{u, 0} f j Λ :=
  Functor.whiskerRight (derivedRefinementComparison Λ g)
      (etaleModuleDerivedDirectImage.{u, 0} Λ k.toBase) ≫
    Functor.whiskerLeft (etaleModuleDerivedExtensionByZero.{u, 0} Λ j.immersion)
      (inv (derivedBaseComparison Λ g))

/-- The component of `Rf_!^k ⟶ Rf_!^j` at `K` is `R(k̄)_*` applied to the map of Tag 0F7G at `K`,
followed by the inverse of the composition comparison at `Rj_! K`. -/
lemma derivedLowerShriekHom_app (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) :
    (derivedLowerShriekHom Λ g).app K =
      (etaleModuleDerivedDirectImage.{u, 0} Λ k.toBase).map
          ((derivedRefinementComparison Λ g).app K) ≫
        (inv (derivedBaseComparison Λ g)).app
          ((etaleModuleDerivedExtensionByZero.{u, 0} Λ j.immersion).obj K) := rfl

/-- The comparison `Rf_!^k ⟶ Rf_!^j` is invertible at a complex with torsion cohomology sheaves. -/
lemma isIso_derivedLowerShriekHom_app (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X))
    (hK : isTorsionPlus.{u, 0} Λ X K) : IsIso ((derivedLowerShriekHom Λ g).app K) := by
  have := isIso_derivedRefinementComparison_app Λ g K hK
  rw [derivedLowerShriekHom_app]
  infer_instance

/-- **The isomorphism `Rf_!^k ≅ Rf_!^j` on `D⁺_tors(X_étale, Λ)`** attached to a morphism
`g : j ⟶ k` of compactifications of `X` over `Y` ([Stacks, Tag 0F7I], the isomorphism
displayed in the proof):
`R(k̄)_* ∘ Rk_! ≅ R(k̄)_* ∘ Rḡ_* ∘ Rj_! ≅ R(j̄)_* ∘ Rj_!`, the first step being the map of
[Stacks, Tag 0F7G]. -/
def derivedLowerShriekHomIso :
    (isTorsionPlus.{u, 0} Λ X).ι ⋙ derivedLowerShriek.{u, 0} f k Λ ≅
      (isTorsionPlus.{u, 0} Λ X).ι ⋙ derivedLowerShriek.{u, 0} f j Λ :=
  haveI : IsIso (Functor.whiskerLeft (isTorsionPlus.{u, 0} Λ X).ι (derivedLowerShriekHom Λ g)) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _
      fun K => isIso_derivedLowerShriekHom_app Λ g K.obj K.property
  asIso (Functor.whiskerLeft (isTorsionPlus.{u, 0} Λ X).ι (derivedLowerShriekHom Λ g))

/-- The component of `Rf_!^k ≅ Rf_!^j` at `K` is the component of `derivedLowerShriekHom` at the
underlying complex of `K`. -/
@[simp]
lemma derivedLowerShriekHomIso_hom_app (K : (isTorsionPlus.{u, 0} Λ X).FullSubcategory) :
    (derivedLowerShriekHomIso Λ g).hom.app K = (derivedLowerShriekHom Λ g).app K.obj := rfl

end HomIso

/-! ### The cocycle law -/

section Cocycle

variable {j k l : CompactificationOf (Over.mk f)} (g : j ⟶ k) (h : k ⟶ l)

/-- The composition comparison `R(ḡh̄)_* ⟶ Rḡ_* ⋙ Rh̄_*` along a composite of morphisms of
compactifications. -/
def derivedMapComparison :
    etaleModuleDerivedDirectImage.{u, 0} Λ (CompactificationOf.Hom.map (g ≫ h)) ⟶
      etaleModuleDerivedDirectImage.{u, 0} Λ (CompactificationOf.Hom.map g) ⋙
        etaleModuleDerivedDirectImage.{u, 0} Λ (CompactificationOf.Hom.map h) :=
  (rightDerivedFunctorPlusNatIso (etaleModuleDirectImageComp.{u, 0} Λ
      (CompactificationOf.Hom.map g) (CompactificationOf.Hom.map h)
      (CompactificationOf.Hom.map (g ≫ h)) rfl)).inv ≫ rightDerivedFunctorPlusComp _ _

/-- **The cocycle law for the underived identifications** `θ`. -/
lemma refinementIso_comp :
    (refinementIso Λ h).hom ≫ Functor.whiskerRight (refinementIso Λ g).hom
      (etaleModuleDirectImage.{u, 0} Λ (CompactificationOf.Hom.map h)) =
    (refinementIso Λ (g ≫ h)).hom ≫
      Functor.whiskerLeft (etaleModuleExtensionByZero.{u, 0} Λ j.immersion)
        (etaleModuleDirectImageComp.{u, 0} Λ (CompactificationOf.Hom.map g)
          (CompactificationOf.Hom.map h) (CompactificationOf.Hom.map (g ≫ h)) rfl).inv := by
  ext F : 2
  simp only [refinementIso, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, asIso_hom]
  rw [etaleModuleRefinementComparison_comp Λ (CompactificationOf.Hom.map (g ≫ h)) rfl
    (CompactificationOf.immersion_comp_map g) (CompactificationOf.immersion_comp_map h)
    (CompactificationOf.immersion_comp_map (g ≫ h)) F]
  simp

/-- **The maps of Tag 0F7G compose**, via the comparison `R(ḡh̄)_* ⟶ Rḡ_* ⋙ Rh̄_*`; this is
[Stacks, Tag 0F7C] in this situation. -/
lemma derivedRefinementComparison_comp :
    derivedRefinementComparison Λ h ≫
        Functor.whiskerRight (derivedRefinementComparison Λ g)
          (etaleModuleDerivedDirectImage.{u, 0} Λ (CompactificationOf.Hom.map h)) =
      derivedRefinementComparison Λ (g ≫ h) ≫
        Functor.whiskerLeft (etaleModuleDerivedExtensionByZero.{u, 0} Λ j.immersion)
          (derivedMapComparison Λ g h) := by
  simpa only [derivedRefinementComparison, derivedMapComparison, Category.assoc] using
    rightDerivedFunctorPlusComp_paste (refinementIso Λ g) (refinementIso Λ h)
      (refinementIso Λ (g ≫ h)) (etaleModuleDirectImageComp.{u, 0} Λ
        (CompactificationOf.Hom.map g) (CompactificationOf.Hom.map h)
        (CompactificationOf.Hom.map (g ≫ h)) rfl) (refinementIso_comp Λ g h)

/-- **The composition comparisons of derived direct images are associative** along
`j̄ = ḡ ≫ h̄ ≫ l̄`. -/
lemma derivedBaseComparison_comp :
    derivedBaseComparison Λ (g ≫ h) ≫
        Functor.whiskerRight (derivedMapComparison Λ g h)
          (etaleModuleDerivedDirectImage.{u, 0} Λ l.toBase) =
      derivedBaseComparison Λ g ≫
        Functor.whiskerLeft (etaleModuleDerivedDirectImage.{u, 0} Λ (CompactificationOf.Hom.map g))
          (derivedBaseComparison Λ h) := by
  have hc : (etaleModuleDirectImageComp.{u, 0} Λ (CompactificationOf.Hom.map (g ≫ h)) l.toBase
        j.toBase (CompactificationOf.map_comp_toBase (g ≫ h)).symm).symm.hom ≫
        Functor.whiskerRight (etaleModuleDirectImageComp.{u, 0} Λ (CompactificationOf.Hom.map g)
          (CompactificationOf.Hom.map h) (CompactificationOf.Hom.map (g ≫ h)) rfl).symm.hom
          (etaleModuleDirectImage.{u, 0} Λ l.toBase) =
      (etaleModuleDirectImageComp.{u, 0} Λ (CompactificationOf.Hom.map g) k.toBase j.toBase
          (CompactificationOf.map_comp_toBase g).symm).symm.hom ≫
        Functor.whiskerLeft (etaleModuleDirectImage.{u, 0} Λ (CompactificationOf.Hom.map g))
          (etaleModuleDirectImageComp.{u, 0} Λ (CompactificationOf.Hom.map h) l.toBase k.toBase
            (CompactificationOf.map_comp_toBase h).symm).inv := by
    ext F : 2
    exact smallEtalePushforwardComp'_inv_app_cocycle (CompactificationOf.Hom.map g)
      (CompactificationOf.Hom.map h) l.toBase (CompactificationOf.Hom.map (g ≫ h)) rfl k.toBase
      (CompactificationOf.map_comp_toBase h).symm j.toBase
      (CompactificationOf.map_comp_toBase (g ≫ h)).symm
      (CompactificationOf.map_comp_toBase g).symm (ModuleCat.{u + 1} Λ) F
  simpa only [derivedBaseComparison, derivedMapComparison, rightDerivedFunctorPlusNatIso_symm,
    Iso.symm_hom, Category.assoc] using rightDerivedFunctorPlusComp_paste _ _ _ _ hc

/-- **The cocycle law**: the isomorphism attached to a composite of morphisms of
compactifications is the composite of the isomorphisms. -/
theorem derivedLowerShriekHomIso_comp :
    derivedLowerShriekHomIso Λ (g ≫ h) =
      derivedLowerShriekHomIso Λ h ≪≫ derivedLowerShriekHomIso Λ g := by
  refine Iso.ext (NatTrans.ext (funext fun K => ?_))
  simp only [Iso.trans_hom, NatTrans.comp_app, derivedLowerShriekHomIso_hom_app,
    derivedLowerShriekHom_app]
  have h1 := NatTrans.congr_app (derivedRefinementComparison_comp Λ g h) K.obj
  have h2 := NatTrans.congr_app (derivedBaseComparison_comp Λ g h)
    ((etaleModuleDerivedExtensionByZero.{u, 0} Λ j.immersion).obj K.obj)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h1 h2
  have hn := (inv (derivedBaseComparison Λ h)).naturality
    ((derivedRefinementComparison Λ g).app K.obj)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [Category.assoc]
  rw [← reassoc_of% hn, ← Functor.map_comp_assoc, h1, Functor.map_comp, Category.assoc]
  congr 1
  rw [← cancel_epi ((derivedBaseComparison Λ (g ≫ h)).app
    ((etaleModuleDerivedExtensionByZero.{u, 0} Λ j.immersion).obj K.obj)), reassoc_of% h2]
  simp

end Cocycle

end Stacks.EtaleCohomology
