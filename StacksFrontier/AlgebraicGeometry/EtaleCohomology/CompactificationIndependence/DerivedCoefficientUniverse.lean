module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Derived
public import
StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.ModuleCoefficientUniverse
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonCoherence
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowTransformationDevissage
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology

/-!
# `Rf_!` along a morphism of compactifications, for coefficients in any universe

Let `Λ : Type r` be a coefficient ring in an arbitrary universe, `f : X ⟶ Y` a morphism of schemes
and `g : j ⟶ k` a morphism of compactifications of `X` over `Y`, with ambient morphism
`ḡ : X̄_j ⟶ X̄_k`. The canonical isomorphism `Rf_!^k ≅ Rf_!^j` of the derived lower shriek
functors on `D⁺_tors(X_étale, Λ)` of the proof of [Stacks, Tag 0F7I] is

`R(k̄)_* ∘ Rk_! ≅ R(k̄)_* ∘ Rḡ_* ∘ Rj_! ≅ R(j̄)_* ∘ Rj_!`,

whose first step is the map of [Stacks, Tag 0F7G] and whose second step is the composition
comparison of derived direct images, and these isomorphisms turn composition of morphisms of
compactifications into composition.

## Main definitions

* `Stacks.EtaleCohomology.derivedRefinementComparisonUniv`: the map of Tag 0F7G.
* `Stacks.EtaleCohomology.derivedBaseComparisonUniv`: `R(j̄)_* ≅ Rḡ_* ⋙ R(k̄)_*`.
* `Stacks.EtaleCohomology.derivedLowerShriekHomIsoUniv`: `Rf_!^k ≅ Rf_!^j` on `D⁺_tors`.

## Main results

* `Stacks.EtaleCohomology.isIso_derivedRefinementComparisonUniv_app`: **Tag 0F7G, case (a)**:
  the map is invertible on `D⁺_tors`, for an arbitrary ring `Λ`.
* `Stacks.EtaleCohomology.derivedLowerShriekHomIsoUniv_comp`: the cocycle law.

## Implementation notes

The functors `Rf_!` live in the standard model of the derived category.

## References

* [Stacks Project, Tag 0F7G](https://stacks.math.columbia.edu/tag/0F7G)
* [Stacks Project, Tag 0F7I](https://stacks.math.columbia.edu/tag/0F7I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r


namespace Stacks.EtaleCohomology

/- `etaleModules_enoughInjectives_univZero` is stated for the coefficient ring in `Type`; instance
search would try to unify an arbitrary coefficient universe with it and fail on the universe
constraint, so it is switched off here. -/
attribute [-instance] etaleModules_enoughInjectives_univZero

attribute [local instance 2000] etaleModules_enoughInjectives

open CategoryTheory.Functor

attribute [local instance] HasDerivedCategory.standard commShiftRightDerivedFunctorPlus
  natTransCommShiftRightDerivedFunctorPlusUnit

variable (Λ : Type r) [Ring Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}

/-! ### The comparisons attached to a morphism of compactifications -/

section Comparisons

variable {j k : CompactificationOf (Over.mk f)} (g : j ⟶ k)

/-- The underived identification `θ_g : k_! ≅ ḡ_* j_!` (Tags 0F79 and 0F51). -/
def refinementIsoUniv :
    etaleModuleExtensionByZero.{u, r} Λ k.immersion ≅
      etaleModuleExtensionByZero.{u, r} Λ j.immersion ⋙
        etaleModuleDirectImage.{u, r} Λ (CompactificationOf.Hom.map g) :=
  haveI := isIso_etaleModuleRefinementComparison_univ Λ (CompactificationOf.immersion_comp_map g)
  asIso (etaleModuleRefinementComparison Λ (CompactificationOf.immersion_comp_map g))

/-- **The map `Rk_! ⟶ Rḡ_* ∘ Rj_!` of [Stacks, Tag 0F7G]**: the invariance comparison of `θ_g`
followed by the composition comparison of [Stacks, Tag 05T2]. -/
def derivedRefinementComparisonUniv :
    etaleModuleDerivedExtensionByZero.{u, r} Λ k.immersion ⟶
      etaleModuleDerivedExtensionByZero.{u, r} Λ j.immersion ⋙
        etaleModuleDerivedDirectImage.{u, r} Λ (CompactificationOf.Hom.map g) :=
  (rightDerivedFunctorPlusNatIso (refinementIsoUniv Λ g)).hom ≫ rightDerivedFunctorPlusComp _ _

/-- The composition comparison `R(j̄)_* ⟶ Rḡ_* ⋙ R(k̄)_*` of derived direct images. -/
def derivedBaseComparisonUniv :
    etaleModuleDerivedDirectImage.{u, r} Λ j.toBase ⟶
      etaleModuleDerivedDirectImage.{u, r} Λ (CompactificationOf.Hom.map g) ⋙
        etaleModuleDerivedDirectImage.{u, r} Λ k.toBase :=
  (rightDerivedFunctorPlusNatIso (etaleModuleDirectImageComp.{u, r} Λ
      (CompactificationOf.Hom.map g) k.toBase j.toBase
      (CompactificationOf.map_comp_toBase g).symm)).inv ≫ rightDerivedFunctorPlusComp _ _

/-- The composition comparison `R(j̄)_* ⟶ Rḡ_* ⋙ R(k̄)_*` is an isomorphism. -/
instance isIso_derivedBaseComparisonUniv : IsIso (derivedBaseComparisonUniv Λ g) := by
  dsimp only [derivedBaseComparisonUniv]
  infer_instance

end Comparisons

/-! ### Tag 0F7G, case (a) -/

section Invertibility

/-- The unit `rightDerivedFunctorPlusUnith` (whose definition is not exposed) followed by the
comparison with the `totalRightDerived` presentation is the unit of `totalRightDerived`. -/
private lemma totalRightDerivedUnit_app_eq_derivedCoefUniv {D E : Type*} [Category* D]
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
private lemma rightAcyclic_iff_isIso_unith_app_derivedCoefUniv {D E : Type*}
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
  rw [totalRightDerivedUnit_app_eq_derivedCoefUniv]
  exact isIso_comp_right_iff _ _

variable {j k : CompactificationOf (Over.mk f)} (g : j ⟶ k)

/-- The composition comparison `R(ḡ_* ∘ j_!) ⟶ Rj_! ⋙ Rḡ_*` is invertible at a torsion sheaf
placed in degree zero. -/
lemma isIso_rightDerivedFunctorPlusComp_app_single_univ (M : EtaleModules.{u, r} Λ X)
    (hM : IsTorsionEtaleModule.{u, r} Λ X M) :
    IsIso ((rightDerivedFunctorPlusComp (etaleModuleExtensionByZero.{u, r} Λ j.immersion)
      (etaleModuleDirectImage.{u, r} Λ (CompactificationOf.Hom.map g))).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M)) := by
  let F := etaleModuleExtensionByZero.{u, r} Λ j.immersion
  let H := etaleModuleDirectImage.{u, r} Λ (CompactificationOf.Hom.map g)
  let Xs := (HomotopyCategory.Plus.singleFunctor (EtaleModules.{u, r} Λ X) 0).obj M
  have hF : IsIso (F.rightDerivedFunctorPlusUnith.app Xs) :=
    (rightAcyclic_iff_isIso_unith_app_derivedCoefUniv F M).1 (rightAcyclic_of_exact F M)
  have hK : IsIso ((etaleModuleExtensionByZero.{u, r} Λ k.immersion).rightDerivedFunctorPlusUnith.app
      Xs) := (rightAcyclic_iff_isIso_unith_app_derivedCoefUniv _ M).1 (rightAcyclic_of_exact _ M)
  have hFH : IsIso ((F ⋙ H).rightDerivedFunctorPlusUnith.app Xs) := by
    have w := rightDerivedFunctorPlusNatIso_hom_fac_app (refinementIsoUniv Λ g) Xs
    exact IsIso.of_isIso_fac_left w.symm
  have hac : H.rightAcyclic (F.obj M) :=
    (Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived H (F.obj M)).2
      fun p hp => isZero_rightDerived_etaleModuleDirectImage_extensionByZero_univ Λ
        (CompactificationOf.immersion_comp_map g) M hM p hp
  have hH : IsIso (H.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj Xs)) := by
    let e := Stacks.Cohomology.LerayDegreewise.mapHomotopyCategoryPlusSingleObjIso F 0 M
    have hn := H.rightDerivedFunctorPlusUnith.naturality e.hom
    have : IsIso (H.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.singleFunctor _ 0).obj (F.obj M))) :=
      (rightAcyclic_iff_isIso_unith_app_derivedCoefUniv H (F.obj M)).1 hac
    exact IsIso.of_isIso_fac_right hn.symm
  have w := unit_comp_rightDerivedFunctorPlusComp_app F H Xs
  have : IsIso (H.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj Xs) ≫
      H.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app Xs)) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ hH (Functor.map_isIso _ _)
  have key : IsIso ((F ⋙ H).rightDerivedFunctorPlusUnith.app Xs ≫
      (rightDerivedFunctorPlusComp F H).app (DerivedCategory.Plus.Qh.obj Xs)) := by
    rwa [w]
  have ht : IsIso ((rightDerivedFunctorPlusComp F H).app (DerivedCategory.Plus.Qh.obj Xs)) :=
    IsIso.of_isIso_comp_left ((F ⋙ H).rightDerivedFunctorPlusUnith.app Xs) _
  let e := (DerivedCategory.Plus.singleFunctorIsoCompQh (EtaleModules.{u, r} Λ X) 0).app M
  have ht' : IsIso ((rightDerivedFunctorPlusComp F H).app
      ((HomotopyCategory.Plus.singleFunctor _ 0 ⋙ DerivedCategory.Plus.Qh).obj M)) := ht
  exact (NatTrans.isIso_app_iff_of_iso _ e).2 ht'

/-- **[Stacks, Tag 0F7G], case (a), for compactifications**: the map `Rk_! ⟶ Rḡ_* ∘ Rj_!` is
invertible on bounded below complexes with torsion cohomology sheaves, for an arbitrary
coefficient ring. -/
theorem isIso_derivedRefinementComparisonUniv_app
    (K : DerivedCategory.Plus (EtaleModules.{u, r} Λ X))
    (hK : isTorsionPlus.{u, r} Λ X K) : IsIso ((derivedRefinementComparisonUniv Λ g).app K) := by
  let F := etaleModuleExtensionByZero.{u, r} Λ j.immersion
  let H := etaleModuleDirectImage.{u, r} Λ (CompactificationOf.Hom.map g)
  have := isTriangulated_rightDerivedFunctorPlus (F ⋙ H)
  have := isTriangulated_rightDerivedFunctorPlus F
  have := isTriangulated_rightDerivedFunctorPlus H
  have := natTransCommShift_rightDerivedFunctorPlusComp F H
  obtain ⟨a, ha⟩ := K.property
  have hGE : K.IsGE a := (DerivedCategory.Plus.isGE_ι_obj_iff K a).1 ha
  have ht : IsIso ((rightDerivedFunctorPlusComp F H).app K) := by
    refine DerivedCategory.Plus.isIso_app_of_bounded_below_of_isGE
      (rightDerivedFunctorPlusComp F H) (fun L m hL => ?_) (fun L m hL => ?_) K a hGE
      (fun q => isIso_rightDerivedFunctorPlusComp_app_single_univ Λ g _ (hK q))
    · exact isGE_rightDerivedFunctorPlus_obj (F ⋙ H) L m
    · have := isGE_rightDerivedFunctorPlus_obj F L m
      exact isGE_rightDerivedFunctorPlus_obj H _ m
  rw [derivedRefinementComparisonUniv, NatTrans.comp_app]
  infer_instance

end Invertibility

/-! ### The isomorphism `Rf_!^k ≅ Rf_!^j` -/

section HomIso

variable {j k : CompactificationOf (Over.mk f)} (g : j ⟶ k)

/-- The comparison `Rf_!^k ⟶ Rf_!^j` on `D⁺(X_étale, Λ)` attached to a morphism of
compactifications: the map of Tag 0F7G followed by the inverse of the composition comparison
`R(j̄)_* ≅ Rḡ_* ⋙ R(k̄)_*`. -/
def derivedLowerShriekHomUniv :
    derivedLowerShriek.{u, r} f k Λ ⟶ derivedLowerShriek.{u, r} f j Λ :=
  Functor.whiskerRight (derivedRefinementComparisonUniv Λ g)
      (etaleModuleDerivedDirectImage.{u, r} Λ k.toBase) ≫
    Functor.whiskerLeft (etaleModuleDerivedExtensionByZero.{u, r} Λ j.immersion)
      (inv (derivedBaseComparisonUniv Λ g))

/-- The component of `Rf_!^k ⟶ Rf_!^j` at `K` is `R(k̄)_*` of the map of Tag 0F7G at `K`, followed
by the inverse of the composition comparison at `Rj_! K`. -/
lemma derivedLowerShriekHomUniv_app (K : DerivedCategory.Plus (EtaleModules.{u, r} Λ X)) :
    (derivedLowerShriekHomUniv Λ g).app K =
      (etaleModuleDerivedDirectImage.{u, r} Λ k.toBase).map
          ((derivedRefinementComparisonUniv Λ g).app K) ≫
        (inv (derivedBaseComparisonUniv Λ g)).app
          ((etaleModuleDerivedExtensionByZero.{u, r} Λ j.immersion).obj K) := rfl

/-- The comparison `Rf_!^k ⟶ Rf_!^j` is invertible at every bounded below complex with torsion
cohomology sheaves. -/
lemma isIso_derivedLowerShriekHomUniv_app (K : DerivedCategory.Plus (EtaleModules.{u, r} Λ X))
    (hK : isTorsionPlus.{u, r} Λ X K) : IsIso ((derivedLowerShriekHomUniv Λ g).app K) := by
  have := isIso_derivedRefinementComparisonUniv_app Λ g K hK
  rw [derivedLowerShriekHomUniv_app]
  infer_instance

/-- **The isomorphism `Rf_!^k ≅ Rf_!^j` on `D⁺_tors(X_étale, Λ)`** attached to a morphism
`g : j ⟶ k` of compactifications of `X` over `Y` ([Stacks, Tag 0F7I], the isomorphism
displayed in the proof):
`R(k̄)_* ∘ Rk_! ≅ R(k̄)_* ∘ Rḡ_* ∘ Rj_! ≅ R(j̄)_* ∘ Rj_!`, the first step being the map of
[Stacks, Tag 0F7G]. -/
def derivedLowerShriekHomIsoUniv :
    (isTorsionPlus.{u, r} Λ X).ι ⋙ derivedLowerShriek.{u, r} f k Λ ≅
      (isTorsionPlus.{u, r} Λ X).ι ⋙ derivedLowerShriek.{u, r} f j Λ :=
  haveI : IsIso (Functor.whiskerLeft (isTorsionPlus.{u, r} Λ X).ι
      (derivedLowerShriekHomUniv Λ g)) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _
      fun K => isIso_derivedLowerShriekHomUniv_app Λ g K.obj K.property
  asIso (Functor.whiskerLeft (isTorsionPlus.{u, r} Λ X).ι (derivedLowerShriekHomUniv Λ g))

/-- The component of `Rf_!^k ≅ Rf_!^j` at `K` is the component of the comparison
`Rf_!^k ⟶ Rf_!^j` at the underlying complex of `K`. -/
@[simp]
lemma derivedLowerShriekHomIsoUniv_hom_app (K : (isTorsionPlus.{u, r} Λ X).FullSubcategory) :
    (derivedLowerShriekHomIsoUniv Λ g).hom.app K = (derivedLowerShriekHomUniv Λ g).app K.obj := rfl

end HomIso

/-! ### The cocycle law -/

section Cocycle

variable {j k l : CompactificationOf (Over.mk f)} (g : j ⟶ k) (h : k ⟶ l)

/-- The composition comparison `R(ḡh̄)_* ⟶ Rḡ_* ⋙ Rh̄_*` along a composite of morphisms of
compactifications. -/
def derivedMapComparisonUniv :
    etaleModuleDerivedDirectImage.{u, r} Λ (CompactificationOf.Hom.map (g ≫ h)) ⟶
      etaleModuleDerivedDirectImage.{u, r} Λ (CompactificationOf.Hom.map g) ⋙
        etaleModuleDerivedDirectImage.{u, r} Λ (CompactificationOf.Hom.map h) :=
  (rightDerivedFunctorPlusNatIso (etaleModuleDirectImageComp.{u, r} Λ
      (CompactificationOf.Hom.map g) (CompactificationOf.Hom.map h)
      (CompactificationOf.Hom.map (g ≫ h)) rfl)).inv ≫ rightDerivedFunctorPlusComp _ _

/-- **The cocycle law for the underived identifications** `θ`. -/
lemma refinementIsoUniv_comp :
    (refinementIsoUniv Λ h).hom ≫ Functor.whiskerRight (refinementIsoUniv Λ g).hom
      (etaleModuleDirectImage.{u, r} Λ (CompactificationOf.Hom.map h)) =
    (refinementIsoUniv Λ (g ≫ h)).hom ≫
      Functor.whiskerLeft (etaleModuleExtensionByZero.{u, r} Λ j.immersion)
        (etaleModuleDirectImageComp.{u, r} Λ (CompactificationOf.Hom.map g)
          (CompactificationOf.Hom.map h) (CompactificationOf.Hom.map (g ≫ h)) rfl).inv := by
  ext F : 2
  have := etaleModuleRefinementComparison_comp Λ (CompactificationOf.Hom.map (g ≫ h)) rfl
    (CompactificationOf.immersion_comp_map g) (CompactificationOf.immersion_comp_map h)
    (CompactificationOf.immersion_comp_map (g ≫ h)) F
  simp only [refinementIsoUniv, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, asIso_hom]
  rw [this]
  simp

/-- **The maps of Tag 0F7G compose**, via the comparison `R(ḡh̄)_* ⟶ Rḡ_* ⋙ Rh̄_*`; this is
[Stacks, Tag 0F7C] in this situation. -/
lemma derivedRefinementComparisonUniv_comp :
    derivedRefinementComparisonUniv Λ h ≫
        Functor.whiskerRight (derivedRefinementComparisonUniv Λ g)
          (etaleModuleDerivedDirectImage.{u, r} Λ (CompactificationOf.Hom.map h)) =
      derivedRefinementComparisonUniv Λ (g ≫ h) ≫
        Functor.whiskerLeft (etaleModuleDerivedExtensionByZero.{u, r} Λ j.immersion)
          (derivedMapComparisonUniv Λ g h) := by
  have hc := refinementIsoUniv_comp Λ g h
  have := rightDerivedFunctorPlusComp_paste (refinementIsoUniv Λ g) (refinementIsoUniv Λ h)
    (refinementIsoUniv Λ (g ≫ h)) (etaleModuleDirectImageComp.{u, r} Λ
      (CompactificationOf.Hom.map g) (CompactificationOf.Hom.map h)
      (CompactificationOf.Hom.map (g ≫ h)) rfl) hc
  simpa only [derivedRefinementComparisonUniv, derivedMapComparisonUniv, Category.assoc] using this

/-- **The composition comparisons of derived direct images are associative** along
`j̄ = ḡ ≫ h̄ ≫ l̄`. -/
lemma derivedBaseComparisonUniv_comp :
    derivedBaseComparisonUniv Λ (g ≫ h) ≫
        Functor.whiskerRight (derivedMapComparisonUniv Λ g h)
          (etaleModuleDerivedDirectImage.{u, r} Λ l.toBase) =
      derivedBaseComparisonUniv Λ g ≫
        Functor.whiskerLeft (etaleModuleDerivedDirectImage.{u, r} Λ (CompactificationOf.Hom.map g))
          (derivedBaseComparisonUniv Λ h) := by
  have hc : (etaleModuleDirectImageComp.{u, r} Λ (CompactificationOf.Hom.map (g ≫ h)) l.toBase
        j.toBase (CompactificationOf.map_comp_toBase (g ≫ h)).symm).symm.hom ≫
        Functor.whiskerRight (etaleModuleDirectImageComp.{u, r} Λ (CompactificationOf.Hom.map g)
          (CompactificationOf.Hom.map h) (CompactificationOf.Hom.map (g ≫ h)) rfl).symm.hom
          (etaleModuleDirectImage.{u, r} Λ l.toBase) =
      (etaleModuleDirectImageComp.{u, r} Λ (CompactificationOf.Hom.map g) k.toBase j.toBase
          (CompactificationOf.map_comp_toBase g).symm).symm.hom ≫
        Functor.whiskerLeft (etaleModuleDirectImage.{u, r} Λ (CompactificationOf.Hom.map g))
          (etaleModuleDirectImageComp.{u, r} Λ (CompactificationOf.Hom.map h) l.toBase k.toBase
            (CompactificationOf.map_comp_toBase h).symm).inv := by
    ext F : 2
    exact smallEtalePushforwardComp'_inv_app_cocycle (CompactificationOf.Hom.map g)
      (CompactificationOf.Hom.map h) l.toBase (CompactificationOf.Hom.map (g ≫ h)) rfl k.toBase
      (CompactificationOf.map_comp_toBase h).symm j.toBase
      (CompactificationOf.map_comp_toBase (g ≫ h)).symm
      (CompactificationOf.map_comp_toBase g).symm (ModuleCat.{max (u + 1) r} Λ) F
  have := rightDerivedFunctorPlusComp_paste _ _ _ _ hc
  simpa only [derivedBaseComparisonUniv, derivedMapComparisonUniv,
    rightDerivedFunctorPlusNatIso_symm,
    Iso.symm_hom, Category.assoc] using this

/-- **The cocycle law**: the isomorphism attached to a composite of morphisms of
compactifications is the composite of the isomorphisms. -/
theorem derivedLowerShriekHomIsoUniv_comp :
    derivedLowerShriekHomIsoUniv Λ (g ≫ h) =
      derivedLowerShriekHomIsoUniv Λ h ≪≫ derivedLowerShriekHomIsoUniv Λ g := by
  apply Iso.ext
  refine NatTrans.ext (funext fun K => ?_)
  simp only [Iso.trans_hom, NatTrans.comp_app, derivedLowerShriekHomIsoUniv_hom_app,
    derivedLowerShriekHomUniv_app]
  have h1 := congrArg (fun t => NatTrans.app t K.obj) (derivedRefinementComparisonUniv_comp Λ g h)
  have h2 := congrArg (fun t => NatTrans.app t
    ((etaleModuleDerivedExtensionByZero.{u, r} Λ j.immersion).obj K.obj))
    (derivedBaseComparisonUniv_comp Λ g h)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h1 h2
  have hn := (inv (derivedBaseComparisonUniv Λ h)).naturality
    ((derivedRefinementComparisonUniv Λ g).app K.obj)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [Category.assoc]
  rw [← reassoc_of% hn, ← Functor.map_comp_assoc, h1, Functor.map_comp, Category.assoc]
  congr 1
  rw [← cancel_epi ((derivedBaseComparisonUniv Λ (g ≫ h)).app
    ((etaleModuleDerivedExtensionByZero.{u, r} Λ j.immersion).obj K.obj)), reassoc_of% h2]
  simp

end Cocycle

end Stacks.EtaleCohomology
