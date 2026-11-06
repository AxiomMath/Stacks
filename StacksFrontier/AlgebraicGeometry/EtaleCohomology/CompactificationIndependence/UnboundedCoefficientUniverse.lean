module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.DerivedCoefficientUniverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Unbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.BoundednessUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageCompositionUnbounded
public import StacksFrontier.CategoryTheory.Functor.Derived.CompComparisonPaste
public import StacksFrontier.Homology.Injectives.KInjective.RightDerivedCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Bounded

/-!
# Unbounded `Rf_!` along a morphism of compactifications, for coefficients in any universe

Let `Λ : Type r` be a torsion coefficient ring in an arbitrary universe. For `f : X ⟶ Y` with `Y`
quasi-compact and `g : j ⟶ k` a morphism of compactifications of `X` over `Y`, this file
constructs the canonical isomorphism `Rf_!^k ≅ Rf_!^j` of the derived lower shriek functors
`Stacks.EtaleCohomology.derivedLowerShriekUnbounded` on the unbounded derived categories and
proves its cocycle law.

The map `Rk_! ⟶ Rḡ_* ∘ Rj_!` of [Stacks, Tag 0F7G] is invertible on the whole of `D(X_étale, Λ)`
(case (b)).

## Main definitions

* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedHomIsoUniv`.

## Main results

* `isIso_etaleModuleDerivedDirectImageUnboundedUnit_app_of_rightAcyclic_univ`: complexes of
  `a_*`-acyclic sheaves compute `Ra_*`, for `a` proper and `Λ` torsion.
* `Stacks.EtaleCohomology.isIso_derivedRefinementComparisonUnboundedUniv`: Tag 0F7G, case (b).
* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedHomIsoUniv_comp`: the cocycle law.

## References

* [Stacks Project, Tag 0F7G](https://stacks.math.columbia.edu/tag/0F7G)
* [Stacks Project, Tag 0F7I](https://stacks.math.columbia.edu/tag/0F7I)
* [Stacks Project, Tag 07K7](https://stacks.math.columbia.edu/tag/07K7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.DerivedBaseChange

universe u r

namespace Stacks.EtaleCohomology

/- `etaleModules_enoughInjectives_univZero` is stated for the coefficient ring in `Type`; instance
search would try to unify an arbitrary coefficient universe with it and fail on the universe
constraint, so it is switched off here. -/
attribute [-instance] etaleModules_enoughInjectives_univZero

attribute [local instance 2000] etaleModules_enoughInjectives

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type r) [Ring Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- The unit of `RF` (Mathlib's `rightDerivedFunctorPlusUnith`, whose definition is not exposed)
is invertible at `K` exactly when the unit of `Functor.totalRightDerived` is: both are units of
right derived functors of the same functor. -/
private lemma isIso_rightDerivedFunctorPlusUnith_app_iff_unboundedCoefficientUniverse
    {D : Type*} {E : Type*}
    [Category* D] [Category* E] [Abelian D] [Abelian E] [HasDerivedCategory D]
    [HasDerivedCategory E] (G : D ⥤ E) [G.Additive]
    [EnoughInjectives D] (K : HomotopyCategory.Plus D) :
    IsIso (G.rightDerivedFunctorPlusUnith.app K) ↔
      IsIso (((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso D)).app K) := by
  have : IsIso (G.rightDerivedFunctorPlus.rightDerivedDesc G.rightDerivedFunctorPlusUnith
      (HomotopyCategory.Plus.quasiIso D) _
      ((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso D))) :=
    (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc _ _ _ _ _).1 inferInstance
  rw [← Functor.rightDerived_fac_app G.rightDerivedFunctorPlus G.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso D) _
    ((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
      DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso D)) K]
  exact (isIso_comp_right_iff _ _).symm

/-! ### Units of unbounded derived functors -/

section Units

include Λ in
/-- Every sheaf of modules over a torsion ring is torsion. -/
lemma isTorsionEtaleModule_of_nsmul_eq_zero_univ {Z : Scheme.{u}} (m : ℕ) (hm : 0 < m)
    (hΛ : (m : Λ) = 0) (M : EtaleModules.{u, r} Λ Z) : IsTorsionEtaleModule.{u, r} Λ Z M := by
  intro U x
  refine ⟨⊤, Z.smallEtaleTopology.top_mem U, fun V g _ => ⟨m, hm, ?_⟩⟩
  rw [← Nat.cast_smul_eq_nsmul Λ, hΛ, zero_smul]

/-- A natural transformation between functors out of the unbounded derived category is an
isomorphism as soon as it is invertible at every K-injective complex. -/
lemma isIso_app_Q_of_isKInjective_univ {A B : Scheme.{u}}
    {G₁ G₂ : DerivedCategory (EtaleModules.{u, r} Λ A) ⥤ DerivedCategory (EtaleModules.{u, r} Λ B)}
    (τ : G₁ ⟶ G₂)
    (h : ∀ (I : CochainComplex (EtaleModules.{u, r} Λ A) ℤ), I.IsKInjective →
      IsIso (τ.app (DerivedCategory.Q.obj I))) : IsIso τ := by
  apply Stacks.Injectives.isIso_natTrans_of_kInjective
  intro I hI
  exact (NatTrans.isIso_app_iff_of_iso τ
    ((DerivedCategory.quotientCompQhIso (EtaleModules.{u, r} Λ A)).app I)).2 (h I hI)

/-- **Complexes of `a_*`-acyclic sheaves compute `Ra_*` on the unbounded derived category**, for
`a` proper over a quasi-compact scheme and a torsion ring `Λ`. -/
lemma isIso_etaleModuleDerivedDirectImageUnboundedUnit_app_of_rightAcyclic_univ {A B : Scheme.{u}}
    (a : A ⟶ B) [IsProper a] [CompactSpace B] (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0)
    (L : CochainComplex (EtaleModules.{u, r} Λ A) ℤ)
    (hL : ∀ i, (etaleModuleDirectImage.{u, r} Λ a).rightAcyclic (L.X i)) :
    IsIso ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ a).app L) := by
  obtain ⟨d, hd⟩ :=
    @AlgebraicGeometry.exists_topologicalKrullDim_fiber_le _ _ a
      (IsProper.toLocallyOfFiniteType (f := a)) (quasiCompact_of_isProper a) ‹_›
  let F := etaleModuleDirectImage.{u, r} Λ a
  let RF := etaleModuleDerivedDirectImageUnbounded.{u, r} Λ a
  let α := Stacks.Injectives.KInjectiveResolution.homotopyCategoryUnit F RF
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ a)
  have hcomp : ∀ Z : EtaleModules.{u, r} Λ A, F.rightAcyclic Z →
      (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso _) ((HomotopyCategory.Plus.singleFunctor _ 0).obj Z) := by
    intro Z hZ
    have : (HomotopyCategory.Plus.quasiIso
        (EtaleModules.{u, r} Λ A)).HasLeftCalculusOfFractions := by
      rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW]; infer_instance
    rw [Functor.computesRightDerived_iff_isIso_app _ DerivedCategory.Plus.Qh
      F.rightDerivedFunctorPlus (HomotopyCategory.Plus.quasiIso _) F.rightDerivedFunctorPlusUnith _
      (fun K => ?_)]
    · exact (isIso_rightDerivedFunctorPlusUnith_app_iff_unboundedCoefficientUniverse F _).2 hZ
    · let r : (HomotopyCategory.Plus.localizerMorphism _).RightResolution K := Classical.arbitrary _
      exact ⟨_, r.w, r.hw, inferInstance⟩
  have h07K7 := Functor.hasRightDerivedFunctor_of_isZero_rightDerived F
    F.rightDerivedFunctorPlus F.rightDerivedFunctorPlusUnith
    (fun Z => (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
      (HomotopyCategory.Plus.quasiIso _) ((HomotopyCategory.Plus.singleFunctor _ 0).obj Z))
    (fun _ => Iff.rfl)
    (fun Z => ⟨Injective.under Z, Injective.ι Z, inferInstance,
      computesRightDerived_singleFunctor_of_injective F _⟩)
    (2 * d + 1) (fun Z => by
      have h := Stacks.BoundedCohomologicalDimension.isLE_rightDerivedFunctorPlus_single F Z
        (2 * d : ℕ) 0 (fun p hp => isZero_rightDerived_etaleModuleDirectImage_of_isProper_univ Λ
          a d hd _ (isTorsionEtaleModule_of_nsmul_eq_zero_univ Λ m hm hΛ _)
          p (by exact_mod_cast hp))
      exact DerivedCategory.isZero_of_isLE _ (0 + (2 * d : ℕ)) _ (by push_cast; omega))
  obtain ⟨-, -, hRF⟩ := h07K7
  obtain ⟨hL', -⟩ := hRF RF α
  have hα := hL' L (fun i => hcomp _ (hL i))
  rw [Stacks.Injectives.KInjectiveResolution.homotopyCategoryUnit_app_quotient,
    ← Category.assoc] at hα
  have : IsIso ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ a).app L ≫
      RF.map ((DerivedCategory.quotientCompQhIso _).inv.app L)) :=
    IsIso.of_isIso_comp_left (DerivedCategory.Qh.map
      ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app L) ≫
        (DerivedCategory.quotientCompQhIso _).hom.app _) _
  exact IsIso.of_isIso_comp_right _ (RF.map ((DerivedCategory.quotientCompQhIso _).inv.app L))

end Units

/-! ### The comparisons attached to a morphism of compactifications -/

section Comparisons

variable {j k : CompactificationOf (Over.mk f)} (g : j ⟶ k)

/-- **The map `Rk_! ⟶ Rḡ_* ∘ Rj_!` of [Stacks, Tag 0F7G]** on unbounded derived categories: the
composition comparison of [Stacks, Tag 05T2] for the underived identification
`θ_g : k_! ≅ ḡ_* j_!`. -/
def derivedRefinementComparisonUnboundedUniv :
    etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ k.immersion ⟶
      etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j.immersion ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, r} Λ (CompactificationOf.Hom.map g) :=
  compComparison (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, r} Λ j.immersion)
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ (CompactificationOf.Hom.map g))
    (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, r} Λ k.immersion)
    (Functor.mapHomologicalComplexCompIso (refinementIsoUniv Λ g).symm (ComplexShape.up ℤ))

/-- The composition comparison `R(j̄)_* ⟶ Rḡ_* ⋙ R(k̄)_*` of unbounded derived direct images. -/
def derivedBaseComparisonUnboundedUniv :
    etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j.toBase ⟶
      etaleModuleDerivedDirectImageUnbounded.{u, r} Λ (CompactificationOf.Hom.map g) ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, r} Λ k.toBase :=
  compComparison (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ (CompactificationOf.Hom.map g))
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ k.toBase)
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ j.toBase)
    (Functor.mapHomologicalComplexCompIso (etaleModuleDirectImageComp.{u, r} Λ
      (CompactificationOf.Hom.map g) k.toBase j.toBase
      (CompactificationOf.map_comp_toBase g).symm) (ComplexShape.up ℤ))

/-- The composition comparison of unbounded derived direct images is invertible. -/
instance isIso_derivedBaseComparisonUnboundedUniv :
    IsIso (derivedBaseComparisonUnboundedUniv Λ g) := by
  refine isIso_app_Q_of_isKInjective_univ Λ _ fun I hI => ?_
  have h := compComparison_fac_app (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ (CompactificationOf.Hom.map g))
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ k.toBase)
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ j.toBase)
    (Functor.mapHomologicalComplexCompIso (etaleModuleDirectImageComp.{u, r} Λ
      (CompactificationOf.Hom.map g) k.toBase j.toBase
      (CompactificationOf.map_comp_toBase g).symm) (ComplexShape.up ℤ)) I
  have := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app.{u, r} Λ j.toBase I hI
  have := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app.{u, r} Λ
    (CompactificationOf.Hom.map g) I hI
  have := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app.{u, r} Λ k.toBase _
    (isKInjective_etaleModuleDirectImage_mapHomologicalComplex Λ
      (CompactificationOf.Hom.map g) I hI)
  exact IsIso.of_isIso_fac_left h

/-- **[Stacks, Tag 0F7G], case (b), for compactifications**: over a torsion ring the map
`Rk_! ⟶ Rḡ_* ∘ Rj_!` is invertible on the whole unbounded derived category. -/
theorem isIso_derivedRefinementComparisonUnboundedUniv [CompactSpace Y] (m : ℕ) (hm : 0 < m)
    (hΛ : (m : Λ) = 0) : IsIso (derivedRefinementComparisonUnboundedUniv Λ g) := by
  refine isIso_app_Q_of_isKInjective_univ Λ _ fun I hI => ?_
  have h := compComparison_fac_app (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, r} Λ j.immersion)
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ (CompactificationOf.Hom.map g))
    (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, r} Λ k.immersion)
    (Functor.mapHomologicalComplexCompIso (refinementIsoUniv Λ g).symm (ComplexShape.up ℤ)) I
  have := isIso_etaleModuleDerivedExtensionByZeroUnboundedUnit_app.{u, r} Λ k.immersion I hI
  have := isIso_etaleModuleDerivedExtensionByZeroUnboundedUnit_app.{u, r} Λ j.immersion I hI
  have : CompactSpace k.space := QuasiCompact.compactSpace_of_compactSpace k.toBase
  have := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app_of_rightAcyclic_univ Λ
    (CompactificationOf.Hom.map g) m hm hΛ
    (((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I) fun i =>
      (Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived _ _).2
        fun p hp => isZero_rightDerived_etaleModuleDirectImage_extensionByZero_univ Λ
          (CompactificationOf.immersion_comp_map g) (I.X i)
          (isTorsionEtaleModule_of_nsmul_eq_zero_univ Λ m hm hΛ _) p hp
  exact IsIso.of_isIso_fac_left h

end Comparisons

/-! ### The isomorphism `Rf_!^k ≅ Rf_!^j` on unbounded derived categories -/

section HomIso

variable {j k : CompactificationOf (Over.mk f)} (g : j ⟶ k)

/-- The comparison `Rf_!^k ⟶ Rf_!^j` on `D(X_étale, Λ)` attached to a morphism of
compactifications. -/
def derivedLowerShriekUnboundedHomUniv :
    derivedLowerShriekUnbounded.{u, r} f k Λ ⟶ derivedLowerShriekUnbounded.{u, r} f j Λ :=
  Functor.whiskerRight (derivedRefinementComparisonUnboundedUniv Λ g)
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ k.toBase) ≫
    Functor.whiskerLeft (etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j.immersion)
      (inv (derivedBaseComparisonUnboundedUniv Λ g))

/-- The component of `Rf_!^k ⟶ Rf_!^j` at `K` is `R(k̄)_*` of the map of Tag 0F7G at `K`, followed
by the inverse of the composition comparison at `Rj_! K`. -/
lemma derivedLowerShriekUnboundedHomUniv_app (K : DerivedCategory (EtaleModules.{u, r} Λ X)) :
    (derivedLowerShriekUnboundedHomUniv Λ g).app K =
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ k.toBase).map
          ((derivedRefinementComparisonUnboundedUniv Λ g).app K) ≫
        (inv (derivedBaseComparisonUnboundedUniv Λ g)).app
          ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j.immersion).obj K) := rfl

/-- **The isomorphism `Rf_!^k ≅ Rf_!^j` on `D(X_étale, Λ)` for a torsion ring `Λ`** attached to
a morphism `g : j ⟶ k` of compactifications ([Stacks, Tag 0F7I], the isomorphism displayed in
the proof), the first step being the map of [Stacks, Tag 0F7G]. -/
def derivedLowerShriekUnboundedHomIsoUniv [CompactSpace Y] (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) :
    derivedLowerShriekUnbounded.{u, r} f k Λ ≅ derivedLowerShriekUnbounded.{u, r} f j Λ :=
  haveI : IsIso (derivedRefinementComparisonUnboundedUniv Λ g) :=
    isIso_derivedRefinementComparisonUnboundedUniv Λ g hΛ.choose hΛ.choose_spec.1 hΛ.choose_spec.2
  haveI : IsIso (derivedLowerShriekUnboundedHomUniv Λ g) := by
    dsimp only [derivedLowerShriekUnboundedHomUniv]
    infer_instance
  asIso (derivedLowerShriekUnboundedHomUniv Λ g)

/-- The forward map of `derivedLowerShriekUnboundedHomIsoUniv` is
`derivedLowerShriekUnboundedHomUniv`. -/
@[simp]
lemma derivedLowerShriekUnboundedHomIsoUniv_hom [CompactSpace Y]
    (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) :
    (derivedLowerShriekUnboundedHomIsoUniv Λ g hΛ).hom =
      derivedLowerShriekUnboundedHomUniv Λ g := rfl

end HomIso

/-! ### The cocycle law -/

section Cocycle

variable {j k l : CompactificationOf (Over.mk f)} (g : j ⟶ k) (h : k ⟶ l)

/-- The composition comparison `R(ḡh̄)_* ⟶ Rḡ_* ⋙ Rh̄_*` of unbounded derived direct images. -/
def derivedMapComparisonUnboundedUniv :
    etaleModuleDerivedDirectImageUnbounded.{u, r} Λ (CompactificationOf.Hom.map (g ≫ h)) ⟶
      etaleModuleDerivedDirectImageUnbounded.{u, r} Λ (CompactificationOf.Hom.map g) ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, r} Λ (CompactificationOf.Hom.map h) :=
  compComparison (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ (CompactificationOf.Hom.map g))
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ (CompactificationOf.Hom.map h))
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ (CompactificationOf.Hom.map (g ≫ h)))
    (Functor.mapHomologicalComplexCompIso (etaleModuleDirectImageComp.{u, r} Λ
      (CompactificationOf.Hom.map g) (CompactificationOf.Hom.map h)
      (CompactificationOf.Hom.map (g ≫ h)) rfl) (ComplexShape.up ℤ))

/-- **The maps of Tag 0F7G compose**, on unbounded derived categories. -/
lemma derivedRefinementComparisonUnboundedUniv_comp :
    derivedRefinementComparisonUnboundedUniv Λ h ≫
        Functor.whiskerRight (derivedRefinementComparisonUnboundedUniv Λ g)
          (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ (CompactificationOf.Hom.map h)) =
      derivedRefinementComparisonUnboundedUniv Λ (g ≫ h) ≫
        Functor.whiskerLeft (etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j.immersion)
          (derivedMapComparisonUnboundedUniv Λ g h) := by
  refine compComparison_paste (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _ _ _ _ _ _ _ _ _ _ fun K => ?_
  ext n : 1
  have hn := congrArg (fun t => NatTrans.app t (K.X n)) (refinementIsoUniv_comp Λ g h)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hn
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f, Iso.symm_hom]
  have e₁ : (etaleModuleDirectImage.{u, r} Λ (CompactificationOf.Hom.map h)).map
        ((refinementIsoUniv Λ g).inv.app (K.X n)) ≫ (refinementIsoUniv Λ h).inv.app (K.X n) =
      inv ((refinementIsoUniv Λ h).hom.app (K.X n) ≫
        (etaleModuleDirectImage.{u, r} Λ (CompactificationOf.Hom.map h)).map
          ((refinementIsoUniv Λ g).hom.app (K.X n))) := by
    simp [← Functor.map_inv]
  have e₂ : (etaleModuleDirectImageComp.{u, r} Λ (CompactificationOf.Hom.map g)
        (CompactificationOf.Hom.map h) (CompactificationOf.Hom.map (g ≫ h)) rfl).hom.app
          ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).obj (K.X n)) ≫
        (refinementIsoUniv Λ (g ≫ h)).inv.app (K.X n) =
      inv ((refinementIsoUniv Λ (g ≫ h)).hom.app (K.X n) ≫
        (etaleModuleDirectImageComp.{u, r} Λ (CompactificationOf.Hom.map g)
          (CompactificationOf.Hom.map h) (CompactificationOf.Hom.map (g ≫ h)) rfl).inv.app
            ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).obj (K.X n))) := by
    simp
  refine (e₁.trans ?_).trans e₂.symm
  simp only [hn]

/-- **The composition comparisons of unbounded derived direct images are associative**. -/
lemma derivedBaseComparisonUnboundedUniv_comp :
    derivedBaseComparisonUnboundedUniv Λ (g ≫ h) ≫
        Functor.whiskerRight (derivedMapComparisonUnboundedUniv Λ g h)
          (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ l.toBase) =
      derivedBaseComparisonUnboundedUniv Λ g ≫
        Functor.whiskerLeft
          (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ (CompactificationOf.Hom.map g))
          (derivedBaseComparisonUnboundedUniv Λ h) := by
  refine compComparison_paste (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _ _ _ _ _ _ _ _ _ _ fun K => ?_
  ext n : 1
  have hc := smallEtalePushforwardComp'_inv_app_cocycle (CompactificationOf.Hom.map g)
    (CompactificationOf.Hom.map h) l.toBase (CompactificationOf.Hom.map (g ≫ h)) rfl k.toBase
    (CompactificationOf.map_comp_toBase h).symm j.toBase
    (CompactificationOf.map_comp_toBase (g ≫ h)).symm
    (CompactificationOf.map_comp_toBase g).symm (ModuleCat.{max (u + 1) r} Λ) (K.X n)
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f]
  let A := etaleModuleDirectImageComp.{u, r} Λ (CompactificationOf.Hom.map (g ≫ h)) l.toBase
    j.toBase (CompactificationOf.map_comp_toBase (g ≫ h)).symm
  let B := etaleModuleDirectImageComp.{u, r} Λ (CompactificationOf.Hom.map g)
    (CompactificationOf.Hom.map h) (CompactificationOf.Hom.map (g ≫ h)) rfl
  let C := etaleModuleDirectImageComp.{u, r} Λ (CompactificationOf.Hom.map g) k.toBase j.toBase
    (CompactificationOf.map_comp_toBase g).symm
  let D := etaleModuleDirectImageComp.{u, r} Λ (CompactificationOf.Hom.map h) l.toBase k.toBase
    (CompactificationOf.map_comp_toBase h).symm
  have hc' : ((A.app (K.X n)).symm ≪≫
      (etaleModuleDirectImage.{u, r} Λ l.toBase).mapIso (B.app (K.X n)).symm) =
      (C.app (K.X n)).symm ≪≫ (D.app ((etaleModuleDirectImage.{u, r} Λ
        (CompactificationOf.Hom.map g)).obj (K.X n))).symm := Iso.ext hc
  simpa [A, B, C, D] using congrArg (fun e => e.symm.hom) hc'

/-- **The cocycle law** on unbounded derived categories. -/
theorem derivedLowerShriekUnboundedHomIsoUniv_comp [CompactSpace Y]
    (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) :
    derivedLowerShriekUnboundedHomIsoUniv Λ (g ≫ h) hΛ =
      derivedLowerShriekUnboundedHomIsoUniv Λ h hΛ ≪≫
        derivedLowerShriekUnboundedHomIsoUniv Λ g hΛ := by
  apply Iso.ext
  refine NatTrans.ext (funext fun K => ?_)
  simp only [Iso.trans_hom, NatTrans.comp_app, derivedLowerShriekUnboundedHomIsoUniv_hom,
    derivedLowerShriekUnboundedHomUniv_app]
  have h1 := congrArg (fun t => NatTrans.app t K)
    (derivedRefinementComparisonUnboundedUniv_comp Λ g h)
  have h2 := congrArg (fun t => NatTrans.app t
    ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j.immersion).obj K))
    (derivedBaseComparisonUnboundedUniv_comp Λ g h)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h1 h2
  have hn := (inv (derivedBaseComparisonUnboundedUniv Λ h)).naturality
    ((derivedRefinementComparisonUnboundedUniv Λ g).app K)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [Category.assoc]
  rw [← reassoc_of% hn, ← Functor.map_comp_assoc, h1, Functor.map_comp, Category.assoc]
  congr 1
  rw [← cancel_epi ((derivedBaseComparisonUnboundedUniv Λ (g ≫ h)).app
    ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j.immersion).obj K)), reassoc_of% h2]
  simp

end Cocycle

end Stacks.EtaleCohomology
