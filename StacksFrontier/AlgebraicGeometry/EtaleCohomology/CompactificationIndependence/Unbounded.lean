module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Derived
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.BoundednessUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageCompositionUnbounded
public import StacksFrontier.CategoryTheory.Functor.Derived.CompComparisonPaste
public import StacksFrontier.Homology.Injectives.KInjective.RightDerivedCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Bounded

/-!
# `Rf_!` along a morphism of compactifications, on unbounded derived categories

Let `Λ` be a torsion ring, `f : X ⟶ Y` a morphism of schemes with `Y` quasi-compact, and
`g : j ⟶ k` a morphism of compactifications of `X` over `Y`. This file constructs the canonical
isomorphism `Rf_!^k ≅ Rf_!^j` of the derived lower shriek functors
`Stacks.EtaleCohomology.derivedLowerShriekUnbounded` on the unbounded derived categories, in the
same way as `Stacks.EtaleCohomology.derivedLowerShriekHomIso` on `D⁺_tors`, and proves its
cocycle law.

The map `Rk_! ⟶ Rḡ_* ∘ Rj_!` of [Stacks, Tag 0F7G] is now invertible on the whole of
`D(X_étale, Λ)` (case (b)): at a K-injective complex `I` it is the unit of `Rḡ_*` at `j_! I`, a
complex of `ḡ_*`-acyclic sheaves (every sheaf of `Λ`-modules is torsion), and `ḡ_*` has finite
cohomological dimension, so such complexes compute `Rḡ_*` ([Stacks, Tag 07K7]).

## Main definitions

* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedHomIso`.

## Main results

* `Stacks.EtaleCohomology.isIso_derivedRefinementComparisonUnbounded`: Tag 0F7G, case (b).
* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedHomIso_comp`: the cocycle law.

## Implementation notes

The unbounded functors live in the standard model of the derived category, like those of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnbounded`.

## References

* [Stacks Project, Tag 0F7G](https://stacks.math.columbia.edu/tag/0F7G)
* [Stacks Project, Tag 0F7I](https://stacks.math.columbia.edu/tag/0F7I)
* [Stacks Project, Tag 07K7](https://stacks.math.columbia.edu/tag/07K7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.DerivedBaseChange

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [Ring Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}

/-! ### Units of unbounded derived functors -/

section Units

-- the structure projections of `Stacks.Models.RegularModelSituation` are global instances whose
-- conclusions (`QuasiCompact ?f`, ...) match every goal and send instance search through
-- `Submodule ?R ?R`; they are irrelevant here
attribute [-instance] Stacks.Models.RegularModelSituation.commRingR
  Stacks.Models.RegularModelSituation.isDomainR
  Stacks.Models.RegularModelSituation.isDiscreteValuationRingR
  Stacks.Models.RegularModelSituation.fieldK Stacks.Models.RegularModelSituation.algebraRK
  Stacks.Models.RegularModelSituation.isFractionRingRK Stacks.Models.RegularModelSituation.fieldk
  Stacks.Models.RegularModelSituation.algebraRk Stacks.Models.RegularModelSituation.isCurve
  Stacks.Models.RegularModelSituation.smooth Stacks.Models.RegularModelSituation.flat
  Stacks.Models.RegularModelSituation.locallyOfFiniteType
  Stacks.Models.RegularModelSituation.quasiCompact

/-- The unit of the unbounded derived direct image is invertible at a K-injective complex, read
through the equivalence of the localization at quasi-isomorphisms of complexes with that of the
homotopy category. -/
lemma isIso_app_Q_of_isKInjective {A B : Scheme.{u}}
    {G₁ G₂ : DerivedCategory (EtaleModules.{u, 0} Λ A) ⥤ DerivedCategory (EtaleModules.{u, 0} Λ B)}
    (τ : G₁ ⟶ G₂)
    (h : ∀ (I : CochainComplex (EtaleModules.{u, 0} Λ A) ℤ), I.IsKInjective →
      IsIso (τ.app (DerivedCategory.Q.obj I))) : IsIso τ :=
  Stacks.Injectives.isIso_natTrans_of_kInjective τ fun I =>
    (NatTrans.isIso_app_iff_of_iso τ
      ((DerivedCategory.quotientCompQhIso (EtaleModules.{u, 0} Λ A)).app I)).2 (h I ‹_›)

/-- **Complexes of `a_*`-acyclic sheaves compute `Ra_*` on the unbounded derived category**, for
`a` proper over a quasi-compact scheme and a torsion ring `Λ`: `a_*` has finite cohomological
dimension ([Stacks, Tag 095U]), so this is part (2) of [Stacks, Tag 07K7]. -/
lemma isIso_etaleModuleDerivedDirectImageUnboundedUnit_app_of_rightAcyclic {A B : Scheme.{u}}
    (a : A ⟶ B) [IsProper a] [CompactSpace B] (m : ℕ) (hm : 0 < m) (hΛ : (m : Λ) = 0)
    (L : CochainComplex (EtaleModules.{u, 0} Λ A) ℤ)
    (hL : ∀ i, (etaleModuleDirectImage.{u, 0} Λ a).rightAcyclic (L.X i)) :
    IsIso ((etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ a).app L) := by
  obtain ⟨d, hd⟩ :=
    @AlgebraicGeometry.exists_topologicalKrullDim_fiber_le _ _ a
      (IsProper.toLocallyOfFiniteType (f := a))
      (@AlgebraicGeometry.instQuasiCompactOfUniversallyClosed _ _ _
        (IsProper.toUniversallyClosed (f := a))) ‹_›
  let F := etaleModuleDirectImage.{u, 0} Λ a
  let RF := etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ a
  let α := Stacks.Injectives.KInjectiveResolution.homotopyCategoryUnit F RF
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ a)
  let P (Z : EtaleModules.{u, 0} Λ A) :=
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
      (HomotopyCategory.Plus.quasiIso _) ((HomotopyCategory.Plus.singleFunctor _ 0).obj Z)
  have hcomp : ∀ Z, F.rightAcyclic Z → P Z := by
    intro Z hZ
    have : (HomotopyCategory.Plus.quasiIso
        (EtaleModules.{u, 0} Λ A)).HasLeftCalculusOfFractions := by
      rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW]
      infer_instance
    dsimp only [P]
    rw [Functor.computesRightDerived_iff_isIso_app _ DerivedCategory.Plus.Qh
      ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerived
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso _))
      (HomotopyCategory.Plus.quasiIso _)
      ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso _)) _
      (fun K => ?_)]
    · exact hZ
    · let r : (HomotopyCategory.Plus.localizerMorphism _).RightResolution K := Classical.arbitrary _
      exact ⟨_, r.w, r.hw, inferInstance⟩
  have h07K7 := Functor.hasRightDerivedFunctor_of_isZero_rightDerived F
    F.rightDerivedFunctorPlus F.rightDerivedFunctorPlusUnith
    P
    (fun _ => Iff.rfl)
    (fun Z => ⟨Injective.under Z, Injective.ι Z, inferInstance,
      computesRightDerived_singleFunctor_of_injective F _⟩)
    (2 * d + 1) (fun Z => by
      have h := Stacks.BoundedCohomologicalDimension.isLE_rightDerivedFunctorPlus_single F Z
        (2 * d : ℕ) 0 (fun p hp => isZero_rightDerived_etaleModuleDirectImage_of_isProper Λ
          a d hd _ (torsionSheafProperty_etaleModuleForget_obj_of_nsmul_eq_zero Λ m hm hΛ _)
          p (by exact_mod_cast hp))
      exact DerivedCategory.isZero_of_isLE _ (0 + (2 * d : ℕ)) _ (by push_cast; omega))
  obtain ⟨-, -, hRF⟩ := h07K7
  obtain ⟨hL', -⟩ := hRF RF α
  have hα := hL' L (fun i => hcomp _ (hL i))
  rw [Stacks.Injectives.KInjectiveResolution.homotopyCategoryUnit_app_quotient,
    ← Category.assoc] at hα
  have : IsIso ((etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ a).app L ≫
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
def derivedRefinementComparisonUnbounded :
    etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ k.immersion ⟶
      etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ j.immersion ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (CompactificationOf.Hom.map g) :=
  compComparison (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, 0} Λ j.immersion)
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ (CompactificationOf.Hom.map g))
    (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, 0} Λ k.immersion)
    (Functor.mapHomologicalComplexCompIso (refinementIso Λ g).symm (ComplexShape.up ℤ))

/-- The composition comparison `R(j̄)_* ⟶ Rḡ_* ⋙ R(k̄)_*` of unbounded derived direct images. -/
def derivedBaseComparisonUnbounded :
    etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ j.toBase ⟶
      etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (CompactificationOf.Hom.map g) ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ k.toBase :=
  compComparison (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ (CompactificationOf.Hom.map g))
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ k.toBase)
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ j.toBase)
    (Functor.mapHomologicalComplexCompIso (etaleModuleDirectImageComp.{u, 0} Λ
      (CompactificationOf.Hom.map g) k.toBase j.toBase
      (CompactificationOf.map_comp_toBase g).symm) (ComplexShape.up ℤ))

/-- The composition comparison of unbounded derived direct images is invertible, direct images
preserving K-injective complexes. -/
instance isIso_derivedBaseComparisonUnbounded : IsIso (derivedBaseComparisonUnbounded Λ g) := by
  refine isIso_app_Q_of_isKInjective Λ _ fun I hI => ?_
  have h := compComparison_fac_app (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ (CompactificationOf.Hom.map g))
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ k.toBase)
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ j.toBase)
    (Functor.mapHomologicalComplexCompIso (etaleModuleDirectImageComp.{u, 0} Λ
      (CompactificationOf.Hom.map g) k.toBase j.toBase
      (CompactificationOf.map_comp_toBase g).symm) (ComplexShape.up ℤ)) I
  have := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app.{u, 0} Λ j.toBase I hI
  have := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app.{u, 0} Λ
    (CompactificationOf.Hom.map g) I hI
  have := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app.{u, 0} Λ k.toBase _
    (isKInjective_etaleModuleDirectImage_mapHomologicalComplex Λ
      (CompactificationOf.Hom.map g) I hI)
  exact IsIso.of_isIso_fac_left h

include Λ in
/-- Every sheaf of modules over a torsion ring is torsion. -/
lemma isTorsionEtaleModule_of_nsmul_eq_zero {Z : Scheme.{u}} (m : ℕ) (hm : 0 < m)
    (hΛ : (m : Λ) = 0) (M : EtaleModules.{u, 0} Λ Z) : IsTorsionEtaleModule.{u, 0} Λ Z M :=
  torsionSheafProperty_etaleModuleForget_obj_of_nsmul_eq_zero Λ m hm hΛ M

/-- **[Stacks, Tag 0F7G], case (b), for compactifications**: over a torsion ring the map
`Rk_! ⟶ Rḡ_* ∘ Rj_!` is invertible on the whole unbounded derived category. -/
theorem isIso_derivedRefinementComparisonUnbounded [CompactSpace Y] (m : ℕ) (hm : 0 < m)
    (hΛ : (m : Λ) = 0) : IsIso (derivedRefinementComparisonUnbounded Λ g) := by
  refine isIso_app_Q_of_isKInjective Λ _ fun I hI => ?_
  have h := compComparison_fac_app (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, 0} Λ j.immersion)
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ (CompactificationOf.Hom.map g))
    (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, 0} Λ k.immersion)
    (Functor.mapHomologicalComplexCompIso (refinementIso Λ g).symm (ComplexShape.up ℤ)) I
  have := isIso_etaleModuleDerivedExtensionByZeroUnboundedUnit_app.{u, 0} Λ k.immersion I hI
  have := isIso_etaleModuleDerivedExtensionByZeroUnboundedUnit_app.{u, 0} Λ j.immersion I hI
  have : CompactSpace k.space := QuasiCompact.compactSpace_of_compactSpace k.toBase
  have := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app_of_rightAcyclic Λ
    (CompactificationOf.Hom.map g) m hm hΛ
    (((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I) fun i =>
      (Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived _ _).2
        fun p hp => isZero_rightDerived_etaleModuleDirectImage_extensionByZero Λ
          (CompactificationOf.immersion_comp_map g) (I.X i)
          (isTorsionEtaleModule_of_nsmul_eq_zero Λ m hm hΛ _) p hp
  exact IsIso.of_isIso_fac_left h

end Comparisons

/-! ### The isomorphism `Rf_!^k ≅ Rf_!^j` on unbounded derived categories -/

section HomIso

variable {j k : CompactificationOf (Over.mk f)} (g : j ⟶ k)

/-- The comparison `Rf_!^k ⟶ Rf_!^j` on `D(X_étale, Λ)` attached to a morphism of
compactifications. -/
def derivedLowerShriekUnboundedHom :
    derivedLowerShriekUnbounded.{u, 0} f k Λ ⟶ derivedLowerShriekUnbounded.{u, 0} f j Λ :=
  Functor.whiskerRight (derivedRefinementComparisonUnbounded Λ g)
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ k.toBase) ≫
    Functor.whiskerLeft (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ j.immersion)
      (inv (derivedBaseComparisonUnbounded Λ g))

/-- The component of `derivedLowerShriekUnboundedHom` at `K` is the image under `Rk̄_*` of the
refinement comparison at `K`, followed by the inverse of the base comparison at `j_! K`. -/
lemma derivedLowerShriekUnboundedHom_app (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (derivedLowerShriekUnboundedHom Λ g).app K =
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ k.toBase).map
          ((derivedRefinementComparisonUnbounded Λ g).app K) ≫
        (inv (derivedBaseComparisonUnbounded Λ g)).app
          ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ j.immersion).obj K) := rfl

/-- **The isomorphism `Rf_!^k ≅ Rf_!^j` on `D(X_étale, Λ)` for a torsion ring `Λ`** attached to
a morphism `g : j ⟶ k` of compactifications ([Stacks, Tag 0F7I], the isomorphism displayed in
the proof), the first step being the map of [Stacks, Tag 0F7G]. -/
def derivedLowerShriekUnboundedHomIso [CompactSpace Y] (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) :
    derivedLowerShriekUnbounded.{u, 0} f k Λ ≅ derivedLowerShriekUnbounded.{u, 0} f j Λ :=
  haveI : IsIso (derivedRefinementComparisonUnbounded Λ g) :=
    isIso_derivedRefinementComparisonUnbounded Λ g hΛ.choose hΛ.choose_spec.1 hΛ.choose_spec.2
  haveI : IsIso (derivedLowerShriekUnboundedHom Λ g) := by
    dsimp only [derivedLowerShriekUnboundedHom]
    infer_instance
  asIso (derivedLowerShriekUnboundedHom Λ g)

/-- The forward map of `derivedLowerShriekUnboundedHomIso` is `derivedLowerShriekUnboundedHom`. -/
@[simp]
lemma derivedLowerShriekUnboundedHomIso_hom [CompactSpace Y]
    (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) :
    (derivedLowerShriekUnboundedHomIso Λ g hΛ).hom = derivedLowerShriekUnboundedHom Λ g := rfl

end HomIso

/-! ### The cocycle law -/

section Cocycle

variable {j k l : CompactificationOf (Over.mk f)} (g : j ⟶ k) (h : k ⟶ l)

/-- The composition comparison `R(ḡh̄)_* ⟶ Rḡ_* ⋙ Rh̄_*` of unbounded derived direct images. -/
def derivedMapComparisonUnbounded :
    etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (CompactificationOf.Hom.map (g ≫ h)) ⟶
      etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (CompactificationOf.Hom.map g) ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (CompactificationOf.Hom.map h) :=
  compComparison (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ (CompactificationOf.Hom.map g))
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ (CompactificationOf.Hom.map h))
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ (CompactificationOf.Hom.map (g ≫ h)))
    (Functor.mapHomologicalComplexCompIso (etaleModuleDirectImageComp.{u, 0} Λ
      (CompactificationOf.Hom.map g) (CompactificationOf.Hom.map h)
      (CompactificationOf.Hom.map (g ≫ h)) rfl) (ComplexShape.up ℤ))

/-- **The maps of Tag 0F7G compose**, on unbounded derived categories. -/
lemma derivedRefinementComparisonUnbounded_comp :
    derivedRefinementComparisonUnbounded Λ h ≫
        Functor.whiskerRight (derivedRefinementComparisonUnbounded Λ g)
          (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (CompactificationOf.Hom.map h)) =
      derivedRefinementComparisonUnbounded Λ (g ≫ h) ≫
        Functor.whiskerLeft (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ j.immersion)
          (derivedMapComparisonUnbounded Λ g h) := by
  refine compComparison_paste (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _ _ _ _ _ _ _ _ _ _ fun K => ?_
  ext n : 1
  have hn := NatTrans.congr_app (refinementIso_comp Λ g h) (K.X n)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hn
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f, Iso.symm_hom]
  have e₁ : (etaleModuleDirectImage.{u, 0} Λ (CompactificationOf.Hom.map h)).map
        ((refinementIso Λ g).inv.app (K.X n)) ≫ (refinementIso Λ h).inv.app (K.X n) =
      inv ((refinementIso Λ h).hom.app (K.X n) ≫
        (etaleModuleDirectImage.{u, 0} Λ (CompactificationOf.Hom.map h)).map
          ((refinementIso Λ g).hom.app (K.X n))) := by
    simp [← Functor.map_inv]
  have e₂ : (etaleModuleDirectImageComp.{u, 0} Λ (CompactificationOf.Hom.map g)
        (CompactificationOf.Hom.map h) (CompactificationOf.Hom.map (g ≫ h)) rfl).hom.app
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj (K.X n)) ≫
        (refinementIso Λ (g ≫ h)).inv.app (K.X n) =
      inv ((refinementIso Λ (g ≫ h)).hom.app (K.X n) ≫
        (etaleModuleDirectImageComp.{u, 0} Λ (CompactificationOf.Hom.map g)
          (CompactificationOf.Hom.map h) (CompactificationOf.Hom.map (g ≫ h)) rfl).inv.app
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj (K.X n))) := by
    simp
  exact (e₁.trans (by simp only [hn])).trans e₂.symm

/-- **The composition comparisons of unbounded derived direct images are associative**. -/
lemma derivedBaseComparisonUnbounded_comp :
    derivedBaseComparisonUnbounded Λ (g ≫ h) ≫
        Functor.whiskerRight (derivedMapComparisonUnbounded Λ g h)
          (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ l.toBase) =
      derivedBaseComparisonUnbounded Λ g ≫
        Functor.whiskerLeft
          (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (CompactificationOf.Hom.map g))
          (derivedBaseComparisonUnbounded Λ h) := by
  refine compComparison_paste (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _ _ _ _ _ _ _ _ _ _ fun K => ?_
  ext n : 1
  have hc := smallEtalePushforwardComp'_inv_app_cocycle (CompactificationOf.Hom.map g)
    (CompactificationOf.Hom.map h) l.toBase (CompactificationOf.Hom.map (g ≫ h)) rfl k.toBase
    (CompactificationOf.map_comp_toBase h).symm j.toBase
    (CompactificationOf.map_comp_toBase (g ≫ h)).symm
    (CompactificationOf.map_comp_toBase g).symm (ModuleCat.{u + 1} Λ) (K.X n)
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f]
  let A := etaleModuleDirectImageComp.{u, 0} Λ (CompactificationOf.Hom.map (g ≫ h)) l.toBase
    j.toBase (CompactificationOf.map_comp_toBase (g ≫ h)).symm
  let B := etaleModuleDirectImageComp.{u, 0} Λ (CompactificationOf.Hom.map g)
    (CompactificationOf.Hom.map h) (CompactificationOf.Hom.map (g ≫ h)) rfl
  let C := etaleModuleDirectImageComp.{u, 0} Λ (CompactificationOf.Hom.map g) k.toBase j.toBase
    (CompactificationOf.map_comp_toBase g).symm
  let D := etaleModuleDirectImageComp.{u, 0} Λ (CompactificationOf.Hom.map h) l.toBase k.toBase
    (CompactificationOf.map_comp_toBase h).symm
  have hc' : ((A.app (K.X n)).symm ≪≫
      (etaleModuleDirectImage.{u, 0} Λ l.toBase).mapIso (B.app (K.X n)).symm) =
      (C.app (K.X n)).symm ≪≫ (D.app ((etaleModuleDirectImage.{u, 0} Λ
        (CompactificationOf.Hom.map g)).obj (K.X n))).symm := Iso.ext hc
  simpa [A, B, C, D] using congrArg (fun e => e.symm.hom) hc'

/-- **The cocycle law** on unbounded derived categories. -/
theorem derivedLowerShriekUnboundedHomIso_comp [CompactSpace Y]
    (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) :
    derivedLowerShriekUnboundedHomIso Λ (g ≫ h) hΛ =
      derivedLowerShriekUnboundedHomIso Λ h hΛ ≪≫ derivedLowerShriekUnboundedHomIso Λ g hΛ := by
  refine Iso.ext (NatTrans.ext (funext fun K => ?_))
  simp only [Iso.trans_hom, NatTrans.comp_app, derivedLowerShriekUnboundedHomIso_hom,
    derivedLowerShriekUnboundedHom_app]
  have h1 := NatTrans.congr_app (derivedRefinementComparisonUnbounded_comp Λ g h) K
  have h2 := NatTrans.congr_app (derivedBaseComparisonUnbounded_comp Λ g h)
    ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ j.immersion).obj K)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h1 h2
  have hn := (inv (derivedBaseComparisonUnbounded Λ h)).naturality
    ((derivedRefinementComparisonUnbounded Λ g).app K)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [Category.assoc]
  rw [← reassoc_of% hn, ← Functor.map_comp_assoc, h1, Functor.map_comp, Category.assoc]
  congr 1
  rw [← cancel_epi ((derivedBaseComparisonUnbounded Λ (g ≫ h)).app
    ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ j.immersion).obj K)), reassoc_of% h2]
  simp

end Cocycle

end Stacks.EtaleCohomology
