module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtensionByZeroSupported
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedOnComplementUnconditional
import StacksCore.Tactic.StacksAttribute

/-!
# Supported objects at the canonical direct images and the canonical extension by zero

Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S`, let `P = U ×_X V` and set `T = |X| \ |U|`. For an object `E` of `D(𝒪_X)` supported
on `T`, the canonical map `E ⟶ Rj_{V,*}(E|_V)` into the chosen total right derived direct image
is an isomorphism, and for `F` in `D(𝒪_V)` supported on `j^{-1}T` the comparison
`j_!F ⟶ Rj_*F` at the canonical derived extension by zero is an isomorphism.

## Main results

* `AlgebraicGeometry.Space.isZero_totalRightDerived_etaleRestrictPush_of_isZero`: the vanishing
  of a right derived functor of `j_{Y,*}((-)|_Y)` at an object whose restriction to `Y`
  vanishes.
* `AlgebraicGeometry.Space.isIso_derivedUnit_edsDerivedRestrictPushEtale_of_cohomologySupportedOn`:
  clause (1)(a) of [Stacks, Tag 08GG] at the canonical derived direct images.
* `AlgebraicGeometry.Space.isIso_supportedShriekToPushforward_edsEtaleDerivedAdjunction`:
  clause (2)(c) of [Stacks, Tag 08GG] at the canonical derived extension by zero.

## References

* [Stacks Project, Tag 08GG](https://stacks.math.columbia.edu/tag/08GG)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Pretriangulated

universe u

namespace AlgebraicGeometry.Space

open CategoryTheory.PushforwardMayerVietoris

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback
  smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat
  hasRightDerivedFunctor_mapHomotopyCategory_modules

/-! ### The derived direct image of a vanishing restriction -/

/-- Let `g : Y ⟶ X` be étale and let `E` in `D(𝒪_X)` have `E|_Y = 0`. Then `R E = 0` for every
right derived functor `R` of `g_*((-)|_Y)`. -/
theorem isZero_totalRightDerived_etaleRestrictPush_of_isZero {W Y : AlgebraicSpaces B S hS}
    (g : Y ⟶ W) (hg : IsEtale B S hS g.hom)
    (R : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (α : (etaleModulePullback.{u, u} B S hS g hg ⋙
          modulePushforward B S hS g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ R)
    (hR : R.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hE : IsZero ((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.obj E)) :
    IsZero (R.obj E) := by
  have hres := exists_quasiIso_isKInjective_modules B S hS W.1 W.2
  obtain ⟨I, hI, ⟨e⟩⟩ := exists_isKInjective_representative_of_universe hres E
  set K := ((etaleModulePullback.{u, u} B S hS g hg).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj I
  have h₁ : IsZero ((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.obj
      (DerivedCategory.Q.obj I)) :=
    hE.of_iso ((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.mapIso e)
  have hQK : IsZero (DerivedCategory.Q.obj K) :=
    h₁.of_iso (((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategoryFactors).app I).symm
  have hacyc : K.Acyclic := by
    intro i
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).map_isZero
      hQK).of_iso
      ((DerivedCategory.homologyFunctorFactors (Modules.{u, u} B S hS Y.1 Y.2) i).app K).symm
  have : CochainComplex.IsKInjective K :=
    CochainComplex.isKInjective_mapHomologicalComplex_of_exact
      (etaleModulePullback.{u, u} B S hS g hg) (etaleModuleLowerShriek B S hS g hg)
      (etaleModuleLowerShriekAdjunction B S hS g hg) I
  have hq : IsZero ((HomotopyCategory.quotient (Modules.{u, u} B S hS Y.1 Y.2)
      (ComplexShape.up ℤ)).obj K) := by
    rw [IsZero.iff_id_eq_zero,
      ← (HomotopyCategory.quotient (Modules.{u, u} B S hS Y.1 Y.2)
        (ComplexShape.up ℤ)).map_id K,
      HomotopyCategory.quotient_map_eq_zero_iff]
    exact CochainComplex.IsKInjective.nonempty_homotopy_zero (𝟙 K) hacyc
  have hq₁ : IsZero (((modulePushforward B S hS g).mapHomotopyCategory
      (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient
        (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ)).obj K)) :=
    Functor.map_isZero _ hq
  have hq₂ : IsZero ((HomotopyCategory.quotient (Modules.{u, u} B S hS W.1 W.2)
      (ComplexShape.up ℤ)).obj (((modulePushforward B S hS g).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K)) :=
    hq₁.of_iso (((modulePushforward B S hS g).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).app K).symm
  have hq₃ : IsZero ((HomotopyCategory.quotient (Modules.{u, u} B S hS W.1 W.2)
      (ComplexShape.up ℤ)).obj (((etaleModulePullback.{u, u} B S hS g hg ⋙
        modulePushforward B S hS g).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :=
    hq₂.of_iso ((HomotopyCategory.quotient (Modules.{u, u} B S hS W.1 W.2)
      (ComplexShape.up ℤ)).mapIso ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (etaleModulePullback.{u, u} B S hS g hg ⋙ modulePushforward B S hS g))
        (ComplexShape.up ℤ)).app I).symm)
  have hq₄ : IsZero (DerivedCategory.Q.obj (((etaleModulePullback.{u, u} B S hS g hg ⋙
      modulePushforward B S hS g).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :=
    (Functor.map_isZero DerivedCategory.Qh hq₃).of_iso
      ((DerivedCategory.quotientCompQhIso (Modules.{u, u} B S hS W.1 W.2)).app _).symm
  exact hq₄.of_iso ((R.mapIso e).symm ≪≫ (rightDerivedObjIsoOfKInjective hres
    (etaleModulePullback.{u, u} B S hS g hg ⋙ modulePushforward B S hS g) inferInstance
    R α hR I hI).symm)

section Square

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-! ### Clause (1)(a) at the canonical derived direct images -/

/-- Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S` and set `T = |X| \ |U|`. For an object `E` of `D(𝒪_X)` supported on `T`, the
canonical map `E ⟶ Rj_{V,*}(E|_V)` into the chosen total right derived direct image is an
isomorphism. -/
@[stacks 08GG "clause (1)(a): the canonical map E ⟶ Rj_*(E|_V) is an isomorphism for E \
    supported on |X| \\ |U|, at the chosen total right derived functors"]
theorem isIso_derivedUnit_edsDerivedRestrictPushEtale_of_cohomologySupportedOn
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hE : CohomologySupportedOn B S hS W.1 W.2 (edsComplementPoints B S hS Uo) E) :
    IsIso ((derivedUnitOfNatTrans (edsAdjEtale B S hS hsq).unit
      (edsDerivedRestrictPushEtale B S hS hsq)
      (edsTotalRightDerivedUnitEtale B S hS hsq)).app E) := by
  obtain ⟨δ, hδ⟩ :=
    exists_mem_distTriang_edsDerivedRestrictPushMayerVietorisLowerShriek B S hS hsq E
  have hU : IsZero ((edsDerivedRestrictPushOpen B S hS hsq).obj E) :=
    isZero_totalRightDerived_etaleRestrictPush_of_isZero B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq) _ (edsTotalRightDerivedUnitOpen B S hS hsq)
      inferInstance E
      (isZero_etaleModulePullback_mapDerivedCategory_of_cohomologySupportedOn B S hS _ E hE
        (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq)
        (range_pointsMap_subset_compl_edsComplementPoints B S hS (edsOpenHom B S hS hsq)
          (range_pointsMap_edsOpenHom B S hS hsq).subset))
  have hP : IsZero ((edsDerivedRestrictPushInter B S hS hsq).obj E) :=
    isZero_totalRightDerived_etaleRestrictPush_of_isZero B S hS (edsInterHom B S hS hsq)
      (isEtale_edsInterHom B S hS hsq) _ (edsTotalRightDerivedUnitInter B S hS hsq)
      inferInstance E
      (isZero_etaleModulePullback_mapDerivedCategory_of_cohomologySupportedOn B S hS _ E hE
        (edsInterHom B S hS hsq) (isEtale_edsInterHom B S hS hsq)
        (range_pointsMap_subset_compl_edsComplementPoints B S hS (edsInterHom B S hS hsq)
          (range_pointsMap_edsInterHom_subset B S hS hsq)))
  have hlift : IsIso (biprod.lift
      ((derivedUnitOfNatTrans (edsAdjOpen B S hS hsq).unit
        (edsDerivedRestrictPushOpen B S hS hsq)
        (edsTotalRightDerivedUnitOpen B S hS hsq)).app E)
      ((derivedUnitOfNatTrans (edsAdjEtale B S hS hsq).unit
        (edsDerivedRestrictPushEtale B S hS hsq)
        (edsTotalRightDerivedUnitEtale B S hS hsq)).app E)) :=
    (Triangle.isZero₃_iff_isIso₁ _ hδ).1 hP
  have hsnd := isIso_biprod_snd_of_isZero_fst ((edsDerivedRestrictPushOpen B S hS hsq).obj E)
    ((edsDerivedRestrictPushEtale B S hS hsq).obj E) hU
  simpa only [biprod.lift_snd] using IsIso.comp_isIso' hlift hsnd

/-! ### Clause (2)(c) at the canonical derived extension by zero -/

variable {RpushD : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
    (edsEtale B S hS hsq).2) ⥤ DerivedCategory (Modules.{u, u} B S hS W.1 W.2)}
  (adjPush : (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory ⊣ RpushD)

/-- For an elementary distinguished square `(U ⊆ X, j : V ⟶ X)` of algebraic spaces over a
scheme `S` with `T = |X| \ |U|`, and `F` an object of `D(𝒪_V)` supported on `j^{-1}T`, the
comparison `j_!F ⟶ Rj_*F` is an isomorphism, given the counit `(Rj_*F)|_V ⟶ F` and the unit
isomorphisms at `j_!F` and at `Rj_*F`, each as a hypothesis on supported objects. Here `j_!` is
the derived extension by zero of `edsEtaleDerivedAdjunction`. -/
theorem isIso_supportedShriekToPushforward_edsEtaleDerivedAdjunction
    (F : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2))
    (h2b : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
        (edsEtalePreimageComplementPoints B S hS hsq) F →
      IsIso (adjPush.counit.app F))
    (h1aShriek : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1
        (edsEtale B S hS hsq).2 (edsEtalePreimageComplementPoints B S hS hsq) F →
      IsIso (adjPush.unit.app ((etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj F)))
    (h1aPush : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1
        (edsEtale B S hS hsq).2 (edsEtalePreimageComplementPoints B S hS hsq) F →
      IsIso (adjPush.unit.app (RpushD.obj F)))
    (hF : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
      (edsEtalePreimageComplementPoints B S hS hsq) F) :
    IsIso (supportedShriekToPushforward B S hS hsq (edsEtaleDerivedAdjunction B S hS hsq)
      adjPush F (isIso_edsEtaleDerivedAdjunction_unit_app_of_cohomologySupportedOn
        B S hS hsq F hF)) :=
  isIso_supportedShriekToPushforward B S hS hsq (edsEtaleDerivedAdjunction B S hS hsq)
    adjPush F
    (fun hF' => isIso_edsEtaleDerivedAdjunction_unit_app_of_cohomologySupportedOn
      B S hS hsq F hF')
    h2b h1aShriek h1aPush hF

end Square

end AlgebraicGeometry.Space

end
