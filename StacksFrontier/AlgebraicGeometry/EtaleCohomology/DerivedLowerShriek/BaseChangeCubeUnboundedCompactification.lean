module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.BaseChangeCubeUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.IndependenceCoefficientUniverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompactificationMorphisms
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.UnderivedExtensionByZeroPasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.UnderivedBaseChangePasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.BaseChangeCube
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportFunctoriality.UnboundedBaseChangeToDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportFunctoriality.DirectImageCompCoherence

/-!
# The unbounded base change map of `Rf_!` does not depend on the compactification

On `D(X_étale, Λ)`, the base change map `g⁻¹ ∘ Rf_! ⟶ Rf'_! ∘ (g')⁻¹` of a cube of
compactifications is natural in morphisms of compactifications, it is the base change map through
the base change of the compactification followed by the canonical comparison of the two
compactifications, and the base change maps of two compactifications correspond under the
canonical comparisons. This is the unbounded counterpart of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/DerivedLowerShriek/BaseChangeCubeTorsion.lean`.

## Main results

* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedBaseChangeCube_naturality`.
* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedBaseChangeCube_eq`.
* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedBaseChange_compactificationIso`.
* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedHomUniv_id`: the comparison along the identity
  of a compactification is the identity, for an arbitrary ring.
* `Stacks.EtaleCohomology.derivedRefinementComparisonUnboundedUniv_baseChange` and
  `Stacks.EtaleCohomology.derivedBaseComparisonUnboundedUniv_baseChange`: the two halves of the
  comparison `Rf_!^{j₂} ⟶ Rf_!^{j₁}` commute with base change.

## Implementation notes

The identities on derived categories are reduced, through the universal property of right derived
functors, to identities of sheaves: the map of [Stacks, Tag 0F7G] commutes with base change by
`Stacks.EtaleCohomology.etaleModuleRefinementComparison_baseChange`, and the base change maps of
direct images compose by `Stacks.EtaleCohomology.etaleModuleDerivedBaseChangeUnbounded_comp`. The
pasting lemmas are stated for abstract categories, or for arbitrary schemes with the comparisons as
variables, so that the kernel never reduces the sheaf functors.

## References

* [Stacks Project, Tag 0F7I](https://stacks.math.columbia.edu/tag/0F7I)
* [Stacks Project, Tag 0F7L](https://stacks.math.columbia.edu/tag/0F7L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type r) [CommRing Λ]

/-! ### Pasting of derived comparisons, for abstract categories -/

namespace DerivedComparisonPaste

section Abstract

variable {CA CB CC CA' CB' CC' DA DB DC DA' DB' DC' : Type*} [Category* CA] [Category* CB]
  [Category* CC] [Category* CA'] [Category* CB'] [Category* CC'] [Category* DA] [Category* DB]
  [Category* DC] [Category* DA'] [Category* DB'] [Category* DC']
  {QA : CA ⥤ DA} {QB : CB ⥤ DB} {QC : CC ⥤ DC} {QA' : CA' ⥤ DA'} {QB' : CB' ⥤ DB'}
  {QC' : CC' ⥤ DC'}
  {P : CA ⥤ CB} {Qt : CB ⥤ CC} {PQ : CA ⥤ CC} {P' : CA' ⥤ CB'} {Qt' : CB' ⥤ CC'}
  {PQ' : CA' ⥤ CC'} {GA : CA ⥤ CA'} {GB : CB ⥤ CB'} {GC : CC ⥤ CC'}
  {RP : DA ⥤ DB} {RQ : DB ⥤ DC} {RPQ : DA ⥤ DC} {RP' : DA' ⥤ DB'} {RQ' : DB' ⥤ DC'}
  {RPQ' : DA' ⥤ DC'} {GDA : DA ⥤ DA'} {GDB : DB ⥤ DB'} {GDC : DC ⥤ DC'}

/-- **Comparisons of right derived functors paste vertically**, for abstract categories and
comparisons `L : RPQ ⟶ RP ⋙ RQ`, `L' : RPQ' ⟶ RP' ⋙ RQ'` which need not be invertible. Let `bP`,
`bQ` and `bPQ` be the transformations `RP ⋙ GDB ⟶ GDA ⋙ RP'` (and so on) induced by comparisons
`cP`, `cQ`, `cPQ` of the underlying functors and by comparisons `ΦA`, `ΦB`, `ΦC` of the
localizations (the hypotheses `hbP`, `hbQ`, `hbPQ`), and `L`, `L'` the comparisons induced by
`P ⋙ Qt ≅ PQ` (the hypotheses `hL`, `hL'`). If the comparisons `cP`, `cQ`, `cPQ` paste (`hc`),
so do `bP`, `bQ` and `bPQ`, read through `L` and `L'`. Stated for abstract categories, so that
the kernel never reduces the functors. -/
theorem derivedComparison_vertical_paste_of_hom (W : MorphismProperty CA) [QA.IsLocalization W]
    (uP : P ⋙ QB ⟶ QA ⋙ RP) (uQ : Qt ⋙ QC ⟶ QB ⋙ RQ) (uPQ : PQ ⋙ QC ⟶ QA ⋙ RPQ)
    (uP' : P' ⋙ QB' ⟶ QA' ⋙ RP') (uQ' : Qt' ⋙ QC' ⟶ QB' ⋙ RQ')
    (uPQ' : PQ' ⋙ QC' ⟶ QA' ⋙ RPQ')
    [hR : (RPQ ⋙ GDC).IsRightDerivedFunctor
      (Functor.whiskerRight uPQ GDC ≫ (Functor.associator _ _ _).hom) W]
    (ΦA : QA ⋙ GDA ≅ GA ⋙ QA') (ΦB : QB ⋙ GDB ≅ GB ⋙ QB') (ΦC : QC ⋙ GDC ≅ GC ⋙ QC')
    (cP : P ⋙ GB ⟶ GA ⋙ P') (cQ : Qt ⋙ GC ⟶ GB ⋙ Qt') (cPQ : PQ ⋙ GC ⟶ GA ⋙ PQ')
    (bP : RP ⋙ GDB ⟶ GDA ⋙ RP') (bQ : RQ ⋙ GDC ⟶ GDB ⋙ RQ')
    (bPQ : RPQ ⋙ GDC ⟶ GDA ⋙ RPQ')
    (e : P ⋙ Qt ≅ PQ) (e' : P' ⋙ Qt' ≅ PQ') (L : RPQ ⟶ RP ⋙ RQ) (L' : RPQ' ⟶ RP' ⋙ RQ')
    (hbP : ∀ K, GDB.map (uP.app K) ≫ bP.app (QA.obj K) =
      ΦB.hom.app (P.obj K) ≫ QB'.map (cP.app K) ≫ uP'.app (GA.obj K) ≫ RP'.map (ΦA.inv.app K))
    (hbQ : ∀ K, GDC.map (uQ.app K) ≫ bQ.app (QB.obj K) =
      ΦC.hom.app (Qt.obj K) ≫ QC'.map (cQ.app K) ≫ uQ'.app (GB.obj K) ≫
        RQ'.map (ΦB.inv.app K))
    (hbPQ : ∀ K, GDC.map (uPQ.app K) ≫ bPQ.app (QA.obj K) =
      ΦC.hom.app (PQ.obj K) ≫ QC'.map (cPQ.app K) ≫ uPQ'.app (GA.obj K) ≫
        RPQ'.map (ΦA.inv.app K))
    (hL : ∀ K, uPQ.app K ≫ L.app (QA.obj K) =
      QC.map (e.inv.app K) ≫ uQ.app (P.obj K) ≫ RQ.map (uP.app K))
    (hL' : ∀ K, uPQ'.app K ≫ L'.app (QA'.obj K) =
      QC'.map (e'.inv.app K) ≫ uQ'.app (P'.obj K) ≫ RQ'.map (uP'.app K))
    (hc : ∀ K, cPQ.app K ≫ e'.inv.app (GA.obj K) =
      GC.map (e.inv.app K) ≫ cQ.app (P.obj K) ≫ Qt'.map (cP.app K)) :
    bPQ ≫ Functor.whiskerLeft GDA L' =
      Functor.whiskerRight L GDC ≫ (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft RP bQ ≫ (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight bP RQ' ≫ (Functor.associator _ _ _).hom := by
  refine Functor.rightDerived_ext _
    (Functor.whiskerRight uPQ GDC ≫ (Functor.associator _ _ _).hom) W _ _ _
    (NatTrans.ext (funext fun K => ?_))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Functor.comp_obj, Category.assoc]
  have nL := L'.naturality (ΦA.inv.app K)
  have nB := bQ.naturality (uP.app K)
  have nU := uQ'.naturality (cP.app K)
  have nΦ := ΦC.hom.naturality (e.inv.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at nL nB nU nΦ
  have hp' : ΦB.inv.app (P.obj K) ≫ GDB.map (uP.app K) ≫ bP.app (QA.obj K) =
      QB'.map (cP.app K) ≫ uP'.app (GA.obj K) ≫ RP'.map (ΦA.inv.app K) := by
    rw [hbP, Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% hbPQ, nL, reassoc_of% hL', ← GDC.map_comp_assoc, hL, GDC.map_comp,
    GDC.map_comp, Category.assoc, Category.assoc, reassoc_of% nB, reassoc_of% hbQ]
  simp only [← Functor.map_comp]
  rw [hp', ← QC'.map_comp_assoc, hc]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% nΦ, ← reassoc_of% nU]

end Abstract

/-- **Degreewise comparisons along an isomorphism `PQ ≅ P ⋙ Qt` paste**, for abstract
categories: if the underived comparisons `η₁`, `β`, `η₂` paste along `θ : PQ ≅ P ⋙ Qt` and
`θ' : PQ' ≅ P' ⋙ Qt'` (`h`), so do the comparisons they induce degreewise on complexes. Stated
for abstract categories, so that the kernel never reduces the functors. -/
theorem mapHomologicalComplex_refinement_paste {ι : Type*} {c : ComplexShape ι}
    {VA VB VC VA' VB' VC' : Type*} [Category* VA] [Category* VB] [Category* VC] [Category* VA']
    [Category* VB'] [Category* VC'] [Preadditive VA] [Preadditive VB] [Preadditive VC]
    [Preadditive VA'] [Preadditive VB'] [Preadditive VC']
    {P : VA ⥤ VB} {Qt : VB ⥤ VC} {PQ : VA ⥤ VC} {P' : VA' ⥤ VB'} {Qt' : VB' ⥤ VC'}
    {PQ' : VA' ⥤ VC'} {GA : VA ⥤ VA'} {GB : VB ⥤ VB'} {GC : VC ⥤ VC'}
    [P.Additive] [Qt.Additive] [PQ.Additive] [P'.Additive] [Qt'.Additive] [PQ'.Additive]
    [GA.Additive] [GB.Additive] [GC.Additive]
    (η₁ : GA ⋙ P' ≅ P ⋙ GB) (η₂ : GA ⋙ PQ' ≅ PQ ⋙ GC) (β : Qt ⋙ GC ⟶ GB ⋙ Qt')
    (θ : PQ ≅ P ⋙ Qt) (θ' : PQ' ≅ P' ⋙ Qt')
    (γ₁ : P.mapHomologicalComplex c ⋙ GB.mapHomologicalComplex c ⟶
      GA.mapHomologicalComplex c ⋙ P'.mapHomologicalComplex c)
    (hγ₁ : γ₁ = (Functor.mapHomologicalComplexCompIso (Iso.refl (P ⋙ GB)) c).hom ≫
      NatTrans.mapHomologicalComplex η₁.inv c ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (GA ⋙ P')) c).inv)
    (γ₂ : PQ.mapHomologicalComplex c ⋙ GC.mapHomologicalComplex c ⟶
      GA.mapHomologicalComplex c ⋙ PQ'.mapHomologicalComplex c)
    (hγ₂ : γ₂ = (Functor.mapHomologicalComplexCompIso (Iso.refl (PQ ⋙ GC)) c).hom ≫
      NatTrans.mapHomologicalComplex η₂.inv c ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (GA ⋙ PQ')) c).inv)
    (γβ : Qt.mapHomologicalComplex c ⋙ GC.mapHomologicalComplex c ⟶
      GB.mapHomologicalComplex c ⋙ Qt'.mapHomologicalComplex c)
    (hγβ : γβ = (Functor.mapHomologicalComplexCompIso (Iso.refl (Qt ⋙ GC)) c).hom ≫
      NatTrans.mapHomologicalComplex β c ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (GB ⋙ Qt')) c).inv)
    (h : ∀ F, GC.map (θ.hom.app F) ≫ β.app (P.obj F) ≫ Qt'.map (η₁.inv.app F) =
      η₂.inv.app F ≫ θ'.hom.app (GA.obj F))
    (K : HomologicalComplex VA c) :
    γ₂.app K ≫
        (Functor.mapHomologicalComplexCompIso θ'.symm c).inv.app
          ((GA.mapHomologicalComplex c).obj K) =
      (GC.mapHomologicalComplex c).map
          ((Functor.mapHomologicalComplexCompIso θ.symm c).inv.app K) ≫
        γβ.app ((P.mapHomologicalComplex c).obj K) ≫
        (Qt'.mapHomologicalComplex c).map (γ₁.app K) := by
  subst hγ₁ hγ₂ hγβ
  ext n
  have hn := h (K.X n)
  simp only [NatTrans.comp_app, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
    Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex_app_f, Iso.refl_hom,
    Iso.refl_inv, NatTrans.id_app, Iso.symm_inv]
  dsimp only [Functor.comp_obj, Functor.mapHomologicalComplex_obj_X]
  simp only [Category.id_comp, Category.comp_id]
  exact hn.symm


section Extension

variable {AX AXb AX' AXb' : Type*} [Category* AX] [Category* AXb] [Category* AX']
  [Category* AXb'] [Abelian AX] [Abelian AXb] [Abelian AX'] [Abelian AXb']
  [HasDerivedCategory AX] [HasDerivedCategory AXb] [HasDerivedCategory AX']
  [HasDerivedCategory AXb']
  {J : AX ⥤ AXb} {G : AX ⥤ AX'} {Φ : AXb ⥤ AXb'} {J' : AX' ⥤ AXb'}
  [J.Additive] [PreservesFiniteLimits J] [PreservesFiniteColimits J]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
  [J'.Additive] [PreservesFiniteLimits J'] [PreservesFiniteColimits J']

/-- **The base change of a derived exact functor along an isomorphism, after the derivation
unit**, for abstract abelian categories. Let `RJ ≅ J.mapDerivedCategory` and
`RJ' ≅ J'.mapDerivedCategory` be compatible with derivation units `uJ`, `uJ'` (`hJ`, `hJ'`) and
`iso : G ∘ RJ' ≅ RJ ∘ Φ` the isomorphism induced by `η : G ⋙ J' ≅ J ⋙ Φ` (`hiso`). Then the
inverse of `iso`, after `Φ` of the unit of `RJ`, is the degreewise inverse of `η` followed by the
unit of `RJ'`, read through the exactness comparisons. Stated for abstract categories, so that
the kernel never reduces the functors. -/
theorem derivedIsoOfNatIso_inv_fac {RJ : DerivedCategory AX ⥤ DerivedCategory AXb}
    {RJ' : DerivedCategory AX' ⥤ DerivedCategory AXb'}
    (uJ : J.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RJ)
    (uJ' : J'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RJ')
    (iJ : RJ ≅ J.mapDerivedCategory) (iJ' : RJ' ≅ J'.mapDerivedCategory)
    (hJ : ∀ K, uJ.app K ≫ iJ.hom.app (DerivedCategory.Q.obj K) =
      J.mapDerivedCategoryFactors.inv.app K)
    (hJ' : ∀ K, uJ'.app K ≫ iJ'.hom.app (DerivedCategory.Q.obj K) =
      J'.mapDerivedCategoryFactors.inv.app K)
    (η : G ⋙ J' ≅ J ⋙ Φ)
    (ct : J.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        Φ.mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ J'.mapHomologicalComplex (ComplexShape.up ℤ))
    (hct : ct = (Functor.mapHomologicalComplexCompIso (Iso.refl (J ⋙ Φ)) (ComplexShape.up ℤ)).hom ≫
      NatTrans.mapHomologicalComplex η.inv (ComplexShape.up ℤ) ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ J')) (ComplexShape.up ℤ)).inv)
    (iso : G.mapDerivedCategory ⋙ RJ' ≅ RJ ⋙ Φ.mapDerivedCategory)
    (hiso : iso = Functor.isoWhiskerLeft _ iJ' ≪≫
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso G J').symm ≪≫
      Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _ η ≪≫
      Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso J Φ ≪≫
      Functor.isoWhiskerRight iJ.symm _)
    (K : CochainComplex AX ℤ) :
    Φ.mapDerivedCategory.map (uJ.app K) ≫ iso.inv.app (DerivedCategory.Q.obj K) =
      Φ.mapDerivedCategoryFactors.hom.app ((J.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map (ct.app K) ≫
        uJ'.app ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        RJ'.map (G.mapDerivedCategoryFactors.inv.app K) := by
  subst hiso
  have hct' : ct.app K =
      (NatIso.mapHomologicalComplex η (ComplexShape.up ℤ)).inv.app K := by
    subst hct
    ext n
    simp
  have nI := iJ'.inv.naturality (G.mapDerivedCategoryFactors.inv.app K)
  have hJ'K : J'.mapDerivedCategoryFactors.inv.app
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
      iJ'.inv.app (DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) =
      uJ'.app ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
    rw [← hJ', Category.assoc, Iso.hom_inv_id_app]
    exact Category.comp_id _
  simp only [Functor.comp_obj] at nI
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc,
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Q,
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_hom_app_Q,
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_inv_app_Q,
    Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, hJ, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, hct', nI, reassoc_of% hJ'K]

end Extension

end DerivedComparisonPaste

/-! ### Extension by zero along a cartesian square, after the derivation unit -/

/-- The derivation unit of `Rj_!`, followed by `Rj_! ≅ j_!` on derived categories, is the
exactness comparison of `j_!`. -/
theorem etaleModuleDerivedExtensionByZeroUnboundedUnit_app_comp_iso_hom {U X : Scheme.{u}}
    (j : U ⟶ X) [Etale j] (K : CochainComplex (EtaleModules.{u, r} Λ U) ℤ) :
    (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, r} Λ j).app K ≫
        (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ j).hom.app
          (DerivedCategory.Q.obj K) =
      (etaleModuleExtensionByZero.{u, r} Λ j).mapDerivedCategoryFactors.inv.app K := by
  rw [etaleModuleDerivedExtensionByZeroUnboundedIso,
    Stacks.Injectives.KInjectiveResolution.isoMapDerivedCategoryOfIsRightDerivedFunctor,
    Functor.rightDerivedNatIso_hom, Functor.rightDerivedNatTrans_app]
  simp

section CubeIso

variable {X X' Xb Xb' : Scheme.{u}} {g' : X' ⟶ X} {j : X ⟶ Xb} {j' : X' ⟶ Xb'} {φ : Xb' ⟶ Xb}
  [Etale j] [Etale j']

/-- The inverse of an isomorphism `η : (g')⁻¹ ∘ j'_! ≅ j_! ∘ φ⁻¹`, applied degreewise to
complexes. The isomorphism is a variable, so that the kernel never unfolds it. -/
def etaleModuleComplexExtensionByZeroCubeMapOf
    (η : etaleModuleInverseImage.{u, r} Λ g' ⋙ etaleModuleExtensionByZero.{u, r} Λ j' ≅
      etaleModuleExtensionByZero.{u, r} Λ j ⋙ etaleModuleInverseImage.{u, r} Λ φ) :
    ((etaleModuleExtensionByZero.{u, r} Λ j).mapHomologicalComplex _ ⋙
        (etaleModuleInverseImage.{u, r} Λ φ).mapHomologicalComplex _ :
        CochainComplex (EtaleModules.{u, r} Λ X) ℤ ⥤ CochainComplex (EtaleModules.{u, r} Λ Xb') ℤ) ⟶
      ((etaleModuleInverseImage.{u, r} Λ g').mapHomologicalComplex _ ⋙
        (etaleModuleExtensionByZero.{u, r} Λ j').mapHomologicalComplex _ :
        CochainComplex (EtaleModules.{u, r} Λ X) ℤ ⥤
          CochainComplex (EtaleModules.{u, r} Λ Xb') ℤ) :=
  (Functor.mapHomologicalComplexCompIso (Iso.refl _) _).hom ≫
    NatTrans.mapHomologicalComplex η.inv _ ≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) _).inv

/-- **The inverse of `(g')⁻¹ ∘ Rj'_! ≅ Rj_! ∘ φ⁻¹` after the derivation unit**: at a complex `K`,
`φ⁻¹` of the derivation unit of `Rj_!` followed by the inverse of
`Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroUnboundedCubeIso` is the degreewise
inverse of the underived isomorphism followed by the derivation unit of `Rj'_!`, read through the
exactness comparisons of the inverse images. -/
theorem etaleModuleDerivedExtensionByZeroUnboundedCubeIso_inv_fac (hc : IsPullback g' j' j φ)
    (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) :
    (etaleModuleDerivedInverseImage.{u, r} Λ φ).map
        ((etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, r} Λ j).app K) ≫
      (etaleModuleDerivedExtensionByZeroUnboundedCubeIso Λ hc).inv.app (DerivedCategory.Q.obj K) =
    (etaleModuleInverseImage.{u, r} Λ φ).mapDerivedCategoryFactors.hom.app
        (((etaleModuleExtensionByZero.{u, r} Λ j).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((etaleModuleComplexExtensionByZeroCubeMapOf Λ
        (etaleModuleInverseImageExtensionByZeroIso.{u, r} Λ hc)).app K) ≫
      (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, r} Λ j').app
        (((etaleModuleInverseImage.{u, r} Λ g').mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
      (etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j').map
        ((etaleModuleInverseImage.{u, r} Λ g').mapDerivedCategoryFactors.inv.app K) :=
  DerivedComparisonPaste.derivedIsoOfNatIso_inv_fac
    (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, r} Λ j)
    (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, r} Λ j')
    (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ j)
    (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ j')
    (etaleModuleDerivedExtensionByZeroUnboundedUnit_app_comp_iso_hom Λ j)
    (etaleModuleDerivedExtensionByZeroUnboundedUnit_app_comp_iso_hom Λ j')
    (etaleModuleInverseImageExtensionByZeroIso.{u, r} Λ hc) _ rfl _ rfl K

end CubeIso

/-! ### The refinement comparison and base change, degreewise -/

section Degreewise

variable {X X' Xb₁ Xb₂ Xb₁' Xb₂' : Scheme.{u}} {g' : X' ⟶ X} {j₁ : X ⟶ Xb₁} {j₂ : X ⟶ Xb₂}
  {j₁' : X' ⟶ Xb₁'} {j₂' : X' ⟶ Xb₂'} {p : Xb₁ ⟶ Xb₂} {p' : Xb₁' ⟶ Xb₂'}
  {φ₁ : Xb₁' ⟶ Xb₁} {φ₂ : Xb₂' ⟶ Xb₂} [Etale j₁] [Etale j₂] [Etale j₁'] [Etale j₂']

/-- **Degreewise pasting of the comparisons of [Stacks, Tag 0F7G] and [Stacks, Tag 03S6] with a
base change map**: if the isomorphisms `θ : j₂_! ≅ j₁_! ∘ p_*`, `θ'`, `η₁`, `η₂` and the
comparison `β` paste on sheaves (`h`), they paste on complexes. All the comparisons, and the
schemes, are variables, so that the kernel never unfolds them. -/
theorem etaleModuleComplexRefinement_baseChange_of
    (η₁ : etaleModuleInverseImage.{u, r} Λ g' ⋙ etaleModuleExtensionByZero.{u, r} Λ j₁' ≅
      etaleModuleExtensionByZero.{u, r} Λ j₁ ⋙ etaleModuleInverseImage.{u, r} Λ φ₁)
    (η₂ : etaleModuleInverseImage.{u, r} Λ g' ⋙ etaleModuleExtensionByZero.{u, r} Λ j₂' ≅
      etaleModuleExtensionByZero.{u, r} Λ j₂ ⋙ etaleModuleInverseImage.{u, r} Λ φ₂)
    (β : etaleModuleDirectImage.{u, r} Λ p ⋙ etaleModuleInverseImage.{u, r} Λ φ₂ ⟶
      etaleModuleInverseImage.{u, r} Λ φ₁ ⋙ etaleModuleDirectImage.{u, r} Λ p')
    (θ : etaleModuleExtensionByZero.{u, r} Λ j₂ ≅
      etaleModuleExtensionByZero.{u, r} Λ j₁ ⋙ etaleModuleDirectImage.{u, r} Λ p)
    (θ' : etaleModuleExtensionByZero.{u, r} Λ j₂' ≅
      etaleModuleExtensionByZero.{u, r} Λ j₁' ⋙ etaleModuleDirectImage.{u, r} Λ p')
    (h : ∀ F, (etaleModuleInverseImage.{u, r} Λ φ₂).map (θ.hom.app F) ≫
        β.app ((etaleModuleExtensionByZero.{u, r} Λ j₁).obj F) ≫
        (etaleModuleDirectImage.{u, r} Λ p').map (η₁.inv.app F) =
      η₂.inv.app F ≫ θ'.hom.app ((etaleModuleInverseImage.{u, r} Λ g').obj F))
    (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) :
    (etaleModuleComplexExtensionByZeroCubeMapOf Λ η₂).app K ≫
        (Functor.mapHomologicalComplexCompIso θ'.symm (ComplexShape.up ℤ)).inv.app
          (((etaleModuleInverseImage.{u, r} Λ g').mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) =
      ((etaleModuleInverseImage.{u, r} Λ φ₂).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((Functor.mapHomologicalComplexCompIso θ.symm (ComplexShape.up ℤ)).inv.app K) ≫
        (etaleModuleComplexBaseChangeUnboundedOf.{u, r} Λ p φ₂ φ₁ p' β).app
          (((etaleModuleExtensionByZero.{u, r} Λ j₁).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
        ((etaleModuleDirectImage.{u, r} Λ p').mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((etaleModuleComplexExtensionByZeroCubeMapOf Λ η₁).app K) :=
  DerivedComparisonPaste.mapHomologicalComplex_refinement_paste η₁ η₂ β θ θ' _ rfl _ rfl _ rfl h K

end Degreewise

/-- **The comparisons of [Stacks, Tag 0F7G] commute with base change, degreewise**: the
degreewise form of `Stacks.EtaleCohomology.etaleModuleRefinementComparison_baseChange`, for an
arbitrary cube of schemes and with the comparisons `θ`, `θ'` and the base change map `β` as
variables, so that the kernel never reduces the schemes or unfolds the comparisons. -/
theorem etaleModuleComplexRefinementComparison_baseChange
    {X X' Xb₁ Xb₂ Xb₁' Xb₂' : Scheme.{u}} {g' : X' ⟶ X} {j₁ : X ⟶ Xb₁} {j₂ : X ⟶ Xb₂}
    {j₁' : X' ⟶ Xb₁'} {j₂' : X' ⟶ Xb₂'} {p : Xb₁ ⟶ Xb₂} {p' : Xb₁' ⟶ Xb₂'}
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] [IsOpenImmersion j₁'] [IsOpenImmersion j₂']
    [IsSeparated p] [IsSeparated p'] (hjk : j₁ ≫ p = j₂) (hjk' : j₁' ≫ p' = j₂')
    {φ₁ : Xb₁' ⟶ Xb₁} {φ₂ : Xb₂' ⟶ Xb₂} (hc₁ : IsPullback g' j₁' j₁ φ₁)
    (hc₂ : IsPullback g' j₂' j₂ φ₂) (wp : p' ≫ φ₂ = φ₁ ≫ p)
    (β : etaleModuleDirectImage.{u, r} Λ p ⋙ etaleModuleInverseImage.{u, r} Λ φ₂ ⟶
      etaleModuleInverseImage.{u, r} Λ φ₁ ⋙ etaleModuleDirectImage.{u, r} Λ p')
    (hβ : β = etaleModuleBaseChange.{u, r} Λ p p' φ₂ φ₁ wp)
    (θ : etaleModuleExtensionByZero.{u, r} Λ j₂ ≅
      etaleModuleExtensionByZero.{u, r} Λ j₁ ⋙ etaleModuleDirectImage.{u, r} Λ p)
    (hθ : θ.hom = etaleModuleRefinementComparison Λ hjk)
    (θ' : etaleModuleExtensionByZero.{u, r} Λ j₂' ≅
      etaleModuleExtensionByZero.{u, r} Λ j₁' ⋙ etaleModuleDirectImage.{u, r} Λ p')
    (hθ' : θ'.hom = etaleModuleRefinementComparison Λ hjk')
    (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) :
    (etaleModuleComplexExtensionByZeroCubeMapOf Λ
        (etaleModuleInverseImageExtensionByZeroIso.{u, r} Λ hc₂)).app K ≫
        (Functor.mapHomologicalComplexCompIso θ'.symm (ComplexShape.up ℤ)).inv.app
          (((etaleModuleInverseImage.{u, r} Λ g').mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) =
      ((etaleModuleInverseImage.{u, r} Λ φ₂).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((Functor.mapHomologicalComplexCompIso θ.symm (ComplexShape.up ℤ)).inv.app K) ≫
        (etaleModuleComplexBaseChangeUnboundedOf.{u, r} Λ p φ₂ φ₁ p' β).app
          (((etaleModuleExtensionByZero.{u, r} Λ j₁).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
        ((etaleModuleDirectImage.{u, r} Λ p').mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((etaleModuleComplexExtensionByZeroCubeMapOf Λ
            (etaleModuleInverseImageExtensionByZeroIso.{u, r} Λ hc₁)).app K) :=
  etaleModuleComplexRefinement_baseChange_of Λ _ _ β θ θ' (fun F => by
    subst hβ
    have h := NatTrans.congr_app (etaleModuleRefinementComparison_baseChange Λ hjk hjk' hc₁ hc₂
      wp) F
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Stacks.Cohomology.DerivedBaseChangePlus.pasteV, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id] at h
    rw [hθ, hθ']
    exact h) K


/-! ### The comparison along the identity of a compactification -/

section Identity

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- The derivation unit of the derived direct image along an identity is invertible at every
complex. -/
lemma isIso_etaleModuleDerivedDirectImageUnboundedUnit_app_id (Z : Scheme.{u})
    (L : CochainComplex (EtaleModules.{u, r} Λ Z) ℤ) :
    IsIso ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ (𝟙 Z)).app L) := by
  have h := etaleModuleDerivedDirectImageUnboundedIdIso_inv_app_Q (Λ := Λ) (X := Z) L
  have : IsIso (DerivedCategory.Q.map
      ((Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).inv.app L ≫
        (NatIso.mapHomologicalComplex (etaleModuleDirectImageIdIso.{u, r} Λ Z)
          (ComplexShape.up ℤ)).inv.app L) ≫
      (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ (𝟙 Z)).app L) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_left (DerivedCategory.Q.map
      ((Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).inv.app L ≫
        (NatIso.mapHomologicalComplex (etaleModuleDirectImageIdIso.{u, r} Λ Z)
          (ComplexShape.up ℤ)).inv.app L))
    ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ (𝟙 Z)).app L)

/-- The map `Rj_! ⟶ Rj_! ∘ R(id)_*` of [Stacks, Tag 0F7G] along the identity of a
compactification is invertible. -/
instance isIso_derivedRefinementComparisonUnboundedUniv_id (j : CompactificationOf (Over.mk f)) :
    IsIso (derivedRefinementComparisonUnboundedUniv Λ (𝟙 j)) := by
  refine isIso_app_Q_of_isKInjective_univ Λ _ fun I hI => ?_
  have h := Stacks.DerivedBaseChange.compComparison_fac_app
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, r} Λ j.immersion)
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ (CompactificationOf.Hom.map (𝟙 j)))
    (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, r} Λ j.immersion)
    (Functor.mapHomologicalComplexCompIso (refinementIsoUniv Λ (𝟙 j)).symm (ComplexShape.up ℤ)) I
  have := isIso_etaleModuleDerivedExtensionByZeroUnboundedUnit_app.{u, r} Λ j.immersion I hI
  have : IsIso ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ
      (CompactificationOf.Hom.map (𝟙 j))).app
        (((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)) :=
    isIso_etaleModuleDerivedDirectImageUnboundedUnit_app_id Λ j.space _
  exact IsIso.of_isIso_fac_left h

/-- **The comparisons `Rf_!^k ⟶ Rf_!^j` compose**, on `D(X_étale, Λ)`, for an arbitrary ring. -/
lemma derivedLowerShriekUnboundedHomUniv_comp {j k l : CompactificationOf (Over.mk f)}
    (g : j ⟶ k) (h : k ⟶ l) :
    derivedLowerShriekUnboundedHomUniv Λ (g ≫ h) =
      derivedLowerShriekUnboundedHomUniv Λ h ≫ derivedLowerShriekUnboundedHomUniv Λ g := by
  refine NatTrans.ext (funext fun K => ?_)
  simp only [NatTrans.comp_app, derivedLowerShriekUnboundedHomUniv_app]
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

/-- The comparison of `Rf_!` along the identity of a compactification is the identity, on
`D(X_étale, Λ)`, for an arbitrary ring. -/
lemma derivedLowerShriekUnboundedHomUniv_id (j : CompactificationOf (Over.mk f)) :
    derivedLowerShriekUnboundedHomUniv Λ (𝟙 j) = 𝟙 _ := by
  have : IsIso (derivedLowerShriekUnboundedHomUniv Λ (𝟙 j)) := by
    dsimp only [derivedLowerShriekUnboundedHomUniv]
    infer_instance
  have h := derivedLowerShriekUnboundedHomUniv_comp Λ (𝟙 j) (𝟙 j)
  rw [Category.comp_id] at h
  rw [← cancel_mono (derivedLowerShriekUnboundedHomUniv Λ (𝟙 j)), Category.id_comp]
  exact h.symm

/-- The isomorphism of `Rf_!` along the identity of a compactification is the identity. -/
lemma derivedLowerShriekUnboundedHomIsoUniv_id [CompactSpace Y]
    (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) (j : CompactificationOf (Over.mk f)) :
    derivedLowerShriekUnboundedHomIsoUniv Λ (𝟙 j) hΛ = Iso.refl _ :=
  Iso.ext (derivedLowerShriekUnboundedHomUniv_id Λ j)

end Identity


section Naturality

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
  {j₁ j₂ : CompactificationOf (Over.mk f)} {j₁' j₂' : CompactificationOf (Over.mk f')}
  (ψ : j₁ ⟶ j₂) (ψ' : j₁' ⟶ j₂') (φ₁ : j₁'.space ⟶ j₁.space) (φ₂ : j₂'.space ⟶ j₂.space)
  (hc₁ : IsPullback g' j₁'.immersion j₁.immersion φ₁)
  (hc₂ : IsPullback g' j₂'.immersion j₂.immersion φ₂)
  (wp : CompactificationOf.Hom.map ψ' ≫ φ₂ = φ₁ ≫ CompactificationOf.Hom.map ψ)
  (w₁ : j₁'.toBase ≫ g = φ₁ ≫ j₁.toBase) (w₂ : j₂'.toBase ≫ g = φ₂ ≫ j₂.toBase)

/-- **Base change maps of unbounded direct images compose along a morphism of
compactifications**: the base change map of `f̄₁ = p ≫ f̄₂`, read through the composition
comparisons `Rf̄₁_* ⟶ Rp_* ∘ Rf̄₂_*`, is the vertical pasting of the base change maps of `p` and of
`f̄₂`. -/
theorem derivedBaseComparisonUnboundedUniv_baseChange :
    etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ j₁.toBase g φ₁ j₁'.toBase w₁.symm ≫
        Functor.whiskerLeft (etaleModuleDerivedInverseImage.{u, r} Λ φ₁)
          (derivedBaseComparisonUnboundedUniv Λ ψ') =
      Functor.whiskerRight (derivedBaseComparisonUnboundedUniv Λ ψ)
          (etaleModuleDerivedInverseImage.{u, r} Λ g) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft
          (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ (CompactificationOf.Hom.map ψ))
          (etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ j₂.toBase g φ₂ j₂'.toBase w₂.symm) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ (CompactificationOf.Hom.map ψ) φ₂ φ₁
            (CompactificationOf.Hom.map ψ') wp.symm)
          (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j₂'.toBase) ≫
        (Functor.associator _ _ _).hom := by
  rw [derivedBaseComparisonUnboundedUniv_eq_lerayIso_hom,
    derivedBaseComparisonUnboundedUniv_eq_lerayIso_hom]
  exact etaleModuleDerivedBaseChangeUnbounded_comp Λ (CompactificationOf.Hom.map ψ) j₂.toBase
    j₁.toBase (CompactificationOf.map_comp_toBase ψ).symm (CompactificationOf.Hom.map ψ')
    j₂'.toBase j₁'.toBase (CompactificationOf.map_comp_toBase ψ').symm φ₁ φ₂ g wp.symm w₂.symm
    w₁.symm

/-- `derivedRefinementComparisonUnboundedUniv_baseChange` with the underived base change map as a
variable `β`, so that the kernel never unfolds it. For a cube
of compactifications through two morphisms of compactifications, the base change of the map
`Rj₂_! ⟶ Rp_* ∘ Rj₁_!` is the map of the base-changed morphism, read through the isomorphisms
`(g')⁻¹ ∘ Rj'_! ≅ Rj_! ∘ φ⁻¹` and the base change map of `p`. -/
theorem derivedRefinementComparisonUnboundedUniv_baseChange_of
    (β : etaleModuleDirectImage.{u, r} Λ (CompactificationOf.Hom.map ψ) ⋙
        etaleModuleInverseImage.{u, r} Λ φ₂ ⟶
      etaleModuleInverseImage.{u, r} Λ φ₁ ⋙
        etaleModuleDirectImage.{u, r} Λ (CompactificationOf.Hom.map ψ'))
    (hβ : β = etaleModuleBaseChange.{u, r} Λ (CompactificationOf.Hom.map ψ)
      (CompactificationOf.Hom.map ψ') φ₂ φ₁ wp) :
    Functor.whiskerRight (derivedRefinementComparisonUnboundedUniv Λ ψ)
        (etaleModuleDerivedInverseImage.{u, r} Λ φ₂) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j₁.immersion)
        (etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ (CompactificationOf.Hom.map ψ) φ₂ φ₁
          (CompactificationOf.Hom.map ψ') wp.symm) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (etaleModuleDerivedExtensionByZeroUnboundedCubeIso Λ hc₁).inv
        (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ (CompactificationOf.Hom.map ψ')) ≫
      (Functor.associator _ _ _).hom =
    (etaleModuleDerivedExtensionByZeroUnboundedCubeIso Λ hc₂).inv ≫
      Functor.whiskerLeft (etaleModuleDerivedInverseImage.{u, r} Λ g')
        (derivedRefinementComparisonUnboundedUniv Λ ψ') := by
  have hbQ := etaleModuleDerivedBaseChangeUnbounded_fac Λ (CompactificationOf.Hom.map ψ) φ₂ φ₁
    (CompactificationOf.Hom.map ψ') wp.symm
  simp only [etaleModuleComplexBaseChangeUnbounded_eq, ← hβ] at hbQ
  exact (DerivedComparisonPaste.derivedComparison_vertical_paste_of_hom
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, r} Λ j₁.immersion)
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ (CompactificationOf.Hom.map ψ))
    (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, r} Λ j₂.immersion)
    (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, r} Λ j₁'.immersion)
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ (CompactificationOf.Hom.map ψ'))
    (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, r} Λ j₂'.immersion)
    (etaleModuleInverseImage.{u, r} Λ g').mapDerivedCategoryFactors
    (etaleModuleInverseImage.{u, r} Λ φ₁).mapDerivedCategoryFactors
    (etaleModuleInverseImage.{u, r} Λ φ₂).mapDerivedCategoryFactors
    (etaleModuleComplexExtensionByZeroCubeMapOf Λ
            (etaleModuleInverseImageExtensionByZeroIso.{u, r} Λ hc₁))
    (etaleModuleComplexBaseChangeUnboundedOf.{u, r} Λ (CompactificationOf.Hom.map ψ) φ₂ φ₁
      (CompactificationOf.Hom.map ψ') β)
    (etaleModuleComplexExtensionByZeroCubeMapOf Λ
            (etaleModuleInverseImageExtensionByZeroIso.{u, r} Λ hc₂))
    (etaleModuleDerivedExtensionByZeroUnboundedCubeIso Λ hc₁).inv
    (etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ (CompactificationOf.Hom.map ψ) φ₂ φ₁
      (CompactificationOf.Hom.map ψ') wp.symm)
    (etaleModuleDerivedExtensionByZeroUnboundedCubeIso Λ hc₂).inv
    (Functor.mapHomologicalComplexCompIso (refinementIsoUniv Λ ψ).symm (ComplexShape.up ℤ))
    (Functor.mapHomologicalComplexCompIso (refinementIsoUniv Λ ψ').symm (ComplexShape.up ℤ))
    (derivedRefinementComparisonUnboundedUniv Λ ψ) (derivedRefinementComparisonUnboundedUniv Λ ψ')
    (etaleModuleDerivedExtensionByZeroUnboundedCubeIso_inv_fac Λ hc₁) hbQ
    (etaleModuleDerivedExtensionByZeroUnboundedCubeIso_inv_fac Λ hc₂)
    (fun K => Stacks.DerivedBaseChange.compComparison_fac_app
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _ _ _ _ K)
    (fun K => Stacks.DerivedBaseChange.compComparison_fac_app
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _ _ _ _ K)
    (etaleModuleComplexRefinementComparison_baseChange Λ
      (CompactificationOf.immersion_comp_map ψ) (CompactificationOf.immersion_comp_map ψ') hc₁ hc₂
      wp β hβ (refinementIsoUniv Λ ψ) rfl (refinementIsoUniv Λ ψ') rfl)).symm

/-- **The map of [Stacks, Tag 0F7G] commutes with base change**, on `D(X_étale, Λ)`: for a cube
of compactifications through two morphisms of compactifications, the base change of the map
`Rj₂_! ⟶ Rp_* ∘ Rj₁_!` is the map of the base-changed morphism, read through the isomorphisms
`(g')⁻¹ ∘ Rj'_! ≅ Rj_! ∘ φ⁻¹` and the base change map of `p`. -/
theorem derivedRefinementComparisonUnboundedUniv_baseChange :
    Functor.whiskerRight (derivedRefinementComparisonUnboundedUniv Λ ψ)
        (etaleModuleDerivedInverseImage.{u, r} Λ φ₂) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j₁.immersion)
        (etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ (CompactificationOf.Hom.map ψ) φ₂ φ₁
          (CompactificationOf.Hom.map ψ') wp.symm) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (etaleModuleDerivedExtensionByZeroUnboundedCubeIso Λ hc₁).inv
        (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ (CompactificationOf.Hom.map ψ')) ≫
      (Functor.associator _ _ _).hom =
    (etaleModuleDerivedExtensionByZeroUnboundedCubeIso Λ hc₂).inv ≫
      Functor.whiskerLeft (etaleModuleDerivedInverseImage.{u, r} Λ g')
        (derivedRefinementComparisonUnboundedUniv Λ ψ') :=
  derivedRefinementComparisonUnboundedUniv_baseChange_of Λ ψ ψ' φ₁ φ₂ hc₁ hc₂ wp _ rfl

include wp in
/-- **The base change map of a cube of compactifications is natural in morphisms of
compactifications**, on `D(X_étale, Λ)` ([Stacks, Tag 0F7L]): along `ψ : j₁ ⟶ j₂` and
`ψ' : j₁' ⟶ j₂'` compatible with the two cubes, the base change maps correspond under the
comparisons `Rf_!^{j₂} ⟶ Rf_!^{j₁}` of [Stacks, Tag 0F7I]. -/
theorem derivedLowerShriekUnboundedBaseChangeCube_naturality :
    Functor.whiskerRight (derivedLowerShriekUnboundedHomUniv Λ ψ)
        (etaleModuleDerivedInverseImage.{u, r} Λ g) ≫
      derivedLowerShriekUnboundedBaseChangeCube Λ j₁ j₁' φ₁ hc₁ w₁ =
    derivedLowerShriekUnboundedBaseChangeCube Λ j₂ j₂' φ₂ hc₂ w₂ ≫
      Functor.whiskerLeft (etaleModuleDerivedInverseImage.{u, r} Λ g')
        (derivedLowerShriekUnboundedHomUniv Λ ψ') := by
  have A1 := derivedBaseComparisonUnboundedUniv_baseChange Λ ψ ψ' φ₁ φ₂ wp w₁ w₂
  have A2 := derivedRefinementComparisonUnboundedUniv_baseChange Λ ψ ψ' φ₁ φ₂ hc₁ hc₂ wp
  refine NatTrans.ext (funext fun K => ?_)
  have a1 := (etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ j₂.toBase g φ₂ j₂'.toBase
    w₂.symm).naturality ((derivedRefinementComparisonUnboundedUniv Λ ψ).app K)
  have a2 := NatTrans.congr_app A1
    ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j₁.immersion).obj K)
  have a3 := (inv (derivedBaseComparisonUnboundedUniv Λ ψ')).naturality
    ((etaleModuleDerivedExtensionByZeroUnboundedCubeIso Λ hc₁).inv.app K)
  have a4 := NatTrans.congr_app A2 K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Functor.comp_obj, Functor.comp_map] at a1 a2 a3 a4 ⊢
  simp only [derivedLowerShriekUnboundedBaseChangeCube, derivedLowerShriekUnboundedHomUniv_app,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp,
    Category.assoc, Functor.comp_obj]
  refine cube_hom_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a1 a2 a3 ?_ ?_ ?_
  · rw [← Functor.map_comp, ← Functor.map_comp, a4, Functor.map_comp]
  · rw [← Functor.map_comp, ← NatTrans.comp_app, IsIso.inv_hom_id, NatTrans.id_app]
    exact CategoryTheory.Functor.map_id _ _
  · exact (NatTrans.comp_app _ _ _).symm.trans ((congrArg (fun t => NatTrans.app t _)
      (IsIso.hom_inv_id (derivedBaseComparisonUnboundedUniv Λ ψ'))).trans (NatTrans.id_app _ _))

end Naturality

section Cube

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
  (sq : IsPullback g' f' f g) (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0)

/-- The base change map of a cube of compactifications is the base change map through the base
change of the compactification, followed by the canonical comparison of the two compactifications
of `f'`, on `D(X_étale, Λ)`. -/
theorem derivedLowerShriekUnboundedBaseChangeCube_eq [CompactSpace Y'] [QuasiSeparatedSpace Y']
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    (j : CompactificationOf (Over.mk f)) (j' : CompactificationOf (Over.mk f'))
    (φ : j'.space ⟶ j.space) (hc : IsPullback g' j'.immersion j.immersion φ)
    (w : j'.toBase ≫ g = φ ≫ j.toBase) :
    derivedLowerShriekUnboundedBaseChangeCube Λ j j' φ hc w =
      derivedLowerShriekUnboundedBaseChange.{u, r} Λ sq j ≫
        Functor.whiskerLeft (etaleModuleDerivedInverseImage.{u, r} Λ g')
          (derivedLowerShriekUnboundedCompactificationIsoUniv f' (j.baseChange sq) j' Λ
            hΛ).hom := by
  let κ := CompactificationOf.toBaseChange sq j j' φ hc.w.symm w
  have N := derivedLowerShriekUnboundedBaseChangeCube_naturality Λ (𝟙 j) κ φ
    (pullback.fst j.toBase g) hc (j.isPullback_baseChange sq)
    ((CompactificationOf.toBaseChange_map_fst sq j j' φ hc.w.symm w).trans
      (Category.comp_id _).symm) w pullback.condition.symm
  rw [derivedLowerShriekUnboundedHomUniv_id, Functor.whiskerRight_id', Category.id_comp] at N
  rw [N, derivedLowerShriekUnboundedBaseChange_eq_cube,
    derivedLowerShriekUnboundedCompactificationIsoUniv_of_hom f' Λ hΛ κ,
    derivedLowerShriekUnboundedHomIsoUniv_hom]

/-- **The unbounded base change maps of `Rf_!` do not depend on the compactification**: for two
compactifications `j₁` and `j₂` of `f`, the base change maps correspond under the canonical
comparisons for `f` and for `f'`. -/
theorem derivedLowerShriekUnboundedBaseChange_compactificationIso [CompactSpace Y]
    [QuasiSeparatedSpace Y] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [CompactSpace Y'] [QuasiSeparatedSpace Y'] [IsSeparated f'] [LocallyOfFiniteType f']
    [QuasiCompact f'] (j₁ j₂ : CompactificationOf (Over.mk f)) :
    Functor.whiskerRight (derivedLowerShriekUnboundedCompactificationIsoUniv f j₁ j₂ Λ hΛ).hom
        (etaleModuleDerivedInverseImage.{u, r} Λ g) ≫
      derivedLowerShriekUnboundedBaseChange.{u, r} Λ sq j₂ =
    derivedLowerShriekUnboundedBaseChange.{u, r} Λ sq j₁ ≫
      Functor.whiskerLeft (etaleModuleDerivedInverseImage.{u, r} Λ g')
        (derivedLowerShriekUnboundedCompactificationIsoUniv f' (j₁.baseChange sq)
          (j₂.baseChange sq) Λ hΛ).hom := by
  let l := IsCofiltered.min j₁ j₂
  let ψ₁ : l ⟶ j₁ := IsCofiltered.minToLeft j₁ j₂
  let ψ₂ : l ⟶ j₂ := IsCofiltered.minToRight j₁ j₂
  have e : ∀ {k : CompactificationOf (Over.mk f)} (ψ : l ⟶ k),
      Functor.whiskerRight (derivedLowerShriekUnboundedHomUniv Λ ψ)
          (etaleModuleDerivedInverseImage.{u, r} Λ g) ≫
        derivedLowerShriekUnboundedBaseChange.{u, r} Λ sq l =
      derivedLowerShriekUnboundedBaseChange.{u, r} Λ sq k ≫
        Functor.whiskerLeft (etaleModuleDerivedInverseImage.{u, r} Λ g')
          (derivedLowerShriekUnboundedHomUniv Λ (CompactificationOf.baseChangeHom sq ψ)) :=
    fun {k} ψ => derivedLowerShriekUnboundedBaseChangeCube_naturality Λ ψ
      (CompactificationOf.baseChangeHom sq ψ) (pullback.fst l.toBase g) (pullback.fst k.toBase g)
      (l.isPullback_baseChange sq) (k.isPullback_baseChange sq)
      (CompactificationOf.baseChangeHom_map_fst sq ψ) pullback.condition.symm
      pullback.condition.symm
  have h2 : Functor.whiskerRight (derivedLowerShriekUnboundedHomIsoUniv Λ ψ₂ hΛ).inv
        (etaleModuleDerivedInverseImage.{u, r} Λ g) ≫
        derivedLowerShriekUnboundedBaseChange.{u, r} Λ sq j₂ =
      derivedLowerShriekUnboundedBaseChange.{u, r} Λ sq l ≫
        Functor.whiskerLeft (etaleModuleDerivedInverseImage.{u, r} Λ g')
          (derivedLowerShriekUnboundedHomIsoUniv Λ (CompactificationOf.baseChangeHom sq ψ₂)
            hΛ).inv := by
    have e2 := e ψ₂
    rw [← derivedLowerShriekUnboundedHomIsoUniv_hom Λ ψ₂ hΛ,
      ← derivedLowerShriekUnboundedHomIsoUniv_hom Λ (CompactificationOf.baseChangeHom sq ψ₂)
        hΛ] at e2
    calc _ = Functor.whiskerRight (derivedLowerShriekUnboundedHomIsoUniv Λ ψ₂ hΛ).inv
            (etaleModuleDerivedInverseImage.{u, r} Λ g) ≫
          derivedLowerShriekUnboundedBaseChange.{u, r} Λ sq j₂ ≫
          Functor.whiskerLeft (etaleModuleDerivedInverseImage.{u, r} Λ g')
            (derivedLowerShriekUnboundedHomIsoUniv Λ (CompactificationOf.baseChangeHom sq ψ₂)
              hΛ).hom ≫
          Functor.whiskerLeft (etaleModuleDerivedInverseImage.{u, r} Λ g')
            (derivedLowerShriekUnboundedHomIsoUniv Λ (CompactificationOf.baseChangeHom sq ψ₂)
              hΛ).inv := by
          rw [← Functor.whiskerLeft_comp, Iso.hom_inv_id, Functor.whiskerLeft_id',
            Category.comp_id]
      _ = _ := by
          rw [← reassoc_of% e2, ← Category.assoc, ← Functor.whiskerRight_comp, Iso.inv_hom_id,
            Functor.whiskerRight_id', Category.id_comp]
  have hC : derivedLowerShriekUnboundedCompactificationIsoUniv f j₁ j₂ Λ hΛ =
      derivedLowerShriekUnboundedHomIsoUniv Λ ψ₁ hΛ ≪≫
        (derivedLowerShriekUnboundedHomIsoUniv Λ ψ₂ hΛ).symm :=
    IsCofiltered.isoSystemComparison_eq _
      (fun a b => derivedLowerShriekUnboundedHomIsoUniv_comp Λ a b hΛ) ψ₁ ψ₂
  have hC' : derivedLowerShriekUnboundedCompactificationIsoUniv f' (j₁.baseChange sq)
        (j₂.baseChange sq) Λ hΛ =
      derivedLowerShriekUnboundedHomIsoUniv Λ (CompactificationOf.baseChangeHom sq ψ₁) hΛ ≪≫
        (derivedLowerShriekUnboundedHomIsoUniv Λ (CompactificationOf.baseChangeHom sq ψ₂)
          hΛ).symm :=
    IsCofiltered.isoSystemComparison_eq _
      (fun a b => derivedLowerShriekUnboundedHomIsoUniv_comp Λ a b hΛ) _ _
  rw [hC, hC']
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.whiskerRight_comp, Functor.whiskerLeft_comp,
    Category.assoc]
  rw [h2, derivedLowerShriekUnboundedHomIsoUniv_hom, derivedLowerShriekUnboundedHomIsoUniv_hom,
    reassoc_of% (e ψ₁)]

end Cube

end Stacks.EtaleCohomology

end
