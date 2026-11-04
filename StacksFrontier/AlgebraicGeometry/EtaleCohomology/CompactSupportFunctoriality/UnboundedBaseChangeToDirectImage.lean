module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportFunctoriality.UnboundedToDirectImage
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ProperBaseChangeUnbounded
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.UnderivedBaseChangePasting
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.UnderivedExtensionByZeroPasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleDerivedBaseChangeUnboundedResolution
import StacksCore.Tactic.StacksAttribute

/-!
# The map `Rf_! ⟶ Rf_*` and base change, on `D(X_étale, Λ)`

The map `Rf_! ⟶ Rf_*` of [Stacks, Tag 0H6X] on unbounded derived categories
(`Stacks.EtaleCohomology.derivedLowerShriekUnboundedToDirectImage`) is compatible with the base
change map `g⁻¹ ∘ Rf_! ⟶ Rf'_! ∘ (g')⁻¹` of [Stacks, Tag 0F7L]
(`Stacks.EtaleCohomology.derivedLowerShriekUnboundedBaseChange`, an isomorphism when `Λ` is
torsion) and the base change map `g⁻¹ ∘ Rf_* ⟶ Rf'_* ∘ (g')⁻¹` of Cohomology on Sites,
Remark 07A7 (`Stacks.EtaleCohomology.etaleModuleDerivedBaseChangeUnbounded`): this is
compatibility (2) of the remark, whose proof the source omits.

## Main results

* `Stacks.EtaleCohomology.etaleModuleDerivedBaseChangeUnbounded_comp`: the unbounded base change
  maps compose along a composite of direct images, read through the Leray isomorphisms.
* `Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroToDirectImageUnbounded_baseChange`:
  the map `Rj_! ⟶ Rj_*` commutes with base change.
* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedBaseChange_comp_toDirectImage`:
  **[Stacks, Tag 0H6X], compatibility (2), on `D(X_étale, Λ)`**.

## References

* [Stacks Project, Tag 0H6X](https://stacks.math.columbia.edu/tag/0H6X)
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

variable {CA CB CC CA' CB' CC' DA DB DC DA' DB' DC' : Type*} [Category* CA] [Category* CB]
  [Category* CC] [Category* CA'] [Category* CB'] [Category* CC'] [Category* DA] [Category* DB]
  [Category* DC] [Category* DA'] [Category* DB'] [Category* DC']
  {QA : CA ⥤ DA} {QB : CB ⥤ DB} {QC : CC ⥤ DC} {QA' : CA' ⥤ DA'} {QB' : CB' ⥤ DB'}
  {QC' : CC' ⥤ DC'}
  {P : CA ⥤ CB} {Qt : CB ⥤ CC} {PQ : CA ⥤ CC} {P' : CA' ⥤ CB'} {Qt' : CB' ⥤ CC'}
  {PQ' : CA' ⥤ CC'} {GA : CA ⥤ CA'} {GB : CB ⥤ CB'} {GC : CC ⥤ CC'}
  {RP : DA ⥤ DB} {RQ : DB ⥤ DC} {RPQ : DA ⥤ DC} {RP' : DA' ⥤ DB'} {RQ' : DB' ⥤ DC'}
  {RPQ' : DA' ⥤ DC'} {GDA : DA ⥤ DA'} {GDB : DB ⥤ DB'} {GDC : DC ⥤ DC'}

/-- **Comparisons of right derived functors paste vertically**, for abstract categories. Let
`bP`, `bQ` and `bPQ` be the transformations `RP ⋙ GDB ⟶ GDA ⋙ RP'` (and so on) induced by
comparisons `cP`, `cQ`, `cPQ` of the underlying functors and by comparisons `ΦA`, `ΦB`, `ΦC`
of the localizations (the hypotheses `hbP`, `hbQ`, `hbPQ`), and `L`, `L'` the comparisons
`RPQ ≅ RP ⋙ RQ` induced by `P ⋙ Qt ≅ PQ` (the hypotheses `hL`, `hL'`). If the comparisons
`cP`, `cQ`, `cPQ` paste (`hc`), so do `bP`, `bQ` and `bPQ`, read through `L` and `L'`. Stated
for abstract categories, so that the kernel never reduces the functors. -/
theorem derivedComparison_vertical_paste (W : MorphismProperty CA) [QA.IsLocalization W]
    (uP : P ⋙ QB ⟶ QA ⋙ RP) (uQ : Qt ⋙ QC ⟶ QB ⋙ RQ) (uPQ : PQ ⋙ QC ⟶ QA ⋙ RPQ)
    (uP' : P' ⋙ QB' ⟶ QA' ⋙ RP') (uQ' : Qt' ⋙ QC' ⟶ QB' ⋙ RQ')
    (uPQ' : PQ' ⋙ QC' ⟶ QA' ⋙ RPQ')
    [hR : (RPQ ⋙ GDC).IsRightDerivedFunctor
      (Functor.whiskerRight uPQ GDC ≫ (Functor.associator _ _ _).hom) W]
    (ΦA : QA ⋙ GDA ≅ GA ⋙ QA') (ΦB : QB ⋙ GDB ≅ GB ⋙ QB') (ΦC : QC ⋙ GDC ≅ GC ⋙ QC')
    (cP : P ⋙ GB ⟶ GA ⋙ P') (cQ : Qt ⋙ GC ⟶ GB ⋙ Qt') (cPQ : PQ ⋙ GC ⟶ GA ⋙ PQ')
    (bP : RP ⋙ GDB ⟶ GDA ⋙ RP') (bQ : RQ ⋙ GDC ⟶ GDB ⋙ RQ')
    (bPQ : RPQ ⋙ GDC ⟶ GDA ⋙ RPQ')
    (e : P ⋙ Qt ≅ PQ) (e' : P' ⋙ Qt' ≅ PQ') (L : RPQ ≅ RP ⋙ RQ) (L' : RPQ' ≅ RP' ⋙ RQ')
    (hbP : ∀ K, GDB.map (uP.app K) ≫ bP.app (QA.obj K) =
      ΦB.hom.app (P.obj K) ≫ QB'.map (cP.app K) ≫ uP'.app (GA.obj K) ≫ RP'.map (ΦA.inv.app K))
    (hbQ : ∀ K, GDC.map (uQ.app K) ≫ bQ.app (QB.obj K) =
      ΦC.hom.app (Qt.obj K) ≫ QC'.map (cQ.app K) ≫ uQ'.app (GB.obj K) ≫
        RQ'.map (ΦB.inv.app K))
    (hbPQ : ∀ K, GDC.map (uPQ.app K) ≫ bPQ.app (QA.obj K) =
      ΦC.hom.app (PQ.obj K) ≫ QC'.map (cPQ.app K) ≫ uPQ'.app (GA.obj K) ≫
        RPQ'.map (ΦA.inv.app K))
    (hL : ∀ K, uPQ.app K ≫ L.hom.app (QA.obj K) =
      QC.map (e.inv.app K) ≫ uQ.app (P.obj K) ≫ RQ.map (uP.app K))
    (hL' : ∀ K, uPQ'.app K ≫ L'.hom.app (QA'.obj K) =
      QC'.map (e'.inv.app K) ≫ uQ'.app (P'.obj K) ≫ RQ'.map (uP'.app K))
    (hc : ∀ K, cPQ.app K ≫ e'.inv.app (GA.obj K) =
      GC.map (e.inv.app K) ≫ cQ.app (P.obj K) ≫ Qt'.map (cP.app K)) :
    bPQ ≫ Functor.whiskerLeft GDA L'.hom =
      Functor.whiskerRight L.hom GDC ≫ (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft RP bQ ≫ (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight bP RQ' ≫ (Functor.associator _ _ _).hom := by
  refine Functor.rightDerived_ext _
    (Functor.whiskerRight uPQ GDC ≫ (Functor.associator _ _ _).hom) W _ _ _
    (NatTrans.ext (funext fun K => ?_))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Functor.comp_obj, Category.assoc]
  have nL := L'.hom.naturality (ΦA.inv.app K)
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


/-! ### `Rj_! ⟶ Rj_*` and base change, for abstract abelian categories -/

section Extension

variable {AX AXb AX' AXb' : Type*} [Category* AX] [Category* AXb] [Category* AX']
  [Category* AXb'] [Abelian AX] [Abelian AXb] [Abelian AX'] [Abelian AXb']
  [HasDerivedCategory AX] [HasDerivedCategory AXb] [HasDerivedCategory AX']
  [HasDerivedCategory AXb']
  {J Js : AX ⥤ AXb} {G : AX ⥤ AX'} {Φ : AXb ⥤ AXb'} {J' J's : AX' ⥤ AXb'}
  [J.Additive] [PreservesFiniteLimits J] [PreservesFiniteColimits J]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
  [J'.Additive] [PreservesFiniteLimits J'] [PreservesFiniteColimits J']
  [Js.Additive] [J's.Additive]

omit [HasDerivedCategory AX] [HasDerivedCategory AXb] [HasDerivedCategory AX']
  [HasDerivedCategory AXb'] [PreservesFiniteLimits J] [PreservesFiniteColimits J]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G] [PreservesFiniteLimits Φ]
  [PreservesFiniteColimits Φ] [PreservesFiniteLimits J'] [PreservesFiniteColimits J'] in
/-- **A degreewise comparison against an isomorphism**, for abstract categories: if
`Φ e ≫ β = η⁻¹ ≫ e' G` objectwise, the same holds for the maps they induce degreewise on
complexes. Stated for abstract categories, so that the kernel never reduces the functors. -/
theorem mapHomologicalComplex_iso_comparison {ι : Type*} {c : ComplexShape ι}
    (η : G ⋙ J' ≅ J ⋙ Φ) (e : J ⟶ Js) (e' : J' ⟶ J's) (β : Js ⋙ Φ ⟶ G ⋙ J's)
    (γ : Js.mapHomologicalComplex c ⋙ Φ.mapHomologicalComplex c ⟶
      G.mapHomologicalComplex c ⋙ J's.mapHomologicalComplex c)
    (hγ : γ = (Functor.mapHomologicalComplexCompIso (Iso.refl (Js ⋙ Φ)) c).hom ≫
      NatTrans.mapHomologicalComplex β c ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ J's)) c).inv)
    (h : ∀ F, Φ.map (e.app F) ≫ β.app F = η.inv.app F ≫ e'.app (G.obj F))
    (K : HomologicalComplex AX c) :
    (NatIso.mapHomologicalComplex η c).inv.app K ≫
        (NatTrans.mapHomologicalComplex e' c).app ((G.mapHomologicalComplex c).obj K) =
      (Φ.mapHomologicalComplex c).map ((NatTrans.mapHomologicalComplex e c).app K) ≫
        γ.app K := by
  subst hγ
  ext n
  have hn := h (K.X n)
  simp only [NatTrans.comp_app, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
    Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex_app_f, Iso.refl_hom,
    Iso.refl_inv, NatTrans.id_app, NatIso.mapHomologicalComplex_inv_app_f]
  dsimp only [Functor.comp_obj, Functor.mapHomologicalComplex_obj_X]
  simp only [Category.id_comp, Category.comp_id]
  exact hn.symm

/-- **The map `Rj_! ⟶ Rj_*` commutes with base change**, for abstract abelian categories. Let
`J ⟶ Js` and `J' ⟶ J's` be the transformations `e`, `e'` (playing `j_! ⟶ j_*`), with `J`, `J'`
exact and `Rj_! ≅ J`, `Rj'_! ≅ J'` on derived categories (`iJ`, `iJ'`), `ε`, `ε'` their derived
maps (characterized by `hε`, `hε'`), `b` the derived comparison `RJs ⋙ Φ ⟶ G ⋙ RJ's` induced by
`β` (`hb`, `hct`), and `iso` the isomorphism `G ⋙ RJ' ≅ RJ ⋙ Φ` induced by `η` (`hiso`). If
`Φ e ≫ β = η⁻¹ ≫ e' G` (`hund`), then `iso⁻¹ ≫ G ε' = ε Φ ≫ b`. Stated for abstract categories,
so that the kernel never reduces the functors. -/
theorem derivedExtensionByZero_comparison_baseChange
    {RJ RJs : DerivedCategory AX ⥤ DerivedCategory AXb}
    {RJ' RJ's : DerivedCategory AX' ⥤ DerivedCategory AXb'}
    (iJ : RJ ≅ J.mapDerivedCategory) (iJ' : RJ' ≅ J'.mapDerivedCategory)
    (uJs : Js.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RJs)
    (uJ's : J's.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RJ's)
    (e : J ⟶ Js) (e' : J' ⟶ J's) (β : Js ⋙ Φ ⟶ G ⋙ J's) (η : G ⋙ J' ≅ J ⋙ Φ)
    (ε : RJ ⟶ RJs) (ε' : RJ' ⟶ RJ's)
    (b : RJs ⋙ Φ.mapDerivedCategory ⟶ G.mapDerivedCategory ⋙ RJ's)
    (ct : Js.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        Φ.mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ J's.mapHomologicalComplex (ComplexShape.up ℤ))
    (hct : ct = (Functor.mapHomologicalComplexCompIso (Iso.refl (Js ⋙ Φ)) (ComplexShape.up ℤ)).hom ≫
      NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ) ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ J's)) (ComplexShape.up ℤ)).inv)
    (iso : G.mapDerivedCategory ⋙ RJ' ≅ RJ ⋙ Φ.mapDerivedCategory)
    (hiso : iso = Functor.isoWhiskerLeft _ iJ' ≪≫
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso G J').symm ≪≫
      Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _ η ≪≫
      Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso J Φ ≪≫
      Functor.isoWhiskerRight iJ.symm _)
    (hε : ∀ K, J.mapDerivedCategoryFactors.inv.app K ≫ iJ.inv.app (DerivedCategory.Q.obj K) ≫
        ε.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e (ComplexShape.up ℤ)).app K) ≫
        uJs.app K)
    (hε' : ∀ K, J'.mapDerivedCategoryFactors.inv.app K ≫ iJ'.inv.app (DerivedCategory.Q.obj K) ≫
        ε'.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e' (ComplexShape.up ℤ)).app K) ≫
        uJ's.app K)
    (hb : ∀ K, Φ.mapDerivedCategory.map (uJs.app K) ≫ b.app (DerivedCategory.Q.obj K) =
      Φ.mapDerivedCategoryFactors.hom.app ((Js.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map (ct.app K) ≫
        uJ's.app ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        RJ's.map (G.mapDerivedCategoryFactors.inv.app K))
    (hund : ∀ F, Φ.map (e.app F) ≫ β.app F = η.inv.app F ≫ e'.app (G.obj F)) :
    iso.inv ≫ Functor.whiskerLeft G.mapDerivedCategory ε' =
      Functor.whiskerRight ε Φ.mapDerivedCategory ≫ b := by
  subst hiso
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso AX (ComplexShape.up ℤ)) (fun K => ?_)
  have hε0 : ε.app (DerivedCategory.Q.obj K) = iJ.hom.app (DerivedCategory.Q.obj K) ≫
      J.mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e (ComplexShape.up ℤ)).app K) ≫
      uJs.app K := by
    rw [← hε, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app_assoc]
  have hdeg := mapHomologicalComplex_iso_comparison η e e' β ct hct hund K
  have nI := iJ'.inv.naturality (G.mapDerivedCategoryFactors.inv.app K)
  have nE := ε'.naturality (G.mapDerivedCategoryFactors.inv.app K)
  have nΦ := Φ.mapDerivedCategoryFactors.hom.naturality
    ((NatTrans.mapHomologicalComplex e (ComplexShape.up ℤ)).app K)
  have hε'K := hε' ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  simp only [Functor.comp_obj, Functor.comp_map] at nI nE nΦ
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Category.assoc, Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Q,
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_hom_app_Q,
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_inv_app_Q,
    Iso.inv_hom_id_app_assoc]
  rw [hε0]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [hb, reassoc_of% nΦ, reassoc_of% nI, nE, reassoc_of% hε'K]
  simp only [← CategoryTheory.Functor.map_comp_assoc, hdeg]

end Extension
/-! ### `Rf_! ⟶ Rf_*` and base change, for abstract categories -/

section LowerShriek

variable {DX DXb DY DX' DXb' DY' : Type*} [Category* DX] [Category* DXb] [Category* DY]
  [Category* DX'] [Category* DXb'] [Category* DY']
  {RJ RJs : DX ⥤ DXb} {Rfb : DXb ⥤ DY} {Rf : DX ⥤ DY} {GY : DY ⥤ DY'} {GX : DX ⥤ DX'}
  {GXb : DXb ⥤ DXb'} {RJ' RJ's : DX' ⥤ DXb'} {Rfb' : DXb' ⥤ DY'} {Rf' : DX' ⥤ DY'}

/-- **The map `Rf_! ⟶ Rf_*` commutes with base change**, for abstract categories. Let
`τ = (ε Rfb) ≫ L⁻¹ : RJ ⋙ Rfb ⟶ Rf` and `τ' = (ε' Rfb') ≫ L'⁻¹ : RJ' ⋙ Rfb' ⟶ Rf'` (playing
`Rf̄_* ∘ Rj_! ⟶ Rf̄_* ∘ Rj_* ≅ Rf_*`), and `bc = (RJ bFb) ≫ (iso⁻¹ Rfb')` (playing the base change
map of `Rf_!`). If the base change maps `bf`, `bFb`, `bJ` paste along the Leray isomorphisms `L`,
`L'` (`hA`) and `ε` commutes with base change (`hB`), then `bc ≫ GX τ' = τ GY ≫ bf`. Stated for
abstract categories, so that the kernel never reduces the functors. -/
theorem lowerShriekBaseChange_comp_toDirectImage_paste
    (ε : RJ ⟶ RJs) (ε' : RJ' ⟶ RJ's) (L : Rf ≅ RJs ⋙ Rfb) (L' : Rf' ≅ RJ's ⋙ Rfb')
    (bFb : Rfb ⋙ GY ⟶ GXb ⋙ Rfb') (bJ : RJs ⋙ GXb ⟶ GX ⋙ RJ's) (bf : Rf ⋙ GY ⟶ GX ⋙ Rf')
    (iso : GX ⋙ RJ' ≅ RJ ⋙ GXb)
    (bc : (RJ ⋙ Rfb) ⋙ GY ⟶ GX ⋙ (RJ' ⋙ Rfb'))
    (hbc : bc = Functor.whiskerLeft RJ bFb ≫ Functor.whiskerRight iso.inv Rfb')
    (τ : RJ ⋙ Rfb ⟶ Rf) (hτ : τ = Functor.whiskerRight ε Rfb ≫ L.inv)
    (τ' : RJ' ⋙ Rfb' ⟶ Rf') (hτ' : τ' = Functor.whiskerRight ε' Rfb' ≫ L'.inv)
    (hA : bf ≫ Functor.whiskerLeft GX L'.hom =
      Functor.whiskerRight L.hom GY ≫ (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft RJs bFb ≫ (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight bJ Rfb' ≫ (Functor.associator _ _ _).hom)
    (hB : iso.inv ≫ Functor.whiskerLeft GX ε' = Functor.whiskerRight ε GXb ≫ bJ) :
    bc ≫ Functor.whiskerLeft GX τ' = Functor.whiskerRight τ GY ≫ bf := by
  subst hbc hτ hτ'
  ext K
  have hA' := NatTrans.congr_app hA K
  have hB' := NatTrans.congr_app hB K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Functor.comp_obj] at hA' hB'
  have hbf : bf.app K = GY.map (L.hom.app K) ≫ bFb.app (RJs.obj K) ≫ Rfb'.map (bJ.app K) ≫
      L'.inv.app (GX.obj K) := by
    rw [← reassoc_of% hA', Iso.hom_inv_id_app, Category.comp_id]
  have hB'' : Rfb'.map (iso.inv.app K) ≫ Rfb'.map (ε'.app (GX.obj K)) =
      Rfb'.map (GXb.map (ε.app K)) ≫ Rfb'.map (bJ.app K) := by
    rw [← Rfb'.map_comp, hB', Rfb'.map_comp]
  have nb := bFb.naturality (ε.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at nb
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    CategoryTheory.Functor.map_comp, Category.assoc, hbf]
  rw [← GY.map_comp_assoc (L.inv.app K) (L.hom.app K), Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% nb, reassoc_of% hB'']

end LowerShriek

end DerivedComparisonPaste

/-! ### The base change maps compose along a composite of direct images -/

section Composition

variable {A B C A' B' C' : Scheme.{u}} (p : A ⟶ B) (q : B ⟶ C) (pq : A ⟶ C) (hpq : pq = p ≫ q)
  (p' : A' ⟶ B') (q' : B' ⟶ C') (pq' : A' ⟶ C') (hpq' : pq' = p' ≫ q')
  (φA : A' ⟶ A) (φB : B' ⟶ B) (φC : C' ⟶ C) (wp : φA ≫ p = p' ≫ φB) (wq : φB ≫ q = q' ≫ φC)
  (wpq : φA ≫ pq = pq' ≫ φC)

/-- **Degreewise comparisons paste**, for abstract categories: if comparisons
`αP : P ⋙ GB ⟶ GA ⋙ P'`, `αQ : Q ⋙ GC ⟶ GB ⋙ Q'` and `αPQ : PQ ⋙ GC ⟶ GA ⋙ PQ'` paste along
isomorphisms `P ⋙ Q ≅ PQ` and `P' ⋙ Q' ≅ PQ'`, so do the comparisons they induce degreewise on
complexes. Stated for abstract categories, so that the kernel never reduces the functors. -/
theorem mapHomologicalComplex_comparison_paste {ι : Type*} {c : ComplexShape ι}
    {VA VB VC VA' VB' VC' : Type*} [Category* VA] [Category* VB] [Category* VC] [Category* VA']
    [Category* VB'] [Category* VC'] [Preadditive VA] [Preadditive VB] [Preadditive VC]
    [Preadditive VA'] [Preadditive VB'] [Preadditive VC']
    {P : VA ⥤ VB} {Q : VB ⥤ VC} {PQ : VA ⥤ VC} {P' : VA' ⥤ VB'} {Q' : VB' ⥤ VC'}
    {PQ' : VA' ⥤ VC'} {GA : VA ⥤ VA'} {GB : VB ⥤ VB'} {GC : VC ⥤ VC'}
    [P.Additive] [Q.Additive] [PQ.Additive] [P'.Additive] [Q'.Additive] [PQ'.Additive]
    [GA.Additive] [GB.Additive] [GC.Additive]
    (αP : P ⋙ GB ⟶ GA ⋙ P') (αQ : Q ⋙ GC ⟶ GB ⋙ Q') (αPQ : PQ ⋙ GC ⟶ GA ⋙ PQ')
    (γP : P.mapHomologicalComplex c ⋙ GB.mapHomologicalComplex c ⟶
      GA.mapHomologicalComplex c ⋙ P'.mapHomologicalComplex c)
    (hγP : γP = (Functor.mapHomologicalComplexCompIso (Iso.refl (P ⋙ GB)) c).hom ≫
      NatTrans.mapHomologicalComplex αP c ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (GA ⋙ P')) c).inv)
    (γQ : Q.mapHomologicalComplex c ⋙ GC.mapHomologicalComplex c ⟶
      GB.mapHomologicalComplex c ⋙ Q'.mapHomologicalComplex c)
    (hγQ : γQ = (Functor.mapHomologicalComplexCompIso (Iso.refl (Q ⋙ GC)) c).hom ≫
      NatTrans.mapHomologicalComplex αQ c ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (GB ⋙ Q')) c).inv)
    (γPQ : PQ.mapHomologicalComplex c ⋙ GC.mapHomologicalComplex c ⟶
      GA.mapHomologicalComplex c ⋙ PQ'.mapHomologicalComplex c)
    (hγPQ : γPQ = (Functor.mapHomologicalComplexCompIso (Iso.refl (PQ ⋙ GC)) c).hom ≫
      NatTrans.mapHomologicalComplex αPQ c ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (GA ⋙ PQ')) c).inv)
    (e : P ⋙ Q ≅ PQ) (e' : P' ⋙ Q' ≅ PQ')
    (h : ∀ F, GC.map (e.hom.app F) ≫ αPQ.app F =
      αQ.app (P.obj F) ≫ Q'.map (αP.app F) ≫ e'.hom.app (GA.obj F))
    (K : HomologicalComplex VA c) :
    γPQ.app K ≫
        (Functor.mapHomologicalComplexCompIso e' c).inv.app ((GA.mapHomologicalComplex c).obj K) =
      (GC.mapHomologicalComplex c).map ((Functor.mapHomologicalComplexCompIso e c).inv.app K) ≫
        γQ.app ((P.mapHomologicalComplex c).obj K) ≫
        (Q'.mapHomologicalComplex c).map (γP.app K) := by
  subst hγP hγQ hγPQ
  ext n
  have hn := h (K.X n)
  simp only [NatTrans.comp_app, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
    Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex_app_f, Iso.refl_hom,
    Iso.refl_inv, NatTrans.id_app]
  dsimp only [Functor.comp_obj, Functor.mapHomologicalComplex_obj_X]
  simp only [Category.id_comp, Category.comp_id]
  rw [← cancel_epi (GC.map (e.hom.app (K.X n))), reassoc_of% hn, ← Functor.map_comp_assoc,
    e.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  exact (whisker_eq _ (whisker_eq _ (e'.hom_inv_id_app _))).trans
    (whisker_eq _ (Category.comp_id _))

/-- `Stacks.EtaleCohomology.etaleModuleBaseChange_pasteV` read at a sheaf. -/
theorem etaleModuleBaseChange_pasteV_app (F : EtaleModules.{u, r} Λ A) :
    (etaleModuleInverseImage.{u, r} Λ φC).map
        ((etaleModuleDirectImageComp.{u, r} Λ p q pq hpq).hom.app F) ≫
      (etaleModuleBaseChange.{u, r} Λ pq pq' φC φA wpq.symm).app F =
    (etaleModuleBaseChange.{u, r} Λ q q' φC φB wq.symm).app
        ((etaleModuleDirectImage.{u, r} Λ p).obj F) ≫
      (etaleModuleDirectImage.{u, r} Λ q').map
        ((etaleModuleBaseChange.{u, r} Λ p p' φB φA wp.symm).app F) ≫
      (etaleModuleDirectImageComp.{u, r} Λ p' q' pq' hpq').hom.app
        ((etaleModuleInverseImage.{u, r} Λ φA).obj F) := by
  simpa [Stacks.Cohomology.DerivedBaseChangePlus.pasteV] using NatTrans.congr_app
    (etaleModuleBaseChange_pasteV Λ p q pq hpq p' q' pq' hpq' φA φB φC wp.symm wq.symm wpq.symm) F

/-- The degreewise base change comparisons compose along a composite of direct images, read
through the composition isomorphisms of direct images, for underived comparisons `βP`, `βQ`,
`βPQ` which paste (`h`). The comparisons enter as variables, so that the kernel never unfolds
them. -/
theorem etaleModuleComplexBaseChangeUnboundedOf_comp
    (βP : etaleModuleDirectImage.{u, r} Λ p ⋙ etaleModuleInverseImage.{u, r} Λ φB ⟶
      etaleModuleInverseImage.{u, r} Λ φA ⋙ etaleModuleDirectImage.{u, r} Λ p')
    (βQ : etaleModuleDirectImage.{u, r} Λ q ⋙ etaleModuleInverseImage.{u, r} Λ φC ⟶
      etaleModuleInverseImage.{u, r} Λ φB ⋙ etaleModuleDirectImage.{u, r} Λ q')
    (βPQ : etaleModuleDirectImage.{u, r} Λ pq ⋙ etaleModuleInverseImage.{u, r} Λ φC ⟶
      etaleModuleInverseImage.{u, r} Λ φA ⋙ etaleModuleDirectImage.{u, r} Λ pq')
    (h : ∀ F, (etaleModuleInverseImage.{u, r} Λ φC).map
        ((etaleModuleDirectImageComp.{u, r} Λ p q pq hpq).hom.app F) ≫ βPQ.app F =
      βQ.app ((etaleModuleDirectImage.{u, r} Λ p).obj F) ≫
        (etaleModuleDirectImage.{u, r} Λ q').map (βP.app F) ≫
        (etaleModuleDirectImageComp.{u, r} Λ p' q' pq' hpq').hom.app
          ((etaleModuleInverseImage.{u, r} Λ φA).obj F))
    (K : CochainComplex (EtaleModules.{u, r} Λ A) ℤ) :
    (etaleModuleComplexBaseChangeUnboundedOf.{u, r} Λ pq φC φA pq' βPQ).app K ≫
        (Functor.mapHomologicalComplexCompIso (etaleModuleDirectImageComp.{u, r} Λ p' q' pq' hpq')
          (ComplexShape.up ℤ)).inv.app
            (((etaleModuleInverseImage.{u, r} Λ φA).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K) =
      ((etaleModuleInverseImage.{u, r} Λ φC).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((Functor.mapHomologicalComplexCompIso (etaleModuleDirectImageComp.{u, r} Λ p q pq hpq)
            (ComplexShape.up ℤ)).inv.app K) ≫
        (etaleModuleComplexBaseChangeUnboundedOf.{u, r} Λ q φC φB q' βQ).app
          (((etaleModuleDirectImage.{u, r} Λ p).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        ((etaleModuleDirectImage.{u, r} Λ q').mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((etaleModuleComplexBaseChangeUnboundedOf.{u, r} Λ p φB φA p' βP).app K) :=
  mapHomologicalComplex_comparison_paste βP βQ βPQ _ rfl _ rfl _ rfl _ _ h K

/-- `Stacks.EtaleCohomology.etaleModuleDerivedBaseChangeUnbounded_comp` with the underived base
change maps as variables `βP`, `βQ`, `βPQ`, so that the kernel never unfolds them. -/
theorem etaleModuleDerivedBaseChangeUnbounded_comp_of
    (βP : etaleModuleDirectImage.{u, r} Λ p ⋙ etaleModuleInverseImage.{u, r} Λ φB ⟶
      etaleModuleInverseImage.{u, r} Λ φA ⋙ etaleModuleDirectImage.{u, r} Λ p')
    (βQ : etaleModuleDirectImage.{u, r} Λ q ⋙ etaleModuleInverseImage.{u, r} Λ φC ⟶
      etaleModuleInverseImage.{u, r} Λ φB ⋙ etaleModuleDirectImage.{u, r} Λ q')
    (βPQ : etaleModuleDirectImage.{u, r} Λ pq ⋙ etaleModuleInverseImage.{u, r} Λ φC ⟶
      etaleModuleInverseImage.{u, r} Λ φA ⋙ etaleModuleDirectImage.{u, r} Λ pq')
    (hβP : βP = etaleModuleBaseChange.{u, r} Λ p p' φB φA wp.symm)
    (hβQ : βQ = etaleModuleBaseChange.{u, r} Λ q q' φC φB wq.symm)
    (hβPQ : βPQ = etaleModuleBaseChange.{u, r} Λ pq pq' φC φA wpq.symm) :
    etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ pq φC φA pq' wpq ≫
        Functor.whiskerLeft (etaleModuleDerivedInverseImage.{u, r} Λ φA)
          (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ p' q' pq' hpq').hom =
      Functor.whiskerRight (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ p q pq hpq).hom
          (etaleModuleDerivedInverseImage.{u, r} Λ φC) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ p)
          (etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ q φC φB q' wq) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ p φB φA p' wp)
          (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ q') ≫
        (Functor.associator _ _ _).hom := by
  have hbP := etaleModuleDerivedBaseChangeUnbounded_fac Λ p φB φA p' wp
  have hbQ := etaleModuleDerivedBaseChangeUnbounded_fac Λ q φC φB q' wq
  have hbPQ := etaleModuleDerivedBaseChangeUnbounded_fac Λ pq φC φA pq' wpq
  simp only [etaleModuleComplexBaseChangeUnbounded_eq, ← hβP, ← hβQ, ← hβPQ] at hbP hbQ hbPQ
  exact DerivedComparisonPaste.derivedComparison_vertical_paste
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ p)
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ q)
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ pq)
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ p')
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ q')
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ pq')
    (etaleModuleInverseImage.{u, r} Λ φA).mapDerivedCategoryFactors
    (etaleModuleInverseImage.{u, r} Λ φB).mapDerivedCategoryFactors
    (etaleModuleInverseImage.{u, r} Λ φC).mapDerivedCategoryFactors
    (etaleModuleComplexBaseChangeUnboundedOf.{u, r} Λ p φB φA p' βP)
    (etaleModuleComplexBaseChangeUnboundedOf.{u, r} Λ q φC φB q' βQ)
    (etaleModuleComplexBaseChangeUnboundedOf.{u, r} Λ pq φC φA pq' βPQ)
    (etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ p φB φA p' wp)
    (etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ q φC φB q' wq)
    (etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ pq φC φA pq' wpq)
    (Functor.mapHomologicalComplexCompIso (etaleModuleDirectImageComp.{u, r} Λ p q pq hpq)
      (ComplexShape.up ℤ))
    (Functor.mapHomologicalComplexCompIso (etaleModuleDirectImageComp.{u, r} Λ p' q' pq' hpq')
      (ComplexShape.up ℤ))
    (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ p q pq hpq)
    (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ p' q' pq' hpq')
    hbP hbQ hbPQ
    (etaleModuleDerivedDirectImageUnboundedLerayIso_hom_fac Λ p q pq hpq)
    (etaleModuleDerivedDirectImageUnboundedLerayIso_hom_fac Λ p' q' pq' hpq')
    (etaleModuleComplexBaseChangeUnboundedOf_comp Λ p q pq hpq p' q' pq' hpq' φA φB φC βP βQ βPQ
      (by
        rw [hβP, hβQ, hβPQ]
        exact etaleModuleBaseChange_pasteV_app Λ p q pq hpq p' q' pq' hpq' φA φB φC wp wq wpq))

/-- **The unbounded base change maps compose along a composite of direct images**, read through
the Leray isomorphisms `R(p ≫ q)_* ≅ Rp_* ∘ Rq_*`: the unbounded form of
`Stacks.EtaleCohomology.etaleModuleDerivedBaseChange_comp`. -/
theorem etaleModuleDerivedBaseChangeUnbounded_comp :
    etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ pq φC φA pq' wpq ≫
        Functor.whiskerLeft (etaleModuleDerivedInverseImage.{u, r} Λ φA)
          (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ p' q' pq' hpq').hom =
      Functor.whiskerRight (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ p q pq hpq).hom
          (etaleModuleDerivedInverseImage.{u, r} Λ φC) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ p)
          (etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ q φC φB q' wq) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ p φB φA p' wp)
          (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ q') ≫
        (Functor.associator _ _ _).hom :=
  etaleModuleDerivedBaseChangeUnbounded_comp_of Λ p q pq hpq p' q' pq' hpq' φA φB φC wp wq wpq _ _ _
    rfl rfl rfl

end Composition

/-! ### `Rj_! ⟶ Rj_*` and base change -/

section ExtensionByZero

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  (sq : IsPullback g' f' f g) (j : CompactificationOf (Over.mk f))

/-- **The map `Rj_! ⟶ Rj_*` commutes with base change along a cartesian square of open
immersions**, with the underived base change map as a variable `β` and the isomorphism
`(g')⁻¹ ∘ Rj'_! ≅ φ⁻¹ ∘ Rj_!` of [Stacks, Tag 03S6] as a variable `iso`, so that the kernel never
unfolds them. Stated for an arbitrary cartesian square, so that the kernel never reduces the
schemes. -/
theorem etaleModuleDerivedExtensionByZeroToDirectImageUnbounded_baseChange_of_isPullback
    {X X' Xb Xb' : Scheme.{u}} {g' : X' ⟶ X} {j : X ⟶ Xb} {j' : X' ⟶ Xb'} {φ : Xb' ⟶ Xb}
    [IsOpenImmersion j] [IsOpenImmersion j'] (hc : IsPullback g' j' j φ)
    (β : etaleModuleDirectImage.{u, r} Λ j ⋙ etaleModuleInverseImage.{u, r} Λ φ ⟶
      etaleModuleInverseImage.{u, r} Λ g' ⋙ etaleModuleDirectImage.{u, r} Λ j')
    (hβ : β = etaleModuleBaseChange.{u, r} Λ j j' φ g' hc.w.symm)
    (iso : (etaleModuleInverseImage.{u, r} Λ g').mapDerivedCategory ⋙
        etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j' ≅
      etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j ⋙
        (etaleModuleInverseImage.{u, r} Λ φ).mapDerivedCategory)
    (hiso : iso =
      Functor.isoWhiskerLeft _ (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ j') ≪≫
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _).symm ≪≫
      Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
        (etaleModuleInverseImageExtensionByZeroIso.{u, r} Λ hc) ≪≫
      Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.isoWhiskerRight (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ j).symm _) :
    iso.inv ≫ Functor.whiskerLeft (etaleModuleInverseImage.{u, r} Λ g').mapDerivedCategory
        (etaleModuleDerivedExtensionByZeroToDirectImageUnbounded.{u, r} Λ j') =
      Functor.whiskerRight (etaleModuleDerivedExtensionByZeroToDirectImageUnbounded.{u, r} Λ j)
          (etaleModuleDerivedInverseImage.{u, r} Λ φ) ≫
        etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ j φ g' j' hc.w := by
  have hb := etaleModuleDerivedBaseChangeUnbounded_fac Λ j φ g' j' hc.w
  simp only [etaleModuleComplexBaseChangeUnbounded_eq, ← hβ] at hb
  exact DerivedComparisonPaste.derivedExtensionByZero_comparison_baseChange
    (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ j)
    (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ j')
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ j)
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ j')
    (etaleModuleExtensionByZeroToDirectImage.{u, r} Λ j)
    (etaleModuleExtensionByZeroToDirectImage.{u, r} Λ j') β
    (etaleModuleInverseImageExtensionByZeroIso.{u, r} Λ hc)
    (etaleModuleDerivedExtensionByZeroToDirectImageUnbounded.{u, r} Λ j)
    (etaleModuleDerivedExtensionByZeroToDirectImageUnbounded.{u, r} Λ j')
    (etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ j φ g' j' hc.w)
    (etaleModuleComplexBaseChangeUnboundedOf.{u, r} Λ j φ g' j' β) rfl iso hiso
    (etaleModuleDerivedExtensionByZeroToDirectImageUnbounded_app_factors Λ j)
    (etaleModuleDerivedExtensionByZeroToDirectImageUnbounded_app_factors Λ j')
    hb (fun F => by
      rw [hβ]
      exact ExtensionByZeroPasting.map_extensionByZeroToDirectImage_comp_baseChange Λ hc F)

/-- **The map `Rj_! ⟶ Rj_*` commutes with base change**, on unbounded derived categories: for a
compactification `j` of `X` over `Y` and its base change along `g : Y' ⟶ Y`, the inverse of the
isomorphism `(g')⁻¹ ∘ Rj'_! ≅ ḡ'⁻¹ ∘ Rj_!` of [Stacks, Tag 03S6] followed by `Rj'_! ⟶ Rj'_*` is
`ḡ'⁻¹` of `Rj_! ⟶ Rj_*` followed by the base change map `ḡ'⁻¹ ∘ Rj_* ⟶ Rj'_* ∘ (g')⁻¹`. -/
theorem etaleModuleDerivedExtensionByZeroToDirectImageUnbounded_baseChange :
    (etaleModuleDerivedExtensionByZeroUnboundedBaseChangeIso.{u, r} Λ sq j).inv ≫
        Functor.whiskerLeft (etaleModuleInverseImage.{u, r} Λ g').mapDerivedCategory
          (etaleModuleDerivedExtensionByZeroToDirectImageUnbounded.{u, r} Λ
            (CompactificationOf.baseChangeImmersion sq j)) =
      Functor.whiskerRight
          (etaleModuleDerivedExtensionByZeroToDirectImageUnbounded.{u, r} Λ j.immersion)
          (etaleModuleDerivedInverseImage.{u, r} Λ (pullback.fst j.toBase g)) ≫
        etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ j.immersion (pullback.fst j.toBase g) g'
          (CompactificationOf.baseChangeImmersion sq j)
          (CompactificationOf.baseChangeImmersion_fst sq j).symm :=
  etaleModuleDerivedExtensionByZeroToDirectImageUnbounded_baseChange_of_isPullback Λ
    (CompactificationOf.isPullback_baseChangeImmersion sq j) _ rfl _ rfl

end ExtensionByZero

/-! ### [Stacks, Tag 0H6X], compatibility (2), on `D(X_étale, Λ)` -/

section CompatibilityTwo

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}

/-- **[Stacks, Tag 0H6X], compatibility (2), on `D(X_étale, Λ)`**: the map `Rf_! ⟶ Rf_*` is
compatible with the base change map `g⁻¹ ∘ Rf_! ⟶ Rf'_! ∘ (g')⁻¹` of [Stacks, Tag 0F7L]
(`Stacks.EtaleCohomology.derivedLowerShriekUnboundedBaseChange`, whose components are those of the
isomorphism `Stacks.EtaleCohomology.derivedLowerShriekUnboundedBaseChangeIso` when `Λ` is torsion)
and the base change map `g⁻¹ ∘ Rf_* ⟶ Rf'_* ∘ (g')⁻¹` of Cohomology on Sites, Remark 07A7
(`Stacks.EtaleCohomology.etaleModuleDerivedBaseChangeUnbounded`): for a cartesian square
`g' ≫ f = f' ≫ g` and a compactification `j` of `f`, the composite
`g⁻¹ ∘ Rf_! ⟶ Rf'_! ∘ (g')⁻¹ ⟶ Rf'_* ∘ (g')⁻¹` is `g⁻¹ ∘ Rf_! ⟶ g⁻¹ ∘ Rf_* ⟶ Rf'_* ∘ (g')⁻¹`,
as transformations of functors on `D(X_étale, Λ)`, `Rf'_!` being computed with the base change of
`j`. -/
@[stacks 0H6X "(2), on D(X_étale, Λ), Λ torsion"]
theorem derivedLowerShriekUnboundedBaseChange_comp_toDirectImage (sq : IsPullback g' f' f g)
    (j : CompactificationOf (Over.mk f)) :
    derivedLowerShriekUnboundedBaseChange.{u, r} Λ sq j ≫
        Functor.whiskerLeft (etaleModuleDerivedInverseImage.{u, r} Λ g')
          (derivedLowerShriekUnboundedToDirectImage.{u, r} Λ f' (j.baseChange sq)) =
      Functor.whiskerRight (derivedLowerShriekUnboundedToDirectImage.{u, r} Λ f j)
          (etaleModuleDerivedInverseImage.{u, r} Λ g) ≫
        etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ f g g' f' sq.w :=
  DerivedComparisonPaste.lowerShriekBaseChange_comp_toDirectImage_paste
    (etaleModuleDerivedExtensionByZeroToDirectImageUnbounded.{u, r} Λ j.immersion)
    (etaleModuleDerivedExtensionByZeroToDirectImageUnbounded.{u, r} Λ
      (CompactificationOf.baseChangeImmersion sq j))
    (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ j.immersion j.toBase f
      (CompactificationOf.immersion_toBase j).symm)
    (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ
      (CompactificationOf.baseChangeImmersion sq j) (pullback.snd j.toBase g) f'
      (CompactificationOf.baseChangeImmersion_snd sq j).symm)
    (etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ j.toBase g (pullback.fst j.toBase g)
      (pullback.snd j.toBase g) pullback.condition)
    (etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ j.immersion (pullback.fst j.toBase g) g'
      (CompactificationOf.baseChangeImmersion sq j)
      (CompactificationOf.baseChangeImmersion_fst sq j).symm)
    (etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ f g g' f' sq.w)
    (etaleModuleDerivedExtensionByZeroUnboundedBaseChangeIso.{u, r} Λ sq j)
    (derivedLowerShriekUnboundedBaseChange.{u, r} Λ sq j) rfl
    (derivedLowerShriekUnboundedToDirectImage.{u, r} Λ f j) rfl
    (derivedLowerShriekUnboundedToDirectImage.{u, r} Λ f' (j.baseChange sq)) rfl
    (etaleModuleDerivedBaseChangeUnbounded_comp Λ j.immersion j.toBase f
      (CompactificationOf.immersion_toBase j).symm (CompactificationOf.baseChangeImmersion sq j)
      (pullback.snd j.toBase g) f' (CompactificationOf.baseChangeImmersion_snd sq j).symm g'
      (pullback.fst j.toBase g) g (CompactificationOf.baseChangeImmersion_fst sq j).symm
      pullback.condition sq.w)
    (etaleModuleDerivedExtensionByZeroToDirectImageUnbounded_baseChange Λ sq j)

end CompatibilityTwo

end Stacks.EtaleCohomology

end
