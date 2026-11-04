module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NewShriekAffineCharts
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NewShriekComparisonZeroth
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NewShriekComparisonRestrict
public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedOnOpensChart
public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedOnOpens
public import StacksFrontier.AlgebraicGeometry.Duality.GlueingDualizingComplexesStandardModel

/-!
# Charts of `H⁰(f_new^! 𝒪_Y)` through an identification of the normalized complexes

In Situation [Stacks, Tag 0AU4], for `f : X ⟶ Y` locally quasi-finite and affine opens
`V ⊆ f⁻¹U`, the identification `H⁰(f_new^! 𝒪_Y)|_V ≅ M|_V` of `NewShriekAffineCharts` is built
from any identification `ω_X^•|_V ≅ (V → Y)^! ω_Y^•`; at the chart normalization of
[Stacks, Tag 0AUB] it gives chart data independent of `U`. This file also records how
`H⁰(g_new^! 𝒪_Y) ≅ H⁰(g^! 𝒪_Y)` depends on the complex upstairs and on the compactification.

## Main definitions

* `Stacks.Duality.NormalizedOnOpens.affineIsoOfIso`: the identification of
  `H⁰(f_new^! 𝒪_Y)|_V` with `M|_V` attached to an identification `ω_X^•|_V ≅ (V → Y)^! ω_Y^•`.
* `Stacks.Duality.NormalizedOnOpens.affineChartData`: the chart data of `ω_{V/Y}` on
  `H⁰(f_new^! 𝒪_Y)|_V` for affine `V ⊆ f⁻¹U`.

## Main results

* `Stacks.Duality.NormalizedOnOpens.affineChartData_eq_of_le`: the chart data on `V` do not
  depend on the chart `U` of `Y`.

## References

* [Stacks Project, Tag 0BUL](https://stacks.math.columbia.edu/tag/0BUL)
* [Stacks Project, Tag 0AUB](https://stacks.math.columbia.edu/tag/0AUB)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Duality

open Stacks.Duality.TwistedInverseImageDuality (Std comparison plusCoh plusCoh_le_qcoh plusCoh_iff
  pull stdMonoidal stdSymmetric stdMonoidalClosed)

/-- `H⁰` at the standard model commutes with restriction along an open immersion. -/
def homologyPullIsoOfOpenImmersion {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (K : Std X) :
    (@DerivedCategory.homologyFunctor U.Modules _ _
      (PerfectApproximation.standardModel U) 0).obj ((pull j).obj K) ≅
      ((@DerivedCategory.homologyFunctor X.Modules _ _
        (PerfectApproximation.standardModel X) 0).obj K).restrict j :=
  letI := PerfectApproximation.standardModel X
  letI := PerfectApproximation.standardModel U
  (DerivedCategory.homologyFunctor U.Modules 0).mapIso
      ((Scheme.Modules.derivedRestrictIsoDerivedPullback j).app K).symm ≪≫
    ((Scheme.Modules.restrictFunctor j).mapDerivedCategoryHomologyIso 0).app K

/-- `homologyPullIso` is the case of an open subscheme. -/
theorem homologyPullIso_eq {X : Scheme.{u}} (V : X.Opens) (K : Std X) :
    homologyPullIso V K = homologyPullIsoOfOpenImmersion V.ι K := rfl

section RestrictGeneric

variable {S₀ : Scheme.{u}} [IsNoetherian S₀] {A' A B : FTS S₀} (h : A' ⟶ A) [IsOpenImmersion h.left]
  {g : A ⟶ B}

/-- A factorization `g = π ∘ i` restricted along an open immersion `h`:
`g' = h ≫ g = π ∘ (i ∘ h)`. -/
def _root_.Stacks.Duality.OpenFiniteFactorization.precompOpen (F : OpenFiniteFactorization g)
    {g' : A' ⟶ B} (w : h ≫ g = g') : OpenFiniteFactorization g' where
  space := F.space
  immersion := h.left ≫ F.immersion
  toBase := F.toBase
  fac := by rw [Category.assoc, F.fac, ← w]; rfl

namespace NormalizedOnOpens

open UpperShriekDuality TwistedInverseImageDuality
open CategoryTheory.MonoidalClosed (dualInto)

attribute [local instance] stdMonoidal stdSymmetric stdMonoidalClosed

/-- The chase behind `upperShriekStdIsoFNewShriekOfIso_trans_hom_app`. -/
theorem ofIso_trans_chase {𝒞 : Type*} [Category 𝒞] {a b c d d' d'' e₁ e₂ : 𝒞} (u : a ⟶ b)
    (x : b ⟶ c) (y : c ⟶ d) (r₂ : d ⟶ e₁) (r₁ : c ⟶ d') (t : d' ⟶ e₁) (m₂ : e₁ ⟶ e₂)
    (m₁ : d' ⟶ d'') (t' : d'' ⟶ e₂) (N1 : y ≫ r₂ = r₁ ≫ t) (N2 : m₁ ≫ t' = t ≫ m₂) :
    u ≫ (x ≫ y) ≫ r₂ ≫ m₂ = (u ≫ x ≫ r₁ ≫ m₁) ≫ t' := by
  simp only [Category.assoc]
  rw [reassoc_of% N1, N2]

/-- `g^! ≅ g_new^!` along an isomorphism of the complexes upstairs. -/
theorem upperShriekStdIsoFNewShriekOfIso_trans_hom_app (g₀ : A' ⟶ B)
    (j : CompactificationOf (Over.mk g₀.left)) {K : Std B.left} (hK : IsDualizing K)
    {ω₁ ω₂ : Std A'.left} (e : upperShriekDualizing g₀ j hK ≅ ω₁) (τ : ω₁ ≅ ω₂)
    (M : (plusCoh B.left).FullSubcategory) :
    (upperShriekStdIsoFNewShriekOfIso g₀ j hK (e ≪≫ τ)).hom.app M =
      (upperShriekStdIsoFNewShriekOfIso g₀ j hK e).hom.app M ≫
        (Functor.isoWhiskerLeft (dualInto K).rightOp (Functor.isoWhiskerLeft (pull g₀.left).op
          (dualIntoMapIso τ))).hom.app M.obj := by
  rw [upperShriekStdIsoFNewShriekOfIso_hom_app, upperShriekStdIsoFNewShriekOfIso_hom_app,
    Iso.trans_hom, Functor.map_comp]
  have N1 : ((TwistedInverseImageDuality.sheafHom A'.left).obj ((pull g₀.left).op.obj
        (((TwistedInverseImageDuality.sheafHom B.left).flip.obj K).rightOp.obj
          ((plusCoh B.left).ι.obj M)))).map τ.hom ≫
      (relativeDualIsoSheafHom ω₂).inv.app ((pull g₀.left).op.obj
        (((TwistedInverseImageDuality.sheafHom B.left).flip.obj K).rightOp.obj
          ((plusCoh B.left).ι.obj M))) =
      (relativeDualIsoSheafHom ω₁).inv.app ((pull g₀.left).op.obj
        (((TwistedInverseImageDuality.sheafHom B.left).flip.obj K).rightOp.obj
          ((plusCoh B.left).ι.obj M))) ≫
      (dualIntoMapIso τ).hom.app ((pull g₀.left).op.obj
        (((TwistedInverseImageDuality.sheafHom B.left).flip.obj K).rightOp.obj
          ((plusCoh B.left).ι.obj M))) :=
    (Category.comp_id _).trans (Category.id_comp _).symm
  exact ofIso_trans_chase _ _ _ _ _ _ _ _ _ N1
    ((dualIntoMapIso τ).hom.naturality ((pull g₀.left).op.map
      ((natIsoRightOp (relativeDualIsoSheafHom K).symm).hom.app ((plusCoh B.left).ι.obj M))))

/-- An isomorphism `α = β ≫ γ`, read on inverses through a functor. -/
theorem mapIso_symm_trans_of_hom_eq {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (G : 𝒞 ⥤ 𝒟)
    {x y z : 𝒞} {t : 𝒟} (α : x ≅ z) (β : x ≅ y) (γ : y ≅ z) (s : G.obj x ≅ t)
    (h : α.hom = β.hom ≫ γ.hom) :
    G.mapIso α.symm ≪≫ s = G.mapIso γ.symm ≪≫ G.mapIso β.symm ≪≫ s := by
  have hi : α.inv = γ.inv ≫ β.inv := by
    rw [← cancel_epi α.hom, Iso.hom_inv_id, h, Category.assoc, γ.hom_inv_id_assoc, β.hom_inv_id]
  ext1
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, hi, Functor.map_comp, Category.assoc]

/-- **Changing the complex upstairs** in `H⁰(g_new^! 𝒪_Y) ≅ H⁰(g^! 𝒪_Y)`. -/
theorem upperShriekStructureSheafZerothIsoOfIso_trans_dualizing (g₀ : A' ⟶ B)
    (j : CompactificationOf (Over.mk g₀.left)) {K : Std B.left} (hK : IsDualizing K)
    {ω₁ ω₂ : Std A'.left} (e : upperShriekDualizing g₀ j hK ≅ ω₁) (τ : ω₁ ≅ ω₂) :
    upperShriekStructureSheafZerothIsoOfIso g₀ j hK (e ≪≫ τ) =
      (@DerivedCategory.homologyFunctor A'.left.Modules _ _
        (PerfectApproximation.standardModel A'.left) 0).mapIso
        ((Functor.isoWhiskerLeft (dualInto K).rightOp (Functor.isoWhiskerLeft (pull g₀.left).op
          (dualIntoMapIso τ))).app (structureStd B.left)).symm ≪≫
      upperShriekStructureSheafZerothIsoOfIso g₀ j hK e := by
  unfold upperShriekStructureSheafZerothIsoOfIso
  exact mapIso_symm_trans_of_hom_eq (@DerivedCategory.homologyFunctor A'.left.Modules _ _
      (PerfectApproximation.standardModel A'.left) 0)
    ((upperShriekStdIsoFNewShriekOfIso g₀ j hK (e ≪≫ τ)).app
      ⟨structureStd B.left, plusCoh_structureStd B.left⟩)
    ((upperShriekStdIsoFNewShriekOfIso g₀ j hK e).app
      ⟨structureStd B.left, plusCoh_structureStd B.left⟩)
    ((Functor.isoWhiskerLeft (dualInto K).rightOp (Functor.isoWhiskerLeft (pull g₀.left).op
          (dualIntoMapIso τ))).app (structureStd B.left))
    (PerfectApproximation.homologyStandardIso _ 0).symm
    (upperShriekStdIsoFNewShriekOfIso_trans_hom_app g₀ j hK e τ
      ⟨structureStd B.left, plusCoh_structureStd B.left⟩)

end NormalizedOnOpens

end RestrictGeneric

namespace NormalizedOnOpens

section Generic

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))
  {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S}
  {hp : IsFiniteTypeOverNoetherian p} {hq : IsFiniteTypeOverNoetherian q}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel S}
  (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) (hf : IsShriekable f)
  (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
  (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS)

/-- An identification `ω_X^• ≅ f^! ω_Y^•`, read as `f^!K ≅ ω_X^•` at the standard model. -/
def normalizationStdIso (e : 𝒦X.complex ≅ (UpperShriek.shriekOf c f hf).obj 𝒦Y.complex) :
    haveI := hq.source_noetherian
    UpperShriekDuality.upperShriekDualizing (ftsHomSelf hf) (c f hf)
        (isDualizing_stdComplex c (Category.id_comp q) hωS 𝒦Y) ≅ stdComplex c 𝒦X :=
  haveI := hq.source_noetherian
  (comparison X).inverse.mapIso
    ((ObjectProperty.ι _).mapIso ((upperShriek (ftsHomSelf hf) (c f hf)).mapIso
        (dualizingQCohIso c 𝒦Y (isDualizing_stdComplex c (Category.id_comp q) hωS 𝒦Y))) ≪≫
      (ObjectProperty.ι _).mapIso ((ObjectProperty.ι _).mapIso e.symm))

end Generic

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))
  {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S}
  {hp : IsFiniteTypeOverNoetherian p} {hq : IsFiniteTypeOverNoetherian q}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel S}
  (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
  (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS)
  (hpe : f ≫ q = p) (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)
  [LocallyQuasiFinite f]

/-- The identification of `H⁰(f_new^! 𝒪_Y)|_V` with `M|_V` attached to a normalization
`ω_X^•|_V ≅ (V → Y)^! ω_Y^•`. -/
def affineIsoOfIso (V : X.affineOpens)
    (e : (𝒦X.restrict V.1).complex ≅ (UpperShriek.shriekOf c (V.1.ι ≫ f)
      (hp.isShriekable_ι_comp_of_isAffineOpen hq hpe V.2)).obj 𝒦Y.complex) :
    haveI := hq.source_noetherian
    ∀ F : OpenFiniteFactorization (ftsHomSelf (hp.isShriekable_ι_comp_of_isAffineOpen hq hpe V.2)),
    (newShriekStructureSheafZeroth c f 𝒦X 𝒦Y).restrict V.1.ι ≅
      @Scheme.Modules.restrict _ _ (finiteZeroTwisted F) F.immersion
        F.isOpenImmersion_immersion :=
  haveI := hq.source_noetherian
  fun F => (newShriekStructureSheafZerothRestrictIso c f 𝒦X 𝒦Y V.1 ≪≫
    upperShriekStructureSheafZerothIsoOfIso
      (ftsHomSelf (hp.isShriekable_ι_comp_of_isAffineOpen hq hpe V.2))
      (c _ (hp.isShriekable_ι_comp_of_isAffineOpen hq hpe V.2))
      (isDualizing_stdComplex c (Category.id_comp q) hωS 𝒦Y)
      (normalizationStdIso c hωS (hp.isShriekable_ι_comp_of_isAffineOpen hq hpe V.2)
        (𝒦X.restrict V.1) 𝒦Y e)) ≪≫
    upperShriekStructureSheafZerothIso F (c _ (hp.isShriekable_ι_comp_of_isAffineOpen hq hpe V.2))

omit [LocallyQuasiFinite f] in
/-- The identification through `ω_X^•|_V ≅ f^! ω_Y^•` of [Stacks, Tag 0AUD]. -/
theorem affineIso_eq_affineIsoOfIso (V : X.affineOpens) :
    haveI := hq.source_noetherian
    ∀ F : OpenFiniteFactorization (ftsHomSelf (hp.isShriekable_ι_comp_of_isAffineOpen hq hpe V.2)),
    affineIso c 𝒦X 𝒦Y hpe hωS V F = affineIsoOfIso c 𝒦X 𝒦Y hpe hωS V
      (upperShriekObjIso c (comp_structure_ι hpe V.1) hωS
        (hp.isShriekable_ι_comp_of_isAffineOpen hq hpe V.2) (𝒦X.restrict V.1) 𝒦Y) F := fun _ => rfl

/-- The chart normalization `ω_X^•|_V ≅ (V → Y)^! ω_Y^•` for affine `V ⊆ f⁻¹U`. -/
abbrev affineChartNormalization (U : Y.affineOpens) (V : X.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    (𝒦X.restrict V.1).complex ≅ (UpperShriek.shriekOf c (V.1.ι ≫ f)
      (hp.isShriekable_ι_comp_of_isAffineOpen hq hpe V.2)).obj 𝒦Y.complex :=
  chartIso hpe 𝒦X 𝒦Y (hp.isShriekable_of_isAffineOpen V.2) (hq.isShriekable_of_isAffineOpen U.2) hVU

/-- The chart data of `ω_{V/Y}` on `H⁰(f_new^! 𝒪_Y)|_V` for affine `V ⊆ f⁻¹U`. -/
def affineChartData (U : Y.affineOpens) (V : X.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    haveI := hp.source_noetherian
    haveI := hq.source_noetherian
    Stacks.Discriminant.RelativeDualizingModuleData (V.1.ι ≫ f) :=
  haveI := hp.source_noetherian
  haveI := hq.source_noetherian
  haveI : LocallyQuasiFinite
      (ftsHomSelf (hp.isShriekable_ι_comp_of_isAffineOpen hq hpe V.2)).left :=
    inferInstanceAs (LocallyQuasiFinite (V.1.ι ≫ f))
  Stacks.Discriminant.RelativeDualizingModuleData.ofFiniteTrace
    (affineFactorization (hp := hp) (hq := hq) hpe V).fac
    (finiteZeroTwisted (affineFactorization (hp := hp) (hq := hq) hpe V))
    (finiteTrace (affineFactorization (hp := hp) (hq := hq) hpe V))
    (bijective_traceDual_finiteTrace (affineFactorization (hp := hp) (hq := hq) hpe V))
    (affineIsoOfIso c 𝒦X 𝒦Y hpe hωS V (affineChartNormalization c 𝒦X 𝒦Y hpe U V hVU)
      (affineFactorization (hp := hp) (hq := hq) hpe V))

/-- The chart data on `V` do not depend on the chart `U ⊇ f(V)` of `Y`. -/
theorem affineChartData_eq_of_le {U' U : Y.affineOpens} (h : U'.1 ≤ U.1) (V : X.affineOpens)
    (hVU' : V.1 ≤ f ⁻¹ᵁ U'.1) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    affineChartData c 𝒦X 𝒦Y hpe hωS U' V hVU' = affineChartData c 𝒦X 𝒦Y hpe hωS U V hVU := by
  rw [affineChartData, affineChartData, affineChartNormalization, affineChartNormalization,
    chartIso_eq_of_le hpe 𝒦X 𝒦Y _ h]


/-- `V → Y` as a morphism of `FTS_Y`, for an affine open `V ⊆ X`. -/
abbrev affineHom (V : X.affineOpens) :=
  ftsHomSelf (hp.isShriekable_ι_comp_of_isAffineOpen hq hpe V.2)

/-- The inclusion `W ⊆ V` of affine opens as a morphism of `FTS_Y`. -/
abbrev affineRestrictHom {V W : X.affineOpens} (hWV : W.1 ≤ V.1) :=
  ftsHomOf (X.homOfLE hWV) (hp.isShriekable_ι_comp_of_isAffineOpen hq hpe W.2).separatedFiniteType
    (hp.isShriekable_ι_comp_of_isAffineOpen hq hpe V.2).separatedFiniteType
    (by rw [← Category.assoc, Scheme.homOfLE_ι])

/-- The inclusion `W ⊆ V` of affine opens is an open immersion. -/
instance {V W : X.affineOpens} (hWV : W.1 ≤ V.1) :
    IsOpenImmersion (affineRestrictHom (hp := hp) (hq := hq) hpe hWV).left :=
  inferInstanceAs (IsOpenImmersion (X.homOfLE hWV))

omit [LocallyQuasiFinite f] in
/-- `W → V → Y` is `W → Y`. -/
theorem affineRestrictHom_comp {V W : X.affineOpens} (hWV : W.1 ≤ V.1) :
    affineRestrictHom (hp := hp) (hq := hq) hpe hWV ≫ affineHom (hp := hp) (hq := hq) hpe V =
      affineHom (hp := hp) (hq := hq) hpe W := by
  ext
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ f) (Scheme.homOfLE_ι X hWV))

omit [LocallyQuasiFinite f] in
/-- The restricted factorization is the factorization restricted along `W ⊆ V`. -/
theorem restrictFactorization_eq {V W : X.affineOpens} (hWV : W.1 ≤ V.1) :
    haveI := hq.source_noetherian
    ∀ F : OpenFiniteFactorization (affineHom (hp := hp) (hq := hq) hpe V),
    restrictFactorization (hp := hp) (hq := hq) hpe hWV F =
      F.precompOpen (affineRestrictHom (hp := hp) (hq := hq) hpe hWV)
        (affineRestrictHom_comp hpe hWV) :=
  fun _ => rfl

/-- `ω_Y^•`, read back from the standard model, is bounded below. -/
theorem isBoundedBelow_dualizingQCoh :
    haveI := hq.source_noetherian
    DerivedCategoryB.IsBoundedBelow (UpperShriekDuality.dualizingQCoh (S := Y)
      (Y := ftsOf (𝟙 Y) (isSeparatedFiniteType_id Y))
      (isDualizing_stdComplex c (Category.id_comp q) hωS 𝒦Y)).obj :=
  have := hq.source_noetherian
  DerivedCategoryB.isBoundedBelow_of_iso (X := 𝒦Y.complex.obj.obj)
    (Y := (comparison Y).functor.obj ((comparison Y).inverse.obj 𝒦Y.complex.obj.obj))
    ((comparison Y).counitIso.app 𝒦Y.complex.obj.obj).symm 𝒦Y.complex.property

/-- The normalization on `V` moved to the compactification of a factorization. -/
abbrev affineNormalizationAt (V : X.affineOpens)
    (e : (𝒦X.restrict V.1).complex ≅ (UpperShriek.shriekOf c (V.1.ι ≫ f)
      (hp.isShriekable_ι_comp_of_isAffineOpen hq hpe V.2)).obj 𝒦Y.complex) :
    haveI := hq.source_noetherian
    ∀ F : OpenFiniteFactorization (affineHom (hp := hp) (hq := hq) hpe V),
    UpperShriekDuality.upperShriekDualizing (affineHom (hp := hp) (hq := hq) hpe V)
        F.compactification (isDualizing_stdComplex c (Category.id_comp q) hωS 𝒦Y) ≅
      stdComplex c (𝒦X.restrict V.1) :=
  haveI := hq.source_noetherian
  fun F => (upperShriekDualizingPlusIso _ _ F.compactification _
      (isBoundedBelow_dualizingQCoh (hp := hp) c 𝒦Y hωS)).symm ≪≫
    normalizationStdIso c hωS (hp.isShriekable_ι_comp_of_isAffineOpen hq hpe V.2)
      (𝒦X.restrict V.1) 𝒦Y e

omit [LocallyQuasiFinite f] in
/-- The identification on `V` computed at the compactification of the factorization. -/
theorem affineIsoOfIso_eq (V : X.affineOpens)
    (e : (𝒦X.restrict V.1).complex ≅ (UpperShriek.shriekOf c (V.1.ι ≫ f)
      (hp.isShriekable_ι_comp_of_isAffineOpen hq hpe V.2)).obj 𝒦Y.complex) :
    haveI := hq.source_noetherian
    ∀ F : OpenFiniteFactorization (affineHom (hp := hp) (hq := hq) hpe V),
    affineIsoOfIso c 𝒦X 𝒦Y hpe hωS V e F =
      newShriekStructureSheafZerothRestrictIso c f 𝒦X 𝒦Y V.1 ≪≫
        upperShriekStructureSheafZerothIsoOfIso _ F.compactification
          (isDualizing_stdComplex c (Category.id_comp q) hωS 𝒦Y)
          (affineNormalizationAt c 𝒦X 𝒦Y hpe hωS V e F) ≪≫
        upperShriekStructureSheafZerothIso F F.compactification := by
  have := hq.source_noetherian
  intro F
  have hA := upperShriekStructureSheafZerothIsoOfIso_trans_upperShriekStructureSheafZerothIso
    (affineHom (hp := hp) (hq := hq) hpe V) (isDualizing_stdComplex c (Category.id_comp q) hωS 𝒦Y) F
    (c _ (hp.isShriekable_ι_comp_of_isAffineOpen hq hpe V.2)) F.compactification
    (isBoundedBelow_dualizingQCoh (hp := hp) c 𝒦Y hωS)
    (affineNormalizationAt c 𝒦X 𝒦Y hpe hωS V e F)
  refine (Iso.trans_assoc _ _ _).trans
    (congrArg (newShriekStructureSheafZerothRestrictIso c f 𝒦X 𝒦Y V.1 ≪≫ ·) (Eq.trans ?_ hA))
  exact congrArg (fun x => upperShriekStructureSheafZerothIsoOfIso
      (affineHom (hp := hp) (hq := hq) hpe V)
      (c _ (hp.isShriekable_ι_comp_of_isAffineOpen hq hpe V.2))
      (isDualizing_stdComplex c (Category.id_comp q) hωS 𝒦Y) x ≪≫
        upperShriekStructureSheafZerothIso F
          (c _ (hp.isShriekable_ι_comp_of_isAffineOpen hq hpe V.2)))
    (Iso.self_symm_id_assoc _ _).symm

end NormalizedOnOpens

end Stacks.Duality
