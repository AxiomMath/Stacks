module

public import StacksFrontier.AlgebraicGeometry.TateMap.Rule
public import StacksFrontier.AlgebraicGeometry.TateMap.Construction
public import StacksFrontier.AlgebraicGeometry.TateMap.Basic
public import StacksFrontier.RingTheory.TateMap.ClaimEngine
public import StacksFrontier.RingTheory.TateMap.UniversalNice
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.ChartFactorization

/-!
# Uniqueness of the Tate rule

Let `c` be a rule assigning to every locally quasi-finite syntomic morphism `f : Y ⟶ X` of
locally Noetherian schemes an isomorphism `det(NL_{Y/X}) ≅ ω_{Y/X}`, and suppose `c` has the two
properties of Stacks 0FKD. Then on every affine chart `(U, V)` of `f` which is a chart base change
of a quasi-finite basic universal chart `univBase n d → univChart n d k` (Example 0FK8), the value
of `c` is the pullback of the Tate map `cUniv` of the universal chart (the proof of 0FKD). Since
the classified charts form a basis of the topology of `Y`, two such rules agree: this is the
uniqueness half of Stacks 0FKD.

## Main definitions

* `AlgebraicGeometry.TateMap.ringValue`: the value of a rule on `Spec B → Spec A` over the whole
  spectra, read on `A → B`.
* `AlgebraicGeometry.TateMap.affineChartCBC`, `specCBCInv`, `specCBCFwd`, `specSquareCBC`: the
  chart base changes identifying coordinate rings with the sections of their spectra, and the
  chart base change of the spectrum of a chart base change.

## Main results

* `Stacks.TateMap.eq_pullbackTate_of_inverse`: pulling back along a bijective square and back.
* `AlgebraicGeometry.TateMap.chartValue_eq_ringValue`: the value on an affine chart is the value on
  its coordinate rings (property (2) for the square of the chart).
* `AlgebraicGeometry.TateMap.ringValue_pullback`: the values on the two sides of a chart base
  change are related by pullback (property (2) for the spectrum of the chart base change).
* `AlgebraicGeometry.TateMap.ringValue_univ`: on a quasi-finite basic universal chart the value is
  `cUniv` (property (1), and niceness of the chart).
* `AlgebraicGeometry.TateMap.chartValue_eq_tateOf_of_isTateRule`: the three combined.
* `AlgebraicGeometry.TateMap.eq_of_isTateRule`: **two rules with the two properties agree**, the
  classified charts forming a basis of the source (`exists_classifiedChart`).

## References

* [Stacks Project, Tag 0FKD](https://stacks.math.columbia.edu/tag/0FKD)
* [Stacks Project, Example 0FK8](https://stacks.math.columbia.edu/tag/0FK8)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Discriminant
open scoped TensorProduct

universe u

namespace Stacks.TateMap

/-! ### Pulling back along a bijective square and back -/

section Inverse

variable {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra A B] [Algebra A A'] [Algebra A' B'] [Algebra B B']
  [Algebra.Syntomic A B] [Algebra.Syntomic A' B'] [IsNoetherianRing A] [IsNoetherianRing A']

/-- **Undoing a pullback along a bijective square.** If `e'` is the pullback of `e` along a chart
base change whose two maps are bijective, then `e` is the pullback of `e'` along the inverse
square, for any algebra structures `A' → A`, `B' → B` inverse to the given ones. -/
theorem eq_pullbackTate_of_inverse [Algebra A' A] [Algebra B' B]
    [IsScalarTower A A' A] [IsScalarTower B B' B]
    (D : ChartBaseChange A B A' B') (Dinv : ChartBaseChange A' B' A B)
    {F : FiniteOpenFactorization.{u, u, u} A B} (e : detNL A B ≃ₗ[B] dualizingModule F)
    (G : FiniteOpenFactorization.{u, u, u} A' B') :
    pullbackTate Dinv (pullbackTate D e G) F = e := by
  rw [← pullbackTate_comp D Dinv (ChartBaseChange.refl A B) e G F, pullbackTate_refl,
    dualizingModuleEquiv_refl]
  rfl

end Inverse

end Stacks.TateMap

/-! ### Sections of spectra -/

namespace AlgebraicGeometry.TateMap

open Stacks.TateMap

/-- The whole spectrum, as an affine open. -/
abbrev topAffine (R : CommRingCat.{u}) : (Spec R).affineOpens := ⟨⊤, isAffineOpen_top _⟩

/-- Equal morphisms of schemes induce equal maps `appLE` on sections. -/
theorem appLE_eq_of_eq {S T : Scheme.{u}} {φ ψ : S ⟶ T} (h : φ = ψ) {O : T.Opens} {O' : S.Opens}
    (e : O' ≤ φ ⁻¹ᵁ O) (e' : O' ≤ ψ ⁻¹ᵁ O) : φ.appLE O O' e = ψ.appLE O O' e' := by
  subst h
  rfl

/-- The maps on sections of a morphism of the category of Section 0FKB form a commutative
square on any compatible quadruple of opens. -/
theorem OpenBaseChangeSquare.appLE_comm {X Y X' Y' : Scheme.{u}} {f : Y ⟶ X} {f' : Y' ⟶ X'}
    (sq : OpenBaseChangeSquare f f') (U : X.Opens) (V : Y.Opens) (U' : X'.Opens) (V' : Y'.Opens)
    (hVU : V ≤ f ⁻¹ᵁ U) (hU'U : U' ≤ sq.base ⁻¹ᵁ U) (hV'U' : V' ≤ f' ⁻¹ᵁ U')
    (hV'V : V' ≤ sq.cover ⁻¹ᵁ V) :
    f.appLE U V hVU ≫ sq.cover.appLE V V' hV'V =
      sq.base.appLE U U' hU'U ≫ f'.appLE U' V' hV'U' := by
  rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  exact appLE_eq_of_eq sq.w _ _

/-- On an affine open `U`, the canonical open immersion `Spec Γ(X, U) → X` induces the inverse of
`Γ(Spec Γ(X, U), ⊤) ≅ Γ(X, U)` on sections over `U`. -/
theorem fromSpec_appLE_top {X : Scheme.{u}} (U : X.affineOpens)
    (h : (⊤ : (Spec Γ(X, U.1)).Opens) ≤ U.2.fromSpec ⁻¹ᵁ U.1) :
    U.2.fromSpec.appLE U.1 ⊤ h = (Scheme.ΓSpecIso Γ(X, U.1)).inv := by
  rw [Scheme.Hom.appLE, U.2.fromSpec_app_self, Category.assoc, ← Functor.map_comp,
    show ((eqToHom U.2.fromSpec_preimage_self).op ≫ (homOfLE h).op :
      Opposite.op (⊤ : (Spec Γ(X, U.1)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ from Subsingleton.elim _ _,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- On an affine open `U`, the map `Γ(X, U) → Γ(Spec Γ(X, U), ⊤)` induced by
`Spec Γ(X, U) → X` is bijective. -/
theorem bijective_fromSpec_appLE_top {X : Scheme.{u}} (U : X.affineOpens)
    (h : (⊤ : (Spec Γ(X, U.1)).Opens) ≤ U.2.fromSpec ⁻¹ᵁ U.1) :
    Function.Bijective (U.2.fromSpec.appLE U.1 ⊤ h).hom := by
  rw [fromSpec_appLE_top U h]
  exact ConcreteCategory.bijective_of_isIso _

/-- On the whole spectra, the map on sections of `Spec.map g` is `g`. -/
theorem specMap_appLE_top {R S : CommRingCat.{u}} (g : R ⟶ S)
    (h : (⊤ : (Spec S).Opens) ≤ Spec.map g ⁻¹ᵁ ⊤) :
    (Spec.map g).appLE ⊤ ⊤ h = (Scheme.ΓSpecIso R).hom ≫ g ≫ (Scheme.ΓSpecIso S).inv := by
  have h1 : (Spec.map g).appLE ⊤ ⊤ h = (Spec.map g).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_map' _ _ (Scheme.Hom.preimage_top _).symm).symm
  rw [h1, ← Scheme.ΓSpecIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]

/-- On an affine open `U`, `Γ(Spec Γ(X, U), ⊤) ≅ Γ(X, U)` undoes the map induced by
`Spec Γ(X, U) → X`. -/
private theorem ΓSpecIso_hom_fromSpec_appLE_top {X : Scheme.{u}} (U : X.affineOpens)
    (h : (⊤ : (Spec Γ(X, U.1)).Opens) ≤ U.2.fromSpec ⁻¹ᵁ U.1) (a : Γ(X, U.1)) :
    (Scheme.ΓSpecIso Γ(X, U.1)).hom.hom ((U.2.fromSpec.appLE U.1 ⊤ h).hom a) = a := by
  rw [fromSpec_appLE_top U h]
  exact (Scheme.ΓSpecIso Γ(X, U.1)).inv_hom_id_apply a

/-- Under the identifications `Γ(Spec R, ⊤) ≅ R`, the map on sections of `Spec.map g` is `g`. -/
private theorem ΓSpecIso_hom_specMap_appLE_top {R S : CommRingCat.{u}} (g : R ⟶ S)
    (h : (⊤ : (Spec S).Opens) ≤ Spec.map g ⁻¹ᵁ ⊤) (r : Γ(Spec R, ⊤)) :
    (Scheme.ΓSpecIso S).hom.hom (((Spec.map g).appLE ⊤ ⊤ h).hom r) =
      g.hom ((Scheme.ΓSpecIso R).hom.hom r) := by
  rw [specMap_appLE_top]
  exact (Scheme.ΓSpecIso S).inv_hom_id_apply _

/-! ### The square of an affine chart -/

section AffineChart

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.affineOpens) (V : Y.affineOpens)
  (hVU : V.1 ≤ f ⁻¹ᵁ U.1)

/-- The whole spectrum `Spec Γ(X, U)` lies over `U` under the base of the square of an affine
chart. -/
theorem affineChart_hU'U : (topAffine Γ(X, U.1)).1 ≤
    (OpenBaseChangeSquare.ofAffineChart f U V hVU).base ⁻¹ᵁ U.1 :=
  U.2.fromSpec_preimage_self.ge

/-- The whole spectrum `Spec Γ(Y, V)` lies over `V` under the cover of the square of an affine
chart. -/
theorem affineChart_hV'V : (topAffine Γ(Y, V.1)).1 ≤
    (OpenBaseChangeSquare.ofAffineChart f U V hVU).cover ⁻¹ᵁ V.1 :=
  V.2.fromSpec_preimage_self.ge

/-- The whole spectrum `Spec Γ(Y, V)` lies over the whole spectrum `Spec Γ(X, U)`. -/
theorem affineChart_hV'U' : (topAffine Γ(Y, V.1)).1 ≤
    Spec.map (f.appLE U.1 V.1 hVU) ⁻¹ᵁ (topAffine Γ(X, U.1)).1 :=
  (Scheme.Hom.preimage_top _).ge

/-- The chart base change of the square of an affine chart, on the whole spectra: both maps are
bijective. -/
def affineChartCBC :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    letI : Algebra Γ(X, U.1) Γ(Spec Γ(X, U.1), ⊤) :=
      ((OpenBaseChangeSquare.ofAffineChart f U V hVU).base.appLE U.1 ⊤
        (affineChart_hU'U f U V hVU)).hom.toAlgebra
    letI : Algebra Γ(Spec Γ(X, U.1), ⊤) Γ(Spec Γ(Y, V.1), ⊤) :=
      ((Spec.map (f.appLE U.1 V.1 hVU)).appLE ⊤ ⊤ (affineChart_hV'U' f U V hVU)).hom.toAlgebra
    letI : Algebra Γ(Y, V.1) Γ(Spec Γ(Y, V.1), ⊤) :=
      ((OpenBaseChangeSquare.ofAffineChart f U V hVU).cover.appLE V.1 ⊤
        (affineChart_hV'V f U V hVU)).hom.toAlgebra
    ChartBaseChange Γ(X, U.1) Γ(Y, V.1) Γ(Spec Γ(X, U.1), ⊤) Γ(Spec Γ(Y, V.1), ⊤) :=
  letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  letI : Algebra Γ(X, U.1) Γ(Spec Γ(X, U.1), ⊤) :=
    ((OpenBaseChangeSquare.ofAffineChart f U V hVU).base.appLE U.1 ⊤
      (affineChart_hU'U f U V hVU)).hom.toAlgebra
  letI : Algebra Γ(Spec Γ(X, U.1), ⊤) Γ(Spec Γ(Y, V.1), ⊤) :=
    ((Spec.map (f.appLE U.1 V.1 hVU)).appLE ⊤ ⊤ (affineChart_hV'U' f U V hVU)).hom.toAlgebra
  letI : Algebra Γ(Y, V.1) Γ(Spec Γ(Y, V.1), ⊤) :=
    ((OpenBaseChangeSquare.ofAffineChart f U V hVU).cover.appLE V.1 ⊤
      (affineChart_hV'V f U V hVU)).hom.toAlgebra
  ChartBaseChange.ofBijective
    (bijective_fromSpec_appLE_top U (affineChart_hU'U f U V hVU))
    (bijective_fromSpec_appLE_top V (affineChart_hV'V f U V hVU))
    (fun a ↦ ConcreteCategory.congr_hom ((OpenBaseChangeSquare.ofAffineChart f U V hVU).appLE_comm
      U.1 V.1 ⊤ ⊤ hVU (affineChart_hU'U f U V hVU) (affineChart_hV'U' f U V hVU)
      (affineChart_hV'V f U V hVU)) a)

/-- Under the identifications `Γ(Spec R, ⊤) ≅ R`, the map on sections of
`Spec Γ(Y, V) → Spec Γ(X, U)` is `Γ(X, U) → Γ(Y, V)`. -/
theorem affineChartCBCInv_comm (r : Γ(Spec Γ(X, U.1), ⊤)) :
    (Scheme.ΓSpecIso Γ(Y, V.1)).hom.hom
        (((Spec.map (f.appLE U.1 V.1 hVU)).appLE ⊤ ⊤ (affineChart_hV'U' f U V hVU)).hom r) =
      (f.appLE U.1 V.1 hVU).hom ((Scheme.ΓSpecIso Γ(X, U.1)).hom.hom r) := by
  exact ΓSpecIso_hom_specMap_appLE_top _ _ r

/-- The inverse of `affineChartCBC`. -/
def affineChartCBCInv :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    letI : Algebra Γ(Spec Γ(X, U.1), ⊤) Γ(X, U.1) :=
      (Scheme.ΓSpecIso Γ(X, U.1)).hom.hom.toAlgebra
    letI : Algebra Γ(Spec Γ(X, U.1), ⊤) Γ(Spec Γ(Y, V.1), ⊤) :=
      ((Spec.map (f.appLE U.1 V.1 hVU)).appLE ⊤ ⊤ (affineChart_hV'U' f U V hVU)).hom.toAlgebra
    letI : Algebra Γ(Spec Γ(Y, V.1), ⊤) Γ(Y, V.1) :=
      (Scheme.ΓSpecIso Γ(Y, V.1)).hom.hom.toAlgebra
    ChartBaseChange Γ(Spec Γ(X, U.1), ⊤) Γ(Spec Γ(Y, V.1), ⊤) Γ(X, U.1) Γ(Y, V.1) :=
  letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  letI : Algebra Γ(Spec Γ(X, U.1), ⊤) Γ(X, U.1) :=
    (Scheme.ΓSpecIso Γ(X, U.1)).hom.hom.toAlgebra
  letI : Algebra Γ(Spec Γ(X, U.1), ⊤) Γ(Spec Γ(Y, V.1), ⊤) :=
    ((Spec.map (f.appLE U.1 V.1 hVU)).appLE ⊤ ⊤ (affineChart_hV'U' f U V hVU)).hom.toAlgebra
  letI : Algebra Γ(Spec Γ(Y, V.1), ⊤) Γ(Y, V.1) :=
    (Scheme.ΓSpecIso Γ(Y, V.1)).hom.hom.toAlgebra
  ChartBaseChange.ofBijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso Γ(X, U.1)).hom)
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso Γ(Y, V.1)).hom)
    (affineChartCBCInv_comm f U V hVU)

/-- The square of an affine chart is an object of the category of Section 0FKB. -/
theorem isQuasiFiniteSyntomic_affineChart (hf : IsQuasiFiniteSyntomic f) :
    IsQuasiFiniteSyntomic (Spec.map (f.appLE U.1 V.1 hVU)) := by
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  have := algebra_syntomic_appLE hf.2 U V hVU
  have := AlgebraicGeometry.quasiFinite_appLE hf.1 U V hVU
  exact isQuasiFiniteSyntomic_specMap Γ(X, U.1) Γ(Y, V.1)

/-- **Step (i): an affine chart.** The value of a Tate rule on an affine chart `(U, V)` of `f` is
the pullback, along the identification of the coordinate rings with the sections of their
spectra, of its value on the whole spectra for `Spec Γ(Y, V) → Spec Γ(X, U)`. -/
theorem chartValue_eq_pullbackTate_affineChart (c : TateRule.{u}) (hc : IsTateRuleOnCharts c)
    [IsLocallyNoetherian X] (hf : IsQuasiFiniteSyntomic f) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    haveI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    haveI := algebra_syntomic_appLE hf.2 U V hVU
    letI : Algebra Γ(Spec Γ(X, U.1), ⊤) Γ(Spec Γ(Y, V.1), ⊤) :=
      ((Spec.map (f.appLE U.1 V.1 hVU)).appLE ⊤ ⊤ (affineChart_hV'U' f U V hVU)).hom.toAlgebra
    haveI := algebra_syntomic_appLE (isQuasiFiniteSyntomic_affineChart f U V hVU hf).2
      (topAffine _) (topAffine _) (affineChart_hV'U' f U V hVU)
    haveI : IsNoetherianRing Γ(Spec Γ(X, U.1), ⊤) :=
      IsLocallyNoetherian.component_noetherian (topAffine _)
    letI : Algebra Γ(Spec Γ(X, U.1), ⊤) Γ(X, U.1) :=
      (Scheme.ΓSpecIso Γ(X, U.1)).hom.hom.toAlgebra
    letI : Algebra Γ(Spec Γ(Y, V.1), ⊤) Γ(Y, V.1) :=
      (Scheme.ΓSpecIso Γ(Y, V.1)).hom.hom.toAlgebra
    ∀ (F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1))
      (G : FiniteOpenFactorization.{u, u, u} Γ(Spec Γ(X, U.1), ⊤) Γ(Spec Γ(Y, V.1), ⊤)),
      chartValue (c X Y f hf) U V hVU F =
        pullbackTate (affineChartCBCInv f U V hVU)
          (chartValue (c _ _ (Spec.map (f.appLE U.1 V.1 hVU))
            (isQuasiFiniteSyntomic_affineChart f U V hVU hf)) (topAffine _) (topAffine _)
            (affineChart_hV'U' f U V hVU) G) F := by
  intro F G
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have := algebra_syntomic_appLE hf.2 U V hVU
  let : Algebra Γ(Spec Γ(X, U.1), ⊤) Γ(Spec Γ(Y, V.1), ⊤) :=
    ((Spec.map (f.appLE U.1 V.1 hVU)).appLE ⊤ ⊤ (affineChart_hV'U' f U V hVU)).hom.toAlgebra
  have := algebra_syntomic_appLE (isQuasiFiniteSyntomic_affineChart f U V hVU hf).2
    (topAffine _) (topAffine _) (affineChart_hV'U' f U V hVU)
  have : IsNoetherianRing Γ(Spec Γ(X, U.1), ⊤) :=
    IsLocallyNoetherian.component_noetherian (topAffine _)
  let : Algebra Γ(Spec Γ(X, U.1), ⊤) Γ(X, U.1) :=
    (Scheme.ΓSpecIso Γ(X, U.1)).hom.hom.toAlgebra
  let : Algebra Γ(Spec Γ(Y, V.1), ⊤) Γ(Y, V.1) :=
    (Scheme.ΓSpecIso Γ(Y, V.1)).hom.hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(Spec Γ(X, U.1), ⊤) :=
    ((OpenBaseChangeSquare.ofAffineChart f U V hVU).base.appLE U.1 ⊤
      (affineChart_hU'U f U V hVU)).hom.toAlgebra
  let : Algebra Γ(Y, V.1) Γ(Spec Γ(Y, V.1), ⊤) :=
    ((OpenBaseChangeSquare.ofAffineChart f U V hVU).cover.appLE V.1 ⊤
      (affineChart_hV'V f U V hVU)).hom.toAlgebra
  have h2 := hc.2 X Y (Spec Γ(X, U.1)) (Spec Γ(Y, V.1)) f (Spec.map (f.appLE U.1 V.1 hVU)) hf
    (isQuasiFiniteSyntomic_affineChart f U V hVU hf) (OpenBaseChangeSquare.ofAffineChart f U V hVU)
    U V (topAffine _) (topAffine _) hVU (affineChart_hU'U f U V hVU)
    (affineChart_hV'U' f U V hVU) (affineChart_hV'V f U V hVU) (affineChartCBC f U V hVU) F G
  rw [← h2]
  have : IsScalarTower Γ(X, U.1) Γ(Spec Γ(X, U.1), ⊤) Γ(X, U.1) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (ΓSpecIso_hom_fromSpec_appLE_top U _ a).symm
  have : IsScalarTower Γ(Y, V.1) Γ(Spec Γ(Y, V.1), ⊤) Γ(Y, V.1) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (ΓSpecIso_hom_fromSpec_appLE_top V _ a).symm
  exact (eq_pullbackTate_of_inverse (affineChartCBC f U V hVU) (affineChartCBCInv f U V hVU)
    _ G).symm

end AffineChart

/-! ### Property (1) on an affine chart -/

section ChartDelta

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] {f : Y ⟶ X} {hf : IsQuasiFiniteSyntomic f}

/-- If `c` carries `δ(NL_{Y/X})` to `τ_{Y/X}`, then its value on every affine chart carries
`δ(NL_{B/A})` to `τ_{B/A}`. -/
theorem chartValue_deltaNL (c : detNL f hf ≅ omega f hf)
    (hc : c.hom.app ⊤ (deltaNL f hf) = tau f hf) (U : X.affineOpens) (V : Y.affineOpens)
    (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    haveI := algebra_syntomic_appLE hf.2 U V hVU
    haveI := AlgebraicGeometry.quasiFinite_appLE hf.1 U V hVU
    letI := isLocallyNoetherian_source f hf
    haveI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    haveI : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
    ∀ F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1),
      chartValue c U V hVU F (Stacks.TateMap.deltaNL Γ(X, U.1) Γ(Y, V.1)) =
        dualizingModule.traceElement F := by
  intro F
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  have := algebra_syntomic_appLE hf.2 U V hVU
  have := AlgebraicGeometry.quasiFinite_appLE hf.1 U V hVU
  let := isLocallyNoetherian_source f hf
  let := hf.1
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
  have : Flat f := AlgebraicGeometry.flat hf.2
  have hnat : c.hom.app V.1 ((detNL f hf).presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op
      (deltaNL f hf)) = (omega f hf).presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op
        (c.hom.app ⊤ (deltaNL f hf)) :=
    congr($(c.hom.mapPresheaf.naturality (homOfLE (le_top : V.1 ≤ ⊤)).op) (deltaNL f hf))
  rw [← detNLChartEquiv_deltaNL f hf U V hVU]
  show (omegaData f hf).localEquiv U V hVU F
    (c.hom.app V.1 ((detNLChartEquiv f hf U V hVU).symm (detNLChartEquiv f hf U V hVU
      ((detNL f hf).presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op (deltaNL f hf))))) = _
  rw [LinearEquiv.symm_apply_apply, hnat, hc]
  exact localEquiv_relativeTraceSection (omegaData f hf) U V hVU F

end ChartDelta

/-! ### The value of a rule on a ring -/

section RingValue

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- The spectrum of `A → B`. -/
abbrev specHom : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))

/-- The whole spectrum of `B` lies over the whole spectrum of `A`. -/
theorem specHom_top :
    (topAffine (CommRingCat.of B)).1 ≤ specHom A B ⁻¹ᵁ (topAffine (CommRingCat.of A)).1 :=
  (Scheme.Hom.preimage_top _).ge

/-- Under the identifications `Γ(Spec R, ⊤) ≅ R`, the map on sections of `Spec B → Spec A` is
`algebraMap A B`. -/
theorem specCBCInv_comm (r : Γ(Spec (CommRingCat.of A), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (((specHom A B).appLE ⊤ ⊤
        (specHom_top A B)).hom r) =
      algebraMap A B ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom r) := by
  exact ΓSpecIso_hom_specMap_appLE_top _ _ r

/-- The identification of the sections of the spectra of `A → B` with `A → B`, as a chart base
change. -/
def specCBCInv :
    letI : Algebra Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of B), ⊤) :=
      ((specHom A B).appLE ⊤ ⊤ (specHom_top A B)).hom.toAlgebra
    letI : Algebra Γ(Spec (CommRingCat.of A), ⊤) A :=
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toAlgebra
    letI : Algebra Γ(Spec (CommRingCat.of B), ⊤) B :=
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.toAlgebra
    ChartBaseChange Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of B), ⊤) A B :=
  letI : Algebra Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of B), ⊤) :=
    ((specHom A B).appLE ⊤ ⊤ (specHom_top A B)).hom.toAlgebra
  letI : Algebra Γ(Spec (CommRingCat.of A), ⊤) A :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toAlgebra
  letI : Algebra Γ(Spec (CommRingCat.of B), ⊤) B :=
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.toAlgebra
  ChartBaseChange.ofBijective
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom)
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).hom)
    (specCBCInv_comm A B)

variable [IsNoetherianRing A] [Algebra.QuasiFinite A B] [Algebra.Syntomic A B]

omit [IsNoetherianRing A] in
/-- `Spec B → Spec A` is quasi-finite and syntomic. -/
theorem isQuasiFiniteSyntomic_specHom : IsQuasiFiniteSyntomic (specHom A B) :=
  isQuasiFiniteSyntomic_specMap A B

/-- **The value of a rule on a ring.** For a rule `c` and a quasi-finite syntomic algebra `B`
over a Noetherian ring `A`, the value of `c` on `Spec B → Spec A` over the whole spectra, read on
`A → B` itself. -/
def ringValue (c : TateRule.{u}) (G : FiniteOpenFactorization.{u, u, u} A B) :
    Stacks.TateMap.detNL A B ≃ₗ[B] dualizingModule G :=
  letI : Algebra Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of B), ⊤) :=
    ((specHom A B).appLE ⊤ ⊤ (specHom_top A B)).hom.toAlgebra
  letI : Algebra Γ(Spec (CommRingCat.of A), ⊤) A :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toAlgebra
  letI : Algebra Γ(Spec (CommRingCat.of B), ⊤) B :=
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.toAlgebra
  haveI := algebra_syntomic_appLE (isQuasiFiniteSyntomic_specHom A B).2 (topAffine _)
    (topAffine _) (specHom_top A B)
  haveI := AlgebraicGeometry.quasiFinite_appLE (isQuasiFiniteSyntomic_specHom A B).1
    (topAffine _) (topAffine _) (specHom_top A B)
  haveI : IsNoetherianRing Γ(Spec (CommRingCat.of A), ⊤) :=
    IsLocallyNoetherian.component_noetherian (topAffine _)
  pullbackTate (specCBCInv A B)
    (chartValue (c _ _ (specHom A B) (isQuasiFiniteSyntomic_specHom A B)) (topAffine _)
      (topAffine _) (specHom_top A B)
      (nonempty_finiteOpenFactorization (A := Γ(Spec (CommRingCat.of A), ⊤))
        (B := Γ(Spec (CommRingCat.of B), ⊤))).some) G

/-- A rule with property (1) has values on rings carrying `δ(NL_{B/A})` to `τ_{B/A}`. -/
theorem ringValue_deltaNL [IsNoetherianRing B] (c : TateRule.{u}) (hc : IsTateRuleOnCharts c)
    (G : FiniteOpenFactorization.{u, u, u} A B) :
    ringValue A B c G (Stacks.TateMap.deltaNL A B) = dualizingModule.traceElement G := by
  let : Algebra Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of B), ⊤) :=
    ((specHom A B).appLE ⊤ ⊤ (specHom_top A B)).hom.toAlgebra
  let : Algebra Γ(Spec (CommRingCat.of A), ⊤) A :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toAlgebra
  let : Algebra Γ(Spec (CommRingCat.of B), ⊤) B :=
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.toAlgebra
  have := algebra_syntomic_appLE (isQuasiFiniteSyntomic_specHom A B).2 (topAffine _)
    (topAffine _) (specHom_top A B)
  have := AlgebraicGeometry.quasiFinite_appLE (isQuasiFiniteSyntomic_specHom A B).1
    (topAffine _) (topAffine _) (specHom_top A B)
  have : IsNoetherianRing Γ(Spec (CommRingCat.of A), ⊤) :=
    IsLocallyNoetherian.component_noetherian (topAffine _)
  have : IsNoetherianRing Γ(Spec (CommRingCat.of B), ⊤) :=
    IsLocallyNoetherian.component_noetherian (topAffine _)
  exact pullbackTate_deltaNL (specCBCInv A B) _ G
    (chartValue_deltaNL _ (hc.1 _ _ (specHom A B) (isQuasiFiniteSyntomic_specHom A B))
      (topAffine _) (topAffine _) (specHom_top A B) _)

end RingValue

section Classification

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- Under the identifications `R ≅ Γ(Spec R, ⊤)`, the map on sections of `Spec B → Spec A` is
`algebraMap A B`. -/
theorem specCBCFwd_comm (a : A) :
    ((specHom A B).appLE ⊤ ⊤ (specHom_top A B)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B a) := by
  rw [specMap_appLE_top]
  show (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B
    ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))) = _
  rw [(Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id_apply]

/-- The identification of `A → B` with the sections of its spectra, as a chart base change. -/
def specCBCFwd :
    letI : Algebra Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of B), ⊤) :=
      ((specHom A B).appLE ⊤ ⊤ (specHom_top A B)).hom.toAlgebra
    letI : Algebra A Γ(Spec (CommRingCat.of A), ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.toAlgebra
    letI : Algebra B Γ(Spec (CommRingCat.of B), ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom.toAlgebra
    ChartBaseChange A B Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of B), ⊤) :=
  letI : Algebra Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of B), ⊤) :=
    ((specHom A B).appLE ⊤ ⊤ (specHom_top A B)).hom.toAlgebra
  letI : Algebra A Γ(Spec (CommRingCat.of A), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.toAlgebra
  letI : Algebra B Γ(Spec (CommRingCat.of B), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom.toAlgebra
  ChartBaseChange.ofBijective
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv)
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).inv)
    (fun a ↦ (specCBCFwd_comm A B a).symm)

end Classification

section ClassificationSquare

variable {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra A B] [Algebra A A'] [Algebra A' B'] [Algebra B B'] (D : ChartBaseChange A B A' B')

/-- The whole spectrum of `A'` lies over the whole spectrum of `A` under the base of the
spectrum of a chart base change. -/
theorem ofSpec_hU'U : (topAffine (CommRingCat.of A')).1 ≤
    (OpenBaseChangeSquare.ofSpec D).base ⁻¹ᵁ (topAffine (CommRingCat.of A)).1 :=
  (Scheme.Hom.preimage_top _).ge

/-- The whole spectrum of `B'` lies over the whole spectrum of `B` under the cover of the
spectrum of a chart base change. -/
theorem ofSpec_hV'V : (topAffine (CommRingCat.of B')).1 ≤
    (OpenBaseChangeSquare.ofSpec D).cover ⁻¹ᵁ (topAffine (CommRingCat.of B)).1 :=
  (Scheme.Hom.preimage_top _).ge

/-- On sections over the whole spectra, the base of the spectrum of a chart base change is the
map `A → A'`. -/
theorem ofSpec_base_appLE (x : Γ(Spec (CommRingCat.of A), ⊤)) :
    ((OpenBaseChangeSquare.ofSpec D).base.appLE ⊤ ⊤ (ofSpec_hU'U D)).hom x =
      (Scheme.ΓSpecIso (CommRingCat.of A')).inv.hom
        (algebraMap A A' ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom x)) :=
  congrArg (fun φ : Γ(Spec (CommRingCat.of A), ⊤) ⟶ Γ(Spec (CommRingCat.of A'), ⊤) ↦
    φ.hom x) (specMap_appLE_top (CommRingCat.ofHom (algebraMap A A')) (ofSpec_hU'U D))

/-- On sections over the whole spectra, the cover of the spectrum of a chart base change is the
map `B → B'`. -/
theorem ofSpec_cover_appLE (x : Γ(Spec (CommRingCat.of B), ⊤)) :
    ((OpenBaseChangeSquare.ofSpec D).cover.appLE ⊤ ⊤ (ofSpec_hV'V D)).hom x =
      (Scheme.ΓSpecIso (CommRingCat.of B')).inv.hom
        (algebraMap B B' ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom x)) :=
  congrArg (fun φ : Γ(Spec (CommRingCat.of B), ⊤) ⟶ Γ(Spec (CommRingCat.of B'), ⊤) ↦
    φ.hom x) (specMap_appLE_top (CommRingCat.ofHom (algebraMap B B')) (ofSpec_hV'V D))

/-- The chart base change of the spectrum of a chart base change, on the whole spectra. -/
def specSquareCBC :
    letI : Algebra Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of B), ⊤) :=
      ((specHom A B).appLE ⊤ ⊤ (specHom_top A B)).hom.toAlgebra
    letI : Algebra Γ(Spec (CommRingCat.of A'), ⊤) Γ(Spec (CommRingCat.of B'), ⊤) :=
      ((specHom A' B').appLE ⊤ ⊤ (specHom_top A' B')).hom.toAlgebra
    letI : Algebra Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of A'), ⊤) :=
      ((OpenBaseChangeSquare.ofSpec D).base.appLE ⊤ ⊤ (ofSpec_hU'U D)).hom.toAlgebra
    letI : Algebra Γ(Spec (CommRingCat.of B), ⊤) Γ(Spec (CommRingCat.of B'), ⊤) :=
      ((OpenBaseChangeSquare.ofSpec D).cover.appLE ⊤ ⊤ (ofSpec_hV'V D)).hom.toAlgebra
    ChartBaseChange Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of B), ⊤)
      Γ(Spec (CommRingCat.of A'), ⊤) Γ(Spec (CommRingCat.of B'), ⊤) :=
  letI : Algebra Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of B), ⊤) :=
    ((specHom A B).appLE ⊤ ⊤ (specHom_top A B)).hom.toAlgebra
  letI : Algebra Γ(Spec (CommRingCat.of A'), ⊤) Γ(Spec (CommRingCat.of B'), ⊤) :=
    ((specHom A' B').appLE ⊤ ⊤ (specHom_top A' B')).hom.toAlgebra
  letI : Algebra Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of A'), ⊤) :=
    ((OpenBaseChangeSquare.ofSpec D).base.appLE ⊤ ⊤ (ofSpec_hU'U D)).hom.toAlgebra
  letI : Algebra Γ(Spec (CommRingCat.of B), ⊤) Γ(Spec (CommRingCat.of B'), ⊤) :=
    ((OpenBaseChangeSquare.ofSpec D).cover.appLE ⊤ ⊤ (ofSpec_hV'V D)).hom.toAlgebra
  letI : Algebra Γ(Spec (CommRingCat.of A), ⊤) A :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toAlgebra
  letI : Algebra Γ(Spec (CommRingCat.of B), ⊤) B :=
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.toAlgebra
  letI : Algebra A' Γ(Spec (CommRingCat.of A'), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of A')).inv.hom.toAlgebra
  letI : Algebra B' Γ(Spec (CommRingCat.of B'), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of B')).inv.hom.toAlgebra
  letI : Algebra Γ(Spec (CommRingCat.of A), ⊤) A' :=
    ((algebraMap A A').comp (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom).toAlgebra
  haveI : IsScalarTower Γ(Spec (CommRingCat.of A), ⊤) A A' :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : Algebra Γ(Spec (CommRingCat.of B), ⊤) B' :=
    ((algebraMap B B').comp (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom).toAlgebra
  haveI : IsScalarTower Γ(Spec (CommRingCat.of B), ⊤) B B' :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower Γ(Spec (CommRingCat.of A), ⊤) A' Γ(Spec (CommRingCat.of A'), ⊤) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ ofSpec_base_appLE D x
  haveI : IsScalarTower Γ(Spec (CommRingCat.of B), ⊤) B' Γ(Spec (CommRingCat.of B'), ⊤) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ ofSpec_cover_appLE D x
  (specCBCFwd A' B').comp (D.comp (specCBCInv A B))

end ClassificationSquare

section Steps

/-- **Step (i).** The value of a rule on an affine chart is its value on the coordinate rings. -/
theorem chartValue_eq_ringValue (c : TateRule.{u}) (hc : IsTateRuleOnCharts c) {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] (f : Y ⟶ X) (hf : IsQuasiFiniteSyntomic f) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    haveI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    haveI := algebra_syntomic_appLE hf.2 U V hVU
    haveI := AlgebraicGeometry.quasiFinite_appLE hf.1 U V hVU
    ∀ F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1),
      chartValue (c X Y f hf) U V hVU F = ringValue Γ(X, U.1) Γ(Y, V.1) c F := by
  intro F
  exact chartValue_eq_pullbackTate_affineChart f U V hVU c hc hf F _

/-- **Step (iii).** On a quasi-finite basic universal chart with a positive degree bound, the
value of a rule with property (1) is the Tate map of the universal chart. -/
theorem ringValue_univ (c : TateRule.{u}) (hc : IsTateRuleOnCharts c) (n d : ℕ) [NeZero d]
    (k : MvPolynomial (Fin n) (univBase.{u} n d))
    [Algebra.QuasiFinite (univBase.{u} n d) (univChart n d k)]
    (F : FiniteOpenFactorization.{u, u, u} (univBase.{u} n d) (univChart n d k)) :
    ringValue (univBase.{u} n d) (univChart n d k) c F = cUniv n d k F :=
  eq_cUniv n d k F _ (ringValue_deltaNL _ _ c hc F)

/-- **Step (ii): a classification.** The value of a rule with property (2) on a chart base
change `A' → B'` of `A → B` is the pullback of its value on `A → B`. -/
theorem ringValue_pullback (c : TateRule.{u}) (hc : IsTateRuleOnCharts c) {A B A' B' : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [Algebra A B] [Algebra A A']
    [Algebra A' B'] [Algebra B B'] [IsNoetherianRing A] [IsNoetherianRing A']
    [Algebra.QuasiFinite A B] [Algebra.QuasiFinite A' B'] [Algebra.Syntomic A B]
    [Algebra.Syntomic A' B'] (D : ChartBaseChange A B A' B')
    (G : FiniteOpenFactorization.{u, u, u} A B) (G' : FiniteOpenFactorization.{u, u, u} A' B') :
    ringValue A' B' c G' = pullbackTate D (ringValue A B c G) G' := by
  let : Algebra Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of B), ⊤) :=
    ((specHom A B).appLE ⊤ ⊤ (specHom_top A B)).hom.toAlgebra
  let : Algebra Γ(Spec (CommRingCat.of A'), ⊤) Γ(Spec (CommRingCat.of B'), ⊤) :=
    ((specHom A' B').appLE ⊤ ⊤ (specHom_top A' B')).hom.toAlgebra
  let : Algebra Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of A'), ⊤) :=
    ((OpenBaseChangeSquare.ofSpec D).base.appLE ⊤ ⊤ (ofSpec_hU'U D)).hom.toAlgebra
  let : Algebra Γ(Spec (CommRingCat.of B), ⊤) Γ(Spec (CommRingCat.of B'), ⊤) :=
    ((OpenBaseChangeSquare.ofSpec D).cover.appLE ⊤ ⊤ (ofSpec_hV'V D)).hom.toAlgebra
  let : Algebra Γ(Spec (CommRingCat.of A), ⊤) A :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toAlgebra
  let : Algebra Γ(Spec (CommRingCat.of B), ⊤) B :=
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.toAlgebra
  let : Algebra Γ(Spec (CommRingCat.of A'), ⊤) A' :=
    (Scheme.ΓSpecIso (CommRingCat.of A')).hom.hom.toAlgebra
  let : Algebra Γ(Spec (CommRingCat.of B'), ⊤) B' :=
    (Scheme.ΓSpecIso (CommRingCat.of B')).hom.hom.toAlgebra
  let : Algebra Γ(Spec (CommRingCat.of A), ⊤) A' :=
    ((algebraMap A A').comp (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom).toAlgebra
  have : IsScalarTower Γ(Spec (CommRingCat.of A), ⊤) A A' :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra Γ(Spec (CommRingCat.of B), ⊤) B' :=
    ((algebraMap B B').comp (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom).toAlgebra
  have : IsScalarTower Γ(Spec (CommRingCat.of B), ⊤) B B' :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of A'), ⊤) A' :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      (ΓSpecIso_hom_specMap_appLE_top (CommRingCat.ofHom (algebraMap A A')) _ x).symm
  have : IsScalarTower Γ(Spec (CommRingCat.of B), ⊤) Γ(Spec (CommRingCat.of B'), ⊤) B' :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      (ΓSpecIso_hom_specMap_appLE_top (CommRingCat.ofHom (algebraMap B B')) _ x).symm
  have := algebra_syntomic_appLE (isQuasiFiniteSyntomic_specHom A B).2 (topAffine _)
    (topAffine _) (specHom_top A B)
  have := AlgebraicGeometry.quasiFinite_appLE (isQuasiFiniteSyntomic_specHom A B).1
    (topAffine _) (topAffine _) (specHom_top A B)
  have := algebra_syntomic_appLE (isQuasiFiniteSyntomic_specHom A' B').2 (topAffine _)
    (topAffine _) (specHom_top A' B')
  have := AlgebraicGeometry.quasiFinite_appLE (isQuasiFiniteSyntomic_specHom A' B').1
    (topAffine _) (topAffine _) (specHom_top A' B')
  have : IsNoetherianRing Γ(Spec (CommRingCat.of A), ⊤) :=
    IsLocallyNoetherian.component_noetherian (topAffine _)
  have : IsNoetherianRing Γ(Spec (CommRingCat.of A'), ⊤) :=
    IsLocallyNoetherian.component_noetherian (topAffine _)
  let G₀ := (nonempty_finiteOpenFactorization (A := Γ(Spec (CommRingCat.of A), ⊤))
    (B := Γ(Spec (CommRingCat.of B), ⊤))).some
  let G₀' := (nonempty_finiteOpenFactorization (A := Γ(Spec (CommRingCat.of A'), ⊤))
    (B := Γ(Spec (CommRingCat.of B'), ⊤))).some
  let cv := chartValue (c _ _ (specHom A B) (isQuasiFiniteSyntomic_specHom A B)) (topAffine _)
    (topAffine _) (specHom_top A B) G₀
  have h2 := hc.2 _ _ _ _ (specHom A B) (specHom A' B') (isQuasiFiniteSyntomic_specHom A B)
    (isQuasiFiniteSyntomic_specHom A' B') (OpenBaseChangeSquare.ofSpec D) (topAffine _)
    (topAffine _) (topAffine _) (topAffine _) (specHom_top A B) (ofSpec_hU'U D)
    (specHom_top A' B') (ofSpec_hV'V D) (specSquareCBC D) G₀ G₀'
  have e1 := pullbackTate_comp (specCBCInv A B) D (D.comp (specCBCInv A B)) cv G G'
  have e2 := pullbackTate_comp (specSquareCBC D) (specCBCInv A' B') (D.comp (specCBCInv A B))
    cv G₀' G'
  show pullbackTate (specCBCInv A' B') (chartValue (c _ _ (specHom A' B')
      (isQuasiFiniteSyntomic_specHom A' B')) (topAffine _) (topAffine _) (specHom_top A' B') G₀')
      G' = pullbackTate D (pullbackTate (specCBCInv A B) cv G) G'
  rw [← h2, ← e2, e1]

/-- **A rule with the two properties is the classified Tate map on every classified chart.** If
`c` satisfies both properties of Stacks 0FKD, then on an affine chart `(U, V)` of `f` which is a
chart base change of a quasi-finite basic universal chart, the value of `c` is the pullback of
the Tate map of the universal chart. -/
theorem chartValue_eq_tateOf_of_isTateRule (c : TateRule.{u}) (hc : IsTateRuleOnCharts c)
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] (f : Y ⟶ X) (hf : IsQuasiFiniteSyntomic f)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) {n d : ℕ} [NeZero d]
    (k : MvPolynomial (Fin n) (univBase.{u} n d))
    [Algebra.QuasiFinite (univBase.{u} n d) (univChart n d k)] :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    haveI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    haveI := algebra_syntomic_appLE hf.2 U V hVU
    ∀ (instR : Algebra (univBase.{u} n d) Γ(X, U.1)) (instC : Algebra (univChart n d k) Γ(Y, V.1))
      (D : ChartBaseChange (univBase.{u} n d) (univChart n d k) Γ(X, U.1) Γ(Y, V.1))
      (F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1)),
      chartValue (c X Y f hf) U V hVU F = tateOf k instR instC D F := by
  intro instR instC D F
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have := algebra_syntomic_appLE hf.2 U V hVU
  have := AlgebraicGeometry.quasiFinite_appLE hf.1 U V hVU
  rw [chartValue_eq_ringValue c hc f hf U V hVU F,
    ringValue_pullback c hc D (nonempty_finiteOpenFactorization (A := univBase.{u} n d)
      (B := univChart n d k)).some F, ringValue_univ c hc n d k]
  rfl

end Steps

/-! ### Uniqueness -/

/-- An isomorphism `det(NL_{Y/X}) ≅ ω_{Y/X}` is determined, on the sections over an affine
chart, by its chart value. -/
theorem app_eq_of_chartValue_eq {X Y : Scheme.{u}} [IsLocallyNoetherian X] {f : Y ⟶ X}
    {hf : IsQuasiFiniteSyntomic f} (c c' : detNL f hf ≅ omega f hf) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (F : letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
      FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1))
    (h : chartValue c U V hVU F = chartValue c' U V hVU F) (s : Γ(detNL f hf, V.1)) :
    c.hom.app V.1 s = c'.hom.app V.1 s := by
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  have := algebra_syntomic_appLE hf.2 U V hVU
  let := isLocallyNoetherian_source f hf
  let := hf.1
  have h1 := LinearEquiv.congr_fun h (detNLChartEquiv f hf U V hVU s)
  simp only [chartValue, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    sectionsLinearEquiv_of_iso_apply] at h1
  exact ((omegaData f hf).localEquiv U V hVU F).injective h1

/-- **Uniqueness of the Tate rule.** Two rules with the two properties of Stacks 0FKD agree. -/
theorem eq_of_isTateRule (c c' : TateRule.{u}) (hc : IsTateRuleOnCharts c)
    (hc' : IsTateRuleOnCharts c') : c = c' := by
  funext X Y _ f hf
  refine Iso.ext (hom_ext_of_basis (fun κ : ClassifiedChart f ↦ κ.source.1)
    (fun W x hx ↦ exists_classifiedChart f hf W x hx) _ _ fun κ s ↦ ?_)
  let : Algebra Γ(X, κ.base.1) Γ(Y, κ.source.1) :=
    (f.appLE κ.base κ.source κ.source_le).hom.toAlgebra
  have := κ.neZero
  have := κ.quasiFinite
  refine app_eq_of_chartValue_eq _ _ κ.base κ.source κ.source_le (classifiedFact f hf κ) ?_ s
  exact (chartValue_eq_tateOf_of_isTateRule c hc f hf κ.base κ.source κ.source_le κ.k κ.instR
    κ.instC κ.data (classifiedFact f hf κ)).trans
      (chartValue_eq_tateOf_of_isTateRule c' hc' f hf κ.base κ.source κ.source_le κ.k κ.instR
        κ.instC κ.data (classifiedFact f hf κ)).symm

end AlgebraicGeometry.TateMap
