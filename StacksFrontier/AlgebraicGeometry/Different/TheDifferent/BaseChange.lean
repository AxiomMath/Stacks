module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.DualizingModulesQuasi.FlatAlgebraBaseChange
public import StacksFrontier.AlgebraicGeometry.Different.NoetherDifferent.PairingIndependence
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.NoetherComparison
public import StacksFrontier.AlgebraicGeometry.Discriminant.BaseLocalization
public import StacksFrontier.AlgebraicGeometry.Discriminant.TraceElementUnique
public import StacksFrontier.RingTheory.Ideal.Annihilator.QuotientSpanBaseChange
public import StacksFrontier.RingTheory.TraceElement.BaseChange
public import StacksFrontier.RingTheory.TraceElement.TargetLocalization

/-!
# Base change of the different

Let `f : Y ⟶ X` be a flat locally quasi-finite morphism of locally Noetherian schemes and let
`g : X' ⟶ X` be arbitrary, with `Y' = X' ×_X Y` and `f' : Y' ⟶ X'` the base change of `f`. Let
`R ⊆ Y` and `R' ⊆ Y'` be the closed subschemes cut out by the differents `𝔇_f` and `𝔇_{f'}`.
This file proves [Stacks, Tag 0BW7]: the projection `Y' → Y` induces a bijective closed
immersion `R' → R ×_Y Y'`, which is an isomorphism when `g` is flat and also when `ω_{Y/X}` is
invertible.

## Main definitions

* `Stacks.Discriminant.differentIdealSheaf`: the different, read as ideal-sheaf data on the
  source.

## Main results

* `Stacks.Discriminant.different_sections_eq_cokerSpanIdeal`: on an affine chart the different
  is `Ann_B(ω_{B/A} / B τ_{B/A})`.
* `Stacks.Discriminant.differentIdealSheaf_comap_le` and
  `Stacks.Discriminant.differentIdealSheaf_support_comap`: the inverse image of `𝔇_f` is
  contained in `𝔇_{f'}` and the two cut out the same closed subset of `Y'`.
* `Stacks.Discriminant.differentIdealSheaf_comap_eq_of_flat` and
  `Stacks.Discriminant.differentIdealSheaf_comap_eq_of_invertible`: the inclusion is an equality
  if `g` is flat, resp. if `ω_{Y/X}` is invertible.
* `Stacks.Discriminant.exists_bijectiveClosedImmersion_different_baseChange`: the bijective
  closed immersion `R' → R ×_Y Y'` of the tag.
* `Stacks.Discriminant.isIso_different_baseChange_of_flat` and
  `Stacks.Discriminant.isIso_different_baseChange_of_invertible`: that closed immersion is an
  isomorphism, i.e. `R' = R ×_Y Y'`, under the two hypotheses of the tag.

## Implementation notes

As in `StacksFrontier.AlgebraicGeometry.Different.TheDifferent.Basic`, the relative dualizing
module of Tag 0BVG and its trace element of Tag 0BVJ are taken as data, namely a
`Stacks.Discriminant.RelativeDualizingModuleData` together with a
`Stacks.Discriminant.RelativeTraceSection`; the sheaf itself is not constructed anywhere in this
library. Both `f` and `f'` therefore carry their own such data, and no compatibility between the
two is assumed: the chart identifications of the data pin the sections over every affine chart
to the algebraic relative dualizing module of that chart, and the trace-section condition pins
the trace element there by the uniqueness of Tag 0BT7, so the comparison of the two differents
is forced.

`R` and `R'` are not constructed either: the hypothesis on a closed immersion `i : R ⟶ Y` is
`i.ker = differentIdealSheaf ω τ`, i.e. that `R` is the closed subscheme of `Y` cut out by the
different. `AlgebraicGeometry.Scheme.IdealSheafData.subschemeι` of `differentIdealSheaf ω τ`
satisfies it, by `AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι`.

Invertibility of `ω_{Y/X}` is spelled as invertibility of the module of sections over every
affine open of `Y`. For a quasi-coherent module that is the same condition as being an
invertible sheaf, since over an affine open the sheaf is the tilde of its sections.

The commutative algebra is in
`StacksFrontier.RingTheory.Ideal.Annihilator.QuotientSpanBaseChange`: the different of a chart
is the ideal `Stacks.Annihilator.cokerSpanIdeal` of the relative dualizing module and its trace
element, and all four assertions of the tag are the behaviour of that ideal under base change.
Tag 0BVF identifies `ω_{B'/A'}` with `B' ⊗_B ω_{B/A}` and Tag 0BT9 says the trace element
matches; the chart of `Y'` is identified with `Spec(A' ⊗_A B)` through
`AlgebraicGeometry.isIso_pushoutSection_of_isAffineOpen`.

## References

* [Stacks Project, Tag 0BW7](https://stacks.math.columbia.edu/tag/0BW7)
* [Stacks Project, Tag 0BVF](https://stacks.math.columbia.edu/tag/0BVF)
* [Stacks Project, Tag 0BT9](https://stacks.math.columbia.edu/tag/0BT9)
* [Stacks Project, Tag 0BT7](https://stacks.math.columbia.edu/tag/0BT7)
* [Stacks Project, Tag 00L2](https://stacks.math.columbia.edu/tag/00L2)
* [Stacks Project, Tag 0BUR](https://stacks.math.columbia.edu/tag/0BUR)
* [Stacks Project, Tag 07T8](https://stacks.math.columbia.edu/tag/07T8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open scoped AlgebraicGeometry TensorProduct

attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
  PresheafOfModules.presheaf TopCat.Sheaf structureSheafRing Scheme.Modules

universe u

namespace Stacks.Discriminant

open Stacks.Annihilator

attribute [local instance] algebraDualModule

/-! ### The different of a chart, algebraically -/

section AlgebraBaseChange

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- For an invertible relative dualizing module the chart different is the image of evaluation
at the trace element. -/
theorem range_eval_eq_cokerSpanIdeal {M : Type u} [AddCommGroup M] [Module B M]
    [Module.Invertible B M] (τ : M) :
    LinearMap.range (LinearMap.applyₗ (R := B) (M₂ := B) τ) = cokerSpanIdeal B τ := by
  refine SetLike.coe_injective ?_
  rw [cokerSpanIdeal_def, ← range_eval_eq_annihilator_quotient_span τ]
  rfl

/-- **Invertible case.** If `M` is an invertible `B`-module the ideal `Ann_B(M / Bτ)` extends to
the corresponding ideal of any base change. -/
theorem map_cokerSpanIdeal_eq_of_invertible {M : Type u} [AddCommGroup M] [Module B M]
    [Module.Invertible B M] (B₁ : Type u) [CommRing B₁] [Algebra B B₁] (τ : M) :
    Ideal.map (algebraMap B B₁) (cokerSpanIdeal B τ) =
      cokerSpanIdeal B₁ ((1 : B₁) ⊗ₜ[B] τ) := by
  refine le_antisymm (map_cokerSpanIdeal_le B₁ τ) ?_
  refine (cokerSpanIdeal_tmul_le_map_range_eval B₁ τ).trans ?_
  rw [range_eval_eq_cokerSpanIdeal]

variable [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat A B]
  [Algebra.FiniteType A B] [Algebra.QuasiFinite A B]

/-- **Tags 0BVF and 0BT9.** The relative dualizing module of the base-changed algebra, with its
trace element, is the base change of the relative dualizing module with `1 ⊗ τ_{B/A}`, so the
two cut out the same ideal. -/
theorem cokerSpanIdeal_traceElement_baseChange (F : FiniteOpenFactorization.{u, u, u} A B)
    (A₁ : Type u) [CommRing A₁] [Algebra A A₁] [IsNoetherianRing A₁] :
    letI : IsNoetherianRing (A₁ ⊗[A] B) := Algebra.FiniteType.isNoetherianRing A₁ _
    letI : Algebra B (A₁ ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    cokerSpanIdeal (A₁ ⊗[A] B)
        (dualizingModule.traceElement (FiniteOpenFactorization.baseChange F A₁)) =
      cokerSpanIdeal (A₁ ⊗[A] B)
        ((1 : A₁ ⊗[A] B) ⊗ₜ[B] dualizingModule.traceElement F) := by
  let : IsNoetherianRing (A₁ ⊗[A] B) := Algebra.FiniteType.isNoetherianRing A₁ _
  let : Algebra B (A₁ ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  let : Module B (dualizingModule (FiniteOpenFactorization.baseChange F A₁)) :=
    Module.compHom (M := dualizingModule (FiniteOpenFactorization.baseChange F A₁))
      (algebraMap B (A₁ ⊗[A] B))
  let : IsScalarTower B (A₁ ⊗[A] B)
      (dualizingModule (FiniteOpenFactorization.baseChange F A₁)) :=
    IsScalarTower.of_compHom B (A₁ ⊗[A] B) _
  refine (cokerSpanIdeal_congr (LinearEquiv.ofBijective
    (dualizingModule.baseChangeLinearMap F A₁)
    (dualizingModule.baseChangeLinearMap_bijective F A₁)) ?_).symm
  change dualizingModule.baseChangeLinearMap F A₁
    (1 ⊗ₜ[B] dualizingModule.traceElement F) = _
  rw [dualizingModule.baseChangeLinearMap_one_tmul]
  exact eq_traceElement_of_isTraceElement (FiniteOpenFactorization.baseChange F A₁)
    (isTraceElement_baseChange F A₁ _ (isTraceElement_traceElement F))

end AlgebraBaseChange

/-! ### The chart different under a ring isomorphism -/

section AlgebraTransport

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B]
  [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
  [Module.Flat A B] [Algebra.QuasiFinite A B]

/-- Localizing the target away from an element extends the chart different to the chart
different of the localization. -/
theorem map_cokerSpanIdeal_traceElement_of_isLocalizationAway [Algebra B C] [Algebra A C]
    [IsScalarTower A B C] [Module.Flat A C] [Algebra.QuasiFinite A C] (b : B)
    [IsLocalization.Away b C] (F : FiniteOpenFactorization.{u, u, u} A B)
    (G : FiniteOpenFactorization.{u, u, u} A C) :
    Ideal.map (algebraMap B C) (cokerSpanIdeal B (dualizingModule.traceElement F)) =
      cokerSpanIdeal C (dualizingModule.traceElement G) := by
  have : Module.Finite B (dualizingModule F) := dualizingModule_finite F
  have : Module.Flat B C := IsLocalization.flat C (Submonoid.powers b)
  have hl : IsLocalizedModule (Submonoid.powers b)
      (TensorProduct.mk B C (dualizingModule F) 1) := inferInstance
  have ht : (localizedModule_dualizingModule_equiv b F G
        (TensorProduct.mk B C (dualizingModule F) 1) hl)
      ((TensorProduct.mk B C (dualizingModule F) 1) (dualizingModule.traceElement F)) =
      dualizingModule.traceElement G :=
    eq_traceElement_of_isTraceElement G
      (isTraceElement_localization b F G _ hl (isTraceElement_traceElement F))
  exact (map_cokerSpanIdeal_eq_of_flat C (dualizingModule.traceElement F)).trans
    (cokerSpanIdeal_congr _ ht)

/-- An isomorphism of target algebras carries the chart different to the chart different. -/
theorem map_cokerSpanIdeal_traceElement_of_algEquiv [Algebra A C] [Module.Flat A C]
    [Algebra.QuasiFinite A C] (e : B ≃ₐ[A] C) (F : FiniteOpenFactorization.{u, u, u} A B)
    (G : FiniteOpenFactorization.{u, u, u} A C) :
    Ideal.map e.toRingHom (cokerSpanIdeal B (dualizingModule.traceElement F)) =
      cokerSpanIdeal C (dualizingModule.traceElement G) := by
  let : Algebra B C := e.toRingHom.toAlgebra
  have : IsScalarTower A B C :=
    IsScalarTower.of_algebraMap_eq' (by ext a; exact (e.commutes a).symm)
  have : IsLocalization.Away (1 : B) C :=
    IsLocalization.away_of_isUnit_of_bijective C isUnit_one e.bijective
  exact map_cokerSpanIdeal_traceElement_of_isLocalizationAway (1 : B) F G

end AlgebraTransport

/-! ### The chart different of a base-changed algebra -/

section ChartComparison

variable {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra A B] [Algebra A A'] [Algebra A' B']
  [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing A'] [IsNoetherianRing B']
  [Module.Flat A B] [Algebra.FiniteType A B] [Algebra.QuasiFinite A B]
  [Module.Flat A' B'] [Algebra.QuasiFinite A' B']

/-- The three assertions of [Stacks, Tag 0BW7] on a chart: for a cocartesian square of
Noetherian rings with `A → B` flat and quasi-finite, the chart different of `A' → B'` contains
the extension of the chart different of `A → B`, the two cut out the same closed subset of
`Spec B'`, and they agree when `A → A'` is flat or when `ω_{B/A}` is invertible. -/
theorem cokerSpanIdeal_traceElement_pushout (e : (A' ⊗[A] B) ≃ₐ[A'] B') (φ : B →+* B')
    (he : ∀ b : B, e ((1 : A') ⊗ₜ[A] b) = φ b)
    (F : FiniteOpenFactorization.{u, u, u} A B) (G : FiniteOpenFactorization.{u, u, u} A' B') :
    Ideal.map φ (cokerSpanIdeal B (dualizingModule.traceElement F)) ≤
        cokerSpanIdeal B' (dualizingModule.traceElement G) ∧
      PrimeSpectrum.zeroLocus (cokerSpanIdeal B' (dualizingModule.traceElement G) : Set B') =
        PrimeSpectrum.comap φ ⁻¹'
          PrimeSpectrum.zeroLocus
            (cokerSpanIdeal B (dualizingModule.traceElement F) : Set B) ∧
      ((Module.Flat A A' ∨ Module.Invertible B (dualizingModule F)) →
        Ideal.map φ (cokerSpanIdeal B (dualizingModule.traceElement F)) =
          cokerSpanIdeal B' (dualizingModule.traceElement G)) := by
  let : IsNoetherianRing (A' ⊗[A] B) := Algebra.FiniteType.isNoetherianRing A' _
  let : Algebra B (A' ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  have hfin : Module.Finite B (dualizingModule F) := dualizingModule_finite F
  set F' := FiniteOpenFactorization.baseChange F A' with hF'
  have hG : cokerSpanIdeal B' (dualizingModule.traceElement G) =
      Ideal.map e.toRingHom (cokerSpanIdeal (A' ⊗[A] B)
        ((1 : A' ⊗[A] B) ⊗ₜ[B] dualizingModule.traceElement F)) :=
    (map_cokerSpanIdeal_traceElement_of_algEquiv e F' G).symm.trans
      (by rw [cokerSpanIdeal_traceElement_baseChange F A'])
  have hcomp : e.toRingHom.comp (algebraMap B (A' ⊗[A] B)) = φ := RingHom.ext he
  have hmap : Ideal.map φ (cokerSpanIdeal B (dualizingModule.traceElement F)) =
      Ideal.map e.toRingHom (Ideal.map (algebraMap B (A' ⊗[A] B))
        (cokerSpanIdeal B (dualizingModule.traceElement F))) := by
    rw [Ideal.map_map, hcomp]
  refine ⟨?_, ?_, ?_⟩
  · rw [hG, hmap]
    exact Ideal.map_mono (map_cokerSpanIdeal_le _ _)
  · have hz : ∀ J : Ideal (A' ⊗[A] B),
        PrimeSpectrum.zeroLocus (Ideal.map e.toRingHom J : Set B') =
          PrimeSpectrum.comap e.toRingHom ⁻¹'
            PrimeSpectrum.zeroLocus (J : Set (A' ⊗[A] B)) :=
      fun J ↦ Set.ext fun _ ↦ Ideal.map_le_iff_le_comap
    rw [hG, hz, zeroLocus_cokerSpanIdeal_tmul, ← Set.preimage_comp,
      ← PrimeSpectrum.comap_comp, hcomp]
  · rintro (hflat | hinv)
    · have : Module.Flat B (A' ⊗[A] B) := Module.Flat.of_linearEquiv
        (Algebra.TensorProduct.commRight A B A').symm.toLinearEquiv
      rw [hG, hmap,
        map_cokerSpanIdeal_eq_of_flat (A' ⊗[A] B) (dualizingModule.traceElement F)]
    · rw [hG, hmap,
        map_cokerSpanIdeal_eq_of_invertible (A' ⊗[A] B) (dualizingModule.traceElement F)]

end ChartComparison

/-! ### The different on an affine chart -/

section Chart

variable {X Y : Scheme.{u}} {f : Y ⟶ X}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Flat f] [LocallyQuasiFinite f]

open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

/-- The ideal of sections of the different over an affine chart `V = Spec B` lying over an
affine open `U = Spec A` of the base is `Ann_B(ω_{B/A} / B τ_{B/A})`. -/
theorem different_sections_eq_cokerSpanIdeal (ω : RelativeDualizingModuleData f)
    (τ : RelativeTraceSection ω) (U : X.affineOpens) (V : Y.affineOpens)
    (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    letI : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
    letI : Module.Flat Γ(X, U.1) Γ(Y, V.1) :=
      RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hVU)
    letI : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
      RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
    ∀ F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1),
      (show Ideal Γ(Y, V.1) from (different ω τ).toSubmodule.obj (op V.1)) =
        cokerSpanIdeal Γ(Y, V.1) (dualizingModule.traceElement F) := by
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
  let : Module.Flat Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hVU)
  let : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
  intro F
  let := moduleOfLE ω.sheaf (show V.1 ≤ ⊤ from le_top)
  have hsect : ω.localEquiv U V hVU F ((traceHom ω τ).app V.1 (1 : Γ(Y, V.1))) =
      dualizingModule.traceElement F := by
    have happ : (traceHom ω τ).app V.1 (1 : Γ(Y, V.1)) =
        restrictₗ ω.sheaf (show V.1 ≤ ⊤ from le_top) τ.sect :=
      traceMorphism_app_one ω τ V.1
    rw [happ]
    exact eq_traceElement_of_isTraceElement F (τ.isTraceElement_localEquiv U V hVU F)
  rw [different_sections_eq_annihilator ω τ V, ← (cokernelSectionsEquiv ω τ V).annihilator_eq]
  exact cokerSpanIdeal_congr (ω.localEquiv U V hVU F) hsect

/-- The different, read as ideal-sheaf data on the source: the annihilator ideal sheaf of the
cokernel of the trace morphism. -/
def differentIdealSheaf (ω : RelativeDualizingModuleData f) (τ : RelativeTraceSection ω) :
    Y.IdealSheafData :=
  haveI := isCoherent_traceCoker ω τ
  haveI hqf := Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
    (traceCoker ω τ)
  haveI := hqf.1
  haveI := hqf.2
  annihilatorIdeal' (traceCoker ω τ)

/-- The ideal-sheaf data of the different has the sections of the different as its ideals. -/
theorem differentIdealSheaf_ideal (ω : RelativeDualizingModuleData f)
    (τ : RelativeTraceSection ω) (V : Y.affineOpens) :
    (differentIdealSheaf ω τ).ideal V =
      (show Ideal Γ(Y, V.1) from (different ω τ).toSubmodule.obj (op V.1)) := by
  have := isCoherent_traceCoker ω τ
  have hqf := Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
    (traceCoker ω τ)
  have := hqf.1
  have := hqf.2
  rw [different_sections_eq_annihilator ω τ V]
  exact annihilatorIdeal_ideal (traceCoker ω τ) V

/-- The ideals of the different on an affine chart, in algebraic terms. -/
theorem differentIdealSheaf_ideal_eq_cokerSpanIdeal (ω : RelativeDualizingModuleData f)
    (τ : RelativeTraceSection ω) (U : X.affineOpens) (V : Y.affineOpens)
    (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    letI : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
    letI : Module.Flat Γ(X, U.1) Γ(Y, V.1) :=
      RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hVU)
    letI : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
      RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
    ∀ F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1),
      (differentIdealSheaf ω τ).ideal V =
        cokerSpanIdeal Γ(Y, V.1) (dualizingModule.traceElement F) := by
  intro F
  rw [differentIdealSheaf_ideal ω τ V]
  exact different_sections_eq_cokerSpanIdeal ω τ U V hVU F

/-- The kernel of the closed immersion of the closed subscheme of `Y` cut out by the different
is the different. -/
theorem ker_subschemeι_differentIdealSheaf (ω : RelativeDualizingModuleData f)
    (τ : RelativeTraceSection ω) :
    (differentIdealSheaf ω τ).subschemeι.ker = differentIdealSheaf ω τ :=
  Scheme.IdealSheafData.ker_subschemeι _

end Chart

/-! ### Ideal sheaves, inverse images and affine charts -/

section Gluing

/-- In a cocartesian square of commutative rings whose left map is surjective, the kernel of the
right map is the extension of the kernel of the left one. -/
theorem ker_eq_map_of_isPushout {A B C D : CommRingCat.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {inl : B ⟶ D} {inr : C ⟶ D} (h : IsPushout f g inl inr)
    (hf : Function.Surjective f.hom) :
    RingHom.ker inr.hom = Ideal.map g.hom (RingHom.ker f.hom) := by
  set J := Ideal.map g.hom (RingHom.ker f.hom) with hJ
  have hle : J ≤ RingHom.ker inr.hom := by
    rw [hJ, Ideal.map_le_iff_le_comap]
    intro a ha
    change inr.hom (g.hom a) = 0
    rw [show inr.hom (g.hom a) = inl.hom (f.hom a) from
      congrArg (fun b : A ⟶ D ↦ b.hom a) h.w.symm, show f.hom a = 0 from ha, map_zero]
  refine le_antisymm (fun c hc ↦ ?_) hle
  set q := Ideal.Quotient.mk J with hq
  set b : B →+* C ⧸ J := (RingHom.liftOfSurjective f.hom hf) ⟨q.comp g.hom, by
    intro a ha
    change q (g.hom a) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha)⟩ with hb
  have hbw : f ≫ CommRingCat.ofHom b = g ≫ CommRingCat.ofHom q := by
    refine CommRingCat.hom_ext ?_
    exact congrArg Subtype.val ((RingHom.liftOfSurjective f.hom hf).symm_apply_apply _)
  set d : D ⟶ CommRingCat.of (C ⧸ J) :=
    h.isColimit.desc (PushoutCocone.mk (CommRingCat.ofHom b) (CommRingCat.ofHom q) hbw) with hdd
  have hd : inr ≫ d = CommRingCat.ofHom q := h.isColimit.fac _ .right
  have hdc : d.hom (inr.hom c) = q c :=
    congrArg (fun a : C ⟶ CommRingCat.of (C ⧸ J) ↦ a.hom c) hd
  refine Ideal.Quotient.eq_zero_iff_mem.mp ?_
  change q c = 0
  rw [← hdc, show inr.hom c = 0 from hc, map_zero]

/-- The ideals of the inverse image of an ideal sheaf on an affine chart of the source lying
over an affine chart of the target: the extension of the ideal along the chart ring map. -/
theorem ideal_comap_affine {X Y : Scheme.{u}} (I : Y.IdealSheafData) (p : X ⟶ Y)
    (V : Y.affineOpens) (W : X.affineOpens) (hWV : W.1 ≤ p ⁻¹ᵁ V.1) :
    (I.comap p).ideal W = Ideal.map (p.appLE V W hWV).hom (I.ideal V) := by
  set j := I.subschemeι with hj
  have hW : pullback.fst p j ⁻¹ᵁ W.1 =
      pullback.snd p j ⁻¹ᵁ (j ⁻¹ᵁ V.1) ⊓ pullback.fst p j ⁻¹ᵁ W.1 := by
    refine le_antisymm (le_inf (fun z hz ↦ ?_) le_rfl) inf_le_right
    change j ((pullback.snd p j) z) ∈ V.1
    rw [← show p ((pullback.fst p j) z) = j ((pullback.snd p j) z) from
      congrArg (fun a : pullback p j ⟶ Y ↦ a z) (pullback.condition (f := p) (g := j))]
    exact hWV hz
  have hpo := (isIso_pushoutSection_iff (IsPullback.of_hasPullback p j).flip hWV le_rfl hW).mp
    (isIso_pushoutSection_of_isAffineOpen (IsPullback.of_hasPullback p j).flip hWV le_rfl hW
      V.2 W.2 (V.2.preimage j))
  simp only [Scheme.Hom.appLE_eq_app] at hpo
  have hk := ker_eq_map_of_isPushout hpo (j.app_surjective V.1 V.2)
  rw [Scheme.IdealSheafData.comap, Scheme.Hom.ker_apply]
  rwa [show RingHom.ker (j.app V.1).hom = I.ideal V by
    rw [← Scheme.Hom.ker_apply, Scheme.IdealSheafData.ker_subschemeι]] at hk

/-- Containment of ideal sheaves is local: it suffices to exhibit, around every point, one
affine open on which the ideals are contained. -/
theorem idealSheaf_le_of_affine_neighborhoods {Y : Scheme.{u}} {I J : Y.IdealSheafData}
    (h : ∀ y : Y, ∃ V : Y.affineOpens, y ∈ V.1 ∧ I.ideal V ≤ J.ideal V) : I ≤ J := by
  choose V hy hV using h
  exact Scheme.IdealSheafData.le_of_iSup_eq_top V
    (top_le_iff.mp fun y _ ↦ Opens.mem_iSup.mpr ⟨y, hy y⟩) hV

/-- Membership in the support of an ideal sheaf, tested on an affine chart. -/
theorem mem_support_iff_primeIdealOf {Y : Scheme.{u}} (I : Y.IdealSheafData)
    (V : Y.affineOpens) (y : Y) (hy : y ∈ V.1) :
    y ∈ I.support ↔
      V.2.primeIdealOf ⟨y, hy⟩ ∈ PrimeSpectrum.zeroLocus (I.ideal V : Set Γ(Y, V.1)) := by
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hy, ← V.2.fromSpec_preimage_zeroLocus]
  change y ∈ Y.zeroLocus (U := V.1) (I.ideal V : Set Γ(Y, V.1)) ↔
    V.2.fromSpec (V.2.primeIdealOf ⟨y, hy⟩) ∈
      Y.zeroLocus (U := V.1) (I.ideal V : Set Γ(Y, V.1))
  rw [V.2.fromSpec_primeIdealOf]

/-- Every point of a scheme lies in an affine open contained in a given open neighbourhood. -/
theorem exists_affine_subset {Y : Scheme.{u}} (y : Y) (O : Y.Opens) (hy : y ∈ O) :
    ∃ V : Y.affineOpens, y ∈ V.1 ∧ V.1 ≤ O := by
  obtain ⟨-, ⟨V, hV, rfl⟩, hyV, hVO⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hy O.isOpen
  exact ⟨⟨V, hV⟩, hyV, hVO⟩

/-- Around every point of a fibre product there is a cocartesian square of affine charts: an
affine open `U` of the base, affine opens `V` over `U` in one factor and `U'` over `U` in the
other, and the affine open of the fibre product they cut out. -/
theorem exists_affine_pullback_chart {X X' Y : Scheme.{u}} (f : Y ⟶ X) (g : X' ⟶ X)
    (z : (pullback f g : Scheme.{u})) :
    ∃ (U : X.affineOpens) (V : Y.affineOpens) (U' : X'.affineOpens)
      (_ : V.1 ≤ f ⁻¹ᵁ U.1) (_ : U'.1 ≤ g ⁻¹ᵁ U.1) (W : (pullback f g).affineOpens),
      W.1 = pullback.fst f g ⁻¹ᵁ V.1 ⊓ pullback.snd f g ⁻¹ᵁ U'.1 ∧ z ∈ W.1 := by
  obtain ⟨U, hzU, -⟩ := exists_affine_subset (f ((pullback.fst f g) z)) ⊤ trivial
  obtain ⟨V, hzV, hV⟩ := exists_affine_subset ((pullback.fst f g) z) (f ⁻¹ᵁ U.1) hzU
  have hzU' : (pullback.snd f g) z ∈ g ⁻¹ᵁ U.1 := by
    change g ((pullback.snd f g) z) ∈ U.1
    rw [← show f ((pullback.fst f g) z) = g ((pullback.snd f g) z) from
      congrArg (fun a : pullback f g ⟶ X ↦ a z) (pullback.condition (f := f) (g := g))]
    exact hzU
  obtain ⟨U', hzU'mem, hU'⟩ := exists_affine_subset ((pullback.snd f g) z) (g ⁻¹ᵁ U.1) hzU'
  have : IsAffine U.1.toScheme := U.2
  have : IsAffine V.1.toScheme := V.2
  have : IsAffine U'.1.toScheme := U'.2
  have hO : IsAffineOpen (pullback.fst f g ⁻¹ᵁ V.1 ⊓ pullback.snd f g ⁻¹ᵁ U'.1) :=
    IsAffine.of_isIso (Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback f g) hU' hV
      (show pullback.fst f g ⁻¹ᵁ V.1 ⊓ pullback.snd f g ⁻¹ᵁ U'.1 = _ from rfl)).isoPullback.hom
  exact ⟨U, V, U', hV, hU', ⟨_, hO⟩, rfl, ⟨hzV, hzU'mem⟩⟩

end Gluing

/-! ### The base change of the different -/

section BaseChange

variable {X X' Y : Scheme.{u}} (f : Y ⟶ X) (g : X' ⟶ X)
  [IsLocallyNoetherian X] [IsLocallyNoetherian X'] [IsLocallyNoetherian Y]
  [Flat f] [LocallyOfFiniteType f] [LocallyQuasiFinite f]

/-- The chart comparison of [Stacks, Tag 0BW7], for a cocartesian square of affine charts of a
cartesian square of schemes. -/
theorem differentIdealSheaf_ideal_pullback_chart (ω : RelativeDualizingModuleData f)
    (τ : RelativeTraceSection ω)
    (ω' : RelativeDualizingModuleData (pullback.snd f g))
    (τ' : RelativeTraceSection ω')
    (U : X.affineOpens) (V : Y.affineOpens) (U' : X'.affineOpens)
    (hV : V.1 ≤ f ⁻¹ᵁ U.1) (hU' : U'.1 ≤ g ⁻¹ᵁ U.1) (W : (pullback f g).affineOpens)
    (hW : W.1 = pullback.fst f g ⁻¹ᵁ V.1 ⊓ pullback.snd f g ⁻¹ᵁ U'.1) :
    Ideal.map ((pullback.fst f g).appLE V W (hW.le.trans inf_le_left)).hom
        ((differentIdealSheaf ω τ).ideal V) ≤
        (differentIdealSheaf ω' τ').ideal W ∧
      PrimeSpectrum.zeroLocus
          ((differentIdealSheaf ω' τ').ideal W : Set Γ(pullback f g, W.1)) =
        PrimeSpectrum.comap ((pullback.fst f g).appLE V W (hW.le.trans inf_le_left)).hom ⁻¹'
          PrimeSpectrum.zeroLocus ((differentIdealSheaf ω τ).ideal V : Set Γ(Y, V.1)) ∧
      ((Flat g ∨ Module.Invertible Γ(Y, V.1) Γ(ω.sheaf, V.1)) →
        Ideal.map ((pullback.fst f g).appLE V W (hW.le.trans inf_le_left)).hom
            ((differentIdealSheaf ω τ).ideal V) =
          (differentIdealSheaf ω' τ').ideal W) := by
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hV).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(X', U'.1) := (g.appLE U U' hU').hom.toAlgebra
  let : Algebra Γ(Y, V.1) Γ(pullback f g, W.1) :=
    ((pullback.fst f g).appLE V W (hW.le.trans inf_le_left)).hom.toAlgebra
  let : Algebra Γ(X', U'.1) Γ(pullback f g, W.1) :=
    ((pullback.snd f g).appLE U' W (hW.le.trans inf_le_right)).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(pullback f g, W.1) :=
    ((algebraMap Γ(Y, V.1) Γ(pullback f g, W.1)).comp
      (algebraMap Γ(X, U.1) Γ(Y, V.1))).toAlgebra
  have : IsScalarTower Γ(X, U.1) Γ(Y, V.1) Γ(pullback f g, W.1) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hpo := (isIso_pushoutSection_iff (IsPullback.of_hasPullback f g) hU' hV hW).mp
    (isIso_pushoutSection_of_isAffineOpen (IsPullback.of_hasPullback f g) hU' hV hW
      U.2 U'.2 V.2)
  have : IsScalarTower Γ(X, U.1) Γ(X', U'.1) Γ(pullback f g, W.1) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hpo.w)
  have : Algebra.IsPushout Γ(X, U.1) Γ(X', U'.1) Γ(Y, V.1) Γ(pullback f g, W.1) :=
    CommRingCat.isPushout_iff_isPushout.mp hpo.flip
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
  have : IsNoetherianRing Γ(X', U'.1) := IsLocallyNoetherian.component_noetherian U'
  have : IsNoetherianRing Γ(pullback f g, W.1) :=
    IsLocallyNoetherian.component_noetherian W
  have : Module.Flat Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hV)
  have : Algebra.FiniteType Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.finiteType_algebraMap.mp (f.finiteType_appLE U.2 V.2 hV)
  have : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hV)
  have : Module.Flat Γ(X', U'.1) Γ(pullback f g, W.1) :=
    RingHom.flat_algebraMap_iff.mp
      ((pullback.snd f g).flat_appLE U'.2 W.2 (hW.le.trans inf_le_right))
  have : Algebra.QuasiFinite Γ(X', U'.1) Γ(pullback f g, W.1) :=
    RingHom.quasiFinite_algebraMap.mp
      (LocallyQuasiFinite.quasiFinite_appLE U'.2 W.2 (hW.le.trans inf_le_right))
  obtain ⟨F⟩ := ω.factorization U V hV
  obtain ⟨G⟩ := ω'.factorization U' W (hW.le.trans inf_le_right)
  have h := cokerSpanIdeal_traceElement_pushout
    (Algebra.IsPushout.equiv Γ(X, U.1) Γ(X', U'.1) Γ(Y, V.1) Γ(pullback f g, W.1))
    (algebraMap Γ(Y, V.1) Γ(pullback f g, W.1))
    (fun b ↦ by simp [Algebra.IsPushout.equiv_tmul]) F G
  rw [differentIdealSheaf_ideal_eq_cokerSpanIdeal ω τ U V hV F,
    differentIdealSheaf_ideal_eq_cokerSpanIdeal ω' τ' U' W (hW.le.trans inf_le_right) G]
  refine ⟨h.1, h.2.1, fun hyp ↦ h.2.2 ?_⟩
  rcases hyp with hyp | hyp
  · exact Or.inl (RingHom.flat_algebraMap_iff.mp (g.flat_appLE U.2 U'.2 hU'))
  · exact Or.inr (Module.Invertible.congr (ω.localEquiv U V hV F))

/-- **[Stacks, Tag 0BW7], the closed immersion.** The inverse image of the different of `f` is
contained in the different of its base change. -/
theorem differentIdealSheaf_comap_le (ω : RelativeDualizingModuleData f)
    (τ : RelativeTraceSection ω) (ω' : RelativeDualizingModuleData (pullback.snd f g))
    (τ' : RelativeTraceSection ω') :
    (differentIdealSheaf ω τ).comap (pullback.fst f g) ≤ differentIdealSheaf ω' τ' := by
  refine idealSheaf_le_of_affine_neighborhoods fun z ↦ ?_
  obtain ⟨U, V, U', hV, hU', W, hW, hz⟩ := exists_affine_pullback_chart f g z
  refine ⟨W, hz, ?_⟩
  rw [ideal_comap_affine _ _ V W (hW.le.trans inf_le_left)]
  exact (differentIdealSheaf_ideal_pullback_chart f g ω τ ω' τ' U V U' hV hU' W hW).1

/-- **[Stacks, Tag 0BW7], bijectivity.** The different of the base change and the inverse image
of the different cut out the same closed subset of the base-changed source. -/
theorem differentIdealSheaf_support_comap (ω : RelativeDualizingModuleData f)
    (τ : RelativeTraceSection ω) (ω' : RelativeDualizingModuleData (pullback.snd f g))
    (τ' : RelativeTraceSection ω') :
    (differentIdealSheaf ω' τ').support =
      ((differentIdealSheaf ω τ).comap (pullback.fst f g)).support := by
  ext z
  obtain ⟨U, V, U', hV, hU', W, hW, hz⟩ := exists_affine_pullback_chart f g z
  change z ∈ (differentIdealSheaf ω' τ').support ↔
    z ∈ ((differentIdealSheaf ω τ).comap (pullback.fst f g)).support
  rw [mem_support_iff_primeIdealOf _ W z hz, mem_support_iff_primeIdealOf _ W z hz,
    ideal_comap_affine _ _ V W (hW.le.trans inf_le_left),
    (differentIdealSheaf_ideal_pullback_chart f g ω τ ω' τ' U V U' hV hU' W hW).2.1]
  exact Ideal.map_le_iff_le_comap.symm

/-- If on every affine chart of `Y` either `g` is flat or `ω_{Y/X}` is invertible, the different
of the base change is contained in the inverse image of the different of `f`. -/
private theorem differentIdealSheaf_le_comap_of_flat_or_invertible
    (ω : RelativeDualizingModuleData f) (τ : RelativeTraceSection ω)
    (ω' : RelativeDualizingModuleData (pullback.snd f g)) (τ' : RelativeTraceSection ω')
    (h : ∀ V : Y.affineOpens, Flat g ∨ Module.Invertible Γ(Y, V.1) Γ(ω.sheaf, V.1)) :
    differentIdealSheaf ω' τ' ≤ (differentIdealSheaf ω τ).comap (pullback.fst f g) := by
  refine idealSheaf_le_of_affine_neighborhoods fun z ↦ ?_
  obtain ⟨U, V, U', hV, hU', W, hW, hz⟩ := exists_affine_pullback_chart f g z
  refine ⟨W, hz, ?_⟩
  rw [ideal_comap_affine _ _ V W (hW.le.trans inf_le_left)]
  exact ((differentIdealSheaf_ideal_pullback_chart f g ω τ ω' τ' U V U' hV hU' W hW).2.2
    (h V)).ge

/-- **[Stacks, Tag 0BW7], flat base change.** If `g` is flat the inverse image of the different
of `f` is the different of the base change. -/
theorem differentIdealSheaf_comap_eq_of_flat [Flat g] (ω : RelativeDualizingModuleData f)
    (τ : RelativeTraceSection ω) (ω' : RelativeDualizingModuleData (pullback.snd f g))
    (τ' : RelativeTraceSection ω') :
    (differentIdealSheaf ω τ).comap (pullback.fst f g) = differentIdealSheaf ω' τ' := by
  exact le_antisymm (differentIdealSheaf_comap_le f g ω τ ω' τ')
    (differentIdealSheaf_le_comap_of_flat_or_invertible f g ω τ ω' τ' fun _ ↦ Or.inl ‹_›)

/-- **[Stacks, Tag 0BW7], invertible dualizing module.** If `ω_{Y/X}` is invertible the inverse
image of the different of `f` is the different of the base change, for an arbitrary `g`. -/
theorem differentIdealSheaf_comap_eq_of_invertible (ω : RelativeDualizingModuleData f)
    (τ : RelativeTraceSection ω) (ω' : RelativeDualizingModuleData (pullback.snd f g))
    (τ' : RelativeTraceSection ω')
    (hinv : ∀ V : Y.affineOpens, Module.Invertible Γ(Y, V.1) Γ(ω.sheaf, V.1)) :
    (differentIdealSheaf ω τ).comap (pullback.fst f g) = differentIdealSheaf ω' τ' := by
  exact le_antisymm (differentIdealSheaf_comap_le f g ω τ ω' τ')
    (differentIdealSheaf_le_comap_of_flat_or_invertible f g ω τ ω' τ' fun V ↦ Or.inr (hinv V))

end BaseChange

/-! ### The closed subschemes -/

section Subscheme

/-- The image of a closed immersion is the closed subset cut out by its kernel. -/
theorem closedImmersion_range_eq_support {R Y : Scheme.{u}} (i : R ⟶ Y)
    [IsClosedImmersion i] :
    Set.range i.base = (i.ker.support : Set Y) := by
  rw [Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq]

/-- A closed immersion whose kernel contains the inverse image of the kernel of another, with
the same support, factors through it by a bijective closed immersion into the fibre product. -/
theorem exists_bijectiveClosedImmersion_of_ker {Y Y' R R' : Scheme.{u}} (p : Y' ⟶ Y)
    (i : R ⟶ Y) (i' : R' ⟶ Y') [IsClosedImmersion i] [IsClosedImmersion i']
    (hle : i.ker.comap p ≤ i'.ker) (hsupp : i'.ker.support = (i.ker.comap p).support) :
    ∃ (k : R' ⟶ R) (hk : k ≫ i = i' ≫ p),
      IsClosedImmersion (pullback.lift k i' hk) ∧
        Function.Bijective (pullback.lift k i' hk).base := by
  have hle' : i.ker ≤ (i' ≫ p).ker := by
    rwa [Scheme.Hom.ker_comp, Scheme.IdealSheafData.le_map_iff_comap_le]
  set k := IsClosedImmersion.lift i (i' ≫ p) hle' with hkdef
  have hk : k ≫ i = i' ≫ p := IsClosedImmersion.lift_fac _ _ _
  have hj : pullback.lift k i' hk ≫ pullback.snd i p = i' := pullback.lift_snd _ _ _
  have : IsClosedImmersion (pullback.lift k i' hk ≫ pullback.snd i p) := by
    rw [hj]; infer_instance
  have : IsClosedImmersion (pullback.lift k i' hk) :=
    IsClosedImmersion.of_comp_isClosedImmersion _ (pullback.snd i p)
  refine ⟨k, hk, inferInstance, (pullback.lift k i' hk).isClosedEmbedding.injective, fun z ↦ ?_⟩
  have hz : (pullback.snd i p) z ∈ (i'.ker.support : Set Y') := by
    rw [hsupp, Scheme.IdealSheafData.support_comap]
    change p ((pullback.snd i p) z) ∈ i.ker.support
    rw [show p ((pullback.snd i p) z) = i ((pullback.fst i p) z) from
      congrArg (fun a : pullback i p ⟶ Y ↦ a z) (pullback.condition (f := i) (g := p)).symm]
    exact i.range_subset_ker_support (Set.mem_range_self _)
  rw [← closedImmersion_range_eq_support] at hz
  obtain ⟨r, hr⟩ := hz
  exact ⟨r, (pullback.snd i p).isClosedEmbedding.injective
    ((congrArg (fun a : R' ⟶ Y' ↦ a r) hj).trans hr)⟩

/-- If the kernels agree, the closed immersion into the fibre product is an isomorphism. -/
theorem isIso_pullbackLift_of_ker {Y Y' R R' : Scheme.{u}} (p : Y' ⟶ Y) (i : R ⟶ Y)
    (i' : R' ⟶ Y') [IsClosedImmersion i] [IsClosedImmersion i']
    (heq : i.ker.comap p = i'.ker) (k : R' ⟶ R) (hk : k ≫ i = i' ≫ p) :
    IsIso (pullback.lift k i' hk) := by
  refine IsClosedImmersion.isIso_of_ker_eq i' (pullback.snd i p) _
    (pullback.lift_snd k i' hk) ?_
  have hker : (pullback.snd i p).ker = i.ker.comap p := by
    rw [← Scheme.Hom.ker_comp_of_isIso (pullbackSymmetry p i).hom]
    simpa using Scheme.IdealSheafData.ker_fst_of_isClosedImmersion i p
  exact heq.symm.trans hker.symm

end Subscheme

/-! ### Tag 0BW7 -/

section Tag

variable {X X' Y : Scheme.{u}} (f : Y ⟶ X) (g : X' ⟶ X)
  [IsLocallyNoetherian X] [IsLocallyNoetherian X'] [IsLocallyNoetherian Y]
  [Flat f] [LocallyOfFiniteType f] [LocallyQuasiFinite f]

variable {R R' : Scheme.{u}} (ω : RelativeDualizingModuleData f) (τ : RelativeTraceSection ω)
  (ω' : RelativeDualizingModuleData (pullback.snd f g)) (τ' : RelativeTraceSection ω')
  (i : R ⟶ Y) (i' : R' ⟶ pullback f g) [IsClosedImmersion i] [IsClosedImmersion i']

/-- **[Stacks, Tag 0BW7].** Consider a cartesian diagram of locally Noetherian schemes with
`f : Y ⟶ X` flat and locally quasi-finite, let `R ⊆ Y` and `R' ⊆ Y'` be the closed subschemes
cut out by the differents `𝔇_f` and `𝔇_{f'}`. Then `Y' → Y` induces a bijective closed immersion
`R' → R ×_Y Y'`. -/
@[stacks 0BW7 "the bijective closed immersion"]
theorem exists_bijectiveClosedImmersion_different_baseChange
    (hi : i.ker = differentIdealSheaf ω τ) (hi' : i'.ker = differentIdealSheaf ω' τ') :
    ∃ (k : R' ⟶ R) (hk : k ≫ i = i' ≫ pullback.fst f g),
      IsClosedImmersion (pullback.lift k i' hk) ∧
        Function.Bijective (pullback.lift k i' hk).base := by
  refine exists_bijectiveClosedImmersion_of_ker (pullback.fst f g) i i' ?_ ?_ <;> rw [hi, hi']
  exacts [differentIdealSheaf_comap_le f g ω τ ω' τ',
    differentIdealSheaf_support_comap f g ω τ ω' τ']

/-- **[Stacks, Tag 0BW7], flat base change.** If moreover `g` is flat then `R' = R ×_Y Y'`. -/
@[stacks 0BW7 "equality under flat base change"]
theorem isIso_different_baseChange_of_flat [Flat g]
    (hi : i.ker = differentIdealSheaf ω τ) (hi' : i'.ker = differentIdealSheaf ω' τ')
    (k : R' ⟶ R) (hk : k ≫ i = i' ≫ pullback.fst f g) :
    IsIso (pullback.lift k i' hk) := by
  refine isIso_pullbackLift_of_ker (pullback.fst f g) i i' ?_ k hk
  rw [hi, hi']
  exact differentIdealSheaf_comap_eq_of_flat f g ω τ ω' τ'

/-- **[Stacks, Tag 0BW7], invertible dualizing module.** If moreover `ω_{Y/X}` is invertible
then `R' = R ×_Y Y'`, for an arbitrary `g`. -/
@[stacks 0BW7 "equality for invertible dualizing module"]
theorem isIso_different_baseChange_of_invertible
    (hinv : ∀ V : Y.affineOpens, Module.Invertible Γ(Y, V.1) Γ(ω.sheaf, V.1))
    (hi : i.ker = differentIdealSheaf ω τ) (hi' : i'.ker = differentIdealSheaf ω' τ')
    (k : R' ⟶ R) (hk : k ≫ i = i' ≫ pullback.fst f g) :
    IsIso (pullback.lift k i' hk) := by
  refine isIso_pullbackLift_of_ker (pullback.fst f g) i i' ?_ k hk
  rw [hi, hi']
  exact differentIdealSheaf_comap_eq_of_invertible f g ω τ ω' τ' hinv

end Tag

end Stacks.Discriminant

end
