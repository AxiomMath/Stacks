module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.Unramified.Locus
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.BaseChange
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.NormDiscriminant
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.EtaleAt
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Basic
public import StacksFrontier.RingTheory.Support.Fiber

/-!
# The different cuts out the ramification locus

Let `f : Y ⟶ X` be a flat locally quasi-finite morphism locally of finite type between locally
Noetherian schemes, with relative dualizing module `ω_{Y/X}` and trace element `τ_{Y/X}`.  The
closed subscheme `R ⊆ Y` defined by the different `𝔇_f` has as its underlying set exactly the
points at which `f` is not étale, equivalently at which `f` is not unramified.

## Main results

* `Stacks.Discriminant.zeroLocus_cokerSpanIdeal_traceElement`: for a flat quasi-finite algebra
  of finite type over a Noetherian ring, the primes containing `Ann_B(ω_{B/A} / B τ_{B/A})` are
  exactly the primes at which `B` is not unramified over `A`.
* `Stacks.Discriminant.mem_support_differentIdealSheaf_iff_not_etaleAt` and
  `Stacks.Discriminant.mem_support_differentIdealSheaf_iff_not_unramifiedAt`: the support of the
  different is the non-étale, equivalently the non-unramified, locus.
* `Stacks.Discriminant.range_eq_setOf_not_etaleAt` and
  `Stacks.Discriminant.range_eq_setOf_not_unramifiedAt`: the closed subscheme cut out by the
  different is that locus.
* `AlgebraicGeometry.unramifiedAt_iff_mem_unramifiedLocus`: unramifiedness at a point read on an
  affine chart, and `AlgebraicGeometry.etaleAt_iff_unramifiedAt`: a flat morphism locally of
  finite type over a locally Noetherian base is étale at a point exactly when it is unramified
  there.

## Implementation notes

The argument is the one of the source, carried out on affine charts rather than on the schemes.
On a chart `V = Spec B` over `U = Spec A` the different is the ideal
`Stacks.Annihilator.cokerSpanIdeal B τ_{B/A}` of
`StacksFrontier/AlgebraicGeometry/Different/TheDifferent/BaseChange.lean`, whose zero locus commutes
with base change; base changing to the residue field of a prime of `A` therefore reduces the
statement to the fibre, where the fibre ring is finite over a field.  The fibre of the
non-unramified locus is computed the same way, because `Ω_{B/A}` commutes with base change and
the unramified locus is the complement of the support of `Ω_{B/A}`.

Over a field `K` the relative dualizing module of a finite algebra `C` is `Hom_K(C, K)` and the
trace element is the trace functional, so `C τ = Hom_K(C,K)` says exactly that the trace form is
nondegenerate, which is étaleness.  The pointwise statement over a field follows from that global
one by localizing away from an element, on both sides.

Since the relative dualizing module is taken as data, the chart factorizations come from the
field `Stacks.Discriminant.RelativeDualizingModuleData.factorization`.

## References

* [Stacks Project, Tag 0BW9](https://stacks.math.columbia.edu/tag/0BW9)
* [Stacks Project, Tag 0BW4](https://stacks.math.columbia.edu/tag/0BW4)
* [Stacks Project, Tag 0BUR](https://stacks.math.columbia.edu/tag/0BUR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.Annihilator
open scoped TensorProduct

universe u

namespace Stacks.Discriminant

attribute [local instance] algebraDualModule

/-! ### The ideal of the cokernel of a section -/

/-- The annihilator of `M / Bτ` is the unit ideal exactly when `τ` generates `M`. -/
theorem cokerSpanIdeal_eq_top_iff {B M : Type*} [CommRing B] [AddCommGroup M] [Module B M]
    (τ : M) :
    cokerSpanIdeal B τ = ⊤ ↔ Submodule.span B {τ} = ⊤ := by
  rw [cokerSpanIdeal_def, Module.annihilator_eq_top_iff, Submodule.Quotient.subsingleton_iff]

/-! ### The field case -/

section FieldCase

variable {K C : Type u} [Field K] [CommRing C] [Algebra K C] [IsNoetherianRing C]
  [Module.Finite K C]

/-- Over a field the trace element generates the relative dualizing module exactly when the
algebra is unramified. -/
theorem cokerSpanIdeal_traceElement_eq_top_iff
    (F : FiniteOpenFactorization.{u, u, u} K C) :
    cokerSpanIdeal C (dualizingModule.traceElement F) = ⊤ ↔
      Algebra.FormallyUnramified K C := by
  have : Module.Projective K C := inferInstance
  have hself : cokerSpanIdeal C (dualizingModule.traceElement F) =
      cokerSpanIdeal C (Algebra.traceForm K C 1) := by
    refine (cokerSpanIdeal_congr (dualizingModuleEquiv F (selfFactorization K C))
      (dualizingModuleEquiv_traceElement F (selfFactorization K C))).trans ?_
    refine cokerSpanIdeal_congr (selfFactorizationDualEquiv (A := K) (B := C)) ?_
    rw [← (eq_traceElement_of_isTraceElement (selfFactorization K C)
      (isTraceElement_finiteFlatTraceElement K C) :
      finiteFlatTraceElement K C = dualizingModule.traceElement (selfFactorization K C)),
      selfFactorizationDualEquiv_finiteFlatTraceElement_eq_traceForm_one,
      finiteProjectiveTraceForm_eq_traceForm]
  rw [hself, cokerSpanIdeal_eq_top_iff]
  have hsmul (c : C) : c • (Algebra.traceForm K C 1) = Algebra.traceForm K C c := by
    ext x
    change Algebra.traceForm K C 1 (c * x) = Algebra.traceForm K C c x
    simp [Algebra.traceForm_apply]
  have hspan : Submodule.span C {Algebra.traceForm K C 1} = ⊤ ↔
      Function.Surjective (Algebra.traceForm K C) := by
    rw [Submodule.eq_top_iff', Function.Surjective]
    refine forall_congr' fun φ ↦ ?_
    rw [Submodule.mem_span_singleton]
    exact ⟨fun ⟨c, hc⟩ ↦ ⟨c, (hsmul c).symm.trans hc⟩, fun ⟨c, hc⟩ ↦ ⟨c, (hsmul c).trans hc⟩⟩
  rw [hspan]
  have hfr : Module.finrank K C = Module.finrank K (Module.Dual K C) := by simp
  rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr,
    ← LinearMap.ker_eq_bot, ← LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot,
    ← finiteDimensional_etale_iff_traceForm_nondegenerate K C]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have : Algebra.FormallyEtale K C := h.formallyEtale
    infer_instance
  · have : Algebra.FormallyUnramified K C := h
    exact ⟨Algebra.FormallyEtale.of_formallyUnramified_of_field K C,
      Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

/-- Over a field the primes containing the chart different are exactly the primes at which the
algebra fails to be unramified. -/
theorem zeroLocus_cokerSpanIdeal_traceElement_of_field
    (F : FiniteOpenFactorization.{u, u, u} K C) :
    PrimeSpectrum.zeroLocus (cokerSpanIdeal C (dualizingModule.traceElement F) : Set C) =
      (Algebra.unramifiedLocus K C)ᶜ := by
  ext q
  rw [PrimeSpectrum.mem_zeroLocus, Set.mem_compl_iff]
  change (cokerSpanIdeal C (dualizingModule.traceElement F) : Set C) ⊆ q.asIdeal ↔
    ¬ Algebra.IsUnramifiedAt K q.asIdeal
  have key (g : C) : (cokerSpanIdeal C (dualizingModule.traceElement F)).map
      (algebraMap C (Localization.Away g)) = ⊤ ↔
        Algebra.FormallyUnramified K (Localization.Away g) := by
    have : Module.Finite K (Localization.Away g) := Module.Finite.of_quasiFinite
    rw [map_cokerSpanIdeal_traceElement_of_isLocalizationAway
      (A := K) (B := C) (C := Localization.Away g) g F (selfFactorization K _),
      cokerSpanIdeal_traceElement_eq_top_iff]
  refine ⟨fun hJ hq ↦ ?_, fun hq ↦ ?_⟩
  · obtain ⟨g, hgq, hur⟩ := Algebra.exists_unramified_of_isUnramifiedAt (R := K) q.asIdeal
    have hdisj : Disjoint (Submonoid.powers g : Set C)
        (cokerSpanIdeal C (dualizingModule.traceElement F) : Set C) := by
      rw [Set.disjoint_left]
      rintro x ⟨n, rfl⟩ hx
      exact hgq (q.2.mem_of_pow_mem n (hJ hx))
    exact (IsLocalization.map_algebraMap_ne_top_iff_disjoint (Submonoid.powers g)
      (Localization.Away g) _).2 hdisj ((key g).mpr hur.formallyUnramified)
  · by_contra hJ
    obtain ⟨d, hdJ, hdq⟩ := Set.not_subset.mp hJ
    exact hq ((Algebra.basicOpen_subset_unramifiedLocus_iff.mpr
      ((key d).mp (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hdJ)
        (IsLocalization.map_units (Localization.Away d) ⟨d, Submonoid.mem_powers d⟩))))
      (show q ∈ PrimeSpectrum.basicOpen d from hdq))

end FieldCase

/-! ### The general case, by passage to the fibres -/

section General

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat A B]
  [Algebra.FiniteType A B] [Algebra.QuasiFinite A B]

/-- The primes containing the chart different are exactly the primes at which the algebra fails
to be unramified. -/
theorem zeroLocus_cokerSpanIdeal_traceElement (F : FiniteOpenFactorization.{u, u, u} A B) :
    PrimeSpectrum.zeroLocus (cokerSpanIdeal B (dualizingModule.traceElement F) : Set B) =
      (Algebra.unramifiedLocus A B)ᶜ := by
  have hfin : Module.Finite B (dualizingModule F) := dualizingModule_finite F
  have hΩ : Module.Finite B Ω[B⁄A] := inferInstance
  rw [Algebra.unramifiedLocus_eq_compl_support, compl_compl]
  ext q
  have hqp : q.asIdeal.IsPrime := q.2
  set p : Ideal A := q.asIdeal.comap (algebraMap A B)
  have hp : p.IsPrime := Ideal.comap_isPrime (algebraMap A B) q.asIdeal
  have hover : q.asIdeal.LiesOver p := ⟨rfl⟩
  set Q := PrimeSpectrum.primesOverOrderIsoFiber A B p ⟨q.asIdeal, hqp, hover⟩ with hQdef
  have hQq : PrimeSpectrum.comap (algebraMap B (p.Fiber B)) Q = q :=
    PrimeSpectrum.comap_primesOverOrderIsoFiber A B p q.asIdeal hover
  have h1 : q ∈ PrimeSpectrum.zeroLocus
        (cokerSpanIdeal B (dualizingModule.traceElement F) : Set B) ↔
      Q ∈ PrimeSpectrum.zeroLocus (cokerSpanIdeal (p.Fiber B)
        (dualizingModule.traceElement
          (FiniteOpenFactorization.baseChange F p.ResidueField)) : Set (p.Fiber B)) := by
    rw [cokerSpanIdeal_traceElement_baseChange F p.ResidueField,
      zeroLocus_cokerSpanIdeal_tmul, Set.mem_preimage, hQq]
  have h2 : Q ∈ PrimeSpectrum.zeroLocus (cokerSpanIdeal (p.Fiber B)
        (dualizingModule.traceElement
          (FiniteOpenFactorization.baseChange F p.ResidueField)) : Set (p.Fiber B)) ↔
      Q ∈ Module.support (p.Fiber B) Ω[(p.Fiber B)⁄p.ResidueField] := by
    rw [zeroLocus_cokerSpanIdeal_traceElement_of_field,
      Algebra.unramifiedLocus_eq_compl_support, compl_compl]
  have h3 : Module.support (p.Fiber B) Ω[(p.Fiber B)⁄p.ResidueField] =
      Module.support (p.Fiber B) (TensorProduct B (p.Fiber B) Ω[B⁄A]) :=
    (KaehlerDifferential.tensorKaehlerEquiv A p.ResidueField B (p.Fiber B)).support_eq.symm
  rw [h1, h2, h3, hQdef]
  exact Module.primesOverOrderIsoFiber_mem_support_iff A B Ω[B⁄A] p q.asIdeal hover

end General

end Stacks.Discriminant

/-! ### Unramifiedness and étaleness at a point, read on an affine chart -/

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- The stalk map of a morphism unramified at a point is formally unramified there. -/
theorem formallyUnramified_stalkMap_of_unramifiedAt (f : X ⟶ S) {x : X}
    (h : UnramifiedAt f x) : (f.stalkMap x).hom.FormallyUnramified := by
  obtain ⟨U₀, hU₀, hxU₀, V₀, hV₀, e, halg⟩ := h
  rw [formallyUnramified_stalkMap_iff V₀ hV₀ U₀ hU₀ e hxU₀]
  let _ : Algebra Γ(S, V₀) Γ(X, U₀) := (f.appLE V₀ U₀ e).hom.toAlgebra
  have _ : Algebra.Unramified Γ(S, V₀) Γ(X, U₀) := halg
  rw [Algebra.unramifiedLocus_eq_univ_iff.mpr Algebra.Unramified.formallyUnramified]
  trivial

/-- Unramifiedness at a point, read on an arbitrary pair of affine charts: it is membership of
the corresponding prime in the unramified locus of the map of sections. -/
theorem unramifiedAt_iff_mem_unramifiedLocus (f : X ⟶ S) [LocallyOfFiniteType f] {x : X}
    (V : S.Opens) (hV : IsAffineOpen V) (U : X.Opens) (hU : IsAffineOpen U)
    (hUV : U ≤ f ⁻¹ᵁ V) (hx : x ∈ U) :
    letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
    UnramifiedAt f x ↔
      hU.primeIdealOf ⟨x, hx⟩ ∈ Algebra.unramifiedLocus Γ(S, V) Γ(X, U) := by
  let _ : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  rw [← formallyUnramified_stalkMap_iff V hV U hU hUV hx]
  refine ⟨formallyUnramified_stalkMap_of_unramifiedAt f, fun hstalk ↦ ?_⟩
  have _ : Algebra.FiniteType Γ(S, V) Γ(X, U) :=
    RingHom.finiteType_algebraMap.mp (f.finiteType_appLE hV hU hUV)
  have _ : Algebra.IsUnramifiedAt Γ(S, V) (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    (formallyUnramified_stalkMap_iff V hV U hU hUV hx).mp hstalk
  obtain ⟨r, hr, hur⟩ := Algebra.exists_unramified_of_isUnramifiedAt
    (R := Γ(S, V)) (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  have hrle : X.basicOpen r ≤ f ⁻¹ᵁ V := (X.basicOpen_le r).trans hUV
  refine ⟨X.basicOpen r, hU.basicOpen r, ?_, V, hV, hrle, ?_⟩
  · change (⟨x, hx⟩ : U).1 ∈ X.basicOpen r
    rw [← hU.fromSpec_primeIdealOf ⟨x, hx⟩]
    change hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen r
    rw [hU.fromSpec_preimage_basicOpen]
    exact hr
  · let _ : Algebra Γ(S, V) Γ(X, X.basicOpen r) :=
      (f.appLE V (X.basicOpen r) hrle).hom.toAlgebra
    have _ : IsLocalization.Away r Γ(X, X.basicOpen r) := hU.isLocalization_basicOpen r
    have _ : IsScalarTower Γ(S, V) Γ(X, U) Γ(X, X.basicOpen r) := by
      refine IsScalarTower.of_algebraMap_eq' ?_
      simp only [RingHom.algebraMap_toAlgebra]
      exact (CommRingCat.hom_ext_iff.mp
        (f.appLE_map hUV (homOfLE (X.basicOpen_le r)).op)).symm
    have _ : Algebra.Unramified Γ(S, V) (Localization.Away r) := hur
    exact Algebra.Unramified.of_equiv
      ((IsLocalization.algEquiv (.powers r) (Localization.Away r)
        Γ(X, X.basicOpen r)).restrictScalars Γ(S, V))

/-- A flat morphism locally of finite type over a locally Noetherian base is étale at a point
exactly when it is unramified there. -/
theorem etaleAt_iff_unramifiedAt (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    [Flat f] (x : X) : EtaleAt f x ↔ UnramifiedAt f x := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨U, hU, hxU, V, hV, e, hEt⟩ := h
    refine ⟨U, hU, hxU, V, hV, e, ?_⟩
    let _ : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    have _ : Algebra.Etale Γ(S, V) Γ(X, U) := RingHom.etale_algebraMap.mpr hEt
    exact ⟨inferInstance, inferInstance⟩
  · rw [← isEtaleAt_iff_etaleAt]
    exact ⟨Flat.stalkMap f x, formallyUnramified_stalkMap_of_unramifiedAt f h,
      LocallyOfFiniteType.stalkMap f x⟩

end AlgebraicGeometry

/-! ### The zero locus of the different -/

namespace Stacks.Discriminant

section Tag

variable {X Y : Scheme.{u}} {f : Y ⟶ X}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  [Flat f] [LocallyOfFiniteType f] [LocallyQuasiFinite f]

/-- The underlying set of the closed subscheme cut out by the different is the set of points at
which `f` is not unramified. -/
theorem mem_support_differentIdealSheaf_iff_not_unramifiedAt
    (ω : RelativeDualizingModuleData f) (τ : RelativeTraceSection ω) (y : Y) :
    y ∈ (differentIdealSheaf ω τ).support ↔ ¬ UnramifiedAt f y := by
  obtain ⟨U, hyU, -⟩ := exists_affine_subset (f y) ⊤ trivial
  obtain ⟨V, hyV, hVU⟩ := exists_affine_subset y (f ⁻¹ᵁ U.1) hyU
  obtain ⟨F⟩ := ω.factorization U V hVU
  let _ : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  have _ : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have _ : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
  have _ : Module.Flat Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hVU)
  have _ : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
  have _ : Algebra.FiniteType Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.finiteType_algebraMap.mp (f.finiteType_appLE U.2 V.2 hVU)
  rw [mem_support_iff_primeIdealOf (differentIdealSheaf ω τ) V y hyV,
    differentIdealSheaf_ideal_eq_cokerSpanIdeal ω τ U V hVU F,
    zeroLocus_cokerSpanIdeal_traceElement F, Set.mem_compl_iff,
    ← unramifiedAt_iff_mem_unramifiedLocus f U.1 U.2 V.1 V.2 hVU hyV]

/-- The underlying set of the closed subscheme cut out by the different is the set of points at
which `f` is not étale. -/
theorem mem_support_differentIdealSheaf_iff_not_etaleAt
    (ω : RelativeDualizingModuleData f) (τ : RelativeTraceSection ω) (y : Y) :
    y ∈ (differentIdealSheaf ω τ).support ↔ ¬ EtaleAt f y := by
  rw [mem_support_differentIdealSheaf_iff_not_unramifiedAt ω τ y,
    etaleAt_iff_unramifiedAt f y]

/-- For a flat quasi-finite morphism of locally Noetherian schemes, the closed subscheme
`R ⊆ Y` cut out by the different `𝔇_f` is exactly the set of points at which `f` is not
étale. -/
@[stacks 0BW9 "the non-étale locus"]
theorem range_eq_setOf_not_etaleAt (ω : RelativeDualizingModuleData f)
    (τ : RelativeTraceSection ω) {R : Scheme.{u}} (i : R ⟶ Y) [IsClosedImmersion i]
    (hi : i.ker = differentIdealSheaf ω τ) :
    Set.range i.base = {y : Y | ¬ EtaleAt f y} := by
  rw [closedImmersion_range_eq_support i, hi]
  exact Set.ext fun y ↦ mem_support_differentIdealSheaf_iff_not_etaleAt ω τ y

/-- Equivalently, the closed subscheme cut out by the different is exactly the set of points at
which `f` is not unramified. -/
@[stacks 0BW9 "the non-unramified locus"]
theorem range_eq_setOf_not_unramifiedAt (ω : RelativeDualizingModuleData f)
    (τ : RelativeTraceSection ω) {R : Scheme.{u}} (i : R ⟶ Y) [IsClosedImmersion i]
    (hi : i.ker = differentIdealSheaf ω τ) :
    Set.range i.base = {y : Y | ¬ UnramifiedAt f y} := by
  rw [closedImmersion_range_eq_support i, hi]
  exact Set.ext fun y ↦ mem_support_differentIdealSheaf_iff_not_unramifiedAt ω τ y

/-- The closed subscheme cut out by the different, in its canonical presentation, is the
non-étale locus. -/
theorem range_subschemeι_differentIdealSheaf_eq_setOf_not_etaleAt
    (ω : RelativeDualizingModuleData f) (τ : RelativeTraceSection ω) :
    Set.range (differentIdealSheaf ω τ).subschemeι.base = {y : Y | ¬ EtaleAt f y} :=
  range_eq_setOf_not_etaleAt ω τ _ (ker_subschemeι_differentIdealSheaf ω τ)

/-- The closed subscheme cut out by the different, in its canonical presentation, is the
non-unramified locus. -/
theorem range_subschemeι_differentIdealSheaf_eq_setOf_not_unramifiedAt
    (ω : RelativeDualizingModuleData f) (τ : RelativeTraceSection ω) :
    Set.range (differentIdealSheaf ω τ).subschemeι.base = {y : Y | ¬ UnramifiedAt f y} :=
  range_eq_setOf_not_unramifiedAt ω τ _ (ker_subschemeι_differentIdealSheaf ω τ)

end Tag

end Stacks.Discriminant

end
