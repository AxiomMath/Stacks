module

public import StacksFrontier.RingTheory.FormsTrace.ExistenceAlgebra
public import StacksFrontier.RingTheory.FormsTrace.ExistenceTransport
public import StacksFrontier.AlgebraicGeometry.DeRham.Comparison.Existence
public import StacksFrontier.AlgebraicGeometry.TateMap.TateMap
public import StacksFrontier.RingTheory.TraceElement.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.EventualMapEq

/-!
# Existence of trace maps on forms, Noetherian case

Let `A → B` be a finite syntomic ring map with `A` Noetherian (so `B` is finite projective over
`A`). The proof of Stacks, Lemma 0FLB constructs maps `Θ^p : Ω^p_B → Ω^p_A` satisfying condition
(1) of that lemma from

* the canonical maps `c^p : Ω^p_B → Ω^p_A ⊗_A det(NL_{B/A})` of Lemma 0FLA, which carry a pulled
  back form `ω` to `ω ⊗ δ(NL_{B/A})`;
* the Tate map `det(NL_{B/A}) ≅ ω_{B/A}` of Proposition 0FKD, carrying `δ(NL_{B/A})` to the
  trace element `τ_{B/A}`;
* the identification `ω_{B/A} = Hom_A(B, A)` of a finite flat algebra, under which `τ_{B/A}` is
  `Trace_{B/A}` (Tag 0BT8).

All three exist in the library at the level of sheaves on schemes; this file reads them on an
affine chart `(U, V)` of a locally quasi-finite syntomic morphism `f : Y ⟶ X`, assembles them
with `Stacks.FormsTrace.exists_isFormsTrace_of_twisted`, and applies the result to
`Spec B → Spec A` and the chart `(⊤, ⊤)`, transporting along `Γ(Spec R, ⊤) ≅ R`.

## Main definitions

* `Stacks.FormsTrace.twistedChartMap`: the maps of Lemma 0FLA on an affine chart, as maps
  `Ω^p_B → ⋀^p_B(B ⊗_A Ω_A) ⊗_B det(NL_{B/A})`.

## Main results

* `Stacks.FormsTrace.twistedChartMap_pullback`: they carry a pulled back form `ω` to
  `ω ⊗ δ(NL_{B/A})`.
* `Stacks.FormsTrace.chartValue_tateIso_deltaNL`: the Tate map on an affine chart carries
  `δ(NL_{B/A})` to the trace element.
* `Stacks.FormsTrace.exists_tate_affineChart`: the Tate map on an affine chart, followed by
  `ω_{B/A} = Hom_A(B, A)`, carries `δ(NL_{B/A})` to `Trace_{B/A}`.
* `Stacks.FormsTrace.exists_isFormsTrace_affineChart`: condition (1) of Lemma 0FLB on a finite
  projective affine chart.
* `Stacks.FormsTrace.exists_isFormsTrace_of_isNoetherianRing`: condition (1) of Lemma 0FLB can be
  satisfied for every finite syntomic `A → B` with `A` Noetherian.

## References

* [Stacks Project, Tag 0FLB](https://stacks.math.columbia.edu/tag/0FLB)
* [Stacks Project, Tag 0FLA](https://stacks.math.columbia.edu/tag/0FLA)
* [Stacks Project, Tag 0FKD](https://stacks.math.columbia.edu/tag/0FKD)
* [Stacks Project, Tag 0BT8](https://stacks.math.columbia.edu/tag/0BT8)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Stacks.FormsTrace

section Chart

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.affineOpens) (V : Y.affineOpens)
  (hVU : V.1 ≤ f ⁻¹ᵁ U.1)

attribute [local instance] Scheme.Hom.isQuasicoherent_relativeDifferentialForms

/-- `Scheme.Modules.sectionsLinearMap` form of `Scheme.Hom.GarelMaps.app_absoluteFormsMap`:
maps satisfying (0H9C) and (0H9D) carry the image of a pulled back form `ζ` to `ζ ⊗ δ`. -/
theorem sectionsLinearMap_garelMaps_absoluteFormsMap {L : Y.Modules} {δ : Γ(L, ⊤)}
    {c : f.GarelMaps L}
    (hn : c.IsNormalized δ) (hm : c.IsMultiplicative) (p : ℕ) (W : Y.Opens)
    (ζ : Γ(f.pullbackForms p, W)) :
    Scheme.Modules.sectionsLinearMap (c p) W ((f.absoluteFormsMap p).val.app (op W) ζ) =
      f.twistedPullbackFormsTmul L p W ζ (L.val.map (homOfLE le_top).op δ) :=
  Scheme.Hom.GarelMaps.app_absoluteFormsMap hn hm p W ζ

/-- The chart `(U, V)` of `f`, as an element of the chart index of `f`. -/
abbrev affineChart : f.chartIndex.ι := ⟨(U, V), hVU⟩

/-- **The maps of Lemma 0FLA on an affine chart**: for a locally quasi-finite syntomic
`f : Y ⟶ X` and affine opens `V ⊆ f⁻¹(U)`, with `A = Γ(X, U)` and `B = Γ(Y, V)`, the sections
over `V` of the glued maps `Scheme.Hom.chartGarelMaps`, read as `B`-linear maps
`Ω^p_B → ⋀^p_B(B ⊗_A Ω_A) ⊗_B det(NL_{B/A})`. -/
def twistedChartMap (hf : Syntomic f) [LocallyQuasiFinite f] (p : ℕ) :=
  letI := (f.appLE U V hVU).hom.toAlgebra
  (TensorProduct.congr (Scheme.pullbackFormsSectionsEquiv V.2 f U.2 hVU p)
      (f.detNLSectionsEquiv hf (affineChart f U V hVU))).toLinearMap ∘ₗ
    (f.twistedSectionsEquiv V.2 (f.detNL hf) p).toLinearMap ∘ₗ
      Scheme.Modules.sectionsLinearMap (f.chartGarelMaps hf p) V.1 ∘ₗ
    (Scheme.absoluteFormsSectionsEquiv Y V.2 p).symm.toLinearMap

/-- `twistedChartMap` carries the image of a pulled back form `ζ` to `ζ ⊗ δ(NL_{B/A})`, read
through `Γ(f^*Ω^p_{X/ℤ}, V) ≃ ⋀^p_B(B ⊗_A Ω_A)`. -/
theorem twistedChartMap_pullback (hf : Syntomic f) [LocallyQuasiFinite f] (p : ℕ)
    (ζ : Γ(f.pullbackForms p, V.1)) :
    letI := (f.appLE U V hVU).hom.toAlgebra
    twistedChartMap f U V hVU hf p
        (exteriorPower.map p (KaehlerDifferential.mapBaseChange ℤ Γ(X, U.1) Γ(Y, V.1))
          (Scheme.pullbackFormsSectionsEquiv V.2 f U.2 hVU p ζ)) =
      Scheme.pullbackFormsSectionsEquiv V.2 f U.2 hVU p ζ ⊗ₜ
        f.deltaNLChart hf (affineChart f U V hVU) := by
  have hA := (LinearEquiv.symm_apply_eq _).mpr
      (Scheme.absoluteFormsSectionsEquiv_absoluteFormsMap V.2 f U.2 hVU p ζ).symm
  have hB := sectionsLinearMap_garelMaps_absoluteFormsMap f (f.chartGarelMaps_isNormalized hf)
    (f.chartGarelMaps_isMultiplicative hf) p V.1 ζ
  have hC := (congrArg (f.twistedSectionsEquiv V.2 (f.detNL hf) p)
    (f.twistedSectionsEquiv_symm_tmul V.2 (f.detNL hf) p ζ
      ((f.detNL hf).val.map (homOfLE le_top).op (f.deltaNL hf))).symm).trans
    ((f.twistedSectionsEquiv V.2 (f.detNL hf) p).apply_symm_apply _)
  have hD := (TensorProduct.congr_tmul (Scheme.pullbackFormsSectionsEquiv V.2 f U.2 hVU p)
      (f.detNLSectionsEquiv hf (affineChart f U V hVU)) ζ
      ((f.detNL hf).val.map (homOfLE le_top).op (f.deltaNL hf))).trans
    (congrArg (Scheme.pullbackFormsSectionsEquiv V.2 f U.2 hVU p ζ ⊗ₜ ·)
      (f.detNLSectionsEquiv_deltaNL hf (affineChart f U V hVU)))
  simp only [twistedChartMap, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  simp only [hA, hB, hC, hD]

end Chart

section Tate

open AlgebraicGeometry.TateMap

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] (f : Y ⟶ X) (hf : IsQuasiFiniteSyntomic f)
  (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)

/-- **The Tate map on an affine chart carries `δ(NL_{B/A})` to `τ_{B/A}`**: the chart value
of `AlgebraicGeometry.TateMap.tateIso` (Proposition 0FKD) on `(U, V)`, for any finite-open
factorization computing `ω_{B/A}`, carries `δ(NL_{B/A})` to the trace element. -/
theorem chartValue_tateIso_deltaNL
    (F : letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
      Stacks.Discriminant.FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1)) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    haveI := algebra_syntomic_appLE hf.2 U V hVU
    haveI := AlgebraicGeometry.quasiFinite_appLE hf.1 U V hVU
    haveI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    haveI : Module.Flat Γ(X, U.1) Γ(Y, V.1) :=
      haveI : Flat f := AlgebraicGeometry.flat hf.2
      RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hVU)
    haveI : Module.FinitePresentation Γ(X, U.1) F.middle :=
      Module.finitePresentation_of_finite _ _
    chartValue (tateIso f hf) U V hVU F (Stacks.TateMap.deltaNL Γ(X, U.1) Γ(Y, V.1)) =
      Stacks.Discriminant.dualizingModule.traceCandidate F := by
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  have := algebra_syntomic_appLE hf.2 U V hVU
  have := AlgebraicGeometry.quasiFinite_appLE hf.1 U V hVU
  have := isLocallyNoetherian_source f hf
  have := hf.1
  have : Flat f := AlgebraicGeometry.flat hf.2
  have h1 := (LinearEquiv.symm_apply_eq _).mpr (detNLChartEquiv_deltaNL f hf U V hVU).symm
  have h2 := Stacks.AlgebraicGeometry.ModuleLimits.Hom_app_presheaf_map (tateIso f hf).hom
    (le_top : V.1 ≤ ⊤) (deltaNL f hf)
  simp only [chartValue, LinearEquiv.trans_apply, sectionsLinearEquiv_of_iso_apply]
  rw [h1, ← h2, tateIso_deltaNL f hf]
  exact Stacks.Discriminant.localEquiv_relativeTraceSection (omegaData f hf) U V hVU F

attribute [local instance] Stacks.Discriminant.algebraDualModule

include hf in
/-- **The Tate map on an affine chart, followed by `ω_{B/A} = Hom_A(B, A)`**: for a finite
projective affine chart `(U, V)` of a locally quasi-finite syntomic `f : Y ⟶ X` with `X` locally
Noetherian, `A = Γ(X, U)`, `B = Γ(Y, V)`, there is a `B`-linear map
`u : det(NL_{B/A}) → Hom_A(B, A)` (for `(b · φ)(x) = φ(bx)`) carrying `δ(NL_{B/A})` to
`Trace_{B/A}`: the chart value of the Tate map of Proposition 0FKD with `ω_{B/A}` computed by
`A → B → B`, followed by evaluation; `τ_{B/A}` is `Trace_{B/A}` by Tag 0BT8. -/
theorem exists_tate_affineChart :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    haveI := hf.1
    ∀ [Module.Finite Γ(X, U.1) Γ(Y, V.1)] [Module.Projective Γ(X, U.1) Γ(Y, V.1)],
      ∃ u : f.detNLChart hf.2 (affineChart f U V hVU) →ₗ[Γ(Y, V.1)]
          Module.Dual Γ(X, U.1) Γ(Y, V.1),
        u (f.deltaNLChart hf.2 (affineChart f U V hVU)) = trace Γ(X, U.1) Γ(Y, V.1) := by
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  have := hf.1
  intro _ _
  have := algebra_syntomic_appLE hf.2 U V hVU
  have := AlgebraicGeometry.quasiFinite_appLE hf.1 U V hVU
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have : IsNoetherianRing Γ(Y, V.1) :=
    have := isLocallyNoetherian_source f hf
    IsLocallyNoetherian.component_noetherian V
  have : Module.FinitePresentation Γ(X, U.1) Γ(Y, V.1) :=
    Module.finitePresentation_of_finite _ _
  have hT := chartValue_tateIso_deltaNL f hf U V hVU
    (Stacks.Discriminant.selfFactorization Γ(X, U.1) Γ(Y, V.1))
  have hτ := (Stacks.Discriminant.isTraceElement_iff_eq_traceCandidate
    (Stacks.Discriminant.selfFactorization Γ(X, U.1) Γ(Y, V.1)) _).mp
    (Stacks.Discriminant.isTraceElement_finiteFlatTraceElement.{u, u, u, u, u}
      Γ(X, U.1) Γ(Y, V.1))
  refine ⟨(Stacks.Discriminant.selfFactorizationDualEquiv (A := Γ(X, U.1))
      (B := Γ(Y, V.1))).toLinearMap ∘ₗ
      (chartValue (tateIso f hf) U V hVU
        (Stacks.Discriminant.selfFactorization Γ(X, U.1) Γ(Y, V.1))).toLinearMap ∘ₗ
      detNLToTate Γ(X, U.1) Γ(Y, V.1), ?_⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    detNLToTate_deltaNL, hT, ← hτ]
  exact selfFactorizationDualEquiv_finiteFlatTraceElement_eq_trace Γ(X, U.1) Γ(Y, V.1)

include hf in
/-- **Condition (1) of Lemma 0FLB on a finite projective affine chart.** Let `f : Y ⟶ X` be
locally quasi-finite syntomic with `X` locally Noetherian, and `(U, V)` an affine chart with
`B = Γ(Y, V)` finite projective over `A = Γ(X, U)`. Then there are maps `Θ^p : Ω^p_B → Ω^p_A`
satisfying condition (1) of Lemma 0FLB: they are built from the maps of Lemma 0FLA on the chart,
the Tate map of Proposition 0FKD on the chart and `ω_{B/A} = Hom_A(B, A)` (Tag 0BT8). -/
theorem exists_isFormsTrace_affineChart :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    ∀ [Module.Finite Γ(X, U.1) Γ(Y, V.1)] [Module.Projective Γ(X, U.1) Γ(Y, V.1)],
      ∃ Θ : ∀ p : ℕ, ⋀[Γ(Y, V.1)]^p Ω[Γ(Y, V.1)⁄ℤ] →ₗ[Γ(X, U.1)] ⋀[Γ(X, U.1)]^p Ω[Γ(X, U.1)⁄ℤ],
        IsFormsTrace Γ(X, U.1) Γ(Y, V.1) Θ := by
  intro _ _
  have := hf.1
  obtain ⟨u, hu⟩ := exists_tate_affineChart f hf U V hVU
  exact @exists_isFormsTrace_of_twisted _ _ _ _ (f.appLE U.1 V.1 hVU).hom.toAlgebra _ _ _ _ _
    (twistedChartMap f U V hVU hf.2) (f.deltaNLChart hf.2 (affineChart f U V hVU)) _
    (fun p => Scheme.pullbackFormsSectionsEquiv V.2 f U.2 hVU p)
    (fun p => (Scheme.pullbackFormsSectionsEquiv V.2 f U.2 hVU p).surjective)
    (twistedChartMap_pullback f U V hVU hf.2) u hu

end Tate

/-- **Condition (1) of Stacks, Lemma 0FLB can be satisfied, Noetherian case.** For a finite
syntomic ring map `A → B` with `A` Noetherian (`B` finite projective over `A`) there are
`A`-linear maps `Θ^p : Ω^p_B → Ω^p_A` with `Θ^p(b · ω) = Trace_{B/A}(b) · ω` for `b ∈ B` and every
form `ω` of `A`. They are read off `Spec B → Spec A` on the chart `(⊤, ⊤)`
(`Stacks.FormsTrace.exists_isFormsTrace_affineChart`) and transported along
`Γ(Spec R, ⊤) ≅ R`. -/
theorem exists_isFormsTrace_of_isNoetherianRing (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] [IsNoetherianRing A] [Module.Finite A B] [Module.Projective A B]
    [Algebra.Syntomic A B] :
    ∃ Θ : ∀ p : ℕ, ⋀[B]^p Ω[B⁄ℤ] →ₗ[A] ⋀[A]^p Ω[A⁄ℤ], IsFormsTrace A B Θ := by
  have hf := AlgebraicGeometry.TateMap.isQuasiFiniteSyntomic_specMap A B
  set f : Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let U : (Spec (.of A)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  let V : (Spec (.of B)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have hVU : V.1 ≤ f ⁻¹ᵁ U.1 := fun _ _ => trivial
  let eA : A ≃+* Γ(Spec (.of A), U.1) :=
    (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.symm
  let eB : B ≃+* Γ(Spec (.of B), V.1) :=
    (Scheme.ΓSpecIso (.of B)).commRingCatIsoToRingEquiv.symm
  have h : ∀ a, eB (algebraMap A B a) = (f.appLE U.1 V.1 hVU).hom (eA a) := fun a => by
    rw [show f.appLE U.1 V.1 hVU = f.appTop from f.appLE_eq_app]
    exact congrArg (fun g => g.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B)))
  have hfin : let := (f.appLE U.1 V.1 hVU).hom.toAlgebra
      Module.Finite Γ(Spec (.of A), U.1) Γ(Spec (.of B), V.1) := by
    let := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    exact Module.Finite.of_equiv_equiv eA eB (RingHom.ext fun a => (h a).symm)
  have hproj : let := (f.appLE U.1 V.1 hVU).hom.toAlgebra
      Module.Projective Γ(Spec (.of A), U.1) Γ(Spec (.of B), V.1) := by
    let := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    have : Flat f := AlgebraicGeometry.flat hf.2
    have : Module.Flat Γ(Spec (.of A), U.1) Γ(Spec (.of B), V.1) :=
      RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hVU)
    have : IsNoetherianRing Γ(Spec (.of A), U.1) :=
      IsLocallyNoetherian.component_noetherian U
    have := hfin
    have : Module.FinitePresentation Γ(Spec (.of A), U.1) Γ(Spec (.of B), V.1) :=
      Module.finitePresentation_of_finite _ _
    exact Module.Flat.projective_of_finitePresentation
  exact @exists_isFormsTrace_of_ringEquiv _ _ _ _ _ _ _ _ _
    (f.appLE U.1 V.1 hVU).hom.toAlgebra eA eB h _ _ hfin hproj
    (@exists_isFormsTrace_affineChart _ _ _ f hf U V hVU hfin hproj)

end Stacks.FormsTrace

end
