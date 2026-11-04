module

public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.AffineOpenDeRhamSquareComplex
public import StacksFrontier.AlgebraicGeometry.DeRham.ArtinianRigidity.ChartBasis
public import StacksFrontier.AlgebraicGeometry.DeRham.ArtinianRigidity.DerivedTransfer

/-!
# Rigidity of de Rham cohomology over an Artinian `ℚ`-algebra

Let `A` be an Artinian local `ℚ`-algebra with residue field `k` and coefficient field
`σ : k → A`, and let `f : X ⟶ Spec A` be separated and smooth. Let `X₀` be the special fibre and
`X' = X₀ ×_k Spec A` the trivial deformation of `X₀`. Then
`Rf_*Ω^•_{X/A} ≅ Rf'_*Ω^•_{X'/A}` in `D⁺(𝒪_{Spec A})`: in characteristic zero, de Rham cohomology
over an Artinian base depends only on the special fibre.

## The proof

Let `W_N ⊆ X ×_A X'` be the `N`-th infinitesimal neighbourhood of the graph of the identification
`X₀ = X'₀`, with `𝔪^N = 0`, and `q, q'` its projections to `X` and `X'`. On a chart the
comparison `Ω^•_{X/A} → q_*Ω^•_{W_N/A}` is the restriction of forms
`Ω^•_{R/A} → Ω^•_{((R ⊗_A R')/I^N)/A}`, a quasi-isomorphism by the graded Poincaré lemma
(`quasiIso_chartFst`). Both comparisons are therefore quasi-isomorphisms of complexes of sheaves
(`quasiIso_deRhamPushforwardChain_of_sections`), and `q`, `q'` are affine, so
`Rf_*Ω^•_{X/A} ≅ R(q ≫ f)_*Ω^•_{W_N/A} = R(q' ≫ f')_*Ω^•_{W_N/A} ≅ Rf'_*Ω^•_{X'/A}`
(`derivedDeRhamDirectImageIsoOfQuasiIso`).

## Main results

* `Stacks.DeRhamRigidity.ringDeRhamAbSquareMap_triangle_eq`,
  `Stacks.DeRhamRigidity.quasiIso_sections_of_quasiIso_deRhamComplexMap`: the comparison of a
  triangle `Y ⟶ X ⟶ S` on an affine chart is the restriction of forms of the rings of sections.
* `Stacks.DeRhamRigidity.nonempty_derivedDeRhamDirectImage_iso_trivialMap_of_charts`: the
  rigidity isomorphism, given the chart bases and the affineness of the projections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open Stacks.AlgebraicGeometry.AffineOpenDeRham Stacks.Cohomology.LerayLowDegree

universe u

namespace Stacks.DeRhamRigidity

section Triangle

variable {Y X S : Scheme.{u}} (q : Y ⟶ X) (p : X ⟶ S) {U : X.Opens} {V : S.Opens}
  (hU : IsAffineOpen U) (hU' : IsAffineOpen (q ⁻¹ᵁ U)) (hV : IsAffineOpen V) (e : U ≤ p ⁻¹ᵁ V)

/-- If `U ≤ p⁻¹ V`, then `q⁻¹ U ≤ (q ≫ p)⁻¹ V`. -/
theorem preimage_le_preimage_comp (e : U ≤ p ⁻¹ᵁ V) : q ⁻¹ᵁ U ≤ (q ≫ p) ⁻¹ᵁ V :=
  fun _ hx => e hx

/-- The map `Γ(S, V) → Γ(X, U)` induced by `p` followed by the restriction `Γ(X, U) → Γ(Y, q⁻¹ U)`
induced by `q` is the map `Γ(S, V) → Γ(Y, q⁻¹ U)` induced by `q ≫ p`. -/
theorem appLE_comp_app (e : U ≤ p ⁻¹ᵁ V) :
    p.appLE V U e ≫ q.app U = (q ≫ p).appLE V (q ⁻¹ᵁ U) (preimage_le_preimage_comp q p e) := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]

/-- The composite `q ≫ p` equals `(q ≫ p) ≫ 𝟙 S`. -/
theorem comp_comp_id : q ≫ p = (q ≫ p) ≫ 𝟙 S := (Category.comp_id _).symm

include hU hU' hV in
/-- **On an affine chart the comparison of a triangle is the restriction of forms**: for
`q : Y ⟶ X` over `S` with `U`, `q⁻¹ U` and `V` affine, the comparison map of de Rham complexes on
sections is the map `Ω^•_{Γ(X, U)/Γ(S, V)} → Ω^•_{Γ(Y, q⁻¹ U)/Γ(S, V)}` induced by `q`. -/
theorem ringDeRhamAbSquareMap_triangle_eq :
    letI : Algebra Γ(S, V) Γ(X, U) := (p.appLE V U e).hom.toAlgebra
    letI : Algebra Γ(S, V) Γ(Y, q ⁻¹ᵁ U) :=
      ((q ≫ p).appLE V _ (preimage_le_preimage_comp q p e)).hom.toAlgebra
    letI : Algebra Γ(X, U) Γ(Y, q ⁻¹ᵁ U) := (q.app U).hom.toAlgebra
    haveI : IsScalarTower Γ(S, V) Γ(X, U) Γ(Y, q ⁻¹ᵁ U) :=
      IsScalarTower.of_algebraMap_eq fun r =>
        (ConcreteCategory.congr_hom (appLE_comp_app q p e) r).symm
    ringDeRhamAbSquareMap q p (q ≫ p) (𝟙 S) hU hU' hV hV e (preimage_le_preimage_comp q p e)
        (comp_comp_id q p) =
      ((forget₂ (ModuleCat.{u} Γ(S, V)) AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.up ℕ)).map
        (KaehlerDifferential.deRhamComplexMap Γ(S, V) Γ(X, U) Γ(Y, q ⁻¹ᵁ U)) := by
  ext n : 1
  refine ringDeRhamAb_hom_ext p e n fun b => ?_
  let : Algebra Γ(S, V) Γ(X, U) := (p.appLE V U e).hom.toAlgebra
  let : Algebra Γ(S, V) Γ(Y, q ⁻¹ᵁ U) :=
    ((q ≫ p).appLE V _ (preimage_le_preimage_comp q p e)).hom.toAlgebra
  let : Algebra Γ(X, U) Γ(Y, q ⁻¹ᵁ U) := (q.app U).hom.toAlgebra
  have : IsScalarTower Γ(S, V) Γ(X, U) Γ(Y, q ⁻¹ᵁ U) :=
    IsScalarTower.of_algebraMap_eq fun r =>
      (ConcreteCategory.congr_hom (appLE_comp_app q p e) r).symm
  rw [ringDeRhamAbSquareMap_f_smul_ιMulti_d]
  exact (KaehlerDifferential.mapExteriorPower_smul_ιMulti_D Γ(S, V) Γ(X, U)
    Γ(Y, q ⁻¹ᵁ U) n b).symm

include hU hU' hV in
/-- **A chart on which the restriction of forms is a quasi-isomorphism is a chart on which the
comparison of de Rham complexes is a quasi-isomorphism on sections.** -/
theorem quasiIso_sections_of_quasiIso_deRhamComplexMap
    (h : letI : Algebra Γ(S, V) Γ(X, U) := (p.appLE V U e).hom.toAlgebra
      letI : Algebra Γ(S, V) Γ(Y, q ⁻¹ᵁ U) :=
        ((q ≫ p).appLE V _ (preimage_le_preimage_comp q p e)).hom.toAlgebra
      letI : Algebra Γ(X, U) Γ(Y, q ⁻¹ᵁ U) := (q.app U).hom.toAlgebra
      haveI : IsScalarTower Γ(S, V) Γ(X, U) Γ(Y, q ⁻¹ᵁ U) :=
        IsScalarTower.of_algebraMap_eq fun r =>
          (ConcreteCategory.congr_hom (appLE_comp_app q p e) r).symm
      QuasiIso (KaehlerDifferential.deRhamComplexMap Γ(S, V) Γ(X, U) Γ(Y, q ⁻¹ᵁ U))) :
    QuasiIso (((abelianSections.{u, u} X.carrier U).mapHomologicalComplex
      (ComplexShape.up ℕ)).map (Scheme.Hom.deRhamAbelianPushforwardMap q p (q ≫ p) (𝟙 S)
        (comp_comp_id q p))) := by
  have hring := ringDeRhamAbSquareMap_triangle_eq q p hU hU' hV e
  have hsq : ((abelianSections.{u, u} X.carrier U).mapHomologicalComplex
      (ComplexShape.up ℕ)).map (Scheme.Hom.deRhamAbelianPushforwardMap q p (q ≫ p) (𝟙 S)
        (comp_comp_id q p)) =
      (deRhamSectionsAbComplexIso p hU hV e).inv ≫
        ringDeRhamAbSquareMap q p (q ≫ p) (𝟙 S) hU hU' hV hV e
          (preimage_le_preimage_comp q p e) (comp_comp_id q p) ≫
        (deRhamSectionsAbComplexIso (q ≫ p) hU' hV (preimage_le_preimage_comp q p e)).hom := by
    simp only [ringDeRhamAbSquareMap, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.inv_hom_id_assoc]
    rfl
  rw [hsq, hring]
  exact quasiIso_comp (hφ := quasiIso_of_isIso (deRhamSectionsAbComplexIso p hU hV e).inv)
    (hφ' := quasiIso_comp (hφ := HomologicalComplex.quasiIso_map_of_preservesHomology _ _
      (hφ := h)) (hφ' := quasiIso_of_isIso
      (deRhamSectionsAbComplexIso (q ≫ p) hU' hV (preimage_le_preimage_comp q p e)).hom))

end Triangle

/-- The maximal ideal of an Artinian local ring has a vanishing positive power. -/
theorem exists_maximalIdeal_pow_eq_bot (A : Type*) [CommRing A] [IsArtinianRing A]
    [IsLocalRing A] : ∃ N : ℕ, N ≠ 0 ∧ maximalIdeal A ^ N = ⊥ := by
  obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal A).mp ‹_›
  refine ⟨n + 1, n.succ_ne_zero, ?_⟩
  rw [pow_succ, hn, zero_mul, Ideal.zero_eq_bot]

section Rigidity

variable {A : CommRingCat.{u}} [IsLocalRing A] {σ : A ⧸ maximalIdeal A →+* A}
  (hσ : (Ideal.Quotient.mk (maximalIdeal A)).comp σ = RingHom.id _)
  {X : Scheme.{u}} (f : X ⟶ Spec A) [IsSeparated f]

open Stacks.DeRhamDirectImage

/-- **Rigidity of `Rf_*Ω^•` over an Artinian `ℚ`-algebra, from the charts.** Granted that the
charts of `X` and of `X'` (affine, with étale coordinates over `A`, and nested special fibres)
form bases, and that the two projections of `W_N` are affine, the de Rham complexes of `X` and of
the trivial deformation `X'` of its special fibre have isomorphic derived direct images. -/
theorem nonempty_derivedDeRhamDirectImage_iso_trivialMap_of_charts [Algebra ℚ A] (N : ℕ)
    (hN0 : N ≠ 0) (hN : maximalIdeal A ^ N = ⊥)
    (h₁ : TopologicalSpace.Opens.IsBasis {U : X.Opens | IsAffineOpen U ∧
      (∃ (d : ℕ) (e : MvPolynomial (Fin d) Γ(Spec A, ⊤) →+* Γ(X, U)),
        e.comp MvPolynomial.C = (f.appLE ⊤ U le_top).hom ∧ e.Etale) ∧
      ∃ V : (trivialDef σ f).Opens, IsAffineOpen V ∧
        (∃ (d : ℕ) (e : MvPolynomial (Fin d) Γ(Spec A, ⊤) →+* Γ(trivialDef σ f, V)),
          e.comp MvPolynomial.C = ((trivialMap σ f).appLE ⊤ V le_top).hom ∧ e.Etale) ∧
        specialIncl f ⁻¹ᵁ U ≤ trivialIncl hσ f ⁻¹ᵁ V})
    (h₂ : TopologicalSpace.Opens.IsBasis {V : (trivialDef σ f).Opens | IsAffineOpen V ∧
      (∃ (d : ℕ) (e : MvPolynomial (Fin d) Γ(Spec A, ⊤) →+* Γ(trivialDef σ f, V)),
        e.comp MvPolynomial.C = ((trivialMap σ f).appLE ⊤ V le_top).hom ∧ e.Etale) ∧
      ∃ U : X.Opens, IsAffineOpen U ∧
        (∃ (d : ℕ) (e : MvPolynomial (Fin d) Γ(Spec A, ⊤) →+* Γ(X, U)),
          e.comp MvPolynomial.C = (f.appLE ⊤ U le_top).hom ∧ e.Etale) ∧
        trivialIncl hσ f ⁻¹ᵁ V ≤ specialIncl f ⁻¹ᵁ U})
    [IsAffineHom (graphNbhdFst hσ f N)] [IsAffineHom (graphNbhdSnd hσ f N)] :
    Nonempty (derivedDeRhamDirectImage f ≅ derivedDeRhamDirectImage (trivialMap σ f)) := by
  have hX : QuasiIso (Stacks.DeRhamPullback.deRhamPushforwardChain (graphNbhdFst hσ f N) f) :=
    quasiIso_deRhamPushforwardChain_of_sections _ _ h₁ (comp_comp_id _ _) fun U hU => by
      obtain ⟨hUa, -, V, hV, ⟨d, e, he, het⟩, hUV⟩ := hU
      exact quasiIso_sections_of_quasiIso_deRhamComplexMap _ f hUa
        (hUa.preimage (graphNbhdFst hσ f N)) (isAffineOpen_top _) le_top
        (quasiIso_chartFst hσ f N hN0 hN hUa hV hUV e he het)
  have hX' : QuasiIso
      (Stacks.DeRhamPullback.deRhamPushforwardChain (graphNbhdSnd hσ f N) (trivialMap σ f)) :=
    quasiIso_deRhamPushforwardChain_of_sections _ _ h₂ (comp_comp_id _ _) fun V hV => by
      obtain ⟨hVa, -, U, hU, ⟨d, e, he, het⟩, hVU⟩ := hV
      exact quasiIso_sections_of_quasiIso_deRhamComplexMap _ (trivialMap σ f) hVa
        (hVa.preimage (graphNbhdSnd hσ f N)) (isAffineOpen_top _) le_top
        (quasiIso_chartSnd hσ f N hN0 hN hU hVa hVU e he het)
  exact ⟨derivedDeRhamDirectImageIsoOfQuasiIso _ f hX ≪≫
    eqToIso (congrArg derivedDeRhamDirectImage (graphNbhdFst_comp hσ f N)) ≪≫
    (derivedDeRhamDirectImageIsoOfQuasiIso _ (trivialMap σ f) hX').symm⟩

end Rigidity

open Stacks.DeRhamDirectImage in
/-- **Rigidity of de Rham cohomology over an Artinian `ℚ`-algebra.** Let `A` be an Artinian local
`ℚ`-algebra with a coefficient field `σ : A/𝔪 → A`, and let `f : X ⟶ Spec A` be proper and
smooth. Then `Rf_*Ω^•_{X/A}` is isomorphic in `D⁺(𝒪_{Spec A})` to `Rf'_*Ω^•_{X'/A}` for the
trivial deformation `X' = X₀ ×_{A/𝔪} Spec A` of the special fibre `X₀` of `X`. -/
theorem nonempty_derivedDeRhamDirectImage_iso_trivialMap (A : CommRingCat.{u}) [IsArtinianRing A]
    [IsLocalRing A] [Algebra ℚ A] (σ : A ⧸ IsLocalRing.maximalIdeal A →+* A)
    (hσ : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)).comp σ = RingHom.id _)
    (X : Scheme.{u}) (f : X ⟶ Spec A) [IsProper f] [Smooth f] :
    Nonempty (derivedDeRhamDirectImage f ≅ derivedDeRhamDirectImage (trivialMap σ f)) := by
  obtain ⟨N, hN0, hN⟩ := exists_maximalIdeal_pow_eq_bot A
  exact nonempty_derivedDeRhamDirectImage_iso_trivialMap_of_charts hσ f N hN0 hN
    (isBasis_chartsFst hσ f) (isBasis_chartsSnd hσ f)

end Stacks.DeRhamRigidity
