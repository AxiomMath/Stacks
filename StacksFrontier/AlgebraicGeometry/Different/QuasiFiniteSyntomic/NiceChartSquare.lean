module

public import StacksFrontier.AlgebraicGeometry.Different.QuasiFiniteSyntomic.UniversalFamilyNiceCharts

/-!
# Nice universal chart squares

Let `f : Y ⟶ X` be a locally quasi-finite syntomic morphism of schemes and `y` a point of `Y`.
This file shows that `f` is, near `y`, the base change of a nice chart `N = Spec(B₀[1/h]) ⟶
M = Spec(ℤ[σ])` of the universal family of Example 0FK8, as in the proof of Tag 0FLA: there are
affine opens `y ∈ V ⊆ Y` and `U ⊆ X` with `f(V) ⊆ U` and a morphism `a : U ⟶ M` for which
`V ≅ U ×_M N`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isOpenImmersion_lift_resLE`: the restriction of `f` to opens
  `V ≤ f⁻¹ U` maps `V` by an open immersion into the fibre product `Y ×_X U`.
* `AlgebraicGeometry.exists_niceChartSquare`: the nice universal chart square around a point.

## Implementation notes

The open `V` is a basic open `D(h̄)` of the affine open `V₁` of Stacks 0BWE (5), where `h̄` is the
image of `h` under `B₀ → Γ(X, U) ⊗_{ℤ[σ]} B₀ ≅ Γ(Y, V₁)`. The square of rings with corners
`ℤ[σ]`, `Γ(X, U)`, `B₀[1/h]` and `Γ(Y, V) = Γ(Y, V₁)[1/h̄]` is the composite of the cocartesian
square of the base change `Γ(Y, V₁) = Γ(X, U) ⊗_{ℤ[σ]} B₀` with the cocartesian square of the
localizations at `h` and `h̄`, so it is cocartesian, and its spectrum is the required cartesian
square.

## References

* [Stacks Project, Tag 0FLA](https://stacks.math.columbia.edu/tag/0FLA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- The restriction `f.resLE U V e : V ⟶ U` of a morphism `f : Y ⟶ X` to opens with
`V ≤ f⁻¹ U`, together with the inclusion of `V`, maps `V` by an open immersion into the fibre
product `Y ×_X U`. -/
theorem Scheme.Hom.isOpenImmersion_lift_resLE {X Y : Scheme.{u}} (f : Y ⟶ X)
    {U : X.Opens} {V : Y.Opens} (e : V ≤ f ⁻¹ᵁ U) :
    IsOpenImmersion (pullback.lift V.ι (f.resLE U V e) (Scheme.Hom.resLE_comp_ι f e).symm) := by
  have : IsOpenImmersion
      (pullback.lift V.ι (f.resLE U V e) (Scheme.Hom.resLE_comp_ι f e).symm ≫
        pullback.fst f U.ι) := by
    rw [pullback.lift_fst]
    infer_instance
  exact IsOpenImmersion.of_comp _ (pullback.fst f U.ι)

/-- A point `x` of an affine open `V` lies in `D(r)` when `r` is not in its prime ideal. -/
private theorem IsAffineOpen.mem_basicOpen_of_notMem_primeIdealOf {X : Scheme.{u}}
    {V : X.Opens} (hV : IsAffineOpen V) (x : V) {r : Γ(X, V)}
    (hr : r ∉ (hV.primeIdealOf x).asIdeal) :
    x.1 ∈ X.basicOpen r := by
  have h1 : hV.primeIdealOf x ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen r := by
    rw [hV.fromSpec_preimage_basicOpen r]
    exact (PrimeSpectrum.mem_basicOpen r _).mpr hr
  have h2 : hV.fromSpec (hV.primeIdealOf x) ∈ X.basicOpen r := h1
  rwa [hV.fromSpec_primeIdealOf x] at h2

/-- For a pullback square, the induced map into the chosen pullback is an isomorphism. -/
private theorem _root_.CategoryTheory.IsPullback.isIso_lift {C : Type*} [Category C]
    {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g]
    (hP : IsPullback fst snd f g) : IsIso (pullback.lift fst snd hP.w) := by
  have : pullback.lift fst snd hP.w = hP.isoPullback.hom := by
    refine pullback.hom_ext ?_ ?_
    · rw [hP.isoPullback_hom_fst]
      exact pullback.lift_fst _ _ _
    · rw [hP.isoPullback_hom_snd]
      exact pullback.lift_snd _ _ _
  rw [this]
  infer_instance

/-- For affine opens `V ≤ f⁻¹ U` and a cocartesian square of rings `R → Γ(X, U)`, `R → L`,
`Γ(X, U) → Γ(Y, V) ← L` whose map `Γ(X, U) → Γ(Y, V)` is `f.appLE`, the square of spectra formed by
`f.resLE U V e` is cartesian. -/
private theorem Scheme.Hom.isPullback_resLE_of_isPushout {X Y : Scheme.{u}} (f : Y ⟶ X)
    {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    {R L : Type u} [CommRing R] [CommRing L] [Algebra R Γ(X, U)] [Algebra R L]
    [Algebra Γ(X, U) Γ(Y, V)] [Algebra L Γ(Y, V)] [Algebra R Γ(Y, V)]
    [IsScalarTower R Γ(X, U) Γ(Y, V)]
    [IsScalarTower R L Γ(Y, V)] [Algebra.IsPushout R Γ(X, U) L Γ(Y, V)]
    (happ : f.appLE U V e = CommRingCat.ofHom (algebraMap Γ(X, U) Γ(Y, V))) :
    IsPullback (hV.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap L Γ(Y, V))))
      (f.resLE U V e) (Spec.map (CommRingCat.ofHom (algebraMap R L)))
      (hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U)))) := by
  refine (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_of_isPushout
    R Γ(X, U) L Γ(Y, V))).flip.of_iso hV.isoSpec.symm (Iso.refl _) hU.isoSpec.symm (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp
  · rw [Iso.symm_hom, Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq, ← happ]
    exact Scheme.Opens.toSpecΓ_SpecMap_appLE f U _ e
  · simp
  · simp

/-- Given affine opens `V ≤ f⁻¹ U` and a cocartesian square of rings `R → Γ(X, U)`, `R → B`,
`Γ(X, U) → Γ(Y, V) ← B` whose map `Γ(X, U) → Γ(Y, V)` is `f.appLE`, for `h ∈ B` with image `h̄`
the square of spectra formed by `f.resLE` on `D(h̄)` and `Spec B[1/h] ⟶ Spec R` is cartesian. -/
private theorem Scheme.Hom.exists_isPullback_resLE_basicOpen {X Y : Scheme.{u}} (f : Y ⟶ X)
    {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U)
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] [Algebra R Γ(X, U)]
    [Algebra Γ(X, U) Γ(Y, V)] [Algebra B Γ(Y, V)] [Algebra R Γ(Y, V)]
    [IsScalarTower R Γ(X, U) Γ(Y, V)] [IsScalarTower R B Γ(Y, V)]
    [Algebra.IsPushout R B Γ(X, U) Γ(Y, V)]
    (hf : f.appLE U V hVU = CommRingCat.ofHom (algebraMap Γ(X, U) Γ(Y, V))) (h : B)
    (e : Y.basicOpen (algebraMap B Γ(Y, V) h) ≤ f ⁻¹ᵁ U) :
    ∃ b : (Y.basicOpen (algebraMap B Γ(Y, V) h)).toScheme ⟶ Spec (.of (Localization.Away h)),
      IsPullback b (f.resLE U _ e) (Spec.map (CommRingCat.ofHom
        (algebraMap R (Localization.Away h))))
        (hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U)))) := by
  let hb : Γ(Y, V) := algebraMap B Γ(Y, V) h
  -- the cocartesian square of the localizations at `h` and `h̄`
  have hloc : IsLocalization.Away hb Γ(Y, Y.basicOpen hb) := hV.isLocalization_basicOpen hb
  let ρ := algebraMap Γ(Y, V) Γ(Y, Y.basicOpen hb)
  let _ : Algebra Γ(X, U) Γ(Y, Y.basicOpen hb) := (ρ.comp (algebraMap Γ(X, U) Γ(Y, V))).toAlgebra
  let _ : Algebra R Γ(Y, Y.basicOpen hb) := (ρ.comp (algebraMap R Γ(Y, V))).toAlgebra
  let _ : Algebra B Γ(Y, Y.basicOpen hb) := (ρ.comp (algebraMap B Γ(Y, V))).toAlgebra
  have hunit : IsUnit (algebraMap B Γ(Y, Y.basicOpen hb) h) :=
    IsLocalization.Away.algebraMap_isUnit (S := Γ(Y, Y.basicOpen hb)) hb
  let _ : Algebra (Localization.Away h) Γ(Y, Y.basicOpen hb) :=
    (IsLocalization.Away.lift h hunit).toAlgebra
  have : IsScalarTower R Γ(X, U) Γ(Y, Y.basicOpen hb) :=
    .of_algebraMap_eq fun x ↦ congrArg ρ (IsScalarTower.algebraMap_apply R Γ(X, U) Γ(Y, V) x)
  have : IsScalarTower R Γ(Y, V) Γ(Y, Y.basicOpen hb) := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower Γ(X, U) Γ(Y, V) Γ(Y, Y.basicOpen hb) := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower B Γ(Y, V) Γ(Y, Y.basicOpen hb) := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower B (Localization.Away h) Γ(Y, Y.basicOpen hb) :=
    .of_algebraMap_eq fun x ↦
      (IsLocalization.Away.lift_eq (S := Localization.Away h) h hunit x).symm
  have : IsScalarTower R (Localization.Away h) Γ(Y, Y.basicOpen hb) :=
    .of_algebraMap_eq fun x ↦ by
      rw [IsScalarTower.algebraMap_apply R B (Localization.Away h),
        ← IsScalarTower.algebraMap_apply B (Localization.Away h) Γ(Y, Y.basicOpen hb),
        IsScalarTower.algebraMap_apply B Γ(Y, V) Γ(Y, Y.basicOpen hb),
        ← IsScalarTower.algebraMap_apply R B Γ(Y, V)]
      rfl
  have : IsLocalization (Algebra.algebraMapSubmonoid Γ(Y, V) (Submonoid.powers h))
      Γ(Y, Y.basicOpen hb) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact hloc
  have hpo : Algebra.IsPushout B (Localization.Away h) Γ(Y, V) Γ(Y, Y.basicOpen hb) :=
    (Algebra.isPushout_of_isLocalization (Submonoid.powers h) (Localization.Away h) Γ(Y, V)
      Γ(Y, Y.basicOpen hb)).symm
  -- the composite square
  have : Algebra.IsPushout R Γ(X, U) (Localization.Away h) Γ(Y, Y.basicOpen hb) :=
    ((Algebra.IsPushout.comp_iff R B Γ(X, U) (T := Localization.Away h) (S' := Γ(Y, V))
      (T' := Γ(Y, Y.basicOpen hb))).mpr hpo).symm
  refine ⟨_, f.isPullback_resLE_of_isPushout hU (hV.basicOpen hb) e ?_⟩
  rw [← f.appLE_map hVU (homOfLE (Y.basicOpen_le hb)).op, hf]
  rfl

/-- **The nice universal chart square of the proof of Tag 0FLA.** Let `f : Y ⟶ X` be locally
quasi-finite and syntomic and `y ∈ Y`. Then there are affine opens `y ∈ V ⊆ Y` and `U ⊆ X` with
`f(V) ⊆ U`, a square presentation `P₀` of an algebra `B₀` over `A₀ = ℤ[σ]`, an element `h ∈ B₀`
such that `B₀[1/h]` is a domain, quasi-finite and syntomic over `A₀`, in which the Jacobian
determinant of `P₀` is nonzero, and morphisms `a : U ⟶ Spec A₀` and `b : V ⟶ Spec B₀[1/h]`
for which the square formed by `f.resLE`, `a`, `b` and `Spec B₀[1/h] ⟶ Spec A₀` is cartesian:
`V ≅ U ×_{Spec A₀} Spec B₀[1/h]`. -/
theorem exists_niceChartSquare {X Y : Scheme.{u}} (f : Y ⟶ X)
    [LocallyQuasiFinite f] (hf : Syntomic f) (y : Y) :
    ∃ (U : X.affineOpens) (V : Y.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1) (σ B₀ : Type u)
      (_ : CommRing B₀) (_ : Algebra (MvPolynomial σ ℤ) B₀) (n : ℕ)
      (P₀ : Algebra.Presentation (MvPolynomial σ ℤ) B₀ (Fin n) (Fin n)) (h : B₀)
      (a : U.1.toScheme ⟶ Spec (.of (MvPolynomial σ ℤ)))
      (b : V.1.toScheme ⟶ Spec (.of (Localization.Away h)))
      (w : b ≫ Spec.map (CommRingCat.ofHom
          (algebraMap (MvPolynomial σ ℤ) (Localization.Away h))) =
        f.resLE U.1 V.1 e ≫ a),
      y ∈ V.1 ∧ IsOpenImmersion (pullback.lift b (f.resLE U.1 V.1 e) w) ∧
      IsDomain (Localization.Away h) ∧
      algebraMap B₀ (Localization.Away h) P₀.relationJacobiMatrix.det ≠ 0 ∧
      Algebra.QuasiFinite (MvPolynomial σ ℤ) (Localization.Away h) ∧
      Algebra.Syntomic (MvPolynomial σ ℤ) (Localization.Away h) := by
  -- a square presentation `Γ(Y, V₁) = Γ(X, U)[x_1, …, x_n]/(g_1, …, g_n)` with `n > 0`
  obtain ⟨V₁, U, hyV₁, hVU, n, -, hn, -, -, P, -⟩ :=
    exists_universalPolynomial_specialization
      (hasLocalSquareRelativeGlobalCompleteIntersection_of_locallyQuasiFinite_syntomic ‹_› hf) y
  let _ : Algebra Γ(X, U.1) Γ(Y, V₁.1) := (f.appLE U.1 V₁.1 hVU).hom.toAlgebra
  have : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V₁.1) :=
    (HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite) (Q := RingHom.QuasiFinite)).mp
      ‹_› U V₁ hVU
  -- the nice universal chart at the point of `Spec Γ(Y, V₁)` corresponding to `y`
  obtain ⟨σ, B₀, _, _, P₀, φ, hφ, h, hdom, hjac, hqf, hsyn, hq⟩ :=
    exists_universalChart_of_quasiFiniteAt P (V₁.2.primeIdealOf ⟨y, hyV₁⟩).asIdeal
  -- the cocartesian square of the base change `Γ(Y, V₁) = Γ(X, U) ⊗_{ℤ[σ]} B₀`
  let _ : Algebra (MvPolynomial σ ℤ) Γ(X, U.1) := φ.toAlgebra
  let _ : Algebra (MvPolynomial σ ℤ) Γ(Y, V₁.1) :=
    ((algebraMap Γ(X, U.1) Γ(Y, V₁.1)).comp φ).toAlgebra
  have : IsScalarTower (MvPolynomial σ ℤ) Γ(X, U.1) Γ(Y, V₁.1) := .of_algebraMap_eq fun _ ↦ rfl
  let E := P₀.tensorEquivOfRelation P hφ
  let _ : Algebra B₀ Γ(Y, V₁.1) := (E.toRingHom.comp (Algebra.TensorProduct.includeRight
    (R := MvPolynomial σ ℤ) (A := Γ(X, U.1)) (B := B₀)).toRingHom).toAlgebra
  have : IsScalarTower (MvPolynomial σ ℤ) B₀ Γ(Y, V₁.1) := .of_algebraMap_eq fun x ↦ by
    change algebraMap (MvPolynomial σ ℤ) Γ(Y, V₁.1) x =
      E ((1 : Γ(X, U.1)) ⊗ₜ[MvPolynomial σ ℤ] algebraMap (MvPolynomial σ ℤ) B₀ x)
    refine (E.commutes (algebraMap (MvPolynomial σ ℤ) Γ(X, U.1) x)).symm.trans (congrArg E ?_)
    exact (Algebra.TensorProduct.algebraMap_apply (R := MvPolynomial σ ℤ)
      (S := MvPolynomial σ ℤ) x).symm.trans (Algebra.TensorProduct.algebraMap_apply' x)
  have hpo₁ : Algebra.IsPushout (MvPolynomial σ ℤ) B₀ Γ(X, U.1) Γ(Y, V₁.1) :=
    (⟨IsBaseChange.of_equiv E.toLinearEquiv fun _ ↦ rfl⟩ :
      Algebra.IsPushout (MvPolynomial σ ℤ) Γ(X, U.1) B₀ Γ(Y, V₁.1)).symm
  -- the basic open `V = D(h̄)`
  let hb : Γ(Y, V₁.1) := algebraMap B₀ Γ(Y, V₁.1) h
  have hyV : y ∈ Y.basicOpen hb := V₁.2.mem_basicOpen_of_notMem_primeIdealOf ⟨y, hyV₁⟩ hq
  have e : Y.basicOpen hb ≤ f ⁻¹ᵁ U.1 := (Y.basicOpen_le hb).trans hVU
  obtain ⟨b, hP⟩ := f.exists_isPullback_resLE_basicOpen (R := MvPolynomial σ ℤ) U.2 V₁.2 hVU
    (by exact rfl) h e
  refine ⟨U, ⟨Y.basicOpen hb, V₁.2.basicOpen hb⟩, e, σ, B₀, inferInstance, inferInstance, n, P₀,
    h, _, b, hP.w, hyV, ?_, hdom, hjac, hqf, hsyn⟩
  have := hP.isIso_lift
  infer_instance

end AlgebraicGeometry

end
