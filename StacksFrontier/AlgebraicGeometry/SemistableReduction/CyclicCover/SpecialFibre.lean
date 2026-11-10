module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.CyclicCover.Regular
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.RingTheory.RegularLocalRing.Basic

/-!
# The special fibre of the cyclic cover is `n` times its reduction

Let `X ⟶ Z_R` be the cyclic cover `Spec_{Z_R}(Sym(L_R)/(φ - π))` over `R = k[[π]]` of
[Stacks, Tag 0CEH], with `Z` smooth over `k` and `n` invertible in `k`. Its special fibre is the
effective Cartier divisor `X_k = V(π)` cut out by the uniformizer. Over a trivializing affine open
of `Z` the chart ring is `(A ⊗_k R)[x]/(xⁿ - π f)` with `f` a unit, so `π = f⁻¹ xⁿ` and

`(π) = (x)ⁿ`, with `(x)` the radical of `(π)`,

because the quotient by `x` is `(A ⊗_k R)/(π)`, which is regular, hence reduced. Hence **`X_k` is
`n` times the reduced special fibre `(X_k)_{red} = V(x)` as an effective Cartier divisor.**

## Main definitions

* `Stacks.CyclicCover.uniformizerFunction`: the image of `π` in `Γ(X, 𝒪_X)`.
* `Stacks.CyclicCover.specialFibreIdeal`: the ideal sheaf `π 𝒪_X` of the special fibre.

## Main results

* `Stacks.CyclicCover.isEffectiveCartierDivisor_specialFibreIdeal`,
  `Stacks.CyclicCover.isEffectiveCartierDivisor_radical_specialFibreIdeal`,
  `Stacks.CyclicCover.specialFibreIdeal_eq_radical_pow`: `X_k` and `(X_k)_{red}` are effective
  Cartier divisors, and `X_k = n (X_k)_{red}`.

## References

* [Stacks Project, Tag 0CEH](https://stacks.math.columbia.edu/tag/0CEH)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace Polynomial
open scoped TensorProduct

universe u

namespace Stacks.CyclicCover

/-- A regular ring is reduced: its local rings are regular local rings, hence domains. -/
theorem isReduced_of_isRegularRing (A : Type*) [CommRing A] [IsRegularRing A] : IsReduced A :=
  isReduced_ofLocalizationMaximal _ fun p _ =>
    have := IsRegularLocalRing.isDomain (Localization.AtPrime p)
    inferInstance

/-- A global function restricted to an open `U`, read on `U` as a scheme. -/
theorem topIso_hom_ι_appTop {X : Scheme.{u}} (U : X.Opens) (x : Γ(X, ⊤)) :
    U.topIso.hom (U.ι.appTop x) = X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op x := by
  simp only [Scheme.Opens.topIso_hom, Scheme.Opens.ι_appTop]
  exact ConcreteCategory.congr_hom (X.presheaf.map_comp _ _).symm x

variable {k : Type u} [Field k] {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k)) {L : Z.Modules}
  [SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property L] {n : ℕ}
  (φ : (situation f L).symmetricAlgebra.piece (n : ℤ) ≅ SheafOfModules.unit Z.ringCatSheaf)

/-- The cyclic cover `X` over `R = k[[π]]`, with `c = π`. -/
abbrev coverR : Scheme.{u} := cover f φ (PowerSeries k) PowerSeries.X

/-- **The uniformizer `π` as a global function on `X`.** -/
def uniformizerFunction : Γ(coverR f φ, ⊤) :=
  (coverSnd f φ (PowerSeries k) PowerSeries.X).appTop
    ((Scheme.ΓSpecIso (.of (PowerSeries k))).inv PowerSeries.X)

/-- **The ideal sheaf `π 𝒪_X` of the special fibre `X_k = V(π)`.** -/
def specialFibreIdeal : (coverR f φ).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (Ideal.span {uniformizerFunction f φ})

section Chart

variable (U : Z.affineOpens) (b : Module.Basis PUnit.{u + 1} Γ(Z, U.1) Γ(L, U.1))

/-- The functions on the chart `p⁻¹(U_R)` of `X` are the chart ring. -/
def chartSectionsEquiv :
    letI := (sectionsStructure f U.1).hom.toAlgebra
    chartRing k n (chartCoeff f φ U b) (PowerSeries.X : PowerSeries k) ≃+*
      Γ(coverR f φ, coverOpen f φ U (PowerSeries k) PowerSeries.X) :=
  letI := (sectionsStructure f U.1).hom.toAlgebra
  ((Scheme.ΓSpecIso _).symm ≪≫ Scheme.Γ.mapIso (coverOpenIso f φ U b _ _).op ≪≫
    (coverOpen f φ U (PowerSeries k) PowerSeries.X).topIso).commRingCatIsoToRingEquiv

/-- Under `chartSectionsEquiv`, the image of `1 ⊗ π` in the chart ring is the restriction of
`uniformizerFunction` to the chart `p⁻¹(U_R)`. -/
theorem chartSectionsEquiv_uniformizer :
    letI := (sectionsStructure f U.1).hom.toAlgebra
    chartSectionsEquiv f φ U b (algebraMap (Γ(Z, U.1) ⊗[k] PowerSeries k) _
        ((1 : Γ(Z, U.1)) ⊗ₜ[k] (PowerSeries.X : PowerSeries k))) =
      ((coverR f φ).presheaf.map (homOfLE le_top).op).hom (uniformizerFunction f φ) := by
  let := (sectionsStructure f U.1).hom.toAlgebra
  have h1 : (coverOpenIso f φ U b (PowerSeries k) PowerSeries.X).hom ≫
      Spec.map (CommRingCat.ofHom (chartRight k n (chartCoeff f φ U b) PowerSeries.X)) =
      (coverOpen f φ U (PowerSeries k) PowerSeries.X).ι ≫ coverSnd f φ (PowerSeries k)
        PowerSeries.X :=
    IsPullback.isoIsPullback_hom_snd _ _ _ _
  have h2 := congrArg (fun g => ((Scheme.ΓSpecIso (.of (PowerSeries k))).inv ≫
    Scheme.Hom.appTop g).hom (PowerSeries.X : PowerSeries k)) h1
  simp only [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality] at h2
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  change (coverOpen f φ U (PowerSeries k) PowerSeries.X).topIso.hom
    ((coverOpenIso f φ U b (PowerSeries k) PowerSeries.X).hom.appTop
      ((Scheme.ΓSpecIso _).inv (chartRight k n (chartCoeff f φ U b) PowerSeries.X
        PowerSeries.X))) = _
  rw [h2, uniformizerFunction]
  exact topIso_hom_ι_appTop _ _

include b in
/-- Over a trivializing affine open `U` of `Z`, the chart `p⁻¹(U_R)` of `X` is affine. -/
theorem isAffineOpen_coverOpen :
    IsAffineOpen (coverOpen f φ U (PowerSeries k) PowerSeries.X) :=
  let := (sectionsStructure f U.1).hom.toAlgebra
  IsAffine.of_isIso (coverOpenIso f φ U b (PowerSeries k) PowerSeries.X).hom

omit [SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property L] in
/-- A ring isomorphism maps nonzerodivisors to nonzerodivisors. -/
theorem ringEquiv_mem_nonZeroDivisors {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    {a : A} (ha : a ∈ nonZeroDivisors A) : e a ∈ nonZeroDivisors B := by
  rw [← MulEquivClass.map_nonZeroDivisors e]
  exact Submonoid.mem_map_of_mem _ ha

/-- A natural number whose image in a field is nonzero is nonzero. -/
private theorem ne_zero_of_cast_ne_zero {k : Type*} [Field k] {n : ℕ} (hn : (n : k) ≠ 0) :
    n ≠ 0 := by
  rintro rfl
  simp at hn

/-- **The special fibre on a chart**: on `p⁻¹(U_R)`, with `r` the image of `x`, the ideal of the
special fibre is `(π) = (r)ⁿ`, where `π` and `r` are nonzerodivisors and `(r)` is radical. -/
theorem exists_chart_specialFibreIdeal [Smooth f] (hn : (n : k) ≠ 0) :
    ∃ r p : Γ(coverR f φ, coverOpen f φ U (PowerSeries k) PowerSeries.X),
      r ∈ nonZeroDivisors _ ∧ p ∈ nonZeroDivisors _ ∧ (Ideal.span {r}).IsRadical ∧
      (specialFibreIdeal f φ).ideal ⟨_, isAffineOpen_coverOpen f φ U b⟩ = Ideal.span {p} ∧
      Ideal.span {p} = Ideal.span {r} ^ n := by
  let := (sectionsStructure f U.1).hom.toAlgebra
  have := smooth_sections f U
  have hn0 := ne_zero_of_cast_ne_zero hn
  have hgc : rootCoeff f φ U b * chartCoeff f φ U b = 1 := rootCoeff_mul_chartCoeff f φ U b
  have hu : (chartCoeff f φ U b ⊗ₜ[k] (PowerSeries.X : PowerSeries k) :
      Γ(Z, U.1) ⊗[k] PowerSeries k) = (chartCoeff f φ U b ⊗ₜ[k] 1) *
        ((1 : Γ(Z, U.1)) ⊗ₜ[k] (PowerSeries.X : PowerSeries k)) := by simp
  have hcu : IsUnit (chartCoeff f φ U b ⊗ₜ[k] (1 : PowerSeries k) :
      Γ(Z, U.1) ⊗[k] PowerSeries k) :=
    (IsUnit.of_mul_eq_one_right _ hgc).map Algebra.TensorProduct.includeLeftRingHom
  have hgu : IsUnit (algebraMap (Γ(Z, U.1) ⊗[k] PowerSeries k)
      (chartRing k n (chartCoeff f φ U b) (PowerSeries.X : PowerSeries k))
      (rootCoeff f φ U b ⊗ₜ[k] (1 : PowerSeries k))) :=
    ((IsUnit.of_mul_eq_one _ hgc).map Algebra.TensorProduct.includeLeftRingHom).map _
  have ht : algebraMap (Γ(Z, U.1) ⊗[k] PowerSeries k)
      (chartRing k n (chartCoeff f φ U b) (PowerSeries.X : PowerSeries k))
      ((1 : Γ(Z, U.1)) ⊗ₜ[k] (PowerSeries.X : PowerSeries k)) =
      algebraMap _ _ (rootCoeff f φ U b ⊗ₜ[k] (1 : PowerSeries k)) *
        AdjoinRoot.root _ ^ n := by
    rw [root_pow n (chartCoeff f φ U b) (PowerSeries.X : PowerSeries k), ← map_mul,
      Algebra.TensorProduct.tmul_mul_tmul, hgc, one_mul]
  have hQt := tmul_X_mem_nonZeroDivisors (k := k) Γ(Z, U.1)
  have hQu : (chartCoeff f φ U b ⊗ₜ[k] (PowerSeries.X : PowerSeries k) :
      Γ(Z, U.1) ⊗[k] PowerSeries k) ∈ nonZeroDivisors _ := by
    rw [hu]; exact Submonoid.mul_mem _ hcu.mem_nonZeroDivisors hQt
  have := free_adjoinRoot (chartCoeff f φ U b ⊗ₜ[k] (PowerSeries.X : PowerSeries k) :
      Γ(Z, U.1) ⊗[k] PowerSeries k) hn0
  have htB : algebraMap (Γ(Z, U.1) ⊗[k] PowerSeries k)
      (chartRing k n (chartCoeff f φ U b) (PowerSeries.X : PowerSeries k))
      ((1 : Γ(Z, U.1)) ⊗ₜ[k] (PowerSeries.X : PowerSeries k)) ∈ nonZeroDivisors _ := by
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors
      (M := chartRing k n (chartCoeff f φ U b) (PowerSeries.X : PowerSeries k)) hQt
    refine mem_nonZeroDivisors_iff.2 ⟨fun c hc => hreg ?_, fun c hc => hreg ?_⟩
    · change _ • c = _ • 0; rw [smul_zero, Algebra.smul_def]; exact hc
    · change _ • c = _ • 0; rw [smul_zero, Algebra.smul_def, mul_comm]; exact hc
  have hxB := root_mem_nonZeroDivisors _ hn0 hQu
  have hrad : (Ideal.span {AdjoinRoot.root (Polynomial.X ^ n - C (chartCoeff f φ U b ⊗ₜ[k]
      (PowerSeries.X : PowerSeries k)))}).IsRadical := by
    rw [Ideal.isRadical_iff_quotient_reduced]
    have := isRegularRing_tensor_powerSeries_quot (k := k) Γ(Z, U.1)
    have e := (quotRootEquiv (chartCoeff f φ U b ⊗ₜ[k] (PowerSeries.X : PowerSeries k) :
      Γ(Z, U.1) ⊗[k] PowerSeries k) hn0).trans
      (Ideal.quotEquivOfEq (by rw [hu, Ideal.span_singleton_mul_left_unit hcu]))
    have := IsRegularRing.of_ringEquiv e.symm
    exact isReduced_of_isRegularRing _
  refine ⟨chartSectionsEquiv f φ U b (AdjoinRoot.root _),
    ((coverR f φ).presheaf.map (homOfLE le_top).op).hom (uniformizerFunction f φ),
    ringEquiv_mem_nonZeroDivisors _ hxB, ?_, ?_, ?_, ?_⟩
  · rw [← chartSectionsEquiv_uniformizer f φ U b]
    exact ringEquiv_mem_nonZeroDivisors _ htB
  · have e := Ideal.quotientEquiv _ (Ideal.span {chartSectionsEquiv f φ U b (AdjoinRoot.root _)})
      (chartSectionsEquiv f φ U b) (by rw [Ideal.map_span, Set.image_singleton]; rfl)
    rw [Ideal.isRadical_iff_quotient_reduced] at hrad ⊢
    exact isReduced_of_injective e.symm.toRingHom e.symm.injective
  · rw [specialFibreIdeal, Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_span,
      Set.image_singleton]
  · rw [← chartSectionsEquiv_uniformizer f φ U b, Ideal.span_singleton_pow, ht, map_mul, map_pow,
      Ideal.span_singleton_mul_left_unit (hgu.map _)]

/-- On a chart, the ideal of the reduced special fibre is `(r)` and that of the special fibre is
its `n`-th power. -/
private theorem exists_chart_radical_specialFibreIdeal [Smooth f] (hn : (n : k) ≠ 0) :
    ∃ r : Γ(coverR f φ, coverOpen f φ U (PowerSeries k) PowerSeries.X),
      r ∈ nonZeroDivisors _ ∧
      (specialFibreIdeal f φ).radical.ideal ⟨_, isAffineOpen_coverOpen f φ U b⟩ = Ideal.span {r} ∧
      (specialFibreIdeal f φ).ideal ⟨_, isAffineOpen_coverOpen f φ U b⟩ =
        (specialFibreIdeal f φ).radical.ideal ⟨_, isAffineOpen_coverOpen f φ U b⟩ ^ n := by
  obtain ⟨r, p, hr, -, hrad, hI, hpr⟩ := exists_chart_specialFibreIdeal f φ U b hn
  have hrr : (specialFibreIdeal f φ).radical.ideal ⟨_, isAffineOpen_coverOpen f φ U b⟩ =
      Ideal.span {r} := by
    rw [Scheme.IdealSheafData.radical_ideal, hI, hpr,
      Ideal.radical_pow _ (ne_zero_of_cast_ne_zero hn), hrad.radical]
  exact ⟨r, hr, hrr, by rw [hrr, hI, hpr]⟩

end Chart

/-- On an affine open `U`, the ideal of `I ^ m` is the `m`-th power of the ideal of `I`. -/
theorem ideal_pow {X : Scheme.{u}} (I : X.IdealSheafData) (m : ℕ) (U : X.affineOpens) :
    (I ^ m).ideal U = I.ideal U ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, ih, pow_succ]

/-- The charts `p⁻¹(U_R)`, for `U` ranging over the trivializing opens of `L`, cover `X`. -/
theorem iSup_coverOpen_trivialOpen :
    ⨆ U : TrivialOpen L, coverOpen f φ U.1 (PowerSeries k) PowerSeries.X = ⊤ := by
  have h := congrArg (coverMap f φ (PowerSeries k) PowerSeries.X ⁻¹ᵁ ·)
    (iSup_baseChangeOpen_trivialOpen f (L := L) (PowerSeries k))
  simp only [Scheme.Hom.preimage_iSup, Scheme.Hom.preimage_top] at h
  rw [← h]
  exact iSup_congr fun U => (preimage_baseChangeOpen f φ U.1 _ _).symm

/-- Every point of `X` lies in a chart `p⁻¹(U_R)` for some trivializing open `U` of `L`. -/
theorem exists_mem_coverOpen (x : coverR f φ) :
    ∃ U : TrivialOpen L, x ∈ coverOpen f φ U.1 (PowerSeries k) PowerSeries.X := by
  have : x ∈ (⊤ : (coverR f φ).Opens) := trivial
  rw [← iSup_coverOpen_trivialOpen f φ] at this
  exact Opens.mem_iSup.1 this

variable [Smooth f] (hn : (n : k) ≠ 0)
include hn

/-- **The special fibre `X_k = V(π)` is an effective Cartier divisor.** -/
theorem isEffectiveCartierDivisor_specialFibreIdeal :
    Stacks.Divisors.IsEffectiveCartierDivisor (specialFibreIdeal f φ) := by
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_forall_exists_affineOpen _ fun x => ?_
  obtain ⟨⟨U, ⟨b⟩⟩, hx⟩ := exists_mem_coverOpen f φ x
  obtain ⟨r, p, -, hp, -, hI, -⟩ := exists_chart_specialFibreIdeal f φ U b hn
  exact ⟨_, isAffineOpen_coverOpen f φ U b, hx, p, isRegular_iff_mem_nonZeroDivisors.2 hp, hI⟩

/-- **The reduced special fibre `(X_k)_{red}` is an effective Cartier divisor.** Its ideal is the
radical of `π 𝒪_X`, generated on each chart by the function `x`. -/
theorem isEffectiveCartierDivisor_radical_specialFibreIdeal :
    Stacks.Divisors.IsEffectiveCartierDivisor (specialFibreIdeal f φ).radical := by
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_forall_exists_affineOpen _ fun x => ?_
  obtain ⟨⟨U, ⟨b⟩⟩, hx⟩ := exists_mem_coverOpen f φ x
  obtain ⟨r, hr, hrr, -⟩ := exists_chart_radical_specialFibreIdeal f φ U b hn
  exact ⟨_, isAffineOpen_coverOpen f φ U b, hx, r, isRegular_iff_mem_nonZeroDivisors.2 hr, hrr⟩

/-- **`X_k = n (X_k)_{red}`**: the ideal of the special fibre is the `n`-th power of the ideal of
the reduced special fibre. -/
theorem specialFibreIdeal_eq_radical_pow :
    specialFibreIdeal f φ = (specialFibreIdeal f φ).radical ^ n := by
  classical
  let b : ∀ U : TrivialOpen L, Module.Basis PUnit.{u + 1} Γ(Z, U.1.1) Γ(L, U.1.1) :=
    fun U => U.2.some
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : TrivialOpen L => ⟨_, isAffineOpen_coverOpen f φ U.1 (b U)⟩)
    (iSup_coverOpen_trivialOpen f φ) fun U => ?_
  obtain ⟨-, -, -, h⟩ := exists_chart_radical_specialFibreIdeal f φ U.1 (b U) hn
  rw [ideal_pow]
  exact h

end Stacks.CyclicCover

end
