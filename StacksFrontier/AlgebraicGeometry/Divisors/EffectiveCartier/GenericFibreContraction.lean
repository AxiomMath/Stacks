module

public import StacksFrontier.AlgebraicGeometry.CartierAffineLocalConverse.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.InvertibleGlobalSections
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.BaseChangeDivisor
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.IdealSheafComap
public import StacksFrontier.RingTheory.Valuation.SmoothGenericContraction

/-!
# Extending an effective Cartier divisor from the generic fibre of a smooth scheme

Let `R` be a valuation ring with fraction field `K` and let `X` be a scheme smooth over `Spec R`,
with generic fibre `p : X_K ⟶ X`. If `b : T ⟶ X` is a quasi-compact morphism factoring through
`X_K`, then its kernel ideal `I` is the contraction of the ideal it cuts out on `X_K`; this file
shows that `I` is an effective Cartier divisor on `X` as soon as `p⁻¹I` is one on `X_K`. This is
the scheme-level step of Stacks 0DMC.

## Main results

* `Stacks.Divisors.isEffectiveCartierDivisor_of_generic_kernel`.

## Implementation notes

On an affine open `Spec A ⊆ X` the generic fibre is `Spec (A ⊗_R K)`, the ideal of `p⁻¹I` is an
invertible ideal of `A ⊗_R K` (`Stacks.Divisors.invertible_ideal_top_of_isEffectiveCartierDivisor`)
and `I(Spec A)` is its contraction to `A`, so the ring-theoretic statement
`Algebra.Smooth.exists_away_eq_span_isRegular_comap_genericFibre` produces local generators by
nonzerodivisors, which is the reverse direction of Stacks 01WS.

## References

* [Stacks Project, Tag 0DMC](https://stacks.math.columbia.edu/tag/0DMC)
* [Stacks Project, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct nonZeroDivisors

universe u

namespace Stacks.Divisors

open Algebra.Smooth

/-- Global sections turn an affine generic-fibre square into the tensor
product pushout over the original base ring. -/
private theorem isPushout_affine_generic_fibre
    {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    {X W : Scheme.{u}} [IsAffine X] [IsAffine W]
    (f : X ⟶ Spec (.of R)) (p : W ⟶ X)
    (q : W ⟶ Spec (.of K))
    (h : IsPullback p q f
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    [Algebra R Γ(X, ⊤)]
    (hf : CommRingCat.ofHom (algebraMap R Γ(X, ⊤)) =
      (Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop) :
    IsPushout (CommRingCat.ofHom (algebraMap R Γ(X, ⊤)))
      (CommRingCat.ofHom (algebraMap R K)) p.appTop
      ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appTop) := by
  have H : IsPushout f.appTop
      (Spec.map (CommRingCat.ofHom (algebraMap R K))).appTop
      p.appTop q.appTop := isPushout_appTop_of_isPullback h
  refine H.of_iso' (Scheme.ΓSpecIso (.of R)).symm (Iso.refl _)
    (Scheme.ΓSpecIso (.of K)).symm (Iso.refl _) ?_ ?_ ?_ ?_
  · exact hf.symm
  · simpa only [Iso.symm_hom] using
      (Scheme.ΓSpecIso_inv_naturality
        (CommRingCat.ofHom (algebraMap R K))).symm
  · simp
  · simp

/-- An ideal sheaf which, near every point of its support, is cut out on an affine open by a
single nonzerodivisor is an effective Cartier divisor (the reverse direction of Stacks 01WS). -/
private theorem isEffectiveCartierDivisor_of_affineLocal_span
    {X : Scheme.{u}} (I : X.IdealSheafData)
    (h : ∀ x ∈ I.supportSet,
      ∃ (U : X.Opens) (hU : IsAffineOpen U), x ∈ U ∧
        ∃ f : Γ(X, U), IsRegular f ∧ I.ideal ⟨U, hU⟩ = Ideal.span {f}) :
    IsEffectiveCartierDivisor I := by
  refine (Stacks.CartierAffineLocalConverse.isEffectiveCartierDivisor_iff_isRegular I).2
    fun x hx => ?_
  obtain ⟨U, hU, hxU, f, hf, hgen⟩ := h x hx
  exact ⟨⟨U, hU⟩, hxU, f, hf, hgen⟩

/-- The contraction of an invertible generic-fibre ideal in a smooth affine scheme
over a valuation ring defines an effective Cartier divisor. -/
private theorem isEffectiveCartierDivisor_of_affine_generic_contraction
    {R K : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} [IsAffine X]
    [Algebra R Γ(X, ⊤)] [Algebra.Smooth R Γ(X, ⊤)]
    (J : Ideal (Γ(X, ⊤) ⊗[R] K))
    [Module.Invertible (Γ(X, ⊤) ⊗[R] K) J]
    (I : X.IdealSheafData)
    (hI : I.ideal ⟨⊤, isAffineOpen_top X⟩ =
      J.comap (algebraMap Γ(X, ⊤) (Γ(X, ⊤) ⊗[R] K))) :
    Stacks.Divisors.IsEffectiveCartierDivisor I := by
  apply isEffectiveCartierDivisor_of_affineLocal_span I
  intro x hx
  let q : Ideal Γ(X, ⊤) :=
    ((isAffineOpen_top X).primeIdealOf ⟨x, Set.mem_univ x⟩).asIdeal
  obtain ⟨r, hr, f, hf, hgen⟩ :=
    Algebra.Smooth.exists_away_eq_span_isRegular_comap_genericFibre (R := R) J q
  let U : X.Opens := X.basicOpen r
  have hU : IsAffineOpen U := (isAffineOpen_top X).basicOpen r
  have hxU : x ∈ U := by
    change x ∈ X.basicOpen r
    have hr' : r ∉ ((isAffineOpen_top X).primeIdealOf
        ⟨x, Set.mem_univ x⟩).asIdeal := hr
    have hspec : (isAffineOpen_top X).primeIdealOf
        ⟨x, Set.mem_univ x⟩ ∈ PrimeSpectrum.basicOpen r :=
      (PrimeSpectrum.mem_basicOpen r _).2 hr'
    have hmem : (isAffineOpen_top X).fromSpec
        ((isAffineOpen_top X).primeIdealOf ⟨x, Set.mem_univ x⟩) ∈
        X.basicOpen r := by
      rw [← (isAffineOpen_top X).fromSpec_image_basicOpen r]
      exact ⟨_, hspec, rfl⟩
    simpa only [(isAffineOpen_top X).fromSpec_primeIdealOf] using hmem
  let S := Γ(X, U)
  let : Algebra Γ(X, ⊤) S :=
    (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom.toAlgebra
  let : IsLocalization.Away r S := (isAffineOpen_top X).isLocalization_basicOpen r
  let e : Localization.Away r ≃ₐ[Γ(X, ⊤)] S :=
    IsLocalization.algEquiv (Submonoid.powers r) (Localization.Away r) S
  let f' : S := e f
  have hf' : IsRegular f' := by
    rw [isRegular_iff_mem_nonZeroDivisors] at hf ⊢
    have h := Submonoid.mem_map_of_mem e.toRingEquiv hf
    rw [MulEquivClass.map_nonZeroDivisors] at h
    exact h
  have hmap : Ideal.map (algebraMap Γ(X, ⊤) S)
      (J.comap (algebraMap Γ(X, ⊤) (Γ(X, ⊤) ⊗[R] K))) =
      Ideal.span {f'} := by
    have he : Ideal.map e.toRingHom
        (Ideal.map (algebraMap Γ(X, ⊤) (Localization.Away r))
          (J.comap (algebraMap Γ(X, ⊤) (Γ(X, ⊤) ⊗[R] K)))) =
        Ideal.map (algebraMap Γ(X, ⊤) S)
          (J.comap (algebraMap Γ(X, ⊤) (Γ(X, ⊤) ⊗[R] K))) := by
      rw [Ideal.map_map]
      congr 1
      ext a
      exact e.commutes a
    rw [← he, hgen, Ideal.map_span]
    simp only [Set.image_singleton]
    rfl
  refine ⟨U, hU, hxU, f', hf', ?_⟩
  change I.ideal (X.affineBasicOpen (U := ⟨⊤, isAffineOpen_top X⟩) r) =
    Ideal.span {f'}
  rw [← I.map_ideal_basicOpen ⟨⊤, isAffineOpen_top X⟩ r, hI]
  exact hmap

/-- The affine contraction criterion expressed using a cartesian square of
affine schemes and its pushout square on global sections. -/
private theorem isEffectiveCartierDivisor_of_affine_generic_pushout
    {R K : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {X W : Scheme.{u}} [IsAffine X] [IsAffine W]
    [Algebra R Γ(X, ⊤)] [Algebra.Smooth R Γ(X, ⊤)]
    (p : W ⟶ X) (β : CommRingCat.of K ⟶ CommRingCat.of Γ(W, ⊤))
    (hP : IsPushout (CommRingCat.ofHom (algebraMap R Γ(X, ⊤)))
      (CommRingCat.ofHom (algebraMap R K)) p.appTop β)
    (I : X.IdealSheafData) (J : W.IdealSheafData)
    (hJ : Stacks.Divisors.IsEffectiveCartierDivisor J)
    (hSat : I.ideal ⟨⊤, isAffineOpen_top X⟩ =
      (J.ideal ⟨⊤, isAffineOpen_top W⟩).comap p.appTop.hom) :
    Stacks.Divisors.IsEffectiveCartierDivisor I := by
  let A := Γ(X, ⊤)
  let C := Γ(W, ⊤)
  let : Algebra A C := p.appTop.hom.toAlgebra
  let : Algebra K C := β.hom.toAlgebra
  let : Algebra R C :=
    (p.appTop.hom.comp (algebraMap R A)).toAlgebra
  have : IsScalarTower R A C := .of_algebraMap_eq' rfl
  have : IsScalarTower R K C := by
    apply IsScalarTower.of_algebraMap_eq'
    change p.appTop.hom.comp (algebraMap R A) = β.hom.comp (algebraMap R K)
    exact congrArg (fun f => f.hom) hP.w
  have : Algebra.IsPushout R A K C :=
    CommRingCat.isPushout_iff_isPushout.mp hP
  let e : A ⊗[R] K ≃ₐ[A] C := Algebra.IsPushout.equiv R A K C
  let L : Ideal (A ⊗[R] K) :=
    (J.ideal ⟨⊤, isAffineOpen_top W⟩).comap e.toRingHom
  let : Module.Invertible C (J.ideal ⟨⊤, isAffineOpen_top W⟩) :=
    invertible_ideal_top_of_isEffectiveCartierDivisor J hJ
  let : Module.Invertible (A ⊗[R] K) L :=
    Ideal.invertible_comap_ringEquiv e.toRingEquiv _
  have hI : I.ideal ⟨⊤, isAffineOpen_top X⟩ =
      L.comap (algebraMap A (A ⊗[R] K)) := by
    rw [hSat]
    ext a
    change p.appTop.hom a ∈ J.ideal ⟨⊤, isAffineOpen_top W⟩ ↔
      e (algebraMap A (A ⊗[R] K) a) ∈
        J.ideal ⟨⊤, isAffineOpen_top W⟩
    rw [e.commutes]
    rfl
  exact isEffectiveCartierDivisor_of_affine_generic_contraction L I hI

private theorem isEffectiveCartierDivisor_of_invertible_affineIdeals
    {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : ∀ U : X.affineOpens, Module.Invertible Γ(X, U.1) (I.ideal U)) :
    Stacks.Divisors.IsEffectiveCartierDivisor I := by
  apply isEffectiveCartierDivisor_of_affineLocal_span I
  intro x hx
  obtain ⟨V, hV, hxV, _⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by simp)
  let V' : X.affineOpens := ⟨V, hV⟩
  have : Module.Invertible Γ(X, V) (I.ideal V') := hI V'
  let q : Ideal Γ(X, V) :=
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have : Module.Invertible (Localization.AtPrime q)
      ((I.ideal V').map (algebraMap Γ(X, V) (Localization.AtPrime q))) :=
    Ideal.invertible_map_of_isLocalization q.primeCompl (I.ideal V')
  have : Module.FinitePresentation Γ(X, V) (I.ideal V') :=
    Module.finitePresentation_of_projective _ _
  obtain ⟨r, hr, f, hf, hgen⟩ :=
    Ideal.exists_away_eq_span_isRegular_of_invertible_atPrime (I.ideal V') q
  let U : X.Opens := X.basicOpen r
  have hU : IsAffineOpen U := hV.basicOpen r
  have hxU : x ∈ U := by
    change x ∈ X.basicOpen r
    have hr' : r ∉ (hV.primeIdealOf
        ⟨x, hxV⟩).asIdeal := hr
    have hspec : hV.primeIdealOf
        ⟨x, hxV⟩ ∈ PrimeSpectrum.basicOpen r :=
      (PrimeSpectrum.mem_basicOpen r _).2 hr'
    have hmem : hV.fromSpec
        (hV.primeIdealOf ⟨x, hxV⟩) ∈
        X.basicOpen r := by
      rw [← hV.fromSpec_image_basicOpen r]
      exact ⟨_, hspec, rfl⟩
    simpa only [hV.fromSpec_primeIdealOf] using hmem
  let S := Γ(X, U)
  let : Algebra Γ(X, V) S :=
    (X.presheaf.map (homOfLE (show U ≤ V from X.basicOpen_le r)).op).hom.toAlgebra
  let : IsLocalization.Away r S := hV.isLocalization_basicOpen r
  let e : Localization.Away r ≃ₐ[Γ(X, V)] S :=
    IsLocalization.algEquiv (Submonoid.powers r) (Localization.Away r) S
  let f' : S := e f
  have hf' : IsRegular f' := by
    rw [isRegular_iff_mem_nonZeroDivisors] at hf ⊢
    have h := Submonoid.mem_map_of_mem e.toRingEquiv hf
    rw [MulEquivClass.map_nonZeroDivisors] at h
    exact h
  have hmap : Ideal.map (algebraMap Γ(X, V) S)
      (I.ideal V') =
      Ideal.span {f'} := by
    have he : Ideal.map e.toRingHom
        (Ideal.map (algebraMap Γ(X, V) (Localization.Away r))
          (I.ideal V')) =
        Ideal.map (algebraMap Γ(X, V) S)
          (I.ideal V') := by
      rw [Ideal.map_map]
      congr 1
      ext a
      exact e.commutes a
    rw [← he, hgen, Ideal.map_span]
    simp only [Set.image_singleton]
    rfl
  refine ⟨U, hU, hxU, f', hf', ?_⟩
  change I.ideal (X.affineBasicOpen (U := V') r) =
    Ideal.span {f'}
  rw [← I.map_ideal_basicOpen V' r]
  exact hmap

private theorem invertible_ideal_of_cartier_comap_open
    {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor
      (I.comap U.1.ι)) : Module.Invertible Γ(X, U.1) (I.ideal U) := by
  have h := invertible_ideal_top_of_isEffectiveCartierDivisor (I.comap U.1.ι) hI
  rw [I.ideal_comap_of_isOpenImmersion U.1.ι, Scheme.Opens.ι_appIso] at h
  let V : X.affineOpens := ⟨U.1.ι ''ᵁ ⊤,
    (isAffineOpen_top U.1.toScheme).image_of_isOpenImmersion U.1.ι⟩
  change Module.Invertible Γ(X, V.1) (I.ideal V) at h
  have hV : V = U := Subtype.ext (Scheme.Opens.ι_image_top U.1)
  exact hV ▸ h

private theorem isEffectiveCartierDivisor_of_affine_generic_kernel
    {R K : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {X W T : Scheme.{u}} [IsAffine X] [IsAffine W]
    (f : X ⟶ Spec (.of R)) [Smooth f]
    (p : W ⟶ X) (q : W ⟶ Spec (.of K))
    (H : IsPullback p q f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (b : T ⟶ X) [QuasiCompact b] (t : T ⟶ W) (ht : t ≫ p = b)
    (I : X.IdealSheafData) (hI : I = b.ker)
    (hJ : Stacks.Divisors.IsEffectiveCartierDivisor (I.comap p)) :
    Stacks.Divisors.IsEffectiveCartierDivisor I := by
  let α := (Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop
  let : Algebra R Γ(X, ⊤) := α.hom.toAlgebra
  let : Algebra.Smooth R Γ(X, ⊤) :=
    (RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (.of R)).inv)).comp
      (HasRingHomProperty.appTop (P := @Smooth) f inferInstance)
  apply isEffectiveCartierDivisor_of_affine_generic_pushout p
    ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appTop)
    (isPushout_affine_generic_fibre f p q H rfl) I (I.comap p) hJ
  rw [Stacks.IdealSheaf.ideal_comap_top_of_isAffine, hI, Scheme.Hom.ker_apply]
  have hb : b.appTop.hom = t.appTop.hom.comp p.appTop.hom := by
    rw [← ht, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  change RingHom.ker b.appTop.hom =
    Ideal.comap p.appTop.hom (Ideal.map p.appTop.hom (RingHom.ker b.appTop.hom))
  rw [hb, ← RingHom.comap_ker, Ideal.comap_map_comap]

private theorem ker_comap_of_isOpenImmersion
    {X Y V T : Scheme.{u}} (b : T ⟶ X) [QuasiCompact b]
    (i : Y ⟶ X) [IsOpenImmersion i] (b' : V ⟶ Y) (j : V ⟶ T)
    (H : IsPullback b' j i b) : b.ker.comap i = b'.ker := by
  ext U
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.ker_ideal_of_isPullback_of_isOpenImmersion b b' j i H]

/-- Let `X` be smooth over a valuation ring `R` with fraction field `K`, with generic fibre
`p : W ⟶ X` (the base change of `Spec K ⟶ Spec R`), and let `b : T ⟶ X` be quasi-compact and
factor through `p`. If the kernel ideal `I` of `b` pulls back to an effective Cartier divisor on
`W`, then `I` is an effective Cartier divisor on `X`. -/
theorem isEffectiveCartierDivisor_of_generic_kernel
    {R K : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {X W T : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [Smooth f]
    (p : W ⟶ X) (q : W ⟶ Spec (.of K))
    (H : IsPullback p q f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (b : T ⟶ X) [QuasiCompact b] (t : T ⟶ W) (ht : t ≫ p = b)
    (I : X.IdealSheafData) (hI : I = b.ker)
    (hJ : Stacks.Divisors.IsEffectiveCartierDivisor (I.comap p)) :
    Stacks.Divisors.IsEffectiveCartierDivisor I := by
  have : IsAffineHom p := isAffineHom_isStableUnderBaseChange.of_isPullback
    H.flip inferInstance
  apply isEffectiveCartierDivisor_of_invertible_affineIdeals I
  intro U
  apply invertible_ideal_of_cartier_comap_open I U
  let V : W.Opens := p ⁻¹ᵁ U.1
  have : IsAffine V.toScheme := U.2.preimage p
  let b' := b ∣_ U.1
  let p' := p ∣_ U.1
  let q' := V.ι ≫ q
  let f' := U.1.ι ≫ f
  have H' : IsPullback p' q' f'
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    (isPullback_morphismRestrict p U.1).paste_vert H
  let t' : (b ⁻¹ᵁ U.1).toScheme ⟶ V.toScheme :=
    (isPullback_morphismRestrict p U.1).lift b' ((b ⁻¹ᵁ U.1).ι ≫ t) (by
      rw [Category.assoc, ht]
      exact morphismRestrict_ι b U.1)
  have ht' : t' ≫ p' = b' :=
    (isPullback_morphismRestrict p U.1).lift_fst _ _ _
  apply isEffectiveCartierDivisor_of_affine_generic_kernel f' p' q' H' b' t' ht'
    (I.comap U.1.ι)
  · rw [hI]
    exact ker_comap_of_isOpenImmersion b U.1.ι b' (b ⁻¹ᵁ U.1).ι
      (isPullback_morphismRestrict b U.1)
  · have h := Stacks.Divisors.isPullbackDefined_of_flat V.ι (I.comap p) hJ
    change Stacks.Divisors.IsEffectiveCartierDivisor
      ((I.comap p).comap V.ι) at h
    simpa only [p', V, ← Scheme.IdealSheafData.comap_comp, morphismRestrict_ι] using h

end Stacks.Divisors

end
