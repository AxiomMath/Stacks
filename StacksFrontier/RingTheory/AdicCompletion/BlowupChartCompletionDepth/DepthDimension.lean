module

public import StacksFrontier.RingTheory.AdicCompletion.BlowupChartCompletionDepth.TensorModel

/-!
# Depth and dimension along the completion of an affine blowup chart

This file identifies the `I`-adic completion of the local model `T` with `(A[I/f]_Q)^∧`, shows
that `T` has a dualizing complex when `A` does, and computes depth and dimension along the
completed chart: for a prime `𝔭' ⊂ R'` with `I R' ⊄ 𝔭'`, its contraction `𝔭 ⊂ R` and a finite
`R`-module `M`,
`depth (M_𝔭) + dim (R/𝔭) = depth ((R' ⊗_R M)_{𝔭'}) + dim (R'/𝔭') + trdeg_{κ(𝔮)} κ(Q)`.

## References

* [Stacks Project, Tag 0EJK](https://stacks.math.columbia.edu/tag/0EJK)
* [Stacks Project, Tag 02IJ](https://stacks.math.columbia.edu/tag/02IJ)
* [Stacks Project, Tag 0AW6](https://stacks.math.columbia.edu/tag/0AW6)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace Stacks.Algebraization

namespace BlowupChartModel

section Model

variable {A : Type u} [CommRing A] (I : Ideal A) (f : A) (Q : Ideal (affineBlowup I f))
  [Q.IsPrime]

variable [IsNoetherianRing A]

variable [hJ : Fact (I.map (algebraMap A (Localization.AtPrime Q)) ≤
  maximalIdeal (Localization.AtPrime Q))]

/-- The `A[I/f]_Q`-algebra structure on `T`. -/
noncomputable abbrev algebraLoc : Algebra (Localization.AtPrime Q) (Loc I f Q) :=
  (ιB I f Q).toAlgebra

/-- There is an isomorphism of `A[I/f]_Q`-algebras `(A[I/f]_Q)^∧ ≅ T^∧` of `I`-adic completions
compatible with the maps from `A[I/f]_Q`. -/
theorem exists_algEquiv :
    letI := algebraLoc I f Q
    ∃ E : affineBlowupChartCompletion I f Q ≃ₐ[Localization.AtPrime Q]
        AdicCompletion (ideal I f Q) (Loc I f Q),
      ∀ x, E (algebraMap _ (affineBlowupChartCompletion I f Q) x) =
        algebraMap (Loc I f Q) (AdicCompletion (ideal I f Q) (Loc I f Q)) (ιB I f Q x) := by
  let := algebraLoc I f Q
  let : Module (Localization.AtPrime Q) (Loc I f Q) := Algebra.toModule
  have : Module.Flat (Localization.AtPrime Q) (Loc I f Q) :=
    RingHom.flat_algebraMap_iff.mp (flat_ιB I f Q)
  exact exists_adicCompletionAlgEquiv_of_flat (I.map (algebraMap A (Localization.AtPrime Q)))
    ⟨injective_quotientMap I f Q, surjective_quotientMap I f Q⟩

/-- The isomorphism `(A[I/f]_Q)^∧ ≅ T^∧` of `I`-adic completions. -/
noncomputable def completionEquiv :
    affineBlowupChartCompletion I f Q ≃+* AdicCompletion (ideal I f Q) (Loc I f Q) :=
  letI := algebraLoc I f Q
  (exists_algEquiv I f Q).choose.toRingEquiv

/-- The isomorphism `(A[I/f]_Q)^∧ ≅ T^∧` is compatible with the maps from `A[I/f]_Q`. -/
theorem completionEquiv_algebraMap (x : Localization.AtPrime Q) :
    completionEquiv I f Q (algebraMap _ (affineBlowupChartCompletion I f Q) x) =
      algebraMap (Loc I f Q) (AdicCompletion (ideal I f Q) (Loc I f Q)) (ιB I f Q x) := by
  let := algebraLoc I f Q
  exact (exists_algEquiv I f Q).choose_spec x

/-- The ideal `I A_𝔮` is carried into `I T` by `A_𝔮 → A[I/f]_Q → T`. -/
theorem map_localRingHom_le_ideal :
    (I.map (algebraMap A (Localization.AtPrime (Q.under A)))).map
      ((ιB I f Q).comp
        (Localization.localRingHom (Q.under A) Q (algebraMap A (affineBlowup I f)) rfl)) ≤
      ideal I f Q := by
  rw [← Ideal.map_map, map_localRingHom_under_map]

/-- Under `(A[I/f]_Q)^∧ ≅ T^∧`, the completion map `(A_𝔮)^∧ → (A[I/f]_Q)^∧` becomes
`(A_𝔮)^∧ → T → T^∧`. -/
theorem completionEquiv_completionMap (r : affineBlowupBaseCompletion I f Q) :
    completionEquiv I f Q (affineBlowupCompletionMap I f Q r) =
      algebraMap (Loc I f Q) _ (algebraMap (affineBlowupBaseCompletion I f Q) (Loc I f Q) r) := by
  have e1 := eq_adicCompletionMap_of_apply_algebraMap _ _ _ (map_localRingHom_le_ideal I f Q)
    (Ideal.fg_of_isNoetherianRing _)
    ((completionEquiv I f Q).toRingHom.comp (affineBlowupCompletionMap I f Q)) fun x => by
      show completionEquiv I f Q (affineBlowupCompletionMap I f Q (algebraMap _ _ x)) = _
      rw [affineBlowupCompletionMap_algebraMap, completionEquiv_algebraMap]
      rfl
  have e2 := eq_adicCompletionMap_of_apply_algebraMap _ _ _ (map_localRingHom_le_ideal I f Q)
    (Ideal.fg_of_isNoetherianRing _)
    ((algebraMap (Loc I f Q) _).comp (algebraMap (affineBlowupBaseCompletion I f Q) _)) fun x =>
      congrArg (algebraMap (Loc I f Q) _)
        (RingHom.congr_fun (algebraMap_comp_algebraMap_eq I f Q) x)
  exact RingHom.congr_fun (e1.trans e2.symm) r

/-- Under `(A[I/f]_Q)^∧ ≅ T^∧`, the image under `T → (A[I/f]_Q)^∧` of an element of
`(A_𝔮)^∧ ⊗_A A[I/f]` is its image in `T^∧`. -/
theorem completionEquiv_ψ_algebraMap (x : Tensor I f Q) :
    completionEquiv I f Q (ψ I f Q (algebraMap _ (Loc I f Q) x)) =
      algebraMap (Loc I f Q) _ (algebraMap _ (Loc I f Q) x) := by
  refine tensor_induction I f Q (P := fun x => completionEquiv I f Q (ψ I f Q
    (algebraMap _ (Loc I f Q) x)) = algebraMap (Loc I f Q) _ (algebraMap _ (Loc I f Q) x))
    (by simp) (fun r b => ?_) (fun x y hx hy => ?_) x
  · rw [ψ_algebraMap, map_mul (toChart I f Q), toChart_algebraMap,
      toChart_inr, map_mul (completionEquiv I f Q), completionEquiv_completionMap,
      completionEquiv_algebraMap, ιB_algebraMap, map_mul (algebraMap (Tensor I f Q) (Loc I f Q)),
      map_mul (algebraMap (Loc I f Q) _),
      IsScalarTower.algebraMap_apply (affineBlowupBaseCompletion I f Q) (Tensor I f Q) (Loc I f Q)
        r]
  · rw [(algebraMap (Tensor I f Q) (Loc I f Q)).map_add, (ψ I f Q).map_add,
      (completionEquiv I f Q).map_add, hx, hy, (algebraMap (Loc I f Q) _).map_add]

/-- Under `(A[I/f]_Q)^∧ ≅ T^∧`, the map `T → (A[I/f]_Q)^∧` becomes the completion map of `T`. -/
theorem completionEquiv_ψ (t : Loc I f Q) :
    completionEquiv I f Q (ψ I f Q t) = algebraMap (Loc I f Q) _ t := by
  have h3 : ((completionEquiv I f Q).toRingHom.comp (ψ I f Q)).comp
      (algebraMap (Tensor I f Q) _) =
      (algebraMap (Loc I f Q) (AdicCompletion (ideal I f Q) (Loc I f Q))).comp
        (algebraMap (Tensor I f Q) _) :=
    RingHom.ext (completionEquiv_ψ_algebraMap I f Q)
  exact RingHom.congr_fun (IsLocalization.ringHom_ext (prime I f Q).primeCompl h3) t

/-- The completion of a localization of a ring with a dualizing complex has a dualizing
complex. -/
private theorem exists_isDualizingComplex_completion_localization {B : Type u} [CommRing B]
    [IsNoetherianRing B] (J p : Ideal B) [p.IsPrime]
    (hdual : ∃ K : @DerivedCategory (ModuleCat.{u} B) _ _ (HasDerivedCategory.standard _),
      @Dualizing.IsDualizingComplex B _ _ (HasDerivedCategory.standard (ModuleCat.{u} B)) K) :
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} (AdicCompletion (J.map (algebraMap B (Localization.AtPrime p)))
        (Localization.AtPrime p)))
    letI : IsNoetherianRing (AdicCompletion (J.map (algebraMap B (Localization.AtPrime p)))
      (Localization.AtPrime p)) := AdicCompletion.isNoetherianRing _
    ∃ L : DerivedCategory (ModuleCat.{u}
      (AdicCompletion (J.map (algebraMap B (Localization.AtPrime p))) (Localization.AtPrime p))),
      Dualizing.IsDualizingComplex L := by
  let := HasDerivedCategory.standard (ModuleCat.{u} B)
  let := HasDerivedCategory.standard (ModuleCat.{u} (Localization.AtPrime p))
  obtain ⟨K, hK⟩ := hdual
  exact Dualizing.exists_isDualizingComplex_adicCompletion _
    ⟨_, Dualizing.isDualizingComplex_localization p.primeCompl K hK⟩

/-- `T` has a dualizing complex: it is essentially of finite type over `(A_𝔮)^∧`, which is the
completion of a localization of `A`. -/
theorem exists_isDualizingComplex
    (hdual : ∃ K : @DerivedCategory (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _),
      @Dualizing.IsDualizingComplex A _ _ (HasDerivedCategory.standard (ModuleCat.{u} A)) K) :
    ∃ K : @DerivedCategory (ModuleCat.{u} (Loc I f Q)) _ _ (HasDerivedCategory.standard _),
      @Dualizing.IsDualizingComplex (Loc I f Q) _ _
        (HasDerivedCategory.standard (ModuleCat.{u} (Loc I f Q))) K := by
  have hR := exists_isDualizingComplex_completion_localization I (Q.under A) hdual
  have hEFT : IsEssentiallyOfFiniteType (affineBlowupBaseCompletion I f Q) (Loc I f Q)
      (algebraMap _ _) := by
    have hsc : ∀ r, algebraMap (affineBlowupBaseCompletion I f Q) (Loc I f Q) r =
        algebraMap (Tensor I f Q) (Loc I f Q) (algebraMap _ (Tensor I f Q) r) := fun r =>
      IsScalarTower.algebraMap_apply (affineBlowupBaseCompletion I f Q) (Tensor I f Q) (Loc I f Q) r
    let : Algebra (affineBlowupBaseCompletion I f Q) (Loc I f Q) := (algebraMap _ _).toAlgebra
    refine ⟨Tensor I f Q, inferInstance, inferInstance, inferInstance, (prime I f Q).primeCompl,
      inferInstance, IsScalarTower.of_algebraMap_eq hsc, inferInstance⟩
  obtain ⟨_, L, hL⟩ := Dualizing.exists_isDualizingComplex_of_essentiallyOfFiniteType hEFT hR
  exact ⟨L, hL⟩

/-- `T → (A[I/f]_Q)^∧` is flat: it is the completion of the Noetherian ring `T`. -/
theorem flat_ψ : (ψ I f Q).Flat := by
  have h : ψ I f Q = (completionEquiv I f Q).symm.toRingHom.comp (algebraMap (Loc I f Q) _) := by
    refine RingHom.ext fun t => (completionEquiv I f Q).injective ?_
    rw [completionEquiv_ψ]
    exact ((completionEquiv I f Q).apply_symm_apply _).symm
  rw [h]
  exact RingHom.Flat.comp (RingHom.flat_algebraMap_iff.mpr (AdicCompletion.flat_of_isNoetherian _))
    (RingHom.Flat.of_bijective (completionEquiv I f Q).symm.bijective)

/-- The composite `(A_𝔮)^∧ → T → (A[I/f]_Q)^∧` is the completion map. -/
theorem ψ_comp_algebraMap :
    (ψ I f Q).comp (algebraMap (affineBlowupBaseCompletion I f Q) (Loc I f Q)) =
      affineBlowupCompletionMap I f Q := by
  refine RingHom.ext fun r => ?_
  rw [RingHom.comp_apply,
    IsScalarTower.algebraMap_apply (affineBlowupBaseCompletion I f Q) (Tensor I f Q) (Loc I f Q),
    ψ_algebraMap, toChart_algebraMap]

/-- **The localizations of `T` away from `f` are localizations of `(A_𝔮)^∧`.** -/
theorem isLocalization_atPrime (P : Ideal (Loc I f Q)) [P.IsPrime]
    (hf : algebraMap (affineBlowupBaseCompletion I f Q) (Loc I f Q)
      (algebraMap A (affineBlowupBaseCompletion I f Q) f) ∉ P) :
    IsLocalization.AtPrime (Localization.AtPrime P)
      (P.comap (algebraMap (affineBlowupBaseCompletion I f Q) (Loc I f Q))) := by
  have : IsLocalization.AtPrime (Localization.AtPrime P)
      (P.comap (algebraMap (Tensor I f Q) (Loc I f Q))) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (prime I f Q).primeCompl
      (Localization.AtPrime P) P
  have hP₀ : algebraMap _ (Tensor I f Q) (algebraMap A (affineBlowupBaseCompletion I f Q) f) ∉
      P.comap (algebraMap (Tensor I f Q) (Loc I f Q)) := by
    rw [Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact hf
  have h := isLocalization_atPrime_comap_of_pow_mul (L := Localization.AtPrime P)
    (algebraMap A (affineBlowupBaseCompletion I f Q) f) (exists_pow_mul_eq_algebraMap I f Q)
    (exists_pow_mul_eq_zero I f Q) _ hP₀
  have key : ∀ (p₁ p₂ : Ideal (affineBlowupBaseCompletion I f Q)) [p₁.IsPrime] [p₂.IsPrime],
      p₁ = p₂ → IsLocalization.AtPrime (Localization.AtPrime P) p₁ →
        IsLocalization.AtPrime (Localization.AtPrime P) p₂ := by
    intro p₁ p₂ _ _ h12 h1
    subst h12
    exact h1
  refine key _ _ ?_ h
  rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]

/-- Every element of `(A_𝔮)^∧` is congruent modulo the maximal ideal to a fraction of `A`. -/
theorem exists_mul_sub_mem_maximalIdeal (r : affineBlowupBaseCompletion I f Q) :
    ∃ a t : A, t ∉ Q.under A ∧ algebraMap A (affineBlowupBaseCompletion I f Q) t * r -
      algebraMap A (affineBlowupBaseCompletion I f Q) a ∈
        maximalIdeal (affineBlowupBaseCompletion I f Q) := by
  obtain ⟨y, hy⟩ := exists_sub_mem_map_baseCompletion I f Q r
  obtain ⟨a, t, rfl⟩ := IsLocalization.exists_mk'_eq (Q.under A).primeCompl y
  refine ⟨a, t, t.2, ?_⟩
  have hle : (I.map (algebraMap A (Localization.AtPrime (Q.under A)))).map
      (algebraMap _ (affineBlowupBaseCompletion I f Q)) ≤
        maximalIdeal (affineBlowupBaseCompletion I f Q) := by
    rw [maximalIdeal_baseCompletion]; exact Ideal.map_mono (map_le_maximalIdeal_under I f Q)
  have hspec : algebraMap A (affineBlowupBaseCompletion I f Q) t *
      algebraMap _ (affineBlowupBaseCompletion I f Q)
        (IsLocalization.mk' (Localization.AtPrime (Q.under A)) a t) =
      algebraMap A (affineBlowupBaseCompletion I f Q) a := by
    rw [IsScalarTower.algebraMap_apply A (Localization.AtPrime (Q.under A)), ← map_mul,
      mul_comm, IsLocalization.mk'_spec, ← IsScalarTower.algebraMap_apply]
  rw [← hspec, ← mul_sub]
  exact Ideal.mul_mem_left _ _ (hle hy)

/-- The contraction to `A` of the prime of `(A_𝔮)^∧` under `prime I f Q` is `𝔮`. -/
theorem comap_under_prime :
    Q.under A = (Ideal.under (affineBlowupBaseCompletion I f Q) (prime I f Q)).comap
      (algebraMap A (affineBlowupBaseCompletion I f Q)) := by
  ext a
  show algebraMap A (affineBlowup I f) a ∈ Q ↔
    algebraMap _ (Tensor I f Q) (algebraMap A (affineBlowupBaseCompletion I f Q) a) ∈ prime I f Q
  rw [← RingHom.comp_apply, ← inr_comp_algebraMap, RingHom.comp_apply]
  exact (SetLike.ext_iff.mp (comap_prime_inr I f Q) _).symm

/-- The residue field map `κ(𝔮) → κ(prime I f Q ∩ (A_𝔮)^∧)` is bijective. -/
theorem bijective_residueFieldMap_base :
    Function.Bijective (Ideal.ResidueField.map (Q.under A)
      (Ideal.under (affineBlowupBaseCompletion I f Q) (prime I f Q))
      (algebraMap A (affineBlowupBaseCompletion I f Q)) (comap_under_prime I f Q)) := by
  refine bijective_residueFieldMap_of_forall_exists _ _ _ _ fun r => ?_
  obtain ⟨a, t, ht, h⟩ := exists_mul_sub_mem_maximalIdeal I f Q r
  exact ⟨a, t, ht, (SetLike.ext_iff.mp (comap_prime_algebraMap I f Q) _).mpr h⟩

/-- The residue field map `κ(Q) → κ(prime I f Q)` is bijective. -/
theorem bijective_residueFieldMap_chart :
    Function.Bijective (Ideal.ResidueField.map Q (prime I f Q) (inr I f Q)
      (comap_prime_inr I f Q).symm) := by
  refine bijective_residueFieldMap_of_forall_exists _ _ _ _ fun x => ?_
  refine tensor_induction I f Q (P := fun x => ∃ b u : affineBlowup I f, u ∉ Q ∧
    inr I f Q u * x - inr I f Q b ∈ prime I f Q) ⟨0, 1, Q.primeCompl.one_mem, by simp⟩
    (fun r b => ?_) (fun x y hx hy => ?_) x
  · obtain ⟨a, t, ht, h⟩ := exists_mul_sub_mem_maximalIdeal I f Q r
    refine ⟨algebraMap A (affineBlowup I f) a * b, algebraMap A (affineBlowup I f) t, ht, ?_⟩
    have hinr : ∀ z : A, inr I f Q (algebraMap A (affineBlowup I f) z) =
        algebraMap _ (Tensor I f Q) (algebraMap A (affineBlowupBaseCompletion I f Q) z) :=
      fun z => RingHom.congr_fun (inr_comp_algebraMap I f Q) z
    rw [(inr I f Q).map_mul, hinr, hinr, ← mul_assoc, ← (algebraMap _ (Tensor I f Q)).map_mul,
      ← sub_mul, ← map_sub (algebraMap (affineBlowupBaseCompletion I f Q) (Tensor I f Q))]
    refine Ideal.mul_mem_right _ _ ?_
    rw [← Ideal.mem_comap, comap_prime_algebraMap]
    exact h
  · obtain ⟨b₁, u₁, hu₁, h₁⟩ := hx
    obtain ⟨b₂, u₂, hu₂, h₂⟩ := hy
    refine ⟨u₂ * b₁ + u₁ * b₂, u₁ * u₂, fun h => (‹Q.IsPrime›.mem_or_mem h).elim hu₁ hu₂, ?_⟩
    have heq : inr I f Q (u₁ * u₂) * (x + y) - inr I f Q (u₂ * b₁ + u₁ * b₂) =
        inr I f Q u₂ * (inr I f Q u₁ * x - inr I f Q b₁) +
          inr I f Q u₁ * (inr I f Q u₂ * y - inr I f Q b₂) := by
      rw [(inr I f Q).map_mul, (inr I f Q).map_add, (inr I f Q).map_mul, (inr I f Q).map_mul]
      ring
    rw [heq]
    exact add_mem (Ideal.mul_mem_left _ _ h₁) (Ideal.mul_mem_left _ _ h₂)

omit hJ in
/-- `(A_𝔮)^∧` is universally catenary: it has a dualizing complex, being the completion of a
localization of `A`. -/
theorem isUniversallyCatenary_baseCompletion
    (hdual : ∃ K : @DerivedCategory (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _),
      @Dualizing.IsDualizingComplex A _ _ (HasDerivedCategory.standard (ModuleCat.{u} A)) K) :
    Ring.IsUniversallyCatenary (affineBlowupBaseCompletion I f Q) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} (affineBlowupBaseCompletion I f Q))
  obtain ⟨L, hL⟩ := exists_isDualizingComplex_completion_localization I (Q.under A) hdual
  exact Dualizing.isUniversallyCatenary_of_isDualizingComplex hL

omit hJ in
/-- The residue field extension `κ(Q)/κ(𝔮)` has finite transcendence degree. -/
theorem trdeg_lt_aleph0 :
    letI := Ideal.ResidueField.algebraOfLiesOver (Q.under A) Q
    Algebra.trdeg (Q.under A).ResidueField Q.ResidueField < Cardinal.aleph0 := by
  let := Ideal.ResidueField.algebraOfLiesOver (Q.under A) Q
  rw [resfield_trdeg_eq_quot_trdeg (Q.under A) Q]
  have : Algebra.FiniteType (A ⧸ Q.under A) (affineBlowup I f ⧸ Q) := by
    have hAAP : Algebra.FiniteType A (affineBlowup I f ⧸ Q) :=
      Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType A (affineBlowup I f))
        (Algebra.FiniteType.quotient (affineBlowup I f) Q)
    exact Algebra.FiniteType.of_restrictScalars_finiteType A (A ⧸ Q.under A) _
  exact trdeg_lt_aleph0_of_finiteType

/-- **The dimension formula for `T` away from `f`.** For a prime `P` of `T` not containing `f`,
`dim (T ⧸ P) + trdeg_{κ(𝔮)} κ(Q) = dim ((A_𝔮)^∧ ⧸ P ∩ (A_𝔮)^∧)`: the domain `T ⧸ P` is a
localization of a finite type algebra over the universally catenary local domain
`(A_𝔮)^∧ ⧸ P ∩ (A_𝔮)^∧`, birational to it because `f ∉ P`, at a prime over the closed point
with residue field extension `κ(Q)/κ(𝔮)`; this is Stacks 02IJ. -/
theorem ringKrullDim_quotient_add_trdeg
    (hdual : ∃ K : @DerivedCategory (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _),
      @Dualizing.IsDualizingComplex A _ _ (HasDerivedCategory.standard (ModuleCat.{u} A)) K)
    (P : Ideal (Loc I f Q)) [P.IsPrime]
    (hf : algebraMap (affineBlowupBaseCompletion I f Q) (Loc I f Q)
      (algebraMap A (affineBlowupBaseCompletion I f Q) f) ∉ P) :
    letI := Ideal.ResidueField.algebraOfLiesOver (Q.under A) Q
    ringKrullDim (Loc I f Q ⧸ P) + ((Cardinal.toENat
      (Algebra.trdeg (Q.under A).ResidueField Q.ResidueField) : ℕ∞) : WithBot ℕ∞) =
      ringKrullDim (affineBlowupBaseCompletion I f Q ⧸
        P.comap (algebraMap (affineBlowupBaseCompletion I f Q) (Loc I f Q))) := by
  let := Ideal.ResidueField.algebraOfLiesOver (Q.under A) Q
  set P₀ := P.comap (algebraMap (Tensor I f Q) (Loc I f Q)) with hP₀def
  have hP₀le : P₀ ≤ prime I f Q := by
    rw [hP₀def, ← comap_maximalIdeal_loc]
    exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›))
  have hPeq : P₀.map (algebraMap (Tensor I f Q) (Loc I f Q)) = P :=
    IsLocalization.map_comap (prime I f Q).primeCompl _ P
  have hcomapR : P.comap (algebraMap (affineBlowupBaseCompletion I f Q) (Loc I f Q)) =
      P₀.comap (algebraMap (affineBlowupBaseCompletion I f Q) (Tensor I f Q)) := by
    rw [hP₀def, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
  let p₀ := P₀.comap (algebraMap (affineBlowupBaseCompletion I f Q) (Tensor I f Q))
  have : p₀.IsPrime := Ideal.comap_isPrime _ _
  let D := affineBlowupBaseCompletion I f Q ⧸ p₀
  let S := Tensor I f Q ⧸ P₀
  have : Nontrivial D := Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsPrime.ne_top ‹_›)
  have : IsLocalRing D := IsLocalRing.of_surjective' (Ideal.Quotient.mk p₀)
    Ideal.Quotient.mk_surjective
  have : Algebra.FiniteType D S := by
    have : Algebra.FiniteType (affineBlowupBaseCompletion I f Q) S :=
      Algebra.FiniteType.trans
        (inferInstance : Algebra.FiniteType (affineBlowupBaseCompletion I f Q) (Tensor I f Q))
        (Algebra.FiniteType.quotient (Tensor I f Q) P₀)
    exact Algebra.FiniteType.of_restrictScalars_finiteType (affineBlowupBaseCompletion I f Q) D S
  have hinj : Function.Injective (algebraMap D S) := Ideal.algebraMap_quotient_injective
  have hcat : IsUniversallyCatenary D :=
    Ring.isUniversallyCatenary_iff_isUniversallyCatenary.mp
      (Ring.IsUniversallyCatenary.of_surjective Ideal.Quotient.mk_surjective
        (isUniversallyCatenary_baseCompletion I f Q hdual))
  have : ((prime I f Q).map (Ideal.Quotient.mk P₀)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hP₀le
  let qb := (prime I f Q).map (Ideal.Quotient.mk P₀)
  have hf0 : Ideal.Quotient.mk p₀ (algebraMap A (affineBlowupBaseCompletion I f Q) f) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    show algebraMap (Tensor I f Q) (Loc I f Q) (algebraMap _ (Tensor I f Q) _) ∉ P
    rwa [← IsScalarTower.algebraMap_apply]
  have : Algebra.IsAlgebraic D S := by
    refine isAlgebraic_of_pow_mul hf0 fun s => ?_
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective s
    obtain ⟨n, r, hr⟩ := exists_pow_mul_eq_algebraMap I f Q t
    refine ⟨n, Ideal.Quotient.mk p₀ r, ?_⟩
    show Ideal.Quotient.mk P₀ (algebraMap _ (Tensor I f Q)
      (algebraMap A (affineBlowupBaseCompletion I f Q) f ^ n)) * Ideal.Quotient.mk P₀ t =
        Ideal.Quotient.mk P₀ (algebraMap _ (Tensor I f Q) r)
    rw [← map_mul, hr]
  have hform := height_add_trdeg_residue_eq hinj hcat (Ideal.under D qb) qb
  have hz : Algebra.trdeg D S = 0 := trdeg_eq_zero
  rw [hz] at hform
  simp only [map_zero, Nat.cast_zero, add_zero] at hform
  have hunder : Ideal.under D qb = maximalIdeal D := by
    refine ((maximalIdeal.isMaximal D).eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_).symm
    rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk p₀)
      Ideal.Quotient.mk_surjective, Ideal.map_le_iff_le_comap]
    intro x hx
    show Ideal.Quotient.mk P₀ (algebraMap _ (Tensor I f Q) x) ∈ qb
    refine Ideal.mem_map_of_mem _ ?_
    rw [← Ideal.mem_comap, comap_prime_algebraMap]
    exact hx
  have htr := toNat_trdeg_residue_map_quotientMk_eq (R := affineBlowupBaseCompletion I f Q)
    P₀ (prime I f Q) hP₀le
  have hsq := trdeg_residueField_eq_of_bijective (algebraMap A (affineBlowupBaseCompletion I f Q))
    (inr I f Q) (inr_comp_algebraMap I f Q) (Q.under A) Q
    (Ideal.under (affineBlowupBaseCompletion I f Q) (prime I f Q)) (prime I f Q)
    (comap_under_prime I f Q) (comap_prime_inr I f Q).symm (bijective_residueFieldMap_base I f Q)
    (bijective_residueFieldMap_chart I f Q)
  have hfin := Cardinal.toENat_eq_toNat_of_lt_aleph0 (trdeg_lt_aleph0 I f Q)
  have hdimL : ringKrullDim (Loc I f Q ⧸ P) = (qb.height : WithBot ℕ∞) := by
    rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotEquivOfEq hPeq.symm)]
    exact AdicCompletionDimension.ringKrullDim_quotient_localizationAtPrime P₀ (prime I f Q) hP₀le
  rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotEquivOfEq hcomapR), hdimL, hfin, hsq, htr,
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← hunder]
  exact_mod_cast hform

section Fibre

variable (p' : Ideal (affineBlowupChartCompletion I f Q)) [p'.IsPrime]

/-- The image of `𝔭'` under `(A[I/f]_Q)^∧ ≅ T^∧` is prime. -/
instance : (p'.map (completionEquiv I f Q)).IsPrime := Ideal.map_isPrime_of_equiv _

omit [p'.IsPrime] in
/-- The contraction of `𝔭'` to `(A_𝔮)^∧` is its contraction through `T`. -/
theorem comap_completionMap_eq :
    p'.comap (affineBlowupCompletionMap I f Q) =
      (p'.comap (ψ I f Q)).comap (algebraMap (affineBlowupBaseCompletion I f Q) (Loc I f Q)) := by
  rw [Ideal.comap_comap, ψ_comp_algebraMap]

variable {p'}

omit [p'.IsPrime] in
/-- If `f ∉ 𝔭'`, then the image of `f` in `T` does not lie in the contraction of `𝔭'`. -/
theorem algebraMap_notMem_comap_ψ
    (hfp : algebraMap A (affineBlowupChartCompletion I f Q) f ∉ p') :
    algebraMap (affineBlowupBaseCompletion I f Q) (Loc I f Q)
      (algebraMap A (affineBlowupBaseCompletion I f Q) f) ∉ p'.comap (ψ I f Q) := by
  rw [Ideal.mem_comap, ← RingHom.comp_apply, ψ_comp_algebraMap,
    affineBlowupCompletionMap_algebraMap_base]
  exact hfp

/-- `(A_𝔮)^∧_𝔭 → (A[I/f]_Q)^∧_{𝔭'}` is flat when `f ∉ 𝔭'`. -/
theorem flat_localRingHom_completionMap
    (hfp : algebraMap A (affineBlowupChartCompletion I f Q) f ∉ p') :
    (Localization.localRingHom (p'.comap (affineBlowupCompletionMap I f Q)) p'
      (affineBlowupCompletionMap I f Q) rfl).Flat := by
  have := isLocalization_atPrime I f Q (p'.comap (ψ I f Q)) (algebraMap_notMem_comap_ψ I f Q hfp)
  have key := flat_localRingHom_comp_of_isLocalization
    (R := affineBlowupBaseCompletion I f Q) (ψ I f Q) (flat_ψ I f Q) p'
  rwa [ψ_comp_algebraMap] at key

/-- **The fibre depth and the dimensions.** For `𝔭'` not containing `f`, with `𝔭 = φ⁻¹𝔭'`,
`depth (R'_{𝔭'}/𝔭R'_{𝔭'}) + dim (R'/𝔭') + trdeg_{κ(𝔮)} κ(Q) = dim (R/𝔭)`. -/
theorem depth_fibre_add_ringKrullDim
    (hdual : ∃ K : @DerivedCategory (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _),
      @Dualizing.IsDualizingComplex A _ _ (HasDerivedCategory.standard (ModuleCat.{u} A)) K)
    (hfp : algebraMap A (affineBlowupChartCompletion I f Q) f ∉ p') :
    letI := (affineBlowupCompletionMap I f Q).toAlgebra
    letI := Ideal.ResidueField.algebraOfLiesOver (Q.under A) Q
    ((Module.depth (Localization.AtPrime p') (maximalIdeal _)
        (Localization.AtPrime p' ⧸ (p'.comap (affineBlowupCompletionMap I f Q)).map
          (algebraMap (affineBlowupBaseCompletion I f Q) (Localization.AtPrime p'))) : ℕ∞) :
          WithBot ℕ∞) +
        (ringKrullDim (affineBlowupChartCompletion I f Q ⧸ p') + ((Cardinal.toENat
          (Algebra.trdeg (Q.under A).ResidueField Q.ResidueField) : ℕ∞) : WithBot ℕ∞)) =
      ringKrullDim (affineBlowupBaseCompletion I f Q ⧸
        p'.comap (affineBlowupCompletionMap I f Q)) := by
  let := (affineBlowupCompletionMap I f Q).toAlgebra
  let := Ideal.ResidueField.algebraOfLiesOver (Q.under A) Q
  have := isLocalization_atPrime I f Q (p'.comap (ψ I f Q)) (algebraMap_notMem_comap_ψ I f Q hfp)
  have hd := ringKrullDim_quotient_add_trdeg I f Q hdual _ (algebraMap_notMem_comap_ψ I f Q hfp)
  have key := depth_fibre_add_ringKrullDim_of_ringEquiv (R := affineBlowupBaseCompletion I f Q)
    (R' := affineBlowupChartCompletion I f Q) (T := Loc I f Q) (affineBlowupCompletionMap I f Q) p'
    (ideal_le_maximalIdeal I f Q) (ψ I f Q) (ψ_comp_algebraMap I f Q) (completionEquiv I f Q)
    (completionEquiv_ψ I f Q) (exists_isDualizingComplex I f Q hdual) _ hd
  exact key

end Fibre

end Model

end BlowupChartModel

/-! ### Depth and dimension along the completed chart -/

section Main

open BlowupChartModel

variable {A : Type u} [CommRing A] {I : Ideal A} {f : A} {Q : Ideal (affineBlowup I f)}
  [Q.IsPrime]

/-- If `(A[I/f]_Q)^∧` has a prime ideal then `I A[I/f]_Q` lies in the maximal ideal: otherwise
`I (A[I/f]_Q)^∧` is the unit ideal and lies in the Jacobson radical. -/
theorem map_le_maximalIdeal_of_isPrime [IsNoetherianRing A]
    (p' : Ideal (affineBlowupChartCompletion I f Q)) [p'.IsPrime] :
    I.map (algebraMap A (Localization.AtPrime Q)) ≤ maximalIdeal (Localization.AtPrime Q) := by
  by_contra h
  have htop : I.map (algebraMap A (Localization.AtPrime Q)) = ⊤ := by
    by_contra hne
    exact h (IsLocalRing.le_maximalIdeal hne)
  have := IsLocalization.isNoetherianRing Q.primeCompl (Localization.AtPrime Q)
    (Algebra.FiniteType.isNoetherianRing A (affineBlowup I f))
  have := AdicCompletion.isAdicComplete_self _
    (Ideal.fg_of_isNoetherianRing (I.map (algebraMap A (Localization.AtPrime Q))))
  have hjac := IsAdicComplete.le_jacobson_bot ((I.map (algebraMap A (Localization.AtPrime Q))).map
    (algebraMap _ (AdicCompletion (I.map (algebraMap A (Localization.AtPrime Q)))
      (Localization.AtPrime Q))))
  obtain ⟨M, hM, -⟩ := Ideal.exists_le_maximal p' (Ideal.IsPrime.ne_top ‹_›)
  have h1 : (1 : AdicCompletion (I.map (algebraMap A (Localization.AtPrime Q)))
      (Localization.AtPrime Q)) ∈ (⊥ : Ideal _).jacobson := by
    apply hjac
    rw [← map_one (algebraMap (Localization.AtPrime Q) (AdicCompletion
      (I.map (algebraMap A (Localization.AtPrime Q))) (Localization.AtPrime Q)))]
    refine Ideal.mem_map_of_mem _ ?_
    rw [htop]
    exact Submodule.mem_top
  rw [Ideal.jacobson, Ideal.mem_sInf] at h1
  exact hM.ne_top ((Ideal.eq_top_iff_one M).mpr (h1 ⟨bot_le, hM⟩))

/-- On the completed chart, `I` generates the principal ideal `(f)`. So a prime `𝔭'` with
`I ⊄ 𝔭'` does not contain `f`. -/
theorem algebraMap_notMem_of_not_map_le (hf : f ∈ I)
    {p' : Ideal (affineBlowupChartCompletion I f Q)}
    (hp' : ¬ I.map (algebraMap A (affineBlowupChartCompletion I f Q)) ≤ p') :
    algebraMap A (affineBlowupChartCompletion I f Q) f ∉ p' := by
  intro hfp
  apply hp'
  let g : affineBlowup I f →+* affineBlowupChartCompletion I f Q :=
    (algebraMap (Localization.AtPrime Q) (affineBlowupChartCompletion I f Q)).comp
      (algebraMap (affineBlowup I f) (Localization.AtPrime Q))
  have hg : g.comp (algebraMap A (affineBlowup I f)) =
      algebraMap A (affineBlowupChartCompletion I f Q) := by
    ext a
    simp only [g, RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply A (affineBlowup I f) (Localization.AtPrime Q),
      ← IsScalarTower.algebraMap_apply A (Localization.AtPrime Q)
        (affineBlowupChartCompletion I f Q)]
  have hspan := congrArg (Ideal.map g) (Stacks.Blowup.affineBlowup_idealMap_eq_span I f hf)
  rw [Ideal.map_map, hg, Ideal.map_span, Set.image_singleton, ← RingHom.comp_apply, hg] at hspan
  rwa [hspan, Ideal.span_le, Set.singleton_subset_iff]

/-- **The depth formula along the completed chart, with equality.** In the situation of
`depth_add_ringKrullDim_le_blowupChart`, `depth (M'_{𝔭'}) + dim (R'/𝔭') + trdeg_{κ(𝔮)} κ(Q)`
equals `depth (M_𝔭) + dim (R/𝔭)`. -/
theorem depth_add_ringKrullDim_add_trdeg_eq [IsNoetherianRing A]
    (hdual : ∃ K : @DerivedCategory (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _),
      @Dualizing.IsDualizingComplex A _ _ (HasDerivedCategory.standard (ModuleCat.{u} A)) K)
    (hf : f ∈ I) (M : Type u) [AddCommGroup M] [Module (affineBlowupBaseCompletion I f Q) M]
    [Module.Finite (affineBlowupBaseCompletion I f Q) M]
    (p' : Ideal (affineBlowupChartCompletion I f Q)) [p'.IsPrime]
    (hp' : ¬ I.map (algebraMap A (affineBlowupChartCompletion I f Q)) ≤ p') :
    letI := (affineBlowupCompletionMap I f Q).toAlgebra
    letI := Ideal.ResidueField.algebraOfLiesOver (Q.under A) Q
    ((Module.depth (Localization.AtPrime p') (maximalIdeal _)
        (LocalizedModule p'.primeCompl (TensorProduct (affineBlowupBaseCompletion I f Q)
          (affineBlowupChartCompletion I f Q) M)) : ℕ∞) : WithBot ℕ∞) +
        (ringKrullDim (affineBlowupChartCompletion I f Q ⧸ p') + ((Cardinal.toENat
          (Algebra.trdeg (Q.under A).ResidueField Q.ResidueField) : ℕ∞) : WithBot ℕ∞)) =
      ((Module.depth (Localization.AtPrime (p'.comap (affineBlowupCompletionMap I f Q)))
          (maximalIdeal _) (LocalizedModule (p'.comap (affineBlowupCompletionMap I f Q)).primeCompl
            M) : ℕ∞) : WithBot ℕ∞) +
        ringKrullDim (affineBlowupBaseCompletion I f Q ⧸
          p'.comap (affineBlowupCompletionMap I f Q)) := by
  let := (affineBlowupCompletionMap I f Q).toAlgebra
  let := Ideal.ResidueField.algebraOfLiesOver (Q.under A) Q
  have : Fact (I.map (algebraMap A (Localization.AtPrime Q)) ≤
      maximalIdeal (Localization.AtPrime Q)) := ⟨map_le_maximalIdeal_of_isPrime p'⟩
  have hfp := algebraMap_notMem_of_not_map_le hf hp'
  rw [depth_localizedModule_tensorProduct_eq_add (affineBlowupCompletionMap I f Q) p'
    (flat_localRingHom_completionMap I f Q hfp) M, WithBot.coe_add, add_assoc,
    depth_fibre_add_ringKrullDim I f Q hdual hfp]

/-- **Stacks 0EJK, the depth inequality on the completed chart.** Let `A` be a Noetherian ring
with a dualizing complex, `f ∈ I ⊆ A`, `Q` a prime of `A[I/f]` over `𝔮 ⊂ A`, `R = (A_𝔮)^∧` and
`R' = (A[I/f]_Q)^∧` the `I`-adic completions, `M` a finite `R`-module and `𝔭' ⊂ R'` a prime
with `I R' ⊄ 𝔭'`, `𝔭 = 𝔭' ∩ R`. Then
`depth (M_𝔭) + dim (R/𝔭) ≤ depth ((R' ⊗_R M)_{𝔭'}) + dim (R'/𝔭') + trdeg_{κ(𝔮)} κ(Q)`.

`R_𝔭 → R'_{𝔭'}` is flat with Cohen--Macaulay fibre, so the depth formula (Stacks 0338) gives
`depth ((R' ⊗_R M)_{𝔭'}) = depth (M_𝔭) + dim (R'_{𝔭'}/𝔭R'_{𝔭'})`, and the fibre dimension is
computed by Ratliff's theorem (Stacks 0AW6) and the dimension formula (Stacks 02IJ). -/
theorem depth_add_ringKrullDim_le_blowupChart [IsNoetherianRing A]
    (hdual : ∃ K : @DerivedCategory (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _),
      @Dualizing.IsDualizingComplex A _ _ (HasDerivedCategory.standard (ModuleCat.{u} A)) K)
    (hf : f ∈ I) (M : Type u) [AddCommGroup M] [Module (affineBlowupBaseCompletion I f Q) M]
    [Module.Finite (affineBlowupBaseCompletion I f Q) M]
    (p' : Ideal (affineBlowupChartCompletion I f Q)) [p'.IsPrime]
    (hp' : ¬ I.map (algebraMap A (affineBlowupChartCompletion I f Q)) ≤ p') :
    letI := (affineBlowupCompletionMap I f Q).toAlgebra
    letI := Ideal.ResidueField.algebraOfLiesOver (Q.under A) Q
    enatToEInt (Module.depth (Localization.AtPrime (p'.comap (affineBlowupCompletionMap I f Q)))
        (maximalIdeal _)
        (LocalizedModule (p'.comap (affineBlowupCompletionMap I f Q)).primeCompl M)) +
      krullDimToEInt (ringKrullDim
        (affineBlowupBaseCompletion I f Q ⧸ p'.comap (affineBlowupCompletionMap I f Q))) ≤
    enatToEInt (Module.depth (Localization.AtPrime p') (maximalIdeal _)
        (LocalizedModule p'.primeCompl (TensorProduct (affineBlowupBaseCompletion I f Q)
          (affineBlowupChartCompletion I f Q) M))) +
      krullDimToEInt (ringKrullDim (affineBlowupChartCompletion I f Q ⧸ p')) +
      enatToEInt (Cardinal.toENat (Algebra.trdeg (Q.under A).ResidueField Q.ResidueField)) := by
  let := (affineBlowupCompletionMap I f Q).toAlgebra
  let := Ideal.ResidueField.algebraOfLiesOver (Q.under A) Q
  have heq := depth_add_ringKrullDim_add_trdeg_eq hdual hf M p' hp'
  refine le_of_eq ?_
  rw [← krullDimToEInt_coe, ← krullDimToEInt_coe, ← krullDimToEInt_coe, ← krullDimToEInt_add,
    ← krullDimToEInt_add, ← krullDimToEInt_add, add_assoc, heq]

/-- **Stacks 0EJK, the dimension inequality on the completed chart.** In the situation of
`depth_add_ringKrullDim_le_blowupChart`, `dim (R'/𝔭') + trdeg_{κ(𝔮)} κ(Q) ≤ dim (R/𝔭)`. -/
theorem ringKrullDim_add_trdeg_le_blowupChart [IsNoetherianRing A]
    (hdual : ∃ K : @DerivedCategory (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _),
      @Dualizing.IsDualizingComplex A _ _ (HasDerivedCategory.standard (ModuleCat.{u} A)) K)
    (hf : f ∈ I) (p' : Ideal (affineBlowupChartCompletion I f Q)) [p'.IsPrime]
    (hp' : ¬ I.map (algebraMap A (affineBlowupChartCompletion I f Q)) ≤ p') :
    letI := Ideal.ResidueField.algebraOfLiesOver (Q.under A) Q
    krullDimToEInt (ringKrullDim (affineBlowupChartCompletion I f Q ⧸ p')) +
      enatToEInt (Cardinal.toENat (Algebra.trdeg (Q.under A).ResidueField Q.ResidueField)) ≤
    krullDimToEInt (ringKrullDim
      (affineBlowupBaseCompletion I f Q ⧸ p'.comap (affineBlowupCompletionMap I f Q))) := by
  let := (affineBlowupCompletionMap I f Q).toAlgebra
  let := Ideal.ResidueField.algebraOfLiesOver (Q.under A) Q
  have : Fact (I.map (algebraMap A (Localization.AtPrime Q)) ≤
      maximalIdeal (Localization.AtPrime Q)) := ⟨map_le_maximalIdeal_of_isPrime p'⟩
  have heq := depth_fibre_add_ringKrullDim I f Q hdual (algebraMap_notMem_of_not_map_le hf hp')
  rw [← krullDimToEInt_coe, ← krullDimToEInt_add]
  refine krullDimToEInt_mono (heq ▸ le_add_of_nonneg_left ?_)
  exact WithBot.coe_le_coe.mpr zero_le

end Main

end Stacks.Algebraization
