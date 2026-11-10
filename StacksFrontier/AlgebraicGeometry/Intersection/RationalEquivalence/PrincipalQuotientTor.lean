module

public import StacksFrontier.AlgebraicGeometry.Chow.CalculationMultiplicities.Multiplication
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.TripleProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.TorSheafMultiplicity
public import StacksFrontier.RingTheory.Tor.Balancing
public import StacksFrontier.RingTheory.Tor.DimensionShift

/-!
# `Tor` against the quotient by a nonzerodivisor, and the local identity behind Tag 0B60

Let `B` be a commutative ring and `t ∈ B` a nonzerodivisor. For every `B`-module `T`,

`Tor₀(T, B ⧸ (t)) ≅ T ⧸ tT`,  `Tor₁(T, B ⧸ (t)) ≅ ker(t : T → T)`,  `Torᵢ(T, B ⧸ (t)) = 0` for
`i ≥ 2`,

read off the long exact sequence of `Tor'_•(-, T)` along `0 → (t) → B → B ⧸ (t) → 0`, the ideal
`(t)` being free of rank one. Consequently `∑ᵢ (-1)ⁱ length Torᵢ(T, B ⧸ (t))` is the periodic
length of `(T, 0, t)`, which Tag 02QF computes as a sum over the nonclosed points of the support.

Combined with the associativity of the iterated `Tor` lengths over a regular local ring (the local
form of Tag 0B1L) this gives the local identity that the proof of Tag 0B60 rests on: for finite
modules `M`, `N` over a regular local ring `B`, with `t` regular on `N` and
`Supp M ∩ Supp N ∩ V(t)` the closed point,

`∑ᵢ (-1)ⁱ length Torᵢ(M, N ⧸ tN) = ∑_Q ord_{B/Q}(t) · ∑ⱼ (-1)ʲ length (Torⱼ(M, N))_Q`,

`Q` running over the nonclosed points of `Supp M ∩ Supp N`.

## Main results

* `Stacks.Intersection.PrincipalQuotientTor.length_tor_zero`,
  `Stacks.Intersection.PrincipalQuotientTor.length_tor_one`,
  `Stacks.Intersection.PrincipalQuotientTor.isZero_tor_add_two` — the three `Tor` modules.
* `Stacks.Intersection.PrincipalQuotientTor.sum_length_tor_eq_periodicLength` — the alternating sum
  as a periodic length.
* `Stacks.Intersection.PrincipalQuotientTor.sum_length_tor_quotSMulTop_eq` — the local identity.

## References

* [Stacks Project, Tag 0B60](https://stacks.math.columbia.edu/tag/0B60)
* [Stacks Project, Tag 0B1L](https://stacks.math.columbia.edu/tag/0B1L)
* [Stacks Project, Tag 02QF](https://stacks.math.columbia.edu/tag/02QF)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct Pointwise

universe u

namespace Stacks.Intersection.PrincipalQuotientTor

variable {B : Type u} [CommRing B] (t : B)

/-- For a nonzerodivisor `t`, multiplication by `t` identifies `B` with the ideal `(t)`. -/
noncomputable def spanSingletonEquiv (ht : IsSMulRegular B t) : B ≃ₗ[B] Ideal.span {t} :=
  LinearEquiv.ofBijective
    ((LinearMap.toSpanSingleton B B t).codRestrict (Ideal.span {t})
      (fun b => Ideal.mem_span_singleton'.2 ⟨b, rfl⟩))
    ⟨fun a b hab => by
      have h : a * t = b * t := congrArg Subtype.val hab
      exact ht (by simpa [smul_eq_mul, mul_comm] using h),
    fun x => by
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 x.2
      exact ⟨b, Subtype.ext hb⟩⟩

/-- The isomorphism `spanSingletonEquiv t ht` sends `b` to `b * t`. -/
@[simp]
theorem spanSingletonEquiv_apply (ht : IsSMulRegular B t) (b : B) :
    ((spanSingletonEquiv t ht b : Ideal.span {t}) : B) = b * t :=
  rfl

/-- For a nonzerodivisor `t` the ideal `(t)` is a projective module, being free of rank one. -/
theorem projective_span (ht : IsSMulRegular B t) :
    Projective (ModuleCat.of B (Ideal.span {t})) :=
  ModuleCat.projective_of_free ((Module.Basis.singleton Unit B).map (spanSingletonEquiv t ht))

variable (T : ModuleCat.{u} B)

/-- The higher `Tor'` of `B ⧸ (t)` vanish above degree one. -/
theorem isZero_Tor'_add_two (ht : IsSMulRegular B t) (n : ℕ) :
    IsZero (((Tor' (ModuleCat.{u} B) (n + 2)).obj
      (ModuleCat.of B (B ⧸ Ideal.span {t}))).obj T) := by
  have := projective_span t ht
  have hS := Stacks.Tor.DimensionShift.shortExact_quotientShortComplex (Ideal.span {t})
  have hex := (Stacks.Tor.Tor'_composableArrows_exact_first hS T (n + 1)).exact' 1 2 3
  refine hex.isZero_X₂ ?_ ?_
  · exact (isZero_Tor'_succ_of_projective (ModuleCat.{u} B) (ModuleCat.of B B) T (n + 1)).eq_of_src
      _ _
  · exact (isZero_Tor'_succ_of_projective (ModuleCat.{u} B)
      (ModuleCat.of B (Ideal.span {t})) T n).eq_of_tgt _ _

/-- The two term exact sequence `Tor'₁(B ⧸ (t), T) → (t) ⊗ T → B ⊗ T` at the bottom of the long
exact sequence of `Tor'_•(-, T)`. -/
noncomputable def bottomShortComplex : ShortComplex (ModuleCat.{u} B) :=
  ShortComplex.mk
    (Stacks.Tor.Tor'δFirstZero
      (Stacks.Tor.DimensionShift.shortExact_quotientShortComplex (Ideal.span {t})) T)
    ((Stacks.Tor.DimensionShift.quotientShortComplex (Ideal.span {t})).f ▷ T)
    ((Stacks.Tor.Tor'_composableArrows_exact_first_zero
      (Stacks.Tor.DimensionShift.shortExact_quotientShortComplex (Ideal.span {t}))
        T).toIsComplex.zero 2)

/-- The sequence `Tor'₁(B ⧸ (t), T) → (t) ⊗ T → B ⊗ T` is exact. -/
theorem exact_bottomShortComplex : (bottomShortComplex t T).Exact :=
  (Stacks.Tor.Tor'_composableArrows_exact_first_zero
    (Stacks.Tor.DimensionShift.shortExact_quotientShortComplex (Ideal.span {t})) T).exact' 2 3 4

/-- `Tor'₁(B ⧸ (t), T) → (t) ⊗ T` is injective, `B` being projective. -/
theorem mono_bottomShortComplex_f : Mono (bottomShortComplex t T).f :=
  Stacks.Tor.mono_Tor'δFirstZero
    (Stacks.Tor.DimensionShift.shortExact_quotientShortComplex (Ideal.span {t})) T
    (isZero_Tor'_succ_of_projective (ModuleCat.{u} B) (ModuleCat.of B B) T 0)

/-- `Tor'₁(B ⧸ (t), T)` is the kernel of `(t) ⊗ T → B ⊗ T`. -/
noncomputable def tor'OneIsoKernel :
    ((Tor' (ModuleCat.{u} B) 1).obj (ModuleCat.of B (B ⧸ Ideal.span {t}))).obj T ≅
      kernel ((Stacks.Tor.DimensionShift.quotientShortComplex (Ideal.span {t})).f ▷ T) :=
  haveI := mono_bottomShortComplex_f t T
  (exact_bottomShortComplex t T).fIsKernel.conePointUniqueUpToIso (limit.isLimit _)

/-- The map `(t) ⊗ T → B ⊗ T` has the same kernel as multiplication by `t` on `T`, up to the
identifications `(t) ≅ B` and `B ⊗ T ≅ T`. -/
noncomputable def kerRTensorSubtypeEquiv (ht : IsSMulRegular B t) :
    LinearMap.ker ((Ideal.span {t}).subtype.rTensor T) ≃ₗ[B]
      LinearMap.ker (LinearMap.lsmul B T t) := by
  let e : Ideal.span {t} ⊗[B] (T : Type u) ≃ₗ[B] T :=
    (TensorProduct.congr (spanSingletonEquiv t ht).symm (LinearEquiv.refl B (T : Type u))) ≪≫ₗ
      TensorProduct.lid B (T : Type u)
  have hcomm : (TensorProduct.lid B (T : Type u)).toLinearMap ∘ₗ
      (Ideal.span {t}).subtype.rTensor (T : Type u) =
      LinearMap.lsmul B (T : Type u) t ∘ₗ e.toLinearMap := by
    apply TensorProduct.ext'
    intro j m
    obtain ⟨b, rfl⟩ := (spanSingletonEquiv t ht).surjective j
    simp only [e, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe,
      LinearEquiv.trans_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
      TensorProduct.lid_tmul, LinearEquiv.symm_apply_apply, Submodule.subtype_apply,
      spanSingletonEquiv_apply, LinearMap.lsmul_apply, mul_smul]
    exact smul_comm b t m
  have h1 : LinearMap.ker ((Ideal.span {t}).subtype.rTensor (T : Type u)) =
      LinearMap.ker (LinearMap.lsmul B (T : Type u) t ∘ₗ e.toLinearMap) := by
    rw [← hcomm, LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot]
  have h2 : (LinearMap.ker (LinearMap.lsmul B (T : Type u) t ∘ₗ e.toLinearMap)).map
      e.toLinearMap = LinearMap.ker (LinearMap.lsmul B (T : Type u) t) := by
    rw [LinearMap.ker_comp]
    exact Submodule.map_comap_eq_of_surjective e.surjective _
  exact LinearEquiv.ofEq _ _ h1 ≪≫ₗ e.submoduleMap _ ≪≫ₗ LinearEquiv.ofEq _ _ h2

/-- `Tor₀(T, B ⧸ (t)) ≅ T ⧸ tT`, at the level of lengths. -/
theorem length_tor_zero :
    Module.length B (((Tor (ModuleCat.{u} B) 0).obj T).obj
      (ModuleCat.of B (B ⧸ Ideal.span {t}))) = Module.length B (QuotSMulTop t T) := by
  have e₁ : ((Tor (ModuleCat.{u} B) 0).obj T).obj (ModuleCat.of B (B ⧸ Ideal.span {t})) ≅
      T ⊗ ModuleCat.of B (B ⧸ Ideal.span {t}) :=
    (tensorLeft T).leftDerivedZeroIsoSelf.app (ModuleCat.of B (B ⧸ Ideal.span {t}))
  rw [e₁.toLinearEquiv.length_eq]
  exact (QuotSMulTop.equivTensorQuot t T).symm.length_eq

/-- `Tor₁(T, B ⧸ (t)) ≅ ker(t : T → T)`, at the level of lengths. -/
theorem length_tor_one (ht : IsSMulRegular B t) :
    Module.length B (((Tor (ModuleCat.{u} B) 1).obj T).obj
      (ModuleCat.of B (B ⧸ Ideal.span {t}))) =
      Module.length B (LinearMap.ker (LinearMap.lsmul B T t)) := by
  have e₁ : ((Tor (ModuleCat.{u} B) 1).obj T).obj (ModuleCat.of B (B ⧸ Ideal.span {t})) ≅
      ((Tor' (ModuleCat.{u} B) 1).obj (ModuleCat.of B (B ⧸ Ideal.span {t}))).obj T :=
    (torFlip_iso_Tor'.derivedBraid B 1 T).app (ModuleCat.of B (B ⧸ Ideal.span {t}))
  rw [e₁.toLinearEquiv.length_eq,
    (tor'OneIsoKernel t T).toLinearEquiv.length_eq,
    (ModuleCat.kernelIsoKer _).toLinearEquiv.length_eq]
  exact (kerRTensorSubtypeEquiv t T ht).length_eq

/-- `Torᵢ(T, B ⧸ (t)) = 0` for `i ≥ 2`. -/
theorem isZero_tor_add_two (ht : IsSMulRegular B t) (n : ℕ) :
    IsZero (((Tor (ModuleCat.{u} B) (n + 2)).obj T).obj
      (ModuleCat.of B (B ⧸ Ideal.span {t}))) :=
  have e₁ : ((Tor (ModuleCat.{u} B) (n + 2)).obj T).obj (ModuleCat.of B (B ⧸ Ideal.span {t})) ≅
      ((Tor' (ModuleCat.{u} B) (n + 2)).obj (ModuleCat.of B (B ⧸ Ideal.span {t}))).obj T :=
    (torFlip_iso_Tor'.derivedBraid B (n + 2) T).app (ModuleCat.of B (B ⧸ Ideal.span {t}))
  (isZero_Tor'_add_two t T ht n).of_iso e₁

/-- `Tor₀(N, B ⧸ (t)) ≅ N ⧸ tN`. -/
noncomputable def torZeroIso :
    ((Tor (ModuleCat.{u} B) 0).obj T).obj (ModuleCat.of B (B ⧸ Ideal.span {t})) ≅
      ModuleCat.of B (QuotSMulTop t T) :=
  (tensorLeft T).leftDerivedZeroIsoSelf.app (ModuleCat.of B (B ⧸ Ideal.span {t})) ≪≫
    (QuotSMulTop.equivTensorQuot t T).symm.toModuleIso

/-- If `t` is also a nonzerodivisor on `N`, then `Torᵢ(N, B ⧸ (t)) = 0` for `i ≥ 1`. -/
theorem isZero_tor_succ_of_isSMulRegular (ht : IsSMulRegular B t) (htT : IsSMulRegular T t)
    (n : ℕ) :
    IsZero (((Tor (ModuleCat.{u} B) (n + 1)).obj T).obj
      (ModuleCat.of B (B ⧸ Ideal.span {t}))) := by
  rcases n with _ | n
  · have hker : LinearMap.ker (LinearMap.lsmul B T t) = ⊥ := LinearMap.ker_eq_bot.mpr htT
    have h0 : Module.length B (((Tor (ModuleCat.{u} B) 1).obj T).obj
        (ModuleCat.of B (B ⧸ Ideal.span {t}))) = 0 := by
      rw [length_tor_one t T ht, hker]
      exact Module.length_eq_zero
    rw [Module.length_eq_zero_iff] at h0
    exact ModuleCat.isZero_of_subsingleton _
  · exact isZero_tor_add_two t T ht n

/-- The periodic length of `(T, 0, t)` is `length(T ⧸ tT) - length(ker t)`. -/
theorem periodicLength_zero_lsmul :
    AlgebraicGeometry.periodicLength
        (AlgebraicGeometry.twoPeriodicComplex (0 : Module.End B T) (LinearMap.lsmul B T t)
          (zero_mul _) (mul_zero _)) =
      ((Module.length B (QuotSMulTop t T)).toNat : ℤ) -
        ((Module.length B (LinearMap.ker (LinearMap.lsmul B T t))).toNat : ℤ) := by
  have htwo : (1 + 1 : ZMod 2) = 0 := by decide
  let K := AlgebraicGeometry.twoPeriodicComplex (0 : Module.End B T) (LinearMap.lsmul B T t)
        (zero_mul _) (mul_zero _)
  let S₀ := K.sc' 1 0 1
  let S₁ := K.sc' 0 1 0
  have hg : S₀.g = 0 := by
    simp [S₀, K, HomologicalComplex.sc', AlgebraicGeometry.twoPeriodicComplex]
    rfl
  let e0 := K.homologyIsoSc' (1 : ZMod 2) 0 1 (by simp) (by simp) ≪≫
    S₀.asIsoHomologyι hg ≪≫ S₀.moduleCatOpcyclesIso
  let e1 := K.homologyIsoSc' (0 : ZMod 2) 1 0 (by simp) (by simp [htwo]) ≪≫
    S₁.moduleCatHomologyIso
  have h0 : Module.length B (K.homology 0) = Module.length B (QuotSMulTop t T) := by
    rw [e0.toLinearEquiv.length_eq]
    change Module.length B (T ⧸ LinearMap.range S₀.f.hom) = _
    have hf : S₀.f.hom = LinearMap.lsmul B T t := by
      simp [S₀, K, HomologicalComplex.sc', AlgebraicGeometry.twoPeriodicComplex, htwo]
      rfl
    have hrange : LinearMap.range (LinearMap.lsmul B T t) = t • (⊤ : Submodule B T) := by
      ext y
      simp only [Submodule.mem_smul_pointwise_iff_exists, LinearMap.mem_range,
        Submodule.mem_top, true_and]
      rfl
    rw [hf]
    exact (Submodule.quotEquivOfEq _ _ hrange).length_eq
  have h1 : Module.length B (K.homology 1) =
      Module.length B (LinearMap.ker (LinearMap.lsmul B T t)) := by
    rw [e1.toLinearEquiv.length_eq]
    have hg1 : S₁.g.hom = LinearMap.lsmul B T t := by
      simp [S₁, K, HomologicalComplex.sc', AlgebraicGeometry.twoPeriodicComplex, htwo]
      rfl
    have hf0 : S₁.f = 0 := by
      simp [S₁, K, HomologicalComplex.sc', AlgebraicGeometry.twoPeriodicComplex]
      rfl
    have hf1 : S₁.moduleCatToCycles = 0 := by
      ext x
      change S₁.f.hom x = 0
      rw [hf0]
      rfl
    change Module.length B ((LinearMap.ker S₁.g.hom) ⧸
      LinearMap.range S₁.moduleCatToCycles) = _
    rw [hf1, LinearMap.range_zero, (Submodule.quotEquivOfEqBot _ rfl).length_eq]
    exact congrArg (fun f : T →ₗ[B] T => Module.length B (LinearMap.ker f)) hg1
  change ((Module.length B (K.homology 0)).toNat : ℤ) -
    ((Module.length B (K.homology 1)).toNat : ℤ) = _
  rw [h0, h1]

/-! ### The alternating sum against the quotient by a regular element -/

section Local

variable {B : Type u} [CommRing B]

/-- The alternating sum `∑ᵢ (-1)ⁱ length Torᵢ(T, B ⧸ (t))` is the periodic length of
`(T, 0, t)`. -/
theorem sum_length_tor_eq_periodicLength (t : B) (ht : IsSMulRegular B t)
    (T : ModuleCat.{u} B) (n : ℕ) :
    ∑ p ∈ Finset.range (n + 2), (-1 : ℤ) ^ p * ((Module.length B
        (((Tor (ModuleCat.{u} B) p).obj T).obj
          (ModuleCat.of B (B ⧸ Ideal.span {t})))).toNat : ℤ) =
      AlgebraicGeometry.periodicLength
        (AlgebraicGeometry.twoPeriodicComplex (0 : Module.End B T) (LinearMap.lsmul B T t)
          (zero_mul _) (mul_zero _)) := by
  rw [periodicLength_zero_lsmul, Finset.sum_range_succ', Finset.sum_range_succ',
    Finset.sum_eq_zero, length_tor_zero, length_tor_one t T ht]
  · simp only [pow_zero, one_mul, zero_add, pow_one, neg_one_mul]
    ring
  · intro p _
    rw [Module.length_eq_zero_iff.mpr
      (ModuleCat.subsingleton_of_isZero (isZero_tor_add_two t T ht p))]
    simp

variable [IsLocalRing B]

/-- In a local ring, a nonclosed point of a support of dimension at most one is minimal in it. -/
theorem minimal_support_of_supportDim_le_one {X : Type u} [AddCommGroup X] [Module B X]
    (hX : Module.supportDim B X ≤ 1) {Q : PrimeSpectrum B} (hQ : Q ∈ Module.support B X)
    (hQm : Q ≠ IsLocalRing.closedPoint B) : Minimal (· ∈ Module.support B X) Q := by
  have hle : Q ≤ IsLocalRing.closedPoint B := IsLocalRing.le_maximalIdeal Q.isPrime.ne_top
  have hm : IsLocalRing.closedPoint B ∈ Module.support B X := Module.mem_support_mono hle hQ
  have h1 : Module.supportDim B X = 1 := le_antisymm hX <| Order.one_le_krullDim_iff.mpr
    ⟨⟨Q, hQ⟩, ⟨_, hm⟩, lt_of_le_of_ne hle fun h => hQm (congrArg Subtype.val h)⟩
  have hset := AlgebraicGeometry.minimal_support_eq_nonclosed (R := B) (M := X) h1
  have : Q ∈ {q : PrimeSpectrum B | q ∈ Module.support B X ∧ q ≠ IsLocalRing.closedPoint B} :=
    ⟨hQ, hQm⟩
  rwa [← hset] at this

/-- A module supported at the closed point has support of dimension at most zero. -/
theorem supportDim_nonpos_of_support_subset {X : Type u} [AddCommGroup X] [Module B X]
    (hX : Module.support B X ⊆ {IsLocalRing.closedPoint B}) : Module.supportDim B X ≤ 0 :=
  Order.krullDim_nonpos_iff_forall_isMax.mpr fun p q _ =>
    le_of_eq (Subtype.ext ((hX q.2).trans (hX p.2).symm))

/-- A support meeting the zero locus of an element of the maximal ideal only at the closed point
has dimension at most one. -/
theorem supportDim_le_one_of_support_inter_subset {X : Type u} [AddCommGroup X] [Module B X]
    [Module.Finite B X] [IsNoetherianRing B] (t : B) (htm : t ∈ IsLocalRing.maximalIdeal B)
    (hX : Module.support B X ∩ PrimeSpectrum.zeroLocus {t} ⊆ {IsLocalRing.closedPoint B}) :
    Module.supportDim B X ≤ 1 := by
  have h0 : Module.supportDim B (QuotSMulTop t X) ≤ 0 :=
    supportDim_nonpos_of_support_subset (by rw [Module.support_quotSMulTop]; exact hX)
  calc Module.supportDim B X ≤ Module.supportDim B (QuotSMulTop t X) + 1 :=
        Module.supportDim_le_supportDim_quotSMulTop_succ htm
    _ ≤ 0 + 1 := by gcongr
    _ = 1 := zero_add 1

end Local

/-! ### The local identity -/

section Vanishing

variable {B : Type u} [CommRing B]

/-- `Tor` against a zero module vanishes, on the right. -/
theorem isZero_tor_of_isZero_right (X : ModuleCat.{u} B) {Y : ModuleCat.{u} B} (hY : IsZero Y)
    (p : ℕ) : IsZero (((Tor (ModuleCat.{u} B) p).obj X).obj Y) := by
  change IsZero (((tensorLeft X).leftDerived p).obj Y)
  exact Functor.map_isZero _ hY

/-- `Tor` against a zero module has length zero, on either side. -/
theorem length_tor_eq_zero_of_isZero_left {X : ModuleCat.{u} B} (hX : IsZero X)
    (Y : ModuleCat.{u} B) (p : ℕ) :
    Module.length B (((Tor (ModuleCat.{u} B) p).obj X).obj Y) = 0 := by
  rw [Module.length_tor_comm]
  exact Module.length_eq_zero_iff.mpr
    (ModuleCat.subsingleton_of_isZero (isZero_tor_of_isZero_right Y hX p))

end Vanishing

section Main

variable {B : Type u} [CommRing B] [IsRegularLocalRing B]

/-- **The local identity behind Tag 0B60.** Let `B` be a regular local ring of dimension at most
`n`, let `t` be a nonzerodivisor in the maximal ideal and `M`, `N` finite `B`-modules with `t`
regular on `N`, such that `Supp M ∩ Supp N ∩ V(t)` is the closed point. Then

`∑ᵢ (-1)ⁱ length Torᵢ(M, N ⧸ tN) = ∑_Q ord_{B/Q}(t) · ∑ⱼ (-1)ʲ length (Torⱼ(M, N))_Q`,

the sum running over the nonclosed points `Q` of `Supp M ∩ Supp N`. -/
theorem sum_length_tor_quotSMulTop_eq (M N : ModuleCat.{u} B) [Module.Finite B M]
    [Module.Finite B N] (n : ℕ) (hdim : ringKrullDim B ≤ (n : WithBot ℕ∞)) (t : B)
    (htm : t ∈ IsLocalRing.maximalIdeal B) (htB : IsSMulRegular B t) (htN : IsSMulRegular N t)
    (hsupp : Module.support B M ∩ Module.support B N ∩ PrimeSpectrum.zeroLocus {t} ⊆
      {IsLocalRing.closedPoint B}) :
    ∑ i ∈ Finset.range (n + 2), (-1 : ℤ) ^ i * ((Module.length B
        (((Tor (ModuleCat.{u} B) i).obj M).obj (ModuleCat.of B (QuotSMulTop t N)))).toNat : ℤ) =
      ∑ᶠ Q ∈ {Q : PrimeSpectrum B | Q ∈ Module.support B M ∩ Module.support B N ∧
          Q ≠ IsLocalRing.closedPoint B},
        ((Ring.ord (B ⧸ Q.asIdeal) (Ideal.Quotient.mk Q.asIdeal t)).toNat : ℤ) *
          ∑ j ∈ Finset.range (n + 2), (-1 : ℤ) ^ j *
            ((Module.length (Localization.AtPrime Q.asIdeal)
              (LocalizedModule Q.asIdeal.primeCompl
                (((Tor (ModuleCat.{u} B) j).obj M).obj N))).toNat : ℤ) := by
  classical
  set P := ModuleCat.of B (B ⧸ Ideal.span {t}) with hPdef
  have hsuppP : Module.support B P = PrimeSpectrum.zeroLocus {t} := by
    change Module.support B (B ⧸ Ideal.span {t}) = _
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient, PrimeSpectrum.zeroLocus_span]
  have hA := Stacks.Intersection.finsum_alternating_length_tor_assoc_of_isRegularLocalRing B M N
    P n hdim (by rw [hsuppP]; exact hsupp)
  have hvan : ∀ (X Y : ModuleCat.{u} B) (p : ℕ), n < p →
      IsZero (((Tor (ModuleCat.{u} B) p).obj X).obj Y) := fun X Y p hp =>
    AlgebraicGeometry.TorFormula.isZero_Tor_of_isRegularLocalRing X Y n p hdim hp
  have hlen0 : ∀ {Z : ModuleCat.{u} B}, IsZero Z → ((Module.length B Z).toNat : ℤ) = 0 :=
    fun hZ => by
      rw [Module.length_eq_zero_iff.mpr (ModuleCat.subsingleton_of_isZero hZ)]
      rfl
  -- a sum over `ℕ × ℕ` vanishing outside `[0, n] × [0, n]` is a double sum over `range (n + 2)`
  have hfin : ∀ f : ℕ × ℕ → ℤ, (∀ p q, n < p ∨ n < q → f (p, q) = 0) →
      ∑ᶠ pq, f pq = ∑ p ∈ Finset.range (n + 2), ∑ q ∈ Finset.range (n + 2), f (p, q) := by
    intro f hf
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 2) ×ˢ Finset.range (n + 2)),
      Finset.sum_product]
    intro pq hpq
    simp only [Function.mem_support] at hpq
    simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
    by_contra hc
    exact hpq (hf pq.1 pq.2 (by omega))
  -- the left-associated sum
  have hL : (∑ᶠ pq : ℕ × ℕ, (-1 : ℤ) ^ (pq.1 + pq.2) * ((Module.length B
        (((Tor (ModuleCat.{u} B) pq.1).obj M).obj
          (((Tor (ModuleCat.{u} B) pq.2).obj N).obj P))).toNat : ℤ)) =
      ∑ i ∈ Finset.range (n + 2), (-1 : ℤ) ^ i * ((Module.length B
        (((Tor (ModuleCat.{u} B) i).obj M).obj (ModuleCat.of B (QuotSMulTop t N)))).toNat : ℤ) := by
    rw [hfin]
    · refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.sum_eq_single 0]
      · rw [add_zero, (((Tor (ModuleCat.{u} B) p).obj M).mapIso
          (torZeroIso t N)).toLinearEquiv.length_eq]
      · intro q _ hq
        obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
        rw [hlen0 (isZero_tor_of_isZero_right M
          (isZero_tor_succ_of_isSMulRegular t N htB htN q') p), mul_zero]
      · intro h
        exact absurd (Finset.mem_range.mpr (by omega)) h
    · rintro p q (h | h)
      · rw [hlen0 (hvan _ _ _ h), mul_zero]
      · rw [hlen0 (isZero_tor_of_isZero_right M (hvan N P q h) p), mul_zero]
  -- the right-associated sum, as a sum of periodic lengths
  have hfinT : ∀ q : ℕ, Module.Finite B (((Tor (ModuleCat.{u} B) q).obj M).obj N) :=
    fun q => tor_finite_of_noetherian B M N q
  have hsuppT : ∀ q : ℕ, Module.support B (((Tor (ModuleCat.{u} B) q).obj M).obj N) ⊆
      Module.support B M ∩ Module.support B N := fun q =>
    Stacks.Intersection.support_tor_subset_inter M N q
  have hR : (∑ᶠ pq : ℕ × ℕ, (-1 : ℤ) ^ (pq.1 + pq.2) * ((Module.length B
        (((Tor (ModuleCat.{u} B) pq.1).obj
          (((Tor (ModuleCat.{u} B) pq.2).obj M).obj N)).obj P)).toNat : ℤ)) =
      ∑ q ∈ Finset.range (n + 2), (-1 : ℤ) ^ q *
        AlgebraicGeometry.periodicLength
          (AlgebraicGeometry.twoPeriodicComplex
            (0 : Module.End B (((Tor (ModuleCat.{u} B) q).obj M).obj N))
            (LinearMap.lsmul B (((Tor (ModuleCat.{u} B) q).obj M).obj N) t)
            (zero_mul _) (mul_zero _)) := by
    rw [hfin, Finset.sum_comm]
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [← sum_length_tor_eq_periodicLength t htB _ n, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [pow_add]
      ring
    · rintro p q (h | h)
      · rw [hlen0 (hvan _ P p h), mul_zero]
      · rw [length_tor_eq_zero_of_isZero_left (hvan M N q h) P p]
        simp
  -- the index set
  set I := {Q : PrimeSpectrum B | Q ∈ Module.support B M ∩ Module.support B N ∧
    Q ≠ IsLocalRing.closedPoint B} with hIdef
  set J := Module.annihilator B M ⊔ Module.annihilator B N with hJdef
  have hsuppX : Module.support B (B ⧸ J) = Module.support B M ∩ Module.support B N := by
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient, Module.support_eq_zeroLocus,
      Module.support_eq_zeroLocus, hJdef, PrimeSpectrum.zeroLocus_sup]
  have hdimX : Module.supportDim B (B ⧸ J) ≤ 1 :=
    supportDim_le_one_of_support_inter_subset t htm (by rw [hsuppX]; exact hsupp)
  have hImin : ∀ Q ∈ I, Q.asIdeal ∈ J.minimalPrimes := by
    intro Q hQ
    have hQX : Q ∈ Module.support B (B ⧸ J) := by rw [hsuppX]; exact hQ.1
    have hmin := minimal_support_of_supportDim_le_one hdimX hQX hQ.2
    have hJQ : J ≤ Q.asIdeal := by
      rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient] at hQX
      exact hQX
    refine ⟨⟨Q.isPrime, hJQ⟩, fun P' hP' hle => ?_⟩
    have hP'X : (⟨P', hP'.1⟩ : PrimeSpectrum B) ∈ Module.support B (B ⧸ J) := by
      rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
      exact hP'.2
    exact hmin.2 hP'X hle
  have hIfin : I.Finite :=
    ((Ideal.finite_minimalPrimes_of_isNoetherianRing B J).preimage
      (fun a _ b _ h => PrimeSpectrum.ext h)).subset hImin
  -- each periodic length as a sum over `I`
  have hPL : ∀ q : ℕ, AlgebraicGeometry.periodicLength
        (AlgebraicGeometry.twoPeriodicComplex
          (0 : Module.End B (((Tor (ModuleCat.{u} B) q).obj M).obj N))
          (LinearMap.lsmul B (((Tor (ModuleCat.{u} B) q).obj M).obj N) t)
          (zero_mul _) (mul_zero _)) =
      ∑ Q ∈ hIfin.toFinset,
        ((Ring.ord (B ⧸ Q.asIdeal) (Ideal.Quotient.mk Q.asIdeal t)).toNat : ℤ) *
          ((Module.length (Localization.AtPrime Q.asIdeal)
            (LocalizedModule Q.asIdeal.primeCompl
              (((Tor (ModuleCat.{u} B) q).obj M).obj N))).toNat : ℤ) := by
    intro q
    have := hfinT q
    have hTsupp : Module.support B (((Tor (ModuleCat.{u} B) q).obj M).obj N) ∩
        PrimeSpectrum.zeroLocus {t} ⊆ {IsLocalRing.closedPoint B} := fun Q hQ =>
      hsupp ⟨hsuppT q hQ.1, hQ.2⟩
    rw [AlgebraicGeometry.periodicLength_mul_eq_finsum_support t
      (supportDim_le_one_of_support_inter_subset t htm hTsupp)
      (supportDim_nonpos_of_support_subset (by rw [Module.support_quotSMulTop]; exact hTsupp)),
      ← finsum_mem_eq_finite_toFinset_sum]
    refine finsum_mem_inter_support_eq' _ _ _ fun Q hQ => ?_
    refine ⟨fun h => ⟨hsuppT q h.1, h.2⟩, fun h => ⟨?_, h.2⟩⟩
    by_contra hns
    apply hQ
    have : Subsingleton (LocalizedModule Q.asIdeal.primeCompl
        (((Tor (ModuleCat.{u} B) q).obj M).obj N)) := by
      rw [Module.mem_support_iff, not_nontrivial_iff_subsingleton] at hns
      exact hns
    simp [Module.length_eq_zero]
  rw [← hL, hA, hR, finsum_mem_eq_finite_toFinset_sum _ hIfin]
  simp_rw [hPL, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun Q _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end Main

end Stacks.Intersection.PrincipalQuotientTor

end
