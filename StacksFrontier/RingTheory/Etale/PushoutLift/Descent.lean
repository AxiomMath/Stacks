module

public import StacksFrontier.RingTheory.Etale.PushoutLift.Groupoid
public import Mathlib.RingTheory.Etale.Descent
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Over

/-!
# The ring of the thickening

An effective lifted Čech groupoid `Γ ⇉ Δ` of the faithfully flat étale map `B₀ → Γ₀` comes
with a faithfully flat ring map `B → Γ` with `Γ ⊗[B] Γ ≅ Δ`. We show (`exists_thickening`) that

* `B` is an `A`-algebra and `B → Γ` is étale and faithfully flat;
* there is a surjection `π : B → B₀` of `A`-algebras with kernel `J B`, compatible with the maps
  to `Γ₀`.

The surjectivity of `π` is the degree-zero descent for the faithfully flat map
`B ⧸ J B → Γ ⧸ J Γ`: an element of `Γ₀` coming from `B₀` has equal images in
`Γ₀ ⊗[B₀] Γ₀ = Δ ⧸ J Δ`, hence its lift to `Γ` has images in `Γ ⊗[B] Γ = Δ` which agree modulo
`J`, hence it comes from `B ⧸ J B`.

## Main definitions

* `cmpAlgHom`: The comparison map `Γ ⊗[B] Γ → Δ` as a map of `Γ`-algebras.
* `reductionRingHom`: The ring map `B → B₀` through which `B → Γ → Γ₀` factors.

## Main results

* `etale_of_isEffective`: The map `B → Γ` is étale.
* `reductionRingHom_surjective`: The ring map `B → B₀` is surjective.
* `exists_thickening`: An effective lifted Čech groupoid yields an étale, faithfully flat
  `A`-algebra `B → Γ` with a surjection onto `B₀` whose kernel is `J B`.

## References

* [Stacks Project, Tag 0ALT](https://stacks.math.columbia.edu/tag/0ALT)
-/

@[expose] public section

open TensorProduct Module.Descent.SquareZero

universe u

namespace Stacks.Etale.PushoutLift

/-- A ring map into the range of an injective ring map factors through it. -/
noncomputable def factorRange {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (ι : S →+* T) (hι : Function.Injective ι) (f : R →+* T) (hf : ∀ r, f r ∈ Set.range ι) :
    R →+* S :=
  (RingEquiv.ofBijective ι.rangeRestrict ⟨fun _ _ h => hι (congrArg Subtype.val h),
    ι.rangeRestrict_surjective⟩).symm.toRingHom.comp (f.codRestrict ι.range hf)

/-- The factorization `factorRange ι hι f hf` composed with `ι` is `f`. -/
lemma factorRange_spec {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (ι : S →+* T) (hι : Function.Injective ι) (f : R →+* T) (hf : ∀ r, f r ∈ Set.range ι)
    (r : R) : ι (factorRange ι hι f hf r) = f r := by
  exact congrArg Subtype.val ((RingEquiv.ofBijective ι.rangeRestrict
    ⟨fun _ _ h => hι (congrArg Subtype.val h), ι.rangeRestrict_surjective⟩).apply_symm_apply
    (f.codRestrict ι.range hf r))

/-- If `γ ⊗ 1 - 1 ⊗ γ` lies in `K • (Γ ⊗[B] Γ)`, then the image of `γ` in `Γ ⧸ K Γ` has equal
images in `(Γ ⧸ K Γ) ⊗[B ⧸ K] (Γ ⧸ K Γ)`. -/
lemma includeLeftSubRight_mk_eq_zero_of_mem {B Γ : Type*} [CommRing B] [CommRing Γ]
    [Algebra B Γ] (K : Ideal B) (γ : Γ)
    (h : γ ⊗ₜ[B] (1 : Γ) - 1 ⊗ₜ γ ∈ K • (⊤ : Submodule B (Γ ⊗[B] Γ))) :
    Algebra.TensorProduct.includeLeftSubRight (B ⧸ K) (Γ ⧸ K.map (algebraMap B Γ))
      (Ideal.Quotient.mk (K.map (algebraMap B Γ)) γ) = 0 := by
  let q : Γ →+* Γ ⧸ K.map (algebraMap B Γ) := Ideal.Quotient.mk _
  have hq : ∀ (b : B) (x : Γ), q (b • x) = (Ideal.Quotient.mk K b) • q x := fun b x => by
    rw [Algebra.smul_def, map_mul, Algebra.smul_def]
    rfl
  let f : Γ →+ Γ →+ (Γ ⧸ K.map (algebraMap B Γ)) ⊗[B ⧸ K] (Γ ⧸ K.map (algebraMap B Γ)) :=
    AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => q x ⊗ₜ q y)
      (fun y y' => by rw [map_add, TensorProduct.tmul_add]))
      (fun x x' => by ext y; simp [TensorProduct.add_tmul])
  let ρ : Γ ⊗[B] Γ →+ (Γ ⧸ K.map (algebraMap B Γ)) ⊗[B ⧸ K] (Γ ⧸ K.map (algebraMap B Γ)) :=
    TensorProduct.liftAddHom f (fun b x y => by
      show q (b • x) ⊗ₜ q y = q x ⊗ₜ q (b • y)
      rw [hq, hq, TensorProduct.smul_tmul])
  have hρk : ∀ k ∈ K, ∀ w : Γ ⊗[B] Γ, ρ (k • w) = 0 := by
    intro k hk w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      rw [TensorProduct.smul_tmul']
      show q (k • x) ⊗ₜ q y = 0
      rw [hq, Ideal.Quotient.eq_zero_iff_mem.mpr hk, zero_smul, TensorProduct.zero_tmul]
    | add w w' h h' => rw [smul_add, map_add, h, h', add_zero]
  have hρ : ∀ w ∈ K • (⊤ : Submodule B (Γ ⊗[B] Γ)), ρ w = 0 := fun w hw =>
    Submodule.smul_induction_on hw (fun k hk w _ => hρk k hk w)
      (fun _ _ h h' => by rw [map_add, h, h', add_zero])
  rw [Algebra.TensorProduct.includeLeftSubRight_apply]
  have := hρ _ h
  rw [map_sub] at this
  convert this using 2 <;> simp [ρ, f, q]

variable {A : Type u} [CommRing A] (I J : Ideal A) (hJ : IsNilpotent J)
variable {B₀ : Type u} [CommRing B₀] [Algebra A B₀]
variable {Γ₀ : Type u} [CommRing Γ₀] [Algebra A Γ₀] [Algebra B₀ Γ₀] [IsScalarTower A B₀ Γ₀]
variable {Γ : Type u} [CommRing Γ] [Algebra A Γ] [Algebra Γ Γ₀] [IsScalarTower A Γ Γ₀]
variable [Module.FaithfullyFlat B₀ Γ₀]
variable (hΓ₀ : Function.Surjective (algebraMap Γ Γ₀))
  (hΓ₀ker : RingHom.ker (algebraMap Γ Γ₀) = J.map (algebraMap A Γ))
variable {Δ : Type u} [CommRing Δ] [Algebra Γ Δ] [Algebra.Etale Γ Δ]
  (ψ : Δ →ₐ[Γ] Γ₀ ⊗[B₀] Γ₀) (s : Γ →+* Δ)
  (hψ : Function.Surjective ψ)
  (hψker : RingHom.ker (ψ : Δ →+* Γ₀ ⊗[B₀] Γ₀) = (J.map (algebraMap A Γ)).map (algebraMap Γ Δ))
  (hsψ : ∀ x, ψ (s x) = Algebra.TensorProduct.includeRight (algebraMap Γ Γ₀ x))
  (hsA : ∀ a, s (algebraMap A Γ a) = algebraMap Γ Δ (algebraMap A Γ a))

section Effective

variable {B : Type u} [CommRing B] [Algebra B Γ]
  (hB : ∀ b, s (algebraMap B Γ b) = algebraMap Γ Δ (algebraMap B Γ b))
  [Module.FaithfullyFlat B Γ] (hbij : Function.Bijective (cmp s B hB))

/-- The comparison `Γ ⊗[B] Γ → Δ`, as a map of `Γ`-algebras. -/
noncomputable def cmpAlgHom : Γ ⊗[B] Γ →ₐ[Γ] Δ :=
  letI : Algebra B Δ := ((algebraMap Γ Δ).comp (algebraMap B Γ)).toAlgebra
  haveI : IsScalarTower B Γ Δ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  Algebra.TensorProduct.lift (Algebra.ofId Γ Δ)
    ({ s with commutes' := fun b => hB b } : Γ →ₐ[B] Δ) fun _ _ => Commute.all _ _

omit [Algebra.Etale Γ Δ] [Module.FaithfullyFlat B Γ] in
/-- The underlying function of `cmpAlgHom` is `cmp`. -/
lemma cmpAlgHom_apply (z : Γ ⊗[B] Γ) : cmpAlgHom s hB z = cmp s B hB z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rfl
  | add z w hz hw => rw [map_add, map_add, hz, hw]

include hbij in
/-- **`B → Γ` is étale** when the comparison `Γ ⊗[B] Γ → Δ` is bijective. -/
theorem etale_of_isEffective : Algebra.Etale B Γ := by
  have hb : Function.Bijective (cmpAlgHom s hB) := by
    rwa [show (cmpAlgHom s hB : Γ ⊗[B] Γ → Δ) = cmp s B hB from funext (cmpAlgHom_apply s hB)]
  have : Algebra.Etale Γ (Γ ⊗[B] Γ) := Algebra.Etale.of_equiv (AlgEquiv.ofBijective _ hb).symm
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat Γ

omit [Algebra.Etale Γ Δ] in
include hbij hsA in
/-- The image of `A` in `Γ` lies in the image of `B`. -/
lemma algebraMap_mem_range (a : A) : algebraMap A Γ a ∈ Set.range (algebraMap B Γ) :=
  mem_range_of_eq s hB hbij (hsA a)

/-- The `A`-algebra structure on `B`. -/
noncomputable abbrev algebraOfEffective : Algebra A B :=
  (factorRange (algebraMap B Γ) (FaithfulSMul.algebraMap_injective B Γ) (algebraMap A Γ)
    (algebraMap_mem_range s hsA hB hbij)).toAlgebra

section Reduction

omit [Algebra.Etale Γ Δ] [Module.FaithfullyFlat B Γ] in
include hB hsψ in
/-- The reduction `B → Γ → Γ₀` lands in the image of `B₀`. -/
lemma reduction_mem_range (b : B) :
    algebraMap Γ Γ₀ (algebraMap B Γ b) ∈ Set.range (algebraMap B₀ Γ₀) := by
  refine (Algebra.IsEffective.of_faithfullyFlat B₀ Γ₀ _).mp ?_
  rw [Algebra.TensorProduct.includeLeftSubRight_apply, sub_eq_zero]
  have h1 := congrArg ψ (hB b)
  rw [hsψ, AlgHom.commutes] at h1
  exact h1.symm

/-- The reduction `B → B₀`, as a ring map. -/
noncomputable def reductionRingHom : B →+* B₀ :=
  factorRange (algebraMap B₀ Γ₀) (FaithfulSMul.algebraMap_injective B₀ Γ₀)
    ((algebraMap Γ Γ₀).comp (algebraMap B Γ)) (reduction_mem_range ψ s hsψ hB)

omit [Algebra.Etale Γ Δ] [Module.FaithfullyFlat B Γ] in
/-- The composite of `reductionRingHom` with `B₀ → Γ₀` is the composite `B → Γ → Γ₀`. -/
lemma algebraMap_reductionRingHom (b : B) :
    algebraMap B₀ Γ₀ (reductionRingHom ψ s hsψ hB b) = algebraMap Γ Γ₀ (algebraMap B Γ b) :=
  factorRange_spec _ _ _ _ b

omit [Algebra.Etale Γ Δ] [Module.FaithfullyFlat B Γ] in
include hbij in
/-- Every element of the ideal of `Δ` generated by an ideal `K` of `B` is the image under
`cmp` of an element of `K • (Γ ⊗[B] Γ)`. -/
lemma exists_cmp_eq_of_mem (K : Ideal B) {δ : Δ}
    (hδ : δ ∈ (K.map (algebraMap B Γ)).map (algebraMap Γ Δ)) :
    ∃ z ∈ K • (⊤ : Submodule B (Γ ⊗[B] Γ)), cmp s B hB z = δ := by
  rw [Ideal.map_map] at hδ
  induction hδ using Submodule.span_induction with
  | mem δ hδ =>
    obtain ⟨k, hk, rfl⟩ := hδ
    refine ⟨k • (1 ⊗ₜ 1), Submodule.smul_mem_smul hk Submodule.mem_top, ?_⟩
    rw [TensorProduct.smul_tmul', cmp_tmul, Algebra.smul_def, mul_one, map_one, mul_one]
    rfl
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | add δ δ' _ _ h h' =>
    obtain ⟨z, hz, rfl⟩ := h
    obtain ⟨z', hz', rfl⟩ := h'
    exact ⟨z + z', add_mem hz hz', map_add _ _ _⟩
  | smul d δ _ h =>
    obtain ⟨z, hz, rfl⟩ := h
    obtain ⟨w, rfl⟩ := hbij.2 d
    refine ⟨w * z, ?_, ?_⟩
    · refine Submodule.smul_induction_on hz (fun k hk y _ => ?_) (fun _ _ h h' => ?_)
      · rw [mul_smul_comm]
        exact Submodule.smul_mem_smul hk Submodule.mem_top
      · rw [mul_add]
        exact add_mem h h'
    · rw [smul_eq_mul, ← cmpAlgHom_apply, ← cmpAlgHom_apply, ← cmpAlgHom_apply, map_mul]

omit [Algebra A B₀] [Algebra A Γ₀] [IsScalarTower A B₀ Γ₀] [IsScalarTower A Γ Γ₀]
  [Algebra.Etale Γ Δ] in
include hΓ₀ hΓ₀ker hψker hbij in
/-- **The reduction `B → B₀` is surjective.** -/
theorem reductionRingHom_surjective (hK : (J.map (algebraMap A Γ)) =
    ((J.map (algebraMap A Γ)).comap (algebraMap B Γ)).map (algebraMap B Γ)) :
    Function.Surjective (reductionRingHom ψ s hsψ hB) := by
  classical
  intro β
  set K : Ideal B := (J.map (algebraMap A Γ)).comap (algebraMap B Γ)
  set y := algebraMap B₀ Γ₀ β
  obtain ⟨γ, hγ⟩ := hΓ₀ y
  have hγΔ : algebraMap Γ Δ γ - s γ ∈ (K.map (algebraMap B Γ)).map (algebraMap Γ Δ) := by
    rw [← hK, ← hψker, RingHom.mem_ker, map_sub]
    show ψ (algebraMap Γ Δ γ) - ψ (s γ) = 0
    rw [hsψ, AlgHom.commutes]
    show algebraMap Γ Γ₀ γ ⊗ₜ[B₀] (1 : Γ₀) - 1 ⊗ₜ algebraMap Γ Γ₀ γ = 0
    rw [hγ]
    simp only [y, Algebra.algebraMap_eq_smul_one β, TensorProduct.smul_tmul, sub_self]
  obtain ⟨z, hz, hzδ⟩ := exists_cmp_eq_of_mem s hB hbij K hγΔ
  have hzeq : γ ⊗ₜ[B] (1 : Γ) - 1 ⊗ₜ γ = z := by
    apply hbij.1
    rw [hzδ, map_sub, cmp_tmul, cmp_tmul, map_one, mul_one, map_one, one_mul]
  have : Module.FaithfullyFlat (B ⧸ K) (Γ ⧸ K.map (algebraMap B Γ)) :=
    Module.FaithfullyFlat.of_linearEquiv _ ((B ⧸ K) ⊗[B] Γ)
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor Γ K).toLinearEquiv
  have h0 := includeLeftSubRight_mk_eq_zero_of_mem K γ (hzeq ▸ hz)
  obtain ⟨r, hr⟩ := (Algebra.IsEffective.of_faithfullyFlat _ _ _).mp h0
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective r
  refine ⟨b, FaithfulSMul.algebraMap_injective B₀ Γ₀ ?_⟩
  rw [algebraMap_reductionRingHom]
  show algebraMap Γ Γ₀ (algebraMap B Γ b) = y
  rw [← hγ, ← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, hΓ₀ker, hK, ← Ideal.Quotient.eq]
  exact hr

end Reduction

end Effective

include hΓ₀ hΓ₀ker hψker hsψ hsA in
/-- **The ring of the thickening.** From an effective lifted Čech groupoid `Γ ⇉ Δ` one obtains an
`A`-algebra `B` with an étale, faithfully flat map `B → Γ` and a surjection `π : B → B₀` with
kernel `J B`, compatible with the maps to `Γ₀`. -/
theorem exists_thickening (heff : IsEffective s) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : Algebra B Γ)
      (_ : IsScalarTower A B Γ) (π : B →ₐ[A] B₀),
      Function.Surjective π ∧ RingHom.ker (π : B →+* B₀) = J.map (algebraMap A B) ∧
      (∀ b, algebraMap B₀ Γ₀ (π b) = algebraMap Γ Γ₀ (algebraMap B Γ b)) ∧
      Algebra.Etale B Γ ∧ Module.FaithfullyFlat B Γ := by
  obtain ⟨B, _, _, hB, hff, hbij⟩ := heff
  let : Algebra A B := algebraOfEffective s hsA hB hbij
  have htow : ∀ a, algebraMap B Γ (algebraMap A B a) = algebraMap A Γ a :=
    factorRange_spec _ _ _ _
  have : IsScalarTower A B Γ := IsScalarTower.of_algebraMap_eq fun a => (htow a).symm
  have hJΓ : J.map (algebraMap A Γ) = (J.map (algebraMap A B)).map (algebraMap B Γ) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hcomap : (J.map (algebraMap A Γ)).comap (algebraMap B Γ) = J.map (algebraMap A B) := by
    rw [hJΓ, Ideal.comap_map_eq_self_of_faithfullyFlat]
  have hK : J.map (algebraMap A Γ) =
      ((J.map (algebraMap A Γ)).comap (algebraMap B Γ)).map (algebraMap B Γ) := by
    rw [hcomap, hJΓ]
  let π : B →ₐ[A] B₀ :=
    { reductionRingHom ψ s hsψ hB with
      commutes' := fun a => by
        apply FaithfulSMul.algebraMap_injective B₀ Γ₀
        show algebraMap B₀ Γ₀ (reductionRingHom ψ s hsψ hB (algebraMap A B a)) = _
        rw [algebraMap_reductionRingHom, htow, ← IsScalarTower.algebraMap_apply,
          IsScalarTower.algebraMap_apply A B₀ Γ₀] }
  have hπ : ∀ b, algebraMap B₀ Γ₀ (π b) = algebraMap Γ Γ₀ (algebraMap B Γ b) :=
    algebraMap_reductionRingHom ψ s hsψ hB
  refine ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, π,
    reductionRingHom_surjective J hΓ₀ hΓ₀ker ψ s hψker hsψ hB hbij hK, ?_, hπ,
    etale_of_isEffective s hB hbij, hff⟩
  ext b
  rw [RingHom.mem_ker, ← hcomap, Ideal.mem_comap, ← hΓ₀ker, RingHom.mem_ker, ← hπ,
    map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective B₀ Γ₀)]
  rfl

end Stacks.Etale.PushoutLift

end
