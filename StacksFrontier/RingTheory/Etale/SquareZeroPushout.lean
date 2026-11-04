module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Pushouts of rings along a flat square-zero thickening

Let `ι : A → B` and `d₀, d₁ : B → C` be ring maps with `d₀ ∘ ι = d₁ ∘ ι`, and let `C` be flat over
`A` through `d₀ ∘ ι`. Suppose that, modulo a square-zero ideal `I` of `A`, the square is a
pushout: `ψ : A → A₀` is surjective with kernel `I`, `qB : B → B₀` is surjective with kernel `IB`,
`qC : C → C₀` has kernel `ker(qB) C`, and `C₀ = B₀ ⊗_{A₀} B₀` through the reductions `d₀', d₁'`
of `d₀, d₁`. Then the square itself is a pushout: `C = B ⊗_A B`.

This is the deformation step of the first-order affine case of Stacks 05ZR. Over the square-zero
thickening `A₀ ⊂ A`, a cocartesian square whose corner is flat is cocartesian as soon as its
reduction is.

## Main results

* `CommRingCat.isPushout_of_isPushout_reduction`: the statement above.

## Implementation notes

Write `T = B ⊗_A B` and `P : T → C` for the map `b ⊗ b' ↦ d₀(b) d₁(b')`. The pushout `C₀`
receives a map back to `T / IT`, so the reduction `T → C₀` of `P` is surjective with kernel `IT`.
The kernel of `qC` is `IC`, which squares to zero, so it lies in the image of `P`, and `P` is
surjective. For injectivity, an element `t = Σ aᵢ tᵢ` of the kernel lies in `IT` with `aᵢ ∈ I`.
The equational criterion of flatness for `C` (`Module.Flat.isTrivialRelation_of_sum_smul_eq_zero`)
rewrites the relation `Σ aᵢ P(tᵢ) = 0` as a trivial one. Lifting it through `P` shows that `t`
lies in `I · IT = 0`. Flatness of `ι` and `d₀` enters only through flatness of `C` over `A`.

## References

* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
-/

@[expose] public section


open CategoryTheory TensorProduct

universe u

namespace CommRingCat

/-- Two elements of the extension of a square-zero ideal along a ring map multiply to zero. -/
private theorem mul_eq_zero_of_mem_map_of_sq_eq_bot {R S : Type*} [CommRing R] [CommRing S]
    {I : Ideal R} (f : R →+* S) (hI : I ^ 2 = ⊥) {x y : S} (hx : x ∈ I.map f) (hy : y ∈ I.map f) :
    x * y = 0 := by
  have : x * y ∈ I.map f ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hx hy
  rwa [← Ideal.map_pow, hI, Ideal.map_bot] at this

/-- **A square of rings that is a pushout modulo a square-zero ideal, with flat corner, is a
pushout.** Let `ι : A → B` and `d₀, d₁ : B → C` satisfy `d₀ ∘ ι = d₁ ∘ ι`, with `ι` and `d₀` flat.
Let `ψ : A → A₀` be surjective with square-zero kernel `I`, and let `qB : B → B₀` be surjective
with kernel `IB`, compatible with `ψ` through `φ : A₀ → B₀`. Let `qC : C → C₀` have kernel
`d₀(ker qB) C`, and let `d₀', d₁' : B₀ → C₀` be the reductions of `d₀, d₁`. If `C₀` is the pushout
of `φ` along itself through `d₀', d₁'`, then `C` is the pushout of `ι` along itself through
`d₀, d₁`. -/
theorem isPushout_of_isPushout_reduction {A A₀ B B₀ C C₀ : Type u} [CommRing A] [CommRing A₀]
    [CommRing B] [CommRing B₀] [CommRing C] [CommRing C₀]
    (ι : A →+* B) (hι : ι.Flat) (d₀ d₁ : B →+* C) (hd : d₀.comp ι = d₁.comp ι) (hfd₀ : d₀.Flat)
    (qB : B →+* B₀) (qC : C →+* C₀) (hqB : Function.Surjective qB)
    (ψ : A →+* A₀) (hψ : Function.Surjective ψ) (φ : A₀ →+* B₀) (hφψ : φ.comp ψ = qB.comp ι)
    (hI : RingHom.ker ψ ^ 2 = ⊥) (hJI : RingHom.ker qB = Ideal.map ι (RingHom.ker ψ))
    (d₀' d₁' : B₀ →+* C₀) (hd₀ : qC.comp d₀ = d₀'.comp qB) (hd₁ : qC.comp d₁ = d₁'.comp qB)
    (hC : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom φ) (CommRingCat.ofHom d₀')
      (CommRingCat.ofHom d₁'))
    (hK₀ : RingHom.ker qC = Ideal.map d₀ (RingHom.ker qB)) :
    IsPushout (CommRingCat.ofHom ι) (CommRingCat.ofHom ι) (CommRingCat.ofHom d₀)
      (CommRingCat.ofHom d₁) := by
  let : Algebra A B := ι.toAlgebra
  let : Algebra A C := (d₀.comp ι).toAlgebra
  have hfl : Module.Flat A C := RingHom.Flat.comp hι hfd₀
  set I := RingHom.ker ψ
  let D₀ : B →ₐ[A] C := { d₀ with commutes' := fun _ => rfl }
  let D₁ : B →ₐ[A] C := { d₁ with commutes' := fun a => (RingHom.congr_fun hd a).symm }
  let P : B ⊗[A] B →ₐ[A] C := Algebra.TensorProduct.productMap D₀ D₁
  have hPt : ∀ b b' : B, P (b ⊗ₜ b') = d₀ b * d₁ b' := fun b b' =>
    Algebra.TensorProduct.productMap_apply_tmul D₀ D₁ b b'
  set IT : Ideal (B ⊗[A] B) := Ideal.map (algebraMap A (B ⊗[A] B)) I with hIT
  -- elements of `I` vanish downstairs
  have hqBι : ∀ a ∈ I, qB (ι a) = 0 := fun a ha => by
    rw [← RingHom.comp_apply, ← hφψ, RingHom.comp_apply, RingHom.mem_ker.mp ha, map_zero]
  have hqCι : ∀ a ∈ I, qC (d₀ (ι a)) = 0 := fun a ha => by
    rw [← RingHom.comp_apply qC d₀, hd₀, RingHom.comp_apply, hqBι a ha, map_zero]
  -- the reduction of `P`
  let μ : B ⊗[A] B →+* C₀ := qC.comp (P : B ⊗[A] B →+* C)
  have hμt : ∀ b b' : B, μ (b ⊗ₜ b') = d₀' (qB b) * d₁' (qB b') := fun b b' => by
    change qC (P (b ⊗ₜ b')) = _
    rw [hPt, map_mul, ← RingHom.comp_apply qC d₀, ← RingHom.comp_apply qC d₁, hd₀, hd₁]
    rfl
  have hITμ : ∀ x ∈ IT, μ x = 0 := by
    suffices IT ≤ RingHom.ker μ from fun x hx => this hx
    rw [hIT, Ideal.map_le_iff_le_comap]
    intro a ha
    change qC (P (algebraMap A (B ⊗[A] B) a)) = 0
    rw [AlgHom.commutes]
    exact hqCι a ha
  let μ' : (B ⊗[A] B) ⧸ IT →+* C₀ := Ideal.Quotient.lift IT μ hITμ
  -- the inverse of the reduction, out of the pushout `C₀`
  have hk : ∀ f : B →+* B ⊗[A] B, (∀ a, f (ι a) = algebraMap A (B ⊗[A] B) a) →
      RingHom.ker qB ≤ RingHom.ker ((Ideal.Quotient.mk IT).comp f) := fun f hf => by
    rw [hJI, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, hf]
    exact Ideal.mem_map_of_mem _ ha
  have hk₀ := hk Algebra.TensorProduct.includeLeftRingHom fun a =>
    (Algebra.TensorProduct.algebraMap_apply (R := A) (A := B) (B := B) a).symm
  have hk₁ := hk Algebra.TensorProduct.includeRight.toRingHom fun a =>
    (Algebra.TensorProduct.algebraMap_apply' a).symm
  let e₀ : B₀ →+* (B ⊗[A] B) ⧸ IT := qB.liftOfSurjective hqB ⟨_, hk₀⟩
  let e₁ : B₀ →+* (B ⊗[A] B) ⧸ IT := qB.liftOfSurjective hqB ⟨_, hk₁⟩
  have he₀ : ∀ b, e₀ (qB b) = Ideal.Quotient.mk IT (b ⊗ₜ 1) := fun b =>
    qB.liftOfSurjective_comp_apply hqB ⟨_, hk₀⟩ b
  have he₁ : ∀ b, e₁ (qB b) = Ideal.Quotient.mk IT (1 ⊗ₜ b) := fun b =>
    qB.liftOfSurjective_comp_apply hqB ⟨_, hk₁⟩ b
  have he : e₀.comp φ = e₁.comp φ := by
    ext x
    obtain ⟨a, rfl⟩ := hψ x
    rw [RingHom.comp_apply, RingHom.comp_apply, ← RingHom.comp_apply φ ψ, hφψ,
      RingHom.comp_apply, he₀, he₁]
    have hswap : ι a ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] ι a :=
      (Algebra.TensorProduct.algebraMap_apply (R := A) (A := B) (B := B) a).symm.trans
        (Algebra.TensorProduct.algebraMap_apply' a)
    rw [hswap]
  let χ : CommRingCat.of C₀ ⟶ CommRingCat.of ((B ⊗[A] B) ⧸ IT) :=
    hC.desc (CommRingCat.ofHom e₀) (CommRingCat.ofHom e₁) (by
      rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, he])
  have hχ₀ : ∀ x, χ.hom (d₀' x) = e₀ x := fun x =>
    congrArg (fun g => g.hom x) (hC.inl_desc (CommRingCat.ofHom e₀) (CommRingCat.ofHom e₁) _)
  have hχ₁ : ∀ x, χ.hom (d₁' x) = e₁ x := fun x =>
    congrArg (fun g => g.hom x) (hC.inr_desc (CommRingCat.ofHom e₀) (CommRingCat.ofHom e₁) _)
  have hχμ : ∀ t, χ.hom (μ t) = Ideal.Quotient.mk IT t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b b' =>
        rw [hμt, map_mul, hχ₀, hχ₁, he₀, he₁, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul,
          mul_one, one_mul]
    | add s t hs ht => rw [map_add, map_add, hs, ht, map_add]
  have hμ'χ : ∀ c, μ' (χ.hom c) = c := by
    have h : χ ≫ CommRingCat.ofHom μ' = 𝟙 _ := by
      refine hC.hom_ext ?_ ?_
      · ext x
        obtain ⟨b, rfl⟩ := hqB x
        change μ' (χ.hom (d₀' (qB b))) = d₀' (qB b)
        rw [hχ₀, he₀, Ideal.Quotient.lift_mk, hμt, map_one, map_one, mul_one]
      · ext x
        obtain ⟨b, rfl⟩ := hqB x
        change μ' (χ.hom (d₁' (qB b))) = d₁' (qB b)
        rw [hχ₁, he₁, Ideal.Quotient.lift_mk, hμt, map_one, map_one, one_mul]
    intro c
    exact congrArg (fun g => g.hom c) h
  have hμsurj : Function.Surjective μ := by
    intro c
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (χ.hom c)
    refine ⟨t, ?_⟩
    rw [← hμ'χ c, ← ht, Ideal.Quotient.lift_mk]
  have hkerμ : ∀ t, μ t = 0 → t ∈ IT := by
    intro t ht
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hχμ, ht, map_zero]
  -- `P` is surjective
  have hK : RingHom.ker qC = Ideal.map (algebraMap A C) I := by
    rw [hK₀, hJI, Ideal.map_map]
    rfl
  have hdecomp : ∀ c : C, ∃ t, c - P t ∈ RingHom.ker qC := by
    intro c
    obtain ⟨t, ht⟩ := hμsurj (qC c)
    refine ⟨t, ?_⟩
    rw [RingHom.mem_ker, map_sub, ← ht]
    exact sub_self _
  have hgen : ∀ a ∈ I, ∀ c : C, c * algebraMap A C a ∈ (P.range : Set C) := by
    intro a ha c
    obtain ⟨t, ht⟩ := hdecomp c
    have hk : (c - P t) * algebraMap A C a = 0 :=
      mul_eq_zero_of_mem_map_of_sq_eq_bot _ hI (hK ▸ ht) (Ideal.mem_map_of_mem _ ha)
    refine ⟨t * algebraMap A (B ⊗[A] B) a, ?_⟩
    change P (t * algebraMap A (B ⊗[A] B) a) = _
    rw [map_mul, AlgHom.commutes]
    rw [sub_mul, sub_eq_zero] at hk
    exact hk.symm
  have hKP : ∀ k ∈ RingHom.ker qC, ∀ c : C, c * k ∈ (P.range : Set C) := by
    intro k hk
    rw [hK] at hk
    induction hk using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨a, ha, rfl⟩ := hx
        exact hgen a ha
    | zero => intro c; rw [mul_zero]; exact P.range.zero_mem
    | add x y _ _ hx hy => intro c; rw [mul_add]; exact P.range.add_mem (hx c) (hy c)
    | smul c' x _ hx => intro c; rw [smul_eq_mul, ← mul_assoc]; exact hx (c * c')
  have hPsurj : Function.Surjective P := by
    intro c
    obtain ⟨t, ht⟩ := hdecomp c
    obtain ⟨s, hs⟩ := hKP _ ht 1
    change P s = _ at hs
    refine ⟨t + s, ?_⟩
    rw [map_add, hs, one_mul, add_sub_cancel]
  -- `P` is injective
  have hPinj : Function.Injective P := by
    rw [injective_iff_map_eq_zero]
    intro t ht
    have htIT : t ∈ IT := hkerμ t (by change qC (P t) = 0; rw [ht, map_zero])
    have htsm : t ∈ I • (⊤ : Submodule A (B ⊗[A] B)) := by
      rw [Ideal.smul_top_eq_map]; exact htIT
    have hspan : (⊤ : Submodule A (B ⊗[A] B)) = Submodule.span A (Set.range id) := by
      rw [Set.range_id, Submodule.span_univ]
    rw [hspan, Submodule.mem_ideal_smul_span_iff_exists_sum] at htsm
    obtain ⟨a, haI, hat⟩ := htsm
    have htsum : t = ∑ i : a.support, a i • (i : B ⊗[A] B) := by
      rw [← hat, Finsupp.sum]
      exact (Finset.sum_coe_sort a.support (fun i => a i • id i)).symm
    have hsum : ∑ i : a.support, a i • P (i : B ⊗[A] B) = 0 := by
      rw [← ht, htsum, map_sum]
      exact Finset.sum_congr rfl fun i _ => (map_smul P _ _).symm
    obtain ⟨k, b, y, hy, hb⟩ := @Module.Flat.isTrivialRelation_of_sum_smul_eq_zero A C _ _ _ hfl
      _ _ (fun i : a.support => a i) (fun i : a.support => P (i : B ⊗[A] B)) hsum
    choose z hz using fun j => hPsurj (y j)
    have hw : ∀ i : a.support, (i : B ⊗[A] B) - ∑ j, b i j • z j ∈ IT := by
      intro i
      refine hkerμ _ ?_
      have h0 : P ((i : B ⊗[A] B) - ∑ j, b i j • z j) = 0 := by
        rw [map_sub, map_sum]
        simp only [map_smul, hz]
        rw [← hy i, sub_self]
      change qC (P _) = 0
      rw [h0, map_zero]
    have hIT0 : ∀ x : A, x ∈ I → ∀ w ∈ IT, x • w = 0 := by
      intro x hx w hw
      rw [Algebra.smul_def]
      exact mul_eq_zero_of_mem_map_of_sq_eq_bot _ hI (Ideal.mem_map_of_mem _ hx) hw
    have hsplit : t = ∑ i : a.support, a i • ((i : B ⊗[A] B) - ∑ j, b i j • z j) +
        ∑ i : a.support, a i • ∑ j, b i j • z j := by
      rw [← Finset.sum_add_distrib, htsum]
      exact Finset.sum_congr rfl fun i _ => by rw [← smul_add, sub_add_cancel]
    have hsecond : ∑ i : a.support, a i • ∑ j, b i j • z j =
        ∑ j, (∑ i : a.support, a i * b i j) • z j := by
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [Finset.sum_smul]
    rw [hsplit, hsecond, Finset.sum_eq_zero fun (i : a.support) _ => hIT0 _ (haI i) _ (hw i),
      Finset.sum_eq_zero fun j _ => by rw [hb j, zero_smul], add_zero]
  -- assemble
  let e : B ⊗[A] B ≃+* C := RingEquiv.ofBijective (P : B ⊗[A] B →+* C) ⟨hPinj, hPsurj⟩
  refine (CommRingCat.isPushout_tensorProduct A B B).of_iso (Iso.refl _) (Iso.refl _)
    (Iso.refl _) e.toCommRingCatIso ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · ext b
    change P (b ⊗ₜ 1) = d₀ b
    rw [hPt, map_one, mul_one]
  · ext b
    change P (1 ⊗ₜ b) = d₁ b
    rw [hPt, map_one, one_mul]

end CommRingCat

end
