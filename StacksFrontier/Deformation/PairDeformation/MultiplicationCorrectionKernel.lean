module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import StacksFrontier.Deformation.PairDeformation.MultiplicationCorrection
public import StacksFrontier.RingTheory.Etale.SquareZeroEqualizerDescent

/-!
# Killing the square of the kernel of an arrow by a multiplication correction

Let `ρ : R₁ → R₀` be a surjective map of commutative rings with kernel `K`, and
`q : R₁ → O ⊕ L` (the trivial square-zero extension) a surjective map lying over a map
`q₀ : R₀ → O`. Assume the kernel of `q` maps onto the kernel of `q₀`, and that the part of
`ker q` killed by `ρ` is annihilated by `K`. This is the situation of a solution of the extension
problem on the arrow site: there `ker q = G ⊕ G_L`, the part killed by `ρ` is `G_L`, and an
element `(0, l)` of `O ⊕ L` acts on `G_L` by `μ(0 ⊗ l) = 0`.

Then `q` identifies `K` modulo `K ∩ ker q` with `L`, the product `K × K → R₁` factors through a
symmetric `R₁`-bilinear pairing `μ : L × L → R₁` with values in `K ∩ ker q`, and the second
component of `q` is a derivation `π` with `π ∘ μ = 0`. After correcting the multiplication of
`R₁` by `(π, μ)`, the kernel `K` has square zero, so it is a module over `R₁ / K ≅ R₀`; the maps
`ρ` and `q` stay ring maps.

## Main definitions

* `Deformation.PairDeformation.ArrowKernelData`: the hypotheses above.
* `Deformation.PairDeformation.ArrowKernelData.derivation`: `π`, the second component of `q`.
* `Deformation.PairDeformation.ArrowKernelData.pairing`: the pairing `μ` induced by the
  product of `K`.
* `Deformation.PairDeformation.ArrowKernelData.correction`: the multiplication correction
  `(π, μ)`.
* `Deformation.PairDeformation.ArrowKernelData.correctedArrow`,
  `Deformation.PairDeformation.ArrowKernelData.correctedProjection`: `ρ` and `q` out of the
  corrected ring.
* `Deformation.PairDeformation.ArrowKernelData.correctedKernel`: the kernel of the corrected
  arrow.
* `Deformation.PairDeformation.ArrowKernelData.correctedKernelModule`: the corrected kernel as an
  `R₀`-module.

## Main results

* `Deformation.PairDeformation.ArrowKernelData.mul_mem_ker`: `K · K ⊆ ker q ∩ K`.
* `Deformation.PairDeformation.ArrowKernelData.pairing_snd`: `μ(π k, π k') = k k'` on `K`.
* `Deformation.PairDeformation.ArrowKernelData.correctedKernel_sq_eq_bot`: after the correction
  the kernel of the arrow has square zero.

## References

* [Stacks Project, Tag 0D4W](https://stacks.math.columbia.edu/tag/0D4W)
-/

@[expose] public section

namespace Deformation.PairDeformation

open TrivSqZeroExt

variable {R₁ R₀ O L : Type*} [CommRing R₁] [CommRing R₀] [CommRing O] [AddCommGroup L]
  [Module O L] [Module Oᵐᵒᵖ L] [IsCentralScalar O L]

/-- The hypotheses of the kernel correction: a surjective arrow `ρ : R₁ → R₀`, a surjective map
`q : R₁ → O ⊕ L` over a map `q₀ : R₀ → O`, such that `ker q` maps onto `ker q₀` and the part of
`ker q` killed by `ρ` is annihilated by `ker ρ`. -/
structure ArrowKernelData (R₁ R₀ O L : Type*) [CommRing R₁] [CommRing R₀] [CommRing O]
    [AddCommGroup L] [Module O L] [Module Oᵐᵒᵖ L] [IsCentralScalar O L] where
  /-- The arrow. -/
  arrow : R₁ →+* R₀
  /-- The arrow is surjective. -/
  arrow_surjective : Function.Surjective arrow
  /-- The projection onto the trivial square-zero extension. -/
  projection : R₁ →+* TrivSqZeroExt O L
  /-- The projection is surjective. -/
  projection_surjective : Function.Surjective projection
  /-- The projection on the target of the arrow. -/
  baseProjection : R₀ →+* O
  /-- The arrow lies over the augmentation `O ⊕ L → O`. -/
  baseProjection_arrow : ∀ x, baseProjection (arrow x) = (projection x).fst
  /-- The kernel of the projection maps onto the kernel of the base projection. -/
  exists_ker_projection : ∀ y, baseProjection y = 0 → ∃ g, projection g = 0 ∧ arrow g = y
  /-- The part of the kernel of the projection killed by the arrow is annihilated by the kernel
  of the arrow. -/
  mul_eq_zero : ∀ g k, projection g = 0 → arrow g = 0 → arrow k = 0 → g * k = 0

namespace ArrowKernelData

variable (D : ArrowKernelData R₁ R₀ O L)

/-- The projection of an element of the kernel of the arrow has first component zero. -/
theorem fst_projection_of_arrow_eq_zero {k : R₁} (hk : D.arrow k = 0) :
    (D.projection k).fst = 0 := by
  rw [← D.baseProjection_arrow, hk, map_zero]

/-- The projection of an element of the kernel of the arrow lies in `L`: it is `inr` of its
second component. -/
theorem projection_of_arrow_eq_zero {k : R₁} (hk : D.arrow k = 0) :
    D.projection k = inr (D.projection k).snd :=
  TrivSqZeroExt.ext (by rw [D.fst_projection_of_arrow_eq_zero hk, fst_inr]) rfl

/-- **The product of the kernel of the arrow lies in the kernel of the projection.** -/
theorem projection_mul_eq_zero {k k' : R₁} (hk : D.arrow k = 0) (hk' : D.arrow k' = 0) :
    D.projection (k * k') = 0 := by
  rw [map_mul, D.projection_of_arrow_eq_zero hk, D.projection_of_arrow_eq_zero hk', inr_mul_inr]

/-- **`K · K ⊆ ker q ∩ K`.** -/
theorem mul_mem_ker :
    RingHom.ker D.arrow * RingHom.ker D.arrow ≤
      RingHom.ker D.projection ⊓ RingHom.ker D.arrow := by
  refine Ideal.mul_le.mpr fun k hk k' hk' => ⟨?_, ?_⟩
  · exact D.projection_mul_eq_zero hk hk'
  · exact Ideal.mul_mem_left _ k hk'

/-- Every element of `L` is the second component of the projection of an element of the kernel
of the arrow. -/
theorem exists_lift (l : L) : ∃ k, D.arrow k = 0 ∧ (D.projection k).snd = l := by
  obtain ⟨x, hx⟩ := D.projection_surjective (inr l)
  have h0 : D.baseProjection (D.arrow x) = 0 := by rw [D.baseProjection_arrow, hx, fst_inr]
  obtain ⟨g, hg, hgx⟩ := D.exists_ker_projection _ h0
  refine ⟨x - g, by rw [map_sub, hgx, sub_self], ?_⟩
  rw [map_sub, hg, sub_zero, hx, snd_inr]

/-- The product with an element of the kernel of the arrow depends only on the second component
of the projection. -/
theorem mul_eq_mul_of_snd_eq {k₁ k₂ k : R₁} (h₁ : D.arrow k₁ = 0) (h₂ : D.arrow k₂ = 0)
    (hk : D.arrow k = 0) (h : (D.projection k₁).snd = (D.projection k₂).snd) :
    k₁ * k = k₂ * k := by
  have hq : D.projection (k₁ - k₂) = 0 := by
    rw [map_sub, D.projection_of_arrow_eq_zero h₁, D.projection_of_arrow_eq_zero h₂, h, sub_self]
  have hρ : D.arrow (k₁ - k₂) = 0 := by rw [map_sub, h₁, h₂, sub_self]
  rw [← sub_eq_zero, ← sub_mul]
  exact D.mul_eq_zero _ _ hq hρ hk

/-- A chosen element of the kernel of the arrow with given second component. -/
noncomputable def lift (l : L) : R₁ := (D.exists_lift l).choose

/-- The chosen lift `D.lift l` lies in the kernel of the arrow. -/
theorem arrow_lift (l : L) : D.arrow (D.lift l) = 0 := (D.exists_lift l).choose_spec.1

/-- The second component of the projection of the chosen lift `D.lift l` is `l`. -/
theorem snd_lift (l : L) : (D.projection (D.lift l)).snd = l := (D.exists_lift l).choose_spec.2

variable [Module R₁ L] (hsmul : ∀ (r : R₁) (l : L), r • l = (D.projection r).fst • l)
include hsmul

/-- On the kernel of the arrow, the second component of the projection is `R₁`-linear:
`π (r k) = r • π k`. -/
theorem snd_projection_mul_of_arrow_eq_zero (r : R₁) {k : R₁} (hk : D.arrow k = 0) :
    (D.projection (r * k)).snd = r • (D.projection k).snd := by
  rw [map_mul, snd_mul, D.fst_projection_of_arrow_eq_zero hk, MulOpposite.op_zero, zero_smul,
    add_zero, hsmul]

/-- **The pairing induced by the product of the kernel of the arrow**: `μ(l, l') = k k'` for any
`k, k'` in the kernel of the arrow with second components `l, l'`. -/
noncomputable def pairing : L →ₗ[R₁] L →ₗ[R₁] R₁ :=
  LinearMap.mk₂ R₁ (fun l l' => D.lift l * D.lift l')
    (fun l₁ l₂ l' => by
      rw [← _root_.add_mul]
      refine D.mul_eq_mul_of_snd_eq (D.arrow_lift _) ?_ (D.arrow_lift _) ?_
      · rw [map_add, D.arrow_lift, D.arrow_lift, add_zero]
      · rw [map_add, snd_add, D.snd_lift, D.snd_lift, D.snd_lift])
    (fun r l l' => by
      rw [smul_eq_mul, ← _root_.mul_assoc]
      refine D.mul_eq_mul_of_snd_eq (D.arrow_lift _) ?_ (D.arrow_lift _) ?_
      · rw [map_mul, D.arrow_lift, MulZeroClass.mul_zero]
      · rw [D.snd_projection_mul_of_arrow_eq_zero hsmul r (D.arrow_lift l), D.snd_lift,
          D.snd_lift])
    (fun l l₁ l₂ => by
      rw [_root_.mul_comm, _root_.mul_comm (D.lift l), _root_.mul_comm (D.lift l),
        ← _root_.add_mul]
      refine D.mul_eq_mul_of_snd_eq (D.arrow_lift _) ?_ (D.arrow_lift _) ?_
      · rw [map_add, D.arrow_lift, D.arrow_lift, add_zero]
      · rw [map_add, snd_add, D.snd_lift, D.snd_lift, D.snd_lift])
    (fun r l l' => by
      rw [smul_eq_mul, _root_.mul_comm, _root_.mul_comm (D.lift l), ← _root_.mul_assoc]
      refine D.mul_eq_mul_of_snd_eq (D.arrow_lift _) ?_ (D.arrow_lift _) ?_
      · rw [map_mul, D.arrow_lift, MulZeroClass.mul_zero]
      · rw [D.snd_projection_mul_of_arrow_eq_zero hsmul r (D.arrow_lift l'), D.snd_lift,
          D.snd_lift])

/-- The pairing `μ(l, l')` is the product of the chosen lifts of `l` and `l'`. -/
theorem pairing_apply (l l' : L) : D.pairing hsmul l l' = D.lift l * D.lift l' := rfl

/-- **`μ(π k, π k') = k k'`** for `k, k'` in the kernel of the arrow. -/
theorem pairing_snd {k k' : R₁} (hk : D.arrow k = 0) (hk' : D.arrow k' = 0) :
    D.pairing hsmul (D.projection k).snd (D.projection k').snd = k * k' := by
  rw [pairing_apply, D.mul_eq_mul_of_snd_eq (D.arrow_lift _) hk (D.arrow_lift _) (D.snd_lift _),
    _root_.mul_comm k, _root_.mul_comm k,
    D.mul_eq_mul_of_snd_eq (D.arrow_lift _) hk' hk (D.snd_lift _)]

/-- The pairing `μ` is symmetric. -/
theorem pairing_comm (l l' : L) : D.pairing hsmul l l' = D.pairing hsmul l' l :=
  _root_.mul_comm _ _

/-- The values of the pairing `μ` lie in the kernel of the arrow. -/
theorem arrow_pairing (l l' : L) : D.arrow (D.pairing hsmul l l') = 0 := by
  rw [pairing_apply, map_mul, D.arrow_lift, MulZeroClass.zero_mul]

/-- The values of the pairing `μ` lie in the kernel of the projection. -/
theorem projection_pairing (l l' : L) : D.projection (D.pairing hsmul l l') = 0 :=
  D.projection_mul_eq_zero (D.arrow_lift l) (D.arrow_lift l')

/-- **The second component of the projection is a derivation** `π : R₁ → L`. -/
def derivation : Derivation ℤ R₁ L :=
  Derivation.mk'
    { toFun := fun x => (D.projection x).snd
      map_add' := fun x y => by rw [map_add, snd_add]
      map_smul' := fun n x => by
        simp only [eq_intCast, Int.cast_id, map_zsmul]
        rfl }
    (fun x y => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, map_mul, snd_mul, hsmul, op_smul_eq_smul,
        _root_.add_comm])

/-- The derivation `π` sends `x` to the second component of its projection. -/
theorem derivation_apply (x : R₁) : D.derivation hsmul x = (D.projection x).snd := rfl

/-- **The multiplication correction of the arrow**: `π` the second component of `q`, `μ` the
pairing induced by the product of the kernel of the arrow. -/
noncomputable def correction : MultiplicationCorrection R₁ L where
  derivation := D.derivation hsmul
  pairing := D.pairing hsmul
  pairing_comm := D.pairing_comm hsmul
  derivation_pairing a b := by rw [derivation_apply, D.projection_pairing, snd_zero]

/-- The arrow, out of the corrected ring. -/
noncomputable def correctedArrow : CorrectedRing (D.correction hsmul) →+* R₀ :=
  CorrectedRing.ringHomFrom _ D.arrow (D.arrow_pairing hsmul)

/-- The projection onto `O ⊕ L`, out of the corrected ring. -/
noncomputable def correctedProjection :
    CorrectedRing (D.correction hsmul) →+* TrivSqZeroExt O L :=
  CorrectedRing.ringHomFrom _ D.projection (D.projection_pairing hsmul)

/-- The arrow out of the corrected ring is surjective. -/
theorem correctedArrow_surjective : Function.Surjective (D.correctedArrow hsmul) :=
  Function.Surjective.of_comp (g := CorrectedRing.toCorrected _) D.arrow_surjective

/-- The projection out of the corrected ring is surjective. -/
theorem correctedProjection_surjective : Function.Surjective (D.correctedProjection hsmul) :=
  Function.Surjective.of_comp (g := CorrectedRing.toCorrected _) D.projection_surjective

/-- The kernel of the corrected arrow; as a set it is the kernel of the arrow. -/
noncomputable def correctedKernel : Ideal (CorrectedRing (D.correction hsmul)) :=
  RingHom.ker (D.correctedArrow hsmul)

/-- An element of the corrected ring lies in the corrected kernel exactly when its underlying
element of `R₁` lies in the kernel of the arrow. -/
theorem mem_correctedKernel (x : CorrectedRing (D.correction hsmul)) :
    x ∈ D.correctedKernel hsmul ↔ D.arrow (CorrectedRing.ofCorrected _ x) = 0 :=
  RingHom.mem_ker

/-- **After the correction, any two elements of the kernel of the arrow multiply to zero.** -/
theorem correctedKernel_mul_eq_zero {x y : CorrectedRing (D.correction hsmul)}
    (hx : x ∈ D.correctedKernel hsmul) (hy : y ∈ D.correctedKernel hsmul) : x * y = 0 := by
  rw [mem_correctedKernel] at hx hy
  apply CorrectedRing.ofCorrected_injective (D.correction hsmul)
  rw [CorrectedRing.ofCorrected_mul, CorrectedRing.ofCorrected_zero]
  change _ - D.pairing hsmul (D.projection _).snd (D.projection _).snd = 0
  rw [D.pairing_snd hsmul hx hy, sub_self]

/-- **After the correction, the kernel of the arrow has square zero.** -/
theorem correctedKernel_sq_eq_bot : D.correctedKernel hsmul ^ 2 = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [pow_two]
  exact Ideal.mul_le.mpr fun x hx y hy =>
    (Submodule.mem_bot _).mpr (D.correctedKernel_mul_eq_zero hsmul hx hy)

/-- **The corrected kernel is an `R₀`-module**, through `R₁ / K ≅ R₀`: `ρ r • k = r ⋆ k`. -/
@[instance_reducible]
noncomputable def correctedKernelModule : Module R₀ (D.correctedKernel hsmul) :=
  RingHom.moduleOfKerSMul (D.correctedArrow_surjective hsmul) (D.correctedKernel hsmul)
    fun _ hj x => Subtype.ext (D.correctedKernel_mul_eq_zero hsmul hj x.2)

/-- The `R₀`-module structure on the corrected kernel is the corrected action of `R₁` through
the arrow: `ρ r • k = r ⋆ k`. -/
theorem correctedKernelModule_smul (r : CorrectedRing (D.correction hsmul))
    (x : D.correctedKernel hsmul) :
    letI := D.correctedKernelModule hsmul
    D.correctedArrow hsmul r • x = r • x :=
  RingHom.moduleOfKerSMul_smul _ _ _ r x

end ArrowKernelData

end Deformation.PairDeformation
