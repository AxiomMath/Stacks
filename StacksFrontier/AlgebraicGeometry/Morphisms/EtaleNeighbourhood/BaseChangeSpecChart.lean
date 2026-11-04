module

public import Mathlib.AlgebraicGeometry.Stalk
public import StacksFrontier.AlgebraicGeometry.Pushout.SectionsTensorProduct

/-!
# The affine chart of a base change along the spectrum of a local ring

Let `g : Y ⟶ T` be a morphism of schemes and let `b : Spec Λ ⟶ T` have as source the spectrum of
a **local** ring. Write `t` for the image of the closed point of `Spec Λ`. Because `Λ` is local,
every open of `T` containing `t` pulls back to all of `Spec Λ`
(`AlgebraicGeometry.Scheme.preimage_eq_top_of_closedPoint_mem`), so a chart of the fibre product
`Y ×_T Spec Λ` needs no second factor: for an affine open `W_T ∋ t` of `T` and an affine open
`V_Y` of `Y` over it, the open `pr₁ ⁻¹ᵁ V_Y` is already affine, and its sections are
`Λ ⊗_{Γ(T, W_T)} Γ(Y, V_Y)`.

This is the affine chart the proof of Stacks Tag 0CAW works in. There `Λ = 𝒪^∧_{S, s}`, the
morphism `b` is the one `σ : 𝒪_{T, t} → 𝒪^∧_{S, s}` determines, `C = Γ(T, W_T)`,
`B = Γ(Y, V_Y)`, and the chart ring is the `B ⊗_{C, σ} R^∧` over which the source extends an
étale algebra: "`σ` and `φ` correspond to ring maps `σ : C → R^∧` and
`φ : A → (B ⊗_{C, σ} R^∧)^∧`". The identification matters because the étale algebra produced by
the earlier steps of that proof lives over the ring of sections of a chart of `Y_σ`, while the
filtered-colimit presentation it is then descended along
(`Stacks.Smoothing.exists_colimitPresentation_tensorProduct_of_indSmooth` feeding
`Algebra.Etale.exists_etale_stage_of_isColimit_of_smallCategory`) is a statement about
`B ⊗_C Λ`, with `Λ` a ring given in advance rather than a ring of sections.

What locality of `Λ` is used for is only the inequality `⊤ ≤ b ⁻¹ᵁ W_T`, so both statements are
proved for an arbitrary ring `Λ` with that inequality as a hypothesis and then specialised. The
general form is what the last step of the proof of Stacks Tag 0CAW needs on its `W` side: there
the second factor is `V = Spec D` for `D` the étale `R`-algebra that the final application of Tag
0CAU produces, and `D` is **not** local, so the closed-point form does not apply; what does hold
is that `τ : Spec D ⟶ T` factors through the chart `W_T` of `T` by construction, which is the
hypothesis `⊤ ≤ τ ⁻¹ᵁ W_T`.

## Main results

* `AlgebraicGeometry.isAffineOpen_preimage_pullback_fst_of_preimage_eq_top`: for an arbitrary `Λ`
  with `b ⁻¹ᵁ W_T = ⊤`, the open `pr₁ ⁻¹ᵁ V_Y` of `Y ×_T Spec Λ` is affine.
* `AlgebraicGeometry.exists_ringEquiv_tensorProduct_sections_pullback_fst_of_preimage_eq_top`:
  under the same hypothesis, its ring of sections is `Λ ⊗_{Γ(T, W_T)} Γ(Y, V_Y)`.
* `AlgebraicGeometry.isAffineOpen_preimage_pullback_fst_of_closedPoint_mem`: the open
  `pr₁ ⁻¹ᵁ V_Y` of `Y ×_T Spec Λ` is affine.
* `AlgebraicGeometry.exists_ringEquiv_tensorProduct_sections_pullback_fst`: its ring of sections
  is `Λ ⊗_{Γ(T, W_T)} Γ(Y, V_Y)`, by an isomorphism carrying `l ⊗ 1` to the section pulled back
  from `Spec Λ` and `1 ⊗ s` to the section pulled back from `V_Y`.

## Implementation notes

Neither statement has any content of its own: the general chart of a cartesian square is
`AlgebraicGeometry.isAffineOpen_of_isPullback` and
`AlgebraicGeometry.isPushout_appLE_of_isPullback_inter`, and the identification of its sections
with an abstract tensor product is `AlgebraicGeometry.sectionsTensorEquiv`. What is done here is
the instantiation that a base change along `Spec` of a local ring admits and a general one does
not, namely at the chart `⊤` of `Spec Λ`: the hypothesis `U_T ≤ b ⁻¹ᵁ W_T` of those lemmas, a
real constraint in general, is automatic, and the chart `pr₁ ⁻¹ᵁ V_Y ⊓ pr₂ ⁻¹ᵁ ⊤` of the fibre
product collapses to `pr₁ ⁻¹ᵁ V_Y`. The second factor of the tensor product is then `Λ` itself
rather than `Γ(Spec Λ, ⊤)`, through `AlgebraicGeometry.Scheme.ΓSpecIso`, which is what makes the
statement usable by a caller holding `Λ` with its own algebra structure.

The algebra structures on `Λ` and on `Γ(Y, V_Y)` over `Γ(T, W_T)` are taken as parameters,
constrained to be the two restriction maps on sections, rather than installed in the statement by
`RingHom.toAlgebra`: a caller holds `Λ` with an algebra structure of its own, and an opaque
instance also keeps the elaborated statement small, which matters because the tensor product
appears in it many times. The order of the factors is `Λ ⊗ Γ(Y, V_Y)`, the order
`AlgebraicGeometry.sectionsTensorEquiv` produces, with the base-change factor on the left.

## References

* [Stacks Project, Tag 0CAW](https://stacks.math.columbia.edu/tag/0CAW), whose proof's affine
  reduction this is
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct IsLocalRing

universe u

namespace AlgebraicGeometry

variable {T Y : Scheme.{u}} (g : Y ⟶ T) {Λ : CommRingCat.{u}} (b : Spec Λ ⟶ T)

/-- The chart of `Y ×_T Spec Λ` cut out by an affine open `V_Y` of `Y` is cut out by `V_Y` alone:
the second factor contributes `⊤`. -/
theorem preimage_pullback_fst_eq_inf_preimage_pullback_snd {VY : Y.Opens} :
    pullback.fst g b ⁻¹ᵁ VY =
      pullback.fst g b ⁻¹ᵁ VY ⊓ pullback.snd g b ⁻¹ᵁ (⊤ : (Spec Λ).Opens) := by
  simp

/-- **An affine open of `Y` lying over an affine open `W_T` of `T` through which `b` factors pulls
back to an affine open of `Y ×_T Spec Λ`.** Here `Λ` is any commutative ring, `W_T` is an affine
open of `T` with `b ⁻¹ᵁ W_T = ⊤`, and `V_Y` is an affine open of `Y` contained in `g ⁻¹ᵁ W_T`.

This is not an instance of `AlgebraicGeometry.IsAffineOpen.preimage`, which would need
`b : Spec Λ ⟶ T` to be an affine morphism; what makes it true is that `b` meets no open of `T`
avoiding `W_T`, so the chart `pr₁ ⁻¹ᵁ V_Y` is the fibre product of the affine schemes `V_Y` and
`Spec Λ` over `W_T`. -/
theorem isAffineOpen_preimage_pullback_fst_of_preimage_eq_top
    {WT : T.Opens} (hWT : IsAffineOpen WT) (hbT : (⊤ : (Spec Λ).Opens) ≤ b ⁻¹ᵁ WT)
    {VY : Y.Opens} (hVY : IsAffineOpen VY) (hVYW : VY ≤ g ⁻¹ᵁ WT) :
    IsAffineOpen (pullback.fst g b ⁻¹ᵁ VY) :=
  isAffineOpen_of_isPullback (IsPullback.of_hasPullback g b) hWT hVY
    (isAffineOpen_top (Spec Λ)) hVYW hbT
    (preimage_pullback_fst_eq_inf_preimage_pullback_snd g b)

/-- **The sections over that chart are `Λ ⊗_{Γ(T, W_T)} Γ(Y, V_Y)`.** The two algebra structures
over `Γ(T, W_T)` are required to be the restriction maps on sections of `b` and of `g`, and the
isomorphism carries `l ⊗ 1` to the section pulled back from `Spec Λ` and `1 ⊗ s` to the section
pulled back from `V_Y`. Here `Λ` is any commutative ring and `b ⁻¹ᵁ W_T = ⊤`.

In the notation of the proof of Stacks Tag 0CAW this identifies the ring of sections of the chart
of `Y ×_{T, τ} V` at `(y, v)`, for `V = Spec D` and `τ` the morphism a ring map `C → D` and the
chart `W_T` of `T` determine, with `D ⊗_C B`. -/
theorem exists_ringEquiv_tensorProduct_sections_pullback_fst_of_preimage_eq_top
    {WT : T.Opens} (hWT : IsAffineOpen WT) (hbT : (⊤ : (Spec Λ).Opens) ≤ b ⁻¹ᵁ WT)
    {VY : Y.Opens} (hVY : IsAffineOpen VY) (hVYW : VY ≤ g ⁻¹ᵁ WT)
    [Algebra Γ(T, WT) Λ] [Algebra Γ(T, WT) Γ(Y, VY)]
    (hΛ : ∀ t : Γ(T, WT), algebraMap Γ(T, WT) Λ t =
      (Scheme.ΓSpecIso Λ).hom.hom ((b.appLE WT ⊤ hbT).hom t))
    (hB : ∀ t : Γ(T, WT),
      algebraMap Γ(T, WT) Γ(Y, VY) t = (g.appLE WT VY hVYW).hom t) :
    ∃ χ : Λ ⊗[Γ(T, WT)] Γ(Y, VY) ≃+* Γ(pullback g b, pullback.fst g b ⁻¹ᵁ VY),
      (∀ l : Λ, χ (l ⊗ₜ 1) =
          ((pullback.snd g b).appLE ⊤ (pullback.fst g b ⁻¹ᵁ VY) le_top).hom
            ((Scheme.ΓSpecIso Λ).inv.hom l)) ∧
        (∀ s : Γ(Y, VY), χ (1 ⊗ₜ s) =
          ((pullback.fst g b).appLE VY (pullback.fst g b ⁻¹ᵁ VY) le_rfl).hom s) := by
  have hUY : pullback.fst g b ⁻¹ᵁ VY =
      pullback.fst g b ⁻¹ᵁ VY ⊓ pullback.snd g b ⁻¹ᵁ (⊤ : (Spec Λ).Opens) :=
    preimage_pullback_fst_eq_inf_preimage_pullback_snd g b
  have hD : ∀ t : Γ(T, WT),
      ((Scheme.ΓSpecIso Λ).commRingCatIsoToRingEquiv) ((b.appLE WT ⊤ hbT).hom t) =
        algebraMap Γ(T, WT) Λ ((RingEquiv.refl Γ(T, WT)) t) := fun t => (hΛ t).symm
  have hB' : ∀ t : Γ(T, WT),
      ((RingEquiv.refl Γ(Y, VY))) ((g.appLE WT VY hVYW).hom t) =
        algebraMap Γ(T, WT) Γ(Y, VY) ((RingEquiv.refl Γ(T, WT)) t) := fun t => (hB t).symm
  refine ⟨(sectionsTensorEquiv (IsPullback.of_hasPullback g b) hbT hVYW hUY hWT
      (isAffineOpen_top (Spec Λ)) hVY (RingEquiv.refl Γ(T, WT))
      (Scheme.ΓSpecIso Λ).commRingCatIsoToRingEquiv (RingEquiv.refl Γ(Y, VY)) hD hB').symm,
    fun l => ?_, fun s => ?_⟩
  · have hcoe : ((Scheme.ΓSpecIso Λ).commRingCatIsoToRingEquiv)
        ((Scheme.ΓSpecIso Λ).inv.hom l) = l :=
      congr($((Scheme.ΓSpecIso Λ).inv_hom_id).hom l)
    refine (RingEquiv.symm_apply_eq _).mpr (Eq.trans ?_ (sectionsTensorEquiv_appLE_right
      (IsPullback.of_hasPullback g b) hbT hVYW hUY hWT (isAffineOpen_top (Spec Λ)) hVY
      (RingEquiv.refl Γ(T, WT)) (Scheme.ΓSpecIso Λ).commRingCatIsoToRingEquiv
      (RingEquiv.refl Γ(Y, VY)) hD hB' ((Scheme.ΓSpecIso Λ).inv.hom l)).symm)
    rw [hcoe]
    rfl
  · exact (RingEquiv.symm_apply_eq _).mpr (sectionsTensorEquiv_appLE_left
      (IsPullback.of_hasPullback g b) hbT hVYW hUY hWT (isAffineOpen_top (Spec Λ)) hVY
      (RingEquiv.refl Γ(T, WT)) (Scheme.ΓSpecIso Λ).commRingCatIsoToRingEquiv
      (RingEquiv.refl Γ(Y, VY)) hD hB' s).symm

section IsLocalRing

variable [IsLocalRing Λ]

/-- **An affine open of `Y` lying over an affine open of `T` around the image of the closed point
pulls back to an affine open of `Y ×_T Spec Λ`.** Here `Λ` is a local ring, `W_T` is an affine
open of `T` containing the image of the closed point of `Spec Λ`, and `V_Y` is an affine open of
`Y` contained in `g ⁻¹ᵁ W_T`.

This is not an instance of `AlgebraicGeometry.IsAffineOpen.preimage`, which would need
`b : Spec Λ ⟶ T` to be an affine morphism; what makes it true is that `b` meets no open of `T`
avoiding `t`, since `Λ` is local, so the chart `pr₁ ⁻¹ᵁ V_Y` is the fibre product of the affine
schemes `V_Y` and `Spec Λ` over `W_T`. This is the case of
`AlgebraicGeometry.isAffineOpen_preimage_pullback_fst_of_preimage_eq_top` in which the hypothesis
`b ⁻¹ᵁ W_T = ⊤` is supplied by locality of `Λ`. -/
theorem isAffineOpen_preimage_pullback_fst_of_closedPoint_mem
    {WT : T.Opens} (hWT : IsAffineOpen WT) (ht : b (closedPoint Λ) ∈ WT)
    {VY : Y.Opens} (hVY : IsAffineOpen VY) (hVYW : VY ≤ g ⁻¹ᵁ WT) :
    IsAffineOpen (pullback.fst g b ⁻¹ᵁ VY) :=
  isAffineOpen_preimage_pullback_fst_of_preimage_eq_top g b hWT
    (Scheme.preimage_eq_top_of_closedPoint_mem b ht).ge hVY hVYW

/-- **The sections over that chart are `Λ ⊗_{Γ(T, W_T)} Γ(Y, V_Y)`.** The two algebra structures
over `Γ(T, W_T)` are required to be the restriction maps on sections of `b` and of `g`, and the
isomorphism carries `l ⊗ 1` to the section pulled back from `Spec Λ` and `1 ⊗ s` to the section
pulled back from `V_Y`.

In the notation of the proof of Stacks Tag 0CAW this identifies the ring of sections of the chart
of `Y_σ = Y ×_{T, σ} \operatorname{Spec}(R^\wedge)` at `y_σ` with `B ⊗_{C, σ} R^\wedge`. This is
the case of
`AlgebraicGeometry.exists_ringEquiv_tensorProduct_sections_pullback_fst_of_preimage_eq_top` in
which the hypothesis `b ⁻¹ᵁ W_T = ⊤` is supplied by locality of `Λ`. -/
theorem exists_ringEquiv_tensorProduct_sections_pullback_fst
    {WT : T.Opens} (hWT : IsAffineOpen WT) (ht : b (closedPoint Λ) ∈ WT)
    {VY : Y.Opens} (hVY : IsAffineOpen VY) (hVYW : VY ≤ g ⁻¹ᵁ WT)
    [Algebra Γ(T, WT) Λ] [Algebra Γ(T, WT) Γ(Y, VY)]
    (hΛ : ∀ t : Γ(T, WT), algebraMap Γ(T, WT) Λ t =
      (Scheme.ΓSpecIso Λ).hom.hom
        ((b.appLE WT ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem b ht).ge).hom t))
    (hB : ∀ t : Γ(T, WT),
      algebraMap Γ(T, WT) Γ(Y, VY) t = (g.appLE WT VY hVYW).hom t) :
    ∃ χ : Λ ⊗[Γ(T, WT)] Γ(Y, VY) ≃+* Γ(pullback g b, pullback.fst g b ⁻¹ᵁ VY),
      (∀ l : Λ, χ (l ⊗ₜ 1) =
          ((pullback.snd g b).appLE ⊤ (pullback.fst g b ⁻¹ᵁ VY) le_top).hom
            ((Scheme.ΓSpecIso Λ).inv.hom l)) ∧
        (∀ s : Γ(Y, VY), χ (1 ⊗ₜ s) =
          ((pullback.fst g b).appLE VY (pullback.fst g b ⁻¹ᵁ VY) le_rfl).hom s) :=
  exists_ringEquiv_tensorProduct_sections_pullback_fst_of_preimage_eq_top g b hWT
    (Scheme.preimage_eq_top_of_closedPoint_mem b ht).ge hVY hVYW hΛ hB

end IsLocalRing

end AlgebraicGeometry

end
