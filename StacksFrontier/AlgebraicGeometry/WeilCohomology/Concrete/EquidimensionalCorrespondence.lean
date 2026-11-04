module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.DimensionDecompositionBasePoint

/-!
# Correspondences between equidimensional schemes

Let `k` be a field and let `X`, `Y` be smooth separated schemes over `k`. The space of
correspondences of Section 0FFZ is the direct sum over the parts of `X` and `Y` of constant
dimension,

`Corrʳ(X, Y) = ⊕_d ⊕_e CH_{e-r}(X_d × Y_e) ⊗ ℚ`.

When `X` has constant relative dimension `d` and `Y` constant relative dimension `e`, only the
summand `(d, e)` survives and its parts are `X` and `Y` themselves, so

`Corrʳ(X, Y) = CH_{e-r}(X × Y) ⊗ ℚ = CH^{d+r}(X × Y) ⊗ ℚ`,

which is how the source computes with correspondences between equidimensional schemes, for
instance in Example 0FG6 for `X = Y = P¹_k`.

## Main definitions

* `Stacks.WeilCohomology.corrEquivCorrespondence`: the `ℚ`-linear isomorphism
  `Corrʳ(X, Y) ≃ CH_{e-r}(X × Y) ⊗ ℚ` for `X`, `Y` of constant relative dimensions `d`, `e`.

## Main results

* `Stacks.WeilCohomology.eq_of_mem_dimPart`, `Stacks.WeilCohomology.dimPart_self_eq_top`,
  `Stacks.WeilCohomology.isEmpty_dimPart_of_ne` and `Stacks.WeilCohomology.isIso_dimPart_self_ι`:
  for a smooth morphism of constant relative dimension `d` the part of dimension `d` is
  everything and the other parts are empty.
* `Stacks.WeilCohomology.corrEquivCorrespondence_comp`: the isomorphisms carry the composition of
  Section 0FFZ to the composition `c' ∘ c = pr₁₃,*(pr₁₂^* c · pr₂₃^* c')` on the products, for an
  iso-invariant family of diagonal classes.
* `Stacks.WeilCohomology.corrEquivCorrespondence_lof_lof` and
  `Stacks.WeilCohomology.corrEquivCorrespondence_symm_apply`: the isomorphism is the transport
  along the inclusions of the parts on the surviving summand.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Stacks.Chow

universe u

namespace Stacks.WeilCohomology

/-! ### The parts of a smooth morphism of constant relative dimension -/

section Parts

variable {X S : Scheme.{u}} (sX : X ⟶ S) [Smooth sX] {d : ℕ}

/-- A point of a part `X_e` of a smooth morphism of constant relative dimension `d` forces
`e = d`: the part is then of relative dimension both `e` and `d`, with a nonempty fibre. -/
theorem eq_of_mem_dimPart (h : RelativeDimension sX d) {e : ℕ} {x : X} (hx : x ∈ dimPart sX e) :
    e = d := by
  let y : (dimPart sX e).toScheme := ⟨x, hx⟩
  have hd : RelativeDimension (partBase sX e) d :=
    RelativeDimension.comp_isOpenImmersion (dimPart sX e).ι sX h
  have hy := ((relativeDimension_partBase sX e) _ ⟨(partBase sX e).asFiber y⟩).2.symm.trans
    (hd _ ⟨(partBase sX e).asFiber y⟩).2
  exact_mod_cast hy

/-- For a smooth morphism of constant relative dimension `d`, the part of dimension `d` is
everything. -/
theorem dimPart_self_eq_top (h : RelativeDimension sX d) : dimPart sX d = ⊤ := by
  ext x
  simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
  obtain ⟨e, he⟩ := (isClopenDecomposition_dimPart sX).exists_mem x
  rwa [eq_of_mem_dimPart sX h he] at he

/-- For a smooth morphism of constant relative dimension `d`, the parts of other dimensions are
empty schemes. -/
theorem isEmpty_dimPart_of_ne (h : RelativeDimension sX d) {e : ℕ} (he : e ≠ d) :
    IsEmpty (dimPart sX e).toScheme :=
  ⟨fun y ↦ he (eq_of_mem_dimPart sX h y.2)⟩

/-- For a smooth morphism of constant relative dimension `d`, the inclusion of the part of
dimension `d` is an isomorphism. -/
theorem isIso_dimPart_self_ι (h : RelativeDimension sX d) : IsIso (dimPart sX d).ι := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  rw [Scheme.Opens.opensRange_ι, dimPart_self_eq_top sX h]

end Parts

/-! ### Correspondences between equidimensional schemes -/

section Equidimensional

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sY : Y ⟶ (fieldChowSituation k).S)
  [Smooth sX] [IsSeparated sX] [Smooth sY] [IsSeparated sY] {d e : ℕ}

/-- The summands of `Corrʳ(X, Y)` other than the one of index `(d, e)` vanish for `X` of constant
relative dimension `d`: their source part is empty. -/
theorem subsingleton_corr_summand_of_ne (hX : RelativeDimension sX d) (r : ℤ) {d' : ℕ}
    (hd' : d' ≠ d) :
    Subsingleton (DirectSum ℕ fun e' ↦
      Correspondence (fieldChowSituation k) (partBase sX d') (partBase sY e') e' r) := by
  have := isEmpty_dimPart_of_ne sX hX hd'
  have : ∀ e' : ℕ, Subsingleton
      (Correspondence (fieldChowSituation k) (partBase sX d') (partBase sY e') e' r) :=
    fun e' ↦ subsingleton_correspondence_of_isEmpty_left _ _ _ _ _
  infer_instance

/-- **Correspondences between equidimensional schemes.** For `X` of constant relative dimension
`d` and `Y` of constant relative dimension `e` over `k`, the correspondences of Section 0FFZ are
the rational Chow group of the product in dimension `e - r`,
`Corrʳ(X, Y) = CH_{e-r}(X × Y) ⊗ ℚ = CH^{d+r}(X × Y) ⊗ ℚ`: only the summand `(d, e)` of
`⊕_{d', e'} CH_{e'-r}(X_{d'} × Y_{e'}) ⊗ ℚ` is nonzero, and its parts are `X` and `Y`
themselves. -/
def corrEquivCorrespondence (hX : RelativeDimension sX d) (hY : RelativeDimension sY e)
    (r : ℤ) : Corr k sX sY r ≃ₗ[ℚ] Correspondence (fieldChowSituation k) sX sY e r :=
  haveI := isIso_dimPart_self_ι sX hX
  haveI := isIso_dimPart_self_ι sY hY
  (directSumEquivSummand d fun _ hd' ↦ subsingleton_corr_summand_of_ne k sX sY hX r hd') ≪≫ₗ
    (directSumEquivSummand e fun e' he' ↦ by
      haveI := isEmpty_dimPart_of_ne sY hY he'
      exact subsingleton_correspondence_of_isEmpty_right _ _ _ _ _) ≪≫ₗ
    correspondenceEquivOfIso (fieldChowSituation k) sX sY (partBase sX d) (partBase sY e)
      (dimPart sX d).ι (dimPart sY e).ι rfl rfl e r

/-- On the surviving summand the isomorphism `Corrʳ(X, Y) ≃ CH_{e-r}(X × Y) ⊗ ℚ` is the transport
along the inclusions of the parts. -/
theorem corrEquivCorrespondence_lof_lof (hX : RelativeDimension sX d)
    (hY : RelativeDimension sY e) (r : ℤ)
    (c : Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e) e r) :
    haveI := isIso_dimPart_self_ι sX hX
    haveI := isIso_dimPart_self_ι sY hY
    corrEquivCorrespondence k sX sY hX hY r
        (DirectSum.lof ℚ ℕ (fun d' ↦ DirectSum ℕ fun e' ↦
            Correspondence (fieldChowSituation k) (partBase sX d') (partBase sY e') e' r) d
          (DirectSum.lof ℚ ℕ (fun e' ↦
            Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e') e' r) e c)) =
      correspondenceEquivOfIso (fieldChowSituation k) sX sY (partBase sX d) (partBase sY e)
        (dimPart sX d).ι (dimPart sY e).ι rfl rfl e r c := by
  simp [corrEquivCorrespondence]

/-- The inverse of `Corrʳ(X, Y) ≃ CH_{e-r}(X × Y) ⊗ ℚ` puts a class, transported back to the
parts, in the summand `(d, e)`. -/
theorem corrEquivCorrespondence_symm_apply (hX : RelativeDimension sX d)
    (hY : RelativeDimension sY e) (r : ℤ) (c : Correspondence (fieldChowSituation k) sX sY e r) :
    haveI := isIso_dimPart_self_ι sX hX
    haveI := isIso_dimPart_self_ι sY hY
    (corrEquivCorrespondence k sX sY hX hY r).symm c =
      DirectSum.lof ℚ ℕ (fun d' ↦ DirectSum ℕ fun e' ↦
          Correspondence (fieldChowSituation k) (partBase sX d') (partBase sY e') e' r) d
        (DirectSum.lof ℚ ℕ (fun e' ↦
          Correspondence (fieldChowSituation k) (partBase sX d) (partBase sY e') e' r) e
          ((correspondenceEquivOfIso (fieldChowSituation k) sX sY (partBase sX d)
            (partBase sY e) (dimPart sX d).ι (dimPart sY e).ι rfl rfl e r).symm c)) :=
  rfl

/-- **Composition of correspondences between equidimensional schemes.** For `X`, `Y`, `Z` of
constant relative dimensions `d`, `e`, `f` over `k` and an iso-invariant family of diagonal
classes (for instance the canonical one, `Stacks.WeilCohomology.canonicalDiagonalClassFamily`, by
`Stacks.WeilCohomology.canonicalDiagonalClassFamily_isoInvariant`), the isomorphisms
`Corrʳ(X, Y) ≃ CH_{e-r}(X × Y) ⊗ ℚ` carry the composition of Section 0FFZ on the direct sums to
the composition `c' ∘ c = pr₁₃,*(pr₁₂^* c · pr₂₃^* c')` on the products themselves. -/
theorem corrEquivCorrespondence_comp (Δ : DiagonalClassFamily k) (hΔ : Δ.IsoInvariant)
    {Z : Scheme.{u}} (sZ : Z ⟶ (fieldChowSituation k).S) [Smooth sZ] [IsSeparated sZ]
    [IsProper sY] {f : ℕ} (hX : RelativeDimension sX d) (hY : RelativeDimension sY e)
    (hZ : RelativeDimension sZ f) (r s : ℤ) (a : Corr k sX sY r) (b : Corr k sY sZ s) :
    corrEquivCorrespondence k sX sZ hX hZ (r + s) (comp k sX sY sZ Δ r s a b) =
      composition k sX sY sZ Δ hX hY hZ r s (corrEquivCorrespondence k sX sY hX hY r a)
        (corrEquivCorrespondence k sY sZ hY hZ s b) := by
  have := isIso_dimPart_self_ι sX hX
  have := isIso_dimPart_self_ι sY hY
  have := isIso_dimPart_self_ι sZ hZ
  obtain ⟨a, rfl⟩ := (corrEquivCorrespondence k sX sY hX hY r).symm.surjective a
  obtain ⟨b, rfl⟩ := (corrEquivCorrespondence k sY sZ hY hZ s).symm.surjective b
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    corrEquivCorrespondence_symm_apply, corrEquivCorrespondence_symm_apply,
    comp_lof_lof_of_apply_eq_lof k Δ sX sY sZ r s d e f _ _ _ (by
      rw [DirectSum.lof_eq_of, DirectSum.of_eq_same]),
    corrEquivCorrespondence_lof_lof,
    correspondenceEquivOfIso_composition k Δ sX sY sZ (partBase sX d) (partBase sY e)
      (partBase sZ f) (dimPart sX d).ι (dimPart sY e).ι (dimPart sZ f).ι rfl rfl rfl hΔ hX hY hZ,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

end Equidimensional

end Stacks.WeilCohomology

end
