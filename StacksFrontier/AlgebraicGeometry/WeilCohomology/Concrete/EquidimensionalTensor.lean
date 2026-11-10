module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.EquidimensionalCorrespondence
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Tensor

/-!
# The tensor product of correspondences between equidimensional schemes

Let `k` be a field and let `X, X', Y, Y'` be smooth proper schemes over `k` of constant
dimensions `d, d', e, e'`. Then `Corrʳ(X, Y) = CH_{e-r}(X × Y) ⊗ ℚ`
(`Stacks.WeilCohomology.corrEquivCorrespondence`), and this file shows that under these
identifications the tensor product of correspondences of Section 0FFZ,
`c ⊗ c' = pr₁₃^* c · pr₂₄^* c'`, defined block by block on the parts of constant dimension, is the
tensor product `Stacks.WeilCohomology.tensorBlock` on the products themselves. It is the analogue
for the tensor product of `Stacks.WeilCohomology.corrEquivCorrespondence_comp`.

The input is that the tensor product is natural with respect to isomorphisms of the four factors,
for an iso-invariant family of diagonal classes: the fourfold product is transported along the
product of the four isomorphisms, which carries `pr₁₃` and `pr₂₄` to `pr₁₃` and `pr₂₄`, and the
intersection product along it by iso-invariance.

## Main results

* `Stacks.WeilCohomology.chowPushforwardOfIso_tensorInt` and
  `Stacks.WeilCohomology.correspondenceEquivOfIso_tensorBlock`: the tensor product is natural with
  respect to isomorphisms over `k`.
* `Stacks.WeilCohomology.corrEquivCorrespondence_tensor`: the identifications
  `Corrʳ(X, Y) ≃ CH_{e-r}(X × Y) ⊗ ℚ` carry `tensor` to `tensorBlock`.

## References

* [Stacks Project, Section 0FFZ](https://stacks.math.columbia.edu/tag/0FFZ)
* [Stacks Project, Tag 0FG7](https://stacks.math.columbia.edu/tag/0FG7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

variable (k : Type u) [Field k] (Δ : DiagonalClassFamily k)

/-! ### Naturality with respect to isomorphisms -/

section Naturality

variable {A A' B B' A₀ A₀' B₀ B₀' : Scheme.{u}}
  (sA : A ⟶ (fieldChowSituation k).S) (sA' : A' ⟶ (fieldChowSituation k).S)
  (sB : B ⟶ (fieldChowSituation k).S) (sB' : B' ⟶ (fieldChowSituation k).S)
  (sA₀ : A₀ ⟶ (fieldChowSituation k).S) (sA₀' : A₀' ⟶ (fieldChowSituation k).S)
  (sB₀ : B₀ ⟶ (fieldChowSituation k).S) (sB₀' : B₀' ⟶ (fieldChowSituation k).S)
  [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] [LocallyOfFiniteType sB]
  [LocallyOfFiniteType sB'] [LocallyOfFiniteType sA₀] [LocallyOfFiniteType sA₀']
  [LocallyOfFiniteType sB₀] [LocallyOfFiniteType sB₀']
  [Smooth sA] [Smooth sA'] [Smooth sB] [Smooth sB'] [Smooth sA₀] [Smooth sA₀'] [Smooth sB₀]
  [Smooth sB₀']
  (φA : A₀ ⟶ A) [IsIso φA] (φA' : A₀' ⟶ A') [IsIso φA'] (φB : B₀ ⟶ B) [IsIso φB]
  (φB' : B₀' ⟶ B') [IsIso φB'] (hφA : φA ≫ sA = sA₀) (hφA' : φA' ≫ sA' = sA₀')
  (hφB : φB ≫ sB = sB₀) (hφB' : φB' ≫ sB' = sB₀')

/-- The product of the four isomorphisms, `(A₀ × A₀') × (B₀ × B₀') ⟶ (A × A') × (B × B')`. -/
abbrev tensorProductHom :
    tensorProduct sA₀ sA₀' sB₀ sB₀' ⟶ tensorProduct sA sA' sB sB' :=
  prodHom (prodBase sA sA') (prodBase sB sB') (prodBase sA₀ sA₀') (prodBase sB₀ sB₀')
    (prodHom sA sA' sA₀ sA₀' φA φA' hφA hφA') (prodHom sB sB' sB₀ sB₀' φB φB' hφB hφB')
    (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (prodHom_comp_prodBase _ _ _ _ _ _ _ _)

/-- The product of four isomorphisms is an isomorphism. -/
instance isIso_tensorProductHom :
    IsIso (tensorProductHom k sA sA' sB sB' sA₀ sA₀' sB₀ sB₀' φA φA' φB φB' hφA hφA' hφB hφB') := by
  have : IsIso (prodHom sA sA' sA₀ sA₀' φA φA' hφA hφA') :=
    Limits.pullback.map_isIso (i₃ := 𝟙 _) ..
  have : IsIso (prodHom sB sB' sB₀ sB₀' φB φB' hφB hφB') :=
    Limits.pullback.map_isIso (i₃ := 𝟙 _) ..
  unfold tensorProductHom prodHom
  apply Limits.pullback.map_isIso

omit [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] [LocallyOfFiniteType sB]
  [LocallyOfFiniteType sB'] [LocallyOfFiniteType sA₀] [LocallyOfFiniteType sA₀']
  [LocallyOfFiniteType sB₀] [LocallyOfFiniteType sB₀'] [Smooth sA] [Smooth sA'] [Smooth sB]
  [Smooth sB'] [Smooth sA₀] [Smooth sA₀'] [Smooth sB₀] [Smooth sB₀'] [IsIso φA] [IsIso φA']
  [IsIso φB] [IsIso φB'] in
/-- The product of the four isomorphisms is a morphism over `k`. -/
theorem tensorProductHom_comp_tensorBase :
    tensorProductHom k sA sA' sB sB' sA₀ sA₀' sB₀ sB₀' φA φA' φB φB' hφA hφA' hφB hφB' ≫
        tensorBase sA sA' sB sB' = tensorBase sA₀ sA₀' sB₀ sB₀' :=
  prodHom_comp_prodBase _ _ _ _ _ _ _ _

omit [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] [LocallyOfFiniteType sB]
  [LocallyOfFiniteType sB'] [LocallyOfFiniteType sA₀] [LocallyOfFiniteType sA₀']
  [LocallyOfFiniteType sB₀] [LocallyOfFiniteType sB₀'] [Smooth sA] [Smooth sA'] [Smooth sB]
  [Smooth sB'] [Smooth sA₀] [Smooth sA₀'] [Smooth sB₀] [Smooth sB₀'] [IsIso φA] [IsIso φA']
  [IsIso φB] [IsIso φB'] in
/-- The product of the four isomorphisms commutes with the projections `pr₁₃` onto the first and
third factors, with `φA × φB` on the target. -/
theorem tensorPr₁₃_tensorProductHom :
    tensorPr₁₃ sA₀ sA₀' sB₀ sB₀' ≫ prodHom sA sB sA₀ sB₀ φA φB hφA hφB =
      tensorProductHom k sA sA' sB sB' sA₀ sA₀' sB₀ sB₀' φA φA' φB φB' hφA hφA' hφB hφB' ≫
        tensorPr₁₃ sA sA' sB sB' := by
  apply Limits.pullback.hom_ext <;> simp [tensorProductHom]

omit [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] [LocallyOfFiniteType sB]
  [LocallyOfFiniteType sB'] [LocallyOfFiniteType sA₀] [LocallyOfFiniteType sA₀']
  [LocallyOfFiniteType sB₀] [LocallyOfFiniteType sB₀'] [Smooth sA] [Smooth sA'] [Smooth sB]
  [Smooth sB'] [Smooth sA₀] [Smooth sA₀'] [Smooth sB₀] [Smooth sB₀'] [IsIso φA] [IsIso φA']
  [IsIso φB] [IsIso φB'] in
/-- The product of the four isomorphisms commutes with the projections `pr₂₄` onto the second and
fourth factors, with `φA' × φB'` on the target. -/
theorem tensorPr₂₄_tensorProductHom :
    tensorPr₂₄ sA₀ sA₀' sB₀ sB₀' ≫ prodHom sA' sB' sA₀' sB₀' φA' φB' hφA' hφB' =
      tensorProductHom k sA sA' sB sB' sA₀ sA₀' sB₀ sB₀' φA φA' φB φB' hφA hφA' hφB hφB' ≫
        tensorPr₂₄ sA sA' sB sB' := by
  apply Limits.pullback.hom_ext <;> simp [tensorProductHom]

/-- Flat pullback along `d`, `v` commutes with pushforward along isomorphisms `u₀`, `u₁`, for
flat morphisms of a given relative dimension. -/
private theorem flatPullbackChow_chowPushforwardOfIso_general (C : ChowSituation.{u})
    {A₀ A₁ B₀ B₁ : Scheme.{u}} (sA₀ : A₀ ⟶ C.S) [LocallyOfFiniteType sA₀]
    (sA₁ : A₁ ⟶ C.S) [LocallyOfFiniteType sA₁] (sB₀ : B₀ ⟶ C.S) [LocallyOfFiniteType sB₀]
    (sB₁ : B₁ ⟶ C.S) [LocallyOfFiniteType sB₁]
    (u₀ : A₀ ⟶ B₀) [IsIso u₀] (hu₀ : u₀ ≫ sB₀ = sA₀)
    (u₁ : A₁ ⟶ B₁) [IsIso u₁] (hu₁ : u₁ ≫ sB₁ = sA₁)
    (d : A₁ ⟶ A₀) [LocallyOfFiniteType d] [Flat d] (hd : d ≫ sA₀ = sA₁)
    (v : B₁ ⟶ B₀) [LocallyOfFiniteType v] [Flat v] (hv : v ≫ sB₀ = sB₁)
    (hsq : d ≫ u₀ = u₁ ≫ v) {r : ℕ} (hdr : RelativeDimension d r) (hvr : RelativeDimension v r)
    (k : ℤ) (α : chowGroup C sA₀ k) :
    flatPullbackChow C sB₁ sB₀ v hv r hvr k
        (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
        (chowPushforwardOfIso C sA₀ sB₀ u₀ hu₀ k α) =
      chowPushforwardOfIso C sA₁ sB₁ u₁ hu₁ (k + (r : ℤ))
        (flatPullbackChow C sA₁ sA₀ d hd r hdr k
          (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) α) :=
  flatPullbackChow_chowPushforwardOfIso C sA₀ sA₁ sB₀ sB₁ u₀ hu₀ u₁ hu₁ d hd v hv hsq r hdr hvr k
    _ _ α

/-- **The tensor product of correspondences is natural with respect to isomorphisms over `k`**, on
integral Chow groups: for isomorphisms `φA, φA', φB, φB'` of the four factors over `k`,
`(φA × φA' × φB × φB')_*(c ⊗ c') = (φA × φB)_* c ⊗ (φA' × φB')_* c'`, for an iso-invariant family
of diagonal classes. -/
theorem chowPushforwardOfIso_tensorInt (hΔ : Δ.IsoInvariant) {d d' e e' : ℕ}
    (hA : RelativeDimension sA d) (hA' : RelativeDimension sA' d') (hB : RelativeDimension sB e)
    (hB' : RelativeDimension sB' e') (hA₀ : RelativeDimension sA₀ d)
    (hA₀' : RelativeDimension sA₀' d') (hB₀ : RelativeDimension sB₀ e)
    (hB₀' : RelativeDimension sB₀' e') (r r' : ℤ)
    (c : chowGroup (fieldChowSituation k) (prodBase sA₀ sB₀) ((e : ℤ) - r))
    (c' : chowGroup (fieldChowSituation k) (prodBase sA₀' sB₀') ((e' : ℤ) - r')) :
    chowPushforwardOfIso _ (tensorBase sA₀ sA₀' sB₀ sB₀') (tensorBase sA sA' sB sB')
        (tensorProductHom k sA sA' sB sB' sA₀ sA₀' sB₀ sB₀' φA φA' φB φB' hφA hφA' hφB hφB')
        (tensorProductHom_comp_tensorBase k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _
        (tensorInt k sA₀ sA₀' sB₀ sB₀' Δ hA₀ hA₀' hB₀ hB₀' r r' c c') =
      tensorInt k sA sA' sB sB' Δ hA hA' hB hB' r r'
        (chowPushforwardOfIso _ _ _ (prodHom sA sB sA₀ sB₀ φA φB hφA hφB)
          (prodHom_comp_prodBase _ _ _ _ _ _ _ _) _ c)
        (chowPushforwardOfIso _ _ _ (prodHom sA' sB' sA₀' sB₀' φA' φB' hφA' hφB')
          (prodHom_comp_prodBase _ _ _ _ _ _ _ _) _ c') := by
  set Ψ := tensorProductHom k sA sA' sB sB' sA₀ sA₀' sB₀ sB₀' φA φA' φB φB' hφA hφA' hφB hφB'
  have hΨ : Ψ ≫ tensorBase sA sA' sB sB' = tensorBase sA₀ sA₀' sB₀ sB₀' :=
    tensorProductHom_comp_tensorBase k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  simp only [tensorInt, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply,
    AddMonoidHom.coe_toIntLinearMap, LinearEquiv.coe_coe, AddEquiv.coe_toIntLinearEquiv]
  rw [flatPullbackChow_chowPushforwardOfIso_general (fieldChowSituation k) _ _ _ _ _
      (prodHom_comp_prodBase _ _ _ _ _ _ _ _) Ψ hΨ (tensorPr₁₃ _ _ _ _)
      (tensorPr₁₃_comp_prodBase _ _ _ _) (tensorPr₁₃ _ _ _ _)
      (tensorPr₁₃_comp_prodBase _ _ _ _)
      (tensorPr₁₃_tensorProductHom k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
      (relativeDimension_tensorPr₁₃ k _ _ _ _ hA₀' hB₀')
      (relativeDimension_tensorPr₁₃ k _ _ _ _ hA' hB') _ c,
    flatPullbackChow_chowPushforwardOfIso_general (fieldChowSituation k) _ _ _ _ _
      (prodHom_comp_prodBase _ _ _ _ _ _ _ _) Ψ hΨ (tensorPr₂₄ _ _ _ _)
      (tensorPr₂₄_comp_prodBase _ _ _ _) (tensorPr₂₄ _ _ _ _)
      (tensorPr₂₄_comp_prodBase _ _ _ _)
      (tensorPr₂₄_tensorProductHom k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
      (relativeDimension_tensorPr₂₄ k _ _ _ _ hA₀ hB₀)
      (relativeDimension_tensorPr₂₄ k _ _ _ _ hA hB) _ c',
    ← chowGroupDegreeEquiv_chowPushforwardOfIso,
    hΔ (tensorBase sA sA' sB sB') (tensorBase sA₀ sA₀' sB₀ sB₀') Ψ hΨ _
      (relativeDimension_tensorBase k sA sA' sB sB' hA hA' hB hB')
      (relativeDimension_tensorBase k sA₀ sA₀' sB₀ sB₀' hA₀ hA₀' hB₀ hB₀') _ _ _ _]
  congr 1
  exact (chowGroupEquivOfIso (fieldChowSituation k) _ _ Ψ hΨ _).apply_symm_apply _

/-- **The tensor product of correspondences is natural with respect to isomorphisms over `k`**:
for isomorphisms of the four factors over `k`, the transport of `c ⊗ c'` is the tensor product of
the transports, for an iso-invariant family of diagonal classes. -/
theorem correspondenceEquivOfIso_tensorBlock (hΔ : Δ.IsoInvariant) {d d' e e' : ℕ}
    (hA : RelativeDimension sA d) (hA' : RelativeDimension sA' d') (hB : RelativeDimension sB e)
    (hB' : RelativeDimension sB' e') (hA₀ : RelativeDimension sA₀ d)
    (hA₀' : RelativeDimension sA₀' d') (hB₀ : RelativeDimension sB₀ e)
    (hB₀' : RelativeDimension sB₀' e') (r r' : ℤ)
    (c : Correspondence (fieldChowSituation k) sA₀ sB₀ e r)
    (c' : Correspondence (fieldChowSituation k) sA₀' sB₀' e' r') :
    correspondenceEquivOfIso _ (prodBase sA sA') (prodBase sB sB') (prodBase sA₀ sA₀')
        (prodBase sB₀ sB₀') (prodHom sA sA' sA₀ sA₀' φA φA' hφA hφA')
        (prodHom sB sB' sB₀ sB₀' φB φB' hφB hφB') (prodHom_comp_prodBase _ _ _ _ _ _ _ _)
        (prodHom_comp_prodBase _ _ _ _ _ _ _ _) _ (r + r')
        (tensorBlock k sA₀ sA₀' sB₀ sB₀' Δ hA₀ hA₀' hB₀ hB₀' r r' c c') =
      tensorBlock k sA sA' sB sB' Δ hA hA' hB hB' r r'
        (correspondenceEquivOfIso _ sA sB sA₀ sB₀ φA φB hφA hφB e r c)
        (correspondenceEquivOfIso _ sA' sB' sA₀' sB₀' φA' φB' hφA' hφB' e' r' c') := by
  induction c using TensorProduct.inductionOn with
  | tmul q c =>
    induction c' using TensorProduct.inductionOn with
    | tmul q' c' =>
      rw [tensorBlock_tmul, correspondenceEquivOfIso_tmul, correspondenceEquivOfIso_tmul,
        correspondenceEquivOfIso_tmul, tensorBlock_tmul,
        ← chowPushforwardOfIso_tensorInt k Δ sA sA' sB sB' sA₀ sA₀' sB₀ sB₀' φA φA' φB φB' hφA hφA'
          hφB hφB' hΔ hA hA' hB hB' hA₀ hA₀' hB₀ hB₀']
    | add x y hx hy => simp only [map_add, hx, hy]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

end Naturality

/-! ### Correspondences between equidimensional schemes -/

section Equidimensional

variable {X X' Y Y' : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sX' : X' ⟶ (fieldChowSituation k).S)
  (sY : Y ⟶ (fieldChowSituation k).S) (sY' : Y' ⟶ (fieldChowSituation k).S)
  [Smooth sX] [IsSeparated sX] [Smooth sX'] [IsSeparated sX'] [Smooth sY] [IsSeparated sY]
  [Smooth sY'] [IsSeparated sY'] [IsProper sX] [IsProper sX'] [IsProper sY] [IsProper sY']

/-- Reading a block of the tensor product in the block of the product and then transporting it
to the product is transporting it directly: the inclusion of `(X_d × X'_{d'}) × (Y_e × Y'_{e'})`
in `(X × X')_{d+d'} × (Y × Y')_{e+e'}` followed by the inclusion of the latter in
`(X × X') × (Y × Y')` is the product of the inclusions of the four parts. -/
theorem correspondenceEquivOfIso_tensorBlockInclusion (d d' e e' : ℕ) (r : ℤ)
    [IsIso (dimPart sX d).ι] [IsIso (dimPart sX' d').ι] [IsIso (dimPart sY e).ι]
    [IsIso (dimPart sY' e').ι] [IsIso (dimPart (prodBase sX sX') (d + d')).ι]
    [IsIso (dimPart (prodBase sY sY') (e + e')).ι]
    (z : Correspondence (fieldChowSituation k) (prodBase (partBase sX d) (partBase sX' d'))
      (prodBase (partBase sY e) (partBase sY' e')) ((e + e' : ℕ) : ℤ) r) :
    correspondenceEquivOfIso (fieldChowSituation k) (prodBase sX sX') (prodBase sY sY')
        (partBase (prodBase sX sX') (d + d')) (partBase (prodBase sY sY') (e + e'))
        (dimPart (prodBase sX sX') (d + d')).ι (dimPart (prodBase sY sY') (e + e')).ι rfl rfl
        ((e + e' : ℕ) : ℤ) r (tensorBlockInclusion k sX sX' sY sY' d d' e e' r z) =
      correspondenceEquivOfIso (fieldChowSituation k) (prodBase sX sX') (prodBase sY sY')
        (prodBase (partBase sX d) (partBase sX' d')) (prodBase (partBase sY e) (partBase sY' e'))
        (prodHom sX sX' (partBase sX d) (partBase sX' d') (dimPart sX d).ι (dimPart sX' d').ι
          rfl rfl)
        (prodHom sY sY' (partBase sY e) (partBase sY' e') (dimPart sY e).ι (dimPart sY' e').ι
          rfl rfl)
        (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (prodHom_comp_prodBase _ _ _ _ _ _ _ _)
        ((e + e' : ℕ) : ℤ) r z := by
  have hw : tensorBlockHom k sX sX' sY sY' d d' e e' ≫
      prodHom (prodBase sX sX') (prodBase sY sY') (partBase (prodBase sX sX') (d + d'))
        (partBase (prodBase sY sY') (e + e')) (dimPart (prodBase sX sX') (d + d')).ι
        (dimPart (prodBase sY sY') (e + e')).ι rfl rfl =
      prodHom (prodBase sX sX') (prodBase sY sY') (prodBase (partBase sX d) (partBase sX' d'))
        (prodBase (partBase sY e) (partBase sY' e'))
        (prodHom sX sX' (partBase sX d) (partBase sX' d') (dimPart sX d).ι (dimPart sX' d').ι
          rfl rfl)
        (prodHom sY sY' (partBase sY e) (partBase sY' e') (dimPart sY e).ι (dimPart sY' e').ι
          rfl rfl)
        (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (prodHom_comp_prodBase _ _ _ _ _ _ _ _) := by
    apply Limits.pullback.hom_ext <;>
      simp only [tensorBlockHom, Category.assoc, Limits.pullback.lift_fst,
        Limits.pullback.lift_fst_assoc, Limits.pullback.lift_snd,
        Limits.pullback.lift_snd_assoc, partProdHom_ι]
  induction z using TensorProduct.inductionOn with
  | tmul q c =>
    rw [tensorBlockInclusion_tmul, correspondenceEquivOfIso_tmul, correspondenceEquivOfIso_tmul]
    congr 1
    rw [← properChowPushforward_eq_chowPushforwardOfIso _ _ _ _ _ _
        (properPushforwardDescends _ _ _ _ _ _),
      ← properChowPushforward_comp_apply (fieldChowSituation k) _ _ _ _ _ _ hw
        (tensorBlockHom_comp_prodBase k sX sX' sY sY' d d' e e')
        (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (prodHom_comp_prodBase _ _ _ _ _ _ _ _) _
        (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _)
        (properPushforwardDescends _ _ _ _ _ _)]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **The tensor product of correspondences between equidimensional schemes.** For `X, X', Y, Y'`
of constant relative dimensions `d, d', e, e'` over `k` and an iso-invariant family of diagonal
classes (for instance the canonical one, by
`Stacks.WeilCohomology.canonicalDiagonalClassFamily_isoInvariant`), the isomorphisms
`Corrʳ(X, Y) ≃ CH_{e-r}(X × Y) ⊗ ℚ` carry the tensor product of Section 0FFZ on the direct sums to
the tensor product `pr₁₃^* c · pr₂₄^* c'` on the products themselves. -/
theorem corrEquivCorrespondence_tensor (hΔ : Δ.IsoInvariant) {d d' e e' : ℕ}
    (hX : RelativeDimension sX d) (hX' : RelativeDimension sX' d') (hY : RelativeDimension sY e)
    (hY' : RelativeDimension sY' e') (hXX : RelativeDimension (prodBase sX sX') (d + d'))
    (hYY : RelativeDimension (prodBase sY sY') (e + e')) (r r' : ℤ) (a : Corr k sX sY r)
    (b : Corr k sX' sY' r') :
    corrEquivCorrespondence k (prodBase sX sX') (prodBase sY sY') hXX hYY (r + r')
        (tensor k sX sX' sY sY' Δ r r' a b) =
      tensorBlock k sX sX' sY sY' Δ hX hX' hY hY' r r'
        (corrEquivCorrespondence k sX sY hX hY r a)
        (corrEquivCorrespondence k sX' sY' hX' hY' r' b) := by
  have := isIso_dimPart_self_ι sX hX
  have := isIso_dimPart_self_ι sX' hX'
  have := isIso_dimPart_self_ι sY hY
  have := isIso_dimPart_self_ι sY' hY'
  have := isIso_dimPart_self_ι (prodBase sX sX') hXX
  have := isIso_dimPart_self_ι (prodBase sY sY') hYY
  obtain ⟨a, rfl⟩ := (corrEquivCorrespondence k sX sY hX hY r).symm.surjective a
  obtain ⟨b, rfl⟩ := (corrEquivCorrespondence k sX' sY' hX' hY' r').symm.surjective b
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    corrEquivCorrespondence_symm_apply, corrEquivCorrespondence_symm_apply, tensor_lof_lof,
    corrEquivCorrespondence_lof_lof, correspondenceEquivOfIso_tensorBlockInclusion,
    correspondenceEquivOfIso_tensorBlock k Δ sX sX' sY sY' _ _ _ _ (dimPart sX d).ι
      (dimPart sX' d').ι (dimPart sY e).ι (dimPart sY' e').ι rfl rfl rfl rfl hΔ hX hX' hY hY',
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- The identifications `Corrʳ(X, Y) ≃ CH_{e-r}(X × Y) ⊗ ℚ` carry the iterated composite
`comp (comp a b) c` of correspondences between equidimensional schemes to the iterated
`composition` of the images, for an iso-invariant family of diagonal classes. -/
theorem corrEquivCorrespondence_comp_comp (hΔ : Δ.IsoInvariant) {X Y Z W : Scheme.{u}}
    (sX : X ⟶ (fieldChowSituation k).S) (sY : Y ⟶ (fieldChowSituation k).S)
    (sZ : Z ⟶ (fieldChowSituation k).S) (sW : W ⟶ (fieldChowSituation k).S) [Smooth sX]
    [IsSeparated sX] [Smooth sY] [IsSeparated sY] [Smooth sZ] [IsSeparated sZ] [Smooth sW]
    [IsSeparated sW] [IsProper sY] [IsProper sZ] {dX dY dZ dW : ℕ}
    (hX : RelativeDimension sX dX) (hY : RelativeDimension sY dY) (hZ : RelativeDimension sZ dZ)
    (hW : RelativeDimension sW dW) (r s t : ℤ) (a : Corr k sX sY r) (b : Corr k sY sZ s)
    (c : Corr k sZ sW t) :
    corrEquivCorrespondence k sX sW hX hW (r + s + t)
        (comp k sX sZ sW Δ (r + s) t (comp k sX sY sZ Δ r s a b) c) =
      composition k sX sZ sW Δ hX hZ hW (r + s) t
        (composition k sX sY sZ Δ hX hY hZ r s (corrEquivCorrespondence k sX sY hX hY r a)
          (corrEquivCorrespondence k sY sZ hY hZ s b))
        (corrEquivCorrespondence k sZ sW hZ hW t c) := by
  rw [corrEquivCorrespondence_comp k sX sZ Δ hΔ sW hX hZ hW,
    corrEquivCorrespondence_comp k sX sY Δ hΔ sZ hX hY hZ]

end Equidimensional

end Stacks.WeilCohomology

end
