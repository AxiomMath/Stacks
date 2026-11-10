module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFibreStableReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFibrePureDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFibreTwistPurity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StableDecompositionAlgebra
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FiniteIndexSemisimple
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.SpanLatticeBound
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.ImageStabilizer
public import StacksFrontier.LinearAlgebra.CharpolyDecomposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFibrePureConstituent

/-!
# The decomposition into constituents which stay absolutely irreducible

Let `U ≅ 𝔸¹_k` over a finite field `k`, and let `σ` be a representation of `π₁(U)` over a finite
extension `E` of `ℚ_ℓ` which is absolutely irreducible and `ι'`-pure of weight `β`. For a suitable
finite extension `k₀` of `k`, the pullback of `σ` to `π₁(𝔸¹_{k₀})` is conjugate, over a finite
extension `E'` of `E`, to a direct sum of constituents which stay absolutely irreducible over every
finite extension of `k₀` and are `ι''`-pure of weight `β` for an embedding `ι''` of `E'` extending
`ι'`.

## Main results

All names are in the namespace `Stacks.EtaleCohomology`.

* `finiteEtale_specMap_polynomial_mapRingHom`: `𝔸¹_{k₀} → 𝔸¹_k` is finite étale.
* `finiteIndex_range_etaleFundamentalGroupMap`: for `T → S` finite étale, the image of
  `π₁(T) → π₁(S)` has finite index.
* `span_image_eq_of_span_eq`: images of sets with the same span span the same subspace over an
  extension of scalars.
* `norm_eq_of_isRoot_charpoly_pullback_frobenius`: the pullback of a pure representation to
  `π₁(𝔸¹_{k₀})` is pure of the same weight.
* `laumonStableDecompositionInput`: the decomposition.
* `laumonFibreStableReductionInput`: purity of the fibres for representations which stay absolutely
  irreducible implies it for every absolutely irreducible representation.

## References

* K. Kedlaya, *Fourier transforms and p-adic "Weil II"*, Compos. Math. 142 (2006), §6.4.
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix
open Module

universe u

namespace Stacks.EtaleCohomology

section FiniteIndex

/-- **`𝔸¹_{k₀} → 𝔸¹_k` is finite étale** for a finite extension `k₀` of a finite field `k`. -/
public theorem finiteEtale_specMap_polynomial_mapRingHom (k k₀ : Type u) [Field k] [Finite k]
    [Field k₀] [Finite k₀] [Algebra k k₀] :
    finiteEtale (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k₀)))) := by
  have : Module.Finite k k₀ := Module.Finite.of_finite
  have : Algebra.IsSeparable k k₀ := inferInstance
  have : Algebra.FormallyEtale k k₀ := Algebra.FormallyEtale.of_isSeparable k k₀
  have : Algebra.FinitePresentation k k₀ := Algebra.FinitePresentation.of_finiteType.mp
    inferInstance
  have : Algebra.Etale k k₀ :=
    { formallyEtale := inferInstance, finitePresentation := inferInstance }
  have hpb := isPullback_specMap_polynomial_mapRingHom k k₀
  have hfin : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k k₀))) := by
    rw [IsFinite.SpecMap_iff, CommRingCat.hom_ofHom]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have het : Etale (Spec.map (CommRingCat.ofHom (algebraMap k k₀))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale), CommRingCat.hom_ofHom]
    exact RingHom.etale_algebraMap.mpr inferInstance
  exact ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsFinite) hpb.flip hfin,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale) hpb.flip het⟩

/-- **The image of `π₁(T) → π₁(S)` has finite index** for a finite étale `T → S`. -/
public theorem finiteIndex_range_etaleFundamentalGroupMap {T S : Scheme.{u}} [ConnectedSpace S]
    [ConnectedSpace T] {f : T ⟶ S} (hf : finiteEtale f) (t : GeometricPoint T) :
    (etaleFundamentalGroupMap f t).toMonoidHom.range.FiniteIndex := by
  rw [range_etaleFundamentalGroupMap_eq_stabilizer hf t]
  have : Finite (MulAction.orbit (EtaleFundamentalGroup S (t.map f))
      (finiteEtaleOverSourcePoint hf t)) := Subtype.finite
  have := Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer
    (EtaleFundamentalGroup S (t.map f)) (finiteEtaleOverSourcePoint hf t))
  exact Subgroup.finiteIndex_of_finite_quotient

end FiniteIndex

section Span

variable {E E' : Type*} [Field E] [Field E'] [Algebra E E'] {M₁ M₂ : Type*} [AddCommGroup M₁]
  [Module E M₁] [AddCommGroup M₂] [Module E M₂] [Module E' M₂] [IsScalarTower E E' M₂]

/-- **Images of sets with the same span span the same subspace over an extension**: if
`span_E S₁ = span_E S₂` then `span_{E'} T(S₁) = span_{E'} T(S₂)` for every `E`-linear `T` into an
`E'`-module. -/
public theorem span_image_eq_of_span_eq (T : M₁ →ₗ[E] M₂) {S₁ S₂ : Set M₁}
    (h : Submodule.span E S₁ = Submodule.span E S₂) :
    Submodule.span E' (T '' S₁) = Submodule.span E' (T '' S₂) := by
  have key : ∀ {A B : Set M₁}, B ⊆ Submodule.span E A →
      Submodule.span E' (T '' B) ≤ Submodule.span E' (T '' A) := by
    intro A B hBA
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, hb, rfl⟩
    have hTb : T b ∈ Submodule.span E (T '' A) := by
      rw [Submodule.span_image]
      exact Submodule.mem_map_of_mem (hBA hb)
    exact Submodule.span_le_restrictScalars E E' _ hTb
  exact le_antisymm (key (h ▸ Submodule.subset_span)) (key (h.symm ▸ Submodule.subset_span))

end Span

section Purity

variable {U : Scheme.{u}} [ConnectedSpace U] {k : Type u} [Field k] [Fintype k]
  (f : U ⟶ Spec (.of k)) [LocallyOfFiniteType f] (e : U ⟶ Spec (.of (Polynomial k))) [IsIso e]
  {p n : ℕ} [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ n)
  (k₀ : Type u) [Field k₀] [Fintype k₀] [Algebra k k₀] {n₀ : ℕ} (hcard₀ : Fintype.card k₀ = p ^ n₀)
  (x₀ : GeometricPoint (Spec (.of (Polynomial k₀)))) {E : Type} [Field E] {m : ℕ}

omit [Fact p.Prime] [CharP k p] in
include hcard hcard₀ in
/-- **Purity of the pullback to `𝔸¹_{k₀}` at the closed points**: if `σ` is `ι'`-pure of weight
`β` at the closed points of `U`, then so is its pullback to `π₁(𝔸¹_{k₀})` along
`𝔸¹_{k₀} → 𝔸¹_k ≅ U` at the closed points of `𝔸¹_{k₀}`. -/
public theorem norm_eq_of_isRoot_charpoly_pullback_frobenius
    (σ : EtaleFundamentalGroup U (x₀.map (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (algebraMap k k₀))) ≫ inv e)) →* GL (Fin m) E)
    (ι' : E →+* ℂ) (β : ℤ)
    (hpure : ∀ (y : closedPoints U) (z : ℂ),
      ((σ (geometricFrobeniusFamily f (x₀.map (Spec.map (CommRingCat.ofHom
        (Polynomial.mapRingHom (algebraMap k k₀))) ≫ inv e)) y)).val.charpoly.map ι').IsRoot z →
        ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ (((residueDegree f y.1 : ℤ) * β : ℝ) / 2))
    [LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k₀ (Polynomial k₀))))]
    (y : closedPoints (Spec (.of (Polynomial k₀)))) (z : ℂ)
    (hz : ((σ (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (algebraMap k k₀))) ≫ inv e) x₀
        (geometricFrobeniusFamily (Spec.map (CommRingCat.ofHom (algebraMap k₀ (Polynomial k₀))))
          x₀ y))).val.charpoly.map ι').IsRoot z) :
    ‖z‖ = ((p ^ n₀ : ℕ) : ℝ) ^ (((residueDegree (Spec.map (CommRingCat.ofHom
      (algebraMap k₀ (Polynomial k₀)))) y.1 : ℤ) * β : ℝ) / 2) := by
  have := locallyOfFiniteType_specMap_mapRingHom k k₀
  let g : Spec (.of (Polynomial k₀)) ⟶ U :=
    Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k₀))) ≫ inv e
  let f₀ : Spec (.of (Polynomial k₀)) ⟶ Spec (.of k₀) :=
    Spec.map (CommRingCat.ofHom (algebraMap k₀ (Polynomial k₀)))
  have hy : g.base y.1 ∈ closedPoints U := by
    have : JacobsonSpace U := LocallyOfFiniteType.jacobsonSpace f
    exact g.closedPoints_subset_preimage_closedPoints y.2
  obtain ⟨h, hh⟩ := exists_etaleFundamentalGroupMap_geometricFrobeniusFamily_eq_conj_pow g x₀ y hy
    f f₀
  change ((((σ (etaleFundamentalGroupMap g x₀ (geometricFrobeniusFamily f₀ x₀ y)) :
    GL (Fin m) E) : Matrix (Fin m) (Fin m) E).charpoly.map ι').IsRoot z) at hz
  rw [hh, map_mul, map_mul, map_inv, charpoly_conj_val, map_pow, Units.val_pow_eq_pow_val,
    ← Matrix.charpoly_toLin', Matrix.toLin'_pow] at hz
  have := finite_residueField f₀ y.1 y.2
  have := finite_residueField f (g.base y.1) hy
  obtain ⟨v, hv, rfl⟩ := exists_isRoot_charpoly_map_pow_eq ι' _
    (residueFieldMapDegree_ne_zero g y) hz
  rw [Matrix.charpoly_toLin'] at hv
  have hvn := hpure ⟨g.base y.1, hy⟩ v hv
  have key : ∀ Q D r : ℕ, (((Q : ℕ) : ℝ) ^ (((D : ℤ) * β : ℝ) / 2)) ^ r =
      (((Q ^ (D * r) : ℕ)) : ℝ) ^ ((β : ℝ) / 2) := by
    intro Q D r
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), Nat.cast_pow,
      ← Real.rpow_natCast (Q : ℝ) (D * r), ← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    push_cast
    ring
  have hnat : (p ^ n) ^ (residueDegree f (g.base y.1) * residueFieldMapDegree g y) =
      (p ^ n₀) ^ (residueDegree f₀ y.1 * 1) := by
    have h₁ := natCard_residueField_eq (p := p) (n := n) (f := f) (y := ⟨g.base y.1, hy⟩) hcard
    have h₂ := natCard_residueField_eq (p := p) (n := n₀) (f := f₀) (y := y) hcard₀
    let := (g.residueFieldMap y.1).hom.toAlgebra
    have : Module.Finite (U.residueField (g.base y.1))
        ((Spec (.of (Polynomial k₀))).residueField y.1) := Module.Finite.of_finite
    have h₃ := Module.natCard_eq_pow_finrank (K := U.residueField (g.base y.1))
      (V := (Spec (.of (Polynomial k₀))).residueField y.1)
    rw [mul_one, ← pow_mul, ← pow_mul, ← h₂, ← mul_assoc, pow_mul, ← h₁, h₃]
    rfl
  have hR : ((p ^ n₀ : ℕ) : ℝ) ^ (((residueDegree f₀ y.1 : ℤ) * β : ℝ) / 2) =
      (((p ^ n₀) ^ (residueDegree f₀ y.1 * 1) : ℕ) : ℝ) ^ ((β : ℝ) / 2) := by
    rw [← key, pow_one]
  rw [norm_pow, hvn, key]
  exact (congrArg (fun N : ℕ => ((N : ℕ) : ℝ) ^ ((β : ℝ) / 2)) hnat).trans hR.symm

end Purity

section Main

/-- A group representation into `GL_ι(E)` which is irreducible over an algebraically closed
`K ⊇ E` has `E`-span of its matrices equal to all matrices. -/
private theorem span_range_val_eq_top_of_irreducible {G E K ι : Type*} [Group G] [Field E]
    [Field K] [IsAlgClosed K] [Algebra E K] [Fintype ι] [DecidableEq ι]
    (ρ : G →* (Matrix ι ι E)ˣ)
    (hirr : ∀ W : Submodule K (ι → K),
      (∀ g, ∀ v ∈ W, (ρ g).val.map (algebraMap E K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) :
    Submodule.span E (Set.range fun g => (ρ g).val) = ⊤ :=
  span_range_eq_top_of_forall_mulVec_map_mem (K := K) (fun g => (ρ g).val)
    (fun a b => ⟨a * b, by rw [map_mul, Units.val_mul]⟩) ⟨1, by rw [map_one, Units.val_one]⟩ hirr

/-- **The decomposition into constituents which stay absolutely irreducible**
(`Stacks.EtaleCohomology.LaumonStableDecompositionInput`; Kedlaya, *Fourier transforms and p-adic
Weil II*, §6.4, in the proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): for `σ` on
`U ≅ 𝔸¹_k` absolutely irreducible and `ι'`-pure of weight `β`, the pullback of `σ` to
`π₁(𝔸¹_{k₀})`, for a suitable finite extension `k₀` of `k`, is conjugate over a finite extension
`E'` of `E` to a direct sum of representations which stay absolutely irreducible over every finite
extension of `k₀` and are `ι''`-pure of weight `β`. -/
public theorem laumonStableDecompositionInput : LaumonStableDecompositionInput.{u} := by
  intro B U ℓ _ _ k _ _ f _ e _ he p n _ _ hcard x E _ _ _ d b m σ hσ K _ _ _ hirr ι' β hpure
  classical
  have hspanσ : Submodule.span E (Set.range fun g => (σ g).val) = ⊤ :=
    span_range_val_eq_top_of_irreducible (K := K) σ hirr
  let P : ℕ → Prop := fun d => ∃ (k₁ : Type u) (_ : Field k₁) (_ : Fintype k₁) (_ : Algebra k k₁)
    (x₁ : GeometricPoint (Spec (.of (Polynomial k₁))))
    (_ : x₁.map (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k₁))) ≫
      inv e) = x)
    (Φ : EtaleFundamentalGroup (Spec (.of (Polynomial k₁))) x₁ →* EtaleFundamentalGroup U.1 x),
    IsEtaleFundamentalGroupHomInducedBy (finiteEtaleBaseChange
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k₁))) ≫ inv e)) Φ ∧
    finrank E (Submodule.span E (Set.range fun γ => (σ (Φ γ)).val)) = d
  have hP : ∃ d, P d := by
    obtain ⟨x₁, hx₁⟩ := exists_geometricPoint_polynomial_map_eq e k x
    exact ⟨_, k, inferInstance, inferInstance, Algebra.id k, x₁, hx₁, _,
      isEtaleFundamentalGroupHomInducedBy_map_cast _ x₁ hx₁, rfl⟩
  obtain ⟨k₀, _, _, _, x₀, hx₀, Φ₀, hΦ₀, hd₀⟩ := Nat.find_spec hP
  subst hx₀
  let g₀ : Spec (.of (Polynomial k₀)) ⟶ U.1 :=
    Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k₀))) ≫ inv e
  let φ₀ : EtaleFundamentalGroup (Spec (.of (Polynomial k₀))) x₀ →* EtaleFundamentalGroup U.1
      (x₀.map g₀) := (etaleFundamentalGroupMap g₀ x₀).toMonoidHom
  have hφ₀ : IsEtaleFundamentalGroupHomInducedBy (finiteEtaleBaseChange g₀) φ₀ :=
    isEtaleFundamentalGroupHomInducedBy_map g₀ x₀
  have hdφ₀ : finrank E (Submodule.span E (Set.range fun γ => (σ (φ₀ γ)).val)) = Nat.find hP := by
    obtain ⟨c, hc⟩ := hΦ₀.isInnerConjugate_of_eq hφ₀ rfl
    have h : (fun γ => (σ (φ₀ γ)).val) = fun γ =>
        ((σ c : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) * (σ (Φ₀ γ)).val *
          (((σ c)⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) := by
      funext γ
      rw [hc γ, map_mul, map_mul, map_inv]
      rfl
    rw [h, finrank_span_range_conj, hd₀]
  have hstab : ∀ (k' : Type u) [Field k'] [Fintype k'] [Algebra k₀ k']
      (x' : GeometricPoint (Spec (.of (Polynomial k'))))
      (hx' : x'.map (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k₀ k'))) ≫
        inv (𝟙 (Spec (.of (Polynomial k₀))))) = x₀),
      Submodule.span E (Set.range fun γ' => (σ (φ₀ ((hx' ▸ (etaleFundamentalGroupMap
        (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k₀ k'))) ≫
          inv (𝟙 (Spec (.of (Polynomial k₀))))) x').toMonoidHom) γ'))).val) =
      Submodule.span E (Set.range fun γ => (σ (φ₀ γ)).val) := by
    intro k' _ _ _ x' hx'
    let ik : Algebra k k' := ((algebraMap k₀ k').comp (algebraMap k k₀)).toAlgebra
    have halg : algebraMap k k' = (algebraMap k₀ k').comp (algebraMap k k₀) := rfl
    have hcomp : Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e =
        (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k₀ k'))) ≫
          inv (𝟙 (Spec (.of (Polynomial k₀))))) ≫ g₀ := by
      simp only [g₀, IsIso.inv_id, Category.comp_id, ← Category.assoc, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, Polynomial.mapRingHom_comp, halg]
    have hxk : x'.map (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫
        inv e) = x₀.map g₀ := by
      rw [hcomp, GeometricPoint.map_comp, hx']
    have hΦ' : IsEtaleFundamentalGroupHomInducedBy (finiteEtaleBaseChange
        (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e))
        (φ₀.comp (hx' ▸ (etaleFundamentalGroupMap
          (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k₀ k'))) ≫
            inv (𝟙 (Spec (.of (Polynomial k₀))))) x').toMonoidHom)) := by
      rw [hcomp]
      exact (isEtaleFundamentalGroupHomInducedBy_map_cast _ x' hx').comp_baseChange hφ₀
    have hmin := Nat.find_min' hP ⟨k', inferInstance, inferInstance, ik, x', hxk, _, hΦ', rfl⟩
    have hle : Submodule.span E (Set.range fun γ' => (σ (φ₀ ((hx' ▸ (etaleFundamentalGroupMap
        (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k₀ k'))) ≫
          inv (𝟙 (Spec (.of (Polynomial k₀))))) x').toMonoidHom) γ'))).val) ≤
        Submodule.span E (Set.range fun γ => (σ (φ₀ γ)).val) :=
      Submodule.span_mono (by rintro _ ⟨γ', rfl⟩; exact ⟨_, rfl⟩)
    exact Submodule.eq_of_le_of_finrank_le hle (by rw [hdφ₀]; exact hmin)
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[ℓ] E).injective
  have : CharZero (algebraicClosure E K) :=
    charZero_of_injective_algebraMap (algebraMap E (algebraicClosure E K)).injective
  have hfe := finiteEtale_specMap_polynomial_mapRingHom k k₀
  have hfe₀ : finiteEtale g₀ := by
    have : IsFinite (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k₀)))) :=
      hfe.1
    have : Etale (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k₀)))) :=
      hfe.2
    exact ⟨inferInstanceAs (IsFinite (_ ≫ inv e)), inferInstanceAs (Etale (_ ≫ inv e))⟩
  have hfi : φ₀.range.FiniteIndex := finiteIndex_range_etaleFundamentalGroupMap hfe₀ x₀
  have hss : ∀ W : Submodule (algebraicClosure E K) (Fin m → algebraicClosure E K),
      (∀ γ, ∀ v ∈ W, (σ (φ₀ γ)).val.map (algebraMap E (algebraicClosure E K)) *ᵥ v ∈ W) →
      ∃ W', IsCompl W W' ∧
        ∀ γ, ∀ v ∈ W', (σ (φ₀ γ)).val.map (algebraMap E (algebraicClosure E K)) *ᵥ v ∈ W' :=
    fun W hW => exists_isCompl_comp_of_irreducible
      ((Matrix.GeneralLinearGroup.map (algebraMap E (algebraicClosure E K))).comp σ) φ₀
      φ₀.range.normalCore (Subgroup.normalCore_le _)
      (fun W hW => eq_bot_or_eq_top_of_span_range_eq_top (K := algebraicClosure E K)
        (fun g => (σ g).val) hspanσ W hW) W hW
  obtain ⟨E', hfin, r, ms, eqv, Q, hblk, hirrK⟩ :=
    exists_intermediateField_blockDiagonal (K := K) (fun γ => (σ (φ₀ γ)).val) hss
  let iQ : Algebra ℚ_[ℓ] E' := ((algebraMap E E').comp (algebraMap ℚ_[ℓ] E)).toAlgebra
  have tQ : IsScalarTower ℚ_[ℓ] E E' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have fQ : FiniteDimensional ℚ_[ℓ] E' := Module.Finite.trans E E'
  have : Algebra.IsAlgebraic E E' := Algebra.IsAlgebraic.of_finite E E'
  let iC : Algebra E ℂ := ι'.toAlgebra
  let j : E' →ₐ[E] ℂ := IsAlgClosed.lift
  have hι : j.toRingHom.comp (algebraMap E E') = ι' := RingHom.ext fun a => j.commutes a
  let τE : EtaleFundamentalGroup (Spec (.of (Polynomial k₀))) x₀ →* Matrix (Fin m) (Fin m) E' :=
    (Units.coeHom _).comp ((Matrix.GeneralLinearGroup.map (algebraMap E E')).comp (σ.comp φ₀))
  let ρE := conjReindexHom τE eqv Q
  have hρE : ∀ γ, ρE γ = blockDiagonal' (blockDiag' (ρE γ)) := hblk
  let σs : ∀ i, EtaleFundamentalGroup (Spec (.of (Polynomial k₀))) x₀ →* GL (Fin (ms i)) E' :=
    fun i => (blockDiagRep ρE hρE i).toHomUnits
  let T : ∀ i, Matrix (Fin m) (Fin m) E →ₗ[E] Matrix (Fin (ms i)) (Fin (ms i)) E' := fun i =>
    { toFun := fun X => blockDiag' ((Q : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) E') *
        reindexLinearEquiv E E' eqv eqv ((Algebra.ofId E E').mapMatrix X) *
          ((Q⁻¹ : GL (Σ i, Fin (ms i)) E') : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) E')) i
      map_add' := fun X Y => by
        simp only [map_add, Matrix.mul_add, Matrix.add_mul, blockDiag'_add, Pi.add_apply]
      map_smul' := fun c X => by
        simp only [map_smul, Matrix.mul_smul, Matrix.smul_mul, blockDiag'_smul, Pi.smul_apply,
          RingHom.id_apply] }
  have hT : ∀ i γ, (σs i γ).val = T i (σ (φ₀ γ)).val := fun i γ => rfl
  have hspan : ∀ i, Submodule.span E' (Set.range fun γ => (σs i γ).val) = ⊤ := fun i =>
    span_range_val_eq_top_of_irreducible (K := K) (σs i) (fun W hW => hirrK i W hW)
  have : Module.Finite k k₀ := Module.Finite.of_finite
  have hcard₀ : Fintype.card k₀ = p ^ (n * finrank k k₀) := by
    rw [Module.card_eq_pow_finrank (K := k) (V := k₀), hcard, pow_mul]
  have hτc : Continuous (restrictScalarsRep b (σ.comp φ₀)) :=
    continuous_restrictScalarsRep_comp_etaleFundamentalGroupMap g₀ x₀ rfl b σ hσ
  refine ⟨k₀, inferInstance, inferInstance, inferInstance, schemeSizeBelow_spec_polynomial k₀ B,
    x₀, rfl, n * finrank k k₀, hcard₀, E', inferInstance, iQ, fQ, inferInstance, tQ,
    finrank ℚ_[ℓ] E', Module.finBasis ℚ_[ℓ] E', j.toRingHom, r, ms, σs, eqv, Q, hι,
    fun i => continuous_restrictScalarsRep_of_linearMap b (Module.finBasis ℚ_[ℓ] E') hτc (σs i)
      ((T i).restrictScalars ℚ_[ℓ]) (hT i),
    fun i K' _ _ _ W hW => eq_bot_or_eq_top_of_span_range_eq_top (K := K') (fun g => (σs i g).val)
      (hspan i) W hW, ?_, ?_, fun γ => hblk γ⟩
  · intro i k' _ _ _ x' hx' K' _ _ _ W hW
    refine eq_bot_or_eq_top_of_span_range_eq_top (K := K') _ ?_ W hW
    rw [eq_top_iff, ← hspan i]
    have h1 : (Set.range fun γ' => (((σs i).comp (hx' ▸ (etaleFundamentalGroupMap
        (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k₀ k'))) ≫
          inv (𝟙 (Spec (.of (Polynomial k₀))))) x').toMonoidHom)) γ').val) =
        T i '' Set.range fun γ' => (σ (φ₀ ((hx' ▸ (etaleFundamentalGroupMap
          (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k₀ k'))) ≫
            inv (𝟙 (Spec (.of (Polynomial k₀))))) x').toMonoidHom) γ'))).val := by
      rw [← Set.range_comp]
      rfl
    have h2 : (Set.range fun γ => (σs i γ).val) =
        T i '' Set.range fun γ => (σ (φ₀ γ)).val := by
      rw [← Set.range_comp]
      rfl
    rw [h1, h2, span_image_eq_of_span_eq (T i) (hstab k' x' hx')]
  · intro i y z hz
    have hprod : ((σ (φ₀ (geometricFrobeniusFamily
        (Spec.map (CommRingCat.ofHom (algebraMap k₀ (Polynomial k₀)))) x₀ y))).val.charpoly.map
          ι') = ∏ t, ((σs t (geometricFrobeniusFamily
            (Spec.map (CommRingCat.ofHom (algebraMap k₀ (Polynomial k₀)))) x₀ y)).val.charpoly.map
              j.toRingHom) := by
      set γ := geometricFrobeniusFamily
        (Spec.map (CommRingCat.ofHom (algebraMap k₀ (Polynomial k₀)))) x₀ y
      have hbd : blockDiagonal' (fun t => (σs t γ).val) = ρE γ := (hρE γ).symm
      have hcp : (blockDiagonal' fun t => (σs t γ).val).charpoly =
          (σ (φ₀ γ)).val.charpoly.map (algebraMap E E') := by
        rw [hbd, conjReindexHom_apply, Matrix.coe_units_inv, Matrix.charpoly_units_conj,
          Matrix.charpoly_reindex]
        exact Matrix.charpoly_map (σ (φ₀ γ)).val (algebraMap E E')
      rw [← Polynomial.map_prod j.toRingHom (fun t => (σs t γ).val.charpoly) Finset.univ,
        ← Matrix.charpoly_blockDiagonal' (fun t => (σs t γ).val), hcp,
        Polynomial.map_map, hι]
    have hroot : ((σ (φ₀ (geometricFrobeniusFamily
        (Spec.map (CommRingCat.ofHom (algebraMap k₀ (Polynomial k₀)))) x₀ y))).val.charpoly.map
          ι').IsRoot z := by
      rw [hprod, Polynomial.IsRoot, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hz
    exact norm_eq_of_isRoot_charpoly_pullback_frobenius f e hcard k₀ hcard₀ x₀ σ ι' β hpure y z
      hroot

/-- **The reduction to representations which stay absolutely irreducible**
(`Stacks.EtaleCohomology.LaumonFibreStableReductionInput`): the purity of the fibres for
representations which stay absolutely irreducible over every finite extension of the base field
implies it for every absolutely irreducible representation. -/
public theorem laumonFibreStableReductionInput : LaumonFibreStableReductionInput.{u} :=
  laumonFibreStableReductionInput_of_inputs laumonFibrePureDescentInput
    laumonFibrePureConstituentInput laumonStableDecompositionInput

end Main

end Stacks.EtaleCohomology

end
