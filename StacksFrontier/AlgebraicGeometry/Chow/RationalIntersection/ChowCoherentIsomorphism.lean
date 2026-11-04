module

public import StacksFrontier.AlgebraicGeometry.Chow.AdamsOperator.SecondAdamsDerived
public import StacksFrontier.AlgebraicGeometry.Chow.AdamsOperator.SupportedDevissage
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.CodimensionWeightOperator
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0FEW: `K'₀(X) ⊗ 𝐐 ≅ CH_*(X) ⊗ 𝐐`

Let `(S, δ)` be as in Situation 02QL and let `i : X ⟶ Y` be a closed immersion of schemes locally
of finite type over `S`, with `Y` regular and quasi-compact. This file assembles Stacks 0FEW.

## Transport of an operator along the dévissage

Direct image identifies `𝐐 ⊗ K₀(Coh_Z(X))` with `𝐐 ⊗ K₀(Coh_{i(Z)}(Y))`, naturally in the closed
subset `Z ⊆ X` (`Stacks.Chow.supportedCoherentKZeroRatPushforwardIso`, Stacks 0FDT with
supports). An endomorphism `ψ` of `W ↦ 𝐐 ⊗ K₀(Coh_W(Y))` therefore transports to an endomorphism
of `Z ↦ 𝐐 ⊗ K₀(Coh_Z(X))`. Direct image preserves the `k`-cycles: at a point `ξ` with
`δ(ξ) = k` the coefficient of `[ℱ]_k` is the length of `ℱ_ξ`, which is the length of
`(i_*ℱ)_{i(ξ)}`, and `δ_{X/S}(ξ) = δ_{Y/S}(i(ξ))`. So codimension weights on `Y` transport to
codimension weights on `X`.

## Main definitions

* `Stacks.Chow.transportedOperator` — the endomorphism of `Z ↦ 𝐐 ⊗ K₀(Coh_Z(X))` induced by an
  endomorphism of `W ↦ 𝐐 ⊗ K₀(Coh_W(Y))`.

## Main results

* `Stacks.Chow.rationalCycleCoeff_supportedCoherentKZeroRatCycle_pushforward` — direct image
  preserves the coefficients of the `k`-cycles.
* `Stacks.Chow.transportedOperator_codimensionWeight` — codimension weights transport.
* `Stacks.Chow.injective_liftBaseChange_coherentChowCharacter` — injectivity in Stacks 0FEW.
* `Stacks.Chow.bijective_liftBaseChange_coherentChowCharacter` — **Stacks 0FEW**.

## References

* [Stacks Project, Tag 0FEW](https://stacks.math.columbia.edu/tag/0FEW)
* [Stacks Project, Tag 0FDT](https://stacks.math.columbia.edu/tag/0FDT)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (a : Y ⟶ C.S) [LocallyOfFiniteType a]
  (i : X ⟶ Y) [IsClosedImmersion i]

/-! ### Transport along the dévissage -/

section Transport

variable [IsLocallyNoetherian Y] [IsLocallyNoetherian X] [CompactSpace Y]

/-- The endomorphism of `Z ↦ 𝐐 ⊗ K₀(Coh_Z(X))` induced, through the dévissage isomorphism
`𝐐 ⊗ K₀(Coh_Z(X)) ≅ 𝐐 ⊗ K₀(Coh_{i(Z)}(Y))`, by an endomorphism of `W ↦ 𝐐 ⊗ K₀(Coh_W(Y))`. -/
def transportedOperator (ψ : supportedCoherentKZeroRat Y ⟶ supportedCoherentKZeroRat Y) :
    supportedCoherentKZeroRat X ⟶ supportedCoherentKZeroRat X :=
  (supportedCoherentKZeroRatPushforwardIso i).hom ≫ Functor.whiskerLeft i.closedImageFunctor ψ ≫
    (supportedCoherentKZeroRatPushforwardIso i).inv

omit [LocallyOfFiniteType a] [IsLocallyNoetherian Y] [IsLocallyNoetherian X] [CompactSpace Y] in
/-- The relative dimension on the image `i(Z)` is that on `Z`. -/
theorem forall_mem_closedImage_relativeDimension_le {Z : Closeds X} {k : ℤ}
    (hZ : ∀ z ∈ Z, relativeDimension C.dimensionFunction (i ≫ a) z ≤ k) :
    ∀ y ∈ i.closedImage Z, relativeDimension C.dimensionFunction a y ≤ k := by
  rintro _ ⟨z, hz, rfl⟩
  rw [← relativeDimension_comp_closedImmersion]
  exact hZ z hz

/-- **Direct image preserves the coefficients of `k`-cycles.** At a point `ξ` with
`δ_{X/S}(ξ) = k`, the coefficient of the `k`-cycle of `x ∈ 𝐐 ⊗ K₀(Coh_Z(X))` equals that, at
`i(ξ)`, of the `k`-cycle of its direct image in `𝐐 ⊗ K₀(Coh_{i(Z)}(Y))`. -/
theorem rationalCycleCoeff_supportedCoherentKZeroRatCycle_pushforward {Z : Closeds X} {k : ℤ}
    (hZ : ∀ z ∈ Z, relativeDimension C.dimensionFunction (i ≫ a) z ≤ k)
    (x : (supportedCoherentKZeroRat X).obj Z) {ξ : X}
    (hξ : relativeDimension C.dimensionFunction (i ≫ a) ξ = k) :
    rationalCycleCoeff C (i ≫ a) k ξ (supportedCoherentKZeroRatCycle C (i ≫ a) Z k hZ x) =
      rationalCycleCoeff C a k (i.base ξ)
        (supportedCoherentKZeroRatCycle C a (i.closedImage Z) k
          (forall_mem_closedImage_relativeDimension_le C a i hZ)
          (((supportedCoherentKZeroRatPushforwardIso i).hom.app Z).hom x)) := by
  have hξ' : relativeDimension C.dimensionFunction a (i.base ξ) = k := by
    rw [← relativeDimension_comp_closedImmersion]
    exact hξ
  have h : (cycleCoeffHom C (i ≫ a) k ξ).comp (supportedCoherentKZeroCycle C (i ≫ a) Z k hZ) =
      ((cycleCoeffHom C a k (i.base ξ)).comp (supportedCoherentKZeroCycle C a (i.closedImage Z) k
        (forall_mem_closedImage_relativeDimension_le C a i hZ))).comp
          (supportedCoherentKZeroPushforward i Z) :=
    KZero.hom_ext fun A => by
      simp only [AddMonoidHom.comp_apply, cycleCoeffHom_apply,
        supportedCoherentKZeroPushforward_mk]
      rw [supportedCoherentKZeroCycle_mk_apply_of_eq C (i ≫ a) Z k hZ A hξ,
        supportedCoherentKZeroCycle_mk_apply_of_eq C a _ k _ _ hξ']
      exact (sheafMultiplicity_pushforward_of_isClosedImmersion i A.obj.obj ξ).symm
  set e := ((supportedCoherentKZeroRatPushforwardIso i).hom.app Z).hom
  set c₁ := supportedCoherentKZeroRatCycle C (i ≫ a) Z k hZ
  set c₂ := supportedCoherentKZeroRatCycle C a (i.closedImage Z) k
    (forall_mem_closedImage_relativeDimension_le C a i hZ)
  set r₁ := rationalCycleCoeff C (i ≫ a) k ξ
  set r₂ := rationalCycleCoeff C a k (i.base ξ)
  induction x using TensorProduct.induction_on with
  | zero =>
    refine ((congrArg r₁ (map_zero c₁)).trans (map_zero r₁)).trans ?_
    exact ((congrArg r₂ ((congrArg c₂ (map_zero e)).trans (map_zero c₂))).trans
      (map_zero r₂)).symm
  | tmul q b =>
    show r₁ (q ⊗ₜ[ℤ] supportedCoherentKZeroCycle C (i ≫ a) Z k hZ b) =
      r₂ (q ⊗ₜ[ℤ] supportedCoherentKZeroCycle C a (i.closedImage Z) k
        (forall_mem_closedImage_relativeDimension_le C a i hZ)
        (supportedCoherentKZeroPushforward i Z b))
    rw [rationalCycleCoeff_tmul, rationalCycleCoeff_tmul]
    have := DFunLike.congr_fun h b
    simp only [AddMonoidHom.comp_apply, cycleCoeffHom_apply] at this
    rw [this]
  | add x y hx hy =>
    refine ((congrArg r₁ (map_add c₁ x y)).trans (map_add r₁ _ _)).trans ?_
    refine (congrArg₂ (· + ·) hx hy).trans ?_
    exact ((congrArg r₂ ((congrArg c₂ (map_add e x y)).trans (map_add c₂ _ _))).trans
      (map_add r₂ _ _)).symm

/-- **Codimension weights transport along the dévissage.** If `ψ` acts on the `k`-cycles of
`𝐐 ⊗ K₀(Coh_W(Y))`, at each point `y ∈ W` with `δ(y) = k` maximal on `W`, as multiplication by
`ℓ^n`, `n = dim 𝒪_{Y, y}`, then the transported operator acts on the `k`-cycles of
`𝐐 ⊗ K₀(Coh_Z(X))` at each `ξ ∈ Z` with `δ(ξ) = k` maximal on `Z` as multiplication by `ℓ^n`,
`n = dim 𝒪_{Y, i(ξ)}`: this is the hypothesis of
`Stacks.Chow.injective_liftBaseChange_coherentChowCharacter_of_codimensionWeightOperator`. -/
theorem transportedOperator_codimensionWeight {ℓ : ℚ}
    (ψ : supportedCoherentKZeroRat Y ⟶ supportedCoherentKZeroRat Y)
    (hψ : ∀ (W : Closeds Y) (k : ℤ)
      (hW : ∀ z ∈ W, relativeDimension C.dimensionFunction a z ≤ k)
      (x : (supportedCoherentKZeroRat Y).obj W) (y : Y), y ∈ W →
      relativeDimension C.dimensionFunction a y = k → ∀ n : ℕ,
      ringKrullDim (Y.presheaf.stalk y) = (n : ℕ∞) →
      rationalCycleCoeff C a k y (supportedCoherentKZeroRatCycle C a W k hW ((ψ.app W).hom x)) =
        ℓ ^ n * rationalCycleCoeff C a k y (supportedCoherentKZeroRatCycle C a W k hW x))
    (Z : Closeds X) (k : ℤ) (hZ : ∀ z ∈ Z, relativeDimension C.dimensionFunction (i ≫ a) z ≤ k)
    (x : (supportedCoherentKZeroRat X).obj Z) (ξ : X) (hξZ : ξ ∈ Z)
    (hξ : relativeDimension C.dimensionFunction (i ≫ a) ξ = k) (n : ℕ)
    (hn : ringKrullDim (Y.presheaf.stalk (i.base ξ)) = (n : ℕ∞)) :
    rationalCycleCoeff C (i ≫ a) k ξ
        (supportedCoherentKZeroRatCycle C (i ≫ a) Z k hZ
          (((transportedOperator i ψ).app Z).hom x)) =
      ℓ ^ n * rationalCycleCoeff C (i ≫ a) k ξ
        (supportedCoherentKZeroRatCycle C (i ≫ a) Z k hZ x) := by
  have hξ' : relativeDimension C.dimensionFunction a (i.base ξ) = k := by
    rw [← relativeDimension_comp_closedImmersion]
    exact hξ
  rw [rationalCycleCoeff_supportedCoherentKZeroRatCycle_pushforward C a i hZ _ hξ,
    rationalCycleCoeff_supportedCoherentKZeroRatCycle_pushforward C a i hZ _ hξ]
  have he : ((supportedCoherentKZeroRatPushforwardIso i).hom.app Z).hom
      (((transportedOperator i ψ).app Z).hom x) =
        (ψ.app (i.closedImage Z)).hom
          (((supportedCoherentKZeroRatPushforwardIso i).hom.app Z).hom x) := by
    simp only [transportedOperator, NatTrans.comp_app, Functor.whiskerLeft_app,
      ModuleCat.comp_apply]
    exact congr($(Iso.inv_hom_id_app (supportedCoherentKZeroRatPushforwardIso i) Z).hom _)
  rw [he]
  exact hψ _ k _ _ (i.base ξ) (show i.base ξ ∈ i.base '' (Z : Set X) from ⟨ξ, hξZ, rfl⟩)
    hξ' n hn

end Transport

/-! ### Stacks 0FEW -/

section Proposition

variable (hY : IsRegular Y) [CompactSpace Y]

/-- **Injectivity in Stacks 0FEW.** For a closed immersion `i : X ⟶ Y` of schemes locally of
finite type over `S`, with `Y` regular and quasi-compact, the composition
`ℱ ↦ ch(X ⟶ Y, ℱ[0]) ∩ [Y]` induces an injection `K'₀(X) ⊗ 𝐐 ⟶ CH_*(X) ⊗ 𝐐`. No bound on `δ`
and no separatedness are assumed.

The second Adams operation `ψ² = [L T] - 2 [L Λ²]` on `𝐐 ⊗ K₀(Coh_W(Y))`
(`Stacks.Chow.supportedSecondAdamsRat`) multiplies the coefficient of a `k`-cycle at a point `y`
of maximal `δ` by `2^{dim 𝒪_{Y, y}}`; transported to `𝐐 ⊗ K₀(Coh_Z(X))` along the dévissage, it
is an operator with codimension weights, and the separation of weights
(`Stacks.Chow.injective_liftBaseChange_coherentChowCharacter_of_codimensionWeightOperator`)
gives injectivity. -/
theorem injective_liftBaseChange_coherentChowCharacter :
    Function.Injective ((coherentChowCharacter C a i hY).toIntLinearMap.liftBaseChange ℚ) := by
  have := isNoetherian_of_isClosedImmersion_of_compactSpace C a i
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian a
  refine injective_liftBaseChange_coherentChowCharacter_of_codimensionWeightOperator C a i hY
    (ℓ := 2) one_lt_two (transportedOperator i (supportedSecondAdamsRat Y hY)) ?_
  intro Z k hZ x ξ hξZ hξ n hn
  exact transportedOperator_codimensionWeight C a i (ℓ := 2) _
    (fun W k hW x y _ hy n hn =>
      rationalCycleCoeff_supportedCoherentKZeroRatCycle_supportedSecondAdamsRat C a hY W k hW x y
        hy n hn) Z k hZ x ξ hξZ hξ n hn

/-- **Stacks 0FEW.** Let `(S, δ)` be as in Situation 02QL and let `i : X ⟶ Y` be a closed
immersion of schemes locally of finite type over `S`, with `Y` regular and quasi-compact. Then
the composition `K'₀(X) ⟶ K₀(D_{X, perf}(𝒪_Y)) ⟶ A^*(X ⟶ Y) ⊗ 𝐐 ⟶ CH_*(X) ⊗ 𝐐`,
`[ℱ] ↦ ch(X ⟶ Y, ℱ[0]) ∩ [Y]`, induces an isomorphism `K'₀(X) ⊗ 𝐐 ≅ CH_*(X) ⊗ 𝐐`; moreover the
canonical map `CH_k(X) ⊗ 𝐐 ⟶ gr_k K'₀(X) ⊗ 𝐐` is an isomorphism for every `k`.

Surjectivity and the "moreover" are conditions (1) and (2) of the source's proof
(`Stacks.Chow.surjective_liftBaseChange_coherentChowCharacter`,
`Stacks.Chow.bijective_rTensor_chowToGradedCoherentKZero_of_isClosedImmersion`); injectivity is
`Stacks.Chow.injective_liftBaseChange_coherentChowCharacter`. -/
@[stacks 0FEW "the whole proposition: the map K'_0(X) ⊗ Q → CH_*(X) ⊗ Q, [F] ↦ \
ch(X → Y, F[0]) ∩ [Y], is bijective, and CH_k(X) ⊗ Q → gr_k K'_0(X) ⊗ Q is bijective for \
every k, for a closed immersion X → Y of schemes locally of finite type over S with Y regular and \
quasi-compact, (S, δ) as in Situation 02QL"]
theorem bijective_liftBaseChange_coherentChowCharacter :
    haveI := isNoetherian_of_isClosedImmersion_of_compactSpace C a i
    Function.Bijective ((coherentChowCharacter C a i hY).toIntLinearMap.liftBaseChange ℚ) ∧
      ∀ k : ℤ, Function.Bijective (TensorProduct.map (LinearMap.id : ℚ →ₗ[ℤ] ℚ)
        (chowToGradedCoherentKZero C (i ≫ a) k).toIntLinearMap) :=
  ⟨⟨injective_liftBaseChange_coherentChowCharacter C a i hY,
      surjective_liftBaseChange_coherentChowCharacter C a i hY⟩,
    bijective_rTensor_chowToGradedCoherentKZero_of_isClosedImmersion C a i hY⟩

end Proposition

end Stacks.Chow

end
