module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveBundleCycleClassBridge
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveBundleTrace
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilChernData
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilChernPerfectPairing
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilDataCoordinates
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ClosedImmersionGysinPushforward

/-!
# Lemma 0FIN: the cycle class map commutes with pushforward along a projective bundle

Let (D0), (D1), (D2') satisfy axioms (A1)–(A7) (`Stacks.WeilCohomology.WeilChernData`), let `ℰ`
be finite locally free of rank `r + 1 ≥ 1` on a nonempty equidimensional smooth projective `X`
of dimension `d`, and `p : P = 𝐏(ℰ) ⟶ X`, as in axiom (A3). Stacks Lemma 0FIN: `γ` commutes with
pushforward along `p`, for the data `WeilChernData.toWeilData` of Section 0FHA.

## Proof

As in the source, everything rests on the trace map of `P`. Let `ξ = c₁^H(𝒪_P(1))` and
`λ_P(∑_i ξ^i ∪ p^*a_i) = ∫_X(a_r)` (`WeilChernData.bundleTraceTw`).

* **`γ` on `P`.** `CH^*(P) ⊗ 𝐐` is spanned by the classes `c₁(𝒪(1))^i · p^!y` (Stacks 02TX), and
  `p_*(c₁(𝒪(1))^i) = δ_{i,r}` (Stacks 02TW). The projection formula (Stacks 0FFA) and
  `γ(c₁(𝒪(1))) = ξ` then show that the coefficient of `ξ^r` in `γ(x)` is `γ(p_*x)`
  (`WeilChernData.bundleFormulaEquiv_symm_coeff_cycleClassSeries_last`).
* **`λ_P` is the trace of (A6).** The same holds for `1 × p : P × P ⟶ P × X`, a base change of
  `p` (`WeilChernData.prodBundleFormulaEquiv_symm_coeff_cycleClassSeries_last`). Applied to
  `[Δ_P]`, the top coefficient of `γ([Δ_P])` is `γ((1 × p)_*[Δ_P]) = γ([Γ_p]) = (p × 1)^*γ([Δ_X])`.
  So `(1 ⊗ λ_P)γ([Δ_P]) = p^*((1 ⊗ ∫_X)γ([Δ_X])) = p^*1 = 1`
  (`WeilChernData.traceContract_bundleTraceTw`). By the uniqueness of Remark 0FIK, `∫_P = λ_P`
  (`WeilChernData.toWeilData_trace_bundle`). The source cites the class of the diagonal of `P`
  (Lemma 0FGR) here; only its top coefficient `[Γ_p]` is needed, and that coefficient comes from
  02TX and 02TW for `P × P ⟶ P × X`.
* **The pushforward.** `p_*γ(α)` is characterised by `∫_X b ∪ p_*γ(α) = ∫_P p^*b ∪ γ(α)`
  (axiom (A), Lemma 0FIJ). With `∫_P = λ_P` and the first step, the right side is
  `∫_X(b ∪ γ(p_*α))`.

## Main results

* `Stacks.WeilCohomology.WeilChernData.toWeilData_trace_bundle`: `∫_P = λ_P`.
* `Stacks.WeilCohomology.WeilChernData.cycleClass_equidimensionalPushforward_bundleProj`:
  Lemma 0FIN.

## References

* [Stacks Project, Tag 0FIN](https://stacks.math.columbia.edu/tag/0FIN)
* [Stacks Project, Tag 0FIK](https://stacks.math.columbia.edu/tag/0FIK)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow
open scoped TensorProduct

universe u w

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme FirstChernClassData

namespace WeilChernData

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] (𝔚 : WeilChernData k F)
  (X : (SmoothProjectiveScheme k).FullSubcategory) (E : X.obj.left.Modules) (r : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)]

/-- `c₁^H(𝒪_P(1))` read in `A(P)`. -/
theorem coe_c₁A_bundleTwist :
    letI := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
    ((𝔚.c₁A (bundle X E r) (picardClassOf _ (Stacks.Chow.bundleTwist E)
      (Stacks.Chow.isInvertible_bundleTwist E)) : 𝔚.A (bundle X E r)) : 𝔚.H (bundle X E r)) =
      𝔚.bundleClassU X E r :=
  rfl

/-- **The top coefficient of `γ` on `P = 𝐏(ℰ)`**: for `x ∈ CH^*(P) ⊗ 𝐐`, the coefficient of
`ξ^r` in the projective bundle formula (A3) for the degree-`m` part of `γ(x)` is the
degree-`(m - r)` part of `γ(p_* x)`. -/
theorem bundleFormulaEquiv_symm_coeff_cycleClassSeries_last
    (x : smoothRationalChowRing (k := k) (bundle X E r).obj.hom) (m : ℕ) :
    (𝔚.bundleFormulaEquiv X E r 𝔚.projectiveBundle).symm
        ((PowerSeries.coeff m (𝔚.isCohomologicalChernCharacter.cycleClassSeries (bundle X E r) x) :
          𝔚.A (bundle X E r)) : 𝔚.H (bundle X E r)) (Fin.last r) =
      ((if r ≤ m then PowerSeries.coeff (m - r) (𝔚.isCohomologicalChernCharacter.cycleClassSeries X
          (rationalPush (bundleProj X E r) x)) else 0 : 𝔚.A X) : 𝔚.H X) := by
  let := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  set h := 𝔚.isCohomologicalChernCharacter
  have : SheafOfModules.IsInvertible (bundle X E r).obj.left.sheaf.obj
      (bundle X E r).obj.left.ringCatSheaf.property (Stacks.Chow.bundleTwist E) :=
    Stacks.Chow.isInvertible_bundleTwist E
  have hsq : IsPullback (bundleProj X E r).hom.left (𝟙 _) (𝟙 _) (Stacks.Chow.bundleProj E) :=
    IsPullback.of_id_snd
  have eL : Stacks.Chow.bundleTwist E ≅
      (Scheme.Modules.pullback (𝟙 _)).obj (Stacks.Chow.bundleTwist E) :=
    ((Scheme.Modules.pullbackId _).app _).symm
  refine eq_coeff_pushforward_of_sum_eq_coeff
    (smoothGysinRingHom (bundle X E r).obj.hom X.obj.hom (Over.w (bundleProj X E r).hom))
    (rationalPush (bundleProj X E r)).toAddMonoidHom
    (h.cycleClassSeries (bundle X E r)).toRingHom (h.cycleClassSeries X).toRingHom
    (𝔚.pullA (bundleProj X E r)).toRingHom
    (rationalFirstChernClass (bundle X E r) (Stacks.Chow.bundleTwist E))
    (𝔚.c₁A (bundle X E r) (picardClassOf _ (Stacks.Chow.bundleTwist E)
      (Stacks.Chow.isInvertible_bundleTwist E))) r
    (evenPart (𝔚.grade (bundle X E r))).val.toRingHom (evenPart (𝔚.grade X)).val.toRingHom
    (𝔚.pull (bundleProj X E r)).toRingHom (fun a => rfl)
    (fun x y => rationalPush_mul_smoothGysinRingHom _ x y)
    (rationalPush_rationalFirstChernClass_pow E r (bundleProj X E r) (𝟙 _) (𝟙 _) hsq _ eL)
    (exists_eq_sum_rationalFirstChernClass_pow_mul E r (bundleProj X E r) (𝟙 _) (𝟙 _) hsq _ eL)
    (fun y => h.cycleClassSeries_smoothGysinRingHom _ y)
    (h.cycleClassSeries_rationalFirstChernClass 𝔚.coproduct 𝔚.projectiveBundle _ _ _) ?_ x m _ ?_
  · intro a b hab
    apply (𝔚.bundleFormulaEquiv X E r 𝔚.projectiveBundle).injective
    rwa [bundleFormulaEquiv_apply, bundleFormulaEquiv_apply, bundleFormulaLin_apply,
      bundleFormulaLin_apply]
  · show ∑ i : Fin (r + 1), 𝔚.bundleClassU X E r ^ (i : ℕ) * 𝔚.pull (bundleProj X E r) _ = _
    rw [← bundleFormulaLin_apply, ← bundleFormulaEquiv_apply _ _ _ _ 𝔚.projectiveBundle,
      LinearEquiv.apply_symm_apply]
    rfl

/-- The class `ξ₂ = c₁^H(pr₂^*𝒪_P(1))` on `P × P` is `pr₂^*ξ`, by (A2). -/
theorem coe_c₁A_prod_bundleTwist :
    letI := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
    ((𝔚.c₁A (prod (bundle X E r) (bundle X E r)) (picardClassOf _
        ((Scheme.Modules.pullback (snd (bundle X E r) (bundle X E r)).hom.left).obj
          (Stacks.Chow.bundleTwist E))
        (isInvertible_pullback_obj _ _ (Stacks.Chow.isInvertible_bundleTwist E))) :
          𝔚.A (prod (bundle X E r) (bundle X E r))) : 𝔚.H (prod (bundle X E r) (bundle X E r))) =
      𝔚.pull (snd (bundle X E r) (bundle X E r)) (𝔚.bundleClassU X E r) := by
  let := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  rw [coe_c₁A, bundleClassU, ← κ_pullTw, bundleClass]
  exact congrArg (𝔚.κ _ 1) (𝔚.pullback (snd (bundle X E r) (bundle X E r))
    (Stacks.Chow.bundleTwist E) (Stacks.Chow.isInvertible_bundleTwist E)).symm

/-- **The top coefficient of `γ` on `P × P ⟶ P × X`**: for `x ∈ CH^*(P × P) ⊗ 𝐐`, the coefficient
of `pr₂^*ξ^r` of the degree-`m` part of `γ(x)` is the degree-`(m - r)` part of
`γ((1 × p)_* x)`. -/
theorem prodBundleFormulaEquiv_symm_coeff_cycleClassSeries_last
    (x : smoothRationalChowRing (k := k) (prod (bundle X E r) (bundle X E r)).obj.hom) (m : ℕ) :
    (𝔚.prodBundleFormulaEquiv X E r 𝔚.kunneth 𝔚.projectiveBundle).symm
        ((PowerSeries.coeff m (𝔚.isCohomologicalChernCharacter.cycleClassSeries
          (prod (bundle X E r) (bundle X E r)) x) : 𝔚.A (prod (bundle X E r) (bundle X E r))) :
          𝔚.H (prod (bundle X E r) (bundle X E r))) (Fin.last r) =
      ((if r ≤ m then PowerSeries.coeff (m - r) (𝔚.isCohomologicalChernCharacter.cycleClassSeries
          (prod (bundle X E r) X)
          (rationalPush (prodMap (𝟙 (bundle X E r)) (bundleProj X E r)) x)) else 0 :
          𝔚.A (prod (bundle X E r) X)) : 𝔚.H (prod (bundle X E r) X)) := by
  let := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  set h := 𝔚.isCohomologicalChernCharacter
  set L := (Scheme.Modules.pullback (snd (bundle X E r) (bundle X E r)).hom.left).obj
    (Stacks.Chow.bundleTwist E)
  have : SheafOfModules.IsInvertible (bundle X E r).obj.left.sheaf.obj
      (bundle X E r).obj.left.ringCatSheaf.property (Stacks.Chow.bundleTwist E) :=
    Stacks.Chow.isInvertible_bundleTwist E
  have : SheafOfModules.IsInvertible (prod (bundle X E r) (bundle X E r)).obj.left.sheaf.obj
      (prod (bundle X E r) (bundle X E r)).obj.left.ringCatSheaf.property L :=
    GenuineChern.isInvertible_pullback _ _
  refine eq_coeff_pushforward_of_sum_eq_coeff
    (smoothGysinRingHom (prod (bundle X E r) (bundle X E r)).obj.hom (prod (bundle X E r) X).obj.hom
      (Over.w (prodMap (𝟙 (bundle X E r)) (bundleProj X E r)).hom))
    (rationalPush (prodMap (𝟙 (bundle X E r)) (bundleProj X E r))).toAddMonoidHom
    (h.cycleClassSeries (prod (bundle X E r) (bundle X E r))).toRingHom
    (h.cycleClassSeries (prod (bundle X E r) X)).toRingHom
    (𝔚.pullA (prodMap (𝟙 (bundle X E r)) (bundleProj X E r))).toRingHom
    (rationalFirstChernClass (prod (bundle X E r) (bundle X E r)) L)
    (𝔚.c₁A (prod (bundle X E r) (bundle X E r)) (picardClassOf _ L
      (isInvertible_pullback_obj _ _ (Stacks.Chow.isInvertible_bundleTwist E)))) r
    (evenPart (𝔚.grade (prod (bundle X E r) (bundle X E r)))).val.toRingHom
    (evenPart (𝔚.grade (prod (bundle X E r) X))).val.toRingHom
    (𝔚.pull (prodMap (𝟙 (bundle X E r)) (bundleProj X E r))).toRingHom (fun a => rfl)
    (fun x y => rationalPush_mul_smoothGysinRingHom _ x y)
    (rationalPush_rationalFirstChernClass_pow E r _ _ _ (isPullback_prodMap_id_bundleProj X E r) L
      (Iso.refl _))
    (exists_eq_sum_rationalFirstChernClass_pow_mul E r _ _ _
      (isPullback_prodMap_id_bundleProj X E r) L (Iso.refl _))
    (fun y => h.cycleClassSeries_smoothGysinRingHom _ y)
    (h.cycleClassSeries_rationalFirstChernClass 𝔚.coproduct 𝔚.projectiveBundle _ _ _) ?_ x m _ ?_
  · intro a b hab
    apply (𝔚.prodBundleFormulaEquiv X E r 𝔚.kunneth 𝔚.projectiveBundle).injective
    rw [prodBundleFormulaEquiv_apply, prodBundleFormulaEquiv_apply]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Subalgebra.coe_val] at hab
    rwa [𝔚.coe_c₁A_prod_bundleTwist X E r] at hab
  · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Subalgebra.coe_val]
    rw [𝔚.coe_c₁A_prod_bundleTwist X E r, ← prodBundleFormulaEquiv_apply 𝔚.toFirstChernClassData
      X E r 𝔚.kunneth 𝔚.projectiveBundle, LinearEquiv.apply_symm_apply]

/-! ### The trace map of `P` -/

section Trace

variable {X E r} {d : ℕ} (hX : IsNonemptyEquidimensional X d)

/-- **The trace map `λ_P` of the proof of Lemma 0FIN**: `λ_P(∑ ξ^i ∪ p^*a_i) = ∫_X a_r`, on
`H^{2(d+r)}(P)(d+r)`. -/
def bundleTraceTw :
    tateTwist F 𝔚.tate (𝔚.grade (bundle X E r) (2 * ((d + r : ℕ) : ℤ))) (d + r : ℕ) →ₗ[F] F :=
  𝔚.bundleTrace X E r 𝔚.projectiveBundle (𝔚.untwistTrace X d (𝔚.toWeilData.trace X d hX)) ∘ₗ
    (𝔚.grade (bundle X E r) (2 * ((d + r : ℕ) : ℤ))).subtype ∘ₗ
    (tateTwistCoordinates 𝔚.coord ((d + r : ℕ) : ℤ)).toLinearMap

/-- Untwisting the trace `bundleTraceTw` on `H^{2(d+r)}(P)(d+r)` recovers `bundleTrace` built from
the untwisted trace of `X`. -/
theorem untwistTrace_bundleTraceTw :
    𝔚.untwistTrace (bundle X E r) (d + r) (𝔚.bundleTraceTw hX) =
      𝔚.bundleTrace X E r 𝔚.projectiveBundle (𝔚.untwistTrace X d (𝔚.toWeilData.trace X d hX)) := by
  classical
  ext a
  simp only [untwistTrace, bundleTraceTw, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, Submodule.coe_subtype, coe_projGrade]
  conv_rhs => rw [← DirectSum.sum_support_decompose (𝔚.grade (bundle X E r)) a, map_sum]
  by_cases hmem : (2 * ((d + r : ℕ) : ℤ)) ∈ (DirectSum.decompose (𝔚.grade (bundle X E r)) a).support
  · rw [Finset.sum_eq_single_of_mem _ hmem]
    intro j _ hj
    exact 𝔚.bundleTrace_eq_zero_of_mem X E r 𝔚.projectiveBundle _ (2 * (d : ℤ))
      (fun m hm b hb => 𝔚.untwistTrace_eq_zero X d _ m hm b hb) (by push_cast at hj ⊢; omega)
      (Submodule.coe_mem _)
  · rw [DFinsupp.notMem_support_iff.mp hmem, Finset.sum_eq_zero]
    · simp
    · intro j hj
      have hj' : j ≠ 2 * ((d + r : ℕ) : ℤ) := fun h => hmem (h ▸ hj)
      exact 𝔚.bundleTrace_eq_zero_of_mem X E r 𝔚.projectiveBundle _ (2 * (d : ℤ))
        (fun m hm b hb => 𝔚.untwistTrace_eq_zero X d _ m hm b hb) (by push_cast at hj' ⊢; omega)
        (Submodule.coe_mem _)

/-- **`λ_P` satisfies the normalisation of axiom (A6)**: `(1 ⊗ λ_P) γ([Δ_P]) = 1`. -/
theorem traceContract_bundleTraceTw :
    𝔚.traceContract 𝔚.kunneth (bundle X E r) (d + r) (𝔚.bundleTraceTw hX)
      (𝔚.γ (prod (bundle X E r) (bundle X E r)) (d + r) (diagonalClass (bundle X E r) (d + r))) =
      1 := by
  set h := 𝔚.isCohomologicalChernCharacter
  have hP := isNonemptyEquidimensional_bundle X E r hX
  rw [traceContract_eq, untwistTrace_bundleTraceTw]
  set x := smoothChowEquiv (prod (bundle X E r) (bundle X E r)).obj.hom
    (codimensionToRationalChow k _ ((d + r : ℕ) : ℤ) (diagonalClass (bundle X E r) (d + r)))
  set G := 𝔚.κ (prod (bundle X E r) (bundle X E r)) (d + r : ℕ)
    (𝔚.γ (prod (bundle X E r) (bundle X E r)) (d + r) (diagonalClass (bundle X E r) (d + r)))
  have hG : G = ((PowerSeries.coeff (d + r) (h.cycleClassSeries _ x) : 𝔚.A _) : 𝔚.H _) :=
    (h.coe_coeff_cycleClassSeries _ _ _).symm
  set Ψ := 𝔚.prodBundleFormulaEquiv X E r 𝔚.kunneth 𝔚.projectiveBundle
  have hw := 𝔚.prodBundleFormulaEquiv_symm_coeff_cycleClassSeries_last X E r x (d + r)
  rw [← hG, if_pos (Nat.le_add_left r d), Nat.add_sub_cancel] at hw
  show tensorContractRight _ ((𝔚.kunnethEquiv 𝔚.kunneth _ _).symm G) = 1
  rw [← Ψ.apply_symm_apply G, tensorContractRight_bundleTrace_prodBundleFormulaEquiv, hw]
  have hPP : IsNonemptyEquidimensional (prod (bundle X E r) (bundle X E r)) (2 * (d + r)) := by
    rw [two_mul]
    exact isNonemptyEquidimensional_prod hP hP
  have hPX : IsNonemptyEquidimensional (prod (bundle X E r) X) (d + r + d) :=
    isNonemptyEquidimensional_prod hP hX
  rw [← smoothChowEquiv_codimensionToRationalChow_equidimensionalPushforward _ hPP hPX
      ((d + r : ℕ) : ℤ) d (by push_cast; ring),
    equidimensionalPushforward_diagonalClass_bundle X E r hX, h.coe_coeff_cycleClassSeries,
    h.codimensionCycleClass_codimensionGysin, κ_pullTw,
    tensorContractRight_symm_pull_prodMap, pull_id, AlgHom.toLinearMap_id, LinearMap.comp_id]
  have h1 : tensorContractRight (𝔚.untwistTrace X d (𝔚.toWeilData.trace X d hX))
      ((𝔚.kunnethEquiv 𝔚.kunneth X X).symm
        (𝔚.κ (prod X X) d (𝔚.γ (prod X X) d (diagonalClass X d)))) = 1 :=
    h.traceContract_toWeilData_trace 𝔚.coproduct 𝔚.projectiveBundle 𝔚.kunneth 𝔚.trace X d hX
  rw [h1, map_one]

end Trace

/-! ### Lemma 0FIN -/

section Pushforward

omit [SheafOfModules.IsFiniteLocallyFreeOfRank E (r + 1)] in
/-- `λ` untwisted, on a class of degree `2D`. -/
theorem untwistTrace_coe (Z : (SmoothProjectiveScheme k).FullSubcategory) (D : ℕ)
    (lam : tateTwist F 𝔚.tate (𝔚.grade Z (2 * (D : ℤ))) D →ₗ[F] F) (z : 𝔚.grade Z (2 * (D : ℤ))) :
    𝔚.untwistTrace Z D lam (z : 𝔚.H Z) = lam ((tateTwistCoordinates 𝔚.coord (D : ℤ)).symm z) := by
  simp only [untwistTrace, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  congr 2
  exact Subtype.ext (by rw [coe_projGrade, DirectSum.decompose_of_mem_same _ z.2])

omit [SheafOfModules.IsFiniteLocallyFreeOfRank E (r + 1)] in
/-- The trace of `toWeilData` in coordinates is `λ` untwisted. -/
theorem traceCoord_toWeilData (Z : (SmoothProjectiveScheme k).FullSubcategory) (D : ℕ)
    (hZ : IsNonemptyEquidimensional Z D) (z : 𝔚.toWeilData.grade Z (2 * (D : ℤ))) :
    𝔚.toWeilData.traceCoord Z D hZ z =
      𝔚.untwistTrace Z D (𝔚.toWeilData.trace Z D hZ) (z : 𝔚.toWeilData.H Z) :=
  (𝔚.untwistTrace_coe Z D (𝔚.toWeilData.trace Z D hZ) z).symm

variable {X E r} {d : ℕ} (hX : IsNonemptyEquidimensional X d)

/-- **The trace map of `P` is `λ_P`** (Remark 0FIK): `∫_P(∑ ξ^i ∪ p^*a_i) = ∫_X a_r`. -/
theorem toWeilData_trace_bundle (hP : IsNonemptyEquidimensional (bundle X E r) (d + r)) :
    𝔚.toWeilData.trace (bundle X E r) (d + r) hP = 𝔚.bundleTraceTw (E := E) (r := r) hX := by
  set h := 𝔚.isCohomologicalChernCharacter
  refine 𝔚.trace_unique_of_key 𝔚.kunneth (bundle X E r) (d + r)
    (𝔚.γ (prod (bundle X E r) (bundle X E r)) (d + r) (diagonalClass (bundle X E r) (d + r)))
    ?_ (h.key_diagonalClass 𝔚.coproduct 𝔚.projectiveBundle 𝔚.divisor 𝔚.blowup _ _ hP) _ _
    (h.traceContract_toWeilData_trace 𝔚.coproduct 𝔚.projectiveBundle 𝔚.kunneth 𝔚.trace _ _ hP)
    (𝔚.traceContract_bundleTraceTw hX)
  exact h.κ_codimensionCycleClass_mem 𝔚.coproduct 𝔚.projectiveBundle _ _ _

/-- **Stacks Project, Lemma 0FIN.** Let (D0), (D1), (D2') satisfy axioms (A1)–(A7), let `ℰ` be
a finite locally free module of rank `r + 1 ≥ 1` on a nonempty equidimensional smooth projective
`X` over `k` and `p : P = 𝐏(ℰ) ⟶ X` its projective bundle, as in axiom (A3). Then `γ` commutes
with pushforward along `p`: for `P` and `X` of dimensions `e` and `d` and `α ∈ CH^i(P)`,
`γ(p_*α) = p_*γ(α)` in `H^{2j}(X)(j)`, `j = i + d - e`, where `p_*α` is proper pushforward of
cycles and `p_*γ(α)` the pushforward on cohomology of Section 0FHA, for the data
`WeilChernData.toWeilData` (`∫_X = λ` of (A6), `γ` of Tag 0FIF). This is clause (C)(b),
`WeilData.CycleClassPushforward`, for the morphism `p`. -/
@[stacks 0FIN "the whole lemma, under exactly (A1)-(A7) (WeilChernData): for p : P(E) -> X \
  with E of rank r + 1 >= 1 and X nonempty equidimensional, gamma(p_* alpha) = p_* gamma(alpha) \
  for every alpha in CH^i(P), with the pushforward of Section 0FHA for toWeilData; nothing \
  assumed"]
theorem cycleClass_equidimensionalPushforward_bundleProj {d e : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hP : IsNonemptyEquidimensional (bundle X E r) e)
    (i j : ℤ) (hij : j = i + d - e) (α : codimensionChowGroup k (bundle X E r).obj.hom i) :
    𝔚.toWeilData.cycleClass X j (equidimensionalPushforward (bundleProj X E r) e d i j hij α) =
      𝔚.toWeilData.pushforward 𝔚.perfectPairing (bundleProj X E r) hP hX (2 * i) i
        (2 * j) j (by omega) (by omega) (𝔚.toWeilData.cycleClass (bundle X E r) i α) := by
  have hP' := isNonemptyEquidimensional_bundle X E r hX
  have := hP.nonempty
  obtain rfl : e = d + r :=
    AlgebraicGeometry.RelativeDimension.eq_of_nonempty hP.relativeDimension hP'.relativeDimension
  set W := 𝔚.toWeilData
  set h := 𝔚.isCohomologicalChernCharacter
  refine W.eq_of_pairingTw_eq 𝔚.perfectPairing hX (2 * ((d + r : ℕ) : ℤ) - 2 * i) (2 * j)
    (by omega) (((d + r : ℕ) : ℤ) - i) j (by omega) fun c => ?_
  rw [← W.pushforward_trace' 𝔚.perfectPairing (bundleProj X E r) hP hX (2 * i) i (2 * j) j
      (by omega) (by omega) _ _ (by omega) (by omega) (by omega) (by omega) c,
    W.pairingTw_eq_traceCoord, W.pairingTw_eq_traceCoord, traceCoord_toWeilData,
    traceCoord_toWeilData, 𝔚.toWeilData_trace_bundle hX hP, untwistTrace_bundleTraceTw]
  simp only [WeilData.coe_cup]
  rw [WeilData.twCoord_pullTw, WeilData.coe_pullDeg]
  have hcl : ∀ (Y : (SmoothProjectiveScheme k).FullSubcategory) (n : ℕ)
      (β : codimensionChowGroup k Y.obj.hom n),
      ((W.twCoord Y (2 * (n : ℤ)) n (W.cycleClass Y n β) : W.grade Y _) : W.H Y) =
        𝔚.κ Y n (𝔚.γ Y n β) := fun Y n β =>
    h.coe_twCoord_toWeilData_cycleClass 𝔚.coproduct 𝔚.projectiveBundle 𝔚.kunneth 𝔚.trace Y n β
  by_cases hi : 0 ≤ i
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    rw [hcl, ← h.coe_coeff_cycleClassSeries]
    set x := smoothChowEquiv (bundle X E r).obj.hom
      (codimensionToRationalChow k (bundle X E r).obj.hom (m : ℤ) α)
    set y := ((PowerSeries.coeff m (h.cycleClassSeries (bundle X E r) x) : 𝔚.A (bundle X E r)) :
      𝔚.H (bundle X E r))
    have hy : y = 𝔚.bundleFormulaLin X E r
        ((𝔚.bundleFormulaEquiv X E r 𝔚.projectiveBundle).symm y) := by
      rw [← bundleFormulaEquiv_apply _ _ _ _ 𝔚.projectiveBundle, LinearEquiv.apply_symm_apply]
    show _ = 𝔚.bundleTrace X E r 𝔚.projectiveBundle _
      (𝔚.pull (bundleProj X E r) ((W.twCoord X _ _ c : W.grade X _) : W.H X) * y)
    rw [hy]
    refine Eq.trans ?_ (bundleTrace_pull_mul 𝔚.toFirstChernClassData X E r 𝔚.projectiveBundle
      _ _ _).symm
    refine congrArg (fun z : 𝔚.H X => 𝔚.untwistTrace X d (𝔚.toWeilData.trace X d hX)
      ((show 𝔚.H X from ((W.twCoord X _ _ c : W.grade X _) : W.H X)) * z)) ?_
    rw [𝔚.bundleFormulaEquiv_symm_coeff_cycleClassSeries_last]
    split_ifs with hrm
    · obtain rfl : j = ((m - r : ℕ) : ℤ) := by omega
      rw [hcl, ← h.coe_coeff_cycleClassSeries,
        smoothChowEquiv_codimensionToRationalChow_equidimensionalPushforward _ hP hX]
    · obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero (show j < 0 by omega)
      rw [show ∀ β, W.cycleClass X (Int.negSucc n) β = 0 from fun _ => rfl]
      simp only [map_zero, ZeroMemClass.coe_zero]
      rfl
  · obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero (show i < 0 by omega)
    obtain ⟨n', rfl⟩ := Int.eq_negSucc_of_lt_zero (show j < 0 by omega)
    rw [show ∀ β, W.cycleClass X (Int.negSucc n') β = 0 from fun _ => rfl,
      show W.cycleClass (bundle X E r) (Int.negSucc n) α = 0 from rfl]
    simp only [map_zero, ZeroMemClass.coe_zero, mul_zero]
    exact (map_zero _).trans (map_zero _).symm

end Pushforward

end WeilChernData

end Stacks.WeilCohomology

end
