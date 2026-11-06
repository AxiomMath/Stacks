module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.BaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.RankZero
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveBundleBlocks
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The projective space bundle formula for Chow motives

Let `k` be a field, `X` a smooth projective scheme over `k`, `ℰ` a finite locally free
`𝒪_X`-module of rank `r` and `p : P = 𝐏(ℰ) ⟶ X` its projective bundle. Stacks 0FGQ: the map

  `∑_{i < r} c_i : ⨁_{i < r} h(X)(-i) ⟶ h(P)`,   `c_i = c₁(pr₂^*𝒪_P(1))^i ∩ [Γ_p]`,

is an isomorphism in the category `M_k` of Chow motives.

## Proof

The source deduces this from Manin's identity principle and the projective space bundle formula
for Chow groups (Stacks 02TX). Here the identity principle is replaced by the Yoneda lemma at the
two objects that matter: a morphism `c : M ⟶ N` with `M = ⨁ h(X)(-i)` is an isomorphism as soon as
`- ≫ c` is bijective on morphisms out of `N = h(P)` and out of each `h(X)(-j)`. For a motive
`T = h(Z)(m)` the map `(u_i) ↦ ∑_i c_i ∘ u_i` is, block by block on the decompositions of `Z`, `X`
and `P` into their parts of constant dimension,

  `(u_i) ↦ ∑_i c₁(pr₂^*𝒪(1))^i ∩ (1 × p_d)^* u_i`,  `CH_*(Z_f × X_d)^{⊕ r} ⟶ CH_*(Z_f × P_{d+r-1})`

(`Stacks.WeilCohomology.composition_blockTwistCap_graphBlock`), and `Z_f × P_{d+r-1} ⟶ Z_f × X_d`
is the projective bundle of the pullback of `ℰ` (Stacks 01O3), so this is the map of Stacks 02TX,
bijective by `Stacks.Chow.bijective_bundleMap_of_isPullback`; the parts `P_e` with `e < r - 1` are
empty.

## Main results

* `Stacks.WeilCohomology.isIso_projectiveBundleFormula`: **Stacks 0FGQ**, for a module of any
  rank `r`.
* `Stacks.WeilCohomology.isIso_projectiveBundleMotiveMap`: the same for rank `n + 1`.
* `Stacks.WeilCohomology.bijective_sum_comp_projectiveBundleFinHom`: for every motive `h(Z)(m)`,
  `(u_i) ↦ ∑_i c_i ∘ u_i` is a bijection onto the morphisms `h(Z)(m) ⟶ h(P)`.
* `Stacks.WeilCohomology.bijective_projectiveBundleCompSum`: the same on correspondences.
* `Stacks.WeilCohomology.bijective_projectiveBundleBlockSum`: Stacks 02TX on the blocks
  `Z_f × P_{d+n} ⟶ Z_f × X_d`, with rational coefficients.
* `Stacks.WeilCohomology.isPullback_projectiveBundleBlock`: `Z_f × P_{d+n}` is the base change of
  `P ⟶ X` along `Z_f × X_d ⟶ X`.
* `Stacks.WeilCohomology.isIso_biproduct_desc_of_bijective`: the Yoneda criterion used in place of
  Manin's identity principle.
* `Stacks.WeilCohomology.isZero_twistedMotive_of_isEmpty`: the motive of the empty scheme is zero,
  which is the case `r = 0`.

## References

* [Stacks Project, Tag 0FGQ](https://stacks.math.columbia.edu/tag/0FGQ)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

/-- If an open subscheme `V` of `P` is the preimage of an open subscheme `U` of `X` under
`p : P ⟶ X`, then `V` is the base change of `U` along `p`. -/
theorem isPullback_of_eq_preimage {X P : Scheme.{u}} (p : P ⟶ X) (U : X.Opens) (V : P.Opens)
    (hV : V = p ⁻¹ᵁ U) (φ : V.toScheme ⟶ U.toScheme) (hφ : φ ≫ U.ι = V.ι ≫ p) :
    IsPullback φ V.ι U.ι p := by
  subst hV
  have : φ = p ∣_ U := by rw [← cancel_mono U.ι, hφ, morphismRestrict_ι]
  subst this
  exact isPullback_morphismRestrict p U

/-- **Bijectivity passes to rational coefficients.** If `(α_i) ↦ ∑_i T_i α_i` is bijective for
`ℤ`-linear maps `T_i : M_i ⟶ N` indexed by a finite type, so is
`(x_i) ↦ ∑_i (ℚ ⊗ T_i)(x_i)`. -/
theorem bijective_sum_baseChange {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] {N : Type*} [AddCommGroup N] (T : ∀ i, M i →ₗ[ℤ] N)
    (hT : Function.Bijective fun α : (∀ i, M i) ↦ ∑ i, T i (α i)) :
    Function.Bijective fun x : (∀ i, TensorProduct ℤ ℚ (M i)) ↦ ∑ i, (T i).baseChange ℚ (x i) := by
  set Tsum : (∀ i, M i) →ₗ[ℤ] N := ∑ i, (T i).comp (LinearMap.proj i) with hTsum
  have hTsum' : ∀ α, Tsum α = ∑ i, T i (α i) := fun α ↦ by simp [Tsum]
  have hbij : Function.Bijective Tsum := by
    have : ⇑Tsum = fun α : (∀ i, M i) ↦ ∑ i, T i (α i) := funext hTsum'
    rw [this]; exact hT
  set e := LinearEquiv.ofBijective Tsum hbij
  have hbc : Function.Bijective (Tsum.baseChange ℚ) := by
    have : ⇑(Tsum.baseChange ℚ) = ⇑(e.baseChange ℤ ℚ _ _) := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => rw [map_add, map_add, ha, hb]
      | tmul q m => rfl
    rw [this]
    exact (e.baseChange ℤ ℚ _ _).bijective
  have key : ∀ x : (∀ i, TensorProduct ℤ ℚ (M i)),
      ∑ i, (T i).baseChange ℚ (x i) =
        Tsum.baseChange ℚ ((TensorProduct.piRight ℤ ℚ ℚ M).symm x) := by
    have hlin : (∑ i, ((T i).baseChange ℚ).comp (LinearMap.proj i) :
        (∀ i, TensorProduct ℤ ℚ (M i)) →ₗ[ℚ] TensorProduct ℤ ℚ N) =
        (Tsum.baseChange ℚ).comp (TensorProduct.piRight ℤ ℚ ℚ M).symm.toLinearMap := by
      refine LinearMap.pi_ext fun i x ↦ ?_
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => rw [Pi.single_add, map_add, map_add, ha, hb]
      | tmul q m =>
        rw [LinearMap.sum_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
          TensorProduct.piRight_symm_single, LinearMap.baseChange_tmul, hTsum',
          Finset.sum_eq_single i (fun j _ hj ↦ by
            rw [LinearMap.comp_apply, LinearMap.proj_apply, Pi.single_eq_of_ne hj, map_zero])
            (by simp),
          LinearMap.comp_apply, LinearMap.proj_apply, Pi.single_eq_same, LinearMap.baseChange_tmul,
          Finset.sum_eq_single i (fun j _ hj ↦ by rw [Pi.single_eq_of_ne hj, map_zero]) (by simp),
          Pi.single_eq_same]
    intro x
    have := congrArg (fun F ↦ F x) hlin
    simpa [LinearMap.sum_apply] using this
  have hfun : (fun x : (∀ i, TensorProduct ℤ ℚ (M i)) ↦ ∑ i, (T i).baseChange ℚ (x i)) =
      ⇑(Tsum.baseChange ℚ) ∘ ⇑(TensorProduct.piRight ℤ ℚ ℚ M).symm :=
    funext key
  rw [hfun]
  exact hbc.comp (TensorProduct.piRight ℤ ℚ ℚ M).symm.bijective

section Block

variable {k : Type u} [Field k] (X : (SmoothProjectiveScheme k).FullSubcategory)
  (E : X.obj.left.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]
  (Z : (SmoothProjectiveScheme k).FullSubcategory)

local notation "𝒞" => fieldChowSituation k

/-- `P_{d+n}` is the base change of `X_d ⊆ X` along `p : P ⟶ X`. -/
theorem isPullback_projectiveBundlePartProj (d : ℕ) :
    IsPullback (projectiveBundlePartProj X E n d)
      (dimPart (projectiveBundle X E n).obj.hom (d + n)).ι (dimPart X.obj.hom d).ι
      (SmoothProjectiveScheme.bundleProj X E n).hom.left :=
  isPullback_of_eq_preimage _ _ _ (dimPart_projectiveBundle X E n d) _
    (projectiveBundlePartProj_ι X E n d)

/-- **`Z_f × P_{d+n}` is the base change of the projective bundle `P ⟶ X` along
`Z_f × X_d ⟶ X_d ⊆ X`.** -/
theorem isPullback_projectiveBundleBlock (f d : ℕ) :
    IsPullback (prodMapRight (partBase Z.obj.hom f) (partBase X.obj.hom d)
        (partBase (projectiveBundle X E n).obj.hom (d + n)) (projectiveBundlePartProj X E n d)
        (projectiveBundlePartProj_partBase X E n d))
      (pullback.snd (partBase Z.obj.hom f) (partBase (projectiveBundle X E n).obj.hom (d + n)) ≫
        (dimPart (projectiveBundle X E n).obj.hom (d + n)).ι)
      (pullback.snd (partBase Z.obj.hom f) (partBase X.obj.hom d) ≫ (dimPart X.obj.hom d).ι)
      (SmoothProjectiveScheme.bundleProj X E n).hom.left :=
  (isPullback_prodMapRight _ _ _ _ _).paste_vert (isPullback_projectiveBundlePartProj X E n d)

/-- **Stacks 02TX on a block**: for `Z_f × P_{d+n} ⟶ Z_f × X_d`, the map
`(α_i) ↦ ∑_i c₁(pr₂^*𝒪(1))^i ∩ (1 × p_d)^* α_i` is bijective. -/
theorem bijective_bundleMap_projectiveBundleBlock (f d : ℕ) (k' : ℤ) :
    Function.Bijective (bundleMap 𝒞 (prodBase (partBase Z.obj.hom f) (partBase X.obj.hom d))
      (prodBase (partBase Z.obj.hom f) (partBase (projectiveBundle X E n).obj.hom (d + n)))
      (prodMapRight (partBase Z.obj.hom f) (partBase X.obj.hom d)
        (partBase (projectiveBundle X E n).obj.hom (d + n)) (projectiveBundlePartProj X E n d)
        (projectiveBundlePartProj_partBase X E n d))
      (prodMapRight_comp_prodBase _ _ _ _ _) n
      (relativeDimension_prodMapRight _ _ _ _ _
        (relativeDimension_projectiveBundlePartProj X E n d))
      (invCap 𝒞 _ (partTwist X E n (Z := Z) f d)) k') := by
  let := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (n + 1)
  exact bijective_bundleMap_of_isPullback 𝒞 E n _ _ _ _ _ _ _
    (isPullback_projectiveBundleBlock X E n Z f d) (partTwist X E n (Z := Z) f d)
    ((Scheme.Modules.pullbackComp _ _).app _) k'

/-- **Stacks 02TX on a block, with rational coefficients and in the degrees of the
correspondences**: for degrees `r_i` with `r_i + i = s`,
`(x_i) ↦ ∑_i c₁(pr₂^*𝒪(1))^i ∩ (1 × p_d)^* x_i`,
`⨁_i Corr^{r_i}(Z_f, X_d) ⟶ Corr^s(Z_f, P_{d+n})`, is bijective. -/
theorem bijective_projectiveBundleBlockSum (f d : ℕ) (r : Fin (n + 1) → ℤ) (s : ℤ)
    (hrs : ∀ i : Fin (n + 1), r i + (i : ℕ) = s) :
    Function.Bijective fun x : (∀ i : Fin (n + 1),
        Correspondence 𝒞 (partBase Z.obj.hom f) (partBase X.obj.hom d) d (r i)) ↦
      ∑ i, correspondenceCongr k (partBase Z.obj.hom f)
        (partBase (projectiveBundle X E n).obj.hom (d + n)) (hrs i)
        (projectiveBundleBlockMap X E n f d i (r i) (x i)) := by
  set U := prodBase (partBase Z.obj.hom f) (partBase X.obj.hom d)
  set Q := prodBase (partBase Z.obj.hom f) (partBase (projectiveBundle X E n).obj.hom (d + n))
  set q := prodMapRight (partBase Z.obj.hom f) (partBase X.obj.hom d)
    (partBase (projectiveBundle X E n).obj.hom (d + n)) (projectiveBundlePartProj X E n d)
    (projectiveBundlePartProj_partBase X E n d)
  have hq : q ≫ U = Q := prodMapRight_comp_prodBase _ _ _ _ _
  have hqn := relativeDimension_prodMapRight (partBase Z.obj.hom f) (partBase X.obj.hom d)
    (partBase (projectiveBundle X E n).obj.hom (d + n)) _
    (projectiveBundlePartProj_partBase X E n d)
    (relativeDimension_projectiveBundlePartProj X E n d)
  set ξ := invCap 𝒞 Q (partTwist X E n (Z := Z) f d)
  -- the integral maps
  let T : ∀ i : Fin (n + 1), chowGroup 𝒞 U ((d : ℤ) - r i) →ₗ[ℤ]
      chowGroup 𝒞 Q (((d + n : ℕ) : ℤ) - s) := fun i ↦
    ((chowGroupDegreeEquiv 𝒞 Q (by rw [← hrs i])).toAddMonoidHom.comp
      ((capPow 𝒞 Q ξ i ((d : ℤ) - r i + n) (((d + n : ℕ) : ℤ) - (r i + i))
        (by push_cast; omega)).comp
        (flatPullbackChowOfRelativeDimension 𝒞 Q U q hq n hqn ((d : ℤ) - r i)))).toIntLinearMap
  have hTbc : ∀ i (x : Correspondence 𝒞 (partBase Z.obj.hom f) (partBase X.obj.hom d) d (r i)),
      correspondenceCongr k (partBase Z.obj.hom f)
        (partBase (projectiveBundle X E n).obj.hom (d + n)) (hrs i)
        (projectiveBundleBlockMap X E n f d i (r i) x) = (T i).baseChange ℚ x := by
    intro i x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
    | tmul q' y => rfl
  have hfun : (fun x : (∀ i : Fin (n + 1),
        Correspondence 𝒞 (partBase Z.obj.hom f) (partBase X.obj.hom d) d (r i)) ↦
      ∑ i, correspondenceCongr k (partBase Z.obj.hom f)
        (partBase (projectiveBundle X E n).obj.hom (d + n)) (hrs i)
        (projectiveBundleBlockMap X E n f d i (r i) (x i))) =
      fun x ↦ ∑ i, (T i).baseChange ℚ (x i) :=
    funext fun x ↦ Finset.sum_congr rfl fun i _ ↦ hTbc i (x i)
  rw [hfun]
  refine bijective_sum_baseChange T ?_
  -- the integral statement is Stacks 02TX on the block, up to degrees
  have h02TX := bijective_bundleMap_projectiveBundleBlock X E n Z f d ((d : ℤ) - s)
  have hdeg : ∀ i : Fin (n + 1), (d : ℤ) - r i = (d : ℤ) - s + (i : ℕ) := fun i ↦ by
    have := hrs i; omega
  have hfun' : (fun α : (∀ i : Fin (n + 1), chowGroup 𝒞 U ((d : ℤ) - r i)) ↦ ∑ i, T i (α i)) =
      ⇑(chowGroupDegreeEquiv 𝒞 Q (by push_cast; ring :
          (d : ℤ) - s + n = ((d + n : ℕ) : ℤ) - s)) ∘
        ⇑(bundleMap 𝒞 U Q q hq n hqn ξ ((d : ℤ) - s)) ∘
        (fun α i ↦ chowGroupDegreeEquiv 𝒞 U (hdeg i) (α i)) := by
    funext α
    simp only [Function.comp_apply, bundleMap_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ eq_of_heq ?_
    refine (chowGroupDegreeEquiv_heq _ _ _ _).trans (HEq.trans ?_
      (chowGroupDegreeEquiv_heq _ _ _ _).symm)
    simp only [bundleTerm, AddMonoidHom.coe_comp, Function.comp_apply]
    refine capPow_heq_of_heq 𝒞 Q ξ i _ _ (by rw [hdeg i]) (by have := hrs i; push_cast; omega) ?_
    exact flatPullbackChowOfRelativeDimension_heq 𝒞 Q U q hq n hqn (hdeg i)
      (chowGroupDegreeEquiv_heq _ _ _ _).symm
  rw [hfun']
  refine (chowGroupDegreeEquiv 𝒞 Q _).bijective.comp (h02TX.comp ?_)
  exact ⟨fun α β h ↦ funext fun i ↦ (chowGroupDegreeEquiv 𝒞 U (hdeg i)).injective
      (congrFun h i),
    fun β ↦ ⟨fun i ↦ (chowGroupDegreeEquiv 𝒞 U (hdeg i)).symm (β i), funext fun i ↦ by simp⟩⟩

end Block

section CorrComposition

variable {k : Type u} [Field k] (X : (SmoothProjectiveScheme k).FullSubcategory)
  (E : X.obj.left.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]
  (Z : (SmoothProjectiveScheme k).FullSubcategory)

/-- **Composition of a block with `c_i`**: for `x ∈ Corrʳ(Z_f, X_d)`,
`c_i ∘ x = c₁(pr₂^*𝒪(1))^i ∩ (1 × p_d)^* x`, in the block `(f, d + n)`. -/
theorem comp_lof_lof_projectiveBundleCorr (i : ℕ) (r : ℤ) (f d : ℕ)
    (x : Correspondence (fieldChowSituation k) (partBase Z.obj.hom f) (partBase X.obj.hom d) d r) :
    comp k Z.obj.hom X.obj.hom (projectiveBundle X E n).obj.hom (canonicalDiagonalClassFamily k)
        r i (DirectSum.lof ℚ ℕ _ f (DirectSum.lof ℚ ℕ _ d x))
        (SmoothProjectiveCorr.toCorr X (projectiveBundle X E n) (i : ℤ)
          (projectiveBundleCorr X E n i rfl)) =
      DirectSum.lof ℚ ℕ _ f (DirectSum.lof ℚ ℕ _ (d + n)
        (projectiveBundleBlockMap X E n f d i r x)) := by
  rw [comp_lof_lof_of_apply_eq_lof (Δ := canonicalDiagonalClassFamily k) (sX := Z.obj.hom)
    (sY := X.obj.hom) (sZ := (projectiveBundle X E n).obj.hom)
    (y := blockTwistCap k X.obj.hom (projectiveBundle X E n).obj.hom
      (projectiveBundleTwist X E n) i d (d + n) (by omega : (i : ℤ) = 0 + i)
      (graphBlock k X.obj.hom (projectiveBundle X E n).obj.hom
        (SmoothProjectiveScheme.bundleProj X E n).hom.left
        (Over.w (SmoothProjectiveScheme.bundleProj X E n).hom) d (d + n)))
    (hy := projectiveBundleCorr_apply X E n i d),
    composition_blockTwistCap_graphBlock]

/-- **The blocks of `c_i ∘ u`**: the block `(f, d + n)` of `c_i ∘ u` is
`c₁(pr₂^*𝒪(1))^i ∩ (1 × p_d)^* u_{f,d}`. -/
theorem comp_projectiveBundleCorr_apply_apply (i : ℕ) (r : ℤ) (u : Corr k Z.obj.hom X.obj.hom r)
    (f d : ℕ) :
    comp k Z.obj.hom X.obj.hom (projectiveBundle X E n).obj.hom (canonicalDiagonalClassFamily k)
        r i u (SmoothProjectiveCorr.toCorr X (projectiveBundle X E n) (i : ℤ)
          (projectiveBundleCorr X E n i rfl)) f (d + n) =
      projectiveBundleBlockMap X E n f d i r (u f d) := by
  have key : (DirectSum.component ℚ ℕ _ (d + n)) ∘ₗ (DirectSum.component ℚ ℕ _ f) ∘ₗ
      (comp k Z.obj.hom X.obj.hom (projectiveBundle X E n).obj.hom
        (canonicalDiagonalClassFamily k) r i).flip
        (SmoothProjectiveCorr.toCorr X (projectiveBundle X E n) (i : ℤ)
          (projectiveBundleCorr X E n i rfl)) =
      (projectiveBundleBlockMap X E n f d i r) ∘ₗ (DirectSum.component ℚ ℕ _ d) ∘ₗ
        (DirectSum.component ℚ ℕ _ f) := by
    refine DirectSum.linearMap_ext ℚ fun f' ↦ DirectSum.linearMap_ext ℚ fun d' ↦
      LinearMap.ext fun z ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.flip_apply]
    rw [comp_lof_lof_projectiveBundleCorr]
    by_cases hf : f' = f
    · subst hf
      simp only [DirectSum.component.lof_self]
      by_cases hd : d' = d
      · subst hd
        simp only [DirectSum.component.lof_self]
      · simp only [← DirectSum.apply_eq_component, DirectSum.lof_eq_of]
        rw [DirectSum.of_eq_of_ne _ _ _ (by omega), DirectSum.of_eq_of_ne _ _ _ (Ne.symm hd),
          map_zero]
    · simp only [← DirectSum.apply_eq_component, DirectSum.lof_eq_of]
      rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hf), DirectSum.of_eq_of_ne _ _ _ (Ne.symm hf),
        DirectSum.zero_apply, DirectSum.zero_apply, map_zero]
  exact LinearMap.congr_fun key u

/-- The map `(u_i) ↦ ∑_i c_i ∘ u_i`, `⨁_i Corr^{r_i}(Z, X) ⟶ Corr^s(Z, P)` for `r_i + i = s`. -/
def projectiveBundleCompSum (r : Fin (n + 1) → ℤ) (s : ℤ)
    (hrs : ∀ i : Fin (n + 1), r i + (i : ℕ) = s) :
    (∀ i : Fin (n + 1), Corr k Z.obj.hom X.obj.hom (r i)) →ₗ[ℚ]
      Corr k Z.obj.hom (projectiveBundle X E n).obj.hom s :=
  ∑ i, (corrCongr k Z.obj.hom (projectiveBundle X E n).obj.hom (hrs i)).toLinearMap ∘ₗ
    (comp k Z.obj.hom X.obj.hom (projectiveBundle X E n).obj.hom (canonicalDiagonalClassFamily k)
      (r i) i).flip (SmoothProjectiveCorr.toCorr X (projectiveBundle X E n) (i : ℤ)
        (projectiveBundleCorr X E n i rfl)) ∘ₗ LinearMap.proj i

/-- `projectiveBundleCompSum` sends `(u_i)` to `∑_i c_i ∘ u_i`, each term read in degree `s`. -/
theorem projectiveBundleCompSum_apply (r : Fin (n + 1) → ℤ) (s : ℤ)
    (hrs : ∀ i : Fin (n + 1), r i + (i : ℕ) = s)
    (u : ∀ i : Fin (n + 1), Corr k Z.obj.hom X.obj.hom (r i)) :
    projectiveBundleCompSum X E n Z r s hrs u =
      ∑ i, corrCongr k Z.obj.hom (projectiveBundle X E n).obj.hom (hrs i)
        (comp k Z.obj.hom X.obj.hom (projectiveBundle X E n).obj.hom
          (canonicalDiagonalClassFamily k) (r i) i (u i)
          (SmoothProjectiveCorr.toCorr X (projectiveBundle X E n) (i : ℤ)
            (projectiveBundleCorr X E n i rfl))) := by
  rw [projectiveBundleCompSum, LinearMap.sum_apply]
  rfl

/-- The block `(f, d + n)` of `∑_i c_i ∘ u_i` is `∑_i c₁(pr₂^*𝒪(1))^i ∩ (1 × p_d)^* (u_i)_{f,d}`,
each term read in degree `s`. -/
theorem projectiveBundleCompSum_apply_apply (r : Fin (n + 1) → ℤ) (s : ℤ)
    (hrs : ∀ i : Fin (n + 1), r i + (i : ℕ) = s)
    (u : ∀ i : Fin (n + 1), Corr k Z.obj.hom X.obj.hom (r i))
    (f d : ℕ) :
    projectiveBundleCompSum X E n Z r s hrs u f (d + n) =
      ∑ i, correspondenceCongr k (partBase Z.obj.hom f)
        (partBase (projectiveBundle X E n).obj.hom (d + n)) (hrs i)
        (projectiveBundleBlockMap X E n f d i (r i) (u i f d)) := by
  rw [projectiveBundleCompSum_apply, DirectSum.sum_apply, DirectSum.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← comp_projectiveBundleCorr_apply_apply]
  rfl

/-- For `u_i = w_i` supported on the single block `(f, d)`, the block `(f, d + n)` of
`∑_i c_i ∘ u_i` is `∑_i c₁(pr₂^*𝒪(1))^i ∩ (1 × p_d)^* w_i`. -/
theorem projectiveBundleCompSum_of_of_apply_self (r : Fin (n + 1) → ℤ) (s : ℤ)
    (hrs : ∀ i : Fin (n + 1), r i + (i : ℕ) = s) (f d : ℕ)
    (w : ∀ i : Fin (n + 1),
      Correspondence (fieldChowSituation k) (partBase Z.obj.hom f) (partBase X.obj.hom d) d (r i)) :
    projectiveBundleCompSum X E n Z r s hrs (fun i ↦ DirectSum.of (fun f' ↦ DirectSum ℕ fun d' ↦
        Correspondence (fieldChowSituation k) (partBase Z.obj.hom f') (partBase X.obj.hom d') d'
          (r i)) f
        (DirectSum.of (fun d' ↦ Correspondence (fieldChowSituation k) (partBase Z.obj.hom f)
          (partBase X.obj.hom d') d' (r i)) d (w i))) f (d + n) =
      ∑ i, correspondenceCongr k (partBase Z.obj.hom f)
        (partBase (projectiveBundle X E n).obj.hom (d + n)) (hrs i)
        (projectiveBundleBlockMap X E n f d i (r i) (w i)) := by
  rw [projectiveBundleCompSum_apply_apply]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [DirectSum.of_eq_same, DirectSum.of_eq_same]

/-- For `u_i` supported on the single block `(f, d)`, the block `(f, d'' + n)` of `∑_i c_i ∘ u_i`
vanishes when `d ≠ d''`. -/
theorem projectiveBundleCompSum_of_of_apply_of_ne_right (r : Fin (n + 1) → ℤ) (s : ℤ)
    (hrs : ∀ i : Fin (n + 1), r i + (i : ℕ) = s) (f d : ℕ)
    (w : ∀ i : Fin (n + 1),
      Correspondence (fieldChowSituation k) (partBase Z.obj.hom f) (partBase X.obj.hom d) d (r i))
    {d'' : ℕ} (hd : d ≠ d'') :
    projectiveBundleCompSum X E n Z r s hrs (fun i ↦ DirectSum.of (fun f' ↦ DirectSum ℕ fun d' ↦
        Correspondence (fieldChowSituation k) (partBase Z.obj.hom f') (partBase X.obj.hom d') d'
          (r i)) f
        (DirectSum.of (fun d' ↦ Correspondence (fieldChowSituation k) (partBase Z.obj.hom f)
          (partBase X.obj.hom d') d' (r i)) d (w i))) f (d'' + n) = 0 := by
  rw [projectiveBundleCompSum_apply_apply]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  conv_lhs => rw [DirectSum.of_eq_same, DirectSum.of_eq_of_ne _ _ _ (Ne.symm hd)]
  exact (congrArg _ (LinearMap.map_zero (projectiveBundleBlockMap X E n f d'' i (r i)))).trans
    (LinearEquiv.map_zero _)

/-- For `u_i` supported on the single block `(f, d)`, the block `(f'', d'' + n)` of `∑_i c_i ∘ u_i`
vanishes when `f ≠ f''`. -/
theorem projectiveBundleCompSum_of_of_apply_of_ne_left (r : Fin (n + 1) → ℤ) (s : ℤ)
    (hrs : ∀ i : Fin (n + 1), r i + (i : ℕ) = s) (f d : ℕ)
    (w : ∀ i : Fin (n + 1),
      Correspondence (fieldChowSituation k) (partBase Z.obj.hom f) (partBase X.obj.hom d) d (r i))
    {f'' : ℕ} (hf : f ≠ f'')
    (d'' : ℕ) :
    projectiveBundleCompSum X E n Z r s hrs (fun i ↦ DirectSum.of (fun f' ↦ DirectSum ℕ fun d' ↦
        Correspondence (fieldChowSituation k) (partBase Z.obj.hom f') (partBase X.obj.hom d') d'
          (r i)) f
        (DirectSum.of (fun d' ↦ Correspondence (fieldChowSituation k) (partBase Z.obj.hom f)
          (partBase X.obj.hom d') d' (r i)) d (w i))) f'' (d'' + n) = 0 := by
  rw [projectiveBundleCompSum_apply_apply]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  conv_lhs => rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hf)]
  exact (congrArg _ (LinearMap.map_zero (projectiveBundleBlockMap X E n f'' d'' i (r i)))).trans
    (LinearEquiv.map_zero _)

section Single

variable {ι : Type*} [DecidableEq ι] {κ : ι → Type*} [∀ i, DecidableEq (κ i)]
  {β : ∀ i, κ i → Type*} [∀ i j, AddCommMonoid (β i j)]

/-- The `(i, j)` component of the pure element `x` in block `(i, j)` of a double direct sum is
`x`. -/
theorem of_of_apply_self (i : ι) (j : κ i) (x : β i j) :
    DirectSum.of (fun i ↦ DirectSum (κ i) (β i)) i (DirectSum.of (β i) j x) i j = x := by
  rw [DirectSum.of_eq_same, DirectSum.of_eq_same]

/-- The `(i', j')` component of the pure element `x` in block `(i, j)` of a double direct sum
vanishes when `i ≠ i'`. -/
theorem of_of_apply_of_ne_left (i : ι) (j : κ i) (x : β i j) {i' : ι} (h : i ≠ i')
    (j' : κ i') :
    DirectSum.of (fun i ↦ DirectSum (κ i) (β i)) i (DirectSum.of (β i) j x) i' j' = 0 := by
  rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
  rfl

/-- The `(i, j')` component of the pure element `x` in block `(i, j)` of a double direct sum
vanishes when `j ≠ j'`. -/
theorem of_of_apply_of_ne_right (i : ι) (j : κ i) (x : β i j) {j' : κ i} (h : j ≠ j') :
    DirectSum.of (fun i ↦ DirectSum (κ i) (β i)) i (DirectSum.of (β i) j x) i j' = 0 := by
  rw [DirectSum.of_eq_same, DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]

/-- A pure element of a double direct sum in a block that is a subsingleton is zero. -/
theorem of_of_eq_zero (i : ι) (j : κ i) (x : β i j) [Subsingleton (β i j)] :
    DirectSum.of (fun i ↦ DirectSum (κ i) (β i)) i (DirectSum.of (β i) j x) = 0 := by
  rw [Subsingleton.elim x 0, map_zero, map_zero]

/-- A linear map into a double direct sum whose range contains every pure block is
surjective. -/
theorem surjective_of_of_of_mem_range {R : Type*} [Semiring R] {M : Type*} [AddCommMonoid M]
    [Module R M] [∀ i j, Module R (β i j)]
    (Ψ : M →ₗ[R] DirectSum ι fun i ↦ DirectSum (κ i) (β i))
    (h : ∀ i j (x : β i j),
      DirectSum.of (fun i ↦ DirectSum (κ i) (β i)) i (DirectSum.of (β i) j x) ∈
        LinearMap.range Ψ) :
    Function.Surjective Ψ := by
  intro y
  suffices hy : y ∈ LinearMap.range Ψ from hy
  induction y using DirectSum.induction_on with
  | zero => exact Submodule.zero_mem _
  | add a b ha hb => exact Submodule.add_mem _ ha hb
  | of i y' =>
    induction y' using DirectSum.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | of j x => exact h i j x

end Single

/-- The correspondences into the part `P_e` of the projective bundle vanish for `e < n`. -/
private theorem subsingleton_correspondence_projectiveBundle_of_lt (f e : ℕ) (s : ℤ)
    (he : ¬ n ≤ e) :
    Subsingleton (Correspondence (fieldChowSituation k) (partBase Z.obj.hom f)
      (partBase (projectiveBundle X E n).obj.hom e) e s) := by
  have : IsEmpty (dimPart (projectiveBundle X E n).obj.hom e).toScheme :=
    ⟨fun x ↦ not_mem_dimPart_projectiveBundle_of_lt X E n (by omega) x.1 x.2⟩
  exact subsingleton_correspondence_of_isEmpty_right _ _ _ e s

/-- `∑_i c_i ∘ u_i` for `u_i` supported on the single block `(f, d)`. -/
theorem projectiveBundleCompSum_of_of (r : Fin (n + 1) → ℤ) (s : ℤ)
    (hrs : ∀ i : Fin (n + 1), r i + (i : ℕ) = s) (f d : ℕ)
    (w : ∀ i : Fin (n + 1),
      Correspondence (fieldChowSituation k) (partBase Z.obj.hom f) (partBase X.obj.hom d) d (r i))
    (z : Correspondence (fieldChowSituation k) (partBase Z.obj.hom f)
      (partBase (projectiveBundle X E n).obj.hom (d + n)) (d + n : ℕ) s)
    (hw : ∑ i, correspondenceCongr k (partBase Z.obj.hom f)
      (partBase (projectiveBundle X E n).obj.hom (d + n)) (hrs i)
      (projectiveBundleBlockMap X E n f d i (r i) (w i)) = z) :
    projectiveBundleCompSum X E n Z r s hrs (fun i ↦ DirectSum.of (fun f' ↦ DirectSum ℕ fun d' ↦
        Correspondence (fieldChowSituation k) (partBase Z.obj.hom f') (partBase X.obj.hom d') d'
          (r i)) f
        (DirectSum.of (fun d' ↦ Correspondence (fieldChowSituation k) (partBase Z.obj.hom f)
          (partBase X.obj.hom d') d' (r i)) d (w i))) =
      DirectSum.of (fun f ↦ DirectSum ℕ fun e ↦ Correspondence (fieldChowSituation k)
          (partBase Z.obj.hom f) (partBase (projectiveBundle X E n).obj.hom e) e s) f
        (DirectSum.of (fun e ↦ Correspondence (fieldChowSituation k) (partBase Z.obj.hom f)
          (partBase (projectiveBundle X E n).obj.hom e) e s) (d + n) z) := by
  refine DirectSum.ext fun f'' ↦ DirectSum.ext fun e'' ↦ ?_
  by_cases he'' : n ≤ e''
  · obtain ⟨d'', rfl⟩ : ∃ d'', e'' = d'' + n := ⟨e'' - n, by omega⟩
    by_cases hf : f = f''
    · subst hf
      by_cases hd : d = d''
      · subst hd
        exact (projectiveBundleCompSum_of_of_apply_self X E n Z r s hrs f d w).trans
          (hw.trans (of_of_apply_self (β := fun f e ↦ Correspondence (fieldChowSituation k)
            (partBase Z.obj.hom f) (partBase (projectiveBundle X E n).obj.hom e) e s) f (d + n)
            z).symm)
      · exact (projectiveBundleCompSum_of_of_apply_of_ne_right X E n Z r s hrs f d w hd).trans
          (of_of_apply_of_ne_right (β := fun f e ↦ Correspondence (fieldChowSituation k)
            (partBase Z.obj.hom f) (partBase (projectiveBundle X E n).obj.hom e) e s) f (d + n)
            z (by omega)).symm
    · exact (projectiveBundleCompSum_of_of_apply_of_ne_left X E n Z r s hrs f d w hf d'').trans
        (of_of_apply_of_ne_left (β := fun f e ↦ Correspondence (fieldChowSituation k)
          (partBase Z.obj.hom f) (partBase (projectiveBundle X E n).obj.hom e) e s) f (d + n)
          z hf (d'' + n)).symm
  · have := subsingleton_correspondence_projectiveBundle_of_lt X E n Z f'' e'' s he''
    exact Subsingleton.elim _ _

/-- **`(u_i) ↦ ∑_i c_i ∘ u_i` is bijective**: block by block it is the map of Stacks 02TX for
`Z_f × P_{d+n} ⟶ Z_f × X_d`, and the parts `P_e`, `e < n`, are empty. -/
theorem bijective_projectiveBundleCompSum (r : Fin (n + 1) → ℤ) (s : ℤ)
    (hrs : ∀ i : Fin (n + 1), r i + (i : ℕ) = s) :
    Function.Bijective (projectiveBundleCompSum X E n Z r s hrs) := by
  refine ⟨fun u v huv ↦ ?_, fun y ↦ ?_⟩
  · funext i
    refine DFinsupp.ext fun f ↦ DFinsupp.ext fun d ↦ ?_
    have h := congrArg (fun w ↦ w f (d + n)) huv
    simp only [projectiveBundleCompSum_apply_apply] at h
    exact congrFun ((bijective_projectiveBundleBlockSum X E n Z f d r s hrs).1 h) i
  · have hzero : projectiveBundleCompSum X E n Z r s hrs 0 = 0 := map_zero _
    have hblock : ∀ (f e : ℕ) (z : Correspondence (fieldChowSituation k) (partBase Z.obj.hom f)
        (partBase (projectiveBundle X E n).obj.hom e) e s),
        ∃ u, projectiveBundleCompSum X E n Z r s hrs u =
          DirectSum.of (fun f ↦ DirectSum ℕ fun e ↦ Correspondence (fieldChowSituation k)
              (partBase Z.obj.hom f) (partBase (projectiveBundle X E n).obj.hom e) e s) f
            (DirectSum.of (fun e ↦ Correspondence (fieldChowSituation k) (partBase Z.obj.hom f)
              (partBase (projectiveBundle X E n).obj.hom e) e s) e z) := by
      intro f e z
      by_cases he : n ≤ e
      · obtain ⟨d, rfl⟩ : ∃ d, e = d + n := ⟨e - n, by omega⟩
        obtain ⟨w, hw⟩ := (bijective_projectiveBundleBlockSum X E n Z f d r s hrs).2 z
        exact ⟨_, projectiveBundleCompSum_of_of X E n Z r s hrs f d w z hw⟩
      · have := subsingleton_correspondence_projectiveBundle_of_lt X E n Z f e s he
        exact ⟨0, hzero.trans (of_of_eq_zero (β := fun f e ↦ Correspondence (fieldChowSituation k)
          (partBase Z.obj.hom f) (partBase (projectiveBundle X E n).obj.hom e) e s) f e z).symm⟩
    exact surjective_of_of_of_mem_range (β := fun f e ↦ Correspondence (fieldChowSituation k)
      (partBase Z.obj.hom f) (partBase (projectiveBundle X E n).obj.hom e) e s) _ hblock y

end CorrComposition

section Yoneda

open CategoryTheory.Limits

variable {C : Type*} [Category C] [Preadditive C] {ι : Type} [Fintype ι] {A : ι → C}
  [HasBiproduct A] {N : C}

/-- **A Yoneda criterion for a map out of a finite direct sum.** If `(u_i) ↦ ∑_i u_i ≫ c_i` is
bijective on morphisms out of `N` and out of each `A_j`, then `∑ c_i : ⨁ A_i ⟶ N` is an
isomorphism. -/
theorem isIso_biproduct_desc_of_bijective (c : ∀ i, A i ⟶ N)
    (hN : Function.Bijective fun u : (∀ i, N ⟶ A i) ↦ ∑ i, u i ≫ c i)
    (hA : ∀ j, Function.Bijective fun u : (∀ i, A j ⟶ A i) ↦ ∑ i, u i ≫ c i) :
    IsIso (biproduct.desc c) := by
  have key : ∀ {T : C} (x : T ⟶ ⨁ A), x ≫ biproduct.desc c = ∑ i, (x ≫ biproduct.π A i) ≫ c i := by
    intro T x
    have hx : x = biproduct.lift (f := A) fun i ↦ x ≫ biproduct.π A i :=
      biproduct.hom_ext _ _ fun i ↦ by simp
    conv_lhs => rw [hx]
    exact biproduct.lift_desc
  obtain ⟨u, hu⟩ := hN.2 (𝟙 N)
  have hd : biproduct.lift (f := A) u ≫ biproduct.desc c = 𝟙 N := by
    rw [biproduct.lift_desc]; exact hu
  have hinj : ∀ x y : ⨁ A ⟶ ⨁ A, x ≫ biproduct.desc c = y ≫ biproduct.desc c → x = y := by
    intro x y hxy
    refine biproduct.hom_ext' _ _ fun j ↦ ?_
    have h := congrArg (fun z ↦ biproduct.ι A j ≫ z) hxy
    simp only [← Category.assoc] at h
    rw [key, key] at h
    have := (hA j).1 h
    exact biproduct.hom_ext _ _ fun i ↦ by simpa using congrFun this i
  refine ⟨⟨biproduct.lift (f := A) u, hinj _ _ ?_, hd⟩⟩
  rw [Category.assoc, hd, Category.comp_id, Category.id_comp]

end Yoneda

section Motive

open CategoryTheory.GradedCategory CategoryTheory.Limits

variable {k : Type u} [Field k] (X : (SmoothProjectiveScheme k).FullSubcategory)
  (E : X.obj.left.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]

/-- The underlying morphism of a finite sum of morphisms of the twisted Karoubi envelope is the sum
of the underlying morphisms. -/
theorem TwistedKaroubi.sum_val {R : Type*} [Ring R] {D : Type*} [Category D] [Preadditive D]
    [GradedCategory R D] {M N : TwistedKaroubi R D} {ι : Type*} (s : Finset ι)
    (f : ι → (M ⟶ N)) : (∑ i ∈ s, f i).val = ∑ i ∈ s, (f i).val :=
  map_sum (⟨⟨fun g : M ⟶ N ↦ g.val, TwistedKaroubi.zero_val M N⟩,
    fun g g' ↦ TwistedKaroubi.add_val g g'⟩ : (M ⟶ N) →+ (M.X ⟶ N.X)) f s

/-- The correspondence of `c_i : h(X)(-i) ⟶ h(P)`, in the total module of correspondences, is
`c_i ∈ Corr^i(X, P)`. -/
theorem homOf_projectiveBundleCorr (i : ℕ) {r : ℤ} (h : r = i) :
    ChowMotiveCat.homOf r (projectiveBundleCorr X E n i h) =
      ChowMotiveCat.homOf (i : ℤ) (projectiveBundleCorr X E n i rfl) := by
  subst h
  rfl

/-- The underlying correspondence of `c_i : h(X)(-i) ⟶ h(P)` is `c_i ∈ Corr^i(X, P)`. -/
theorem projectiveBundleHom_val (i : ℕ) :
    (projectiveBundleHom X E n i).val =
      ChowMotiveCat.homOf (i : ℤ) (projectiveBundleCorr X E n i rfl) :=
  homOf_projectiveBundleCorr X E n i _

variable (Z : (SmoothProjectiveScheme k).FullSubcategory) (m : ℤ)

/-- Morphisms `h(Z)(m) ⟶ h(Y)(m')` are the correspondences of degree `m' - m`. -/
theorem bijective_component_val {Y : (SmoothProjectiveScheme k).FullSubcategory} (m' : ℤ) :
    Function.Bijective fun u : twistedMotive Z m ⟶ twistedMotive Y m' ↦
      ChowMotiveCat.component (m' - m) u.val := by
  refine ⟨fun u v huv ↦ TwistedKaroubi.hom_ext ?_, fun x ↦ ?_⟩
  · rw [← ChowMotiveCat.homOf_component u.2.1, ← ChowMotiveCat.homOf_component v.2.1]
    exact congrArg _ huv
  · exact ⟨TwistedKaroubi.Hom.mk (ChowMotiveCat.homOf _ x)
      ⟨ChowMotiveCat.homOf_mem_grade x, Category.id_comp _, Category.comp_id _⟩,
      ChowMotiveCat.component_homOf x⟩

/-- Composition with `c_i` in the category of correspondences, read in an equal degree. -/
theorem homOf_corrCongr_comp_projectiveBundleCorr {Z : (SmoothProjectiveScheme k).FullSubcategory}
    (i : ℕ) {r s : ℤ} (h : r + (i : ℤ) = s) (x : SmoothProjectiveCorr Z X r) :
    ChowMotiveCat.homOf s ((SmoothProjectiveCorr.toCorr Z (projectiveBundle X E n) s).symm
      (corrCongr k Z.obj.hom (projectiveBundle X E n).obj.hom h
        (comp k Z.obj.hom X.obj.hom (projectiveBundle X E n).obj.hom
          (canonicalDiagonalClassFamily k) r i (SmoothProjectiveCorr.toCorr Z X r x)
          (SmoothProjectiveCorr.toCorr X (projectiveBundle X E n) (i : ℤ)
            (projectiveBundleCorr X E n i rfl))))) =
      ChowMotiveCat.homOf (r + i)
        ((canonicalCorrespondenceCompositionData k).comp x (projectiveBundleCorr X E n i rfl)) := by
  rw [ChowMotiveCat.homOf, ChowMotiveCat.homOf, DirectSum.lof_eq_of, DirectSum.lof_eq_of,
    ← toCorr_correspondenceCompositionData_comp]
  exact of_toCorr_symm_corrCongr h _

set_option synthInstance.maxHeartbeats 200000 in
/-- **The key identity**: on correspondences, `(u_i) ↦ ∑_i c_i ∘ u_i` is
`Stacks.WeilCohomology.projectiveBundleCompSum`. -/
theorem homOf_projectiveBundleCompSum
    (u : ∀ i : Fin (n + 1), twistedMotive Z m ⟶ twistedMotive X (-((i : ℕ) : ℤ))) :
    ChowMotiveCat.homOf (0 - m)
      ((SmoothProjectiveCorr.toCorr Z (projectiveBundle X E n) (0 - m)).symm
      (projectiveBundleCompSum X E n Z (fun i ↦ -((i : ℕ) : ℤ) - m) (0 - m) (fun i ↦ by ring)
        (fun i ↦ SmoothProjectiveCorr.toCorr Z X _
          (ChowMotiveCat.component (-((i : ℕ) : ℤ) - m) (u i).val)))) =
      (∑ i, u i ≫ projectiveBundleFinHom X E n i).val := by
  rw [projectiveBundleCompSum_apply, map_sum, map_sum, TwistedKaroubi.sum_val]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [TwistedKaroubi.comp_val]
  conv_rhs => rw [← ChowMotiveCat.homOf_component (r := -((i : ℕ) : ℤ) - m)
    (TwistedKaroubi.val_mem (u i)).1, projectiveBundleFinHom, projectiveBundleHom_val,
    ChowMotiveCat.homOf_comp_homOf]
  exact homOf_corrCongr_comp_projectiveBundleCorr X E n i (by ring) _

/-- **`(u_i) ↦ ∑_i c_i ∘ u_i` on morphisms of motives is bijective**: for every motive
`h(Z)(m)`, composition with the `c_i` is a bijection from the families of morphisms
`h(Z)(m) ⟶ h(X)(-i)` onto the morphisms `h(Z)(m) ⟶ h(P)`. -/
theorem bijective_sum_comp_projectiveBundleFinHom :
    Function.Bijective fun u : (∀ i : Fin (n + 1),
        twistedMotive Z m ⟶ twistedMotive X (-((i : ℕ) : ℤ))) ↦
      ∑ i, u i ≫ projectiveBundleFinHom X E n i := by
  have hrs : ∀ i : Fin (n + 1), (-((i : ℕ) : ℤ) - m) + (i : ℕ) = 0 - m := fun i ↦ by ring
  have hΨ := bijective_projectiveBundleCompSum X E n Z (fun i ↦ -((i : ℕ) : ℤ) - m) (0 - m) hrs
  have hsrc : Function.Bijective fun u : (∀ i : Fin (n + 1),
      twistedMotive Z m ⟶ twistedMotive X (-((i : ℕ) : ℤ))) ↦
      fun i : Fin (n + 1) ↦ SmoothProjectiveCorr.toCorr Z X _
        (ChowMotiveCat.component (-((i : ℕ) : ℤ) - m) (u i).val) :=
    ⟨fun u v huv ↦ funext fun i : Fin (n + 1) ↦
        (bijective_component_val Z m (Y := X) (-((i : ℕ) : ℤ))).1 (congrFun huv i),
      fun x ↦ ⟨fun i : Fin (n + 1) ↦
          ((bijective_component_val Z m (Y := X) (-((i : ℕ) : ℤ))).2 (x i)).choose,
        funext fun i : Fin (n + 1) ↦
          ((bijective_component_val Z m (Y := X) (-((i : ℕ) : ℤ))).2 (x i)).choose_spec⟩⟩
  have htgt := bijective_component_val Z m (Y := projectiveBundle X E n) 0
  have hfun : (fun f : twistedMotive Z m ⟶ twistedMotive (projectiveBundle X E n) 0 ↦
      ChowMotiveCat.component (0 - m) f.val) ∘
      (fun u : (∀ i : Fin (n + 1), twistedMotive Z m ⟶ twistedMotive X (-((i : ℕ) : ℤ))) ↦
        ∑ i, u i ≫ projectiveBundleFinHom X E n i) =
      (SmoothProjectiveCorr.toCorr Z (projectiveBundle X E n) (0 - m)).symm ∘
        (projectiveBundleCompSum X E n Z (fun i ↦ -((i : ℕ) : ℤ) - m) (0 - m) hrs) ∘
        fun u (i : Fin (n + 1)) ↦ SmoothProjectiveCorr.toCorr Z X _
          (ChowMotiveCat.component (-((i : ℕ) : ℤ) - m) (u i).val) := by
    funext u
    simp only [Function.comp_apply]
    rw [← homOf_projectiveBundleCompSum X E n Z m u, ChowMotiveCat.component_homOf]
  refine (Function.Bijective.of_comp_iff' htgt _).1 ?_
  rw [hfun]
  exact (SmoothProjectiveCorr.toCorr Z (projectiveBundle X E n) (0 - m)).symm.bijective.comp
    (hΨ.comp hsrc)

/-- **Stacks Project, Tag 0FGQ (the projective space bundle formula).** Let `X` be a smooth
projective scheme over `k`, `ℰ` a finite locally free `𝒪_X`-module of rank `n + 1` and
`p : P = 𝐏(ℰ) ⟶ X` its projective bundle. Then

  `∑_{i ≤ n} c_i : ⨁_{i ≤ n} h(X)(-i) ⟶ h(P)`,   `c_i = c₁(pr₂^*𝒪_P(1))^i ∩ [Γ_p]`,

is an isomorphism in the category `M_k` of Chow motives. -/
theorem isIso_projectiveBundleMotiveMap :
    IsIso (biproduct.desc (projectiveBundleFinHom X E n)) :=
  isIso_biproduct_desc_of_bijective _
    (bijective_sum_comp_projectiveBundleFinHom X E n (projectiveBundle X E n) 0)
    fun j ↦ bijective_sum_comp_projectiveBundleFinHom X E n X (-((j : ℕ) : ℤ))

end Motive

section Formula

open CategoryTheory.GradedCategory CategoryTheory.Limits

variable {k : Type u} [Field k]

/-- **The motive of the empty scheme is zero**: correspondences between empty schemes vanish. -/
theorem isZero_twistedMotive_of_isEmpty (Y : (SmoothProjectiveScheme k).FullSubcategory)
    [IsEmpty Y.obj.left] (m : ℤ) : IsZero (twistedMotive Y m) := by
  have : ∀ d, IsEmpty (dimPart Y.obj.hom d).toScheme := fun d ↦ ⟨fun x ↦ isEmptyElim x.1⟩
  have : ∀ (r : ℤ) (d e : ℕ), Subsingleton (Correspondence (fieldChowSituation k)
      (partBase Y.obj.hom d) (partBase Y.obj.hom e) e r) := fun r d e ↦
    subsingleton_correspondence_of_isEmpty_left _ _ _ e r
  have : ∀ (r : ℤ) (d : ℕ), Subsingleton (DirectSum ℕ fun e ↦ Correspondence
      (fieldChowSituation k) (partBase Y.obj.hom d) (partBase Y.obj.hom e) e r) := fun r d ↦
    inferInstanceAs (Subsingleton (Π₀ e, Correspondence (fieldChowSituation k)
      (partBase Y.obj.hom d) (partBase Y.obj.hom e) e r))
  have : ∀ r : ℤ, Subsingleton (SmoothProjectiveCorr Y Y r) := fun r ↦
    inferInstanceAs (Subsingleton (Π₀ d, DirectSum ℕ fun e ↦ Correspondence
      (fieldChowSituation k) (partBase Y.obj.hom d) (partBase Y.obj.hom e) e r))
  have : Subsingleton ((twistedMotive Y m).X ⟶ (twistedMotive Y m).X) :=
    inferInstanceAs (Subsingleton (Π₀ r, SmoothProjectiveCorr Y Y r))
  exact (IsZero.iff_id_eq_zero _).2 (TwistedKaroubi.hom_ext (Subsingleton.elim _ _))

variable (X : (SmoothProjectiveScheme k).FullSubcategory) (E : X.obj.left.Modules) (r : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]

/-- **Stacks Project, Tag 0FGQ (the projective space bundle formula).** Let `k` be a field, `X` a
smooth projective scheme over `k`, `ℰ` a finite locally free `𝒪_X`-module of rank `r` and
`p : P = 𝐏(ℰ) ⟶ X` its projective bundle, with `𝒪_P(1)` normalized so that `p_*𝒪_P(1) = ℰ`. For
`i = 0, …, r - 1` let `c_i = c₁(pr₂^*𝒪_P(1))^i ∩ [Γ_p] ∈ Corr^i(X, P)`, read as a morphism
`h(X)(-i) ⟶ h(P)`, where `h(Y)(m) = (Y, 1, m)` is `Stacks.WeilCohomology.twistedMotive Y m` and
`h(P) = (P, 1, 0) = twistedMotive P 0` (`Stacks.WeilCohomology.twistedMotive_zero`). Then

  `∑_{i < r} c_i : ⨁_{i < r} h(X)(-i) ⟶ h(P)`

is an isomorphism in the category `M_k` of Chow motives. -/
@[stacks 0FGQ "the projective space bundle formula: the sum of the c_i = c_1(pr_2^*O_P(1))^i ∩
[Gamma_p], from the direct sum of the h(X)(-i), i < r, to h(P), is an isomorphism in M_k"]
theorem isIso_projectiveBundleFormula :
    IsIso (biproduct.desc (projectiveBundleOfRankHom X E r) :
      (⨁ fun i : Fin r ↦ twistedMotive X (-((i : ℕ) : ℤ))) ⟶
        twistedMotive (projectiveBundleOfRank X E r) 0) := by
  rcases r with _ | n
  · let := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 0
    have : IsEmpty (projectiveBundleOfRank X E 0).obj.left := isEmpty_bundle_of_rank_zero E
    refine IsZero.isIso ?_ (isZero_twistedMotive_of_isEmpty _ 0) _
    exact (IsZero.iff_id_eq_zero _).2 (biproduct.hom_ext _ _ fun j ↦ j.elim0)
  · have h : biproduct.desc (projectiveBundleOfRankHom X E (n + 1)) =
        biproduct.desc (projectiveBundleFinHom X E n) ≫
          eqToHom (twistedMotive_projectiveBundleOfRank_succ X E n) :=
      biproduct.hom_ext' _ _ fun j ↦ by
        rw [biproduct.ι_desc, biproduct.ι_desc_assoc]
        rfl
    rw [h]
    have := isIso_projectiveBundleMotiveMap X E n
    infer_instance

end Formula

end Stacks.WeilCohomology

end
