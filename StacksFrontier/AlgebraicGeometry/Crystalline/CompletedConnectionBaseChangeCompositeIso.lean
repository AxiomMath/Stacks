module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionBaseChangeComposite
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CompletedFormsShapeNatural

/-!
# The comparison of the twice base-changed module with the once base-changed one is bijective

`Crystalline.CompletedConnection.baseChangeComposite` is the map

`(M ⊗̂_D D') ⊗̂_{D'} D'' → M ⊗̂_D D''`

along which the functoriality of the base change of completed de Rham complexes under
composition is stated, `Crystalline.CompletedDeRham.baseChangeComplexHom_comp`.  That law reads

`α_ψ ≫ α_{ψ'} ≫ ρ = α_{ψ_comp}`,

with `ρ` the morphism of complexes induced by the comparison.  This module proves the comparison
bijective with no hypothesis at all: no flatness, no finiteness, no completeness of `M`; hence `ρ`
is an isomorphism of complexes.

## Main results

* `Crystalline.adicCompletionMapₛₗ_bijective` — a completed semilinear map is bijective as soon
  as the maps it induces on the levels are.
* `Crystalline.CompletedConnection.baseChangeComposite_bijective` — **the comparison is
  bijective.**
* `Crystalline.CompletedConnection.baseChangeCompositeEquiv` — it as a `D''`-linear
  isomorphism.
* `Crystalline.CompletedDeRham.isIso_horizontalComplexHom_baseChangeComposite` — **hence the
  correction in `...baseChangeComplexHom_comp` is an isomorphism of complexes.**

## References

* [Stacks Project, Lemma 60.21.4, Tag 07LH](https://stacks.math.columbia.edu/tag/07LH)
* [Stacks Project, Tag 05GG](https://stacks.math.columbia.edu/tag/05GG)
-/

@[expose] public noncomputable section

namespace Crystalline

open CategoryTheory DividedPowers TensorProduct

universe u v w

/-! ### Bijectivity of a completed map from bijectivity at every level -/

section Levelwise

variable {R S : Type*} [CommRing R] [CommRing S] {P Q : Type*} [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module S Q] {σ : R →+* S} {I : Ideal R} {Jd : Ideal S}

/-- **A completed semilinear map is bijective as soon as the maps it induces on the levels
are.** -/
public theorem adicCompletionMapₛₗ_bijective (g : P →ₛₗ[σ] Q) (h : I.map σ ≤ Jd)
    (hlev : ∀ n : ℕ, Function.Bijective (adicQuotientMap g h n)) :
    Function.Bijective (adicCompletionMapₛₗ g h) := by
  classical
  refine ⟨fun x y hxy ↦ AdicCompletion.ext fun n ↦ (hlev n).1 ?_, fun z ↦ ?_⟩
  · exact congrArg (fun w : AdicCompletion Jd Q ↦ w.val n) hxy
  · choose pre hpre using fun n : ℕ ↦ (hlev n).2 (z.val n)
    have hcoh : ∀ {m n : ℕ} (hmn : m ≤ n),
        AdicCompletion.transitionMap I P hmn (pre n) = pre m := by
      intro m n hmn
      refine (hlev m).1 ?_
      calc adicQuotientMap g h m (AdicCompletion.transitionMap I P hmn (pre n))
          = AdicCompletion.transitionMap Jd Q hmn (adicQuotientMap g h n (pre n)) :=
            (adicQuotientMap_transition g h hmn (pre n)).symm
        _ = AdicCompletion.transitionMap Jd Q hmn (z.val n) := by rw [hpre]
        _ = z.val m := z.property hmn
        _ = adicQuotientMap g h m (pre m) := (hpre m).symm
    exact ⟨⟨pre, hcoh⟩, AdicCompletion.ext fun n ↦ hpre n⟩

end Levelwise

namespace CompletedConnection

/-! ### The section of the comparison -/

section CompositeIso

variable (p : ℕ) (D : Type u) [CommRing D] (D' : Type u) [CommRing D'] [Algebra D D']
  (D'' : Type u) [CommRing D''] [Algebra D' D''] [Algebra D D'']
  [IsScalarTower D D' D''] (M : Type w) [AddCommGroup M] [Module D M]

/-- **The section `h : D'' ⊗_D M → D'' ⊗_{D'} (D' ⊗_D M)^∧` of the comparison**,
`b'' ⊗ m ↦ b'' ⊗ (1 ⊗ m)^∧`.

It is the associativity isomorphism `D'' ⊗_D M ≅ D'' ⊗_{D'} (D' ⊗_D M)` of
`TensorProduct.AlgebraTensorModule.cancelBaseChange` followed by the structure map of the inner
`p`-adic completion.  It is not a section of
`Crystalline.CompletedConnection.baseChangeComposite` itself — its source is the *uncompleted*
`D'' ⊗_D M` — but it is a section of the map the comparison is the completion of. -/
public def baseChangeCompositeSection :
    (D'' ⊗[D] M) →ₗ[D''] (D'' ⊗[D'] baseChangeCarrier p D D' M) :=
  (LinearMap.baseChange D'' (AdicCompletion.of (pAdicIdeal (A := D') p) (D' ⊗[D] M))) ∘ₗ
    (AlgebraTensorModule.cancelBaseChange D D' D'' D'' M).symm.toLinearMap

/-- The section on a pure tensor: `b'' ⊗ m ↦ b'' ⊗ (1 ⊗ m)^∧`. -/
@[simp] public theorem baseChangeCompositeSection_tmul (b'' : D'') (m : M) :
    baseChangeCompositeSection p D D' D'' M (b'' ⊗ₜ[D] m) =
      b'' ⊗ₜ[D'] AdicCompletion.of (pAdicIdeal (A := D') p) (D' ⊗[D] M) ((1 : D') ⊗ₜ[D] m) :=
  rfl

/-- **`h` composed with the uncompleted comparison `ĉ : D' ⊗_D M → D'' ⊗_D M` is
`v ↦ 1 ⊗ v^∧`.** -/
public theorem baseChangeCompositeSection_carrierTensorMap (v : D' ⊗[D] M) :
    baseChangeCompositeSection p D D' D'' M (carrierTensorMap D D' D'' M v) =
      (1 : D'') ⊗ₜ[D'] AdicCompletion.of (pAdicIdeal (A := D') p) (D' ⊗[D] M) v := by
  induction v using TensorProduct.inductionOn with
  | tmul b' m =>
    rw [carrierTensorMap_tmul, baseChangeCompositeSection_tmul,
      show AdicCompletion.of (pAdicIdeal (A := D') p) (D' ⊗[D] M) (b' ⊗ₜ[D] m) =
          b' • AdicCompletion.of (pAdicIdeal (A := D') p) (D' ⊗[D] M) ((1 : D') ⊗ₜ[D] m) from by
        rw [← _root_.map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one],
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
  | add a b ha hb =>
    rw [_root_.map_add, _root_.map_add, ha, hb, _root_.map_add, TensorProduct.tmul_add]

/-- **The uncompleted comparison composed with its section is the structure map of the outer
completion**: `g (h (b'' ⊗ m)) = (b'' ⊗ m)^∧`. -/
public theorem liftBaseChange_baseChangeCompositeSection (x : D'' ⊗[D] M) :
    (carrierMapLinear p D D' D'' M).liftBaseChange D''
        (baseChangeCompositeSection p D D' D'' M x) =
      AdicCompletion.of (pAdicIdeal (A := D'') p) (D'' ⊗[D] M) x := by
  induction x using TensorProduct.inductionOn with
  | tmul b'' m =>
    rw [baseChangeCompositeSection_tmul, LinearMap.liftBaseChange_tmul, carrierMapLinear_apply,
      carrierMap_of, carrierTensorMap_tmul, map_one, ← _root_.map_smul,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add a b ha hb => rw [_root_.map_add, _root_.map_add, ha, hb, _root_.map_add]

omit [Algebra D D''] [IsScalarTower D D' D''] in
/-- The image of `pⁿ (D' ⊗_D M)^∧` under `w ↦ b'' ⊗ w` lies in `pⁿ` times the twice
base-changed module. -/
public theorem tmul_mem_pow_smul_top (n : ℕ) (b'' : D'') {w : baseChangeCarrier p D D' M}
    (hw : w ∈ pAdicIdeal (A := D') p ^ n • (⊤ : Submodule D' (baseChangeCarrier p D D' M))) :
    b'' ⊗ₜ[D'] w ∈ pAdicIdeal (A := D'') p ^ n •
      (⊤ : Submodule D'' (D'' ⊗[D'] baseChangeCarrier p D D' M)) := by
  have hmap : (pAdicIdeal (A := D') p ^ n).map (algebraMap D' D'') =
      pAdicIdeal (A := D'') p ^ n := by
    rw [Ideal.map_pow, pAdicIdeal_map_eq p D' D'']
  refine Submodule.smul_induction_on hw (fun c hc w' _ ↦ ?_) (fun x y hx hy ↦ ?_)
  · have key : b'' ⊗ₜ[D'] (c • w') =
        algebraMap D' D'' c • (b'' ⊗ₜ[D'] w' : D'' ⊗[D'] baseChangeCarrier p D D' M) := by
      rw [TensorProduct.tmul_smul, algebraMap_smul]
    rw [key]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [← hmap]
    exact Ideal.mem_map_of_mem _ hc
  · rw [TensorProduct.tmul_add]
    exact Submodule.add_mem _ hx hy

/-- The comparison of base-changed modules, read at a level: it is the map the uncompleted
comparison induces on the level. -/
public theorem carrierMap_val (z : baseChangeCarrier p D D' M) (n : ℕ) :
    (carrierMap p D D' D'' M z).val n =
      adicQuotientMap (carrierTensorMap D D' D'' M) (pAdicIdeal_map_le p D' D'') n (z.val n) :=
  rfl

/-- **A level-`n` representative of `g x` whose image under the section recovers `x` modulo
`pⁿ`.** -/
public theorem exists_rep_liftBaseChange (n : ℕ)
    (x : D'' ⊗[D'] baseChangeCarrier p D D' M) :
    ∃ a : D'' ⊗[D] M,
      ((carrierMapLinear p D D' D'' M).liftBaseChange D'' x).val n =
          Submodule.Quotient.mk a ∧
        baseChangeCompositeSection p D D' D'' M a - x ∈ pAdicIdeal (A := D'') p ^ n •
          (⊤ : Submodule D'' (D'' ⊗[D'] baseChangeCarrier p D D' M)) := by
  classical
  induction x using TensorProduct.inductionOn with
  | tmul b'' z =>
    obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective
      (pAdicIdeal (A := D') p ^ n • (⊤ : Submodule D' (D' ⊗[D] M))) (z.val n)
    refine ⟨b'' • carrierTensorMap D D' D'' M v, ?_, ?_⟩
    · rw [LinearMap.liftBaseChange_tmul, carrierMapLinear_apply,
        show (b'' • carrierMap p D D' D'' M z).val n =
            b'' • (carrierMap p D D' D'' M z).val n from
          (AdicCompletion.eval (pAdicIdeal (A := D'') p) (D'' ⊗[D] M) n).map_smul b''
            (carrierMap p D D' D'' M z),
        carrierMap_val, ← hv, adicQuotientMap_mk]
      rfl
    · have hsec : baseChangeCompositeSection p D D' D'' M
          (b'' • carrierTensorMap D D' D'' M v) =
            b'' ⊗ₜ[D'] AdicCompletion.of (pAdicIdeal (A := D') p) (D' ⊗[D] M) v := by
        rw [_root_.map_smul, baseChangeCompositeSection_carrierTensorMap,
          TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have hmem : AdicCompletion.of (pAdicIdeal (A := D') p) (D' ⊗[D] M) v - z ∈
          pAdicIdeal (A := D') p ^ n • (⊤ : Submodule D' (baseChangeCarrier p D D' M)) := by
        rw [AdicCompletion.pow_smul_top_eq_ker_eval (pAdicIdeal_fg p D'), LinearMap.mem_ker,
          _root_.map_sub]
        change Submodule.Quotient.mk v - z.val n = 0
        rw [hv, sub_self]
      rw [hsec, ← TensorProduct.tmul_sub]
      exact tmul_mem_pow_smul_top p D D' D'' M n b'' hmem
  | add x y hx hy =>
    obtain ⟨a, ha, ha'⟩ := hx
    obtain ⟨c, hc, hc'⟩ := hy
    refine ⟨a + c, ?_, ?_⟩
    · rw [_root_.map_add,
        show ((carrierMapLinear p D D' D'' M).liftBaseChange D'' x +
              (carrierMapLinear p D D' D'' M).liftBaseChange D'' y).val n =
            (((carrierMapLinear p D D' D'' M).liftBaseChange D'' x).val n +
              ((carrierMapLinear p D D' D'' M).liftBaseChange D'' y).val n) from rfl,
        ha, hc]
      rfl
    · rw [_root_.map_add,
        show baseChangeCompositeSection p D D' D'' M a +
              baseChangeCompositeSection p D D' D'' M c - (x + y) =
            (baseChangeCompositeSection p D D' D'' M a - x) +
              (baseChangeCompositeSection p D D' D'' M c - y) from by abel]
      exact Submodule.add_mem _ ha' hc'

/-- **The uncompleted comparison is bijective at every level `pⁿ`.** -/
public theorem adicQuotientMap_liftBaseChange_bijective (n : ℕ) :
    Function.Bijective (adicQuotientMap ((carrierMapLinear p D D' D'' M).liftBaseChange D'')
      (le_of_eq (Ideal.map_id (pAdicIdeal (A := D'') p))) n) := by
  classical
  constructor
  · intro s t hst
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective
      (pAdicIdeal (A := D'') p ^ n •
        (⊤ : Submodule D'' (D'' ⊗[D'] baseChangeCarrier p D D' M))) s
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective
      (pAdicIdeal (A := D'') p ^ n •
        (⊤ : Submodule D'' (D'' ⊗[D'] baseChangeCarrier p D D' M))) t
    rw [adicQuotientMap_mk, adicQuotientMap_mk, Submodule.Quotient.eq,
      ← _root_.map_sub] at hst
    obtain ⟨a, ha, ha'⟩ := exists_rep_liftBaseChange p D D' D'' M n (x - y)
    have hzero : ((carrierMapLinear p D D' D'' M).liftBaseChange D'' (x - y)).val n = 0 :=
      LinearMap.mem_ker.mp ((AdicCompletion.pow_smul_top_eq_ker_eval
        (M := D'' ⊗[D] M) (I := pAdicIdeal (A := D'') p) (n := n)
        (pAdicIdeal_fg p D'')).le hst)
    have hamem : a ∈ pAdicIdeal (A := D'') p ^ n • (⊤ : Submodule D'' (D'' ⊗[D] M)) := by
      rw [← Submodule.Quotient.mk_eq_zero, ← ha, hzero]
    rw [Submodule.Quotient.eq, show x - y = baseChangeCompositeSection p D D' D'' M a -
      (baseChangeCompositeSection p D D' D'' M a - (x - y)) by abel]
    have hmap : baseChangeCompositeSection p D D' D'' M a ∈
        pAdicIdeal (A := D'') p ^ n •
          (⊤ : Submodule D'' (D'' ⊗[D'] baseChangeCarrier p D D' M)) := by
      refine Submodule.smul_induction_on hamem (fun c hc w _ ↦ ?_) (fun u v hu hv ↦ ?_)
      · rw [_root_.map_smul]
        exact Submodule.smul_mem_smul hc Submodule.mem_top
      · rw [_root_.map_add]
        exact Submodule.add_mem _ hu hv
    exact Submodule.sub_mem _ hmap ha'
  · intro t
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective
      (pAdicIdeal (A := D'') p ^ n • (⊤ : Submodule D'' (baseChangeCarrier p D D'' M))) t
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective
      (pAdicIdeal (A := D'') p ^ n • (⊤ : Submodule D'' (D'' ⊗[D] M))) (y.val n)
    refine ⟨Submodule.Quotient.mk (baseChangeCompositeSection p D D' D'' M a), ?_⟩
    rw [adicQuotientMap_mk, liftBaseChange_baseChangeCompositeSection,
      Submodule.Quotient.eq,
      AdicCompletion.pow_smul_top_eq_ker_eval (pAdicIdeal_fg p D''), LinearMap.mem_ker,
      _root_.map_sub]
    change Submodule.Quotient.mk a - y.val n = 0
    rw [ha, sub_self]

/-- **The comparison of the twice base-changed module with the once base-changed one is
bijective.** -/
public theorem baseChangeComposite_bijective :
    Function.Bijective (baseChangeComposite p D D' D'' M) := by
  let : IsAdicComplete (pAdicIdeal (A := D'') p) (baseChangeCarrier p D D'' M) :=
    isPAdicallyComplete_baseChangeCarrier p D D'' M
  have hcollapse : Function.Bijective
      ((AdicCompletion.ofLinearEquiv (pAdicIdeal (A := D'') p)
        (baseChangeCarrier p D D'' M)).symm.toLinearMap) :=
    (AdicCompletion.ofLinearEquiv (pAdicIdeal (A := D'') p)
      (baseChangeCarrier p D D'' M)).symm.bijective
  exact hcollapse.comp (adicCompletionMapₛₗ_bijective _ _
    (adicQuotientMap_liftBaseChange_bijective p D D' D'' M))

/-- **The comparison, as a `D''`-linear isomorphism.** -/
public def baseChangeCompositeEquiv :
    baseChangeCarrier p D' D'' (baseChangeCarrier p D D' M) ≃ₗ[D'']
      baseChangeCarrier p D D'' M :=
  LinearEquiv.ofBijective (baseChangeComposite p D D' D'' M)
    (baseChangeComposite_bijective p D D' D'' M)

/-- The isomorphism `baseChangeCompositeEquiv` acts on elements as the comparison map
`baseChangeComposite`. -/
@[simp] public theorem baseChangeCompositeEquiv_apply
    (z : baseChangeCarrier p D' D'' (baseChangeCarrier p D D' M)) :
    baseChangeCompositeEquiv p D D' D'' M z = baseChangeComposite p D D' D'' M z :=
  rfl

end CompositeIso

end CompletedConnection

/-! ### The correction in the composition law is an isomorphism of complexes -/

namespace CompletedDeRham

section CompositeComplexIso

variable (p : ℕ) (D : Type u) [CommRing D] (D' : Type u) [CommRing D'] [Algebra D D']
  (D'' : Type u) [CommRing D''] [Algebra D' D''] [Algebra D D'']
  [IsScalarTower D D' D''] (M : Type w) [AddCommGroup M] [Module D M]
  (Om : ℕ → Type v) [∀ i, AddCommGroup (Om i)] [∀ i, Module D'' (Om i)]
  (wedge : ∀ i, Om i →ₗ[D''] Om 1 →ₗ[D''] Om (i + 1)) (deRham : ∀ i, Om i →+ Om (i + 1))
  {dmap : D'' → Om 1}
  (nablaM : CompletedConnection p D'' (Om 1) dmap
    (CompletedConnection.baseChangeCarrier p D' D''
      (CompletedConnection.baseChangeCarrier p D D' M)))
  (nablaN : CompletedConnection p D'' (Om 1) dmap
    (CompletedConnection.baseChangeCarrier p D D'' M))
  (hleib : IsGradedLeibniz D'' Om wedge deRham dmap)
  (hnabla : ∀ m, nablaN (CompletedConnection.baseChangeComposite p D D' D'' M m) =
    AdicCompletion.map (pAdicIdeal (A := D'') p)
      (TensorProduct.map (CompletedConnection.baseChangeComposite p D D' D'' M)
        (LinearMap.id (R := D'') (M := Om 1))) (nablaM m))

include hnabla in
/-- **The correction in the composition law of the base change of completed de Rham complexes is
an isomorphism of complexes.**

`Crystalline.CompletedDeRham.baseChangeComplexHom_comp` reads
`α_ψ ≫ α_{ψ'} ≫ ρ = α_{ψ_comp}`, where `ρ` is the morphism of complexes induced by the
comparison `Crystalline.CompletedConnection.baseChangeComposite` of the twice base-changed
module with the once base-changed one.

The hypothesis `hnabla` is the horizontality, in the shape
`Crystalline.CompletedDeRham.horizontalComplexHom` asks for. -/
public theorem isIso_horizontalComplexHom_baseChangeComposite
    (hsqM : IsSquareZero p D'' Om wedge deRham
      (CompletedConnection.baseChangeCarrier p D' D''
        (CompletedConnection.baseChangeCarrier p D D' M)) nablaM hleib)
    (hsqN : IsSquareZero p D'' Om wedge deRham
      (CompletedConnection.baseChangeCarrier p D D'' M) nablaN hleib) :
    IsIso (horizontalComplexHom p D''
      (CompletedConnection.baseChangeCarrier p D' D''
        (CompletedConnection.baseChangeCarrier p D D' M))
      (CompletedConnection.baseChangeCarrier p D D'' M) Om
      (CompletedConnection.baseChangeComposite p D D' D'' M) wedge deRham nablaM nablaN hleib
      hnabla hsqM hsqN) :=
  isIso_horizontalComplexHom p D'' _ _ Om
    (CompletedConnection.baseChangeCompositeEquiv p D D' D'' M) wedge deRham nablaM nablaN
    hleib hnabla hsqM hsqN

end CompositeComplexIso

end CompletedDeRham

end Crystalline

end
