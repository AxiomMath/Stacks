module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.ProcyclicTrivialCoinvariants
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.TwoTermTrace

/-!
# The trace of an element on the derived coinvariants of a procyclic group, trivial coefficients

Let `γ ∈ Γ` and let `w ∈ Λ[[G]]` satisfy `(σ - 1) w = γ σ γ⁻¹ - 1`. The automorphism `σ_γ` of
`Λ[[G]]` in degree `0` and `x ↦ σ_γ(x) w` in degree `1` form a lift of the action of `γ` on the
trivial module to the Koszul resolution `Stacks.GroupHomology.Procyclic.koszulResolution`. On
coinvariants it is the identity of `Λ` in degree `0` and right multiplication by `ε(w)` in degree
`-1`, so

`Tr(γ | LH₀(G, Λ)) = 1 - ε(w)` in `Λ^♮`.

## Main definitions

* `Stacks.GroupHomology.Procyclic.koszulLift`: the lift of the action of `γ`.
* `Stacks.GroupHomology.Procyclic.coinvariantsSelfLinearEquiv`: the coinvariants of `Λ[[G]]` are
  `Λ`, through the augmentation.

## Main results

* `Stacks.GroupHomology.Procyclic.koszulLift_comm`: the lift lifts the action of `γ`.
* `Stacks.GroupHomology.Procyclic.perfectDerivedTrace_trivialRep`: the trace formula
  `Tr(γ | LH₀(G, Λ)) = 1 - ε(w)`.

## References

* [Stacks Project, Tag 03VQ](https://stacks.math.columbia.edu/tag/03VQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.GroupHomology.Procyclic

open CompletedGroupAlgebra

attribute [local instance] HasDerivedCategory.standard

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {G : Subgroup Γ}
  [G.Normal] [CompactSpace G] {Λ : Type u} [Ring Λ] (σ : G) (γ : Γ)

/-- The automorphism `σ_γ` of `Λ[[G]]` induced by conjugation by `γ`. -/
public abbrev conjRingEquiv : CompletedGroupAlgebra Λ G ≃+* CompletedGroupAlgebra Λ G :=
  mapRingEquiv (conjContinuousMulEquiv G γ)

omit [CompactSpace G] in
/-- `σ_γ` sends `δ_g` to `δ_{γ g γ⁻¹}`. -/
public theorem conjRingEquiv_of (g : G) :
    conjRingEquiv (Λ := Λ) γ (of g) = of (conjContinuousMulEquiv G γ g) := by
  rw [conjRingEquiv, mapRingEquiv_apply, map_of]
  rfl

/-- The `σ_γ`-semilinear map `x ↦ σ_γ(x) w` on `Λ[[G]]`, as a morphism `Λ[[G]] ⟶ σ_γ^* Λ[[G]]`. -/
public def twistedMulRight (w : CompletedGroupAlgebra Λ G) :
    ModuleCat.of (CompletedGroupAlgebra Λ G) (CompletedGroupAlgebra Λ G) ⟶
      (twistFunctor Λ (conjContinuousMulEquiv G γ)).obj
        (ModuleCat.of (CompletedGroupAlgebra Λ G) (CompletedGroupAlgebra Λ G)) :=
  ModuleCat.ofHom (X := CompletedGroupAlgebra Λ G)
    (Y := (twistFunctor Λ (conjContinuousMulEquiv G γ)).obj
      (ModuleCat.of (CompletedGroupAlgebra Λ G) (CompletedGroupAlgebra Λ G)))
    { toFun := fun x => (conjRingEquiv γ x * w : CompletedGroupAlgebra Λ G)
      map_add' := fun x y => by
        change conjRingEquiv γ (x + y) * w = conjRingEquiv γ x * w + conjRingEquiv γ y * w
        rw [map_add, add_mul]
      map_smul' := fun a x => by
        change conjRingEquiv γ (a * x) * w = conjRingEquiv γ a * (conjRingEquiv γ x * w)
        rw [map_mul, mul_assoc] }

omit [CompactSpace G] in
/-- `twistedMulRight γ w` sends `x` to `σ_γ(x) w`. -/
public theorem twistedMulRight_apply (w x : CompletedGroupAlgebra Λ G) :
    (twistedMulRight γ w).hom x = (conjRingEquiv γ x * w : CompletedGroupAlgebra Λ G) :=
  rfl

variable (Λ) in
/-- The components of the lift of the action of `γ` to the Koszul resolution. -/
public def koszulLiftF (w : CompletedGroupAlgebra Λ G) : ∀ i : ℕ,
    (koszulComplex Λ σ).X i ⟶
      (((twistFunctor Λ (conjContinuousMulEquiv G γ)).mapHomologicalComplex _).obj
        (koszulComplex Λ σ)).X i
  | 0 => twistedMulRight γ 1
  | 1 => twistedMulRight γ w
  | _ + 2 => 0

/-- **The lift of the action of `γ` to the Koszul resolution**, for `w` with
`(σ - 1) w = γ σ γ⁻¹ - 1`. -/
public def koszulLift (hgen : GeneratesQuotients σ) (w : CompletedGroupAlgebra Λ G)
    (hw : ((of σ : CompletedGroupAlgebra Λ G) - 1) * w =
      of (conjContinuousMulEquiv G γ σ) - 1) :
    koszulComplex Λ σ ⟶
      ((twistFunctor Λ (conjContinuousMulEquiv G γ)).mapHomologicalComplex _).obj
        (koszulComplex Λ σ) where
  f := koszulLiftF Λ σ γ w
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    rcases j with _ | j
    · rw [Functor.mapHomologicalComplex_obj_d, koszulComplex_d_one_zero]
      refine ModuleCat.hom_ext (LinearMap.ext fun (x : CompletedGroupAlgebra Λ G) => ?_)
      change (conjRingEquiv γ x * w) * ((of σ : CompletedGroupAlgebra Λ G) - 1) =
        conjRingEquiv γ (x * ((of σ : CompletedGroupAlgebra Λ G) - 1)) * 1
      rw [mul_one, map_mul, map_sub, map_one, conjRingEquiv_of, ← hw, mul_assoc,
        sub_one_mul_comm hgen]
    · exact (show IsZero (ModuleCat.of (CompletedGroupAlgebra Λ G) PUnit.{u + 1}) from
        ModuleCat.isZero_of_subsingleton _).eq_of_src _ _

section Comm

variable {σ} (hgen : GeneratesQuotients σ) {n : ℕ} (hn : n ≠ 0)
  (hpow : ∀ p : ℕ, p.Prime → p ∣ n → HasPrimePowerQuotients σ p) (hΛ : ∀ a : Λ, n • a = 0)
  (hV : IsSmoothFor G (TrivialRep Γ Λ)) (w : CompletedGroupAlgebra Λ G)
  (hw : ((of σ : CompletedGroupAlgebra Λ G) - 1) * w = of (conjContinuousMulEquiv G γ σ) - 1)

/-- **The lift lifts the action of `γ`.** -/
public theorem koszulLift_comm :
    koszulLift σ γ hgen w hw ≫
        (twistResolution (c := conjContinuousMulEquiv G γ)
          (koszulResolution hgen hn hpow hΛ hV)).π =
      (koszulResolution hgen hn hpow hΛ hV).π ≫
        (ChainComplex.single₀ _).map (conjActionHom Λ hV γ) := by
  apply HomologicalComplex.to_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  refine ModuleCat.hom_ext (LinearMap.ext fun (x : CompletedGroupAlgebra Λ G) => ?_)
  show (koszulAugmentationLinear Λ hV (conjRingEquiv γ x * 1) : TrivialRep Γ Λ) =
    (γ • (show TrivialRep Γ Λ from koszulAugmentationLinear Λ hV x) : TrivialRep Γ Λ)
  rw [TrivialRep.smul_def, mul_one, koszulAugmentationLinear_apply,
    koszulAugmentationLinear_apply, conjRingEquiv, augmentation_mapRingEquiv]

end Comm

/-! ### The coinvariants of `Λ[[G]]` -/

section CoinvariantsSelf

omit [G.Normal] [CompactSpace G] in
/-- The augmentation kills `I Λ[[G]]`. -/
public theorem augmentation_eq_zero_of_mem {a : CompletedGroupAlgebra Λ G}
    (ha : a ∈ augmentationSubmodule Λ G (CompletedGroupAlgebra Λ G)) : augmentation a = 0 := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, d, rfl⟩ := hx
    rw [smul_eq_mul, map_mul, hc, zero_mul]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [smul_eq_mul, map_mul, hx, mul_zero]

/-- The augmentation on the coinvariants of `Λ[[G]]`. -/
public def coinvariantsSelfToRing :
    (coinvariantsFunctor Λ G).obj
        (ModuleCat.of (CompletedGroupAlgebra Λ G) (CompletedGroupAlgebra Λ G)) →ₗ[Λ] Λ where
  toFun x := Quotient.liftOn' x (fun a => augmentation a) fun a b hab => by
    have h : -a + b ∈ augmentationSubmodule Λ G (CompletedGroupAlgebra Λ G) :=
      QuotientAddGroup.leftRel_apply.mp hab
    have h0 := augmentation_eq_zero_of_mem h
    rwa [map_add, map_neg, neg_add_eq_zero] at h0
  map_add' x y := by
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact map_add (augmentation (Λ := Λ) (G := G)) a b
  map_smul' c x := by
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change augmentation ((const c : CompletedGroupAlgebra Λ G) * a) = c * augmentation a
    rw [map_mul, augmentation_const]

omit [G.Normal] [CompactSpace G] in
/-- `coinvariantsSelfToRing` sends the class of `a` to the augmentation `ε(a)`. -/
public theorem coinvariantsSelfToRing_mk (a : CompletedGroupAlgebra Λ G) :
    coinvariantsSelfToRing (Λ := Λ) (G := G) (Submodule.Quotient.mk a) = augmentation a :=
  rfl

/-- `Λ[[G]] / I = Λ`: the coinvariants of `Λ[[G]]` are `Λ`, through the augmentation. -/
public def coinvariantsSelfLinearEquiv :
    (coinvariantsFunctor Λ G).obj
        (ModuleCat.of (CompletedGroupAlgebra Λ G) (CompletedGroupAlgebra Λ G)) ≃ₗ[Λ] Λ :=
  LinearEquiv.ofBijective (coinvariantsSelfToRing (Λ := Λ) (G := G))
    ⟨fun x y hxy => by
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [coinvariantsSelfToRing_mk, coinvariantsSelfToRing_mk] at hxy
      change Submodule.Quotient.mk a = Submodule.Quotient.mk b
      rw [Submodule.Quotient.eq, ← mul_one (a - b), ← smul_eq_mul]
      exact smul_mem_augmentationSubmodule (by rw [map_sub, hxy, sub_self]) _,
    fun c => ⟨Submodule.Quotient.mk (const c : CompletedGroupAlgebra Λ G),
      augmentation_const c⟩⟩

omit [G.Normal] [CompactSpace G] in
/-- `coinvariantsSelfLinearEquiv` sends the class of `a` to the augmentation `ε(a)`. -/
public theorem coinvariantsSelfLinearEquiv_mk (a : CompletedGroupAlgebra Λ G) :
    coinvariantsSelfLinearEquiv (Λ := Λ) (G := G) (Submodule.Quotient.mk a) = augmentation a :=
  rfl

end CoinvariantsSelf

/-! ### The trace -/

section Trace

open CategoryTheory.FilteredDerived

variable (hgen : GeneratesQuotients σ) {n : ℕ} (hn : n ≠ 0)
  (hpow : ∀ p : ℕ, p.Prime → p ∣ n → HasPrimePowerQuotients σ p) (hΛ : ∀ a : Λ, n • a = 0)
  (hV : IsSmoothFor G (TrivialRep Γ Λ)) (w : CompletedGroupAlgebra Λ G)
  (hw : ((of σ : CompletedGroupAlgebra Λ G) - 1) * w = of (conjContinuousMulEquiv G γ σ) - 1)

/-- The coinvariants of the Koszul resolution, a chain complex of `Λ`-modules. -/
public abbrev koszulCoinvariants : ChainComplex (ModuleCat.{u} Λ) ℕ :=
  ((coinvariantsFunctor Λ G).mapHomologicalComplex _).obj (koszulComplex Λ σ)

omit [G.Normal] [CompactSpace G] in
/-- The coinvariants of the Koszul resolution vanish in degrees `k ≥ 2`. -/
public theorem koszulCoinvariants_isZero (k : ℕ) (hk : 2 ≤ k) :
    IsZero ((koszulCoinvariants (Λ := Λ) σ).X k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by lia⟩
  exact (coinvariantsFunctor Λ G).map_isZero
    (show IsZero (ModuleCat.of (CompletedGroupAlgebra Λ G) PUnit.{u + 1}) from
      ModuleCat.isZero_of_subsingleton _)

/-- The terms of the coinvariants of the Koszul resolution in degrees `0` and `1` are `Λ`. -/
public def koszulCoinvariantsXEquiv : ∀ k : ℕ, k ≤ 1 →
    ((koszulCoinvariants (Λ := Λ) σ).X k ≃ₗ[Λ] Λ)
  | 0, _ => coinvariantsSelfLinearEquiv
  | 1, _ => coinvariantsSelfLinearEquiv

omit [G.Normal] [CompactSpace G] in
/-- The terms of the coinvariants of the Koszul resolution are finite `Λ`-modules. -/
public theorem koszulCoinvariants_finite (k : ℕ) :
    Module.Finite Λ ((koszulCoinvariants (Λ := Λ) σ).X k) := by
  rcases le_or_gt k 1 with hk | hk
  · exact Module.Finite.equiv (koszulCoinvariantsXEquiv σ k hk).symm
  · exact (finite_projective_of_isZero (koszulCoinvariants_isZero σ k hk)).2

omit [G.Normal] [CompactSpace G] in
/-- The terms of the coinvariants of the Koszul resolution are projective `Λ`-modules. -/
public theorem koszulCoinvariants_projective (k : ℕ) :
    Module.Projective Λ ((koszulCoinvariants (Λ := Λ) σ).X k) := by
  rcases le_or_gt k 1 with hk | hk
  · exact Module.Projective.of_equiv (koszulCoinvariantsXEquiv σ k hk).symm
  · exact (finite_projective_of_isZero (koszulCoinvariants_isZero σ k hk)).1

/-- The endomorphism of the coinvariants of the Koszul resolution induced by the lift. -/
public abbrev koszulCoinvariantsMap :
    koszulCoinvariants (Λ := Λ) σ ⟶ koszulCoinvariants σ :=
  ((coinvariantsFunctor Λ G).mapHomologicalComplex _).map (koszulLift σ γ hgen w hw) ≫
    ((Functor.mapHomologicalComplexCompIso
      (twistCoinvariantsIso Λ (conjContinuousMulEquiv G γ)) _).app (koszulComplex Λ σ)).hom

omit [CompactSpace G] in
/-- The lift acts on the coinvariants `Λ` of `Λ[[G]]` in degree `k` by right multiplication with
`ε(w_k)`. -/
public theorem koszulCoinvariantsMap_f_apply (k : ℕ) (hk : k ≤ 1)
    (a : CompletedGroupAlgebra Λ G) :
    koszulCoinvariantsXEquiv σ k hk
        (((koszulCoinvariantsMap σ γ hgen w hw).f k).hom
          ((koszulCoinvariantsXEquiv σ k hk).symm (augmentation a))) =
      augmentation a * augmentation (if k = 0 then 1 else w) := by
  rcases k with _ | _ | k
  · have h1 : (koszulCoinvariantsXEquiv σ 0 hk).symm (augmentation a) =
        Submodule.Quotient.mk (show ((koszulComplex Λ σ).X 0 : Type u) from a) :=
      (LinearEquiv.symm_apply_eq _).2 (coinvariantsSelfLinearEquiv_mk a).symm
    have h2 : ((koszulCoinvariantsMap σ γ hgen w hw).f 0).hom
        (Submodule.Quotient.mk (show ((koszulComplex Λ σ).X 0 : Type u) from a)) =
        Submodule.Quotient.mk (show ((koszulComplex Λ σ).X 0 : Type u) from
          conjRingEquiv γ a * 1) := by
      simp only [koszulCoinvariantsMap, HomologicalComplex.comp_f,
        Functor.mapHomologicalComplex_map_f, ModuleCat.hom_comp]
      rfl
    rw [h1, h2, ite_eq_left rfl]
    refine (coinvariantsSelfLinearEquiv_mk (conjRingEquiv γ a * 1)).trans ?_
    rw [map_mul, conjRingEquiv, augmentation_mapRingEquiv]
  · have h1 : (koszulCoinvariantsXEquiv σ 1 hk).symm (augmentation a) =
        Submodule.Quotient.mk (show ((koszulComplex Λ σ).X 1 : Type u) from a) :=
      (LinearEquiv.symm_apply_eq _).2 (coinvariantsSelfLinearEquiv_mk a).symm
    have h2 : ((koszulCoinvariantsMap σ γ hgen w hw).f 1).hom
        (Submodule.Quotient.mk (show ((koszulComplex Λ σ).X 1 : Type u) from a)) =
        Submodule.Quotient.mk (show ((koszulComplex Λ σ).X 1 : Type u) from
          conjRingEquiv γ a * w) := by
      simp only [koszulCoinvariantsMap, HomologicalComplex.comp_f,
        Functor.mapHomologicalComplex_map_f, ModuleCat.hom_comp]
      rfl
    rw [h1, h2, ite_eq_right (by lia : 0 + 1 ≠ 0)]
    refine (coinvariantsSelfLinearEquiv_mk (conjRingEquiv γ a * w)).trans ?_
    rw [map_mul, conjRingEquiv, augmentation_mapRingEquiv]
  · lia

omit [CompactSpace G] in
/-- The trace of the lift on the coinvariants in degree `k ≤ 1`. -/
public theorem projectiveModuleTrace_koszulCoinvariantsMap (k : ℕ) (hk : k ≤ 1) :
    haveI := koszulCoinvariants_finite (Λ := Λ) σ k
    haveI := koszulCoinvariants_projective (Λ := Λ) σ k
    Stacks.Trace.projectiveModuleTrace Λ ((koszulCoinvariants σ).X k)
        ((koszulCoinvariantsMap σ γ hgen w hw).f k).hom =
      additiveCommutatorQuotientMk Λ (augmentation (if k = 0 then 1 else w)) := by
  have := koszulCoinvariants_finite (Λ := Λ) σ k
  have := koszulCoinvariants_projective (Λ := Λ) σ k
  set E := koszulCoinvariantsXEquiv (Λ := Λ) σ k hk
  have hconj : E.toLinearMap ∘ₗ ((koszulCoinvariantsMap σ γ hgen w hw).f k).hom ∘ₗ
      E.symm.toLinearMap = mulRightEnd (augmentation (if k = 0 then 1 else w)) := by
    refine LinearMap.ext fun (c : Λ) => ?_
    have hc : c = augmentation (const c : CompletedGroupAlgebra Λ G) :=
      (augmentation_const (Λ := Λ) (G := G) c).symm
    rw [mulRightEnd_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.coe_coe]
    conv_lhs => rw [hc]
    rw [koszulCoinvariantsMap_f_apply, ← hc]
  rw [← projectiveModuleTrace_conj Λ E, hconj, projectiveModuleTrace_mulRightEnd]

include hgen hn hpow hΛ hw in
/-- **The trace of `γ` on the derived coinvariants of the trivial module**:
`Tr(γ | LH₀(G, Λ)) = 1 - ε(w)` in `Λ^♮`, where `(σ - 1) w = γ σ γ⁻¹ - 1`. -/
public theorem perfectDerivedTrace_trivialRep
    (hperf : StacksDraft.Perfect.IsPerfect
      (derivedCoinvariants (toCompletedGroupAlgebraModuleCat Λ hV))) :
    perfectDerivedTrace Λ ⟨_, hperf⟩ (derivedCoinvariantsAction Λ hV γ) =
      additiveCommutatorQuotientMk Λ (1 - augmentation w) := by
  set K := koszulResolution hgen hn hpow hΛ hV
  have hP := finiteProjectiveComplex_extend (koszulCoinvariants_finite (Λ := Λ) σ)
    (koszulCoinvariants_projective σ) (koszulCoinvariants_isZero σ)
  have key := derivedCoinvariantsTwistedMap_eq (conjActionHom Λ hV γ) K
    (koszulLift σ γ hgen w hw) (koszulLift_comm γ hgen hn hpow hΛ hV w hw)
  rw [perfectDerivedTrace_eq_alternatingTrace Λ ⟨_, hperf⟩ _ _ hP
    (derivedCoinvariantsIsoOfResolution K).symm
    (HomologicalComplex.extendMap (koszulCoinvariantsMap σ γ hgen w hw)
      (ComplexShape.embeddingUpIntLE 0)) ?_]
  · rw [alternatingTrace_extendMap (koszulCoinvariants_finite (Λ := Λ) σ)
      (koszulCoinvariants_projective σ) (koszulCoinvariants_isZero σ),
      projectiveModuleTrace_koszulCoinvariantsMap σ γ hgen w hw 0
      (by lia), projectiveModuleTrace_koszulCoinvariantsMap σ γ hgen w hw 1 le_rfl, ite_eq_left rfl,
      ite_eq_right one_ne_zero, map_one, map_sub]
  · rw [Iso.symm_hom, Iso.symm_inv]
    show _ = (derivedCoinvariantsIsoOfResolution K).inv ≫ derivedCoinvariantsTwistedMap
      (conjActionHom Λ hV γ) ≫ (derivedCoinvariantsIsoOfResolution K).hom
    rw [key, ← Functor.map_comp]
    congr 1
    rw [coinvariantsComplexMap, twistCoinvariantsComplexIso, Functor.mapIso_hom,
      ← Functor.map_comp]
    rfl

end Trace

end Stacks.GroupHomology.Procyclic

end
