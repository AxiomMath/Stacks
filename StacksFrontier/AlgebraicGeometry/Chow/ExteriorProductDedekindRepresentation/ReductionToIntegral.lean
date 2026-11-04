module

public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekindRepresentation.SecondVariable

/-!
# Reduction to integral test schemes, and the case of a generic point of the base

The reduction of the cap product with a bivariant class over a Dedekind base to fundamental classes
of integral schemes, the exterior product with such a fundamental class, and the case of an
integral scheme dominating a component of the base.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Transport lemmas -/

/-- The transport of the class of a cycle along an equality of structure morphisms is the class of
a cycle with the same coefficients. -/
theorem exists_chowGroupCongr_mk (C : ChowSituation.{u}) {T : Scheme.{u}} {q q' : T ⟶ C.S}
    [LocallyOfFiniteType q] [LocallyOfFiniteType q'] (h : q = q') (k : ℤ) (b : CycleGroup C q k) :
    ∃ b' : CycleGroup C q' k, b'.1 = b.1 ∧
      chowGroupCongr C h k (QuotientAddGroup.mk' (rationalEquivalences C q k) b) =
        QuotientAddGroup.mk' (rationalEquivalences C q' k) b' := by
  subst h
  exact ⟨b, rfl, rfl⟩

/-! ### Reduction to integral test schemes -/

section Reduction

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (n p : ℤ)
  (c : BivariantClass C G sX (𝟙 C.S) sX (Category.comp_id sX) p) (a : CycleGroup C sX n)

/-- **The cap product on a coproduct of integral schemes.** Let `γ` be a cycle on a coproduct
`∐ Zᵢ` of integral schemes over the base which is `eᵢ [Zᵢ]` on the summand `Zᵢ`. If capping with
`c` is the exterior product with `a` on the fundamental class of every integral scheme, then it is
so on `γ`: both classes on `X ×_S ∐ Zᵢ` are determined by their restrictions to the open and
closed pieces `X ×_S Zᵢ`, and there they are `eᵢ` times the two sides of the hypothesis. -/
theorem cap_mk_sigma_eq_chowGroupDegreeEquiv
    (hint : ∀ {T : Scheme.{u}} (t : T ⟶ C.S) [LocallyOfFiniteType t] [IsIntegral T] (k : ℤ),
      c.cap t k (chowGroupCongr C (Category.comp_id t).symm k
          (QuotientAddGroup.mk' (rationalEquivalences C t k) (fundamentalCycle C t k))) ≍
        QuotientAddGroup.mk' (rationalEquivalences C (pullback.fst sX t ≫ sX) (n + k - 1))
          (exteriorProductDedekindCycles C sX t n k a (fundamentalCycle C t k)))
    {I : Type u} (Z : I → Scheme.{u}) [∀ i, IsIntegral (Z i)] (h : (∐ Z : Scheme.{u}) ⟶ C.S)
    [LocallyOfFiniteType h] [∀ i, LocallyOfFiniteType (Sigma.ι Z i ≫ h)] (k : ℤ) (e : I → ℤ)
    (γ : CycleGroup C h k)
    (hγ : ∀ i z, γ.1 (Sigma.ι Z i z) = (e i • fundamentalCycle C (Sigma.ι Z i ≫ h) k).1 z)
    (γ' : CycleGroup C (h ≫ 𝟙 C.S) k) (hγ' : γ'.1 = γ.1) (hdeg : n + k - 1 = k - p) :
    c.cap h k (QuotientAddGroup.mk' _ γ') = chowGroupDegreeEquiv C _ hdeg
      (QuotientAddGroup.mk' _ (exteriorProductDedekindCycles C sX h n k a γ)) := by
  rw [← sub_eq_zero]
  refine eq_zero_of_chowGroupRestrict_eq_zero C (pullback.fst sX h ≫ sX)
    (fun i ↦ pullback.fst sX (Sigma.ι Z i ≫ h) ≫ sX)
    (fun i ↦ testBaseChangeMapOfEq sX h (Sigma.ι Z i) (Sigma.ι Z i ≫ h) rfl)
    (fun i ↦ testBaseChangeMapOfEq_fst_assoc _ _ _ _ _ _)
    (isClopenDecomposition_of_isOpenImmersion_cover _
      (exists_mem_range_testBaseChangeMapOfEq_sigmaι C sX Z h)
      (pairwise_disjoint_range_testBaseChangeMapOfEq_sigmaι C sX Z h))
    (k - p) _ fun i ↦ ?_
  rw [map_sub, sub_eq_zero]
  rw [BivariantClass.cap_chowGroupRestrict C G sX (𝟙 C.S) sX (Category.comp_id sX) p c
    h (Sigma.ι Z i) (Sigma.ι Z i ≫ h) rfl _
    (isPullback_testBaseChangeMapOfEq _ _ _ _ _) (testBaseChangeMapOfEq_fst _ _ _ _ _) k
    (by simp)]
  rw [chowGroupRestrict_chowGroupDegreeEquiv, chowGroupRestrict_mk C (pullback.fst sX h ≫ sX),
    cycleGroupRestrict_exteriorProductDedekindCycles C sX h (Sigma.ι Z i) (Sigma.ι Z i ≫ h) rfl
      n k a γ]
  obtain ⟨f', hf', hfmk⟩ := exists_chowGroupCongr_mk C (Category.comp_id (Sigma.ι Z i ≫ h)).symm
    k (fundamentalCycle C (Sigma.ι Z i ≫ h) k)
  have hγi : cycleGroupRestrict C h (Sigma.ι Z i ≫ h) (Sigma.ι Z i) rfl k γ =
      e i • fundamentalCycle C (Sigma.ι Z i ≫ h) k := by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ ?_)
    rw [cycleGroupRestrict_apply, hγ i z]
  have hγi' : chowGroupRestrict C (h ≫ 𝟙 C.S) ((Sigma.ι Z i ≫ h) ≫ 𝟙 C.S) (Sigma.ι Z i)
      (by simp) k (QuotientAddGroup.mk' _ γ') = e i • QuotientAddGroup.mk' _ f' := by
    rw [chowGroupRestrict_mk, ← map_zsmul]
    congr 1
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ ?_)
    rw [cycleGroupRestrict_apply]
    have h1 : γ'.1 (Sigma.ι Z i z) = γ.1 (Sigma.ι Z i z) := by rw [hγ']
    have h2 : (e i • f').1 z = e i * f'.1 z := rfl
    rw [h1, h2, hf', hγ i z]
    rfl
  rw [hγi', map_zsmul, hγi, map_zsmul, map_zsmul, map_zsmul]
  congr 1
  have h := hint (Sigma.ι Z i ≫ h) k
  rw [hfmk] at h
  exact ((chowGroupDegreeEquiv_eq_iff_heq C _ hdeg _ _).2 h.symm).symm

/-- **The exterior product with a cycle presented on a coproduct of point closures.** Let
`vᵢ : Zᵢ ⟶ U` be closed immersions of integral schemes with `∐ vᵢ` proper, sending the generic
point of `Zᵢ` to `ptᵢ` with `pt` injective, let `b` be a cycle on `U` supported on the `ptᵢ`, and
let `γ` be the cycle on `∐ Zᵢ` which is `b(ptᵢ)` at the generic point of `Zᵢ` and zero
elsewhere. Then `(1 × ∐ vᵢ)_*(a × γ) = a × b`. -/
theorem properPushforward_exteriorProductDedekindCycles_sigmaDesc {U : Scheme.{u}} (u : U ⟶ C.S)
    [LocallyOfFiniteType u] (k : ℤ) (b : CycleGroup C u k) {I : Type u} (Z : I → Scheme.{u})
    [∀ i, IsIntegral (Z i)] (v : ∀ i, Z i ⟶ U) [∀ i, IsClosedImmersion (v i)]
    [IsProper (Sigma.desc v)] (pt : I → U) (hpt : Function.Injective pt)
    (hb : Function.support (b.1 : U → ℤ) ⊆ Set.range pt)
    (hvgen : ∀ i, (v i).base (genericPoint (Z i)) = pt i)
    (γ : CycleGroup C (Sigma.desc v ≫ u) k)
    (hγ : ∀ i z, γ.1 (Sigma.ι Z i z) = open Classical in
      if z = genericPoint (Z i) then b.1 (pt i) else 0) :
    properPushforward C (pullback.fst sX (Sigma.desc v ≫ u) ≫ sX)
        (pullback.fst sX u ≫ sX) (testBaseChangeMapOfEq sX u (Sigma.desc v) (Sigma.desc v ≫ u) rfl)
        (by rw [testBaseChangeMapOfEq_fst_assoc]) (n + k - 1)
        (exteriorProductDedekindCycles C sX (Sigma.desc v ≫ u) n k a γ) =
      exteriorProductDedekindCycles C sX u n k a b := by
  classical
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ ?_)
  rw [properPushforward_exteriorProductDedekindCycles_sigmaDesc_apply C sX u n k Z v a γ z]
  refine (exteriorProductDedekindCycles_apply_eq_finsum_of_points C sX u n k a b pt hpt hb _
    (fun i y ↦ ?_) z).symm
  by_cases hy : y ∈ Set.range (v i).base
  · obtain ⟨t, rfl⟩ := hy
    rw [properPushforward_apply_image_of_isClosedImmersion, cycleGroupRestrict_apply, hγ]
    by_cases ht : t = genericPoint (Z i)
    · rw [if_pos ht, if_pos (by rw [ht, hvgen])]
    · rw [if_neg ht, if_neg]
      intro h
      exact ht ((v i).isClosedEmbedding.injective (h.trans (hvgen i).symm))
  · rw [properPushforward_apply_of_notMem_range C _ _ (v i) _ k _ hy, if_neg]
    rintro rfl
    exact hy ⟨_, hvgen i⟩

/-- **The reduction to integral test schemes.** If capping with `c ∈ A^p(X → S)` is the exterior
product with the `n`-cycle `a` on the fundamental class of every integral scheme locally of finite
type over the base, then it is the exterior product with `a` on every cycle of every scheme
locally of finite type over the base.

This is the argument of Stacks 02UC. A `k`-cycle `b` on `U` is the pushforward along the proper
morphism `π : ∐ Zᵢ ⟶ U` from the reduced closures of the points of its support of the cycle `γ`
which is `b(i)[Zᵢ]` on the summand `Zᵢ`. Capping commutes with `π_*`, and so does the exterior
product, by `Stacks.Chow.properPushforward_exteriorProductDedekindCycles_sigmaDesc`. On
`X ×_S ∐ Zᵢ` the two classes agree by `Stacks.Chow.cap_mk_sigma_eq_chowGroupDegreeEquiv`. -/
theorem cap_heq_exteriorProductDedekindCycles_of_forall_isIntegral (hnp : n = 1 - p)
    (hint : ∀ {T : Scheme.{u}} (t : T ⟶ C.S) [LocallyOfFiniteType t] [IsIntegral T] (k : ℤ),
      c.cap t k (chowGroupCongr C (Category.comp_id t).symm k
          (QuotientAddGroup.mk' (rationalEquivalences C t k) (fundamentalCycle C t k))) ≍
        QuotientAddGroup.mk' (rationalEquivalences C (pullback.fst sX t ≫ sX) (n + k - 1))
          (exteriorProductDedekindCycles C sX t n k a (fundamentalCycle C t k)))
    {U : Scheme.{u}} (u : U ⟶ C.S) [LocallyOfFiniteType u] (k : ℤ) (b : CycleGroup C u k) :
    c.cap u k (chowGroupCongr C (Category.comp_id u).symm k
        (QuotientAddGroup.mk' (rationalEquivalences C u k) b)) ≍
      QuotientAddGroup.mk' (rationalEquivalences C (pullback.fst sX u ≫ sX) (n + k - 1))
        (exteriorProductDedekindCycles C sX u n k a b) := by
  classical
  have hdeg : n + k - 1 = k - p := by omega
  -- the presentation of `b`
  let Z : ↥(Function.support (b.1 : U → ℤ)) → Scheme.{u} := fun i ↦
    (integralComponentAt (i : U)).subscheme
  let v : ∀ i, Z i ⟶ U := fun i ↦ (integralComponentAt (i : U)).subschemeι
  have _ : ∀ i, IsIntegral (Z i) := fun i ↦ isIntegral_integralComponentAt _
  have _ : IsProper (Sigma.desc v) :=
    isProper_sigmaDesc_of_locallyFinite Z v (locallyFinite_range_subschemeι_support C u k b)
  have hvgen : ∀ i, (v i).base (genericPoint (Z i)) = (i : U) := fun i ↦
    subschemeι_genericPoint_integralComponentAt (i : U)
  have hdim : ∀ i, relativeDimension C.dimensionFunction (Sigma.ι Z i ≫ Sigma.desc v ≫ u)
      (genericPoint (Z i)) = k := fun i ↦ by
    rw [← Category.assoc, Sigma.ι_desc, relativeDimension_comp_closedImmersion, hvgen]
    exact (mem_cyclesOfDimension_iff_forall_point C u k b.1).1 b.2 _ i.2
  obtain ⟨γ, hγ⟩ := exists_cycleGroup_of_sigma C Z (Sigma.desc v ≫ u)
    (fun i ↦ Sigma.ι Z i ≫ Sigma.desc v ≫ u) (fun i ↦ rfl) k
    (fun i ↦ b.1 (i : U) • fundamentalCycle C (Sigma.ι Z i ≫ Sigma.desc v ≫ u) k)
  have hγval : ∀ i (z : Z i), γ.1 (Sigma.ι Z i z) =
      if z = genericPoint (Z i) then b.1 (i : U) else 0 := fun i z ↦ by
    rw [hγ i z]
    show b.1 (i : U) * (fundamentalCycle C (Sigma.ι Z i ≫ Sigma.desc v ≫ u) k).1 z = _
    rw [fundamentalCycle_eq_single C _ genericPoints_eq_singleton (hdim i) (Field.toIsField _)]
    by_cases hz : z = genericPoint (Z i) <;>
      simp [Function.locallyFinsuppWithin.single_apply, hz]
  -- `π_*γ = b`
  have hres : ∀ x : (∐ Z : Scheme.{u}),
      Function.Bijective (((Sigma.desc v).residueFieldMap x).hom) := by
    have _ : ∀ i, SurjectiveOnStalks (v i) := fun i ↦ inferInstance
    have _ : SurjectiveOnStalks (Sigma.desc v) := surjectiveOnStalks_sigmaDesc Z v
    exact fun x ↦ bijective_residueFieldMap_of_surjective_stalkMap _ x
      ((Sigma.desc v).stalkMap_surjective x)
  have hpush : properPushforward C (Sigma.desc v ≫ u) u (Sigma.desc v) rfl k γ = b := by
    refine properPushforward_eq_of_support_section C u (Sigma.desc v ≫ u) (Sigma.desc v) rfl k
      hres b γ (fun i ↦ Sigma.ι Z i (genericPoint (Z i))) (fun i ↦ ?_) (fun i ↦ ?_)
      (fun x hx ↦ ?_)
    · rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
      exact hvgen i
    · rw [hγval, if_pos rfl]
    · obtain ⟨i, z, rfl⟩ := exists_mem_range_sigmaι Z x
      rw [hγval] at hx
      split_ifs at hx with hz
      · exact ⟨i, by rw [hz]⟩
      · exact absurd rfl hx
  -- the cap side through the pushforward
  obtain ⟨b', hb', hbmk⟩ := exists_chowGroupCongr_mk C (Category.comp_id u).symm k b
  obtain ⟨γ', hγ', -⟩ :=
    exists_chowGroupCongr_mk C (Category.comp_id (Sigma.desc v ≫ u)).symm k γ
  have hpush' : properPushforward C ((Sigma.desc v ≫ u) ≫ 𝟙 C.S) (u ≫ 𝟙 C.S) (Sigma.desc v)
      (by simp) k γ' = b' := by
    refine Subtype.ext ?_
    rw [properPushforward_val_congr C (Category.comp_id _) (Category.comp_id u) _ _ rfl γ' γ
      hγ', hpush, hb']
  have hpp : ProperPushforwardDescends C := properPushforwardDescends C
  rw [hbmk, ← hpush', ← properChowPushforward_mk C _ _ (Sigma.desc v) _ k (hpp _ _ _ _ _),
    c.cap_properChowPushforward hpp u (Sigma.desc v) (Sigma.desc v ≫ u) rfl
      (testBaseChangeMapOfEq sX u (Sigma.desc v) (Sigma.desc v ≫ u) rfl)
      (testBaseChangeMapOfEq_fst _ _ _ _ _) (testBaseChangeMapOfEq_snd _ _ _ _ _) k,
    cap_mk_sigma_eq_chowGroupDegreeEquiv C G sX n p c a hint Z (Sigma.desc v ≫ u) k
      (fun i ↦ b.1 (i : U)) γ hγ γ' hγ' hdeg,
    properChowPushforward_chowGroupDegreeEquiv C _ _ _ _ hdeg (hpp _ _ _ _ _),
    properChowPushforward_mk,
    properPushforward_exteriorProductDedekindCycles_sigmaDesc C sX n a u k b Z v Subtype.val
      Subtype.val_injective (fun y hy ↦ ⟨⟨y, hy⟩, rfl⟩) hvgen γ hγval]
  exact chowGroupDegreeEquiv_heq C _ _ _

end Reduction

/-! ### The exterior product with the fundamental class of an integral scheme -/

section Fundamental

variable (C : ChowSituation.{u}) {X T : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  [IsIntegral T] (t : T ⟶ C.S) [LocallyOfFiniteType t] (n : ℤ)

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType t] in
/-- The product `closure {x} ×_S T` with the whole of an integral scheme `T` is the inverse image
of the reduced closure of `x` under the first projection. -/
theorem exteriorProductIdeal_genericPoint (x : X) :
    exteriorProductIdeal sX t x (genericPoint T) =
      (integralComponentAt x).comap (pullback.fst sX t) := by
  have htop : Closeds.closure ({genericPoint T} : Set T) = ⊤ :=
    SetLike.ext' (by rw [Closeds.coe_closure, (genericPoint_spec T).def]; rfl)
  rw [exteriorProductIdeal, htop, Scheme.IdealSheafData.vanishingIdeal_top,
    Scheme.nilradical_eq_bot, Scheme.IdealSheafData.comap_bot, sup_bot_eq]
  rfl

/-- **The exterior product with the fundamental class of an integral scheme**, coefficientwise:
`(a × [T])(z)` is the sum over the points `x` of `X` of `a(x)` times the multiplicity of `z` in
the inverse image of `closure {x}` under `pr_X : X ×_S T ⟶ X`, the terms being those of the
defining rule of Stacks section 42.63. -/
theorem exteriorProductDedekindCycles_fundamentalCycle_apply (m : ℤ)
    (hm : relativeDimension C.dimensionFunction t (genericPoint T) = m) (a : CycleGroup C sX n)
    (z : (pullback sX t : Scheme.{u})) :
    (exteriorProductDedekindCycles C sX t n m a (fundamentalCycle C t m)).1 z =
      ∑ᶠ x : X, open Classical in
        if DominatesBaseComponent C sX x ∨ DominatesBaseComponent C t (genericPoint T) then
          a.1 x * closedSubschemeCycleCoeff C (pullback.fst sX t ≫ sX)
            ((integralComponentAt x).comap (pullback.fst sX t)).subschemeι (n + m - 1) z
        else 0 := by
  classical
  have hfund := fundamentalCycle_eq_single C t genericPoints_eq_singleton hm
    (Field.toIsField (T.presheaf.stalk (genericPoint T)))
  rw [exteriorProductDedekindCycles_apply]
  have hinj : Function.Injective fun x : X ↦ (x, genericPoint T) :=
    fun x x' h ↦ (Prod.ext_iff.1 h).1
  have hsupp : Function.support (exteriorProductDedekindTerm C sX t n m a
      (fundamentalCycle C t m) z) ⊆ Set.range fun x : X ↦ (x, genericPoint T) := by
    intro q hq
    refine ⟨q.1, Prod.ext rfl ?_⟩
    by_contra hne
    refine hq ?_
    unfold exteriorProductDedekindTerm
    rw [hfund, Function.locallyFinsuppWithin.single_apply, if_neg (Ne.symm hne)]
    simp
  rw [← finsum_mem_univ (exteriorProductDedekindTerm C sX t n m a (fundamentalCycle C t m) z),
    finsum_mem_inter_support_eq _ Set.univ (Set.range fun x : X ↦ (x, genericPoint T))
      (by rw [Set.univ_inter, Set.inter_eq_right.mpr hsupp]), finsum_mem_range hinj]
  refine finsum_congr fun x ↦ ?_
  unfold exteriorProductDedekindTerm
  rw [hfund, Function.locallyFinsuppWithin.single_apply, if_pos rfl, mul_one]
  split_ifs
  · exact congrArg _ (closedSubschemeCycleCoeff_congr C _
      (exteriorProductIdeal_genericPoint C sX t x) _ z)
  · rfl

/-- **The exterior product with the fundamental class of an integral scheme `T` dominating a
component of the base is flat pullback along the first projection**, coefficientwise:
`(a × [T])(z) = a(pr_X z) · m(z)`, `m` the multiplicity of the flat pullback along
`pr_X : X ×_S T ⟶ X`, which is flat. This is the case of Stacks 0FC4 in which `[T]` dominates. -/
theorem exteriorProductDedekindCycles_fundamentalCycle_apply_of_dominates
    [Flat (pullback.fst sX t)] (hdom : DominatesBaseComponent C t (genericPoint T)) (m : ℤ)
    (hm : relativeDimension C.dimensionFunction t (genericPoint T) = m) (a : CycleGroup C sX n)
    (z : (pullback sX t : Scheme.{u})) :
    (exteriorProductDedekindCycles C sX t n m a (fundamentalCycle C t m)).1 z =
      a.1 ((pullback.fst sX t).base z) * flatPullbackWeight C (pullback.fst sX t ≫ sX)
        (pullback.fst sX t) (n + m - 1) z := by
  classical
  rw [exteriorProductDedekindCycles_fundamentalCycle_apply C sX t n m hm a z]
  simp_rw [if_pos (Or.inr hdom)]
  rw [finsum_eq_single _ ((pullback.fst sX t).base z) fun x hx ↦ by
    rw [closedSubschemeCycleCoeff_comap_integralComponentAt_eq_zero_of_ne C
      (pullback.fst sX t ≫ sX) sX (pullback.fst sX t) x _ (Ne.symm hx), mul_zero]]
  rfl

end Fundamental

/-! ### Capping the fundamental class of an integral scheme over a generic point of the base -/

section FlatCase

variable {C : ChowSituation.{u}} (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (p : ℤ)

/-- The classes of two cycles with the same coefficients, in two equal degrees, are
heterogeneously equal. -/
theorem mk_heq_mk_of_val_eq {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] {k l : ℤ}
    (hkl : k = l) (x : CycleGroup C q k) (y : CycleGroup C q l) (hxy : x.1 = y.1) :
    QuotientAddGroup.mk' (rationalEquivalences C q k) x ≍
      QuotientAddGroup.mk' (rationalEquivalences C q l) y :=
  (chowGroupDegreeEquiv_eq_iff_heq C q hkl _ _).1
    (chowGroupDegreeEquiv_mk_eq_mk_of_val C q hkl x y hxy)

/-- An integral scheme over a base as in section 42.63 whose generic point lies over a generic
point `η` of the base with `δ(η) = 1` is flat over the base of relative dimension `r`, where its
generic point has relative dimension `1 + r`. -/
theorem IsDedekindChowBase.exists_relativeDimension_of_mem_genericPoints_of_dimensionFunction_eq_one
    (hS : IsDedekindChowBase C) {T : Scheme.{u}} [IsIntegral T] (t : T ⟶ C.S)
    [LocallyOfFiniteType t] (hgen : t.base (genericPoint T) ∈ genericPoints C.S)
    (hδ : C.dimensionFunction (t.base (genericPoint T)) = 1) :
    ∃ (_ : Flat t) (r : ℕ), AlgebraicGeometry.RelativeDimension t r ∧
      relativeDimension C.dimensionFunction t (genericPoint T) = 1 + r := by
  have _ : Flat t := hS.flat_of_mem_genericPoints t hgen
  set η := genericPoint T
  have hge : 1 ≤ relativeDimension C.dimensionFunction t η := by
    show 1 ≤ C.dimensionFunction (t.base η) + (Cardinal.toNat (residueTrdeg t η) : ℤ)
    omega
  refine ⟨inferInstance, (relativeDimension C.dimensionFunction t η - 1).toNat, ?_, by omega⟩
  refine relativeDimension_of_flat_of_coheight C t (𝟙 C.S) _ fun w ↦ ?_
  rw [Category.comp_id, relativeDimension_id]
  have hspec : t.base η ⤳ t.base w :=
    ((genericPoint_spec T).specializes (Set.mem_univ w)).map t.continuous
  by_cases heq : t.base η = t.base w
  · rw [← heq, Order.coheight_eq_zero.mpr (isMax_of_mem_genericPoints ⟨_, hgen⟩), zero_add, hδ]
  · rw [hS.coheight_eq_one_of_specializes hspec heq,
      hS.2.1 _ (hS.isClosed_singleton_of_specializes hspec heq)]
    have h1 : (relativeDimension C.dimensionFunction t η - 1).toNat + 1 =
        (relativeDimension C.dimensionFunction t η - 0).toNat := by omega
    rw [add_comm]
    exact_mod_cast h1

/-- **Capping the fundamental class of an integral scheme dominating a one-dimensional component
of the base.** Let `c ∈ A^p(X → S)` with `c ∩ [S]₁` the class of the cycle `a`, and let `T` be
integral over the base with generic point over a generic point `η` of the base with `δ(η) = 1`.
Then `c ∩ [T] = a × [T]`: `T` is flat over the base of some relative dimension `r`, `[T]_{1+r}` is
the flat pullback of `[S]₁`, and on cycles the flat pullback of `c ∩ [S]₁` along
`X ×_S T ⟶ X ×_S S` is `a × [T]`. -/
theorem cap_fundamentalCycle_heq_of_mem_genericPoints_of_dimensionFunction_eq_one
    (hS : IsDedekindChowBase C)
    (c : BivariantClass C G sX (𝟙 C.S) sX (Category.comp_id sX) p) (a : CycleGroup C sX (1 - p))
    (ha : bivariantCapBaseFundamentalClass C G sX p c =
      QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p)) a)
    {T : Scheme.{u}} [IsIntegral T] (t : T ⟶ C.S) [LocallyOfFiniteType t]
    (hgen : t.base (genericPoint T) ∈ genericPoints C.S)
    (hδ : C.dimensionFunction (t.base (genericPoint T)) = 1) (k : ℤ) :
    c.cap t k (chowGroupCongr C (Category.comp_id t).symm k
        (QuotientAddGroup.mk' (rationalEquivalences C t k) (fundamentalCycle C t k))) ≍
      QuotientAddGroup.mk' (rationalEquivalences C (pullback.fst sX t ≫ sX) (1 - p + k - 1))
        (exteriorProductDedekindCycles C sX t (1 - p) k a (fundamentalCycle C t k)) := by
  obtain ⟨_, r, hr, hrd⟩ :=
    hS.exists_relativeDimension_of_mem_genericPoints_of_dimensionFunction_eq_one t hgen hδ
  by_cases hk : k = 1 + r
  swap
  · rw [fundamentalCycle_eq_zero_of_ne C t genericPoints_eq_singleton
      (by rw [hrd]; exact Ne.symm hk),
      map_zero, map_zero, map_zero, map_zero, map_zero]
    exact heq_zero_chowGroup_of_degree_eq C _ (by ring)
  subst hk
  have hdim : schemeDeltaDimension C (𝟙 C.S ≫ 𝟙 C.S) ≤ ((1 : ℤ) : EInt) :=
    hS.schemeDeltaDimension_le_one (𝟙 C.S ≫ 𝟙 C.S)
  have harg : chowGroupCongr C (Category.comp_id t).symm (1 + r)
      (QuotientAddGroup.mk' (rationalEquivalences C t (1 + r)) (fundamentalCycle C t (1 + r))) =
      flatPullbackChow C (t ≫ 𝟙 C.S) (𝟙 C.S ≫ 𝟙 C.S) t (by simp) r hr 1
        (flatPullbackDescends C _ _ _ _ _ _ _) (baseFundamentalChowClass C) := by
    rw [baseFundamentalChowClass, flatPullbackChow_fundamentalChowClass _ _ _ _ _ r _ 1 _ hdim]
    exact chowGroupCongr_fundamentalChowClass C _ _
  set q' := testBaseChangeMapOfEq sX (𝟙 C.S) t t (Category.comp_id t) with hq'
  have sq := isPullback_testBaseChangeMapOfEq sX (𝟙 C.S) t t (Category.comp_id t)
  have hr' : AlgebraicGeometry.RelativeDimension q' r :=
    AlgebraicGeometry.RelativeDimension.of_isPullback sq hr
  have hnat := BivariantClass.flat_naturality_of_eq C G sX (𝟙 C.S) sX (Category.comp_id sX) p c
    (𝟙 C.S) t t (Category.comp_id t) r hr q' sq (testBaseChangeMapOfEq_fst _ _ _ _ _) 1 (by simp)
    hr' (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _)
    (baseFundamentalChowClass C)
  rw [harg]
  refine hnat.trans ?_
  obtain ⟨κ, hκ⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences C
    (pullback.fst sX (𝟙 C.S) ≫ sX) (1 - p)) (c.cap (𝟙 C.S) 1 (baseFundamentalChowClass C))
  rw [← hκ, flatPullbackChow_mk]
  set a' := properPushforward C (pullback.fst sX (𝟙 C.S) ≫ sX) sX (pullback.fst sX (𝟙 C.S)) rfl
    (1 - p) κ with ha'
  have hαa : QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p)) a' =
      QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p)) a := by
    rw [← ha, bivariantCapBaseFundamentalClass_apply,
      basePullbackPushforward_eq_chowPushforwardOfIso,
      ← hκ, chowPushforwardOfIso_mk]
  have _ : Flat (pullback.fst sX t) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback sX t).flip inferInstance
  have hcyc : (flatPullback C (pullback.fst sX t ≫ sX) (pullback.fst sX (𝟙 C.S) ≫ sX) q'
      (by rw [hq', testBaseChangeMapOfEq_fst_assoc]) r hr' (1 - p) κ).1 =
      (exteriorProductDedekindCycles C sX t (1 - p) (1 + r) a'
        (fundamentalCycle C t (1 + r))).1 := by
    refine Function.locallyFinsuppWithin.ext fun w ↦ ?_
    rw [flatPullback_apply, exteriorProductDedekindCycles_fundamentalCycle_apply_of_dominates C sX t
      (1 - p) hgen (1 + r) hrd a' w]
    have hfw : (pullback.fst sX t).base w = (pullback.fst sX (𝟙 C.S)).base (q'.base w) := by
      rw [← Scheme.Hom.comp_apply, hq', testBaseChangeMapOfEq_fst]
    rw [hfw, ha', properPushforward_apply_of_isIso]
    congr 1
    unfold flatPullbackWeight
    rw [show (1 - p + (1 + (r : ℤ)) - 1) = 1 - p + r by ring]
    refine closedSubschemeCycleCoeff_congr C _ ?_ _ w
    rw [hfw]
    show (integralComponentAt (q'.base w)).comap q' =
      (integralComponentAt ((pullback.fst sX (𝟙 C.S)).base (q'.base w))).comap
        (pullback.fst sX t)
    rw [← testBaseChangeMapOfEq_fst sX (𝟙 C.S) t t (Category.comp_id t),
      Scheme.IdealSheafData.comap_comp,
      comap_integralComponentAt_of_isOpenImmersion (pullback.fst sX (𝟙 C.S))]
  refine (mk_heq_mk_of_val_eq _ (by ring) _ _ hcyc).trans (heq_of_eq ?_)
  have hfac := hS.exteriorProductFactorsThroughRationalEquivalence sX t (1 - p) (1 + r)
  rw [← exteriorProductDedekindChow_mk_mk C sX t _ _ hfac,
    ← exteriorProductDedekindChow_mk_mk C sX t _ _ hfac, hαa]

/-- An integral scheme over a base as in section 42.63 with no zero-dimensional component, whose
generic point lies over a generic point of the base, is flat over the base of relative dimension
`r`, where its generic point has relative dimension `1 + r`. -/
theorem IsDedekindChowBase.exists_relativeDimension_of_mem_genericPoints
    (hS : IsDedekindChowBase C) (hS1 : HasNoZeroDimensionalComponent C) {T : Scheme.{u}}
    [IsIntegral T] (t : T ⟶ C.S) [LocallyOfFiniteType t]
    (hgen : t.base (genericPoint T) ∈ genericPoints C.S) :
    ∃ (_ : Flat t) (r : ℕ), AlgebraicGeometry.RelativeDimension t r ∧
      relativeDimension C.dimensionFunction t (genericPoint T) = 1 + r :=
  hS.exists_relativeDimension_of_mem_genericPoints_of_dimensionFunction_eq_one t hgen
    (hS.dimensionFunction_eq_one_of_mem_genericPoints hS1 hgen)

/-- **Capping the fundamental class of an integral scheme dominating a component of the base.**
Let `c ∈ A^p(X → S)` with `c ∩ [S]₁` the class of the cycle `a`, and let `T` be integral over the
base with generic point over a generic point of the base. Then `c ∩ [T] = a × [T]`.

`T` is flat over the base of some relative dimension `r` (Stacks 0AUW), so `[T]_{1+r}` is the flat
pullback of `[S]₁` and, `c` commuting with flat pullback, `c ∩ [T]` is the flat pullback of
`c ∩ [S]₁` along `X ×_S T ⟶ X ×_S S`; on cycles that flat pullback is `a × [T]`, by
`Stacks.Chow.exteriorProductDedekindCycles_fundamentalCycle_apply_of_dominates`. -/
theorem cap_fundamentalCycle_heq_of_mem_genericPoints (hS : IsDedekindChowBase C)
    (hS1 : HasNoZeroDimensionalComponent C)
    (c : BivariantClass C G sX (𝟙 C.S) sX (Category.comp_id sX) p) (a : CycleGroup C sX (1 - p))
    (ha : bivariantCapBaseFundamentalClass C G sX p c =
      QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p)) a)
    {T : Scheme.{u}} [IsIntegral T] (t : T ⟶ C.S) [LocallyOfFiniteType t]
    (hgen : t.base (genericPoint T) ∈ genericPoints C.S) (k : ℤ) :
    c.cap t k (chowGroupCongr C (Category.comp_id t).symm k
        (QuotientAddGroup.mk' (rationalEquivalences C t k) (fundamentalCycle C t k))) ≍
      QuotientAddGroup.mk' (rationalEquivalences C (pullback.fst sX t ≫ sX) (1 - p + k - 1))
        (exteriorProductDedekindCycles C sX t (1 - p) k a (fundamentalCycle C t k)) :=
  cap_fundamentalCycle_heq_of_mem_genericPoints_of_dimensionFunction_eq_one G sX p hS c a ha t hgen
    (hS.dimensionFunction_eq_one_of_mem_genericPoints hS1 hgen) k

end FlatCase

end Stacks.Chow

end
