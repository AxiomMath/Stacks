module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleFlat
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleFlatGeneral
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleProper
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly

/-!
# The Chern class cap products on a locally finite sum of closed subschemes

Let `ℱ` be finite locally free of rank `r` on a scheme `M` locally of finite type over the base
of chapter 42, and let `vₜ : Tₜ ⟶ M` be a locally finite family of closed subschemes. Suppose
that for every `t` the cap product `c_j(vₜ^*ℱ) ∩ [Tₜ]_k` is the class of a closed subscheme
`wₜ : Wₜ ⟶ Tₜ`. Then for integers `nₜ`

  `c_j(ℱ) ∩ ∑ₜ nₜ [Tₜ]_k = ∑ₜ nₜ [Wₜ]_{k-j}`

in `CH_{k-j}(M)`, the sums being locally finite sums of cycles. This is the reduction of a
statement about `c_j(ℱ) ∩ α` for an arbitrary class `α` to its value on the fundamental classes
of closed subschemes, the way the source argues in [Stacks, Tag 0FAA]: the family is replaced by
the disjoint union `∐ₜ Tₜ`, which is proper over `M`, the cap products commute with the
pushforward along `∐ₜ Tₜ ⟶ M` ([Stacks, Tag 02U9]) and with the restrictions to the summands
([Stacks, Tag 02U8]), and the Chow group of the disjoint union is detected on the summands.

## Main results

* `Stacks.Chow.properPushforward_sigmaDesc_apply` — the coefficients of the pushforward of a cycle
  along `∐ₜ Tₜ ⟶ M` are the locally finite sums of the coefficients of the pushforwards of its
  restrictions to the summands.
* `Stacks.Chow.GenuineChern.chernCap_mk_eq_mk_of_locallyFinite` — the displayed identity.

## References

* [Stacks Project, Tag 02U8](https://stacks.math.columbia.edu/tag/02U8)
* [Stacks Project, Tag 02U9](https://stacks.math.columbia.edu/tag/02U9)
* [Stacks Project, Tag 0FAA](https://stacks.math.columbia.edu/tag/0FAA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {M : Scheme.{u}} (q : M ⟶ C.S) [LocallyOfFiniteType q]

/-! ### Pushforward from a disjoint union of closed subschemes -/

/-- **Pushforward along a proper morphism with surjective stalk maps** adds up the coefficients
over the fibre: the residue field maps are bijective, so every residue degree is one and the
delta-dimension of a point is that of its image. -/
theorem properPushforward_apply_of_surjectiveOnStalks {A : Scheme.{u}} (f : A ⟶ M) [IsProper f]
    [SurjectiveOnStalks f] (k : ℤ) (c : CycleGroup C (f ≫ q) k) (y : M) :
    (properPushforward C (f ≫ q) q f rfl k c).1 y = ∑ᶠ x ∈ f.base ⁻¹' {y}, c.1 x := by
  rw [properPushforward_apply]
  refine finsum_mem_congr rfl fun x _ ↦ ?_
  have hb := bijective_residueFieldMap_of_surjective_stalkMap f x (f.stalkMap_surjective x)
  rw [relativeDimension_comp_of_bijective_residueFieldMap C.dimensionFunction f q x hb,
    residueDegree_eq_one_of_bijective_residueFieldMap f x hb]
  simp

/-- **The coefficients of a pushforward from a disjoint union of closed subschemes.** For closed
immersions `vₜ : Tₜ ⟶ M` with `∐ₜ Tₜ ⟶ M` proper, the coefficient at `y` of the pushforward of
a cycle `γ` on `∐ₜ Tₜ` is the locally finite sum over `t` of the coefficients at `y` of the
pushforwards along `vₜ` of the restrictions of `γ` to the summands. -/
theorem properPushforward_sigmaDesc_apply {J : Type u} (T : J → Scheme.{u})
    (v : ∀ t, T t ⟶ M) [∀ t, IsClosedImmersion (v t)] [IsProper (Sigma.desc v)] (k : ℤ)
    (γ : CycleGroup C (Sigma.desc v ≫ q) k) (y : M) :
    (properPushforward C (Sigma.desc v ≫ q) q (Sigma.desc v) rfl k γ).1 y =
      ∑ᶠ t, (properPushforward C (v t ≫ q) q (v t) rfl k
        (cycleGroupRestrict C (Sigma.desc v ≫ q) (v t ≫ q) (Sigma.ι T t)
          (Sigma.ι_desc_assoc _ _ _) k γ)).1 y := by
  classical
  have : SurjectiveOnStalks (Sigma.desc v) := surjectiveOnStalks_sigmaDesc T v
  rw [properPushforward_apply_of_surjectiveOnStalks]
  simp_rw [properPushforward_apply_of_surjectiveOnStalks C q (v _), cycleGroupRestrict_apply]
  have hbase : ∀ (t : J) (z : T t), (Sigma.desc v).base (Sigma.ι T t z) = (v t).base z :=
    fun t z ↦ by rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
  let e := (sigmaMk T).toEquiv
  have he : ∀ s : (t : J) × T t, e s = Sigma.ι T s.1 s.2 := fun s ↦ sigmaMk_mk T s.1 s.2
  set F : ((t : J) × T t) → ℤ := fun s ↦ if (v s.1).base s.2 = y then γ.1 (e s) else 0
  have hfin : (Function.support F).Finite := by
    have hK : IsCompact ((Sigma.desc v).base ⁻¹' {y}) :=
      (Sigma.desc v).isProperMap.isCompact_preimage isCompact_singleton
    have h1 := γ.1.locallyFiniteSupport.finite_inter_support_of_isCompact hK
    refine (h1.preimage e.injective.injOn).subset fun s hs ↦ ?_
    simp only [F, Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hs
    refine ⟨?_, hs.2⟩
    show (Sigma.desc v).base (e s) ∈ ({y} : Set M)
    rw [he, hbase]
    exact hs.1
  calc ∑ᶠ x ∈ (Sigma.desc v).base ⁻¹' {y}, γ.1 x
      = ∑ᶠ x, if (Sigma.desc v).base x = y then γ.1 x else 0 := by
        rw [finsum_mem_def]
        refine finsum_congr fun x ↦ ?_
        simp [Set.indicator_apply]
    _ = ∑ᶠ s, if (Sigma.desc v).base (e s) = y then γ.1 (e s) else 0 :=
        (finsum_comp_equiv e (f := fun x ↦ if (Sigma.desc v).base x = y then γ.1 x else 0)).symm
    _ = ∑ᶠ s, F s := by
        refine finsum_congr fun s ↦ ?_
        simp only [F, he, hbase]
    _ = ∑ᶠ t, ∑ᶠ z, F ⟨t, z⟩ := finsum_sigma F hfin
    _ = _ := by
        refine finsum_congr fun t ↦ ?_
        rw [finsum_mem_def]
        refine finsum_congr fun z ↦ ?_
        simp [F, Set.indicator_apply, he]

end Stacks.Chow

namespace Stacks.Chow.GenuineChern

variable (C : ChowSituation.{u}) {M : Scheme.{u}} (q : M ⟶ C.S) [LocallyOfFiniteType q]

attribute [local instance] AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback

/-- A Chern class cap product does not see the way its degree is written. -/
theorem chernCap_heq_of_degree {F : M.Modules} {r : ℕ}
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (j : Fin (r + 1))
    {k l : ℤ} (hkl : k = l) {x : chowGroup C q k} {y : chowGroup C q l} (hxy : x ≍ y) :
    chernCap C r q F k j x ≍ chernCap C r q F l j y := by
  subst hkl
  rw [eq_of_heq hxy]

/-- **The Chern class cap products on a disjoint union of closed subschemes.** If the cycles `γ`
on `∐ₜ Tₜ` and `δ` on `∐ₜ Tₜ` restrict to `nₜ [Tₜ]_k` and to `nₜ [Wₜ]_{k-j}` on the summands and
`c_j(vₜ^*ℱ) ∩ [Tₜ]_k = [Wₜ]_{k-j}` for every `t`, then `c_j(ℱ) ∩ [γ] = [δ]`. -/
private theorem chernCap_mk_eq_mk_of_restrict_sigmaDesc (F : M.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (k : ℤ)
    (j : Fin (r + 1)) {J : Type u} (T : J → Scheme.{u}) (v : ∀ t, T t ⟶ M)
    [∀ t, IsClosedImmersion (v t)] [IsProper (Sigma.desc v)]
    (hι : ∀ t, Sigma.ι T t ≫ (Sigma.desc v ≫ q) = v t ≫ q)
    (W : J → Scheme.{u}) (w : ∀ t, W t ⟶ T t) [∀ t, IsClosedImmersion (w t)] (n : J → ℤ)
    (hcap : ∀ t, chernCap C r (v t ≫ q) ((Scheme.Modules.pullback (v t)).obj F) k j
        (QuotientAddGroup.mk' (rationalEquivalences C (v t ≫ q) k)
          (cycleAssociatedToClosedSubscheme C (v t ≫ q) (𝟙 (T t)) k)) =
      QuotientAddGroup.mk' (rationalEquivalences C (v t ≫ q) (k - (j : ℤ)))
        (cycleAssociatedToClosedSubscheme C (v t ≫ q) (w t) (k - (j : ℤ))))
    (γ : CycleGroup C (Sigma.desc v ≫ q) k)
    (hγ : ∀ t, cycleGroupRestrict C (Sigma.desc v ≫ q) (v t ≫ q) (Sigma.ι T t) (hι t) k γ =
      n t • fundamentalCycle C (v t ≫ q) k)
    (δ : CycleGroup C (Sigma.desc v ≫ q) (k - (j : ℤ)))
    (hδ : ∀ t, cycleGroupRestrict C (Sigma.desc v ≫ q) (v t ≫ q) (Sigma.ι T t) (hι t)
      (k - (j : ℤ)) δ = n t • cycleAssociatedToClosedSubscheme C (v t ≫ q) (w t) (k - (j : ℤ))) :
    chernCap C r (Sigma.desc v ≫ q) ((Scheme.Modules.pullback (Sigma.desc v)).obj F) k j
        (QuotientAddGroup.mk' (rationalEquivalences C (Sigma.desc v ≫ q) k) γ) =
      QuotientAddGroup.mk' (rationalEquivalences C (Sigma.desc v ≫ q) (k - (j : ℤ))) δ := by
  refine sub_eq_zero.mp (eq_zero_of_chowGroupRestrict_eq_zero C (Sigma.desc v ≫ q)
    (fun t ↦ v t ≫ q) (Sigma.ι T) hι (isClopenDecomposition_opensRange_sigmaι T)
    (k - (j : ℤ)) _ fun t ↦ ?_)
  rw [map_sub, sub_eq_zero]
  have hr := relativeDimension_of_isOpenImmersion (Sigma.ι T t)
  let eE : (Scheme.Modules.pullback (v t)).obj F ≅
      (Scheme.Modules.pullback (Sigma.ι T t)).obj
        ((Scheme.Modules.pullback (Sigma.desc v)).obj F) :=
    eqToIso (congrArg (fun g ↦ (Scheme.Modules.pullback g).obj F) (Sigma.ι_desc v t).symm) ≪≫
      ((Scheme.Modules.pullbackComp (Sigma.ι T t) (Sigma.desc v)).app F).symm
  have h02U8 := chernCap_flatPullback_heq_general C (Sigma.desc v ≫ q) (v t ≫ q) (Sigma.ι T t)
    (hι t) 0 hr ((Scheme.Modules.pullback (Sigma.desc v)).obj F) r
    ((Scheme.Modules.pullback (v t)).obj F) eE k j
    (QuotientAddGroup.mk' (rationalEquivalences C (Sigma.desc v ≫ q) k) γ)
  have hγ' : flatPullbackChow C (v t ≫ q) (Sigma.desc v ≫ q) (Sigma.ι T t) (hι t) 0 hr k
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ (hι t) 0 hr k)
      (QuotientAddGroup.mk' (rationalEquivalences C (Sigma.desc v ≫ q) k) γ) ≍
      n t • QuotientAddGroup.mk' (rationalEquivalences C (v t ≫ q) k)
        (fundamentalCycle C (v t ≫ q) k) := by
    refine (heq_chowGroupRestrict_flatPullbackChow C (Sigma.desc v ≫ q) (v t ≫ q)
      (Sigma.ι T t) (hι t) hr k _ _).symm.trans (heq_of_eq ?_)
    rw [chowGroupRestrict_mk, hγ t, map_zsmul]
  refine eq_of_heq ((heq_chowGroupRestrict_flatPullbackChow C (Sigma.desc v ≫ q) (v t ≫ q)
    (Sigma.ι T t) (hι t) hr (k - (j : ℤ)) _ _).trans (h02U8.symm.trans ?_))
  refine (chernCap_heq_of_degree C (v t ≫ q) j (by simp) hγ').trans ?_
  rw [map_zsmul, show fundamentalCycle C (v t ≫ q) k =
    cycleAssociatedToClosedSubscheme C (v t ≫ q) (𝟙 (T t)) k from rfl, hcap t, ← map_zsmul,
    ← hδ t, ← chowGroupRestrict_mk]

/-- **The Chern class cap products on a locally finite sum of closed subschemes.** Let `ℱ` be
finite locally free of rank `r` on `M`, let `vₜ : Tₜ ⟶ M` be a locally finite family of closed
subschemes and `wₜ : Wₜ ⟶ Tₜ` closed subschemes with `c_j(vₜ^*ℱ) ∩ [Tₜ]_k = [Wₜ]_{k-j}` in
`CH_{k-j}(Tₜ)`. If `a` is the `k`-cycle `∑ₜ nₜ [Tₜ]_k` and `b` the `(k-j)`-cycle
`∑ₜ nₜ [Wₜ]_{k-j}` on `M`, then `c_j(ℱ) ∩ [a] = [b]`. -/
theorem chernCap_mk_eq_mk_of_locallyFinite (F : M.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (k : ℤ)
    (j : Fin (r + 1)) {J : Type u} (T : J → Scheme.{u}) (v : ∀ t, T t ⟶ M)
    [∀ t, IsClosedImmersion (v t)] (hlf : LocallyFinite fun t ↦ Set.range (v t))
    (W : J → Scheme.{u}) (w : ∀ t, W t ⟶ T t) [∀ t, IsClosedImmersion (w t)] (n : J → ℤ)
    (hcap : ∀ t, chernCap C r (v t ≫ q) ((Scheme.Modules.pullback (v t)).obj F) k j
        (QuotientAddGroup.mk' (rationalEquivalences C (v t ≫ q) k)
          (cycleAssociatedToClosedSubscheme C (v t ≫ q) (𝟙 (T t)) k)) =
      QuotientAddGroup.mk' (rationalEquivalences C (v t ≫ q) (k - (j : ℤ)))
        (cycleAssociatedToClosedSubscheme C (v t ≫ q) (w t) (k - (j : ℤ))))
    (a : CycleGroup C q k)
    (ha : ∀ y, a.1 y = ∑ᶠ t, n t * (cycleAssociatedToClosedSubscheme C q (v t) k).1 y)
    (b : CycleGroup C q (k - (j : ℤ)))
    (hb : ∀ y, b.1 y =
      ∑ᶠ t, n t * (cycleAssociatedToClosedSubscheme C q (w t ≫ v t) (k - (j : ℤ))).1 y) :
    chernCap C r q F k j (QuotientAddGroup.mk' (rationalEquivalences C q k) a) =
      QuotientAddGroup.mk' (rationalEquivalences C q (k - (j : ℤ))) b := by
  classical
  have hproper : IsProper (Sigma.desc v) := isProper_sigmaDesc_of_locallyFinite T v hlf
  have hι : ∀ t, Sigma.ι T t ≫ (Sigma.desc v ≫ q) = v t ≫ q := fun t ↦ Sigma.ι_desc_assoc _ _ _
  obtain ⟨γ, hγ⟩ := exists_cycleGroup_of_sigma C T (Sigma.desc v ≫ q) (fun t ↦ v t ≫ q) hι k
    (fun t ↦ n t • fundamentalCycle C (v t ≫ q) k)
  obtain ⟨δ, hδ⟩ := exists_cycleGroup_of_sigma C T (Sigma.desc v ≫ q) (fun t ↦ v t ≫ q) hι
    (k - (j : ℤ)) (fun t ↦ n t • cycleAssociatedToClosedSubscheme C (v t ≫ q) (w t) (k - (j : ℤ)))
  have hγr : ∀ t, cycleGroupRestrict C (Sigma.desc v ≫ q) (v t ≫ q) (Sigma.ι T t) (hι t) k γ =
      n t • fundamentalCycle C (v t ≫ q) k := fun t ↦
    Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ by
      rw [cycleGroupRestrict_apply]
      exact hγ t z)
  have hδr : ∀ t, cycleGroupRestrict C (Sigma.desc v ≫ q) (v t ≫ q) (Sigma.ι T t) (hι t)
      (k - (j : ℤ)) δ = n t • cycleAssociatedToClosedSubscheme C (v t ≫ q) (w t) (k - (j : ℤ)) :=
    fun t ↦ Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ by
      rw [cycleGroupRestrict_apply]
      exact hδ t z)
  have hpa : properPushforward C (Sigma.desc v ≫ q) q (Sigma.desc v) rfl k γ = a := by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
    rw [properPushforward_sigmaDesc_apply, ha y]
    refine finsum_congr fun t ↦ ?_
    rw [hγr t, ← properPushforwardHom_apply, map_zsmul, properPushforwardHom_apply,
      properPushforward_fundamentalCycle_of_isClosedImmersion C (v t ≫ q) q (v t) rfl k]
    rfl
  have hpb : properPushforward C (Sigma.desc v ≫ q) q (Sigma.desc v) rfl (k - (j : ℤ)) δ = b := by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
    rw [properPushforward_sigmaDesc_apply, hb y]
    refine finsum_congr fun t ↦ ?_
    rw [hδr t, ← properPushforwardHom_apply, map_zsmul, properPushforwardHom_apply,
      properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C (v t ≫ q) q
        (v t) rfl (w t) (k - (j : ℤ))]
    rfl
  have hV := chernCap_mk_eq_mk_of_restrict_sigmaDesc C q F r k j T v hι W w n hcap γ hγr δ hδr
  have hfac := properPushforwardFactorsThroughRationalEquivalence_of_isProper C
    (Sigma.desc v ≫ q) q (Sigma.desc v) rfl k
  have hfacp := properPushforwardFactorsThroughRationalEquivalence_of_isProper C
    (Sigma.desc v ≫ q) q (Sigma.desc v) rfl (k - (j : ℤ))
  rw [← hpa, ← properChowPushforward_mk C _ q (Sigma.desc v) rfl k hfac,
    chernCap_properPushforward C (Sigma.desc v ≫ q) q (Sigma.desc v) rfl F r
      ((Scheme.Modules.pullback (Sigma.desc v)).obj F) (Iso.refl _) k j hfac hfacp, hV,
    properChowPushforward_mk, hpb]

end Stacks.Chow.GenuineChern

end
