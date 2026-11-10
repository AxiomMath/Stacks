module

public import StacksFrontier.AlgebraicGeometry.Chow.ZeroCyclesBertiniChainDefs

/-!
# The iterated Bertini cut is a complete intersection of divisor cuts

Let `X` be locally of finite type over a field `k`, let `M` be an invertible `𝒪_X`-module and let
`s_1, …, s_d` be global sections of `M`, with zero schemes `H_i = Z(s_i)`. Let `Z ⊆ X` be a closed
subscheme all of whose points have `δ`-dimension at most `0`. Suppose that for every `j ≤ d` the
points of `H_1 ∩ ⋯ ∩ H_j` off `Z` have `δ`-dimension at most `d - j`, and that each `s_{j+1}`
restricted to `H_1 ∩ ⋯ ∩ H_j` is a nonzerodivisor at the generic points of its zero scheme of
`δ`-dimension `d - j - 1`. Then the chain

`X = H_∅ ⊇ H_1 ⊇ H_1 ∩ H_2 ⊇ ⋯ ⊇ H_1 ∩ ⋯ ∩ H_d`

is a `d`-fold proper divisor cut of `M` ending in `δ`-dimension `0`, in the sense of
`Stacks.Chow.CompleteIntersection.IsIteratedDivisorCut`.

## Main results

* `Stacks.Chow.BertiniChain.exists_iso_cutSubscheme`: the zero scheme of `s_{j+1}` restricted to
  `H_1 ∩ ⋯ ∩ H_j` is the scheme-theoretic intersection `H_1 ∩ ⋯ ∩ H_{j+1}`.
* `Stacks.Chow.BertiniChain.isIteratedDivisorCut_familyCut`: `H_1 ∩ ⋯ ∩ H_d` is a `d`-fold proper
  divisor cut of `M` ending in `δ`-dimension `0`.

## References

* [Stacks Project, Tag 0FH5](https://stacks.math.columbia.edu/tag/0FH5)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Stacks.Ample
open Stacks.SectionsVanishingOnSubscheme Stacks.Chow.CompleteIntersection

universe u

namespace Stacks.Chow.BertiniChain

attribute [local instance] Stacks.SectionsVanishingOnSubscheme.isInvertible_of_isInvertibleModule

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The intersection of the empty family of zero schemes is the whole scheme. -/
theorem familyCut_prefixFamily_zero (M : X.Modules) [IsInvertibleModule X M] {d : ℕ}
    (s : Fin d → Γ(M, ⊤)) (h : 0 ≤ d) : familyCut M (prefixFamily s 0 h) = ⊥ := by
  simp [familyCut]

/-- Adding one more section to the family intersects with its zero scheme:
`H_1 ∩ ⋯ ∩ H_{j+1} = (H_1 ∩ ⋯ ∩ H_j) ∩ H_{j+1}`. -/
theorem familyCut_prefixFamily_succ (M : X.Modules) [IsInvertibleModule X M] {d : ℕ}
    (s : Fin d → Γ(M, ⊤)) (j : ℕ) (hj : j + 1 ≤ d) :
    familyCut M (prefixFamily s (j + 1) hj) =
      familyCut M (prefixFamily s j (by omega)) ⊔ Stacks.Divisors.zeroScheme X M (s ⟨j, hj⟩) := by
  refine le_antisymm (iSup_le fun i => ?_) (sup_le (iSup_le fun i => ?_) ?_)
  · induction i using Fin.lastCases with
    | last => exact le_sup_of_le_right le_rfl
    | cast i => exact le_sup_of_le_left (le_iSup_of_le i le_rfl)
  · exact le_iSup_of_le i.castSucc le_rfl
  · exact le_iSup_of_le (Fin.last j) le_rfl

/-- **The cut of `H_1 ∩ ⋯ ∩ H_j` by the next section is `H_1 ∩ ⋯ ∩ H_{j+1}`.** If `K = T ⊔ Z(t)`,
then the zero scheme of the restriction of `t` to the closed subscheme cut out by `T` is
isomorphic to the closed subscheme cut out by `K`, compatibly with the immersions into `X`. -/
theorem exists_iso_cutSubscheme (T : X.IdealSheafData) (M : X.Modules) [IsInvertibleModule X M]
    (t : Γ(M, ⊤)) (K : X.IdealSheafData) (hK : K = T ⊔ Stacks.Divisors.zeroScheme X M t) :
    ∃ e : K.subscheme ≅ (cutIdeal T.subschemeι M (restrictedSection T M t)).subscheme,
      e.hom ≫ cutSubscheme T.subschemeι M (restrictedSection T M t) = K.subschemeι := by
  subst hK
  have hcut : cutIdeal T.subschemeι M (restrictedSection T M t) =
      (Stacks.Divisors.zeroScheme X M t).comap T.subschemeι := by
    rw [cutIdeal, restrictedSection_eval_top, Stacks.Divisors.zeroScheme_pullback]
  obtain ⟨e', he'⟩ := Stacks.ChernCap42.exists_iso_comap_sup T
    (Stacks.Divisors.zeroScheme X M t) T.subschemeι (Iso.refl _) (by simp)
  rw [cutSubscheme, hcut]
  exact ⟨e'.symm, by rw [Iso.symm_hom, ← he', Iso.inv_hom_id_assoc]⟩

/-- A point of the closed subscheme cut out by `T` maps into the support of `T`. -/
theorem subschemeι_apply_mem_support (T : X.IdealSheafData) (w : T.subscheme) :
    T.subschemeι w ∈ T.support :=
  T.range_subschemeι.subset ⟨w, rfl⟩

/-- If every point of the support of `I` has `δ`-dimension at most `0` and every point of the
support of `T` outside that of `I` has `δ`-dimension at most `e ≥ 0`, then every point of the
support of `T` has `δ`-dimension at most `e`. -/
theorem relativeDimension_le_of_mem_support (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (I T : X.IdealSheafData)
    (hsupp : ∀ y ∈ I.support,
      relativeDimension (fieldChowSituation k).dimensionFunction f y ≤ 0)
    {e : ℤ} (hdim : DimBoundOff f I T e) (he : 0 ≤ e) {y : X} (hy : y ∈ T.support) :
    relativeDimension (fieldChowSituation k).dimensionFunction f y ≤ e := by
  by_cases hI : y ∈ I.support
  · exact (hsupp y hI).trans he
  · exact hdim y hy hI

/-- **The first `j` cuts form a `j`-fold proper divisor cut**: under the hypotheses of the
chain, `H_1 ∩ ⋯ ∩ H_j` is a `j`-fold proper divisor cut of `M` ending in `δ`-dimension
`d - j`. -/
theorem isIteratedDivisorCut_familyCut_prefixFamily {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (I : X.IdealSheafData) (M : X.Modules)
    [IsInvertibleModule X M] (d : ℕ) (s : Fin d → Γ(M, ⊤))
    (hsupp : ∀ y ∈ I.support,
      relativeDimension (fieldChowSituation k).dimensionFunction f y ≤ 0)
    (hdim : ∀ (j : ℕ) (hj : j ≤ d),
      DimBoundOff f I (familyCut M (prefixFamily s j hj)) ((d : ℤ) - j))
    (hinj : ∀ (j : ℕ) (hj : j < d),
      ∀ ξ : genericPoints (cutIdeal (familyCut M (prefixFamily s j hj.le)).subschemeι M
          (restrictedSection (familyCut M (prefixFamily s j hj.le)) M (s ⟨j, hj⟩))).subscheme,
        relativeDimension (fieldChowSituation k).dimensionFunction
            ((familyCut M (prefixFamily s j hj.le)).subschemeι ≫ f)
            ((cutIdeal (familyCut M (prefixFamily s j hj.le)).subschemeι M
              (restrictedSection (familyCut M (prefixFamily s j hj.le)) M
                (s ⟨j, hj⟩))).subschemeι ξ.1) = (d : ℤ) - j - 1 →
          Function.Injective (ConcreteCategory.hom
            ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
              ((cutIdeal (familyCut M (prefixFamily s j hj.le)).subschemeι M
                (restrictedSection (familyCut M (prefixFamily s j hj.le)) M
                  (s ⟨j, hj⟩))).subschemeι ξ.1)).map
              ((Scheme.Modules.toPresheaf (familyCut M (prefixFamily s j hj.le)).subscheme).map
                (((Scheme.Modules.pullback
                    (familyCut M (prefixFamily s j hj.le)).subschemeι).obj M).unitHomEquiv.symm
                  (restrictedSection (familyCut M (prefixFamily s j hj.le)) M
                    (s ⟨j, hj⟩))))))) :
    ∀ (j : ℕ) (hj : j ≤ d),
      IsIteratedDivisorCut (fieldChowSituation k) f M j ((d : ℤ) - j)
        (familyCut M (prefixFamily s j hj)).subscheme
        (familyCut M (prefixFamily s j hj)).subschemeι
  | 0, hj => by
    change IsIso _
    rw [Scheme.isIso_subschemeι_iff_eq_bot]
    exact familyCut_prefixFamily_zero M s hj
  | j + 1, hj => by
    have ih := isIteratedDivisorCut_familyCut_prefixFamily f I M d s hsupp hdim hinj j (by omega)
    set T := familyCut M (prefixFamily s j (by omega)) with hT
    obtain ⟨e, he⟩ := exists_iso_cutSubscheme T M (s ⟨j, hj⟩) _
      (familyCut_prefixFamily_succ M s j hj)
    refine ⟨T.subscheme, T.subschemeι, inferInstance, ?_, restrictedSection T M (s ⟨j, hj⟩),
      ⟨?_, ?_, ?_⟩, e, he⟩
    · rwa [show (d : ℤ) - ↑(j + 1) + 1 = (d : ℤ) - j by push_cast; ring]
    · have h := Stacks.Chow.schemeDeltaDimension_le_of_forall_relativeDimension_le
        (fieldChowSituation k) f T.subschemeι (k := (d : ℤ) - ↑(j + 1) + 1) fun w =>
          (relativeDimension_le_of_mem_support f I T hsupp (hdim j (by omega)) (by omega)
            (subschemeι_apply_mem_support T w)).trans_eq (by push_cast; ring)
      exact_mod_cast h
    · have hcut : ∀ z, cutSubscheme T.subschemeι M (restrictedSection T M (s ⟨j, hj⟩)) z ∈
          (familyCut M (prefixFamily s (j + 1) hj)).support := fun z => by
        simpa [← he] using subschemeι_apply_mem_support _ (e.inv z)
      exact Stacks.Chow.schemeDeltaDimension_le_of_forall_relativeDimension_le
        (fieldChowSituation k) (T.subschemeι ≫ f) _ (k := (d : ℤ) - ↑(j + 1)) fun z => by
          rw [relativeDimension_comp_closedImmersion]
          exact relativeDimension_le_of_mem_support f I _ hsupp (hdim (j + 1) hj) (by omega)
            (hcut z)
    · intro ξ hξ
      exact hinj j hj ξ (by rw [hξ]; push_cast; ring)

/-- **The chain of cuts is an iterated proper divisor cut.** Under the dimension bounds off `Z`
and the nonvanishing at the generic points of each cut, the intersection `H_1 ∩ ⋯ ∩ H_d` of the
zero schemes of `s_1, …, s_d` is a `d`-fold proper divisor cut of `M` ending in `δ`-dimension
`0`. -/
theorem isIteratedDivisorCut_familyCut {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (I : X.IdealSheafData) (M : X.Modules)
    [IsInvertibleModule X M] (d : ℕ) (s : Fin d → Γ(M, ⊤))
    (hsupp : ∀ y ∈ I.support,
      relativeDimension (fieldChowSituation k).dimensionFunction f y ≤ 0)
    (hdim : ∀ (j : ℕ) (hj : j ≤ d),
      DimBoundOff f I (familyCut M (prefixFamily s j hj)) ((d : ℤ) - j))
    (hinj : ∀ (j : ℕ) (hj : j < d),
      ∀ ξ : genericPoints (cutIdeal (familyCut M (prefixFamily s j hj.le)).subschemeι M
          (restrictedSection (familyCut M (prefixFamily s j hj.le)) M (s ⟨j, hj⟩))).subscheme,
        relativeDimension (fieldChowSituation k).dimensionFunction
            ((familyCut M (prefixFamily s j hj.le)).subschemeι ≫ f)
            ((cutIdeal (familyCut M (prefixFamily s j hj.le)).subschemeι M
              (restrictedSection (familyCut M (prefixFamily s j hj.le)) M
                (s ⟨j, hj⟩))).subschemeι ξ.1) = (d : ℤ) - j - 1 →
          Function.Injective (ConcreteCategory.hom
            ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
              ((cutIdeal (familyCut M (prefixFamily s j hj.le)).subschemeι M
                (restrictedSection (familyCut M (prefixFamily s j hj.le)) M
                  (s ⟨j, hj⟩))).subschemeι ξ.1)).map
              ((Scheme.Modules.toPresheaf (familyCut M (prefixFamily s j hj.le)).subscheme).map
                (((Scheme.Modules.pullback
                    (familyCut M (prefixFamily s j hj.le)).subschemeι).obj M).unitHomEquiv.symm
                  (restrictedSection (familyCut M (prefixFamily s j hj.le)) M
                    (s ⟨j, hj⟩))))))) :
    IsIteratedDivisorCut (fieldChowSituation k) f M d 0 (familyCut M s).subscheme
      (familyCut M s).subschemeι := by
  have h := isIteratedDivisorCut_familyCut_prefixFamily f I M d s hsupp hdim hinj d le_rfl
  rwa [sub_self] at h

end Stacks.Chow.BertiniChain

end
