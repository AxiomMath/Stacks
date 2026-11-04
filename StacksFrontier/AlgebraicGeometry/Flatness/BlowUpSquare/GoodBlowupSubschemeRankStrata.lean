module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.DivisorRankStrata
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodBlowupDecalagePerfect
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodBlowupDivisorSubscheme
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodBlowupSubschemeCohomology
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleSubschemeExistence
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.LocallyFiniteCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback

/-!
# Rank strata of the closed subscheme `T` of tag 0F8X

Let `(X, D, M)` be a triple as in Situation 0F8S, `b : X' ⟶ X` a morphism along which the
pullback `D' = b⁻¹D` is defined, `Q = Lη_{ℐ'}Lb^*M`, and `i : T ⟶ D'` a closed immersion with
the three properties of tag 0F8X. For ranks `ρ = (ρ_n)_{n ∈ ℤ}` the locus `T(ρ) ⊆ T` where
`H^n(Li^*Q)` has rank `ρ_n` for every `n` is open and closed, contains `D' ∩ b⁻¹(W(ρ))` scheme
theoretically, and carries `H^n(Li^*Q)` locally free of rank `ρ_n`. This is Stacks tag 0F8Y.

## Main results

* `AlgebraicGeometry.ComplexAndDivisorSituation.mem_locallyFreeLocus_and_finrank_eq_of_isFreeOver`:
  over an open where every `H^n(M)` is locally free of rank `ρ_n`, the stalks of `H^n(M)` have
  rank `ρ_n`.
* `AlgebraicGeometry.ComplexAndDivisorSituation.exists_isClopen_rankStratum_of_subscheme`: the
  statement for any `b` with `Q` perfect and any closed subscheme `T ⊆ D'` with the properties of
  tag 0F8X.
* `AlgebraicGeometry.ComplexAndDivisorSituation.exists_isClopen_rankStratum_goodBlowup`:
  **Stacks tag 0F8Y**, for the morphism `b` of tag 0GTY and the subscheme `T` of tag 0F8X.

## Implementation notes

`W(ρ)` is the maximal open subscheme of `X` over which every `H^n(M)` is locally free of rank
`ρ_n`, i.e. the union of all such opens. Containing `D' ∩ b⁻¹(W(ρ))` scheme theoretically is
therefore the same as containing `D' ∩ b⁻¹(V)` for each such open `V`, and that is how the
containment is stated: for each such `V` the open subscheme `D' ∩ b⁻¹(V)` of `D'` factors through
`T(ρ) ⟶ T ⟶ D'`.

The ranks are integers, as in the source. A finite locally free module has nonnegative rank, so
the stratum of a `ρ` with a negative entry is empty.

## References

* [Stacks Project, Tag 0F8Y](https://stacks.math.columbia.edu/tag/0F8Y)
* [Stacks Project, Tag 0F8X](https://stacks.math.columbia.edu/tag/0F8X)
* [Stacks Project, Tag 0F8U](https://stacks.math.columbia.edu/tag/0F8U)
* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace StrictlyPerfect

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation

attribute [local instance 10000] HasDerivedCategory.standard

variable (S : ComplexAndDivisorSituation.{u, d})

/-- At a point of an open `V ⊆ X` over which every cohomology sheaf `H^n(M)` is locally free of
rank `ρ_n`, the point lies in the locally free locus `W` and every stalk `H^n(M)_x` has rank
`ρ_n` over `𝒪_{X, x}`. -/
theorem mem_locallyFreeLocus_and_finrank_eq_of_isFreeOver (ρ : ℤ → ℤ) (V : S.X.Opens)
    (hV : ∀ (n : ℤ), ∀ x ∈ V, ∃ U : S.X.Opens, x ∈ U ∧ U ≤ V ∧ ∃ ι : Type u, Finite ι ∧
      (Nat.card ι : ℤ) = ρ n ∧ Nonempty ((restrictModules S.X.toRingedSpace U).obj
        (S.cohomologySheaf n) ≅ _root_.SheafOfModules.free.{u} ι))
    {x : S.X} (hx : x ∈ V) :
    x ∈ S.locallyFreeLocus ∧ ∀ n : ℤ,
      (Module.finrank (ToType (S.X.presheaf.stalk x))
        (ToType (TopCat.Presheaf.stalk (S.cohomologySheaf n).val.presheaf x)) : ℤ) = ρ n := by
  refine ⟨S.le_locallyFreeLocus V (fun n y hy ↦ ?_) hx, fun n ↦ ?_⟩
  · obtain ⟨U, hyU, hUV, ι, hfin, -, he⟩ := hV n y hy
    exact ⟨U, hyU, hUV, ι, hfin, he⟩
  · obtain ⟨U, hxU, -, ι, hfin, hρ, ⟨e⟩⟩ := hV n x hx
    obtain ⟨f⟩ := LocallyFreeRank.Trivialization.stalk_linearEquiv_finsupp S.X.carrier S.X.sheaf
      (S.cohomologySheaf n) x hxU ⟨ι, e⟩
    have : Nontrivial (ToType (TopCat.Presheaf.stalk S.X.sheaf.obj x)) :=
      LocallyFreeRank.scheme_stalksNontrivial S.X x
    have : Fintype ι := Fintype.ofFinite ι
    have key : @Module.finrank (ToType (TopCat.Presheaf.stalk S.X.sheaf.obj x))
        (ToType (TopCat.Presheaf.stalk (S.cohomologySheaf n).val.presheaf x)) _ _
        (LocallyFreeRank.instModuleStalkF S.X.carrier S.X.sheaf (S.cohomologySheaf n) x) =
          Nat.card ι := by
      let := LocallyFreeRank.instModuleStalkF S.X.carrier S.X.sheaf (S.cohomologySheaf n) x
      have h := f.finrank_eq
      rwa [Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card] at h
    exact (congrArg (fun r : ℕ ↦ (r : ℤ)) key).trans hρ

/-- The locus where a locally bounded family of finite locally free modules has prescribed
integer ranks is open and closed. -/
private theorem _root_.AlgebraicGeometry.Scheme.Modules.isClopen_setOf_finiteLocallyFreeRank_eq
    {T : Scheme.{u}} (F : ℤ → T.Modules)
    (hF : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (F n))
    (ρ : ℤ → ℤ)
    (hbd : ∀ t : T, ∃ V : T.Opens, t ∈ V ∧ ∃ s : Finset ℤ, ∀ n ∉ s, ∀ v ∈ V,
      @Scheme.Modules.finiteLocallyFreeRank T (F n) (hF n) v = 0) :
    IsClopen {t : T | ∀ n : ℤ,
      (@Scheme.Modules.finiteLocallyFreeRank _ (F n) (hF n) t : ℤ) = ρ n} := by
  by_cases hρ : ∀ n, 0 ≤ ρ n
  · have : {t : T | ∀ n : ℤ,
        (@Scheme.Modules.finiteLocallyFreeRank _ (F n) (hF n) t : ℤ) = ρ n} =
        Scheme.Modules.rankStratumSet F hF (fun n ↦ (ρ n).toNat) := by
      ext t
      rw [Scheme.Modules.mem_rankStratumSet]
      refine forall_congr' fun n ↦ ?_
      have := hρ n
      omega
    rw [this]
    exact Scheme.Modules.isClopen_rankStratumSet F hF _ hbd
  · push Not at hρ
    obtain ⟨n, hn⟩ := hρ
    convert isClopen_empty
    exact Set.eq_empty_of_forall_notMem fun t ht ↦ by
      have := ht n
      omega

/-- **Stacks tag 0F8Y for an arbitrary `b` and `T`.** Let `b : X' ⟶ X` be a morphism along which
`D' = b⁻¹D` is defined, with `Q = Lη_{ℐ'}Lb^*M` perfect, and let `T ⊆ D'` be a closed subscheme
containing `D' ∩ b⁻¹(W)` scheme theoretically, on which the cohomology sheaves of `Li^*Q` are
finite locally free with the ranks of the cohomology of `M` over `W`. Then the locus
`T(ρ) ⊆ T` where `H^n(Li^*Q)` has rank `ρ_n` for all `n` is open and closed, contains
`D' ∩ b⁻¹(V)` scheme theoretically for every open `V ⊆ X` over which each `H^n(M)` is locally
free of rank `ρ_n`, and `H^n(Li^*Q)` is free of rank `ρ_n` near each point of `T(ρ)`. -/
theorem exists_isClopen_rankStratum_of_subscheme {X' : Scheme.{u}} (b : X' ⟶ S.X)
    (hb : Stacks.Divisors.IsPullbackDefined b S.D)
    (hQ : RingedSpace.IsPerfect (X := X'.toRingedSpace) (S.etaDerivedPullbackObject b hb))
    (T : (S.D.comap b).subscheme.IdealSheafData)
    (h₁ : T.comap ((S.D.comap b).subschemeι ⁻¹ᵁ (b ⁻¹ᵁ S.locallyFreeLocus)).ι = ⊥)
    (h₂ : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (S.etaDerivedPullbackRestrictHomology b hb (T.subschemeι ≫ (S.D.comap b).subschemeι) n))
    (h₃ : ∀ (n : ℤ) (t : T.subscheme)
      (_ : ((T.subschemeι ≫ (S.D.comap b).subschemeι) ≫ b).base t ∈ S.locallyFreeLocus),
      Module.finrank (ToType (T.subscheme.presheaf.stalk t))
          (ToType (TopCat.Presheaf.stalk (S.etaDerivedPullbackRestrictHomology b hb
            (T.subschemeι ≫ (S.D.comap b).subschemeι) n).val.presheaf t)) =
        Module.finrank
          (ToType (S.X.presheaf.stalk (((T.subschemeι ≫ (S.D.comap b).subschemeι) ≫ b).base t)))
          (ToType (TopCat.Presheaf.stalk (S.cohomologySheaf n).val.presheaf
            (((T.subschemeι ≫ (S.D.comap b).subschemeι) ≫ b).base t))))
    (ρ : ℤ → ℤ) :
    ∃ Tρ : T.subscheme.Opens, IsClopen (Tρ : Set T.subscheme) ∧
      (∀ V : S.X.Opens,
        (∀ (n : ℤ), ∀ x ∈ V, ∃ U : S.X.Opens, x ∈ U ∧ U ≤ V ∧ ∃ ι : Type u, Finite ι ∧
          (Nat.card ι : ℤ) = ρ n ∧ Nonempty ((restrictModules S.X.toRingedSpace U).obj
            (S.cohomologySheaf n) ≅ _root_.SheafOfModules.free.{u} ι)) →
        ∃ g : ((S.D.comap b).subschemeι ⁻¹ᵁ (b ⁻¹ᵁ V)).toScheme ⟶ Tρ.toScheme,
          g ≫ Tρ.ι ≫ T.subschemeι = ((S.D.comap b).subschemeι ⁻¹ᵁ (b ⁻¹ᵁ V)).ι) ∧
      ∀ (n : ℤ), ∀ t ∈ Tρ, ∃ U : T.subscheme.Opens, t ∈ U ∧ U ≤ Tρ ∧ ∃ I : Type u,
        Finite I ∧ (Nat.card I : ℤ) = ρ n ∧
          Nonempty (_root_.SheafOfModules.free.{u} I ≅
            (Scheme.Modules.toRingSheafModule (S.etaDerivedPullbackRestrictHomology b hb
              (T.subschemeι ≫ (S.D.comap b).subschemeι) n)).over U) := by
  set j := T.subschemeι ≫ (S.D.comap b).subschemeι
  set F := S.etaDerivedPullbackRestrictHomology b hb j
  have hperf : RingedSpace.IsPerfect (X := T.subscheme.toRingedSpace)
      (S.etaDerivedPullbackRestrict b hb j) :=
    RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback j.toLRSHom.toShHom _ hQ
  have hclopen := Scheme.Modules.isClopen_setOf_finiteLocallyFreeRank_eq F h₂ ρ
    (Stacks.AlgebraicGeometry.PerfectCohomology.exists_finset_finiteLocallyFreeRank_eq_zero
      T.subscheme _ hperf h₂)
  let Tρ : T.subscheme.Opens := ⟨_, hclopen.isOpen⟩
  refine ⟨Tρ, hclopen, fun V hV ↦ ?_, fun n t ht ↦ ?_⟩
  · set U := (S.D.comap b).subschemeι ⁻¹ᵁ (b ⁻¹ᵁ V)
    have hle : U ≤ (S.D.comap b).subschemeι ⁻¹ᵁ (b ⁻¹ᵁ S.locallyFreeLocus) := fun x hx ↦
      (S.mem_locallyFreeLocus_and_finrank_eq_of_isFreeOver ρ V hV hx).1
    have hcomap : T.comap U.ι = ⊥ := by
      rw [← Scheme.homOfLE_ι _ hle, Scheme.IdealSheafData.comap_comp, h₁,
        Scheme.IdealSheafData.comap_bot]
    have hker : T.subschemeι.ker ≤ U.ι.ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι, ← Scheme.IdealSheafData.map_bot,
        Scheme.IdealSheafData.le_map_iff_comap_le, hcomap]
    set g₀ := IsClosedImmersion.lift T.subschemeι U.ι hker
    have hrange : Set.range g₀.base ⊆ Set.range Tρ.ι.base := by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      have hy : T.subschemeι.base (g₀.base y) = U.ι.base y := by
        show (g₀ ≫ T.subschemeι).base y = _
        rw [IsClosedImmersion.lift_fac]
      have hxV : (j ≫ b).base (g₀.base y) ∈ V := by
        show b.base ((S.D.comap b).subschemeι.base (T.subschemeι.base (g₀.base y))) ∈ V
        rw [hy]
        exact y.2
      have hx := S.mem_locallyFreeLocus_and_finrank_eq_of_isFreeOver ρ V hV hxV
      intro n
      rw [@Scheme.Modules.finiteLocallyFreeRank_eq_finrank_stalk _ _ (h₂ n)]
      exact (congrArg (fun r : ℕ ↦ (r : ℤ)) (h₃ n _ hx.1)).trans (hx.2 n)
    refine ⟨IsOpenImmersion.lift Tρ.ι g₀ hrange, ?_⟩
    rw [IsOpenImmersion.lift_fac_assoc, IsClosedImmersion.lift_fac]
  · have hρn : 0 ≤ ρ n := by
      have := ht n
      omega
    obtain ⟨U, htU, hUT, I, ⟨e⟩, he⟩ := @Stacks.SheafOfModules.exists_free_nbhd_of_rank_eq _ _
      (Scheme.Modules.toRingSheafModule (F n)) (LocallyFreeRank.scheme_stalksNontrivial _)
      (@Scheme.Modules.isFiniteLocallyFree_toRingSheafModule _ (F n) (h₂ n)) (ρ n).toNat Tρ
      (fun s hs ↦ by
        have := hs n
        show (@Scheme.Modules.finiteLocallyFreeRank _ (F n) (h₂ n) s) = (ρ n).toNat
        omega) t ht
    refine ⟨U, htU, hUT, I, Finite.of_equiv _ e.symm, ?_, he⟩
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]
    omega

/-- For `b` of tag 0GTY, `Q` of tag 0F8U, `i : T ⟶ D'` of tag 0F8X and integers `ρ_n`, some open
and closed `T(ρ) ⊆ T` contains `D' ∩ b⁻¹(V)` scheme theoretically for every open `V` on which
each `H^n(M)` is locally free of rank `ρ_n`, and `H^n(Li^*Q)|_{T(ρ)}` has rank `ρ_n`. -/
@[stacks 0F8Y]
theorem exists_isClopen_rankStratum_goodBlowup (ρ : ℤ → ℤ) :
    ∃ Tρ : (S.pullbackSubscheme S.goodBlowupToBase S.isGoodOver_goodBlowupToBase).subscheme.Opens,
      IsClopen (Tρ : Set (S.pullbackSubscheme S.goodBlowupToBase
        S.isGoodOver_goodBlowupToBase).subscheme) ∧
      (∀ V : S.X.Opens,
        (∀ (n : ℤ), ∀ x ∈ V, ∃ U : S.X.Opens, x ∈ U ∧ U ≤ V ∧ ∃ ι : Type u, Finite ι ∧
          (Nat.card ι : ℤ) = ρ n ∧ Nonempty ((restrictModules S.X.toRingedSpace U).obj
            (S.cohomologySheaf n) ≅ _root_.SheafOfModules.free.{u} ι)) →
        ∃ g : ((S.D.comap S.goodBlowupToBase).subschemeι ⁻¹ᵁ
            (S.goodBlowupToBase ⁻¹ᵁ V)).toScheme ⟶ Tρ.toScheme,
          g ≫ Tρ.ι ≫
              (S.pullbackSubscheme S.goodBlowupToBase S.isGoodOver_goodBlowupToBase).subschemeι =
            ((S.D.comap S.goodBlowupToBase).subschemeι ⁻¹ᵁ (S.goodBlowupToBase ⁻¹ᵁ V)).ι) ∧
      ∀ (n : ℤ), ∀ t ∈ Tρ, ∃ U : (S.pullbackSubscheme S.goodBlowupToBase
        S.isGoodOver_goodBlowupToBase).subscheme.Opens, t ∈ U ∧ U ≤ Tρ ∧ ∃ I : Type u,
        Finite I ∧ (Nat.card I : ℤ) = ρ n ∧
          Nonempty (_root_.SheafOfModules.free.{u} I ≅
            (Scheme.Modules.toRingSheafModule (S.etaDerivedPullbackRestrictHomology
              S.goodBlowupToBase S.isGoodOver_goodBlowupToBase.pullbackDefined
              ((S.pullbackSubscheme S.goodBlowupToBase
                S.isGoodOver_goodBlowupToBase).subschemeι ≫
                  (S.D.comap S.goodBlowupToBase).subschemeι) n)).over U) :=
  S.exists_isClopen_rankStratum_of_subscheme S.goodBlowupToBase
    S.isGoodOver_goodBlowupToBase.pullbackDefined S.isPerfect_etaDerivedPullbackObject_goodBlowup
    _ (S.locallyOfFinitePresentation_and_comap_eq_bot_goodBlowupToBase _
      ((S.pullback S.goodBlowupToBase
        S.isGoodOver_goodBlowupToBase.pullbackDefined).ideal_goodChartSubscheme
          S.isGoodOver_goodBlowupToBase.isGoodTriple)).2
    (S.isFiniteLocallyFree_etaDerivedPullbackRestrictHomology_of_isGoodOver S.goodBlowupToBase
      S.isGoodOver_goodBlowupToBase)
    (fun n t hw ↦ (S.free_finrank_stalk_etaDerivedPullbackRestrictHomology_of_isGoodOver
      S.goodBlowupToBase S.isGoodOver_goodBlowupToBase
      S.flat_ι_comp_goodBlowupToBase_locallyFreeLocus n t hw).2) ρ

end AlgebraicGeometry.ComplexAndDivisorSituation

end
