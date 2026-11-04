module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyOverFieldSurjective
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Definition
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackClassOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ProperPushforwardGysin
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.VanishingUnconditional
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegree
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.EmbeddedPointCounterexample
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFundamentalClass
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ClosedSubschemeRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CycleCapRuleGeneric
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksCore.Tactic.StacksAttribute

/-!
# Bivariant classes towards a field are Chow classes

Let `k` be a field and let `X` be a scheme locally of finite type over `k`. **Stacks 0FBW**: cap
product with the fundamental class of the point,

  `A^p(X ⟶ Spec k) ⟶ CH_{-p}(X)`,   `c ↦ c ∩ [Spec k]`,

is an isomorphism for every `p ∈ ℤ`. Here `A^p(X ⟶ Spec k)` is the group of bivariant classes
read at the Gysin system `Stacks.Chow.gysinSystemOfInvertible` of the first Chern class of an
invertible module, over the base situation `Stacks.Chow.fieldChowSituation k` whose dimension
function is zero.

## Main results

* `Stacks.Chow.integralFundamentalClassIsFlatPullback_field` — over a field the fundamental class
  of an integral scheme `T` of dimension `r` is concentrated in degree `r`, where it is the flat
  pullback of `[Spec k]` (Stacks 02NK, 02R4).
* `Stacks.Chow.exists_properPushforward_fundamentalCycle_eq` — a cycle with non-negative
  coefficients is the proper pushforward of the fundamental cycle of a scheme `W` flat over the
  field of the right relative dimension.
* `Stacks.Chow.bivariantToBaseEval_bijective_field` — **Stacks 0FBW**: the canonical map is
  bijective.
* `Stacks.Chow.bivariantToBaseEquivField` — **Stacks 0FBW**: the identification
  `A^p(X ⟶ Spec k) ≃ CH_{-p}(X)` as an isomorphism of groups.
* `Stacks.Chow.bivariantChowClassToBaseEquivField` — **Stacks 0FBW** for the bivariant group in
  the form `Stacks.Chow.BivariantChowClass`, whose cap operations are maps.

## References

* [Stacks Project, Tag 0FBW](https://stacks.math.columbia.edu/tag/0FBW)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Relative dimension is local on the source.** If the open subschemes `U i` cover `X` and
each restriction `U i ⟶ S` of `f` has relative dimension `d` (Tag 02NJ), then so does `f`. -/
public theorem RelativeDimension.of_opensCover {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] {ι : Type*} (U : ι → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i) {d : ℕ}
    (h : ∀ i, RelativeDimension ((U i).ι ≫ f) d) : RelativeDimension f d := by
  intro s hs
  have hFT : LocallyOfFiniteType (f.fiberToSpecResidueField s) := by
    show LocallyOfFiniteType (Limits.pullback.snd f (S.fromSpecResidueField s))
    infer_instance
  have hlocal : ∀ w : f.fiber s, topologicalKrullDimAt (f.fiber s) w = (d : WithBot ℕ∞) := by
    intro w
    obtain ⟨i, hi⟩ := hU (f.fiberι s w)
    rw [← Scheme.Hom.topologicalKrullDimAt_fiber_fiberι f s w]
    exact topologicalKrullDimAt_fiber_eq_of_relativeDimension f (U i) d (h i) _ hi
  refine ⟨equidimensional_of_topologicalKrullDimAt_eq (S.residueField s) (f.fiber s)
    (f.fiberToSpecResidueField s) hlocal, ?_⟩
  rw [topologicalKrullDim_eq_iSup_localKrullDim]
  have hloc : ∀ w : f.fiber s, localKrullDim (f.fiber s) w = (d : WithBot ℕ∞) := fun w ↦ by
    rw [← topologicalKrullDimAt_eq_localKrullDim, hlocal w]
  simp_rw [hloc]
  have : Nonempty (f.fiber s) := hs
  exact iSup_const

/-- Relative dimension depends only on the morphism. -/
public theorem RelativeDimension.congr {X S : Scheme.{u}} {f f' : X ⟶ S}
    [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (hff' : f = f') {d : ℕ}
    (h : RelativeDimension f d) : RelativeDimension f' d :=
  hff' ▸ h

end AlgebraicGeometry

namespace Stacks.Chow

/-! ### Fundamental classes over a field -/

section Field

variable (k : Type u) [Field k]

/-- The base of `Stacks.Chow.fieldChowSituation` has delta-dimension at most zero. -/
theorem schemeDeltaDimension_id_fieldChowSituation_le :
    schemeDeltaDimension (fieldChowSituation k) (𝟙 (fieldChowSituation k).S) ≤
      ((0 : ℤ) : EInt) := by
  simpa using schemeDeltaDimension_le_zero_fieldChowSituation k (𝟙 (fieldChowSituation k).S)

/-- **Stacks 02NK and 02R4 over a field.** An integral scheme `T` locally of finite type over a
field has relative dimension `r = dim T` over it, its fundamental class vanishes outside degree
`r`, and in degree `r` it is the flat pullback of the fundamental class of the point. -/
theorem integralFundamentalClassIsFlatPullback_field :
    IntegralFundamentalClassIsFlatPullback (fieldChowSituation k)
      (flatPullbackDescends (fieldChowSituation k)) := by
  intro T sT _ _ sS _ hsS v _ hv
  subst hsS
  have hvT : sT = v := by rw [← hv, Category.comp_id]
  subst hvT
  have hnonneg := relativeDimension_fieldChowSituation_nonneg k sT (genericPoint T)
  set r : ℕ := (relativeDimension (fieldChowSituation k).dimensionFunction sT
    (genericPoint T)).toNat with hrdef
  have hrel : relativeDimension (fieldChowSituation k).dimensionFunction sT (genericPoint T) =
      (0 : ℤ) + (r : ℤ) := by
    rw [hrdef, zero_add, Int.toNat_of_nonneg hnonneg]
  refine ⟨r, relativeDimension_of_isIntegral_over_field k sT, fun k' hk' ↦ ?_, ?_⟩
  · rw [fundamentalChowClass, fundamentalCycle_eq_zero_of_ne (fieldChowSituation k) sT
      genericPoints_eq_singleton (by rw [hrel]; exact fun h ↦ hk' h.symm), map_zero]
  · exact (flatPullbackChow_fundamentalChowClass (fieldChowSituation k) sT
      (𝟙 (fieldChowSituation k).S) sT hv r (relativeDimension_of_isIntegral_over_field k sT) 0
      _ (schemeDeltaDimension_id_fieldChowSituation_le k)).symm

/-- Over a field, the flat pullback of `[Spec k]` along a scheme `W` flat of relative dimension
`r` is the fundamental class `[W]` in degree `r`. -/
theorem flatPullbackBaseClass_eq_fundamentalChowClass {W : Scheme.{u}}
    (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW] [Flat sW] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension sW r) :
    flatPullbackBaseClass (fieldChowSituation k) sW r hr
        (flatPullbackDescends (fieldChowSituation k)) =
      fundamentalChowClass (fieldChowSituation k) sW (-(-(r : ℤ))) := by
  unfold flatPullbackBaseClass baseFundamentalClass
  rw [flatPullbackChow_fundamentalChowClass (fieldChowSituation k)
    (pullback.fst sW (𝟙 (fieldChowSituation k).S) ≫ sW)
    (𝟙 (fieldChowSituation k).S ≫ 𝟙 (fieldChowSituation k).S)
    (pullback.snd sW (𝟙 (fieldChowSituation k).S)) _ r _ 0 _
    (by simpa using schemeDeltaDimension_id_fieldChowSituation_le k),
    chowGroupDegreeEquiv_fundamentalChowClass, chowGroupBaseUnitCollapse, AddEquiv.trans_apply,
    chowGroupDegreeEquiv_fundamentalChowClass, chowGroupEquivOfIso_apply,
    chowPushforwardOfIso_fundamentalChowClass]

end Field

/-! ### Cycles with non-negative coefficients as pushforwards of fundamental cycles -/

section Coproduct

variable (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  [LocallyOfFiniteType sX]

/-- A locally finite family of sets stays locally finite when each member is repeated finitely
many times. -/
theorem LocallyFinite.sigma_fin {A : Type*} [TopologicalSpace A] {I : Type*}
    {t : I → Set A} (ht : LocallyFinite t) (m : I → ℕ) :
    LocallyFinite fun j : (Σ i, Fin (m i)) ↦ t j.1 := by
  intro x
  obtain ⟨U, hU, hfin⟩ := ht x
  exact ⟨U, hU, (hfin.sigma fun _ _ ↦ Set.finite_univ).subset fun j hj ↦ ⟨hj, Set.mem_univ _⟩⟩

/-- **A cycle with non-negative coefficients is a pushforward of a fundamental cycle.** Over a
field, let `b` be an `n`-cycle on `X` with non-negative coefficients, `n = r`. There are a scheme
`W`, a proper morphism `g : W ⟶ X` with `W` of relative dimension `r` over the field, and
`g_*[W]_n = b`. -/
theorem exists_properPushforward_fundamentalCycle_eq (n : ℤ) (r : ℕ) (hrn : (r : ℤ) = n)
    (b : CycleGroup (fieldChowSituation k) sX n) (hb : ∀ x, 0 ≤ b.1 x) :
    ∃ (W : Scheme.{u}) (g : W ⟶ X) (_ : IsProper g) (_ : LocallyOfFiniteType (g ≫ sX)),
      AlgebraicGeometry.RelativeDimension (g ≫ sX) r ∧
        properPushforward (fieldChowSituation k) (g ≫ sX) sX g rfl n
          (fundamentalCycle (fieldChowSituation k) (g ≫ sX) n) = b := by
  classical
  let J : Type u := Σ x : ↥(Function.support (b.1 : X → ℤ)), Fin (b.1 x).toNat
  let Z : J → Scheme.{u} := fun j ↦ (integralComponentAt (j.1 : X)).subscheme
  let v : ∀ j, Z j ⟶ X := fun j ↦ (integralComponentAt (j.1 : X)).subschemeι
  have hZint : ∀ j, IsIntegral (Z j) := fun j ↦ isIntegral_integralComponentAt (j.1 : X)
  have hvgen : ∀ j, (v j).base (genericPoint (Z j)) = (j.1 : X) := fun j ↦
    genericPointOf_integralComponentAt (j.1 : X)
  have hlf : LocallyFinite fun j : J ↦ Set.range (v j) :=
    LocallyFinite.sigma_fin (locallyFinite_range_subschemeι_support (fieldChowSituation k) sX n b)
      (fun x ↦ (b.1 x).toNat)
  have hproper : IsProper (Sigma.desc v) := isProper_sigmaDesc_of_locallyFinite Z v hlf
  set g := Sigma.desc v with hgdef
  have hdimx : ∀ j : J,
      relativeDimension (fieldChowSituation k).dimensionFunction sX (j.1 : X) = n := fun j ↦
    (mem_cyclesOfDimension_iff_forall_point (fieldChowSituation k) sX n b.1).1 b.2 _ j.1.2
  have hιg : ∀ j, Sigma.ι Z j ≫ g ≫ sX = v j ≫ sX := fun j ↦ by
    rw [hgdef, Sigma.ι_desc_assoc]
  have hdimZ : ∀ j,
      schemeDeltaDimension (fieldChowSituation k) (Sigma.ι Z j ≫ g ≫ sX) = (n : EInt) := fun j ↦ by
    rw [schemeDeltaDimension_eq_genericPoint, hιg, relativeDimension_comp_closedImmersion, hvgen,
      hdimx]
  have hdimle : ∀ j (z : Z j),
      relativeDimension (fieldChowSituation k).dimensionFunction (g ≫ sX) (Sigma.ι Z j z) ≤ n :=
    fun j z ↦ by
      rw [← relativeDimension_comp_isOpenImmersion, hιg, relativeDimension_comp_closedImmersion]
      refine relativeDimension_le_of_schemeDeltaDimension_le (fieldChowSituation k) sX (v j)
        (le_of_eq ?_) z
      rw [schemeDeltaDimension_eq_genericPoint, relativeDimension_comp_closedImmersion, hvgen,
        hdimx]
  have hrelZ : ∀ j, AlgebraicGeometry.RelativeDimension (Sigma.ι Z j ≫ g ≫ sX) r := fun j ↦ by
    have H := relativeDimension_of_isIntegral_over_field k (Sigma.ι Z j ≫ g ≫ sX)
    have hη : (relativeDimension (fieldChowSituation k).dimensionFunction (Sigma.ι Z j ≫ g ≫ sX)
        (genericPoint (Z j))).toNat = r := by
      rw [hιg, relativeDimension_comp_closedImmersion, hvgen, hdimx, ← hrn, Int.toNat_natCast]
    rwa [hη] at H
  have hrel : AlgebraicGeometry.RelativeDimension (g ≫ sX) r := by
    refine AlgebraicGeometry.RelativeDimension.of_opensCover (g ≫ sX)
      (fun j ↦ (Sigma.ι Z j).opensRange) (fun x ↦ ?_) (fun j ↦ ?_)
    · exact exists_mem_range_sigmaι Z x
    · have H := AlgebraicGeometry.RelativeDimension.comp_isOpenImmersion
        (Sigma.ι Z j).isoOpensRange.inv (Sigma.ι Z j ≫ g ≫ sX) (hrelZ j)
      refine AlgebraicGeometry.RelativeDimension.congr ?_ H
      rw [← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
  refine ⟨∐ Z, g, hproper, inferInstance, hrel, ?_⟩
  have hfund : ∀ j (z : Z j),
      (fundamentalCycle (fieldChowSituation k) (g ≫ sX) n).1 (Sigma.ι Z j z) =
        if z = genericPoint (Z j) then 1 else 0 := by
    intro j z
    have h1 := cycleAssociatedToClosedSubscheme_apply_of_isOpenImmersion (fieldChowSituation k)
      (fieldChowSituation k) (Sigma.ι Z j ≫ g ≫ sX) (g ≫ sX) (Sigma.ι Z j) (𝟙 _) (𝟙 _)
      (Sigma.ι Z j) (by simp) (by simp) n
      (schemeDeltaDimension_le_of_forall_relativeDimension_le (fieldChowSituation k) (g ≫ sX)
        (𝟙 _) fun w ↦ by
        obtain ⟨j', z', rfl⟩ := exists_mem_range_sigmaι Z w
        exact hdimle j' z')
      (fun x ↦ relativeDimension_comp_isOpenImmersion _ _ _ x) z
    show (fundamentalCycle (fieldChowSituation k) (g ≫ sX) n).1 (Sigma.ι Z j z) = _
    rw [fundamentalCycle, ← h1]
    exact fundamentalCycle_apply_of_isIntegral (fieldChowSituation k) (Sigma.ι Z j ≫ g ≫ sX)
      (hdimZ j) z
  have hres : ∀ x : (∐ Z : Scheme.{u}), Function.Bijective ((g.residueFieldMap x).hom) := by
    have : SurjectiveOnStalks g := surjectiveOnStalks_sigmaDesc Z v
    exact fun x ↦ bijective_residueFieldMap_of_surjective_stalkMap g x
      (g.stalkMap_surjective x)
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y
  have hterm : ∀ w : (∐ Z : Scheme.{u}),
      (fundamentalCycle (fieldChowSituation k) (g ≫ sX) n).1 w *
        (if relativeDimension (fieldChowSituation k).dimensionFunction (g ≫ sX) w =
            relativeDimension (fieldChowSituation k).dimensionFunction sX (g.base w) then
          (g.residueDegree w : ℤ) else 0) =
        (fundamentalCycle (fieldChowSituation k) (g ≫ sX) n).1 w := by
    intro w
    rw [relativeDimension_comp_of_bijective_residueFieldMap
        (fieldChowSituation k).dimensionFunction g sX w (hres w),
      residueDegree_eq_one_of_bijective_residueFieldMap g w (hres w)]
    simp
  rw [properPushforward_apply, finsum_mem_congr rfl (fun w _ ↦ hterm w)]
  set F : (∐ Z : Scheme.{u}) → ℤ :=
    fun w ↦ (fundamentalCycle (fieldChowSituation k) (g ≫ sX) n).1 w with hF
  have hgι : ∀ j (z : Z j), g.base (Sigma.ι Z j z) = (v j).base z := fun j z ↦ by
    rw [← Scheme.Hom.comp_apply, hgdef, Sigma.ι_desc]
  have hjy : ∀ j, g.base (Sigma.ι Z j (genericPoint (Z j))) = y → (j.1 : X) = y := fun j h ↦
    (hvgen j).symm.trans ((hgι j _).symm.trans h)
  by_cases hy : b.1 y = 0
  · rw [hy]
    refine finsum_mem_eq_zero_of_forall_eq_zero fun w hw ↦ ?_
    obtain ⟨j, z, rfl⟩ := exists_mem_range_sigmaι Z w
    show (fundamentalCycle (fieldChowSituation k) (g ≫ sX) n).1 (Sigma.ι Z j z) = 0
    rw [hfund]
    split_ifs with hz
    · subst hz
      exact absurd (hjy j hw ▸ j.1.2) (by simpa using hy)
    · rfl
  · set y' : ↥(Function.support (b.1 : X → ℤ)) := ⟨y, hy⟩
    let e : Fin (b.1 y).toNat → (∐ Z : Scheme.{u}) := fun i ↦
      Sigma.ι Z ⟨y', i⟩ (genericPoint (Z ⟨y', i⟩))
    have he_inj : Function.Injective e := by
      intro i i' hii'
      have h' : sigmaMk Z ⟨⟨y', i⟩, genericPoint (Z ⟨y', i⟩)⟩ =
          sigmaMk Z ⟨⟨y', i'⟩, genericPoint (Z ⟨y', i'⟩)⟩ := by
        rw [sigmaMk_mk, sigmaMk_mk]
        exact hii'
      have h2 : (⟨y', i⟩ : J) = ⟨y', i'⟩ := congrArg Sigma.fst ((sigmaMk Z).injective h')
      exact eq_of_heq (Sigma.mk.inj h2).2
    have hsupp : g.base ⁻¹' {y} ∩ Function.support F = Set.range e ∩ Function.support F := by
      ext w
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Function.mem_support, Set.mem_range]
      obtain ⟨j, z, rfl⟩ := exists_mem_range_sigmaι Z w
      simp only [hF, hfund]
      constructor
      · rintro ⟨hgy, hne⟩
        refine ⟨?_, hne⟩
        split_ifs at hne with hz
        · subst hz
          obtain ⟨⟨x, hx⟩, i⟩ := j
          obtain rfl : x = y := hjy _ hgy
          exact ⟨i, rfl⟩
        · exact absurd rfl hne
      · rintro ⟨⟨i, hi⟩, hne⟩
        refine ⟨?_, hne⟩
        rw [← hi, hgι, hvgen]
    rw [finsum_mem_inter_support_eq F (g.base ⁻¹' {y}) (Set.range e) hsupp,
      ← Set.image_univ, finsum_mem_image he_inj.injOn]
    have hone : ∀ i, F (e i) = 1 := fun i ↦ by
      rw [hF]
      show (fundamentalCycle (fieldChowSituation k) (g ≫ sX) n).1 (Sigma.ι Z ⟨y', i⟩ _) = 1
      rw [hfund, if_pos rfl]
    simp only [hone]
    rw [finsum_mem_univ, finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact Int.toNat_of_nonneg (hb y)

end Coproduct

/-! ### Stacks 0FBW -/

section Identification

variable (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  [LocallyOfFiniteType sX]

/-- The canonical map of Stacks 0FBW carries the proper pushforward `g_* ∘ d` of Stacks 0EPK to
the proper pushforward of the image of `d`. -/
theorem bivariantToBaseEval_bivariantProperPushforward (C : ChowSituation.{u}) {X W : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (g : W ⟶ X) [IsProper g]
    [LocallyOfFiniteType (g ≫ sX)] (p : ℤ)
    (d : BivariantClass C (gysinSystemOfInvertible C) (g ≫ sX) (𝟙 C.S) (g ≫ sX)
      (comp_comp_structureMorphism_eq (rfl : g ≫ sX = g ≫ sX) (Category.comp_id sX)) p) :
    bivariantToBaseEval C (gysinSystemOfInvertible C) sX p
        (bivariantProperPushforwardOfNaturality C (gysinSystemOfInvertible C) (g ≫ sX) sX (𝟙 C.S) g
          sX rfl (Category.comp_id sX) (properPushforwardDescends C) p
          (gysinSystemOfInvertible_isNaturalUnderProperPushforward C)
          (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C) d) =
      properChowPushforward C (g ≫ sX) sX g rfl (-p) (properPushforwardDescends C _ _ g rfl _)
        (bivariantToBaseEval C (gysinSystemOfInvertible C) (g ≫ sX) p d) := by
  rw [bivariantToBaseEval_apply, bivariantProperPushforwardOfNaturality_cap,
    bivariantProperPushforwardCap_apply]
  exact chowGroupBaseUnitCollapse_properChowPushforward C sX g (properPushforwardDescends C) p _

/-- **Stacks 0FBW, surjectivity.** Over a field, every Chow class of `X` in degree `-p` is
`c ∩ [Spec k]` for a bivariant class `c ∈ A^p(X ⟶ Spec k)`. -/
theorem bivariantToBaseEval_surjective_field (p : ℤ) :
    Function.Surjective
      (bivariantToBaseEval (fieldChowSituation k)
        (gysinSystemOfInvertible (fieldChowSituation k)) sX p) := by
  have hcyc := mem_cyclesOfDimension_iff_forall_point (fieldChowSituation k) sX (-p)
  have hpos : ∀ b : CycleGroup (fieldChowSituation k) sX (-p), (∀ x, 0 ≤ b.1 x) →
      QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) sX (-p)) b ∈
        (bivariantToBaseEval (fieldChowSituation k)
          (gysinSystemOfInvertible (fieldChowSituation k)) sX p).range := by
    intro b hb
    by_cases hp : 0 ≤ -p
    · obtain ⟨r, hr⟩ := Int.eq_ofNat_of_zero_le hp
      obtain rfl : p = -(r : ℤ) := by omega
      obtain ⟨W, g, hgp, hgt, hrel, hpush⟩ :=
        exists_properPushforward_fundamentalCycle_eq k sX (-(-(r : ℤ))) r (by ring) b hb
      have : Flat (g ≫ sX) := inferInstance
      refine ⟨bivariantProperPushforwardOfNaturality (fieldChowSituation k)
        (gysinSystemOfInvertible (fieldChowSituation k)) (g ≫ sX) sX
        (𝟙 (fieldChowSituation k).S) g sX rfl
        (Category.comp_id sX) (properPushforwardDescends (fieldChowSituation k)) (-(r : ℤ))
        (gysinSystemOfInvertible_isNaturalUnderProperPushforward (fieldChowSituation k))
        (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward (fieldChowSituation k))
        (flatPullbackBivariantClassOfInvertible (fieldChowSituation k) (g ≫ sX)
          (𝟙 (fieldChowSituation k).S) (g ≫ sX)
          (comp_comp_structureMorphism_eq (rfl : g ≫ sX = g ≫ sX) (Category.comp_id sX)) r
          hrel), ?_⟩
      rw [bivariantToBaseEval_bivariantProperPushforward]
      show properChowPushforward (fieldChowSituation k) (g ≫ sX) sX g rfl (-(-(r : ℤ))) _
        (flatPullbackBaseClass (fieldChowSituation k) (g ≫ sX) r hrel
          (flatPullbackDescends (fieldChowSituation k))) = _
      rw [flatPullbackBaseClass_eq_fundamentalChowClass, fundamentalChowClass,
        properChowPushforward_mk, hpush]
    · have hb0 : b = 0 := by
        refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
        by_contra hx
        have h1 := (hcyc b.1).1 b.2 x hx
        have h2 := relativeDimension_fieldChowSituation_nonneg k sX x
        exact hp (h1 ▸ h2)
      rw [hb0, map_zero]
      exact zero_mem _
  intro α
  induction α using QuotientAddGroup.induction_on with
  | H a =>
    have hmem : ∀ c : AlgebraicCycle X ℤ, c ∈ cyclesOfDimension (fieldChowSituation k) sX (-p) →
        ∀ c' : AlgebraicCycle X ℤ, (∀ x, c' x ≠ 0 → c x ≠ 0) →
          c' ∈ cyclesOfDimension (fieldChowSituation k) sX (-p) := fun c hc c' hc' ↦
      (hcyc c').2 fun x hx ↦ (hcyc c).1 hc x (hc' x hx)
    let P : CycleGroup (fieldChowSituation k) sX (-p) := ⟨a.1⁺, hmem a.1 a.2 _ fun x hx h ↦
      hx (by simp [h])⟩
    let N : CycleGroup (fieldChowSituation k) sX (-p) := ⟨a.1⁻, hmem a.1 a.2 _ fun x hx h ↦
      hx (by simp [h])⟩
    have ha : a = P - N := by
      refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
      show a.1 x = (a.1 x)⁺ - (a.1 x)⁻
      exact (posPart_sub_negPart (a.1 x)).symm
    have hP := hpos P fun x ↦ posPart_nonneg (a.1 x)
    have hN := hpos N fun x ↦ negPart_nonneg (a.1 x)
    show QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) sX (-p)) a ∈
      (bivariantToBaseEval (fieldChowSituation k)
        (gysinSystemOfInvertible (fieldChowSituation k)) sX p).range
    rw [ha, map_sub]
    exact sub_mem hP hN

/-- Let `k` be a field and `X` a scheme locally of finite type over `k`. For
every `p ∈ ℤ` the canonical map `A^p(X ⟶ Spec k) ⟶ CH_{-p}(X)`, `c ↦ c ∩ [Spec k]`, is
bijective. Here `A^p(X ⟶ Spec k)` is the group of bivariant classes of degree `p` for the
structure morphism (Stacks 0B76), read at the Gysin system of the first Chern class of an
invertible module, and the cap product with the fundamental class of the point is read on `X`
through the first projection `X ×_{Spec k} Spec k ≅ X`. -/
@[stacks 0FBW "the canonical map A^p(X → Spec k) → CH_{-p}(X), c ↦ c ∩ [Spec k], is bijective"]
theorem bivariantToBaseEval_bijective_field (p : ℤ) :
    Function.Bijective
      (bivariantToBaseEval (fieldChowSituation k)
        (gysinSystemOfInvertible (fieldChowSituation k)) sX p) :=
  ⟨bivariantToBaseEval_injective (fieldChowSituation k)
      (gysinSystemOfInvertible (fieldChowSituation k)) sX p
      (flatPullbackDescends (fieldChowSituation k))
      (integralFundamentalClassIsFlatPullback_field k),
    bivariantToBaseEval_surjective_field k sX p⟩

/-- The canonical identification `A^p(X ⟶ Spec k) = CH_{-p}(X)` over a field,
as an isomorphism of abelian groups: cap product with the fundamental class of the point. -/
@[stacks 0FBW "the canonical identification A^p(X → Spec k) = CH_{-p}(X) as an isomorphism of \
groups"]
def bivariantToBaseEquivField (p : ℤ) :
    bivariantToBase (fieldChowSituation k) (gysinSystemOfInvertible (fieldChowSituation k)) sX p ≃+
      chowGroup (fieldChowSituation k) sX (-p) :=
  AddEquiv.ofBijective _ (bivariantToBaseEval_bijective_field k sX p)

/-- The identification of Stacks 0FBW is cap product with the fundamental class of the point. -/
@[simp]
theorem bivariantToBaseEquivField_apply (p : ℤ)
    (c : bivariantToBase (fieldChowSituation k) (gysinSystemOfInvertible (fieldChowSituation k))
      sX p) :
    bivariantToBaseEquivField k sX p c =
      chowGroupBaseUnitCollapse (fieldChowSituation k) sX p
        (c.cap (𝟙 (fieldChowSituation k).S) 0 (baseFundamentalClass (fieldChowSituation k))) :=
  rfl

/-- For the bivariant group `A^p(X ⟶ Spec k)` of Stacks 0B76 in the form
`Stacks.Chow.BivariantChowClass`, whose cap operations are plain maps, cap product with the
fundamental class of the point is an isomorphism `A^p(X ⟶ Spec k) ≃ CH_{-p}(X)`. -/
@[stacks 0FBW "the canonical identification A^p(X → Spec k) = CH_{-p}(X), c ↦ c ∩ [Spec k], for \
the bivariant group of Stacks 0B76 whose cap operations are maps"]
def bivariantChowClassToBaseEquivField (p : ℤ) :
    BivariantChowClass (fieldChowSituation k) sX (𝟙 (fieldChowSituation k).S) sX
        (Category.comp_id sX) p ≃+
      chowGroup (fieldChowSituation k) sX (-p) :=
  BivariantChowClass.addEquivBivariantClass.trans (bivariantToBaseEquivField k sX p)

/-- The identification of Stacks 0FBW is `c ↦ c ∩ [Spec k]`, read on `X` through the first
projection `X ×_{Spec k} Spec k ≅ X`. -/
@[simp]
theorem bivariantChowClassToBaseEquivField_apply (p : ℤ)
    (c : BivariantChowClass (fieldChowSituation k) sX (𝟙 (fieldChowSituation k).S) sX
      (Category.comp_id sX) p) :
    bivariantChowClassToBaseEquivField k sX p c =
      chowGroupBaseUnitCollapse (fieldChowSituation k) sX p
        (c.cap (𝟙 (fieldChowSituation k).S) 0 (baseFundamentalClass (fieldChowSituation k))) :=
  rfl

end Identification

end Stacks.Chow

end
