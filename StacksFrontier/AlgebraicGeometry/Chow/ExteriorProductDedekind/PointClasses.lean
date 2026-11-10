module

public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.BaseDecomposition
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.PointClassCommutingField

/-!
# Bivariant classes towards a Dedekind base over its zero-dimensional components

Let `(S, δ)` be as in Stacks section 42.63 and `S₀ ⊆ S` the union of its zero-dimensional
irreducible components (`Stacks.Chow.clopenPoints`): a disjoint union of spectra of fields, open
and closed in `S`, with `δ = 0`. Over `S₀` the argument of Stacks 0FBW and 0FBX applies: a cycle
with non-negative coefficients on a scheme over `S₀` is `g_*[W]` for `W` a coproduct of integral
schemes, flat over `S`, and the bivariant class `g_* ∘ (W ⟶ S)^*` of Stacks 0EPK and 0B78
commutes with every bivariant class.

## Main definitions

* `Stacks.Chow.properFlatPullbackClass` — the class `g_* ∘ (W ⟶ S)^* ∈ A^{-r}(X ⟶ S)` for
  `g : W ⟶ X` proper with `W` flat of relative dimension `r` over `S`.

## Main results

* `Stacks.Chow.exists_properPushforward_fundamentalCycle_eq_of_mem_clopenPoints` — a cycle with
  non-negative coefficients on a scheme over `S₀` is the pushforward of a fundamental cycle of a
  scheme flat over `S`.
* `Stacks.Chow.bivariantCommute_properFlatPullbackClass` — `g_* ∘ (W ⟶ S)^*` commutes with every
  bivariant class, in the sense of Stacks 0FA2.
* `Stacks.Chow.properFlatPullbackClass_cap_eq_zero` — it vanishes on test schemes over which `W`
  has empty fibre product.
* `Stacks.Chow.properFlatPullbackClass_cap_fundamentalChowClass` — at the test scheme `S₀` it
  sends `[S₀]₀` to `g_*[W]`.

## References

* [Stacks Project, Tag 0FBW](https://stacks.math.columbia.edu/tag/0FBW)
* [Stacks Project, Tag 0FBX](https://stacks.math.columbia.edu/tag/0FBX)
* [Stacks Project, Tag 0FC6](https://stacks.math.columbia.edu/tag/0FC6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Cycles over the points as pushforwards of fundamental cycles -/

section Generation

variable {C : ChowSituation.{u}} (hC : IsDedekindChowBase C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (hX : ∀ x : X, sX.base x ∈ clopenPoints C)

include hC hX in
/-- A cycle over the points with non-negative coefficients is a pushforward of a fundamental
cycle: let `X` be a scheme locally of finite type over a Dedekind base, lying over the union
`S₀` of the zero-dimensional components, and let `b` be an `n`-cycle on `X` with non-negative
coefficients, `n = r`. There are a scheme `W`, a proper morphism `g : W ⟶ X` with `W` flat of
relative dimension `r` over the base, and `g_*[W]_n = b`. -/
theorem exists_properPushforward_fundamentalCycle_eq_of_mem_clopenPoints (n : ℤ) (r : ℕ)
    (hrn : (r : ℤ) = n) (b : CycleGroup C sX n) (hb : ∀ x, 0 ≤ b.1 x) :
    ∃ (W : Scheme.{u}) (g : W ⟶ X) (_ : IsProper g) (_ : LocallyOfFiniteType (g ≫ sX))
      (_ : Flat (g ≫ sX)), AlgebraicGeometry.RelativeDimension (g ≫ sX) r ∧
        properPushforward C (g ≫ sX) sX g rfl n (fundamentalCycle C (g ≫ sX) n) = b := by
  classical
  let J : Type u := Σ x : ↥(Function.support (b.1 : X → ℤ)), Fin (b.1 x).toNat
  let Z : J → Scheme.{u} := fun j ↦ (integralComponentAt (j.1 : X)).subscheme
  let v : ∀ j, Z j ⟶ X := fun j ↦ (integralComponentAt (j.1 : X)).subschemeι
  have hZint : ∀ j, IsIntegral (Z j) := fun j ↦ isIntegral_integralComponentAt (j.1 : X)
  have hvgen : ∀ j, (v j).base (genericPoint (Z j)) = (j.1 : X) := fun j ↦
    genericPointOf_integralComponentAt (j.1 : X)
  have hlf : LocallyFinite fun j : J ↦ Set.range (v j) :=
    LocallyFinite.sigma_fin (locallyFinite_range_subschemeι_support C sX n b)
      (fun x ↦ (b.1 x).toNat)
  have hproper : IsProper (Sigma.desc v) := isProper_sigmaDesc_of_locallyFinite Z v hlf
  set g := Sigma.desc v with hgdef
  have hlft : LocallyOfFiniteType (g ≫ sX) := inferInstance
  have hdimx : ∀ j : J,
      relativeDimension C.dimensionFunction sX (j.1 : X) = n := fun j ↦
    (mem_cyclesOfDimension_iff_forall_point C sX n b.1).1 b.2 _ j.1.2
  have hιg : ∀ j, Sigma.ι Z j ≫ g ≫ sX = v j ≫ sX := fun j ↦ by
    rw [hgdef, Sigma.ι_comp_desc_assoc]
  have hdimη : ∀ j, relativeDimension C.dimensionFunction (Sigma.ι Z j ≫ g ≫ sX)
      (genericPoint (Z j)) = n := fun j ↦ by
    rw [hιg, relativeDimension_comp_closedImmersion, hvgen, hdimx]
  have hdimZ : ∀ j,
      schemeDeltaDimension C (Sigma.ι Z j ≫ g ≫ sX) = (n : EInt) := fun j ↦ by
    rw [schemeDeltaDimension_eq_genericPoint, hdimη]
  have hdimle : ∀ j (z : Z j),
      relativeDimension C.dimensionFunction (g ≫ sX) (Sigma.ι Z j z) ≤ n := by
    intro j z
    rw [← relativeDimension_comp_isOpenImmersion, hιg, relativeDimension_comp_closedImmersion]
    refine relativeDimension_le_of_schemeDeltaDimension_le C sX (v j)
      (le_of_eq ?_) z
    simpa only [hιg] using hdimZ j
  have hpt : ∀ (j : J) (z : Z j), (Sigma.ι Z j ≫ g ≫ sX).base z ∈ clopenPoints C := fun j z ↦ by
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact hX _
  have hrelZ : ∀ j, AlgebraicGeometry.RelativeDimension (Sigma.ι Z j ≫ g ≫ sX) r := fun j ↦ by
    have H := relativeDimension_of_irreducibleSpace (Sigma.ι Z j ≫ g ≫ sX) fun z ↦ by
      let _ := (hC.isField_stalk_of_mem_clopenPoints (hpt j z)).toField
      refine ⟨inferInstance, ?_⟩
      rw [ringKrullDim_eq_zero_of_field]
      exact zero_le_one
    have h1 := relativeDimension_comp_eq_add_trdeg C.dimensionFunction (𝟙 C.S)
      (Sigma.ι Z j ≫ g ≫ sX) (genericPoint (Z j))
    rw [Category.comp_id, relativeDimension_id,
      hC.dimensionFunction_eq_zero_of_mem_clopenPoints (hpt j _), zero_add, hdimη j] at h1
    have hη : Cardinal.toNat (residueTrdeg (Sigma.ι Z j ≫ g ≫ sX) (genericPoint (Z j))) = r := by
      have h3 : ((Cardinal.toNat (residueTrdeg (Sigma.ι Z j ≫ g ≫ sX) (genericPoint (Z j))) : ℕ) :
          ℤ) = (r : ℤ) := h1.symm.trans hrn.symm
      exact_mod_cast h3
    rwa [hη] at H
  have hrel : AlgebraicGeometry.RelativeDimension (g ≫ sX) r := by
    refine AlgebraicGeometry.RelativeDimension.of_opensCover (g ≫ sX)
      (fun j ↦ (Sigma.ι Z j).opensRange) (fun x ↦ ?_) (fun j ↦ ?_)
    · exact exists_mem_range_sigmaι Z x
    · have H := AlgebraicGeometry.RelativeDimension.comp_isOpenImmersion
        (Sigma.ι Z j).isoOpensRange.inv (Sigma.ι Z j ≫ g ≫ sX) (hrelZ j)
      refine AlgebraicGeometry.RelativeDimension.congr ?_ H
      rw [← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
  have hflat : Flat (g ≫ sX) := by
    refine Flat.of_stalkMap (g ≫ sX) fun x ↦ ?_
    let _ := (hC.isField_stalk_of_mem_clopenPoints (by
      rw [Scheme.Hom.comp_apply]; exact hX _ : (g ≫ sX).base x ∈ clopenPoints C)).toField
    rw [RingHom.Flat]
    infer_instance
  refine ⟨∐ Z, g, hproper, hlft, hflat, hrel, ?_⟩
  have hfund : ∀ j (z : Z j),
      (fundamentalCycle C (g ≫ sX) n).1 (Sigma.ι Z j z) =
        if z = genericPoint (Z j) then 1 else 0 := by
    intro j z
    have h1 := cycleAssociatedToClosedSubscheme_apply_of_isOpenImmersion C
      C (Sigma.ι Z j ≫ g ≫ sX) (g ≫ sX) (Sigma.ι Z j) (𝟙 _) (𝟙 _)
      (Sigma.ι Z j) (by simp) (by simp) n
      (schemeDeltaDimension_le_of_forall_relativeDimension_le C (g ≫ sX)
        (𝟙 _) fun w ↦ by
        obtain ⟨j', z', rfl⟩ := exists_mem_range_sigmaι Z w
        exact hdimle j' z')
      (fun x ↦ relativeDimension_comp_isOpenImmersion _ _ _ x) z
    change (fundamentalCycle C (g ≫ sX) n).1 (Sigma.ι Z j z) = _
    rw [fundamentalCycle, ← h1]
    exact fundamentalCycle_apply_of_isIntegral C (Sigma.ι Z j ≫ g ≫ sX)
      (hdimZ j) z
  have hres : ∀ x : (∐ Z : Scheme.{u}), Function.Bijective ((g.residueFieldMap x).hom) := by
    have : SurjectiveOnStalks g := surjectiveOnStalks_sigmaDesc Z v
    exact fun x ↦ bijective_residueFieldMap_of_surjective_stalkMap g x
      (g.stalkMap_surjective x)
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y
  have hterm : ∀ w : (∐ Z : Scheme.{u}),
      (fundamentalCycle C (g ≫ sX) n).1 w *
        (if relativeDimension C.dimensionFunction (g ≫ sX) w =
            relativeDimension C.dimensionFunction sX (g.base w) then
          (g.residueDegree w : ℤ) else 0) =
        (fundamentalCycle C (g ≫ sX) n).1 w := by
    intro w
    rw [relativeDimension_comp_of_bijective_residueFieldMap
        C.dimensionFunction g sX w (hres w),
      residueDegree_eq_one_of_bijective_residueFieldMap g w (hres w)]
    simp
  rw [properPushforward_apply, finsum_mem_congr rfl (fun w _ ↦ hterm w)]
  set F : (∐ Z : Scheme.{u}) → ℤ :=
    fun w ↦ (fundamentalCycle C (g ≫ sX) n).1 w with hF
  have hgη : ∀ j, g.base (Sigma.ι Z j (genericPoint (Z j))) = (j.1 : X) := fun j ↦ by
    rw [← hvgen, ← Scheme.Hom.comp_apply, hgdef, Sigma.ι_comp_desc]
  by_cases hy : b.1 y = 0
  · rw [hy]
    refine finsum_mem_eq_zero_of_forall_eq_zero fun w hw ↦ ?_
    obtain ⟨j, z, rfl⟩ := exists_mem_range_sigmaι Z w
    change (fundamentalCycle C (g ≫ sX) n).1 (Sigma.ι Z j z) = 0
    rw [hfund]
    split_ifs with hz
    · subst hz
      exact absurd ((hgη j).symm.trans hw ▸ j.1.2) (by simpa using hy)
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
          have hjy := (hgη j).symm.trans hgy
          obtain ⟨⟨x, hx⟩, i⟩ := j
          obtain rfl : x = y := hjy
          exact ⟨i, rfl⟩
        · exact absurd rfl hne
      · rintro ⟨⟨i, hi⟩, hne⟩
        refine ⟨?_, hne⟩
        rw [← hi, hgη]
    rw [finsum_mem_inter_support_eq F (g.base ⁻¹' {y}) (Set.range e) hsupp,
      ← Set.image_univ, finsum_mem_image he_inj.injOn]
    have hone : ∀ i, F (e i) = 1 := fun i ↦ by
      rw [hF]
      change (fundamentalCycle C (g ≫ sX) n).1 (Sigma.ι Z ⟨y', i⟩ _) = 1
      rw [hfund, ite_eq_left rfl]
    simp only [hone]
    rw [finsum_mem_univ, finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact Int.toNat_of_nonneg (hb y)

end Generation

/-! ### The class `g_* ∘ (W ⟶ S)^*` -/

section ProperFlat

variable (C : ChowSituation.{u}) {X W : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (g : W ⟶ X) [IsProper g] [LocallyOfFiniteType (g ≫ sX)] [Flat (g ≫ sX)] (r : ℕ)
  (hr : AlgebraicGeometry.RelativeDimension (g ≫ sX) r)

/-- The flat-pullback class `(W ⟶ S)^* ∈ A^{-r}(W ⟶ S)` of Stacks 0B78. -/
def baseFlatPullbackClass :
    BivariantClass C (gysinSystemOfInvertible C) (g ≫ sX) (𝟙 C.S) (g ≫ sX)
      (comp_comp_structureMorphism_eq (rfl : g ≫ sX = g ≫ sX) (Category.comp_id sX))
      (-(r : ℤ)) :=
  flatPullbackBivariantClassOfInvertible C (g ≫ sX) (𝟙 C.S) (g ≫ sX)
    (comp_comp_structureMorphism_eq (rfl : g ≫ sX = g ≫ sX) (Category.comp_id sX)) r hr

/-- The class `g_* ∘ (W ⟶ S)^* ∈ A^{-r}(X ⟶ S)` of Stacks 0EPK and 0B78, for `g : W ⟶ X`
proper with `W` flat of relative dimension `r` over the base. -/
def properFlatPullbackClass : bivariantToBase C (gysinSystemOfInvertible C) sX (-(r : ℤ)) :=
  bivariantProperPushforwardOfNaturality C (gysinSystemOfInvertible C) (g ≫ sX) sX (𝟙 C.S) g sX
    rfl (Category.comp_id sX) (properPushforwardDescends C) (-(r : ℤ))
    (gysinSystemOfInvertible_isNaturalUnderProperPushforward C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C)
    (baseFlatPullbackClass C sX g r hr)

/-- `properFlatPullbackClass` is the proper pushforward along `g` of `baseFlatPullbackClass`. -/
theorem isBivariantProperPushforward_properFlatPullbackClass :
    IsBivariantProperPushforward C (gysinSystemOfInvertible C) (g ≫ sX) sX (𝟙 C.S) g sX rfl
      (Category.comp_id sX) (properPushforwardDescends C) (-(r : ℤ))
      (baseFlatPullbackClass C sX g r hr) (properFlatPullbackClass C sX g r hr) :=
  isBivariantProperPushforward_bivariantProperPushforwardOfNaturality C
    (gysinSystemOfInvertible C) (g ≫ sX) sX (𝟙 C.S) g sX rfl (Category.comp_id sX)
    (properPushforwardDescends C) (-(r : ℤ))
    (gysinSystemOfInvertible_isNaturalUnderProperPushforward C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C)
    (baseFlatPullbackClass C sX g r hr)

/-- `g_* ∘ (W ⟶ S)^*` commutes with every bivariant class, in the sense of Stacks 0FA2. -/
theorem bivariantCommute_properFlatPullbackClass {Y Z : Scheme.{u}} (sZ : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] (f : Y ⟶ Z) [LocallyOfFiniteType f] (q : ℤ)
    (c' : BivariantClass C (gysinSystemOfInvertible C) (f ≫ sZ) sZ f rfl q) :
    BivariantCommute C (gysinSystemOfInvertible C) sZ (pullback.snd sX sZ) f (-(r : ℤ)) q
      (bivariantToBaseRestrictionHom C (gysinSystemOfInvertible C) sX sZ (-(r : ℤ))
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (properFlatPullbackClass C sX g r hr)) c' := by
  have hsq : IsPullback (pullback.fst (g ≫ sX) sZ)
      (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) (g ≫ sX) sZ := by
    rw [bivariantPushforwardBaseChange_snd]
    exact IsPullback.of_hasPullback (g ≫ sX) sZ
  have : LocallyOfFiniteType (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) :=
    MorphismProperty.of_isPullback hsq (P := @LocallyOfFiniteType) inferInstance
  have : Flat (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) :=
    MorphismProperty.of_isPullback hsq (P := @Flat) inferInstance
  have hrbc : AlgebraicGeometry.RelativeDimension
      (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) r :=
    AlgebraicGeometry.RelativeDimension.of_isPullback hsq hr
  let e₀ := flatPullbackBivariantClassOfInvertible C
    ((bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) ≫ sZ) sZ
    (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) rfl r hrbc
  intro T t _ k α
  exact bivariantCommute_of_isBivariantProperPushforward C (gysinSystemOfInvertible C) sZ
    (pullback.snd sX sZ) (bivariantPushforwardBaseChange g sX sZ) f (properPushforwardDescends C)
    (-(r : ℤ)) q e₀ c' _
    (isBivariantProperPushforward_bivariantToBaseRestriction_of_isBivariantFlatPullback C
      (gysinSystemOfInvertible C) sX sZ (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) g
      r hr (flatPullbackDescends C) (properPushforwardDescends C) hrbc
      (baseFlatPullbackClass C sX g r hr) (fun _ _ _ _ ↦ rfl) e₀ (fun _ _ _ _ ↦ rfl)
      (isBivariantProperPushforward_properFlatPullbackClass C sX g r hr))
    (bivariantCommute_of_isBivariantFlatPullback C (gysinSystemOfInvertible C) sZ
      (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) f r hrbc
      (flatPullbackDescends C) q c' e₀ (fun _ _ _ _ ↦ rfl)) t k α

/-- The cap operation of `g_* ∘ (W ⟶ S)^*`: flat pullback along `W ×_S T ⟶ T` followed by
pushforward along the base change of `g`. -/
theorem properFlatPullbackClass_cap {T : Scheme.{u}} (t : T ⟶ C.S) [LocallyOfFiniteType t]
    (k : ℤ) (β : chowGroup C (t ≫ 𝟙 C.S) k) :
    (properFlatPullbackClass C sX g r hr).cap t k β =
      properChowPushforward C (pullback.fst (g ≫ sX) t ≫ (g ≫ sX)) (pullback.fst sX t ≫ sX)
        (bivariantPushforwardBaseChange g sX t)
        (bivariantPushforwardBaseChange_comp_structure (rfl : g ≫ sX = g ≫ sX) sX t)
        (k - -(r : ℤ))
        (properPushforwardDescends C _ _ _ _ _)
        (flatPullbackBivariantCap C (g ≫ sX) (𝟙 C.S) (g ≫ sX)
          (comp_comp_structureMorphism_eq (rfl : g ≫ sX = g ≫ sX) (Category.comp_id sX)) r hr
          (flatPullbackDescends C) t k β) := by
  rw [isBivariantProperPushforward_properFlatPullbackClass C sX g r hr t k β,
    bivariantProperPushforwardCap_apply]
  rfl

/-- `g_* ∘ (W ⟶ S)^*` vanishes on a test scheme `T` with `W ×_S T` empty. -/
theorem properFlatPullbackClass_cap_eq_zero {T : Scheme.{u}} (t : T ⟶ C.S)
    [LocallyOfFiniteType t] (hWT : IsEmpty ↥(pullback (g ≫ sX) t)) (k : ℤ)
    (β : chowGroup C (t ≫ 𝟙 C.S) k) : (properFlatPullbackClass C sX g r hr).cap t k β = 0 := by
  rw [properFlatPullbackClass_cap]
  have := subsingleton_chowGroup_of_isEmpty C (pullback.fst (g ≫ sX) t ≫ (g ≫ sX))
    (k - -(r : ℤ))
  rw [Subsingleton.elim (flatPullbackBivariantCap C (g ≫ sX) (𝟙 C.S) (g ≫ sX) _ r hr
    (flatPullbackDescends C) t k β) 0, map_zero]

end ProperFlat

/-! ### The value of `g_* ∘ (W ⟶ S)^*` on `[S₀]₀` -/

section PointValue

variable {C : ChowSituation.{u}} (hC : IsDedekindChowBase C) {X W : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (h : W ⟶ pullback sX (clopenPoints C).ι)
  [IsProper (h ≫ pullback.fst sX (clopenPoints C).ι)]
  [LocallyOfFiniteType ((h ≫ pullback.fst sX (clopenPoints C).ι) ≫ sX)]
  [Flat ((h ≫ pullback.fst sX (clopenPoints C).ι) ≫ sX)] [IsProper h] (r : ℕ)
  (hr : AlgebraicGeometry.RelativeDimension ((h ≫ pullback.fst sX (clopenPoints C).ι) ≫ sX) r)

include hC in
/-- The value of `g_* ∘ (W ⟶ S)^*` on `[S₀]₀`: let `h : W ⟶ X ×_S S₀` be proper with `W` flat of
relative dimension `r` over the base, and `g : W ⟶ X` the composite with the projection. At the
test scheme `S₀` the class `g_* ∘ (W ⟶ S)^*` sends `[S₀]₀` to `h_*[W]`. -/
theorem properFlatPullbackClass_cap_fundamentalChowClass :
    (properFlatPullbackClass C sX (h ≫ pullback.fst sX (clopenPoints C).ι) r hr).cap
        (clopenPoints C).ι 0 (fundamentalChowClass C ((clopenPoints C).ι ≫ 𝟙 C.S) 0) =
      QuotientAddGroup.mk' (rationalEquivalences C (pullback.fst sX (clopenPoints C).ι ≫ sX)
          (0 - -(r : ℤ)))
        (properPushforward C ((h ≫ pullback.fst sX (clopenPoints C).ι) ≫ sX)
          (pullback.fst sX (clopenPoints C).ι ≫ sX) h (Category.assoc _ _ _).symm (0 - -(r : ℤ))
          (fundamentalCycle C ((h ≫ pullback.fst sX (clopenPoints C).ι) ≫ sX) (0 - -(r : ℤ)))) := by
  have := hC.isClosedImmersion_clopenPoints_ι
  have hdimD : schemeDeltaDimension C ((clopenPoints C).ι ≫ 𝟙 C.S) ≤ ((0 : ℤ) : EInt) :=
    schemeDeltaDimension_le_of_forall_relativeDimension_le C (𝟙 C.S) (clopenPoints C).ι
      fun w ↦ by
        rw [relativeDimension_id,
          hC.dimensionFunction_eq_zero_of_mem_clopenPoints (ι_mem_clopenPoints w)]
  rw [properFlatPullbackClass_cap]
  change properChowPushforward C _ _ _ _ _ _ (chowGroupDegreeEquiv C _ _ (flatPullbackChow C _ _
    _ _ r _ 0 _ (fundamentalChowClass C ((clopenPoints C).ι ≫ 𝟙 C.S) 0))) = _
  rw [flatPullbackChow_fundamentalChowClass C _ _ _ _ r _ 0 _ hdimD,
    chowGroupDegreeEquiv_fundamentalChowClass]
  have hw : 𝟙 W ≫ ((h ≫ pullback.fst sX (clopenPoints C).ι) ≫ sX) =
      (h ≫ pullback.snd sX (clopenPoints C).ι) ≫ (clopenPoints C).ι := by
    simp only [Category.id_comp, Category.assoc, pullback.condition]
  let θ : W ⟶ pullback ((h ≫ pullback.fst sX (clopenPoints C).ι) ≫ sX) (clopenPoints C).ι :=
    pullback.lift (𝟙 W) (h ≫ pullback.snd sX (clopenPoints C).ι) hw
  have hθ1 : θ ≫ pullback.fst _ _ = 𝟙 W := pullback.lift_fst _ _ _
  have hθ2 : θ ≫ pullback.snd _ _ = h ≫ pullback.snd sX (clopenPoints C).ι :=
    pullback.lift_snd _ _ _
  have hinv : pullback.fst ((h ≫ pullback.fst sX (clopenPoints C).ι) ≫ sX)
      (clopenPoints C).ι ≫ θ = 𝟙 _ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hθ1, Category.comp_id, Category.id_comp]
    · rw [← cancel_mono (clopenPoints C).ι]
      simp only [Category.assoc, hθ2, Category.id_comp]
      rw [← pullback.condition (f := sX) (g := (clopenPoints C).ι), ← pullback.condition]
      simp only [Category.assoc]
  have : IsIso θ := ⟨⟨pullback.fst _ _, hθ1, hinv⟩⟩
  have hθs : θ ≫ (pullback.fst ((h ≫ pullback.fst sX (clopenPoints C).ι) ≫ sX)
      (clopenPoints C).ι ≫ ((h ≫ pullback.fst sX (clopenPoints C).ι) ≫ sX)) =
      (h ≫ pullback.fst sX (clopenPoints C).ι) ≫ sX := by
    rw [← Category.assoc, hθ1, Category.id_comp]
  have hθb : θ ≫ bivariantPushforwardBaseChange (h ≫ pullback.fst sX (clopenPoints C).ι) sX
      (clopenPoints C).ι = h := by
    apply pullback.hom_ext
    · rw [Category.assoc, bivariantPushforwardBaseChange_fst, ← Category.assoc, hθ1,
        Category.id_comp]
    · rw [Category.assoc, bivariantPushforwardBaseChange_snd, hθ2]
  rw [← chowPushforwardOfIso_fundamentalChowClass C _ _ θ hθs, chowPushforwardOfIso,
    ← properChowPushforward_comp_apply C _ _ (pullback.fst sX (clopenPoints C).ι ≫ sX) θ
      (bivariantPushforwardBaseChange _ sX (clopenPoints C).ι) h hθb hθs _
      (Category.assoc _ _ _).symm _ _ _ (properPushforwardDescends C _ _ _ _ _),
    fundamentalChowClass, properChowPushforward_mk]

end PointValue

end Stacks.Chow

end
