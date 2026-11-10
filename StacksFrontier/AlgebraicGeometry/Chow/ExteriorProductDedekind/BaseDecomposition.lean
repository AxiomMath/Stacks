module

public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.ClopenPoints
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.ChowCohomology
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.RankZero

/-!
# Bivariant classes towards a Dedekind base, over the curves and over the points

Let `(S, δ)` be as in Stacks section 42.63 and let `S₀ ⊆ S` be the open and closed union of the
zero-dimensional irreducible components (`Stacks.Chow.clopenPoints`), so that `S` is the disjoint
union of `S₀` and of the curves `S₁ = S ∖ S₀`. For `c ∈ A^p(X ⟶ S)` this file compares `c` with
the class `c_α` of Stacks 0FC5, `α = c ∩ [S]₁`, without assuming `S₀ = ∅`:

* `α` is represented by a cycle lying over `S₁`, because the restriction of `c ∩ [S]₁` to the
  part of `X ×_S S` over `S₀` is `c ∩ ([S]₁|_{S₀}) = 0`, the base being zero-dimensional there;
* hence `c_α ∩ [S]₁ = α`, so `c - c_α` kills `[S]₁`, and by the argument of Stacks 0FC5 it kills
  the fundamental class of every integral scheme over `S₁`;
* `c_α` kills every class on a test scheme over `S₀`, the exterior product of a cycle over `S₁`
  with one over `S₀` being zero;
* a class killing `[S₀]₀` kills the fundamental class of every integral scheme over `S₀`, such a
  scheme being flat over `S₀` with `[T] = (T ⟶ S₀)^*[S₀]₀`.

## Main results

* `Stacks.Chow.exists_mk_eq_bivariantChowClassCapBaseFundamentalClass` — `c ∩ [S]₁` is the class
  of a cycle lying over `S₁`.
* `Stacks.Chow.bivariantChowClassCapBaseFundamentalClass_dedekindExteriorClass_self` —
  `c_α ∩ [S]₁ = α` for `α = c ∩ [S]₁`.
* `Stacks.Chow.BivariantChowClass.cap_integral_eq_zero_of_not_mem_clopenPoints` — `c - c_α` kills
  the integral schemes over `S₁`.
* `Stacks.Chow.dedekindExteriorClass_cap_eq_zero_of_mem_clopenPoints` — `c_α` kills every class
  on a test scheme over `S₀`.
* `Stacks.Chow.BivariantChowClass.cap_integral_eq_zero_of_mem_clopenPoints` — a class killing
  `[S₀]₀` kills the integral schemes over `S₀`.

## References

* [Stacks Project, Tag 0FC5](https://stacks.math.columbia.edu/tag/0FC5)
* [Stacks Project, Tag 0FC6](https://stacks.math.columbia.edu/tag/0FC6)
* [Stacks Project, Section 42.63 (Tag 0FC3)](https://stacks.math.columbia.edu/tag/0FC3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Chow groups with no points of the right dimension -/

/-- A Chow group in a degree which no point attains is zero. -/
theorem subsingleton_chowGroup_of_forall_relativeDimension_ne (C : ChowSituation.{u})
    {P : Scheme.{u}} (q : P ⟶ C.S) [LocallyOfFiniteType q] (k : ℤ)
    (h : ∀ x : P, relativeDimension C.dimensionFunction q x ≠ k) :
    Subsingleton (chowGroup C q k) := by
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective _ a
  obtain ⟨d, rfl⟩ := QuotientAddGroup.mk'_surjective _ b
  have hz : ∀ e : CycleGroup C q k, e = 0 := fun e ↦ by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
    by_contra hx
    exact h x ((mem_cyclesOfDimension_iff_forall_point C q k e.1).1 e.2 x hx)
  rw [hz c, hz d]

/-- Pushing a cycle restricted along an open immersion which is proper forward again returns the
cycle at the points of the image. -/
theorem properPushforward_cycleGroupRestrict_apply (C : ChowSituation.{u}) {Z A : Scheme.{u}}
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
    (m : A ⟶ Z) [IsOpenImmersion m] [IsProper m] (hm : m ≫ sZ = sA) (k : ℤ)
    (b : CycleGroup C sZ k) (z : A) :
    (properPushforward C sA sZ m hm k (cycleGroupRestrict C sZ sA m hm k b)).1 (m.base z) =
      b.1 (m.base z) := by
  have h := congrArg (fun e : CycleGroup C sA k ↦ e.1 z)
    (cycleGroupRestrict_properPushforward_self C sZ sA m hm k (cycleGroupRestrict C sZ sA m hm k b))
  simpa only [cycleGroupRestrict_apply] using h

/-- The two projections of a fibre product have the same image in the base. -/
private theorem base_fst_eq_base_snd_of_pullback {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (z : ↥(pullback f g)) :
    f.base ((pullback.fst f g).base z) = g.base ((pullback.snd f g).base z) := by
  simpa using congrArg (fun φ : pullback f g ⟶ S ↦ φ.base z) (pullback.condition (f := f) (g := g))

/-! ### The part of `c ∩ [S]₁` over the points -/

section CurvePart

variable {C : ChowSituation.{u}} (hC : IsDedekindChowBase C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (p : ℤ)

include hC in
/-- The inclusion of `S₀` is a closed immersion. -/
theorem IsDedekindChowBase.isClosedImmersion_clopenPoints_ι :
    IsClosedImmersion (clopenPoints C).ι :=
  IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]; exact hC.isClosed_clopenPoints)

/-- A point of the open subscheme `S₀` lies in `S₀`. -/
theorem ι_mem_clopenPoints (s : (clopenPoints C : Scheme.{u})) :
    (clopenPoints C).ι.base s ∈ clopenPoints C := by
  have h := Set.mem_range_self (f := (clopenPoints C).ι.base) s
  rwa [Scheme.Opens.range_ι] at h

/-- The points of `S₀` have relative dimension `δ` over `S`. -/
theorem relativeDimension_clopenPoints_ι (s : (clopenPoints C : Scheme.{u})) :
    relativeDimension C.dimensionFunction ((clopenPoints C).ι ≫ 𝟙 C.S) s =
      C.dimensionFunction ((clopenPoints C).ι.base s) := by
  rw [relativeDimension_comp_isOpenImmersion, relativeDimension_id]

include hC in
/-- **`c ∩ [S]₁` lies over the curves.** For `c ∈ A^p(X ⟶ S)` over a Dedekind base, the class
`c ∩ [S]₁ ∈ CH_{1-p}(X)` is the class of a cycle whose support lies over `S ∖ S₀`. -/
theorem exists_mk_eq_bivariantChowClassCapBaseFundamentalClass
    (c : BivariantChowClass C sX (𝟙 C.S) sX (Category.comp_id sX) p) :
    ∃ a : CycleGroup C sX (1 - p),
      QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p)) a =
        bivariantChowClassCapBaseFundamentalClass sX p c ∧
      ∀ x : X, a.1 x ≠ 0 → sX.base x ∉ clopenPoints C := by
  classical
  have := hC.isClosedImmersion_clopenPoints_ι
  set j := bivariantBaseChangeMap sX (𝟙 C.S) (clopenPoints C).ι with hj
  have hsq := isPullback_bivariantBaseChangeMap sX (𝟙 C.S) (clopenPoints C).ι
  have : IsOpenImmersion j :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hsq inferInstance
  have hjs := bivariantBaseChangeMap_comp_structureMorphism sX sX (𝟙 C.S)
    (clopenPoints C).ι
  have hres : chowGroupRestrict C (pullback.fst sX (𝟙 C.S) ≫ sX)
      (pullback.fst sX ((clopenPoints C).ι ≫ 𝟙 C.S) ≫ sX) j hjs (1 - p)
      (c.cap (𝟙 C.S) 1 (baseFundamentalChowClass C)) = 0 := by
    rw [c.cap_chowGroupRestrict]
    have := subsingleton_chowGroup_of_forall_relativeDimension_ne C
      (((clopenPoints C).ι ≫ 𝟙 C.S) ≫ 𝟙 C.S) 1 fun s ↦ by
        rw [Category.comp_id, relativeDimension_clopenPoints_ι,
          hC.dimensionFunction_eq_zero_of_mem_clopenPoints (ι_mem_clopenPoints s)]
        exact zero_ne_one
    rw [Subsingleton.elim (chowGroupRestrict C _ _ _ _ 1 _) 0, BivariantChowClass.cap_zero']
  obtain ⟨b, hb⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences C _ (1 - p))
    (c.cap (𝟙 C.S) 1 (baseFundamentalChowClass C))
  set b' := b - properPushforward C _ _ j hjs (1 - p)
    (cycleGroupRestrict C _ _ j hjs (1 - p) b) with hb'
  have hmk : QuotientAddGroup.mk' (rationalEquivalences C _ (1 - p)) b' =
      c.cap (𝟙 C.S) 1 (baseFundamentalChowClass C) := by
    rw [hb', map_sub, ← properChowPushforward_mk C _ _ j hjs (1 - p)
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ j hjs (1 - p)),
      ← chowGroupRestrict_mk, hb, hres, map_zero, sub_zero]
  have hb'0 : ∀ y, y ∈ Set.range j.base → b'.1 y = 0 := by
    rintro _ ⟨z, rfl⟩
    change b.1 (j.base z) - (properPushforward C _ _ j hjs (1 - p)
      (cycleGroupRestrict C _ _ j hjs (1 - p) b)).1 (j.base z) = 0
    rw [properPushforward_cycleGroupRestrict_apply, sub_self]
  refine ⟨properPushforward C _ sX (basePullbackProjection C sX) rfl (1 - p) b', ?_, ?_⟩
  · rw [bivariantChowClassCapBaseFundamentalClass_apply, ← hmk, basePullbackPushforward,
      properChowPushforward_mk]
  · intro x hx hxS
    obtain ⟨y, rfl⟩ := support_properPushforward_subset C _ _ _ rfl (1 - p) b' hx
    have hy : y ∈ Set.range j.base := by
      rw [range_base_of_isPullback _ j (clopenPoints C).ι _ hsq.flip, Set.mem_preimage,
        Scheme.Opens.range_ι]
      exact (base_fst_eq_base_snd_of_pullback sX (𝟙 C.S) y) ▸ hxS
    refine hx ?_
    have hinj : Function.Injective (basePullbackProjection C sX).base :=
      (basePullbackProjection C sX).isOpenEmbedding.injective
    have hpre : (basePullbackProjection C sX).base ⁻¹' {(basePullbackProjection C sX).base y} =
        {y} := by
      ext w
      simp [hinj.eq_iff]
    rw [properPushforward_apply, hpre, finsum_mem_singleton, hb'0 y hy, zero_mul]

include hC in
/-- **`c_α ∩ [S]₁ = α` for a cycle over the curves.** If `α` is the class of a cycle whose
support lies over `S ∖ S₀`, then the class `c_α` of the proof of Stacks 0FC5 caps `[S]₁` to
`α`. -/
theorem bivariantChowClassCapBaseFundamentalClass_dedekindExteriorClass_of_mk
    (a₀ : CycleGroup C sX (1 - p)) (ha : ∀ x : X, a₀.1 x ≠ 0 → sX.base x ∉ clopenPoints C) :
    bivariantChowClassCapBaseFundamentalClass sX p
        (dedekindExteriorClass hC sX p
          (QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p)) a₀)) =
      QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p)) a₀ := by
  rw [bivariantChowClassCapBaseFundamentalClass_apply, dedekindExteriorClass_cap,
    dedekindExteriorCap_apply]
  have hS : chowGroupCongr C (Category.comp_id (𝟙 C.S)) 1 (baseFundamentalChowClass C) =
      QuotientAddGroup.mk' (rationalEquivalences C (𝟙 C.S) 1) (fundamentalCycle C (𝟙 C.S) 1) :=
    eq_of_heq ((chowGroupCongr_heq C _ _ _).trans
      (fundamentalChowClass_heq_of_structureMorphism_eq (Category.comp_id (𝟙 C.S)) 1))
  rw [hS, exteriorProductDedekindChowTensor_tmul_mk, basePullbackPushforward,
    ← chowGroupDegreeEquiv_properChowPushforward_comp C _ _ _ _ (by ring : 1 - p + 1 - 1 = 1 - p)
      (properPushforwardDescends C _ _ _ _ _), properChowPushforward_mk,
    mk_properPushforward_exteriorProductDedekindCycles_fundamentalCycle_of_dimensionFunction hC sX
      (1 - p) a₀ fun x hx hdom ↦
        hC.dimensionFunction_eq_one_of_not_mem_clopenPoints hdom (ha x hx)]
  exact chowGroupDegreeEquiv_mk_eq_mk_of_val C sX _ _ _ rfl

include hC in
/-- **`c_α ∩ [S]₁ = α` for `α = c ∩ [S]₁`**, over any Dedekind base. -/
theorem bivariantChowClassCapBaseFundamentalClass_dedekindExteriorClass_self
    (c : BivariantChowClass C sX (𝟙 C.S) sX (Category.comp_id sX) p) :
    bivariantChowClassCapBaseFundamentalClass sX p
        (dedekindExteriorClass hC sX p (bivariantChowClassCapBaseFundamentalClass sX p c)) =
      bivariantChowClassCapBaseFundamentalClass sX p c := by
  obtain ⟨a, ha, hsupp⟩ := exists_mk_eq_bivariantChowClassCapBaseFundamentalClass hC sX p c
  rw [← ha]
  exact bivariantChowClassCapBaseFundamentalClass_dedekindExteriorClass_of_mk hC sX p a hsupp

include hC in
/-- `c - c_α` kills `[S]₁`, for `α = c ∩ [S]₁`. -/
theorem cap_baseFundamentalChowClass_sub_dedekindExteriorClass
    (c : BivariantChowClass C sX (𝟙 C.S) sX (Category.comp_id sX) p) :
    (c - dedekindExteriorClass hC sX p (bivariantChowClassCapBaseFundamentalClass sX p c)).cap
      (𝟙 C.S) 1 (baseFundamentalChowClass C) = 0 := by
  have h : bivariantChowClassCapBaseFundamentalClass sX p
      (c - dedekindExteriorClass hC sX p (bivariantChowClassCapBaseFundamentalClass sX p c)) =
        0 := by
    rw [map_sub, bivariantChowClassCapBaseFundamentalClass_dedekindExteriorClass_self, sub_self]
  rw [bivariantChowClassCapBaseFundamentalClass_apply, basePullbackPushforward] at h
  exact eq_zero_of_properChowPushforward_eq_zero_of_isIso _ _ _ _ _ _ _ h

include hC in
/-- **A class killing `[S]₁` kills the integral schemes over the curves.** A class
`c ∈ A^p(X ⟶ S)` with `c ∩ [S]₁ = 0` kills the fundamental class of every integral scheme `T`
over the base whose generic point maps outside `S₀`. -/
theorem BivariantChowClass.cap_integral_eq_zero_of_not_mem_clopenPoints
    (c : BivariantChowClass C sX (𝟙 C.S) sX (Category.comp_id sX) p)
    (hc : c.cap (𝟙 C.S) 1 (baseFundamentalChowClass C) = 0) {T : Scheme.{u}} (g : T ⟶ C.S)
    [LocallyOfFiniteType g] [IsIntegral T] (hT : g.base (genericPoint T) ∉ clopenPoints C)
    (k : ℤ) : c.cap g k (fundamentalChowClass C (g ≫ 𝟙 C.S) k) = 0 :=
  c.cap_integral_eq_zero_of_cap_baseFundamentalChowClass_of_dimensionFunction hC hc g
    (fun hdom ↦ hC.dimensionFunction_eq_one_of_not_mem_clopenPoints hdom hT) k

end CurvePart

/-! ### `c_α` over the points -/

section PointPart

variable {C : ChowSituation.{u}} (hC : IsDedekindChowBase C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (p : ℤ)

/-- The exterior product of a cycle lying over `S ∖ S₀` with a cycle on a scheme over `S₀`
vanishes. -/
theorem exteriorProductDedekindCycles_eq_zero_of_mem_clopenPoints {T : Scheme.{u}}
    (g : T ⟶ C.S) [LocallyOfFiniteType g] (hg : ∀ t : T, g.base t ∈ clopenPoints C) (n m : ℤ)
    (a : CycleGroup C sX n) (ha : ∀ x : X, a.1 x ≠ 0 → sX.base x ∉ clopenPoints C)
    (b : CycleGroup C g m) : exteriorProductDedekindCycles C sX g n m a b = 0 := by
  classical
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ ?_)
  rw [exteriorProductDedekindCycles_apply]
  refine finsum_eq_zero_of_forall_eq_zero fun q ↦ ?_
  by_contra hne
  have hcl := (mem_closure_of_exteriorProductDedekindTerm_ne_zero C sX g n m a b z q hne).1
  have hsp : q.1 ⤳ (pullback.fst sX g).base z := specializes_iff_mem_closure.mpr hcl
  have hx : sX.base q.1 ∈ clopenPoints C :=
    mem_clopenPoints_of_specializes (hsp.map sX.continuous)
      (base_fst_eq_base_snd_of_pullback sX g z ▸ hg _)
  have h0 : a.1 q.1 = 0 := not_ne_iff.mp fun h ↦ ha q.1 h hx
  apply hne
  unfold exteriorProductDedekindTerm
  split_ifs <;> simp [h0]

/-- **`c_α` vanishes over `S₀`** when `α` is the class of a cycle lying over `S ∖ S₀`. -/
theorem dedekindExteriorClass_cap_eq_zero_of_mem_clopenPoints (a : CycleGroup C sX (1 - p))
    (ha : ∀ x : X, a.1 x ≠ 0 → sX.base x ∉ clopenPoints C) {T : Scheme.{u}} (g : T ⟶ C.S)
    [LocallyOfFiniteType g] (hg : ∀ t : T, g.base t ∈ clopenPoints C) (k : ℤ)
    (β : chowGroup C (g ≫ 𝟙 C.S) k) :
    (dedekindExteriorClass hC sX p (QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p)) a)).cap
      g k β = 0 := by
  rw [dedekindExteriorClass_cap, dedekindExteriorCap_apply]
  obtain ⟨b, hb⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences C g k)
    (chowGroupCongr C (Category.comp_id g) k β)
  rw [← hb, exteriorProductDedekindChowTensor_tmul_mk,
    exteriorProductDedekindCycles_eq_zero_of_mem_clopenPoints sX g hg (1 - p) k a ha b, map_zero,
    map_zero]

include hC in
/-- **A class killing `[S₀]₀` kills the integral schemes over `S₀`.** Let `c ∈ A^p(X ⟶ S)` kill
the fundamental class `[S₀]₀` of the open subscheme `S₀`. If `T` is integral and locally of
finite type over the base with its generic point over `S₀`, then `c ∩ [T] = 0`. -/
theorem BivariantChowClass.cap_integral_eq_zero_of_mem_clopenPoints
    (c : BivariantChowClass C sX (𝟙 C.S) sX (Category.comp_id sX) p)
    (hc : c.cap (clopenPoints C).ι 0
      (fundamentalChowClass C ((clopenPoints C).ι ≫ 𝟙 C.S) 0) = 0)
    {T : Scheme.{u}} (g : T ⟶ C.S) [LocallyOfFiniteType g] [IsIntegral T]
    (hT : g.base (genericPoint T) ∈ clopenPoints C) (k : ℤ) :
    c.cap g k (fundamentalChowClass C (g ≫ 𝟙 C.S) k) = 0 := by
  classical
  have hrange : Set.range g.base ⊆ Set.range (clopenPoints C).ι.base := by
    rintro _ ⟨t, rfl⟩
    have h1 : g.base (genericPoint T) ⤳ g.base t := (genericPoint_specializes t).map g.continuous
    rw [eq_of_specializes_of_mem_clopenPoints hT h1, Scheme.Opens.range_ι]
    exact hT
  set a := IsOpenImmersion.lift (clopenPoints C).ι g hrange with had
  have ha : a ≫ (clopenPoints C).ι = g := IsOpenImmersion.lift_fac _ _ _
  have hfield : ∀ x : (clopenPoints C : Scheme.{u}),
      IsField ((clopenPoints C : Scheme.{u}).presheaf.stalk x) := fun x ↦
    MulEquiv.isField (hC.isField_stalk_of_mem_clopenPoints x.2)
      ((clopenPoints C).stalkIso x).commRingCatIsoToRingEquiv.toMulEquiv
  have : Flat a := flat_of_isField_stalk a hfield
  have : LocallyOfFiniteType a := by
    have : LocallyOfFiniteType (a ≫ (clopenPoints C).ι) := by rw [ha]; infer_instance
    exact locallyOfFiniteType_of_comp a (clopenPoints C).ι
  have harel := relativeDimension_of_irreducibleSpace a fun t ↦ by
    let _ := (hfield (a.base t)).toField
    refine ⟨inferInstance, ?_⟩
    rw [ringKrullDim_eq_zero_of_field]
    exact zero_le_one
  set r := Cardinal.toNat (residueTrdeg a (genericPoint T)) with hr
  have hδT : relativeDimension C.dimensionFunction (g ≫ 𝟙 C.S) (genericPoint T) = 0 + r := by
    rw [← ha, Category.assoc, relativeDimension_comp_eq_add_trdeg, relativeDimension_clopenPoints_ι,
      hC.dimensionFunction_eq_zero_of_mem_clopenPoints (ι_mem_clopenPoints _)]
  by_cases hk : k = 0 + r
  swap
  · rw [fundamentalChowClass, fundamentalCycle_eq_zero_of_ne C (g ≫ 𝟙 C.S)
      genericPoints_eq_singleton (by rw [hδT]; exact fun h ↦ hk h.symm), map_zero]
    exact c.cap_zero' g k
  subst hk
  have := hC.isClosedImmersion_clopenPoints_ι
  have hdimD : schemeDeltaDimension C ((clopenPoints C).ι ≫ 𝟙 C.S) ≤ ((0 : ℤ) : EInt) :=
    schemeDeltaDimension_le_of_forall_relativeDimension_le C (𝟙 C.S) (clopenPoints C).ι
      fun w ↦ by
        rw [relativeDimension_id,
          hC.dimensionFunction_eq_zero_of_mem_clopenPoints (ι_mem_clopenPoints w)]
  have hax := c.cap_flatPullback (clopenPoints C).ι a r harel 0
    (fundamentalChowClass C ((clopenPoints C).ι ≫ 𝟙 C.S) 0)
  rw [hc, map_zero, flatPullbackChow_fundamentalChowClass C _ _ a _ r harel 0 _ hdimD] at hax
  exact c.cap_fundamentalChowClass_eq_zero_of_heq ha.symm rfl (by ring) hax

end PointPart

end Stacks.Chow

end
