module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CommuteOverDedekindBaseUnconditional
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackProperPushforward

/-!
# Bivariant classes towards a Dedekind base commute with every bivariant class

Let `(S, δ)` be a base as in section 42.63 of the Stacks Project (Tag 0FC3): a scheme covered by
spectra of Dedekind domains, with `δ = 0` at closed points and `δ = 1` elsewhere. Let `X` be a
scheme locally of finite type over `S`, let `c ∈ A^p(X → S)`, and let `c' ∈ A^q(Y → Z)` for a
morphism `Y ⟶ Z` of schemes locally of finite type over `S`. **Stacks 0FC6** asserts that
`c ∘ c' = c' ∘ c`.

A field is a Dedekind domain, so such a base may have zero-dimensional components: points `s`
with `{s}` open and closed, the spectra of the fields of the covering, at which `δ = 0`. They
form the *zero-dimensional locus* `S₀`, which is open and closed. Away from `S₀` the identification
`A^p(X → S) = CH_{1-p}(X)`, `c ↦ c ∩ [S]₁`, of Stacks 0FC5 holds, but on `S₀` the class `[S]₁`
vanishes and carries no information. This file proves Stacks 0FC6 for every base as in section
42.63 by adding to `c ∩ [S]₁` the class `c ∩ [S₀]₀ ∈ CH_{-p}(X ×_S S₀)`, which over `S₀` plays
the role of the cap product with the class of the point in Stacks 0FBW.

## Main definitions

* `Stacks.Chow.zeroDimensionalLocus` — the open set of points `s` with `{s}` open and closed.
* `Stacks.Chow.IsDedekindChowBase.positiveDimensionalLocus` — its complement over a base as in
  section 42.63, which is open.
* `Stacks.Chow.bivariantCapZeroDimensionalLocus` — the map `c ↦ c ∩ [S₀]₀`,
  `A^p(X → S) → CH_{-p}(X ×_S S₀)`.

## Main results

* `Stacks.Chow.IsDedekindChowBase.isClosed_zeroDimensionalLocus` — the zero-dimensional locus is
  closed.
* `Stacks.Chow.subsingleton_chowGroup_of_schemeDeltaDimension_le` — Chow groups vanish above the
  delta-dimension.
* `Stacks.Chow.eq_of_bivariantCapBaseFundamentalClass_eq_of_bivariantCapZeroDimensionalLocus_eq` —
  a class is determined by its caps with `[S]₁` and `[S₀]₀`.
* `Stacks.Chow.exists_mem_centralOverBaseSubgroup_restrict_eq`,
  `Stacks.Chow.exists_mem_centralOverBaseSubgroup_bivariantCapZeroDimensionalLocus_eq` — the
  central classes reach every class away from `S₀`, and every class on `X ×_S S₀`.
* `Stacks.Chow.isCentralOverBase_of_isDedekindChowBase_general`,
  `Stacks.Chow.bivariantCommuteOverBase_of_isDedekindChowBase_general` — **Stacks 0FC6** over
  every base as in section 42.63.

## References

* [Stacks Project, Tag 0FC6](https://stacks.math.columbia.edu/tag/0FC6)
* [Stacks Project, Tag 0FC5](https://stacks.math.columbia.edu/tag/0FC5)
* [Stacks Project, Section 42.63 (Tag 0FC3)](https://stacks.math.columbia.edu/tag/0FC3)
* [Stacks Project, Tag 0FBW](https://stacks.math.columbia.edu/tag/0FBW)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The zero-dimensional part of the base -/

/-- The **zero-dimensional locus** of the base: the points `s` with `{s}` open and closed. Over a
base as in section 42.63 these are the points of the zero-dimensional components, the spectra of
the fields among the Dedekind domains of the covering. -/
def zeroDimensionalLocus (C : ChowSituation.{u}) : C.S.Opens where
  carrier := {s | IsOpen ({s} : Set C.S) ∧ IsClosed ({s} : Set C.S)}
  is_open' := isOpen_iff_forall_mem_open.mpr fun s hs ↦
    ⟨{s}, fun t ht ↦ by rw [Set.mem_singleton_iff.mp ht]; exact hs, hs.1, rfl⟩

/-- A point lies in the zero-dimensional locus when its singleton is open and closed. -/
theorem mem_zeroDimensionalLocus_iff {C : ChowSituation.{u}} {s : C.S} :
    s ∈ zeroDimensionalLocus C ↔ IsOpen ({s} : Set C.S) ∧ IsClosed ({s} : Set C.S) :=
  Iff.rfl

namespace IsDedekindChowBase

variable {C : ChowSituation.{u}}

/-- Every point of a base as in section 42.63 has an integral open neighbourhood. -/
theorem exists_isIntegral_opens (hS : IsDedekindChowBase C) (s : C.S) :
    ∃ U : C.S.Opens, s ∈ U ∧ IsIntegral (U : Scheme.{u}) := by
  obtain ⟨U, hsU, hU, hded⟩ := hS.1 s
  have _ : Nonempty U := ⟨⟨s, hsU⟩⟩
  exact ⟨U, hsU, isIntegral_of_isOpenImmersion hU.isoSpec.hom⟩

/-- The generic point of an integral open of the base specializes to every point of it. -/
theorem genericPoint_specializes_of_isIntegral (U : C.S.Opens) [IsIntegral (U : Scheme.{u})]
    {x : C.S} (hx : x ∈ U) : U.ι.base (genericPoint (U : Scheme.{u})) ⤳ x := by
  show _ ⤳ U.ι.base ⟨x, hx⟩
  exact ((genericPoint_spec (U : Scheme.{u})).specializes (Set.mem_univ _)).map U.ι.continuous

/-- A closed point of a base as in section 42.63 with no proper generalization is the whole of an
integral open neighbourhood. -/
theorem exists_isIntegral_opens_eq_singleton (hS : IsDedekindChowBase C) {s : C.S}
    (hc : IsClosed ({s} : Set C.S)) (hg : s ∈ genericPoints C.S) :
    ∃ U : C.S.Opens, (U : Set C.S) = {s} ∧ IsIntegral (U : Scheme.{u}) := by
  obtain ⟨U, hsU, _⟩ := hS.exists_isIntegral_opens s
  have hη : U.ι.base (genericPoint (U : Scheme.{u})) = s :=
    (mem_genericPoints_iff_forall_specializes_eq s).1 hg _
      (genericPoint_specializes_of_isIntegral U hsU)
  refine ⟨U, Set.Subset.antisymm (fun x hx ↦ ?_) (Set.singleton_subset_iff.mpr hsU), ‹_›⟩
  have h := specializes_iff_mem_closure.mp (genericPoint_specializes_of_isIntegral U hx)
  rwa [hη, hc.closure_eq] at h

/-- Over a base as in section 42.63 a point lies in the zero-dimensional locus exactly when it
is closed and has no proper generalization. -/
theorem mem_zeroDimensionalLocus_iff (hS : IsDedekindChowBase C) {s : C.S} :
    s ∈ zeroDimensionalLocus C ↔ IsClosed ({s} : Set C.S) ∧ s ∈ genericPoints C.S := by
  refine ⟨fun h ↦ ⟨h.2, (mem_genericPoints_iff_forall_specializes_eq s).2 fun t hts ↦ ?_⟩,
    fun h ↦ ?_⟩
  · exact (hts.mem_open h.1 rfl : t ∈ ({s} : Set C.S))
  · obtain ⟨U, hU, _⟩ := hS.exists_isIntegral_opens_eq_singleton h.1 h.2
    exact ⟨hU ▸ U.isOpen, h.1⟩

/-- The zero-dimensional locus of a base as in section 42.63 is closed. -/
theorem isClosed_zeroDimensionalLocus (hS : IsDedekindChowBase C) :
    IsClosed (zeroDimensionalLocus C : Set C.S) := by
  refine isOpen_compl_iff.mp (isOpen_iff_forall_mem_open.mpr fun s hs ↦ ?_)
  obtain ⟨U, hsU, _⟩ := hS.exists_isIntegral_opens s
  refine ⟨U, fun x hx hx0 ↦ hs ?_, U.isOpen, hsU⟩
  have h1 : U.ι.base (genericPoint (U : Scheme.{u})) = x :=
    ((genericPoint_specializes_of_isIntegral U hx).mem_open hx0.1 rfl : _)
  have h2 := specializes_iff_mem_closure.mp (genericPoint_specializes_of_isIntegral U hsU)
  rw [h1, hx0.2.closure_eq, Set.mem_singleton_iff] at h2
  rwa [h2]

/-- On the zero-dimensional locus the dimension function vanishes. -/
theorem dimensionFunction_eq_zero_of_mem_zeroDimensionalLocus (hS : IsDedekindChowBase C)
    {s : C.S} (hs : s ∈ zeroDimensionalLocus C) : C.dimensionFunction s = 0 :=
  hS.2.1 s hs.2

/-- A generic point of an irreducible component of a base as in section 42.63 outside the
zero-dimensional locus is not closed, so the dimension function is one there. -/
theorem dimensionFunction_eq_one_of_notMem_zeroDimensionalLocus (hS : IsDedekindChowBase C)
    {s : C.S} (hg : s ∈ genericPoints C.S) (hs : s ∉ zeroDimensionalLocus C) :
    C.dimensionFunction s = 1 :=
  hS.2.2 s fun hc ↦ hs ((hS.mem_zeroDimensionalLocus_iff).2 ⟨hc, hg⟩)

/-- The open complement of the zero-dimensional locus of a base as in section 42.63: the union of
its one-dimensional components. -/
def positiveDimensionalLocus (hS : IsDedekindChowBase C) : C.S.Opens :=
  ⟨(zeroDimensionalLocus C : Set C.S)ᶜ, hS.isClosed_zeroDimensionalLocus.isOpen_compl⟩

/-- A point lies in the positive-dimensional locus when it is not in the zero-dimensional locus. -/
theorem mem_positiveDimensionalLocus_iff (hS : IsDedekindChowBase C) {s : C.S} :
    s ∈ hS.positiveDimensionalLocus ↔ s ∉ zeroDimensionalLocus C :=
  Iff.rfl

/-- The inclusion of the zero-dimensional locus of a base as in section 42.63 is a closed
immersion, the locus being closed. -/
theorem isClosedImmersion_zeroDimensionalLocus_ι (hS : IsDedekindChowBase C) :
    IsClosedImmersion (zeroDimensionalLocus C).ι := by
  refine .of_isPreimmersion _ ?_
  rw [Scheme.Opens.range_ι]
  exact hS.isClosed_zeroDimensionalLocus

/-- A scheme mapping by an open immersion into the zero-dimensional locus of a base as in
section 42.63 has delta-dimension at most zero. -/
theorem schemeDeltaDimension_le_zero (hS : IsDedekindChowBase C) {T : Scheme.{u}}
    (j : T ⟶ C.S) [IsOpenImmersion j] [LocallyOfFiniteType j]
    (hj : ∀ t, j.base t ∈ zeroDimensionalLocus C) :
    schemeDeltaDimension C j ≤ ((0 : ℤ) : EInt) := by
  have h := schemeDeltaDimension_le_of_forall_relativeDimension_le C j (𝟙 T) (k := 0)
    fun w ↦ by
      rw [← Category.comp_id j, relativeDimension_comp_isOpenImmersion, relativeDimension_id]
      exact (hS.dimensionFunction_eq_zero_of_mem_zeroDimensionalLocus (hj _)).le
  simpa using h

end IsDedekindChowBase

/-- A point of the zero-dimensional locus specializes only to itself. -/
theorem eq_of_specializes_of_mem_zeroDimensionalLocus {C : ChowSituation.{u}} {s t : C.S}
    (hs : s ∈ zeroDimensionalLocus C) (h : s ⤳ t) : t = s := by
  have h2 := specializes_iff_mem_closure.mp h
  rwa [hs.2.closure_eq, Set.mem_singleton_iff] at h2

/-! ### Chow groups above the delta-dimension -/

/-- **The Chow groups of a scheme vanish above its delta-dimension**: a cycle of
delta-dimension `k` has nonzero coefficients only at points of delta-dimension `k`, and there are
none when `dim_δ T ≤ n < k`. -/
theorem subsingleton_chowGroup_of_schemeDeltaDimension_le (C : ChowSituation.{u})
    {T : Scheme.{u}} (sT : T ⟶ C.S) [LocallyOfFiniteType sT] {n k : ℤ}
    (hdim : schemeDeltaDimension C sT ≤ (n : EInt)) (hk : n < k) :
    Subsingleton (chowGroup C sT k) := by
  have h0 : ∀ a : CycleGroup C sT k, a = 0 := by
    intro a
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
    by_contra hx
    have h1 := (mem_cyclesOfDimension_iff_forall_point C sT k a.1).1 a.2 x hx
    have h2 := relativeDimension_le_of_schemeDeltaDimension_le C sT (𝟙 T)
      ((schemeDeltaDimension_congr C (Category.id_comp sT)).le.trans hdim) x
    change relativeDimension C.dimensionFunction sT x ≤ n at h2
    omega
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective _ a
  obtain ⟨d, rfl⟩ := QuotientAddGroup.mk'_surjective _ b
  rw [h0 c, h0 d]

/-- The first projection of the pullback of `f` along a monomorphism `i` is an isomorphism as soon
as `f` factors through `i`. -/
theorem isIso_pullbackFst_of_comp_eq {A B Z : Scheme.{u}} (f : A ⟶ Z) (i : B ⟶ Z) [Mono i]
    (f' : A ⟶ B) (h : f' ≫ i = f) : IsIso (pullback.fst f i) := by
  subst h
  infer_instance

/-- Points lying over the zero-dimensional locus have non-negative relative dimension. -/
private theorem relativeDimension_nonneg_of_mem_zeroDimensionalLocus {C : ChowSituation.{u}}
    (hS : IsDedekindChowBase C) {A : Scheme.{u}} (q : A ⟶ C.S) [LocallyOfFiniteType q] (x : A)
    (hx : q.base x ∈ zeroDimensionalLocus C) : 0 ≤ relativeDimension C.dimensionFunction q x := by
  change 0 ≤ C.dimensionFunction _ + (Cardinal.toNat (residueTrdeg q x) : ℤ)
  rw [hS.dimensionFunction_eq_zero_of_mem_zeroDimensionalLocus hx]
  positivity

/-- An open of the base inside the zero-dimensional locus has delta-dimension at most zero. -/
private theorem schemeDeltaDimension_opens_ι_le_zero {C : ChowSituation.{u}}
    (hS : IsDedekindChowBase C) {U : C.S.Opens} (hU : U ≤ zeroDimensionalLocus C) :
    schemeDeltaDimension C (U.ι ≫ 𝟙 C.S) ≤ ((0 : ℤ) : EInt) :=
  hS.schemeDeltaDimension_le_zero _ fun t ↦ by
    rw [Category.comp_id]
    exact hU t.2

/-- Every point of `X ×_S S₀` lies over the zero-dimensional locus. -/
private theorem fst_comp_base_mem_zeroDimensionalLocus {C : ChowSituation.{u}} {X : Scheme.{u}}
    (sX : X ⟶ C.S) (x : (pullback sX (zeroDimensionalLocus C).ι : Scheme.{u})) :
    (pullback.fst sX (zeroDimensionalLocus C).ι ≫ sX).base x ∈ zeroDimensionalLocus C := by
  rw [pullback.condition, Scheme.Hom.comp_apply]
  exact ((pullback.snd sX (zeroDimensionalLocus C).ι).base x).2

/-! ### Injectivity -/

section Injective

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (p : ℤ)

/-- Capping a class `c ∈ A^p(X → S)` with the fundamental class `[S₀]₀` of the zero-dimensional
locus `S₀` of the base, read on `X ×_S S₀`. -/
def bivariantCapZeroDimensionalLocus :
    BivariantClass C G sX (𝟙 C.S) sX (Category.comp_id sX) p →+
      chowGroup C (pullback.fst sX (zeroDimensionalLocus C).ι ≫ sX) (0 - p) :=
  AddMonoidHom.mk'
    (fun c ↦ c.cap (zeroDimensionalLocus C).ι 0
      (fundamentalChowClass C ((zeroDimensionalLocus C).ι ≫ 𝟙 C.S) 0))
    (fun c d ↦ BivariantClass.add_cap C G sX (𝟙 C.S) sX (Category.comp_id sX) p c d _ 0 _)

/-- The defining formula of `Stacks.Chow.bivariantCapZeroDimensionalLocus`. -/
theorem bivariantCapZeroDimensionalLocus_apply
    (c : BivariantClass C G sX (𝟙 C.S) sX (Category.comp_id sX) p) :
    bivariantCapZeroDimensionalLocus C G sX p c =
      c.cap (zeroDimensionalLocus C).ι 0
        (fundamentalChowClass C ((zeroDimensionalLocus C).ι ≫ 𝟙 C.S) 0) :=
  rfl

variable {C}

/-- A class `c ∈ A^p(X → S)` capping `[S₀]₀` to zero kills `[U]₀` for every open `U` of the
base contained in the zero-dimensional locus `S₀`. -/
theorem cap_fundamentalChowClass_opens_eq_zero_of_le_zeroDimensionalLocus
    (hS : IsDedekindChowBase C)
    (c : BivariantClass C G sX (𝟙 C.S) sX (Category.comp_id sX) p)
    (hc : bivariantCapZeroDimensionalLocus C G sX p c = 0)
    {U : C.S.Opens} (hUle : U ≤ zeroDimensionalLocus C) :
    c.cap U.ι 0 (fundamentalChowClass C (U.ι ≫ 𝟙 C.S) 0) = 0 := by
  have hS0 := schemeDeltaDimension_opens_ι_le_zero hS (le_refl (zeroDimensionalLocus C))
  have hB1 := BivariantClass.cap_flatPullbackChow_eq_zero c (zeroDimensionalLocus C).ι
    (C.S.homOfLE hUle) 0 (relativeDimension_of_isOpenImmersion _) 0 _ hc
  rw [flatPullbackChow_fundamentalChowClass _ _ _ _ _ 0 _ 0 _ hS0, Nat.cast_zero, add_zero] at hB1
  exact BivariantClass.cap_fundamentalChowClass_eq_zero_congr C G sX (𝟙 C.S) sX
    (Category.comp_id sX) p c (Scheme.homOfLE_ι _ _).symm 0 hB1

/-- A class `c ∈ A^p(X → S)` capping `[S₀]₀` to zero kills the fundamental class of every
integral scheme `T` over the base whose generic point lies over the zero-dimensional locus
`S₀`. -/
theorem cap_fundamentalChowClass_eq_zero_of_mem_zeroDimensionalLocus (hS : IsDedekindChowBase C)
    (c : BivariantClass C G sX (𝟙 C.S) sX (Category.comp_id sX) p)
    (hc : bivariantCapZeroDimensionalLocus C G sX p c = 0)
    {T : Scheme.{u}} (g : T ⟶ C.S) [LocallyOfFiniteType g] [IsIntegral T]
    (hg : g.base (genericPoint T) ∈ zeroDimensionalLocus C) (k : ℤ) :
    c.cap g k (fundamentalChowClass C (g ≫ 𝟙 C.S) k) = 0 := by
  set s := g.base (genericPoint T) with hs
  obtain ⟨hcl, hgen⟩ := (hS.mem_zeroDimensionalLocus_iff).1 hg
  obtain ⟨U, hU, _⟩ := hS.exists_isIntegral_opens_eq_singleton hcl hgen
  have hmemU : ∀ {x : C.S}, x ∈ U ↔ x = s := fun {x} ↦ by
    rw [← SetLike.mem_coe, hU, Set.mem_singleton_iff]
  have hsU : s ∈ U := hmemU.2 rfl
  have hUle : U ≤ zeroDimensionalLocus C := fun x hx ↦ hmemU.1 hx ▸ hg
  have hrange : ∀ w, g.base w = s := fun w ↦
    eq_of_specializes_of_mem_zeroDimensionalLocus hg
      (((genericPoint_spec T).specializes (Set.mem_univ w)).map g.continuous)
  have _ : Subsingleton (U : Scheme.{u}) :=
    ⟨fun a b ↦ Subtype.ext ((hmemU.1 a.2).trans (hmemU.1 b.2).symm)⟩
  have hUdim := schemeDeltaDimension_opens_ι_le_zero hS hUle
  have hU1 := cap_fundamentalChowClass_opens_eq_zero_of_le_zeroDimensionalLocus G sX p hS c hc hUle
  have hsub : Set.range g.base ⊆ Set.range U.ι.base := by
    rintro _ ⟨w, rfl⟩
    exact ⟨⟨s, hsU⟩, (hrange w).symm⟩
  set h : T ⟶ (U : Scheme.{u}) := IsOpenImmersion.lift U.ι g hsub with hhdef
  have hh : h ≫ U.ι = g := IsOpenImmersion.lift_fac _ _ _
  have _ : LocallyOfFiniteType (h ≫ U.ι) := by
    rw [hh]
    infer_instance
  have _ : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h U.ι
  have _ : Flat h := inferInstance
  have hδs : C.dimensionFunction s = 0 := hS.2.1 _ hcl
  have hnn := relativeDimension_nonneg_of_mem_zeroDimensionalLocus hS g _ hg
  set r := (relativeDimension C.dimensionFunction g (genericPoint T)).toNat with hrdef
  have hr : AlgebraicGeometry.RelativeDimension h r := by
    refine relativeDimension_of_flat_of_coheight C h U.ι r fun w ↦ ?_
    have hmax : Order.coheight (h.base w) = 0 :=
      Order.coheight_eq_zero.mpr fun b _ ↦ le_of_eq (Subsingleton.elim _ _)
    have hUw : U.ι.base (h.base w) = s := by rw [← Scheme.Hom.comp_apply, hh, hrange]
    rw [hmax, zero_add, hh, ← Category.comp_id U.ι, relativeDimension_opensι_comp,
      relativeDimension_id, hUw, hδs, sub_zero]
  have hB5 := BivariantClass.cap_flatPullbackChow_eq_zero c U.ι h r hr 0 _ hU1
  rw [flatPullbackChow_fundamentalChowClass _ _ _ _ _ r _ 0 _ hUdim] at hB5
  have hrd : relativeDimension C.dimensionFunction (g ≫ 𝟙 C.S) (genericPoint T) = 0 + r := by
    rw [Category.comp_id, zero_add, hrdef, Int.toNat_of_nonneg hnn]
  by_cases hk : k = 0 + r
  · subst hk
    exact BivariantClass.cap_fundamentalChowClass_eq_zero_congr C G sX (𝟙 C.S) sX
      (Category.comp_id sX) p c hh.symm _ hB5
  · rw [fundamentalChowClass_eq_zero_of_ne C (g ≫ 𝟙 C.S) (by rw [hrd]; exact Ne.symm hk),
      map_zero]

/-- The class `c ∩ [S]₁` of Stacks 0FC5 restricts to zero over the zero-dimensional locus `S₀`
of the base, that is, on `X ×_S S₀`. -/
theorem chowGroupRestrict_bivariantCapBaseFundamentalClass_eq_zero (hS : IsDedekindChowBase C)
    (c : BivariantClass C G sX (𝟙 C.S) sX (Category.comp_id sX) p) :
    chowGroupRestrict C sX ((sX ⁻¹ᵁ zeroDimensionalLocus C).ι ≫ sX)
        (sX ⁻¹ᵁ zeroDimensionalLocus C).ι rfl (1 - p)
        (bivariantCapBaseFundamentalClass C G sX p c) = 0 := by
  set e' : X ⟶ pullback sX (𝟙 C.S) := pullback.lift (𝟙 X) sX (by simp) with he'
  have hee' : e' ≫ pullback.fst sX (𝟙 C.S) = 𝟙 X := pullback.lift_fst _ _ _
  have _ : IsIso e' := by
    have : IsIso (e' ≫ pullback.fst sX (𝟙 C.S)) := by
      rw [hee']
      infer_instance
    exact IsIso.of_isIso_comp_right e' (pullback.fst sX (𝟙 C.S))
  rw [bivariantCapBaseFundamentalClass_apply, basePullbackPushforward_eq_chowPushforwardOfIso,
    chowPushforwardOfIso_eq_chowGroupRestrict C _ _ _ _ e' hee', chowGroupRestrict_comp]
  have sq := isPullback_bivariantBaseChangeMap sX (𝟙 C.S) (zeroDimensionalLocus C).ι
  have _ : IsOpenImmersion (bivariantBaseChangeMap sX (𝟙 C.S) (zeroDimensionalLocus C).ι) :=
    MorphismProperty.of_isPullback sq (P := @IsOpenImmersion) inferInstance
  have hbase : bivariantBaseChangeMap sX (𝟙 C.S) (zeroDimensionalLocus C).ι ≫
      (pullback.fst sX (𝟙 C.S) ≫ sX) =
      pullback.fst sX ((zeroDimensionalLocus C).ι ≫ 𝟙 C.S) ≫ sX := by
    rw [← Category.assoc, bivariantBaseChangeMap_fst]
  have hcap := BivariantClass.cap_chowGroupRestrict C G sX (𝟙 C.S) sX (Category.comp_id sX) p c
    (𝟙 C.S) (zeroDimensionalLocus C).ι ((zeroDimensionalLocus C).ι ≫ 𝟙 C.S) rfl
    (bivariantBaseChangeMap sX (𝟙 C.S) (zeroDimensionalLocus C).ι) sq
    (bivariantBaseChangeMap_fst _ _ _) 1 (by simp) hbase (baseFundamentalChowClass C)
  have hres : chowGroupRestrict C (𝟙 C.S ≫ 𝟙 C.S)
      (((zeroDimensionalLocus C).ι ≫ 𝟙 C.S) ≫ 𝟙 C.S) (zeroDimensionalLocus C).ι (by simp) 1
      (baseFundamentalChowClass C) = 0 := by
    rw [baseFundamentalChowClass, chowGroupRestrict_fundamentalChowClass C _ _ _ _ 1
      (hS.schemeDeltaDimension_le_one _)]
    have := subsingleton_chowGroup_of_schemeDeltaDimension_le C
      (((zeroDimensionalLocus C).ι ≫ 𝟙 C.S) ≫ 𝟙 C.S) (n := 0) (k := 1)
      (hS.schemeDeltaDimension_le_zero _ fun t ↦ by
        rw [Category.comp_id, Category.comp_id]
        exact t.2) (by norm_num)
    exact Subsingleton.elim _ _
  rw [hres, map_zero] at hcap
  refine (chowGroupRestrict_eq_of_opensRange_le C _ _ _
    (bivariantBaseChangeMap sX (𝟙 C.S) (zeroDimensionalLocus C).ι) hbase
    ((sX ⁻¹ᵁ zeroDimensionalLocus C).ι ≫ e') _ ?_ (1 - p)
    (hcap.trans (map_zero _).symm)).trans (map_zero _)
  rintro _ ⟨z, rfl⟩
  obtain ⟨y, hy⟩ : ((sX ⁻¹ᵁ zeroDimensionalLocus C).ι ≫ e').base z ∈
      Set.range (pullback.fst (pullback.snd sX (𝟙 C.S)) (zeroDimensionalLocus C).ι).base := by
    rw [IsOpenImmersion.range_pullbackFst]
    show (pullback.snd sX (𝟙 C.S)).base (((sX ⁻¹ᵁ zeroDimensionalLocus C).ι ≫ e').base z) ∈
      (zeroDimensionalLocus C).ι.opensRange
    rw [← Scheme.Hom.comp_apply, Category.assoc, he', pullback.lift_snd,
      Scheme.Opens.opensRange_ι, Scheme.Hom.comp_apply]
    exact z.2
  refine ⟨sq.flip.isoPullback.inv.base y, ?_⟩
  rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hy]


/-- **Stacks 0FC5, injectivity, over an arbitrary base as in section 42.63.** A class
`c ∈ A^p(X → S)` is determined by `c ∩ [S]₁ ∈ CH_{1-p}(X)` together with
`c ∩ [S₀]₀ ∈ CH_{-p}(X ×_S S₀)`, where `S₀` is the zero-dimensional locus. -/
theorem eq_of_bivariantCapBaseFundamentalClass_eq_of_bivariantCapZeroDimensionalLocus_eq
    (hS : IsDedekindChowBase C)
    {c d : BivariantClass C (gysinSystemOfInvertible C) sX (𝟙 C.S) sX (Category.comp_id sX) p}
    (h₁ : bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p c =
      bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p d)
    (h₀ : bivariantCapZeroDimensionalLocus C (gysinSystemOfInvertible C) sX p c =
      bivariantCapZeroDimensionalLocus C (gysinSystemOfInvertible C) sX p d) :
    c = d := by
  rw [← sub_eq_zero, BivariantClass.eq_zero_iff_capsIntegral_canonical]
  intro T g _ _ k
  by_cases hg : g.base (genericPoint T) ∈ zeroDimensionalLocus C
  · refine cap_fundamentalChowClass_eq_zero_of_mem_zeroDimensionalLocus _ sX p hS (c - d) ?_ g hg k
    rwa [map_sub, sub_eq_zero]
  refine cap_fundamentalChowClass_eq_zero_of_dimensionFunction_eq_one C sX p hS (c - d) ?_ g k
    fun hgen ↦ hS.dimensionFunction_eq_one_of_notMem_zeroDimensionalLocus hgen hg
  rw [BivariantClass.sub_cap, sub_eq_zero]
  exact chowPushforwardOfIso_injective C _ _ (basePullbackProjection C sX) rfl (1 - p) h₁

end Injective

/-! ### Generation away from the zero-dimensional locus -/

section PositiveDimensional

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (p : ℤ)

/-- **A subgroup of `CH_{1-p}(X)` containing the generators is everything**, for a partition of
the points of `X` into three classes `Q₁`, `Q₂`, `Q₃`: if `K` contains the class of a cycle
`∑_j [y_j]` for every locally finite family of points of delta-dimension `1 - p` all in the same
class, then `K` contains every class. -/
theorem mem_of_forall_cycle_generators_of_partition (K : AddSubgroup (chowGroup C sX (1 - p)))
    (Q₁ Q₂ Q₃ : X → Prop)
    (hQ : ∀ x, (Q₁ x ∧ ¬Q₂ x ∧ ¬Q₃ x) ∨ (¬Q₁ x ∧ Q₂ x ∧ ¬Q₃ x) ∨ (¬Q₁ x ∧ ¬Q₂ x ∧ Q₃ x))
    (h₁ : ∀ {J : Type u} (y : J → X),
      LocallyFinite (fun j ↦ Set.range (integralComponentAt (y j)).subschemeι) →
      (∀ j, relativeDimension C.dimensionFunction sX (y j) = 1 - p) → (∀ j, Q₁ (y j)) →
      ∃ P : CycleGroup C sX (1 - p),
        QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p)) P ∈ K ∧
          ∀ x, P.1 x = ∑ᶠ j ∈ y ⁻¹' {x}, (1 : ℤ))
    (h₂ : ∀ {J : Type u} (y : J → X),
      LocallyFinite (fun j ↦ Set.range (integralComponentAt (y j)).subschemeι) →
      (∀ j, relativeDimension C.dimensionFunction sX (y j) = 1 - p) → (∀ j, Q₂ (y j)) →
      ∃ P : CycleGroup C sX (1 - p),
        QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p)) P ∈ K ∧
          ∀ x, P.1 x = ∑ᶠ j ∈ y ⁻¹' {x}, (1 : ℤ))
    (h₃ : ∀ {J : Type u} (y : J → X),
      LocallyFinite (fun j ↦ Set.range (integralComponentAt (y j)).subschemeι) →
      (∀ j, relativeDimension C.dimensionFunction sX (y j) = 1 - p) → (∀ j, Q₃ (y j)) →
      ∃ P : CycleGroup C sX (1 - p),
        QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p)) P ∈ K ∧
          ∀ x, P.1 x = ∑ᶠ j ∈ y ⁻¹' {x}, (1 : ℤ))
    (α : chowGroup C sX (1 - p)) : α ∈ K := by
  classical
  induction α using QuotientAddGroup.induction_on with
  | H a =>
  obtain ⟨P₁, hP₁, hP₁y⟩ := exists_cycle_mem_of_multiplicity C sX p K a Q₁
    (fun y hlf hδ hQ ↦ h₁ y hlf hδ hQ) fun i ↦ (a.1 i).toNat
  obtain ⟨N₁, hN₁, hN₁y⟩ := exists_cycle_mem_of_multiplicity C sX p K a Q₁
    (fun y hlf hδ hQ ↦ h₁ y hlf hδ hQ) fun i ↦ (-a.1 i).toNat
  obtain ⟨P₂, hP₂, hP₂y⟩ := exists_cycle_mem_of_multiplicity C sX p K a Q₂
    (fun y hlf hδ hQ ↦ h₂ y hlf hδ hQ) fun i ↦ (a.1 i).toNat
  obtain ⟨N₂, hN₂, hN₂y⟩ := exists_cycle_mem_of_multiplicity C sX p K a Q₂
    (fun y hlf hδ hQ ↦ h₂ y hlf hδ hQ) fun i ↦ (-a.1 i).toNat
  obtain ⟨P₃, hP₃, hP₃y⟩ := exists_cycle_mem_of_multiplicity C sX p K a Q₃
    (fun y hlf hδ hQ ↦ h₃ y hlf hδ hQ) fun i ↦ (a.1 i).toNat
  obtain ⟨N₃, hN₃, hN₃y⟩ := exists_cycle_mem_of_multiplicity C sX p K a Q₃
    (fun y hlf hδ hQ ↦ h₃ y hlf hδ hQ) fun i ↦ (-a.1 i).toNat
  have hsub : a = P₁ - N₁ + (P₂ - N₂) + (P₃ - N₃) := by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
    show a.1 x = P₁.1 x - N₁.1 x + (P₂.1 x - N₂.1 x) + (P₃.1 x - N₃.1 x)
    rw [hP₁y, hN₁y, hP₂y, hN₂y, hP₃y, hN₃y]
    by_cases hx : x ∈ Function.support (a.1 : X → ℤ)
    · rcases hQ x with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · rw [dif_pos ⟨hx, h1⟩, dif_pos ⟨hx, h1⟩, dif_neg (fun h ↦ h2 h.2),
          dif_neg (fun h ↦ h2 h.2), dif_neg (fun h ↦ h3 h.2), dif_neg (fun h ↦ h3 h.2)]
        simp only
        omega
      · rw [dif_neg (fun h ↦ h1 h.2), dif_neg (fun h ↦ h1 h.2), dif_pos ⟨hx, h2⟩,
          dif_pos ⟨hx, h2⟩, dif_neg (fun h ↦ h3 h.2), dif_neg (fun h ↦ h3 h.2)]
        simp only
        omega
      · rw [dif_neg (fun h ↦ h1 h.2), dif_neg (fun h ↦ h1 h.2), dif_neg (fun h ↦ h2 h.2),
          dif_neg (fun h ↦ h2 h.2), dif_pos ⟨hx, h3⟩, dif_pos ⟨hx, h3⟩]
        simp only
        omega
    · rw [dif_neg (fun h ↦ hx h.1), dif_neg (fun h ↦ hx h.1), dif_neg (fun h ↦ hx h.1),
        dif_neg (fun h ↦ hx h.1), dif_neg (fun h ↦ hx h.1), dif_neg (fun h ↦ hx h.1)]
      simpa using hx
  rw [hsub]
  show QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p))
    (P₁ - N₁ + (P₂ - N₂) + (P₃ - N₃)) ∈ K
  rw [map_add, map_add, map_sub, map_sub, map_sub]
  exact add_mem (add_mem (sub_mem hP₁ hN₁) (sub_mem hP₂ hN₂)) (sub_mem hP₃ hN₃)

/-- **The images of central classes away from the zero-dimensional locus.** Over a base as in
section 42.63, every class in `CH_{1-p}(X)` agrees, on the open part of `X` lying over the
positive-dimensional locus of the base, with `c ∩ [S]₁` for some central `c ∈ A^p(X → S)`. -/
theorem exists_mem_centralOverBaseSubgroup_restrict_eq (hS : IsDedekindChowBase C)
    (α : chowGroup C sX (1 - p)) :
    ∃ d ∈ centralOverBaseSubgroup C (gysinSystemOfInvertible C) sX p,
      chowGroupRestrict C sX ((sX ⁻¹ᵁ hS.positiveDimensionalLocus).ι ≫ sX)
          (sX ⁻¹ᵁ hS.positiveDimensionalLocus).ι rfl (1 - p)
          (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p d) =
        chowGroupRestrict C sX ((sX ⁻¹ᵁ hS.positiveDimensionalLocus).ι ≫ sX)
          (sX ⁻¹ᵁ hS.positiveDimensionalLocus).ι rfl (1 - p) α := by
  set res := chowGroupRestrict C sX ((sX ⁻¹ᵁ hS.positiveDimensionalLocus).ι ≫ sX)
    (sX ⁻¹ᵁ hS.positiveDimensionalLocus).ι rfl (1 - p) with hres
  set K₀ := (centralOverBaseSubgroup C (gysinSystemOfInvertible C) sX p).map
    (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p) with hK₀
  have hK : ∀ β ∈ K₀, β ∈ (K₀.map res).comap res := fun β hβ ↦ ⟨β, hβ, rfl⟩
  have hmem : α ∈ (K₀.map res).comap res := by
    refine mem_of_forall_cycle_generators_of_partition C sX p _
      (fun x ↦ sX.base x ∈ genericPoints C.S ∧ sX.base x ∉ zeroDimensionalLocus C)
      (fun x ↦ sX.base x ∈ zeroDimensionalLocus C) (fun x ↦ sX.base x ∉ genericPoints C.S)
      (fun x ↦ ?_) (fun y hlf hδ hQ ↦ ?_) (fun y hlf hδ hQ ↦ ?_) (fun y hlf hδ hQ ↦ ?_) α
    · by_cases h0 : sX.base x ∈ zeroDimensionalLocus C
      · have hg := ((hS.mem_zeroDimensionalLocus_iff).1 h0).2
        exact Or.inr (Or.inl ⟨fun h ↦ h.2 h0, h0, fun h ↦ h hg⟩)
      · by_cases hg : sX.base x ∈ genericPoints C.S
        · exact Or.inl ⟨⟨hg, h0⟩, h0, fun h ↦ h hg⟩
        · exact Or.inr (Or.inr ⟨fun h ↦ hg h.1, h0, hg⟩)
    · obtain ⟨P, hP, hPy⟩ :=
        exists_cycle_mem_central_of_mem_genericPoints_of_dimensionFunction_eq_one C sX p hS y hlf
          hδ (fun j ↦ (hQ j).1) fun j ↦
            hS.dimensionFunction_eq_one_of_notMem_zeroDimensionalLocus (hQ j).1 (hQ j).2
      exact ⟨P, hK _ hP, hPy⟩
    · set Zs := fun j ↦ (integralComponentAt (y j)).subscheme with hZs
      set v : ∀ j, Zs j ⟶ X := fun j ↦ (integralComponentAt (y j)).subschemeι with hv
      have _ : ∀ j, IsIntegral (Zs j) := fun j ↦ isIntegral_integralComponentAt _
      have _ : IsProper (Sigma.desc v) := isProper_sigmaDesc_of_locallyFinite Zs v hlf
      have hπ : ∀ j, (v j).base (genericPoint (Zs j)) = y j := fun j ↦
        genericPointOf_integralComponentAt _
      refine ⟨properPushforward C (Sigma.desc v ≫ sX) sX (Sigma.desc v) rfl (1 - p)
        (fundamentalCycle C _ (1 - p)), ⟨0, ⟨0, zero_mem _, map_zero _⟩, ?_⟩,
        fun x ↦ properPushforward_fundamentalCycle_sigma_apply C sX Zs v y hπ (1 - p) hδ x⟩
      rw [map_zero, hres, chowGroupRestrict_mk]
      have h0 : cycleGroupRestrict C sX ((sX ⁻¹ᵁ hS.positiveDimensionalLocus).ι ≫ sX)
          (sX ⁻¹ᵁ hS.positiveDimensionalLocus).ι rfl (1 - p)
          (properPushforward C (Sigma.desc v ≫ sX) sX (Sigma.desc v) rfl (1 - p)
            (fundamentalCycle C _ (1 - p))) = 0 := by
        refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
        rw [cycleGroupRestrict_apply,
          properPushforward_fundamentalCycle_sigma_apply C sX Zs v y hπ (1 - p) hδ]
        refine (finsum_mem_congr (Set.eq_empty_of_forall_notMem fun j hj ↦ ?_)
          fun _ _ ↦ rfl).trans finsum_mem_empty
        have hj' : y j = (sX ⁻¹ᵁ hS.positiveDimensionalLocus).ι.base x := hj
        have hx : sX.base ((sX ⁻¹ᵁ hS.positiveDimensionalLocus).ι.base x) ∉
            zeroDimensionalLocus C := x.2
        exact hx (by rw [← hj']; exact hQ j)
      rw [h0, map_zero]
    · obtain ⟨P, hP, hPy⟩ :=
        exists_cycle_mem_central_of_notMem_genericPoints C sX p hS y hlf hδ hQ
      exact ⟨P, hK _ hP, hPy⟩
  obtain ⟨_, ⟨d, hd, rfl⟩, he⟩ := hmem
  exact ⟨d, hd, he⟩

end PositiveDimensional

/-! ### Generation over the zero-dimensional locus -/

section ZeroDimensional

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **The generators over the zero-dimensional locus.** Over a base as in section 42.63, let
`(y_j)` be a locally finite family of points of `X ×_S S₀` of delta-dimension `r`, `S₀` the
zero-dimensional locus. Then the cycle `∑_j [y_j]` is `d ∩ [S₀]₀` for a central class
`d ∈ A^{-r}(X → S)` with `d ∩ [S]₁ = 0`. -/
theorem exists_cycle_mem_bivariantCapZeroDimensionalLocus_of_sigma (hS : IsDedekindChowBase C)
    {J : Type u} (y : J → (pullback sX (zeroDimensionalLocus C).ι : Scheme.{u}))
    (hlf : LocallyFinite fun j ↦ Set.range (integralComponentAt (y j)).subschemeι) (r : ℕ)
    (hδ : ∀ j, relativeDimension C.dimensionFunction
      (pullback.fst sX (zeroDimensionalLocus C).ι ≫ sX) (y j) = 0 - -(r : ℤ)) :
    ∃ P : CycleGroup C (pullback.fst sX (zeroDimensionalLocus C).ι ≫ sX) (0 - -(r : ℤ)),
      QuotientAddGroup.mk' (rationalEquivalences C _ (0 - -(r : ℤ))) P ∈
          ((centralOverBaseSubgroup C (gysinSystemOfInvertible C) sX (-(r : ℤ))) ⊓
              (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX
                (-(r : ℤ))).ker).map
            (bivariantCapZeroDimensionalLocus C (gysinSystemOfInvertible C) sX (-(r : ℤ))) ∧
        ∀ x, P.1 x = ∑ᶠ j ∈ y ⁻¹' {x}, (1 : ℤ) := by
  have _ := hS.isClosedImmersion_zeroDimensionalLocus_ι
  set Zs := fun j ↦ (integralComponentAt (y j)).subscheme with hZs
  set v : ∀ j, Zs j ⟶ pullback sX (zeroDimensionalLocus C).ι :=
    fun j ↦ (integralComponentAt (y j)).subschemeι with hv
  have _ : ∀ j, IsIntegral (Zs j) := fun j ↦ isIntegral_integralComponentAt _
  have _ : IsProper (Sigma.desc v) := isProper_sigmaDesc_of_locallyFinite Zs v hlf
  have hπ : ∀ j, (v j).base (genericPoint (Zs j)) = y j := fun j ↦
    genericPointOf_integralComponentAt _
  have hpt := fst_comp_base_mem_zeroDimensionalLocus sX
  have hgen : ∀ j, (pullback.fst sX (zeroDimensionalLocus C).ι ≫ sX).base (y j) ∈
      genericPoints C.S := fun j ↦ ((hS.mem_zeroDimensionalLocus_iff).1 (hpt _)).2
  obtain ⟨g, hg⟩ : ∃ g : (∐ Zs : Scheme.{u}) ⟶ X,
      g = Sigma.desc v ≫ pullback.fst sX (zeroDimensionalLocus C).ι := ⟨_, rfl⟩
  have _ : IsProper g := by
    rw [hg]
    infer_instance
  have hιj : ∀ j, Sigma.ι Zs j ≫ g ≫ sX =
      v j ≫ (pullback.fst sX (zeroDimensionalLocus C).ι ≫ sX) := by
    intro j
    rw [hg, Category.assoc, Sigma.ι_desc_assoc]
  have hflat : ∀ j, Flat (v j ≫ (pullback.fst sX (zeroDimensionalLocus C).ι ≫ sX)) := fun j ↦ by
    refine hS.flat_of_mem_genericPoints _ ?_
    rw [Scheme.Hom.comp_apply, subschemeι_genericPoint_integralComponentAt]
    exact hgen j
  have hdesc : g ≫ sX = Sigma.desc fun j ↦
      v j ≫ (pullback.fst sX (zeroDimensionalLocus C).ι ≫ sX) :=
    Sigma.hom_ext _ _ fun j ↦ by rw [hιj, Sigma.ι_desc]
  have _ : Flat (g ≫ sX) := by
    have := hflat
    rw [hdesc]
    infer_instance
  have hr : AlgebraicGeometry.RelativeDimension (g ≫ sX) r := by
    refine AlgebraicGeometry.RelativeDimension.of_sigmaι_comp Zs _ fun j ↦ ?_
    have _ := hflat j
    have h := hS.relativeDimension_integralComponentAt_comp
      (pullback.fst sX (zeroDimensionalLocus C).ι ≫ sX) (y j) (hgen j)
    have e : (relativeDimension C.dimensionFunction
        (pullback.fst sX (zeroDimensionalLocus C).ι ≫ sX) (y j) -
        C.dimensionFunction ((pullback.fst sX (zeroDimensionalLocus C).ι ≫ sX).base (y j))).toNat =
        r := by
      rw [hδ j, hS.dimensionFunction_eq_zero_of_mem_zeroDimensionalLocus (hpt _)]
      omega
    rw [e] at h
    exact AlgebraicGeometry.RelativeDimension.of_eq (hιj j).symm h
  set ξ := flatPullbackBivariantClassOfInvertible C (g ≫ sX) (𝟙 C.S) (g ≫ sX)
    (Category.comp_id _) r hr with hξ
  have hξφ : IsBivariantFlatPullback C (gysinSystemOfInvertible C) (g ≫ sX) (𝟙 C.S) (g ≫ sX)
      (Category.comp_id _) r hr (flatPullbackDescends C) ξ :=
    isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C (g ≫ sX) (𝟙 C.S) (g ≫ sX)
      (Category.comp_id _) r hr
  have hξc : IsCentralOverBase C (gysinSystemOfInvertible C) (g ≫ sX) (-(r : ℤ)) ξ :=
    (IsChowOperationClassOverBase.flat _ r hr _
      (isFlatPullbackOverBase_flatPullbackBivariantClass C _ _ r hr _ hξφ)).isCentralOverBase
  set d := bivariantProperPushforwardOfInvertible C (g ≫ sX) sX (𝟙 C.S) g sX rfl
    (Category.comp_id sX) (-(r : ℤ)) ξ with hd
  have hdc : IsCentralOverBase C (gysinSystemOfInvertible C) sX (-(r : ℤ)) d :=
    fun _ _ sZ _ w _ q c' ↦ bivariantCommuteOverBase_of_isBivariantProperPushforward C _ sX sZ w _
      (properPushforwardDescends C) (-(r : ℤ)) q _ ξ c'
      (isBivariantProperPushforward_bivariantProperPushforwardOfInvertible C _ sX (𝟙 C.S) _ sX rfl
        (Category.comp_id sX) (-(r : ℤ)) ξ) (hξc sZ w q c')
  have hWdim : schemeDeltaDimension C (g ≫ sX) ≤ ((r : ℤ) : EInt) := by
    rw [← schemeDeltaDimension_congr C (Category.id_comp (g ≫ sX))]
    refine schemeDeltaDimension_le_of_forall_relativeDimension_le C (g ≫ sX) (𝟙 _) fun w ↦ ?_
    obtain ⟨j, z, rfl⟩ := exists_mem_range_sigmaι Zs w
    have hZ : schemeDeltaDimension C (𝟙 (Zs j) ≫ Sigma.ι Zs j ≫ g ≫ sX) ≤ ((r : ℤ) : EInt) := by
      rw [schemeDeltaDimension_eq_genericPoint, relativeDimension_comp_closedImmersion, hιj]
      have h := relativeDimension_sigmaι_genericPoint C
        (pullback.fst sX (zeroDimensionalLocus C).ι ≫ sX) Zs v y hπ _ hδ j
      rw [← Category.assoc, Sigma.ι_desc] at h
      simp [h]
    have h1 := relativeDimension_le_of_schemeDeltaDimension_le C _ (𝟙 (Zs j)) hZ z
    rw [relativeDimension_comp_isOpenImmersion] at h1
    simpa using h1
  have hd1 :
      bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX (-(r : ℤ)) d = 0 := by
    rw [hd, bivariantCapBaseFundamentalClass_bivariantProperPushforward,
      bivariantCapBaseFundamentalClass_flatPullbackBivariantClass C _ _ r hr _ hξφ
        (hS.schemeDeltaDimension_le_one (𝟙 C.S ≫ 𝟙 C.S))]
    have := subsingleton_chowGroup_of_schemeDeltaDimension_le C (g ≫ sX) hWdim
      (k := 1 - -(r : ℤ)) (by omega)
    rw [Subsingleton.elim (fundamentalChowClass C (g ≫ sX) (1 - -(r : ℤ))) 0, map_zero]
  have hS0 := schemeDeltaDimension_opens_ι_le_zero hS (le_refl (zeroDimensionalLocus C))
  have _ : IsIso (pullback.fst (g ≫ sX) (zeroDimensionalLocus C).ι) :=
    isIso_pullbackFst_of_comp_eq _ _ (Sigma.desc v ≫ pullback.snd sX _) (by
      rw [hg, Category.assoc, Category.assoc, ← pullback.condition])
  have hcomp : pullback.fst (g ≫ sX) (zeroDimensionalLocus C).ι ≫ Sigma.desc v =
      bivariantPushforwardBaseChange g sX (zeroDimensionalLocus C).ι := by
    refine pullback.hom_ext ?_ ?_
    · rw [bivariantPushforwardBaseChange_fst, Category.assoc, ← hg]
    · rw [bivariantPushforwardBaseChange_snd]
      refine (cancel_mono (zeroDimensionalLocus C).ι).1 ?_
      rw [← pullback.condition, Category.assoc, Category.assoc, ← pullback.condition, hg]
      simp only [Category.assoc]
  have hu : pullback.fst (g ≫ sX) (zeroDimensionalLocus C).ι ≫
      (Sigma.desc v ≫ (pullback.fst sX (zeroDimensionalLocus C).ι ≫ sX)) =
      pullback.fst (g ≫ sX) (zeroDimensionalLocus C).ι ≫ (g ≫ sX) := by
    rw [hg]
    simp only [Category.assoc]
  refine ⟨properPushforward C (Sigma.desc v ≫ (pullback.fst sX (zeroDimensionalLocus C).ι ≫ sX))
    _ (Sigma.desc v) rfl (0 - -(r : ℤ)) (fundamentalCycle C _ (0 - -(r : ℤ))),
    ⟨d, ⟨hdc, hd1⟩, ?_⟩, fun x ↦ properPushforward_fundamentalCycle_sigma_apply C _ Zs v y hπ _
      hδ x⟩
  rw [bivariantCapZeroDimensionalLocus_apply, hd,
    isBivariantProperPushforward_bivariantProperPushforwardOfInvertible,
    bivariantProperPushforwardCap_apply,
    hξφ.cap_fundamentalChowClass (zeroDimensionalLocus C).ι 0 hS0,
    properChowPushforward_comp_apply C _
      (Sigma.desc v ≫ (pullback.fst sX (zeroDimensionalLocus C).ι ≫ sX)) _
      (pullback.fst (g ≫ sX) (zeroDimensionalLocus C).ι) (Sigma.desc v) _ hcomp hu rfl _ _
      (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _),
    properChowPushforward_eq_chowPushforwardOfIso C _ _
      (pullback.fst (g ≫ sX) (zeroDimensionalLocus C).ι) hu,
    chowPushforwardOfIso_fundamentalChowClass]
  rfl

/-- **The classes `c ∩ [S₀]₀` of central classes exhaust `CH_{-p}(X ×_S S₀)`.** Over a base as in
section 42.63, every class in `CH_{-p}(X ×_S S₀)`, `S₀` the zero-dimensional locus, is `d ∩ [S₀]₀`
for a central `d ∈ A^p(X → S)` with `d ∩ [S]₁ = 0`. -/
theorem exists_mem_centralOverBaseSubgroup_bivariantCapZeroDimensionalLocus_eq
    (hS : IsDedekindChowBase C) (p : ℤ)
    (β : chowGroup C (pullback.fst sX (zeroDimensionalLocus C).ι ≫ sX) (0 - p)) :
    ∃ d ∈ centralOverBaseSubgroup C (gysinSystemOfInvertible C) sX p,
      bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p d = 0 ∧
        bivariantCapZeroDimensionalLocus C (gysinSystemOfInvertible C) sX p d = β := by
  suffices h : β ∈ ((centralOverBaseSubgroup C (gysinSystemOfInvertible C) sX p) ⊓
      (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p).ker).map
        (bivariantCapZeroDimensionalLocus C (gysinSystemOfInvertible C) sX p) by
    obtain ⟨d, ⟨hd1, hd2⟩, hd3⟩ := h
    exact ⟨d, hd1, hd2, hd3⟩
  classical
  induction β using QuotientAddGroup.induction_on with
  | H a =>
  have hpt := fst_comp_base_mem_zeroDimensionalLocus sX
  by_cases hp : 0 < p
  · have ha : a = 0 := by
      refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
      by_contra hx
      have h1 := (mem_cyclesOfDimension_iff_forall_point C _ (0 - p) a.1).1 a.2 x hx
      have h2 := relativeDimension_nonneg_of_mem_zeroDimensionalLocus hS _ x (hpt x)
      omega
    rw [ha]
    exact zero_mem _
  obtain ⟨r, rfl⟩ : ∃ r : ℕ, p = -(r : ℤ) := ⟨(-p).toNat, by omega⟩
  have hgen : ∀ M : ↥(Function.support (a.1 : _ → ℤ)) → ℕ,
      ∃ P : CycleGroup C (pullback.fst sX (zeroDimensionalLocus C).ι ≫ sX) (0 - -(r : ℤ)),
        QuotientAddGroup.mk' (rationalEquivalences C _ (0 - -(r : ℤ))) P ∈
            ((centralOverBaseSubgroup C (gysinSystemOfInvertible C) sX (-(r : ℤ))) ⊓
                (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX
                  (-(r : ℤ))).ker).map
              (bivariantCapZeroDimensionalLocus C (gysinSystemOfInvertible C) sX (-(r : ℤ))) ∧
          ∀ x, P.1 x = if h : x ∈ Function.support (a.1 : _ → ℤ) then (M ⟨x, h⟩ : ℤ) else 0 := by
    intro M
    let y : (Σ i : ↥(Function.support (a.1 : _ → ℤ)), Fin (M i)) →
        (pullback sX (zeroDimensionalLocus C).ι : Scheme.{u}) := fun j ↦ j.1.1
    have hlf : LocallyFinite fun j ↦ Set.range (integralComponentAt (y j)).subschemeι :=
      locallyFinite_sigma_fst (locallyFinite_range_subschemeι_support C _ _ a)
    obtain ⟨P, hP, hPy⟩ := exists_cycle_mem_bivariantCapZeroDimensionalLocus_of_sigma C sX hS y hlf
      r fun j ↦ (mem_cyclesOfDimension_iff_forall_point C _ _ a.1).1 a.2 _ j.1.2
    refine ⟨P, hP, fun x ↦ ?_⟩
    rw [hPy]
    by_cases hx : x ∈ Function.support (a.1 : _ → ℤ)
    · rw [dif_pos hx]
      exact (finsum_mem_preimage_sigma_fst_one
        (fun i : ↥(Function.support (a.1 : _ → ℤ)) ↦ i.1) Subtype.val_injective
        ⟨x, hx⟩).trans (by simp)
    · rw [dif_neg hx]
      refine (finsum_mem_congr (Set.eq_empty_of_forall_notMem fun j hj ↦ hx ?_)
        fun _ _ ↦ rfl).trans finsum_mem_empty
      exact (show j.1.1 = x from hj) ▸ j.1.2
  obtain ⟨P, hP, hPy⟩ := hgen fun i ↦ (a.1 i).toNat
  obtain ⟨N, hN, hNy⟩ := hgen fun i ↦ (-a.1 i).toNat
  have hsub : a = P - N := by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
    show a.1 x = P.1 x - N.1 x
    rw [hPy, hNy]
    split_ifs with h
    · simp only
      omega
    · simpa using h
  rw [hsub]
  show QuotientAddGroup.mk' _ (P - N) ∈ _
  rw [map_sub]
  exact sub_mem hP hN

end ZeroDimensional

/-! ### Stacks 0FC6 -/

section Dedekind

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (p : ℤ)

/-- **Stacks 0FC6, centrality form**, over every base as in section 42.63. Every
`c ∈ A^p(X ⟶ S)` is central over the base. -/
theorem isCentralOverBase_of_isDedekindChowBase_general (hS : IsDedekindChowBase C)
    (c : BivariantClass C (gysinSystemOfInvertible C) sX (𝟙 C.S) sX (Category.comp_id sX) p) :
    IsCentralOverBase C (gysinSystemOfInvertible C) sX p c := by
  obtain ⟨d₁, hd₁, h₁⟩ := exists_mem_centralOverBaseSubgroup_restrict_eq C sX p hS
    (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p c)
  let UX : ULift.{u} Bool → X.Opens := fun i ↦
    cond i.down (sX ⁻¹ᵁ hS.positiveDimensionalLocus) (sX ⁻¹ᵁ zeroDimensionalLocus C)
  have hdisj : Disjoint (sX ⁻¹ᵁ hS.positiveDimensionalLocus) (sX ⁻¹ᵁ zeroDimensionalLocus C) :=
    TopologicalSpace.Opens.coe_disjoint.mp (Set.disjoint_left.mpr fun _ h1 h2 ↦ h1 h2)
  have hUX : IsClopenDecomposition UX := by
    refine ⟨fun i j hij ↦ ?_, eq_top_iff.mpr fun x _ ↦ ?_⟩
    · rcases i with ⟨_ | _⟩ <;> rcases j with ⟨_ | _⟩
      · exact absurd rfl hij
      · exact hdisj.symm
      · exact hdisj
      · exact absurd rfl hij
    · rw [TopologicalSpace.Opens.mem_iSup]
      by_cases h : sX.base x ∈ zeroDimensionalLocus C
      · exact ⟨⟨false⟩, h⟩
      · exact ⟨⟨true⟩, h⟩
  have hP : IsClopenDecomposition fun i ↦ (UX i).ι.opensRange := by
    simpa only [Scheme.Opens.opensRange_ι] using hUX
  have hΦ₁ : bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p d₁ =
      bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p c := by
    refine (chowGroupClopenRestrictEquiv C sX (fun i ↦ (UX i).ι ≫ sX) (fun i ↦ (UX i).ι)
      (fun _ ↦ rfl) hP (1 - p)).injective (funext fun i ↦ ?_)
    rw [chowGroupClopenRestrictEquiv_apply, chowGroupClopenRestrictEquiv_apply]
    rcases i with ⟨_ | _⟩
    · exact (chowGroupRestrict_bivariantCapBaseFundamentalClass_eq_zero _ sX p hS d₁).trans
        (chowGroupRestrict_bivariantCapBaseFundamentalClass_eq_zero _ sX p hS c).symm
    · exact h₁
  obtain ⟨d₀, hd₀, hd₀1, hd₀0⟩ :=
    exists_mem_centralOverBaseSubgroup_bivariantCapZeroDimensionalLocus_eq C sX hS p
      (bivariantCapZeroDimensionalLocus C (gysinSystemOfInvertible C) sX p (c - d₁))
  have hc : c = d₁ + d₀ := by
    refine eq_of_bivariantCapBaseFundamentalClass_eq_of_bivariantCapZeroDimensionalLocus_eq sX p
      hS ?_ ?_
    · rw [map_add, hΦ₁, hd₀1, add_zero]
    · rw [map_add, hd₀0, map_sub, add_sub_cancel]
  rw [hc]
  exact (mem_centralOverBaseSubgroup_iff C _ sX p _).1 (add_mem hd₁ hd₀)

/-- Let `(S, δ)` be as in section 42.63 of the Stacks Project, let `X` be a scheme locally of
finite type over `S` and let `c ∈ A^p(X ⟶ S)`. Let `Y ⟶ Z` be a morphism of schemes locally of
finite type over `S` and let `c' ∈ A^q(Y ⟶ Z)`. Then `c ∘ c' = c' ∘ c`:
capping with `c` and capping with `c'` may be performed in either order, the two results being
read on `X ×_S (Y ×_Z T)` and `Y ×_Z (X ×_S T)` through the canonical comparison isomorphism. -/
@[stacks 0FC6 "the commutation c ∘ c' = c' ∘ c read on the cap operations of the two \
composites (`Stacks.Chow.BivariantCommuteOverBase`), for the bivariant classes of the Gysin \
system of invertible modules `Stacks.Chow.gysinSystemOfInvertible`"]
theorem bivariantCommuteOverBase_of_isDedekindChowBase_general (hS : IsDedekindChowBase C)
    {Y Z : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (w : Y ⟶ Z)
    [LocallyOfFiniteType w] (q : ℤ)
    (c : BivariantClass C (gysinSystemOfInvertible C) sX (𝟙 C.S) sX (Category.comp_id sX) p)
    (c' : BivariantClass C (gysinSystemOfInvertible C) (w ≫ sZ) sZ w rfl q) :
    BivariantCommuteOverBase C (gysinSystemOfInvertible C) sX sZ w p q c c' :=
  isCentralOverBase_of_isDedekindChowBase_general C sX p hS c sZ w q c'

end Dedekind

end Stacks.Chow

end
