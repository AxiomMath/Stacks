module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.VanishingUnconditional
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.BivariantClass
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekindBivariant
public import StacksFrontier.AlgebraicGeometry.Chow.GysinFundamentalClass
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.Basic
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced

/-!
# Bivariant classes towards a Dedekind base are determined by `c ∩ [S]₁`

Let `(S, δ)` be as in Stacks section 42.63, every irreducible component of `S` being of dimension
one, and let `X` be locally of finite type over `S`. A bivariant class `c ∈ A^p(X ⟶ S)` with
`c ∩ [S]₁ = 0` is zero. This is the injectivity half of Stacks 0FC5, and the proof is the
source's: by Stacks 02UC it suffices that `c ∩ [T] = 0` for every integral `T` locally of finite
type over `S`, and

* if `T` dominates an irreducible component of `S`, then `T ⟶ S` is flat of relative dimension
  `dim_δ(T) - 1` and `[T] = (T ⟶ S)^* [S]₁`;
* otherwise `T ⟶ S` factors through a closed point `s`, which is an effective Cartier divisor of
  `S`, `[T] = (T ⟶ s)^* [s] = (T ⟶ s)^* (s ⟶ S)^* [S]₁`.

In both cases `c ∩ [T]` is computed from `c ∩ [S]₁` by the flat-pullback and Gysin axioms of
Stacks 0B76.

## Main results

* `Stacks.Chow.IsDedekindChowBase.dimensionFunction_eq_one` — the generic point of an irreducible
  component of dimension one has `δ = 1`.
* `Stacks.Chow.gysinChowOfInvertible_baseFundamentalClass` — the Gysin map of a closed point of
  the base sends `[S]₁` to the fundamental class of the point.
* `Stacks.Chow.BivariantChowClass.eq_zero_of_cap_baseFundamentalChowClass_dedekind` — a bivariant
  class towards the base killing `[S]₁` is zero.

## References

* [Stacks Project, Tag 0FC5](https://stacks.math.columbia.edu/tag/0FC5)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 0AUW](https://stacks.math.columbia.edu/tag/0AUW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The dimension function of the base -/

section Base

variable {C : ChowSituation.{u}} (hC : IsDedekindChowBase C)

include hC in
/-- On a Dedekind base whose irreducible components have dimension one, the generic point of an
irreducible component is not closed, so the dimension function takes the value `1` there. -/
theorem IsDedekindChowBase.dimensionFunction_eq_one
    (hdim : ∀ Z : irreducibleComponents C.S, topologicalKrullDim (Z : Set C.S) = 1) {η : C.S}
    (hη : closure ({η} : Set C.S) ∈ irreducibleComponents C.S) : C.dimensionFunction η = 1 := by
  refine hC.2.2 η fun hcl ↦ ?_
  have h := hdim ⟨_, hη⟩
  change topologicalKrullDim (closure ({η} : Set C.S)) = 1 at h
  rw [hcl.closure_eq] at h
  have h0 := topologicalKrullDim_zero_of_discreteTopology ({η} : Set C.S)
  rw [h] at h0
  exact absurd h0 (by decide)

include hC in
/-- On a Dedekind base the dimension function takes only the values `0` and `1`. -/
theorem IsDedekindChowBase.dimensionFunction_le_one (s : C.S) : C.dimensionFunction s ≤ 1 := by
  by_cases hs : IsClosed ({s} : Set C.S)
  · rw [hC.2.1 s hs]
    exact zero_le_one
  · rw [hC.2.2 s hs]

include hC in
/-- The base of a Dedekind situation has delta-dimension at most one. -/
theorem IsDedekindChowBase.schemeDeltaDimension_base_le_one :
    schemeDeltaDimension C (𝟙 C.S ≫ 𝟙 C.S) ≤ ((1 : ℤ) : EInt) :=
  schemeDeltaDimension_le_of_forall_relativeDimension_le C (𝟙 C.S) (𝟙 C.S) fun s ↦ by
    rw [relativeDimension_id]
    exact hC.dimensionFunction_le_one s

end Base

/-! ### A closed point of the base -/

/-- A closed subscheme cut out by the vanishing ideal of a closed point is supported there. -/
private theorem support_eq_singleton_of_eq_vanishingIdeal {X : Scheme.{u}} {s : X}
    {D : X.IdealSheafData} (hs : IsClosed ({s} : Set X))
    (hD : D = Scheme.IdealSheafData.vanishingIdeal (⟨{s}, hs⟩ : Closeds X)) :
    (D.support : Set X) = {s} := by
  rw [hD, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- Every point of a closed subscheme supported at a single point maps to that point. -/
private theorem subschemeι_base_eq_of_support_eq {X : Scheme.{u}} {s : X} {D : X.IdealSheafData}
    (hD : (D.support : Set X) = {s}) (w : D.subscheme) : D.subschemeι.base w = s := by
  have := Set.mem_range_self (f := D.subschemeι.base) w
  rwa [Scheme.IdealSheafData.range_subschemeι, hD, Set.mem_singleton_iff] at this

section Point

variable {C : ChowSituation.{u}} (hC : IsDedekindChowBase C) {s : C.S}
  (hs : closure ({s} : Set C.S) ∉ irreducibleComponents C.S) (L : C.S.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible C.S.sheaf.obj C.S.ringCatSheaf.property L]
  (σ : Γ(L, ⊤))
  (hσ : Stacks.Divisors.zeroScheme C.S L σ =
    Scheme.IdealSheafData.vanishingIdeal (⟨{s}, hC.isClosed_singleton hs⟩ : Closeds C.S))

include hσ in
/-- A closed point of a Dedekind base, as a closed subscheme, has delta-dimension zero. -/
theorem schemeDeltaDimension_zeroScheme_le_zero :
    schemeDeltaDimension C ((Stacks.Divisors.zeroScheme C.S L σ).subschemeι ≫ (𝟙 C.S ≫ 𝟙 C.S)) ≤
      ((0 : ℤ) : EInt) := by
  refine schemeDeltaDimension_le_of_forall_relativeDimension_le C (𝟙 C.S ≫ 𝟙 C.S) _ fun w ↦ ?_
  have hw := subschemeι_base_eq_of_support_eq
    (support_eq_singleton_of_eq_vanishingIdeal (hC.isClosed_singleton hs) hσ) w
  rw [Category.comp_id, relativeDimension_id, hw, hC.2.1 s (hC.isClosed_singleton hs)]

include hσ in
/-- **The Gysin map of a closed point of the base on `[S]₁`.** For a closed point `s` of a
Dedekind base which is not the generic point of a component, presented as the zero scheme of a
section of an invertible module, `i^*[S]₁ = [s]₀`: the point is an effective Cartier divisor. -/
theorem gysinChowOfInvertible_baseFundamentalClass :
    gysinChowOfInvertible C (𝟙 C.S ≫ 𝟙 C.S) 0 L σ
        (fundamentalChowClass C (𝟙 C.S ≫ 𝟙 C.S) (0 + 1)) =
      fundamentalChowClass C ((Stacks.Divisors.zeroScheme C.S L σ).subschemeι ≫ (𝟙 C.S ≫ 𝟙 C.S))
        0 :=
  gysinChowOfInvertible_fundamentalChowClass C (𝟙 C.S ≫ 𝟙 C.S) 0 L σ
    (by simpa using hC.schemeDeltaDimension_base_le_one)
    (hσ ▸ hC.isEffectiveCartierDivisor_vanishingIdeal hs)

end Point

/-! ### Injectivity -/

section Injective

variable {C : ChowSituation.{u}} {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  {p : ℤ}

/-- Transport of a vanishing along an equality of degrees. -/
theorem eqMp_chowGroup_zero {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] {a b : ℤ}
    (h : a = b) : Eq.mp (congrArg (chowGroup C q) h) 0 = 0 := by
  subst h
  rfl

/-- Pushforward along an isomorphism detects vanishing. -/
theorem eq_zero_of_properChowPushforward_eq_zero_of_isIso {A B : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (u : A ⟶ B) [IsIso u]
    (hu : u ≫ sB = sA) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sA sB u hu k)
    (x : chowGroup C sA k) (h : properChowPushforward C sA sB u hu k hfac x = 0) : x = 0 := by
  have hinv : inv u ≫ sA = sB := by rw [IsIso.inv_comp_eq, hu]
  have h' := congrArg (chowPushforwardOfIso C sB sA (inv u) hinv k) h
  rw [map_zero] at h'
  change chowPushforwardOfIso C sB sA (inv u) hinv k (chowPushforwardOfIso C sA sB u hu k x) = 0
    at h'
  rw [chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_of_eq_id _ _ _ _ (IsIso.hom_inv_id u)] at h'
  exact (eq_of_heq (chowGroupCongr_heq C _ _ x)).symm.trans h'

/-- A bivariant class towards the base kills the fundamental class of a test scheme as soon as it
kills it for an equal test morphism, read in an equal degree. -/
theorem BivariantChowClass.cap_fundamentalChowClass_eq_zero_of_heq
    (c : BivariantChowClass C sX (𝟙 C.S) sX (Category.comp_id sX) p) {T : Scheme.{u}}
    {g₁ g₂ : T ⟶ C.S} [LocallyOfFiniteType g₁] [LocallyOfFiniteType g₂] (hg : g₁ = g₂)
    {k₁ k₂ j : ℤ} (hk : k₁ = k₂) (hj : k₂ - p = j)
    (h : c.cap g₂ k₂ (fundamentalChowClass C (g₂ ≫ 𝟙 C.S) k₂) ≍
      (0 : chowGroup C (pullback.fst sX g₂ ≫ sX) j)) :
    c.cap g₁ k₁ (fundamentalChowClass C (g₁ ≫ 𝟙 C.S) k₁) = 0 := by
  subst hg hk hj
  exact eq_of_heq h

/-- The cap operations of a bivariant class send zero to zero. -/
theorem BivariantChowClass.cap_zero'
    (c : BivariantChowClass C sX (𝟙 C.S) sX (Category.comp_id sX) p) {T : Scheme.{u}}
    (g : T ⟶ C.S) [LocallyOfFiniteType g] (k : ℤ) : c.cap g k 0 = 0 :=
  map_zero ((BivariantChowClass.equivBivariantClass c).cap g k)

variable (hC : IsDedekindChowBase C)
  (hdim : ∀ Z : irreducibleComponents C.S, topologicalKrullDim (Z : Set C.S) = 1)

include hC in
/-- **The geometric step of the injectivity in Stacks 0FC5, over a curve of the base.** A
bivariant class `c ∈ A^p(X ⟶ S)` with `c ∩ [S]₁ = 0` kills the fundamental class of every
integral scheme `T` locally of finite type over the base which, if it dominates an irreducible
component of the base, dominates one whose generic point has `δ = 1`. -/
theorem BivariantChowClass.cap_integral_eq_zero_of_cap_baseFundamentalChowClass_of_dimensionFunction
    (c : BivariantChowClass C sX (𝟙 C.S) sX (Category.comp_id sX) p)
    (hc : c.cap (𝟙 C.S) 1 (baseFundamentalChowClass C) = 0) {T : Scheme.{u}} (g : T ⟶ C.S)
    [LocallyOfFiniteType g] [IsIntegral T]
    (hδ : closure ({g.base (genericPoint T)} : Set C.S) ∈ irreducibleComponents C.S →
      C.dimensionFunction (g.base (genericPoint T)) = 1) (k : ℤ) :
    c.cap g k (fundamentalChowClass C (g ≫ 𝟙 C.S) k) = 0 := by
  classical
  have hzero : relativeDimension C.dimensionFunction (g ≫ 𝟙 C.S) (genericPoint T) ≠ k →
      c.cap g k (fundamentalChowClass C (g ≫ 𝟙 C.S) k) = 0 := fun h ↦ by
    rw [fundamentalChowClass, fundamentalCycle_eq_zero_of_ne C (g ≫ 𝟙 C.S)
      genericPoints_eq_singleton h, map_zero]
    exact c.cap_zero' g k
  by_cases hdom : closure ({g.base (genericPoint T)} : Set C.S) ∈ irreducibleComponents C.S
  · -- `T` dominates a component: `[T] = g^* [S]₁`
    have hflat : Flat g := hC.flat_of_mem_irreducibleComponents g hdom
    have hrel := relativeDimension_of_irreducibleSpace g
      (fun _ ↦ ⟨inferInstance, hC.ringKrullDim_stalk_le_one _⟩)
    set r := Cardinal.toNat (residueTrdeg g (genericPoint T)) with hr
    have hδT : relativeDimension C.dimensionFunction (g ≫ 𝟙 C.S) (genericPoint T) = 1 + r := by
      rw [relativeDimension_comp_eq_add_trdeg, relativeDimension_id, hδ hdom]
    by_cases hk : k = 1 + r
    swap
    · exact hzero (by rw [hδT]; exact fun h ↦ hk h.symm)
    subst hk
    have hax := c.cap_flatPullback (𝟙 C.S) g r hrel 1 (baseFundamentalChowClass C)
    rw [hc, map_zero, baseFundamentalChowClass, flatPullbackChow_fundamentalChowClass C _ _ g _ r
      hrel 1 _ hC.schemeDeltaDimension_base_le_one] at hax
    exact c.cap_fundamentalChowClass_eq_zero_of_heq (Category.comp_id g).symm rfl (by ring) hax
  · -- `T` lies over a closed point `s`: `[T] = a^* [s] = a^* i^* [S]₁`
    have hscl := hC.isClosed_singleton hdom
    obtain ⟨L, hLinv, σ, hσ, -⟩ := hC.exists_section_zeroScheme_eq hdom
    have hrange : Set.range g.base ⊆ {g.base (genericPoint T)} := by
      rintro _ ⟨t, rfl⟩
      have h1 : g.base (genericPoint T) ⤳ g.base t :=
        (genericPoint_specializes t).map g.continuous
      rw [← hscl.closure_eq]
      exact specializes_iff_mem_closure.mp h1
    have hker : (Stacks.Divisors.zeroScheme C.S L σ).subschemeι.ker ≤ g.ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι, hσ, Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
      refine Scheme.IdealSheafData.vanishingIdeal_antimono ?_
      change closure (Set.range g.base) ⊆ {g.base (genericPoint T)}
      exact closure_minimal hrange hscl
    set a := IsClosedImmersion.lift (Stacks.Divisors.zeroScheme C.S L σ).subschemeι g hker with had
    have ha : a ≫ (Stacks.Divisors.zeroScheme C.S L σ).subschemeι = g :=
      IsClosedImmersion.lift_fac _ _ _
    have hDfield := isField_stalk_of_eq_vanishingIdeal_singleton hscl _ hσ
    have haflat : Flat a := flat_of_isField_stalk a hDfield
    have halft : LocallyOfFiniteType a := by
      have : LocallyOfFiniteType (a ≫ (Stacks.Divisors.zeroScheme C.S L σ).subschemeι) := by
        rw [ha]; infer_instance
      exact locallyOfFiniteType_of_comp a (Stacks.Divisors.zeroScheme C.S L σ).subschemeι
    have harel := relativeDimension_of_irreducibleSpace a fun t ↦ by
      let _ := (hDfield (a.base t)).toField
      refine ⟨inferInstance, ?_⟩
      rw [ringKrullDim_eq_zero_of_field]
      exact zero_le_one
    set r := Cardinal.toNat (residueTrdeg a (genericPoint T)) with hr
    have hpt : (Stacks.Divisors.zeroScheme C.S L σ).subschemeι.base (a.base (genericPoint T)) =
        g.base (genericPoint T) := by
      rw [← Scheme.Hom.comp_apply, ha]
    have hδT : relativeDimension C.dimensionFunction (g ≫ 𝟙 C.S) (genericPoint T) = 0 + r := by
      rw [← ha, Category.assoc, relativeDimension_comp_eq_add_trdeg,
        relativeDimension_comp_closedImmersion, relativeDimension_id, hpt, hC.2.1 _ hscl]
    by_cases hk : k = 0 + r
    swap
    · exact hzero (by rw [hδT]; exact fun h ↦ hk h.symm)
    subst hk
    -- the Gysin axiom at the closed point
    have hgys := c.cap_gysin (𝟙 C.S) L σ 0 (fundamentalChowClass C (𝟙 C.S ≫ 𝟙 C.S) (0 + 1))
    have hc' : c.cap (𝟙 C.S) (0 + 1) (fundamentalChowClass C (𝟙 C.S ≫ 𝟙 C.S) (0 + 1)) = 0 := hc
    rw [hc', eqMp_chowGroup_zero _ (by ring), map_zero,
      gysinChowOfInvertible_baseFundamentalClass hC hdom L σ hσ] at hgys
    have hcapD := eq_zero_of_properChowPushforward_eq_zero_of_isIso _ _ _ _ _ _ _ hgys
    have hcapD' : c.cap ((Stacks.Divisors.zeroScheme C.S L σ).subschemeι ≫ 𝟙 C.S) 0
        (fundamentalChowClass C
          (((Stacks.Divisors.zeroScheme C.S L σ).subschemeι ≫ 𝟙 C.S) ≫ 𝟙 C.S) 0) = 0 := hcapD
    have hdimD : schemeDeltaDimension C
        (((Stacks.Divisors.zeroScheme C.S L σ).subschemeι ≫ 𝟙 C.S) ≫ 𝟙 C.S) ≤ ((0 : ℤ) : EInt) :=
      schemeDeltaDimension_zeroScheme_le_zero hC hdom L σ hσ
    -- the flat axiom along `a`
    have hax := c.cap_flatPullback ((Stacks.Divisors.zeroScheme C.S L σ).subschemeι ≫ 𝟙 C.S) a r
      harel 0 (fundamentalChowClass C
        (((Stacks.Divisors.zeroScheme C.S L σ).subschemeι ≫ 𝟙 C.S) ≫ 𝟙 C.S) 0)
    rw [hcapD', map_zero, flatPullbackChow_fundamentalChowClass C _ _ a _ r harel 0 _ hdimD] at hax
    exact c.cap_fundamentalChowClass_eq_zero_of_heq (by rw [← ha, Category.comp_id])
      rfl (by ring) hax

include hC hdim in
/-- **The geometric step of the injectivity in Stacks 0FC5.** A bivariant class `c ∈ A^p(X ⟶ S)`
with `c ∩ [S]₁ = 0` kills the fundamental class of every integral scheme `T` locally of finite
type over the base, in every degree. -/
theorem BivariantChowClass.cap_integral_eq_zero_of_cap_baseFundamentalChowClass
    (c : BivariantChowClass C sX (𝟙 C.S) sX (Category.comp_id sX) p)
    (hc : c.cap (𝟙 C.S) 1 (baseFundamentalChowClass C) = 0) {T : Scheme.{u}} (g : T ⟶ C.S)
    [LocallyOfFiniteType g] [IsIntegral T] (k : ℤ) :
    c.cap g k (fundamentalChowClass C (g ≫ 𝟙 C.S) k) = 0 :=
  c.cap_integral_eq_zero_of_cap_baseFundamentalChowClass_of_dimensionFunction hC hc g
    (fun hdom ↦ hC.dimensionFunction_eq_one hdim hdom) k

include hC hdim in
/-- **Stacks 0FC5, injectivity.** A bivariant class `c ∈ A^p(X ⟶ S)` towards a Dedekind base
whose irreducible components have dimension one is determined by `c ∩ [S]₁`: if `c ∩ [S]₁ = 0`
then `c = 0`. -/
theorem BivariantChowClass.eq_zero_of_cap_baseFundamentalChowClass_dedekind
    (c : BivariantChowClass C sX (𝟙 C.S) sX (Category.comp_id sX) p)
    (hc : c.cap (𝟙 C.S) 1 (baseFundamentalChowClass C) = 0) : c = 0 := by
  have h0 : BivariantChowClass.equivBivariantClass c = 0 := by
    rw [BivariantClass.eq_zero_iff_capsIntegral_canonical]
    intro T g _ _ k
    exact c.cap_integral_eq_zero_of_cap_baseFundamentalChowClass hC hdim hc g k
  exact BivariantChowClass.addEquivBivariantClass.injective
    ((BivariantChowClass.addEquivBivariantClass_apply c).trans (h0.trans (map_zero _).symm))

end Injective

/-! ### The exterior product with `[S]₁` -/

section Unit

variable {C : ChowSituation.{u}}

/-- Transporting a multiple of a fundamental cycle along an equality of degrees. -/
theorem cast_zsmul_fundamentalCycle {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q]
    {k k' : ℤ} (h : k = k') (a : ℤ) :
    (h ▸ (a • fundamentalCycle C q k) : CycleGroup C q k') = a • fundamentalCycle C q k' := by
  subst h
  rfl

/-- The class of a fundamental cycle read in an equal degree is the fundamental class. -/
theorem mk_cycleOfDegreeEq_fundamentalCycle {T : Scheme.{u}} (q : T ⟶ C.S)
    [LocallyOfFiniteType q] {k k' : ℤ} (h : k = k') :
    QuotientAddGroup.mk' (rationalEquivalences C q k')
        (cycleOfDegreeEq q h (fundamentalCycle C q k)) =
      fundamentalChowClass C q k' := by
  subst h
  rfl

/-- Multiples of fundamental classes in equal degrees are heterogeneously equal. -/
theorem zsmul_fundamentalChowClass_heq {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q]
    {k k' : ℤ} (h : k = k') (a : ℤ) :
    a • fundamentalChowClass C q k ≍ a • fundamentalChowClass C q k' := by
  subst h
  rfl

variable (hC : IsDedekindChowBase C)

include hC in
/-- A closed subscheme of a Dedekind base supported at a closed point has delta-dimension
zero. -/
theorem schemeDeltaDimension_le_zero_of_support_eq {s : C.S} (hs : IsClosed ({s} : Set C.S))
    (D : C.S.IdealSheafData) (hD : (D.support : Set C.S) = {s}) :
    schemeDeltaDimension C (D.subschemeι ≫ 𝟙 C.S) ≤ ((0 : ℤ) : EInt) := by
  refine schemeDeltaDimension_le_of_forall_relativeDimension_le C (𝟙 C.S) D.subschemeι fun w ↦ ?_
  rw [relativeDimension_id, subschemeι_base_eq_of_support_eq hD w, hC.2.1 s hs]

include hC in
/-- The base of a Dedekind Chow situation, viewed over itself, has delta-dimension at most one. -/
theorem IsDedekindChowBase.schemeDeltaDimension_id_le_one :
    schemeDeltaDimension C (𝟙 C.S) ≤ ((1 : ℤ) : EInt) := by
  simpa using hC.schemeDeltaDimension_base_le_one

variable (hdim : ∀ Z : irreducibleComponents C.S, topologicalKrullDim (Z : Set C.S) = 1)
  {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (n : ℤ) (a₀ : CycleGroup C sX n)

/-- The summand at a point `x` of the support of `α` of the exterior product `α × [S]₁`: it is
rationally equivalent to `α(x)` times the fundamental cycle of `closure {x} ×_S S`. -/
def BaseSummandData (x : X) : Prop :=
  ∃ A : CycleGroup C ((dedekindPointFibre sX (𝟙 C.S) x).subschemeι ≫
      (pullback.fst sX (𝟙 C.S) ≫ sX)) (n + 1 - 1),
    (∀ z, (properPushforward C _ (pullback.fst sX (𝟙 C.S) ≫ sX)
      (dedekindPointFibre sX (𝟙 C.S) x).subschemeι rfl (n + 1 - 1) A).1 z =
        ∑ᶠ y : C.S, exteriorProductDedekindTerm C sX (𝟙 C.S) n 1 a₀
          (fundamentalCycle C (𝟙 C.S) 1) z (x, y)) ∧
    A - a₀.1 x • fundamentalCycle C _ (n + 1 - 1) ∈ rationalEquivalences C _ (n + 1 - 1)

include hC in
/-- At a dominating point lying over a point where `δ = 1` the summand is exactly
`α(x) [closure {x} ×_S S]`: the flat pullback of the fundamental cycle of the base is the
fundamental cycle. -/
theorem baseSummandData_of_dominates (x : X) (hx : a₀.1 x ≠ 0)
    (hdom : DominatesBaseComponent C sX x) (hδ : C.dimensionFunction (sX.base x) = 1) :
    BaseSummandData sX n a₀ x := by
  classical
  obtain ⟨hflat, r, hr, hrel⟩ := exists_relativeDimension_dedekindPointFibre C sX (𝟙 C.S) hC x hdom
  have hn := (mem_cyclesOfDimension_iff_forall_point C sX n a₀.1).1 a₀.2 x hx
  have hdeg : 1 + (r : ℤ) = n + 1 - 1 := by omega
  have hbase : ((dedekindPointFibre sX (𝟙 C.S) x).subschemeι ≫ pullback.snd sX (𝟙 C.S)) ≫ 𝟙 C.S =
      (dedekindPointFibre sX (𝟙 C.S) x).subschemeι ≫ (pullback.fst sX (𝟙 C.S) ≫ sX) := by
    rw [Category.assoc, ← pullback.condition]
  refine ⟨hdeg ▸ flatPullback C _ (𝟙 C.S) _ hbase r hr 1
      (a₀.1 x • fundamentalCycle C (𝟙 C.S) 1),
    properPushforward_flatPullback_of_dominates C sX (𝟙 C.S) n 1 a₀ _ x hdom r hr hdeg _
      (val_cycleGroup_cast C _ hdeg _), ?_⟩
  rw [map_zsmul, flatPullback_fundamentalCycle C _ (𝟙 C.S) _ hbase r hr 1
    hC.schemeDeltaDimension_id_le_one, cast_zsmul_fundamentalCycle, sub_self]
  exact zero_mem _

include hC in
/-- At a point over a closed point `s` the summand is rationally equivalent to
`α(x) [closure {x} ×_S S]`: the Gysin map of `s` sends `[S]₁` to `[s]₀`, whose flat pullback is
the fundamental class. -/
theorem baseSummandData_of_not_dominates (x : X) (hx : a₀.1 x ≠ 0)
    (hnd : ¬ DominatesBaseComponent C sX x) : BaseSummandData sX n a₀ x := by
  classical
  have hs : closure ({sX.base x} : Set C.S) ∉ irreducibleComponents C.S := hnd
  have hscl := hC.isClosed_singleton hs
  obtain ⟨L, hLinv, σ, hσ, htriv⟩ := hC.exists_section_zeroScheme_eq hs
  have htrivY := Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections (𝟙 C.S) L σ
    htriv
  have hDY := Stacks.Divisors.zeroScheme_pullback (𝟙 C.S) L σ
  obtain ⟨w, hwlft, hwflat, r, hw, hwrel, hrn⟩ :=
    exists_flat_dedekindPointFibre_fibre C sX (𝟙 C.S) n hC x hnd L σ hσ a₀ hx _ hDY
  have hdeg : 1 - 1 + (r : ℤ) = n + 1 - 1 := by omega
  have h11 : (1 : ℤ) = 1 - 1 + 1 := by ring
  have hwbase : w ≫ ((Stacks.Divisors.zeroScheme C.S ((Scheme.Modules.pullback (𝟙 C.S)).obj L)
      (AlgebraicGeometry.pullbackGlobalSections (𝟙 C.S) L σ)).subschemeι ≫ 𝟙 C.S) =
      (dedekindPointFibre sX (𝟙 C.S) x).subschemeι ≫ (pullback.fst sX (𝟙 C.S) ≫ sX) := by
    rw [← Category.assoc, hw, Category.assoc, ← pullback.condition]
  refine ⟨cycleOfDegreeEq _ hdeg (flatPullback C _ _ w hwbase r hwrel (1 - 1)
      (a₀.1 x • gysinCycleMap C (𝟙 C.S) (1 - 1) _ _ htrivY
        (cycleOfDegreeEq (𝟙 C.S) h11 (fundamentalCycle C (𝟙 C.S) 1)))),
    properPushforward_flatPullback_gysin_of_not_dominates C sX (𝟙 C.S) n 1 hC x hnd L σ hσ a₀
      (fundamentalCycle C (𝟙 C.S) 1) _ _ htrivY hDY w hw r hwrel hdeg _ rfl _ rfl, ?_⟩
  -- the support of the fibre over `s`
  have hDYsupp := support_eq_singleton_of_eq_vanishingIdeal hscl
    (hDY.trans ((Scheme.IdealSheafData.comap_id _).trans hσ))
  have hcart : Stacks.Divisors.IsEffectiveCartierDivisor
      (Stacks.Divisors.zeroScheme C.S ((Scheme.Modules.pullback (𝟙 C.S)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (𝟙 C.S) L σ)) := by
    rw [hDY, Scheme.IdealSheafData.comap_id, hσ]
    exact hC.isEffectiveCartierDivisor_vanishingIdeal hs
  have hgys := gysinChowOfInvertible_fundamentalChowClass C (𝟙 C.S) (1 - 1)
    ((Scheme.Modules.pullback (𝟙 C.S)).obj L) (AlgebraicGeometry.pullbackGlobalSections (𝟙 C.S) L σ)
    (by rw [← h11]; exact hC.schemeDeltaDimension_id_le_one) hcart
  have hfl := flatPullbackChow_fundamentalChowClass C _ _ w hwbase r hwrel (1 - 1)
    (flatPullbackDescends C _ _ _ _ _ _ _)
    (by rw [show (1 : ℤ) - 1 = 0 by ring]
        exact schemeDeltaDimension_le_zero_of_support_eq hC hscl _ hDYsupp)
  refine (QuotientAddGroup.eq_zero_iff _).1 ?_
  rw [QuotientAddGroup.mk_sub, sub_eq_zero]
  change QuotientAddGroup.mk' (rationalEquivalences C _ (n + 1 - 1)) _ =
    QuotientAddGroup.mk' (rationalEquivalences C _ (n + 1 - 1)) _
  apply eq_of_heq
  refine (mk_heq_of_val_eq _ hdeg.symm _ _ rfl).trans ?_
  have hmk : QuotientAddGroup.mk' (rationalEquivalences C
      ((Stacks.Divisors.zeroScheme C.S ((Scheme.Modules.pullback (𝟙 C.S)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (𝟙 C.S) L σ)).subschemeι ≫ 𝟙 C.S) (1 - 1))
      (gysinCycleMap C (𝟙 C.S) (1 - 1) _ _ htrivY
        (cycleOfDegreeEq (𝟙 C.S) h11 (fundamentalCycle C (𝟙 C.S) 1))) =
      fundamentalChowClass C ((Stacks.Divisors.zeroScheme C.S
        ((Scheme.Modules.pullback (𝟙 C.S)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (𝟙 C.S) L σ)).subschemeι ≫ 𝟙 C.S) (1 - 1) := by
    refine ((mk_gysinCycleMap C _ _ _ _ htrivY _).trans
      (gysinChowOfInvertible_mk C _ _ _ _ _).symm).trans ?_
    rw [mk_cycleOfDegreeEq_fundamentalCycle, hgys]
  rw [← flatPullbackChow_mk C _ _ w hwbase r hwrel (1 - 1) (flatPullbackDescends C _ _ _ _ _ _ _),
    map_zsmul, map_zsmul, hmk, hfl, map_zsmul]
  exact zsmul_fundamentalChowClass_heq _ hdeg _

include hC in
/-- **The exterior product with `[S]₁` is the identity on cycles lying over the curves of the
base.** Over a Dedekind base, let `α` be an `n`-cycle on `X` whose components dominating an
irreducible component of the base lie over points where `δ = 1`. Then the exterior product
`α × [S]₁`, pushed forward along `X ×_S S ≅ X`, is rationally equivalent to `α`. -/
theorem mk_properPushforward_exteriorProductDedekindCycles_fundamentalCycle_of_dimensionFunction
    (hδ : ∀ x, a₀.1 x ≠ 0 → DominatesBaseComponent C sX x → C.dimensionFunction (sX.base x) = 1) :
    QuotientAddGroup.mk' (rationalEquivalences C sX (n + 1 - 1))
        (properPushforward C (pullback.fst sX (𝟙 C.S) ≫ sX) sX (pullback.fst sX (𝟙 C.S)) rfl
          (n + 1 - 1)
          (exteriorProductDedekindCycles C sX (𝟙 C.S) n 1 a₀ (fundamentalCycle C (𝟙 C.S) 1))) =
      QuotientAddGroup.mk' (rationalEquivalences C sX (n + 1 - 1))
        (cycleOfDegreeEq sX (by ring) a₀) := by
  classical
  have hsum : ∀ x : a₀.1.support, BaseSummandData sX n a₀ x.1 := fun x ↦ by
    by_cases hdom : DominatesBaseComponent C sX x.1
    · exact baseSummandData_of_dominates hC sX n a₀ x.1 x.2 hdom (hδ x.1 x.2 hdom)
    · exact baseSummandData_of_not_dominates hC sX n a₀ x.1 x.2 hdom
  choose A hA1 hA2 using hsum
  have hfinK : LocallyFinite fun x : a₀.1.support ↦
      Set.range (dedekindPointFibre sX (𝟙 C.S) x.1).subschemeι :=
    (locallyFinite_dedekindPointFibre sX (𝟙 C.S) a₀.1).subset fun x ↦ by
      rw [Scheme.IdealSheafData.range_subschemeι]
  have hfinX : LocallyFinite fun x : a₀.1.support ↦
      Set.range ((dedekindPointFibre sX (𝟙 C.S) x.1).subschemeι ≫ pullback.fst sX (𝟙 C.S)) := by
    refine (locallyFinite_support_integralComponentAt a₀).subset fun x ↦ ?_
    rintro _ ⟨w, rfl⟩
    have hw := Set.mem_range_self (f := (dedekindPointFibre sX (𝟙 C.S) x.1).subschemeι.base) w
    rw [Scheme.IdealSheafData.range_subschemeι] at hw
    have hw' : (pullback.fst sX (𝟙 C.S)).base
        ((dedekindPointFibre sX (𝟙 C.S) x.1).subschemeι.base w) ∈ closure ({x.1} : Set X) := by
      simpa [Scheme.IdealSheafData.support_comap,
        Scheme.IdealSheafData.coe_support_vanishingIdeal] using hw
    rw [coe_support_integralComponentAt, Scheme.Hom.comp_apply]
    exact hw'
  have hE := exteriorProductDedekindCycles_apply_eq_finsum C sX (𝟙 C.S) n 1 a₀ _ A hA1
  -- the pushforward of a summand of `α(x) [closure {x} ×_S S]` is `α(x) [closure {x}]`
  have hprime : ∀ (x : a₀.1.support) (z : X),
      (properPushforward C _ sX ((dedekindPointFibre sX (𝟙 C.S) x.1).subschemeι ≫
          pullback.fst sX (𝟙 C.S)) (Category.assoc _ _ _) (n + 1 - 1)
        (a₀.1 x • fundamentalCycle C ((dedekindPointFibre sX (𝟙 C.S) x.1).subschemeι ≫
          (pullback.fst sX (𝟙 C.S) ≫ sX)) (n + 1 - 1))).1 z =
        a₀.1 x * (cycleAssociatedToClosedSubscheme C sX (integralComponentAt x.1).subschemeι n).1 z
      := by
    intro x z
    let I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x.1} : Set X))
    have hcomp : ((pointClosureFibreIso sX (𝟙 C.S) x.1) ≪≫
        asIso (pullback.fst (I.subschemeι ≫ sX) (𝟙 C.S))).hom ≫ I.subschemeι =
        (dedekindPointFibre sX (𝟙 C.S) x.1).subschemeι ≫ pullback.fst sX (𝟙 C.S) := by
      rw [Iso.trans_hom, asIso_hom, Category.assoc]
      exact pointClosureFibreIso_hom_fst sX (𝟙 C.S) x.1
    have hpush := map_zsmul (properPushforwardHom C _ sX ((dedekindPointFibre sX (𝟙 C.S)
      x.1).subschemeι ≫ pullback.fst sX (𝟙 C.S)) (Category.assoc _ _ _) (n + 1 - 1)) (a₀.1 x)
      (fundamentalCycle C ((dedekindPointFibre sX (𝟙 C.S) x.1).subschemeι ≫
          (pullback.fst sX (𝟙 C.S) ≫ sX)) (n + 1 - 1))
    change (properPushforwardHom C _ sX ((dedekindPointFibre sX (𝟙 C.S) x.1).subschemeι ≫
      pullback.fst sX (𝟙 C.S)) (Category.assoc _ _ _) (n + 1 - 1) _).1 z = _
    rw [hpush]
    change a₀.1 x * (properPushforward C _ sX ((dedekindPointFibre sX (𝟙 C.S) x.1).subschemeι ≫
      pullback.fst sX (𝟙 C.S)) (Category.assoc _ _ _) (n + 1 - 1) _).1 z = _
    rw [properPushforward_fundamentalCycle_of_isClosedImmersion,
      cycleAssociatedToClosedSubscheme_eq_of_iso C sX _ _ _ hcomp, show n + 1 - 1 = n by ring]
    rfl
  -- conclusion by Stacks 02RZ
  rw [← sub_eq_zero, ← map_sub]
  refine (QuotientAddGroup.eq_zero_iff _).2 ?_
  refine mem_rationalEquivalences_of_finsum_isClosedImmersion sX (n + 1 - 1)
    (fun x : a₀.1.support ↦ (dedekindPointFibre sX (𝟙 C.S) x.1).subschemeι ≫
      pullback.fst sX (𝟙 C.S)) hfinX
    (fun x ↦ (dedekindPointFibre sX (𝟙 C.S) x.1).subschemeι ≫ (pullback.fst sX (𝟙 C.S) ≫ sX))
    (fun _ ↦ Category.assoc _ _ _)
    (fun x ↦ A x - a₀.1 x • fundamentalCycle C _ (n + 1 - 1)) hA2 _ (fun z ↦ ?_)
  have hfinz : ∀ e : ∀ x : a₀.1.support, CycleGroup C
      ((dedekindPointFibre sX (𝟙 C.S) x.1).subschemeι ≫ (pullback.fst sX (𝟙 C.S) ≫ sX))
        (n + 1 - 1),
      (Function.support fun x : a₀.1.support ↦ (properPushforward C _ sX
        ((dedekindPointFibre sX (𝟙 C.S) x.1).subschemeι ≫ pullback.fst sX (𝟙 C.S))
        (Category.assoc _ _ _) (n + 1 - 1) (e x)).1 z).Finite := fun e ↦
    (hfinX.point_finite z).subset fun x hx ↦
      support_properPushforward_subset C _ _ _ _ (n + 1 - 1) (e x) hx
  have hmap := algebraicCycle_map_finsum_apply (pullback.fst sX (𝟙 C.S))
    (relativeDimension C.dimensionFunction (pullback.fst sX (𝟙 C.S) ≫ sX))
    (relativeDimension C.dimensionFunction sX)
    (fun x : a₀.1.support ↦ Set.range (dedekindPointFibre sX (𝟙 C.S) x.1).subschemeι) hfinK
    (fun x ↦ (properPushforward C _ _ (dedekindPointFibre sX (𝟙 C.S) x.1).subschemeι rfl
      (n + 1 - 1) (A x)).1)
    (fun x ↦ support_properPushforward_subset C _ _ _ _ _ _)
    (exteriorProductDedekindCycles C sX (𝟙 C.S) n 1 a₀ (fundamentalCycle C (𝟙 C.S) 1)).1 hE z
  change (properPushforward C (pullback.fst sX (𝟙 C.S) ≫ sX) sX (pullback.fst sX (𝟙 C.S)) rfl
    (n + 1 - 1) (exteriorProductDedekindCycles C sX (𝟙 C.S) n 1 a₀
      (fundamentalCycle C (𝟙 C.S) 1))).1 z - a₀.1 z = _
  change (properPushforward C (pullback.fst sX (𝟙 C.S) ≫ sX) sX (pullback.fst sX (𝟙 C.S)) rfl
    (n + 1 - 1) (exteriorProductDedekindCycles C sX (𝟙 C.S) n 1 a₀
      (fundamentalCycle C (𝟙 C.S) 1))).1 z = _ at hmap
  rw [hmap, cycle_eq_finsum_primeCycles a₀ z]
  have hP : ∀ x : a₀.1.support, AlgebraicCycle.map (pullback.fst sX (𝟙 C.S))
      (relativeDimension C.dimensionFunction (pullback.fst sX (𝟙 C.S) ≫ sX))
      (relativeDimension C.dimensionFunction sX)
      (properPushforward C _ _ (dedekindPointFibre sX (𝟙 C.S) x.1).subschemeι rfl
        (n + 1 - 1) (A x)).1 z =
      (properPushforward C _ sX ((dedekindPointFibre sX (𝟙 C.S) x.1).subschemeι ≫
          pullback.fst sX (𝟙 C.S)) (Category.assoc _ _ _) (n + 1 - 1) (A x)).1 z := by
    intro x
    change (properPushforward C (pullback.fst sX (𝟙 C.S) ≫ sX) sX (pullback.fst sX (𝟙 C.S)) rfl
      (n + 1 - 1) (properPushforward C _ _ (dedekindPointFibre sX (𝟙 C.S) x.1).subschemeι rfl
        (n + 1 - 1) (A x))).1 z = _
    rw [properPushforward_properPushforward]
  simp_rw [hP]
  rw [show (∑ᶠ x : {x // a₀.1 x ≠ 0}, a₀.1 x.1 *
      (cycleAssociatedToClosedSubscheme C sX (integralComponentAt x.1).subschemeι n).1 z) =
      ∑ᶠ x : a₀.1.support, (properPushforward C _ sX
        ((dedekindPointFibre sX (𝟙 C.S) x.1).subschemeι ≫ pullback.fst sX (𝟙 C.S))
        (Category.assoc _ _ _) (n + 1 - 1)
        (a₀.1 x • fundamentalCycle C ((dedekindPointFibre sX (𝟙 C.S) x.1).subschemeι ≫
          (pullback.fst sX (𝟙 C.S) ≫ sX)) (n + 1 - 1))).1 z from
      finsum_congr fun x ↦ (hprime x z).symm,
    ← finsum_sub_distrib (hfinz _) (hfinz _)]
  refine finsum_congr fun x ↦ ?_
  rw [properPushforward_sub]
  rfl

include hC hdim in
/-- **The exterior product with `[S]₁` is the identity.** Over a Dedekind base whose irreducible
components have dimension one, the exterior product `α × [S]₁` of an `n`-cycle on `X` with the
fundamental cycle of the base, pushed forward along `X ×_S S ≅ X`, is rationally equivalent to
`α`. -/
theorem mk_properPushforward_exteriorProductDedekindCycles_fundamentalCycle :
    QuotientAddGroup.mk' (rationalEquivalences C sX (n + 1 - 1))
        (properPushforward C (pullback.fst sX (𝟙 C.S) ≫ sX) sX (pullback.fst sX (𝟙 C.S)) rfl
          (n + 1 - 1)
          (exteriorProductDedekindCycles C sX (𝟙 C.S) n 1 a₀ (fundamentalCycle C (𝟙 C.S) 1))) =
      QuotientAddGroup.mk' (rationalEquivalences C sX (n + 1 - 1))
        (cycleOfDegreeEq sX (by ring) a₀) :=
  mk_properPushforward_exteriorProductDedekindCycles_fundamentalCycle_of_dimensionFunction hC sX n
    a₀ fun _ _ hdom ↦ hC.dimensionFunction_eq_one hdim hdom

end Unit

end Stacks.Chow

end
