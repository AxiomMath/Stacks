module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.CommuteComposite
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.PointClasses

/-!
# Stacks 0FC6 over every Dedekind base

Let `(S, δ)` be as in Stacks section 42.63: locally the spectrum of a Dedekind domain, with
`δ = 0` at the closed points and `δ = 1` elsewhere. Mathlib's Dedekind domains include fields, so
`S` may have zero-dimensional irreducible components; `S` is normal, hence the disjoint union of
the open and closed union `S₀` of those (spectra of fields, with `δ = 0`) and of the curves. Let
`X` be locally of finite type over `S`, `c ∈ A^p(X ⟶ S)`, `Y ⟶ Z` a morphism of schemes locally of
finite type over `S` and `c' ∈ A^q(Y ⟶ Z)`. **Stacks 0FC6**: `c ∘ c' = c' ∘ c` in
`A^{p+q}(X ×_S Y ⟶ Z)`.

## The proof

The source: `c` is a combination of proper pushforward, integral multiples over connected
components, flat pullback and Gysin maps, with which `c'` commutes. Here `c` is decomposed as

  `c = c_α + d`,

where `c_α` is the class of Stacks 0FC5 for `α = c ∩ [S]₁`, which commutes with `c'` by Stacks
0FC7 (`Stacks.Chow.bivariantCommute_dedekindExteriorClass`), and
`d = (g₊)_* ∘ (W₊ ⟶ S)^* - (g₋)_* ∘ (W₋ ⟶ S)^*` is built over `S₀` as in the proof of Stacks 0FBX
from the class `c ∩ [S₀]₀`, a combination of proper pushforwards of flat pullbacks, which commutes
with `c'` by the axioms of Stacks 0B76 (`Stacks.Chow.bivariantCommute_properFlatPullbackClass`).
The equality `c = c_α + d` is checked by Stacks 02UC on integral test schemes `T`: such a `T` lies
over the curves or over `S₀`. Over the curves `c - c_α` kills `[T]` because it kills `[S]₁`
(Stacks 0FC5) and `d` vanishes; over `S₀` the difference `c - c_α - d` kills `[T]` because it
kills `[S₀]₀`.

## Main results

* `Stacks.Chow.exists_eq_dedekindExteriorClass_add` — the decomposition `c = c_α + d`.
* `Stacks.Chow.bivariantCommute_bivariantToBase_dedekind_of_isDedekindChowBase` — Stacks 0FC6 in
  the form of Stacks 0FA2.
* `Stacks.Chow.BivariantChowClass.comp_comm_of_isDedekindChowBase` — **Stacks 0FC6**.

## References

* [Stacks Project, Tag 0FC6](https://stacks.math.columbia.edu/tag/0FC6)
* [Stacks Project, Tag 0FC5](https://stacks.math.columbia.edu/tag/0FC5)
* [Stacks Project, Tag 0FC7](https://stacks.math.columbia.edu/tag/0FC7)
* [Stacks Project, Tag 0FBX](https://stacks.math.columbia.edu/tag/0FBX)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Two small facts -/

section Facts

variable {C : ChowSituation.{u}}

/-- Points lying over `S₀` have non-negative relative dimension. -/
theorem relativeDimension_nonneg_of_mem_clopenPoints (hC : IsDedekindChowBase C)
    {A : Scheme.{u}} (q : A ⟶ C.S) [LocallyOfFiniteType q] (x : A)
    (hx : q.base x ∈ clopenPoints C) : 0 ≤ relativeDimension C.dimensionFunction q x := by
  have h := relativeDimension_comp_eq_add_trdeg C.dimensionFunction (𝟙 C.S) q x
  rw [Category.comp_id, relativeDimension_id, hC.dimensionFunction_eq_zero_of_mem_clopenPoints hx,
    zero_add] at h
  rw [h]
  positivity

/-- Pushforward of a fundamental cycle, read with two equal structure morphisms. -/
theorem properPushforward_fundamentalCycle_congr {W P : Scheme.{u}} (sP : P ⟶ C.S)
    [LocallyOfFiniteType sP] (h : W ⟶ P) [IsProper h] {s s' : W ⟶ C.S} [LocallyOfFiniteType s]
    [LocallyOfFiniteType s'] (hs : s = s') (hw : h ≫ sP = s) (hw' : h ≫ sP = s') (n : ℤ) :
    properPushforward C s sP h hw n (fundamentalCycle C s n) =
      properPushforward C s' sP h hw' n (fundamentalCycle C s' n) := by
  subst hs
  rfl

end Facts

/-! ### The decomposition `c = c_α + d` -/

section Decomposition

variable {C : ChowSituation.{u}} (hC : IsDedekindChowBase C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (p : ℤ)

/-- The property of a class `d ∈ A^p(X ⟶ S)` of commuting, in the sense of Stacks 0FA2, with every
bivariant class `c' ∈ A^q(Y ⟶ Z)` for every morphism `Y ⟶ Z` of schemes locally of finite type
over the base. -/
def CommutesWithBivariantClasses (d : BivariantChowClass C sX (𝟙 C.S) sX (Category.comp_id sX) p) :
    Prop :=
  ∀ ⦃Y Z : Scheme.{u}⦄ (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : Y ⟶ Z)
    [LocallyOfFiniteType f] (q : ℤ)
    (c' : BivariantClass C (gysinSystemOfInvertible C) (f ≫ sZ) sZ f rfl q),
    BivariantCommute C (gysinSystemOfInvertible C) sZ (pullback.snd sX sZ) f p q
      (bivariantToBaseRestrictionHom C (gysinSystemOfInvertible C) sX sZ p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (BivariantChowClass.equivBivariantClass d)) c'

include hC in
/-- **The part of `c` over the zero-dimensional components.** For `c ∈ A^p(X ⟶ S)` there is a class
`d ∈ A^p(X ⟶ S)` commuting with every bivariant class, with `d ∩ [S₀]₀ = c ∩ [S₀]₀`, and
vanishing on every test scheme lying over the curves of the base. It is
`(g₊)_* ∘ (W₊ ⟶ S)^* - (g₋)_* ∘ (W₋ ⟶ S)^*` for the positive and negative parts
`(g_±)_*[W_±]` of a cycle representing `c ∩ [S₀]₀`. -/
theorem exists_pointPart (c : BivariantChowClass C sX (𝟙 C.S) sX (Category.comp_id sX) p) :
    ∃ d : BivariantChowClass C sX (𝟙 C.S) sX (Category.comp_id sX) p,
      CommutesWithBivariantClasses sX p d ∧
      d.cap (clopenPoints C).ι 0 (fundamentalChowClass C ((clopenPoints C).ι ≫ 𝟙 C.S) 0) =
        c.cap (clopenPoints C).ι 0 (fundamentalChowClass C ((clopenPoints C).ι ≫ 𝟙 C.S) 0) ∧
      ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ C.S) [LocallyOfFiniteType g],
        (∀ t : T, g.base t ∉ clopenPoints C) → ∀ (k : ℤ) (β : chowGroup C (g ≫ 𝟙 C.S) k),
          d.cap g k β = 0 := by
  classical
  -- the scheme `X ×_S S₀` lies over `S₀`
  have hP : ∀ x : (pullback sX (clopenPoints C).ι : Scheme.{u}),
      (pullback.fst sX (clopenPoints C).ι ≫ sX).base x ∈ clopenPoints C := fun x ↦ by
    rw [pullback.condition, Scheme.Hom.comp_apply]
    exact ι_mem_clopenPoints _
  by_cases hp : 0 ≤ -p
  swap
  · -- in positive degree the class `c ∩ [S₀]₀` vanishes
    refine ⟨0, fun Y Z sZ _ f _ q c' ↦ ?_, ?_, fun T g _ _ k β ↦ ?_⟩
    · rw [← BivariantChowClass.addEquivBivariantClass_apply, map_zero, map_zero]
      exact bivariantCommute_zero_left C _ sZ _ f p q c'
    · have := subsingleton_chowGroup_of_forall_relativeDimension_ne C
        (pullback.fst sX (clopenPoints C).ι ≫ sX) (0 - p) fun x hx ↦ by
          have := relativeDimension_nonneg_of_mem_clopenPoints hC _ x (hP x)
          omega
      exact Subsingleton.elim _ _
    · rw [BivariantChowClass.zero_cap]
      rfl
  obtain ⟨r, hr⟩ := Int.eq_ofNat_of_zero_le hp
  obtain rfl : p = -(r : ℤ) := by omega
  have := hC.isClosedImmersion_clopenPoints_ι
  obtain ⟨b, hb⟩ := QuotientAddGroup.mk'_surjective
    (rationalEquivalences C (pullback.fst sX (clopenPoints C).ι ≫ sX) (0 - -(r : ℤ)))
    (c.cap (clopenPoints C).ι 0 (fundamentalChowClass C ((clopenPoints C).ι ≫ 𝟙 C.S) 0))
  -- the positive and negative parts of `b`
  have hmem : ∀ e' : AlgebraicCycle (pullback sX (clopenPoints C).ι : Scheme.{u}) ℤ,
      (∀ x, e' x ≠ 0 → b.1 x ≠ 0) →
        e' ∈ cyclesOfDimension C (pullback.fst sX (clopenPoints C).ι ≫ sX) (0 - -(r : ℤ)) :=
    fun e' he' ↦ (mem_cyclesOfDimension_iff_forall_point C _ _ e').2 fun x hx ↦
      (mem_cyclesOfDimension_iff_forall_point C _ _ b.1).1 b.2 x (he' x hx)
  let bp : CycleGroup C (pullback.fst sX (clopenPoints C).ι ≫ sX) (0 - -(r : ℤ)) :=
    ⟨b.1⁺, hmem _ fun x hx h ↦ hx (by
      rw [Function.locallyFinsuppWithin.posPart_apply, h, posPart_zero])⟩
  let bn : CycleGroup C (pullback.fst sX (clopenPoints C).ι ≫ sX) (0 - -(r : ℤ)) :=
    ⟨b.1⁻, hmem _ fun x hx h ↦ hx (by
      rw [Function.locallyFinsuppWithin.negPart_apply, h, negPart_zero])⟩
  have hbpn : b = bp - bn := by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
    show b.1 x = (b.1 x)⁺ - (b.1 x)⁻
    exact (posPart_sub_negPart (b.1 x)).symm
  -- each part is a pushforward of a fundamental cycle of a scheme flat over the base
  have hpart : ∀ b' : CycleGroup C (pullback.fst sX (clopenPoints C).ι ≫ sX) (0 - -(r : ℤ)),
      (∀ x, 0 ≤ b'.1 x) →
      ∃ d' : BivariantChowClass C sX (𝟙 C.S) sX (Category.comp_id sX) (-(r : ℤ)),
        CommutesWithBivariantClasses sX (-(r : ℤ)) d' ∧
        d'.cap (clopenPoints C).ι 0 (fundamentalChowClass C ((clopenPoints C).ι ≫ 𝟙 C.S) 0) =
          QuotientAddGroup.mk' (rationalEquivalences C _ (0 - -(r : ℤ))) b' ∧
        ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ C.S) [LocallyOfFiniteType g],
          (∀ t : T, g.base t ∉ clopenPoints C) → ∀ (k : ℤ) (β : chowGroup C (g ≫ 𝟙 C.S) k),
            d'.cap g k β = 0 := by
    intro b' hb'
    obtain ⟨W, h, hhp, hlft, hflat, hrel, hpush⟩ :=
      exists_properPushforward_fundamentalCycle_eq_of_mem_clopenPoints hC
        (pullback.fst sX (clopenPoints C).ι ≫ sX) hP (0 - -(r : ℤ)) r (by ring) b' hb'
    have hassoc : (h ≫ pullback.fst sX (clopenPoints C).ι) ≫ sX =
        h ≫ pullback.fst sX (clopenPoints C).ι ≫ sX := Category.assoc _ _ _
    have : LocallyOfFiniteType ((h ≫ pullback.fst sX (clopenPoints C).ι) ≫ sX) := by
      rwa [hassoc]
    have : Flat ((h ≫ pullback.fst sX (clopenPoints C).ι) ≫ sX) := by rwa [hassoc]
    have hrel' : AlgebraicGeometry.RelativeDimension
        ((h ≫ pullback.fst sX (clopenPoints C).ι) ≫ sX) r :=
      AlgebraicGeometry.RelativeDimension.congr hassoc.symm hrel
    have : IsProper (h ≫ pullback.fst sX (clopenPoints C).ι) := inferInstance
    refine ⟨BivariantChowClass.equivBivariantClass.symm
      (properFlatPullbackClass C sX (h ≫ pullback.fst sX (clopenPoints C).ι) r hrel'),
      fun Y Z sZ _ f _ q c' ↦ ?_, ?_, fun T g _ hg k β ↦ ?_⟩
    · rw [Equiv.apply_symm_apply]
      exact bivariantCommute_properFlatPullbackClass C sX _ r hrel' sZ f q c'
    · rw [BivariantChowClass.equivBivariantClass_symm_cap,
        properFlatPullbackClass_cap_fundamentalChowClass hC sX h r hrel', ← hpush,
        properPushforward_fundamentalCycle_congr _ h hassoc]
    · rw [BivariantChowClass.equivBivariantClass_symm_cap]
      refine properFlatPullbackClass_cap_eq_zero C sX _ r hrel' g
        ⟨fun z ↦ hg ((pullback.snd _ g).base z) ?_⟩ k β
      have hz := congrArg (fun φ ↦ φ.base z)
        (pullback.condition (f := (h ≫ pullback.fst sX (clopenPoints C).ι) ≫ sX) (g := g))
      simp only [Scheme.Hom.comp_apply] at hz
      rw [← hz]
      simpa only [Scheme.Hom.comp_apply] using hP (h.base ((pullback.fst _ g).base z))
  obtain ⟨dp, hdp, hdp0, hdp1⟩ := hpart bp fun x ↦ posPart_nonneg (b.1 x)
  obtain ⟨dn, hdn, hdn0, hdn1⟩ := hpart bn fun x ↦ negPart_nonneg (b.1 x)
  have hcap : ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ C.S) [LocallyOfFiniteType g] (k : ℤ)
      (β : chowGroup C (g ≫ 𝟙 C.S) k), (dp - dn).cap g k β = dp.cap g k β - dn.cap g k β :=
    fun _ g _ k β ↦ by rw [BivariantChowClass.sub_cap]; rfl
  refine ⟨dp - dn, fun Y Z sZ _ f _ q c' ↦ ?_, ?_, fun T g _ hg k β ↦ ?_⟩
  · rw [← BivariantChowClass.addEquivBivariantClass_apply, map_sub, map_sub, sub_eq_add_neg]
    exact bivariantCommute_add_left C _ sZ _ f _ q c' (hdp sZ f q c')
      (bivariantCommute_neg_left C _ sZ _ f _ q c' (hdn sZ f q c'))
  · rw [hcap, hdp0, hdn0, ← map_sub, ← hbpn, hb]
  · rw [hcap, hdp1 g hg k β, hdn1 g hg k β, sub_zero]

include hC in
/-- **The decomposition `c = c_α + d`.** Over a Dedekind base, every `c ∈ A^p(X ⟶ S)` is the sum of
the class `c_α` of Stacks 0FC5 for `α = c ∩ [S]₁` and of a class `d` commuting with every
bivariant class. By Stacks 02UC it suffices to compare caps on integral test schemes `T`. If `T`
lies over the curves, `c - c_α` kills `[T]` because it kills `[S]₁`, and `d` vanishes there. If
`T` lies over `S₀`, then `c - c_α - d` kills `[T]` because it kills `[S₀]₀`: `c_α` vanishes over
`S₀`, `α` being represented by a cycle over the curves, and `d ∩ [S₀]₀ = c ∩ [S₀]₀`. -/
theorem exists_eq_dedekindExteriorClass_add
    (c : BivariantChowClass C sX (𝟙 C.S) sX (Category.comp_id sX) p) :
    ∃ d : BivariantChowClass C sX (𝟙 C.S) sX (Category.comp_id sX) p,
      CommutesWithBivariantClasses sX p d ∧
      c = dedekindExteriorClass hC sX p (bivariantChowClassCapBaseFundamentalClass sX p c) + d := by
  obtain ⟨d, hd, hd0, hd1⟩ := exists_pointPart hC sX p c
  refine ⟨d, hd, ?_⟩
  obtain ⟨a, ha, hsupp⟩ := exists_mk_eq_bivariantChowClassCapBaseFundamentalClass hC sX p c
  have hα := cap_baseFundamentalChowClass_sub_dedekindExteriorClass hC sX p c
  rw [← sub_eq_zero, sub_add_eq_sub_sub]
  have h0 : BivariantChowClass.equivBivariantClass
      (c - dedekindExteriorClass hC sX p (bivariantChowClassCapBaseFundamentalClass sX p c) - d) =
        0 := by
    rw [BivariantClass.eq_zero_iff_capsIntegral_canonical]
    intro T g _ _ k
    show (c - dedekindExteriorClass hC sX p (bivariantChowClassCapBaseFundamentalClass sX p c) -
      d).cap g k (fundamentalChowClass C (g ≫ 𝟙 C.S) k) = 0
    by_cases hT : g.base (genericPoint T) ∈ clopenPoints C
    · refine BivariantChowClass.cap_integral_eq_zero_of_mem_clopenPoints hC sX p _ ?_ g hT k
      rw [BivariantChowClass.sub_cap, BivariantChowClass.sub_cap]
      show c.cap _ _ _ - (dedekindExteriorClass hC sX p
        (bivariantChowClassCapBaseFundamentalClass sX p c)).cap _ _ _ - d.cap _ _ _ = 0
      rw [hd0, ← ha, dedekindExteriorClass_cap_eq_zero_of_mem_clopenPoints hC sX p a hsupp _
        ι_mem_clopenPoints, sub_zero, sub_self]
    · have hT' : ∀ t : T, g.base t ∉ clopenPoints C := fun t ht ↦
        hT (mem_clopenPoints_of_specializes ((genericPoint_specializes t).map g.continuous) ht)
      rw [BivariantChowClass.sub_cap]
      show (c - dedekindExteriorClass hC sX p
        (bivariantChowClassCapBaseFundamentalClass sX p c)).cap _ _ _ - d.cap _ _ _ = 0
      rw [hd1 g hT' k, sub_zero]
      exact BivariantChowClass.cap_integral_eq_zero_of_not_mem_clopenPoints hC sX p _ hα g hT k
  exact BivariantChowClass.addEquivBivariantClass.injective
    ((BivariantChowClass.addEquivBivariantClass_apply _).trans (h0.trans (map_zero _).symm))

end Decomposition

/-! ### Stacks 0FC6 -/

section Commute

variable {C : ChowSituation.{u}} (hC : IsDedekindChowBase C) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : Y ⟶ Z)
  [LocallyOfFiniteType f] (p q : ℤ)

include hC in
/-- **Stacks 0FC6, in the form of Stacks 0FA2, over every Dedekind base.** The base change
`res(c) ∈ A^p(X ×_S Z ⟶ Z)` of any `c ∈ A^p(X ⟶ S)` commutes with every `c' ∈ A^q(Y ⟶ Z)`:
`c = c_α + d` with `c_α` commuting with `c'` by Stacks 0FC7 and `d` by the axioms of Stacks
0B76. -/
theorem bivariantCommute_bivariantToBase_of_isDedekindChowBase
    (c : BivariantChowClass C sX (𝟙 C.S) sX (Category.comp_id sX) p)
    (c' : BivariantChowClass C (f ≫ sZ) sZ f rfl q) :
    BivariantCommute C (gysinSystemOfInvertible C) sZ (pullback.snd sX sZ) f p q
      (bivariantToBaseRestrictionHom C (gysinSystemOfInvertible C) sX sZ p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (BivariantChowClass.equivBivariantClass c))
      (BivariantChowClass.equivBivariantClass c') := by
  obtain ⟨d, hd, hc⟩ := exists_eq_dedekindExteriorClass_add hC sX p c
  rw [hc, ← BivariantChowClass.addEquivBivariantClass_apply, map_add, map_add,
    BivariantChowClass.addEquivBivariantClass_apply,
    BivariantChowClass.addEquivBivariantClass_apply]
  exact bivariantCommute_add_left C _ sZ _ f p q _
    (bivariantCommute_dedekindExteriorClass hC sX sZ f p q _ c') (hd sZ f q _)

end Commute

section Composite

variable {C : ChowSituation.{u}} {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : Y ⟶ Z)
  (hf : f ≫ sZ = sY) (p q : ℤ)

/-- **Stacks 0FC6.** Let `(S, δ)` be as in Stacks section 42.63 — locally the spectrum of a
Dedekind domain, with `δ = 0` at the closed points and `δ = 1` elsewhere. Let `X` be a scheme
locally of finite type over `S` and `c ∈ A^p(X ⟶ S)`. Let `f : Y ⟶ Z` be a morphism of schemes
locally of finite type over `S` and `c' ∈ A^q(Y ⟶ Z)`. Then `c ∘ c' = c' ∘ c` in
`A^{p+q}(X ×_S Y ⟶ Z)`.

Here `c ∘ c' = res(c) ∘ c'` with `res(c) ∈ A^p(X ×_S Y ⟶ Y)` the restriction of `c` along
`Y ⟶ S`, and `c' ∘ c = res(c') ∘ res(c)` with `res(c) ∈ A^p(X ×_S Z ⟶ Z)` the restriction of `c`
along `Z ⟶ S` and `res(c') ∈ A^q(Y ×_Z (X ×_S Z) ⟶ X ×_S Z)` the restriction of `c'` along
`X ×_S Z ⟶ Z` (Stacks 0F9Z, 0FA2). The second composite lives on `Y ×_Z (X ×_S Z)` and in degree
`q + p`; it is read on `X ×_S Y` through the canonical isomorphism and in degree `p + q`. -/
@[stacks 0FC6 "c ∘ c' = c' ∘ c in A^{p+q}(X ×_S Y → Z) for c ∈ A^p(X → S) and c' ∈ A^q(Y → Z), \
the composites read as in Stacks 0FA2"]
theorem BivariantChowClass.comp_comm_of_isDedekindChowBase (hC : IsDedekindChowBase C)
    (c : BivariantChowClass C sX (𝟙 C.S) sX (Category.comp_id sX) p)
    (c' : BivariantChowClass C sY sZ f hf q) :
    (c.restrict sY (Category.comp_id sY)).comp c' =
      (((c'.restrict (pullback.snd sX sZ)
          (BivariantChowClass.restrict_structure_eq (Category.comp_id sX) sZ
            (Category.comp_id sZ))).comp
        (c.restrict sZ (Category.comp_id sZ))).degreeCongr (add_comm q p)).transport
        (comp_comp_structureMorphism_eq
          (BivariantChowClass.restrict_structure_eq (Category.comp_id sX) sY
            (Category.comp_id sY)) hf)
        (pointClassCompositeIso C sX sZ f hf) (pointClassCompositeIso_hom_comp C sX sZ f hf) := by
  subst hf
  have := BivariantChowClass.locallyOfFiniteType_of_structure sZ f rfl
  exact BivariantChowClass.comp_comm_of_bivariantCommute C sX sZ f p q c c'
    (bivariantCommute_bivariantToBase_of_isDedekindChowBase hC sX sZ f p q c c')

end Composite

end Stacks.Chow

end
