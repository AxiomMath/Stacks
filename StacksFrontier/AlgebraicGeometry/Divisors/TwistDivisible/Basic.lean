module

public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Divisors.MultiplePointCartier
public import StacksFrontier.AlgebraicGeometry.Divisors.TwistDivisible.LocalToGlobal
public import StacksFrontier.AlgebraicGeometry.Divisors.TwistDivisible.StalkRange
public import StacksFrontier.AlgebraicGeometry.Divisors.TwistSectionMinimality
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk

/-!
# The minimality step of [Stacks, Tag 0A27]

Let `Y` be a locally Noetherian integral scheme, `y ∈ Y` a closed point at which the local ring
`𝒪_{Y,y}` is a discrete valuation ring, and write `I` for the ideal sheaf of `y`. The source's
argument for [Stacks, Tag 0A27] says, of a global section `s` of `𝒪_Y((n+1)y)`:

> if we take `n` minimal with this property, then `s` will map to a generator of the stalk
> `(𝒪_X(nx))_x`, since otherwise it would define a section of `𝒪_X((n-1)x) ⊂ 𝒪_X(n·x)`.

The clause after *"since otherwise"* is this file: a global section of `𝒪_Y((p+1)y)` whose germ
at `y` does **not** generate the stalk comes from `𝒪_Y(p·y)` along the inclusion
`𝒪_Y(p·y) ⊂ 𝒪_Y((p+1)y)`. That inclusion is `Stacks.Divisors.invertibleSheafMap` of the
morphism of ideal sheaves `Stacks.Divisors.negativeTwistMap`, and "the germ does not generate"
is by definition membership of the germ in `𝔪_y · 𝒪_Y((p+1)y)_y`
(`Stacks.SheafOfModules.nonvanishingLocus`).

## The argument

Everything is decided on the stalks. Writing `J_x` for the stalk of `I` at `x`, the image of
`𝒪_Y ⟶ 𝒪_Y(n·y)` on the stalk at `x` is `J_x^n · 𝒪_Y(n·y)_x`
(`Stacks.Divisors.TwistDivisible.range_stalkHom_unitToInvertibleSheaf`, with
`AlgebraicGeometry.IdealSheafData.stalk_pow`). The inclusion carries the canonical section of
`𝒪_Y(p·y)` to that of `𝒪_Y((p+1)y)`, so it carries the first image onto the second, and since
both stalks are free of rank one it is multiplication by a scalar `c` with

`J_x^p · (c) = J_x^(p+1)`.

Off `y` the ideal stalk is the unit ideal, so `(c)` is the unit ideal and the stalk map is
bijective. At `y` the local ring is a discrete valuation ring and `J_y` is its maximal ideal, so
`(c)` is the maximal ideal: the stalk map is injective and its image is exactly
`𝔪_y · 𝒪_Y((p+1)y)_y`, which is where the hypothesis puts the germ of the section. The lifting
criterion `Stacks.Divisors.TwistDivisible.mem_range_sectionsMap_of_germ_mem_range` then turns
that one germ into a global section.

## Main results

* `Stacks.Divisors.mem_range_sectionsMap_invertibleSheafMap_of_notMem_nonvanishingChart`: **the
  minimality step**, in the shape
  `Stacks.Divisors.isAffineOpen_compl_singleton_of_mem_range_of_finrank` consumes it.
* `Stacks.Divisors.TwistDivisible.exists_scalar_twistMap`: the inclusion is multiplication by
  one scalar on each stalk, and that scalar satisfies the ideal identity above.
* `Stacks.Divisors.TwistDivisible.bijective_stalkHom_twistMap` and
  `Stacks.Divisors.TwistDivisible.range_stalkHom_twistMap_eq`: the two cases of that identity.

## Implementation notes

**The morphism `q` and the curve hypotheses are carried, not used.** The statement is phrased
for the proper curve `q : Y ⟶ Spec k` that the consumer has in hand, so that it plugs into the
engine of `StacksFrontier/AlgebraicGeometry/Divisors/TwistSectionMinimality.lean` without
reshaping; what the argument actually uses is that `Y` is locally Noetherian and integral and
that `𝒪_{Y,y}` is a discrete valuation ring.

**Spellings are crossed by declared types, not by rewriting.** `maxIdealStalk` and
`Stacks.Divisors.TwistDivisible.idealStalk` are the maximal ideal and the ideal-sheaf stalk with
their types declared over `ringStalk Y.sheaf y`, which is the ring the stalk of a module is a
module over; without that the scalar action does not synthesize. The nonvanishing-locus
hypothesis arrives with the Tag 01CB module structure on the stalk and is moved to Mathlib's by
`Stacks.SheafOfModules.mem_smul_top_congr` at `Stacks.SheafOfModules.stalkModule_eq`.

## References

* [Stacks Project, Tag 0A27](https://stacks.math.columbia.edu/tag/0A27)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0B8Y](https://stacks.math.columbia.edu/tag/0B8Y)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules.SheafHomStalk
open Stacks.AlgebraicGeometry.ReflexiveModules (stalkHom stalkHom_germAt stalkHom_comp)

universe u

namespace Stacks.Divisors.TwistDivisible

variable {Y : Scheme.{u}}

/-- The maximal ideal of a local ring of `Y`, with its type declared at the `ringStalk`
spelling, which is the ring the stalk of a module is a module over. -/
noncomputable abbrev maxIdealStalk (y : Y) : Ideal (ringStalk Y.sheaf y) :=
  IsLocalRing.maximalIdeal (Y.presheaf.stalk y)

/-- **The inclusion `𝒪_Y(p·D) ⟶ 𝒪_Y((p+1)·D)`**, the morphism dual to the inclusion of ideal
sheaves `ℐ_{(p+1)D} ⟶ ℐ_{pD}`. -/
noncomputable abbrev twistMap (I : Y.IdealSheafData) (p : ℕ) :
    Stacks.Divisors.invertibleSheaf (I ^ p) ⟶ Stacks.Divisors.invertibleSheaf (I ^ (p + 1)) :=
  Stacks.Divisors.invertibleSheafMap
    (Stacks.Divisors.negativeTwistMap (Stacks.Divisors.pow_succ_le_pow I p))

/-- The ring stalk of an integral scheme is a domain. -/
private theorem isDomain_ringStalk [AlgebraicGeometry.IsIntegral Y] (x : Y) :
    IsDomain (ringStalk Y.sheaf x) :=
  inferInstanceAs (IsDomain (Y.presheaf.stalk x))

/-- **The inclusion carries the image of `𝒪_Y ⟶ 𝒪_Y(p·D)` onto that of
`𝒪_Y ⟶ 𝒪_Y((p+1)·D)`,** because it carries the canonical section of the first to the canonical
section of the second. Read through the computation of those two images, this says
`ℐ_{pD,x} · (image of the inclusion at `x`) = ℐ_{(p+1)D,x} · 𝒪_Y((p+1)D)_x`. -/
theorem smul_range_stalkHom_twistMap (I : Y.IdealSheafData) {p : ℕ}
    [Stacks.Divisors.IsEffectiveCartierDivisor (I ^ p)]
    [Stacks.Divisors.IsEffectiveCartierDivisor (I ^ (p + 1))] (x : Y) :
    idealStalk (I ^ p) x • LinearMap.range (stalkHom (twistMap I p) x)
      = idealStalk (I ^ (p + 1)) x • (⊤ : Submodule (ringStalk Y.sheaf x)
          (modStalk (Stacks.Divisors.divisorSheaf (I ^ (p + 1))) x)) := by
  have hcomp : Stacks.Divisors.unitToInvertibleSheaf (I ^ p) ≫ twistMap I p
      = Stacks.Divisors.unitToInvertibleSheaf (I ^ (p + 1)) :=
    Stacks.Divisors.unitToInvertibleSheaf_comp_invertibleSheafMap _
      (Stacks.Divisors.negativeTwistMap_idealInclusion _)
  have h2 : stalkHom (Stacks.Divisors.unitToInvertibleSheaf (I ^ (p + 1))) x
      = (stalkHom (twistMap I p) x).comp
        (stalkHom (Stacks.Divisors.unitToInvertibleSheaf (I ^ p)) x) :=
    (congrArg (fun f : _root_.SheafOfModules.unit (structureSheafRing Y.toRingedSpace) ⟶
        Stacks.Divisors.invertibleSheaf (I ^ (p + 1)) => stalkHom f x) hcomp).symm.trans
      (stalkHom_comp _ _ x)
  have h1 : LinearMap.range
        (stalkHom (Stacks.Divisors.unitToInvertibleSheaf (I ^ (p + 1))) x)
      = Submodule.map (stalkHom (twistMap I p) x)
        (LinearMap.range (stalkHom (Stacks.Divisors.unitToInvertibleSheaf (I ^ p)) x)) := by
    rw [h2, LinearMap.range_comp]
  rw [range_stalkHom_unitToInvertibleSheaf, range_stalkHom_unitToInvertibleSheaf] at h1
  have h3 : Submodule.map (stalkHom (twistMap I p) x)
        (idealStalk (I ^ p) x • (⊤ : Submodule (ringStalk Y.sheaf x)
          (modStalk (Stacks.Divisors.divisorSheaf (I ^ p)) x)))
      = idealStalk (I ^ p) x • Submodule.map (stalkHom (twistMap I p) x) ⊤ :=
    Submodule.map_smul'' (idealStalk (I ^ p) x) ⊤ (stalkHom (twistMap I p) x)
  rw [h3, Submodule.map_top] at h1
  exact h1.symm

/-- **On each stalk the inclusion is multiplication by one scalar `c`,** and that scalar
satisfies `ℐ_{pD,x} · (c) = ℐ_{(p+1)D,x}`. Both stalks are free of rank one over the local ring,
so the scalar is the coordinate of the image of a generator; the ideal identity is the previous
statement read through that description. The scalar being a nonzerodivisor makes the stalk map
injective, and its being a unit makes the stalk map bijective. -/
theorem exists_scalar_twistMap [AlgebraicGeometry.IsIntegral Y] (I : Y.IdealSheafData) {p : ℕ}
    [Stacks.Divisors.IsEffectiveCartierDivisor (I ^ p)]
    [Stacks.Divisors.IsEffectiveCartierDivisor (I ^ (p + 1))] (x : Y) :
    ∃ c : ringStalk Y.sheaf x,
      LinearMap.range (stalkHom (twistMap I p) x)
          = Ideal.span {c} • (⊤ : Submodule (ringStalk Y.sheaf x)
            (modStalk (Stacks.Divisors.divisorSheaf (I ^ (p + 1))) x))
        ∧ idealStalk (I ^ p) x * Ideal.span {c} = idealStalk (I ^ (p + 1)) x
        ∧ (c ≠ 0 → Function.Injective (stalkHom (twistMap I p) x))
        ∧ (IsUnit c → Function.Bijective (stalkHom (twistMap I p) x)) := by
  have := isDomain_ringStalk (Y := Y) x
  obtain ⟨α, hα⟩ := exists_bijective_smul_modStalk (I ^ p) x
  obtain ⟨β, hβ⟩ := exists_bijective_smul_modStalk (I ^ (p + 1)) x
  obtain ⟨c, hc⟩ := exists_apply_eq_smul α β hβ.2 (stalkHom (twistMap I p) x)
  have hspanα : Submodule.span (ringStalk Y.sheaf x) ({α} : Set _) = ⊤ :=
    span_eq_top_of_surjective_smul α hα.2
  have hspanβ : Submodule.span (ringStalk Y.sheaf x) ({β} : Set _) = ⊤ :=
    span_eq_top_of_surjective_smul β hβ.2
  have hrange : LinearMap.range (stalkHom (twistMap I p) x)
      = Ideal.span {c} • (⊤ : Submodule (ringStalk Y.sheaf x)
        (modStalk (Stacks.Divisors.divisorSheaf (I ^ (p + 1))) x)) :=
    (range_eq_span_singleton (stalkHom (twistMap I p) x) α hspanα).trans
      ((congrArg (fun z : modStalk (Stacks.Divisors.divisorSheaf (I ^ (p + 1))) x =>
          Submodule.span (ringStalk Y.sheaf x) ({z} : Set _)) hc).trans
        (span_singleton_smul_eq c β hspanβ))
  refine ⟨c, hrange, ?_, fun hc0 => injective_of_ne_zero hα.2 hβ hc hc0,
    fun hu => bijective_of_isUnit hα hβ hc hu⟩
  refine ideal_eq_of_smul_top_eq β hβ ?_
  refine ((Submodule.mul_smul _ _ _).trans
    (congrArg (fun S => idealStalk (I ^ p) x • S) hrange.symm)).trans ?_
  exact smul_range_stalkHom_twistMap I x


/-- Off its support, the stalk of an ideal sheaf is the unit ideal. -/
theorem idealStalk_eq_top_of_notMem_support (J : Y.IdealSheafData) {x : Y}
    (hx : x ∉ J.support) : idealStalk J x = ⊤ :=
  (AlgebraicGeometry.IdealSheafData.stalk_eq_top_iff_not_mem_support J x).mpr hx

/-- **Away from the divisor the inclusion is bijective on the stalk.** There the two ideal
stalks are the unit ideal, so the scalar generates the unit ideal and is therefore a unit. -/
theorem bijective_stalkHom_twistMap [AlgebraicGeometry.IsIntegral Y] (I : Y.IdealSheafData)
    {p : ℕ} [Stacks.Divisors.IsEffectiveCartierDivisor (I ^ p)]
    [Stacks.Divisors.IsEffectiveCartierDivisor (I ^ (p + 1))] {x : Y}
    (hxp : x ∉ (I ^ p).support) (hxp1 : x ∉ (I ^ (p + 1)).support) :
    Function.Bijective (stalkHom (twistMap I p) x) := by
  obtain ⟨c, -, hideal, -, hbij⟩ := exists_scalar_twistMap I (p := p) x
  rw [idealStalk_eq_top_of_notMem_support _ hxp,
    idealStalk_eq_top_of_notMem_support _ hxp1, Ideal.top_mul] at hideal
  exact hbij (Ideal.span_singleton_eq_top.mp hideal)

/-- **At a point where the two ideal stalks are the powers of a principal nonzero ideal, the
image of the inclusion on the stalk is that ideal times the whole stalk, and the stalk map is
injective.** This is the colength computation `(π)^p · (c) = (π)^(p+1) ⟹ (c) = (π)`. -/
theorem range_stalkHom_twistMap_eq [AlgebraicGeometry.IsIntegral Y] (I : Y.IdealSheafData)
    {p : ℕ} [Stacks.Divisors.IsEffectiveCartierDivisor (I ^ p)]
    [Stacks.Divisors.IsEffectiveCartierDivisor (I ^ (p + 1))] {y : Y}
    (pi : Y.presheaf.stalk y) (hpi : pi ≠ 0)
    (hp : idealStalk (I ^ p) y = Ideal.span ({pi} : Set (ringStalk Y.sheaf y)) ^ p)
    (hp1 : idealStalk (I ^ (p + 1)) y
      = Ideal.span ({pi} : Set (ringStalk Y.sheaf y)) ^ (p + 1)) :
    LinearMap.range (stalkHom (twistMap I p) y)
        = Ideal.span ({pi} : Set (ringStalk Y.sheaf y)) •
          (⊤ : Submodule (ringStalk Y.sheaf y)
            (modStalk (Stacks.Divisors.divisorSheaf (I ^ (p + 1))) y))
      ∧ Function.Injective (stalkHom (twistMap I p) y) := by
  have := isDomain_ringStalk (Y := Y) y
  obtain ⟨c, hrange, hideal, hinj, -⟩ := exists_scalar_twistMap I (p := p) y
  rw [hp, hp1] at hideal
  have hspan : Ideal.span ({c} : Set (ringStalk Y.sheaf y))
      = Ideal.span ({pi} : Set (ringStalk Y.sheaf y)) :=
    span_eq_span_of_pow_mul hpi hideal
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, Ideal.span_singleton_eq_bot.mpr rfl] at hspan
    exact hpi (Ideal.span_singleton_eq_bot.mp hspan.symm)
  exact ⟨by rw [hrange, hspan], hinj hc0⟩

end Stacks.Divisors.TwistDivisible

namespace Stacks.Divisors

open Stacks.Divisors.TwistDivisible

/-- **The minimality step of [Stacks, Tag 0A27].** Let `Y` be a locally Noetherian integral
scheme proper over a field `k` as a curve, let `y` be a closed point at which `𝒪_{Y,y}` is a
discrete valuation ring, and let `t` be a global section of `𝒪_Y((p+1)y)` whose germ at `y` does
not generate the stalk — that is, `y` is outside the nonvanishing chart of `t`. Then `t` comes
from `𝒪_Y(p·y)` along the inclusion `𝒪_Y(p·y) ⊂ 𝒪_Y((p+1)y)`.

This is the source's *"since otherwise it would define a section of `𝒪_X((n-1)x)`"*: the germ of
`t` at `y` lies in `𝔪_y · 𝒪_Y((p+1)y)_y`, which is exactly the image of the inclusion on that
stalk, while off `y` the inclusion is an isomorphism on stalks; a section recognised on the one
stalk where the two sheaves differ is a section of the smaller one.

The morphism `q` and the properness and curve hypotheses are carried so that the statement is
the one the chart engine of
`StacksFrontier/AlgebraicGeometry/Divisors/TwistSectionMinimality.lean` asks for. -/
theorem mem_range_sectionsMap_invertibleSheafMap_of_notMem_nonvanishingChart
    (k : Type u) [Field k] {Y : Scheme.{u}} (q : Y ⟶ Spec (.of k))
    [IsLocallyNoetherian Y] [AlgebraicGeometry.IsIntegral Y] (_hq : IsProper q) (_hc : IsCurve k q)
    {y : Y} (hy : IsClosed ({y} : Set Y))
    [IsDiscreteValuationRing (Y.presheaf.stalk y)] (p : ℕ)
    (t : (invertibleSheaf
        (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y) ^ (p + 1))).sections)
    (ht : y ∉ Stacks.ProjectiveSpaceSections.nonvanishingChart (invertibleSheaf
        (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y) ^ (p + 1))) t) :
    t ∈ Set.range (_root_.SheafOfModules.sectionsMap (invertibleSheafMap
      (negativeTwistMap (pow_succ_le_pow
        (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) p)))) := by
  classical
  have hcart : ∀ n : ℕ, IsEffectiveCartierDivisor
      (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y) ^ n) := fun n =>
    AlgebraicGeometry.isEffectiveCartierDivisor_vanishingIdeal_pow hy n
  have := hcart p
  have := hcart (p + 1)
  obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible (Y.presheaf.stalk y)
  have hmax : IsLocalRing.maximalIdeal (Y.presheaf.stalk y) = Ideal.span {pi} :=
    hpi.maximalIdeal_eq
  have hstalk : ∀ n : ℕ,
      idealStalk (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y) ^ n) y
        = Ideal.span ({pi} : Set (ringStalk Y.sheaf y)) ^ n := by
    intro n
    change AlgebraicGeometry.IdealSheafData.stalk _ y = _
    rw [AlgebraicGeometry.IdealSheafData.stalk_pow,
      AlgebraicGeometry.IdealSheafData.stalk_vanishingIdeal_singleton y hy, hmax]
    rfl
  have hsupp : ∀ n : ℕ, ∀ x : Y, x ≠ y →
      x ∉ (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y) ^ n).support := by
    intro n x hxy hx
    have hx' : x ∈ (Scheme.IdealSheafData.vanishingIdeal
        (⟨{y}, hy⟩ : Closeds Y) ^ n).supportSet := hx
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [supportSet_pow_zero] at hx'
      exact hx'
    · rw [supportSet_pow _ hn,
        AlgebraicGeometry.supportSet_vanishingIdeal_singleton hy] at hx'
      exact hxy hx'
  have hrange := range_stalkHom_twistMap_eq
    (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) pi hpi.ne_zero
    (hstalk p) (hstalk (p + 1))
  refine mem_range_sectionsMap_of_germ_mem_range
    (twistMap (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) p) y
    (fun x => ?_) (fun x hxy => (bijective_stalkHom_twistMap _
      (hsupp p x hxy) (hsupp (p + 1) x hxy)).2) t ?_
  · by_cases hxy : x = y
    · subst hxy
      exact hrange.2
    · exact (bijective_stalkHom_twistMap _ (hsupp p x hxy) (hsupp (p + 1) x hxy)).1
  · rw [hrange.1]
    have hmem : Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm Y.toRingedSpace
        (invertibleSheaf (Scheme.IdealSheafData.vanishingIdeal
          (⟨{y}, hy⟩ : Closeds Y) ^ (p + 1))).val y ⊤ (Opens.mem_top y) (t.eval (op ⊤))
        ∈ IsLocalRing.maximalIdeal
            (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y.toRingedSpace y) •
          (⊤ : Submodule _ _) := not_not.mp ht
    have hinst := Stacks.SheafOfModules.stalkModule_eq (X := Y.toRingedSpace)
      (invertibleSheaf (Scheme.IdealSheafData.vanishingIdeal
        (⟨{y}, hy⟩ : Closeds Y) ^ (p + 1))).val y
    have hmem2 := (Stacks.SheafOfModules.mem_smul_top_congr hinst _ _).mp hmem
    have hmax' : maxIdealStalk y = Ideal.span ({pi} : Set (ringStalk Y.sheaf y)) := hmax
    rw [← hmax']
    exact hmem2

end Stacks.Divisors


end
