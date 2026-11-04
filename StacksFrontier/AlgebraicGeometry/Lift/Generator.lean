module

public import StacksFrontier.AlgebraicGeometry.CartierAffineLocal.Basic
public import StacksFrontier.AlgebraicGeometry.Lift.IdealComap

/-!
# An effective Cartier pullback is cut out by a section of the ideal on the base

This file refines the forward direction of [Stacks, Tag 01WS].

`Stacks.CartierAffineLocal.exists_affineOpen_nonZeroDivisor` says that an effective Cartier
divisor is cut out, around every point, by *some* nonzerodivisor on *some* affine open. For the
existence half of [Stacks, Tag 0806] that is not enough: the morphism into the blowup built by
`Stacks.AlgebraicGeometry.AffineBlowupLift.toBlowUp` needs the generator to be the image of a
section of the ideal sheaf **on an affine open of the base**, because the blowup chart it factors
through is the one attached to such a section.

So, for `f : Y ⟶ X` with `I.comap f` an effective Cartier divisor, an affine open `U` of `X` and
a point `y` of `f⁻¹(U)`, this file produces an affine open `V ∋ y` inside `f⁻¹(U)` and a section
`a ∈ I.ideal U` whose image in `Γ(Y, V)` is a nonzerodivisor generating
`(I.comap f).ideal V`.

## Main results

* `Stacks.Tag0806Lift.exists_affineOpen_nonZeroDivisor_le`: the forward direction of
  [Stacks, Tag 01WS] with the affine open constrained to lie inside a prescribed open.
* `Stacks.Tag0806Lift.exists_affineOpen_section_generator`: **the refinement**, as described
  above.

## Implementation notes

The mathematics is the standard "shrink to a basic open" argument and is elementary.
On a first affine open `V₁ ⊆ f⁻¹(U)` the forward direction of Tag 01WS gives a nonzerodivisor
`g` with `(I.comap f).ideal V₁ = (g)`, and `Stacks.IdealSheaf.ideal_comap_appLE` identifies the
left side with the extension `I.ideal U · Γ(Y, V₁)`. Writing `g = ∑ xᵢ · aᵢ|_{V₁}` with
`aᵢ ∈ I.ideal U` and `aᵢ|_{V₁} = cᵢ g` gives `(∑ xᵢcᵢ) g = g`, hence `∑ xᵢcᵢ = 1` because `g` is
a nonzerodivisor.
The germs of the `cᵢ` at `y` therefore cannot all lie in the maximal ideal of the local ring
`𝒪_{Y,y}`, so some `cᵢ` has `y` in its basic open; on that basic open `aᵢ` and `g` differ by the
unit `cᵢ`, so `aᵢ` generates as well.

Two details are worth recording.

*The nonzerodivisor property is not transported through a localization.* Rather than prove that
the image of `g` in `Γ(Y, D(cᵢ))` is still a nonzerodivisor, the argument applies Tag 01WS
forward a **second** time, inside `D(cᵢ)`, to get an affine `V₃ ∋ y` with its own nonzerodivisor
generator `g₃`; then `(aᵢ|_{V₃})` and `(g₃)` are the same principal ideal, and
`mem_nonZeroDivisors_of_span_eq` — two generators of one principal ideal differ by a unit —
transfers the property with no localization theory at all.

*`exists_affineOpen_nonZeroDivisor_le` is not a corollary of the unconstrained statement*, since
that one returns an affine open with no control on where it sits. It is instead the same three-line
composition, with the intersection `U y ⊓ W` in place of `U y`; both
`Stacks.CartierAffineLocal.exists_nonZeroDivisor_of_trivialization` and
`Stacks.CartierAffineLocal.exists_affineOpens_le` are public, so nothing is duplicated.

## References

* [Stacks Project, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS)
* [Stacks Project, Tag 0806](https://stacks.math.columbia.edu/tag/0806)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Tag0806Lift

/-! ### Commutative algebra -/

/-- An element of an extended ideal `J · S` is a finite `S`-combination of images of elements
of `J`. This is `Submodule.mem_span_set'` applied to the definition of `Ideal.map`. -/
theorem exists_combination_of_mem_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (J : Ideal R) {g : S} (hg : g ∈ Ideal.map φ J) :
    ∃ (n : ℕ) (x : Fin n → S) (a : Fin n → R),
      (∀ i, a i ∈ J) ∧ ∑ i, x i * φ (a i) = g := by
  have hg' : g ∈ Ideal.span ((φ : R → S) '' (J : Set R)) := hg
  rw [Submodule.mem_span_set'] at hg'
  obtain ⟨n, x, w, hw⟩ := hg'
  choose a ha hφa using fun i : Fin n => (w i).2
  refine ⟨n, x, a, ha, ?_⟩
  rw [← hw]
  exact Finset.sum_congr rfl fun i _ => by rw [hφa i]; rfl

/-- **The unit-coefficient step.** If a nonzerodivisor `g` is a combination `∑ xᵢ (cᵢ g)`, then
`∑ xᵢ cᵢ = 1`. -/
theorem sum_mul_eq_one_of_nonZeroDivisor {S : Type*} [CommRing S] {n : ℕ} (x c : Fin n → S)
    {g : S} (hg : g ∈ nonZeroDivisors S) (h : ∑ i, x i * (c i * g) = g) :
    ∑ i, x i * c i = 1 := by
  have hmul : (∑ i, x i * c i) * g = g := by
    rw [Finset.sum_mul]
    exact Eq.trans (Finset.sum_congr rfl fun i _ => by ring) h
  have hfac : (∑ i, x i * c i - 1) * g = 0 := by
    rw [sub_mul, one_mul, hmul, sub_self]
  have := (mem_nonZeroDivisors_iff.mp hg).2 _ hfac
  linear_combination this

/-- **Two generators of one principal ideal differ by a unit.** So if one of them is a
nonzerodivisor, so is the other. This replaces any statement about nonzerodivisors in a
localization. -/
theorem mem_nonZeroDivisors_of_span_eq {S : Type*} [CommRing S] {u v : S}
    (h : Ideal.span ({u} : Set S) = Ideal.span ({v} : Set S)) (hv : v ∈ nonZeroDivisors S) :
    u ∈ nonZeroDivisors S := by
  obtain ⟨s, hs⟩ : ∃ s, s * v = u := by
    rw [← Ideal.mem_span_singleton' (y := v), ← h]; exact Ideal.mem_span_singleton_self u
  obtain ⟨t, ht⟩ : ∃ t, t * u = v := by
    rw [← Ideal.mem_span_singleton' (y := u), h]; exact Ideal.mem_span_singleton_self v
  have hts : (t * s - 1) * v = 0 := by
    rw [sub_mul, one_mul, sub_eq_zero]
    calc t * s * v = t * (s * v) := by ring
      _ = v := by rw [hs, ht]
  have hts1 : t * s = 1 := by
    have := (mem_nonZeroDivisors_iff.mp hv).2 _ hts
    linear_combination this
  have hunit : IsUnit s := IsUnit.of_mul_eq_one t (by rw [mul_comm]; exact hts1)
  rw [← hs]
  exact mul_mem hunit.mem_nonZeroDivisors hv

/-! ### The forward direction of Tag 01WS, inside a prescribed open -/

variable {X : Scheme.{u}}

/-- **The forward direction of [Stacks, Tag 01WS], localized to a prescribed open.** An
effective Cartier divisor is cut out by a single nonzerodivisor on an affine open neighbourhood
of any point, *inside any prescribed open neighbourhood of that point*.

`Stacks.CartierAffineLocal.exists_affineOpen_nonZeroDivisor` is the case `W = ⊤`; this is the
same composition with the trivializing open intersected with `W`. -/
theorem exists_affineOpen_nonZeroDivisor_le (I : X.IdealSheafData)
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (W : X.Opens) {x : X} (hxW : x ∈ W) :
    ∃ V : X.affineOpens, x ∈ (V : Set X) ∧ (V : X.Opens) ≤ W ∧ ∃ g : Γ(X, V.1),
      g ∈ nonZeroDivisors Γ(X, V.1) ∧ I.ideal V = Ideal.span {g} := by
  have hinv : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property
        (Stacks.ClosedImmersion.idealSheaf I.subschemeι.toLRSHom.toShHom) := hI
  obtain ⟨O, hO, t⟩ := Stacks.SheafRankOne.exists_cover_trivialization_of_isInvertible
    (X := X.toRingedSpace) (structureSheafRing X.toRingedSpace).property
    (Stacks.ClosedImmersion.idealSheaf I.subschemeι.toLRSHom.toShHom)
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (hO ▸ Opens.mem_top x)
  obtain ⟨V, hxV, hVle⟩ :=
    Stacks.CartierAffineLocal.exists_affineOpens_le (x := x) (O j ⊓ W) ⟨hj, hxW⟩
  exact ⟨V, hxV, hVle.trans inf_le_right,
    Stacks.CartierAffineLocal.exists_nonZeroDivisor_of_trivialization I (t j).some V
      (homOfLE (hVle.trans inf_le_left))⟩

/-! ### The germ step -/

/-- **A partition of unity has a unit member at every point.** If `∑ xᵢ cᵢ = 1` on an open `V`
of a scheme, then every point of `V` lies in the basic open of some `cᵢ`: the germs of the `cᵢ`
cannot all be nonunits, since the local ring at the point is local. -/
theorem exists_mem_basicOpen_of_sum_eq_one {V : X.Opens} {n : ℕ} (x c : Fin n → Γ(X, V))
    (h : ∑ i, x i * c i = 1) {y : X} (hy : y ∈ V) :
    ∃ i, y ∈ X.basicOpen (c i) := by
  by_contra hcon
  push Not at hcon
  have hgerm : ∑ i, (X.presheaf.germ V y hy).hom (x i) * (X.presheaf.germ V y hy).hom (c i)
      = 1 := by
    rw [← map_one (X.presheaf.germ V y hy).hom, ← h, map_sum]
    exact Finset.sum_congr rfl fun i _ => (map_mul _ _ _).symm
  have hone : (1 : X.presheaf.stalk y) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
    rw [← hgerm]
    refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ ?_
    exact (IsLocalRing.mem_maximalIdeal _).mpr
      (mem_nonunits_iff.mpr fun hu => hcon i ((X.mem_basicOpen (c i) y hy).mpr hu))
  exact (IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk y)).ne_top
    (Ideal.eq_top_of_isUnit_mem _ hone isUnit_one)

/-! ### The refinement -/

/-- **The generator can be taken to be a section of the ideal on the base.** Let `f : Y ⟶ X` be
a morphism of schemes and `I` an ideal sheaf on `X` whose inverse image along `f` is an effective
Cartier divisor. Then for every affine open `U` of `X` and every point `y` of `f⁻¹(U)` there is
an affine open `V ∋ y` inside `f⁻¹(U)` and a section `a ∈ I.ideal U` whose image in `Γ(Y, V)` is
a nonzerodivisor generating `(I.comap f).ideal V`.

This is the input of `Stacks.AlgebraicGeometry.AffineBlowupLift.toBlowUp` at
`B = Γ(Y, V)`: the plain forward direction of [Stacks, Tag 01WS] supplies a nonzerodivisor
generator but says nothing about it being the image of a section on the base, and the blowup
chart is indexed by such a section. See the module docstring for the argument. -/
theorem exists_affineOpen_section_generator {Y : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor (I.comap f)) (U : X.affineOpens) {y : Y}
    (hy : y ∈ f ⁻¹ᵁ (U : X.Opens)) :
    ∃ (V : Y.affineOpens) (hVU : (V : Y.Opens) ≤ f ⁻¹ᵁ (U : X.Opens)),
      y ∈ (V : Set Y) ∧ ∃ a ∈ I.ideal U,
        (f.appLE U.1 V.1 hVU).hom a ∈ nonZeroDivisors Γ(Y, V.1) ∧
        (I.comap f).ideal V = Ideal.span {(f.appLE U.1 V.1 hVU).hom a} := by
  -- A first affine open inside `f⁻¹(U)`, with a nonzerodivisor generator.
  obtain ⟨V₁, hyV₁, hV₁U, g, hgnzd, hgen₁⟩ :=
    exists_affineOpen_nonZeroDivisor_le (I.comap f) hD (f ⁻¹ᵁ (U : X.Opens)) hy
  have hmap₁ : Ideal.map (f.appLE U.1 V₁.1 hV₁U).hom (I.ideal U) = Ideal.span {g} := by
    rw [← Stacks.IdealSheaf.ideal_comap_appLE I f U V₁ hV₁U]; exact hgen₁
  -- Write `g` as a combination of images of sections of `I` on `U`.
  obtain ⟨n, xc, a, haJ, hsum⟩ := exists_combination_of_mem_map
    (f.appLE U.1 V₁.1 hV₁U).hom (I.ideal U) (by rw [hmap₁]; exact Ideal.mem_span_singleton_self g)
  -- Each image is a multiple of `g`.
  have hcex : ∀ i, ∃ c, (f.appLE U.1 V₁.1 hV₁U).hom (a i) = c * g := fun i => by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp
      (show (f.appLE U.1 V₁.1 hV₁U).hom (a i) ∈ Ideal.span {g} by
        rw [← hmap₁]; exact Ideal.mem_map_of_mem _ (haJ i))
    exact ⟨c, hc.symm⟩
  choose c hc using hcex
  -- The coefficients form a partition of unity, so one of them is a unit at `y`.
  have hone : ∑ i, xc i * c i = 1 := by
    refine sum_mul_eq_one_of_nonZeroDivisor xc c hgnzd
      (Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hsum)
    rw [hc i]
  obtain ⟨i, hyb⟩ := exists_mem_basicOpen_of_sum_eq_one xc c hone hyV₁
  -- Shrink to an affine open inside the basic open of that coefficient.
  have hb₁ : Y.basicOpen (c i) ≤ V₁.1 := Y.basicOpen_le (c i)
  obtain ⟨V₃, hyV₃, hV₃b, g₃, hg₃nzd, hgen₃⟩ :=
    exists_affineOpen_nonZeroDivisor_le (I.comap f) hD (Y.basicOpen (c i)) hyb
  have hV₃₁ : (V₃ : Y.Opens) ≤ V₁.1 := hV₃b.trans hb₁
  have hV₃U : (V₃ : Y.Opens) ≤ f ⁻¹ᵁ (U : X.Opens) := hV₃₁.trans hV₁U
  -- The restriction map `Γ(Y, V₁) ⟶ Γ(Y, V₃)` factors through the basic open.
  have hρfac : Y.presheaf.map (homOfLE hb₁).op ≫ Y.presheaf.map (homOfLE hV₃b).op =
      Y.presheaf.map (homOfLE hV₃₁).op := by
    rw [← Functor.map_comp]; rfl
  have hunit : IsUnit ((Y.presheaf.map (homOfLE hV₃₁).op).hom (c i)) := by
    rw [← hρfac]
    exact (Y.toRingedSpace.isUnit_res_basicOpen (c i)).map
      (Y.presheaf.map (homOfLE hV₃b).op).hom
  -- The sections map over `V₃` is the composite, so the ideal and the generator both transport.
  have hφ₃ : f.appLE U.1 V₃.1 hV₃U =
      f.appLE U.1 V₁.1 hV₁U ≫ Y.presheaf.map (homOfLE hV₃₁).op :=
    (Scheme.Hom.appLE_map f hV₁U (homOfLE hV₃₁).op).symm
  have hgenρ : (I.comap f).ideal V₃ =
      Ideal.span {(Y.presheaf.map (homOfLE hV₃₁).op).hom g} := by
    rw [Stacks.IdealSheaf.ideal_comap_appLE I f U V₃ hV₃U, hφ₃, CommRingCat.hom_comp,
      ← Ideal.map_map, hmap₁, Ideal.map_span, Set.image_singleton]
  have hval : (f.appLE U.1 V₃.1 hV₃U).hom (a i) =
      (Y.presheaf.map (homOfLE hV₃₁).op).hom (c i) *
        (Y.presheaf.map (homOfLE hV₃₁).op).hom g := by
    rw [hφ₃, CommRingCat.hom_comp, RingHom.comp_apply, hc i, map_mul]
  refine ⟨V₃, hV₃U, hyV₃, a i, haJ i, ?_, ?_⟩
  · rw [hval]
    refine mul_mem hunit.mem_nonZeroDivisors (mem_nonZeroDivisors_of_span_eq ?_ hg₃nzd)
    rw [← hgenρ, hgen₃]
  · rw [hgenρ, hval, Ideal.span_singleton_mul_left_unit hunit]

end Stacks.Tag0806Lift

end
