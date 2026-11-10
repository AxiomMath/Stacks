module

public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.EtaleLocalizationQuasiFinite.FiniteNeighborhood
public import StacksFrontier.AlgebraicGeometry.SeminormalizationGluing.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapPullback

/-!
# Lifting a morphism from a seminormal scheme through a subintegral morphism

Let `g : S' ⟶ S` be a universal homeomorphism inducing isomorphisms on all residue fields. Then
every morphism to `S` from a seminormal scheme factors through `g`: the base change of `g` to the
source is again such a morphism, hence an object of the seminormalization category of the source,
and seminormality of the source identifies the seminormalization with the source itself.

The case of the spectrum of a discrete valuation ring is the input used by Stacks 0H5G, and it
applies because an integrally closed domain is a seminormal ring.

## Main results

* `isSeminormalRing_of_isIntegrallyClosed` — an integrally closed domain is a seminormal ring.
* `AlgebraicGeometry.bijective_base_of_universalHomeomorphism` — a universal homeomorphism is
  bijective on points.
* `AlgebraicGeometry.isSeminormal_spec_of_isDiscreteValuationRing` — the spectrum of a discrete
  valuation ring is a seminormal scheme.
* `AlgebraicGeometry.exists_comp_eq_of_isSeminormal` — a morphism from a seminormal scheme to `S`
  lifts through a universal homeomorphism `S' ⟶ S` inducing isomorphisms on all residue fields.

## Implementation notes

In an integrally closed domain the element witnessing seminormality for a pair `x ^ 3 = y ^ 2`
with `x ≠ 0` is the quotient `y / x` formed in the fraction field: its square is `x`, so it is
integral over the ring and therefore lies in it. Uniqueness is the cancellation `a ^ 2 * a =
a ^ 2 * b` available in a domain.

The lift is obtained from the universal property of the seminormalization rather than from a
section of the base change, so no reducedness hypothesis on the source is needed beyond the one
contained in seminormality.

## References

* [Stacks Project, Tag 0EUK](https://stacks.math.columbia.edu/tag/0EUK)
* [Stacks Project, Tag 0EUL](https://stacks.math.columbia.edu/tag/0EUL)
* [Stacks Project, Tag 0EUS](https://stacks.math.columbia.edu/tag/0EUS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

/-- An integrally closed domain is a seminormal ring: for `x ^ 3 = y ^ 2` with `x ≠ 0` the
quotient `y / x` in the fraction field has square `x`, hence is integral over the ring and so
lies in it. -/
theorem isSeminormalRing_of_isIntegrallyClosed (R : Type*) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] : IsSeminormalRing R := by
  intro x y hxy
  by_cases hx : x = 0
  · have hy : y = 0 := mul_self_eq_zero.mp (by simpa [hx, pow_two] using hxy.symm)
    subst hx hy
    exact ⟨0, by simp, fun a ha => mul_self_eq_zero.mp (by simpa [pow_two] using ha.1.symm)⟩
  · let K := FractionRing R
    let z : K := algebraMap R K y / algebraMap R K x
    have hxK : algebraMap R K x ≠ 0 := fun h =>
      hx (IsFractionRing.injective R K (by simpa using h))
    have hz2 : z ^ 2 = algebraMap R K x := by
      rw [div_pow, ← map_pow, ← hxy, map_pow, div_eq_iff (pow_ne_zero 2 hxK)]
      ring
    have hz3 : z ^ 3 = algebraMap R K y := by
      rw [pow_succ, hz2]
      exact mul_div_cancel₀ _ hxK
    have hzi : IsIntegral R z := by
      refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
      rw [hz2]
      exact isIntegral_algebraMap
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hzi
    have hpow : ∀ (n : ℕ) (w : R), z ^ n = algebraMap R K w → a ^ n = w := fun n w h =>
      IsFractionRing.injective R K (by rw [map_pow, ha, h])
    have ha2 : a ^ 2 = x := hpow 2 x hz2
    have ha3 : a ^ 3 = y := hpow 3 y hz3
    refine ⟨a, ⟨ha2.symm, ha3.symm⟩, fun b hb => ?_⟩
    have hfac : a ^ 2 ≠ 0 := by rwa [ha2]
    have hmul : a ^ 2 * a = a ^ 2 * b := by
      calc
        a ^ 2 * a = a ^ 3 := by ring
        _ = b ^ 3 := by rw [ha3, hb.2]
        _ = b ^ 2 * b := by ring
        _ = a ^ 2 * b := by rw [← hb.1, ← ha2]
    exact mul_left_cancel₀ hfac hmul.symm

namespace AlgebraicGeometry

/-- A universal homeomorphism is bijective on points: it is a homeomorphism, being its own base
change along the identity. -/
theorem bijective_base_of_universalHomeomorphism {A B : Scheme.{u}} (g : A ⟶ B)
    [UniversalHomeomorphism g] : Function.Bijective g.base :=
  ((inferInstance : UniversalHomeomorphism g).universally_isHomeomorph _ _ _
    IsPullback.of_id_snd).bijective

/-- A discrete valuation ring is a seminormal ring: it is an integrally closed domain. -/
theorem isSeminormalRing_of_isDiscreteValuationRing (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] : IsSeminormalRing R := by
  have hDIC : IsDiscreteValuationRing R ↔
      IsIntegrallyClosed R ∧ ∃! P : Ideal R, P ≠ ⊥ ∧ P.IsPrime :=
    (IsDiscreteValuationRing.TFAE R (IsDiscreteValuationRing.not_isField R)).out 1 4
  have hIC : IsIntegrallyClosed R := (hDIC.mp inferInstance).1
  exact isSeminormalRing_of_isIntegrallyClosed R

/-- The spectrum of a discrete valuation ring is a seminormal scheme. -/
theorem isSeminormal_spec_of_isDiscreteValuationRing (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] : IsSeminormal (Spec (CommRingCat.of R)) :=
  isSeminormal_spec_of_isSeminormalRing (isSeminormalRing_of_isDiscreteValuationRing R)

/-- A morphism from a seminormal scheme to `S` lifts through a universal homeomorphism
`g : S' ⟶ S` which induces isomorphisms on all residue fields.

The base change of `g` along the given morphism is again a universal homeomorphism inducing
isomorphisms on all residue fields, so it is an object of the seminormalization category of the
source; the identity of the source is another, and the canonical morphism from the initial object
to the identity object is an isomorphism because the source is seminormal. Composing its inverse
with the canonical morphism to the base change gives a section of the base change, and the first
projection of that section is the required lift. -/
theorem exists_comp_eq_of_isSeminormal {T S S' : Scheme.{u}} (g : S' ⟶ S)
    [UniversalHomeomorphism g] (hres : ∀ y : S', IsIso (g.residueFieldMap y)) (h : T ⟶ S)
    (hT : IsSeminormal T) : ∃ h' : T ⟶ S', h' ≫ g = h := by
  let C := SeminormalizationCategory T
  let idObj : C := ⟨Over.mk (𝟙 T), universalHomeomorphism_of_isIso (𝟙 T), fun x => by
    change IsIso ((𝟙 T : T ⟶ T).residueFieldMap x)
    rw [Scheme.residueFieldMap_id]
    exact CategoryTheory.IsIso.id _⟩
  let pObj : C := ⟨Over.mk (pullback.snd g h),
    ⟨(MorphismProperty.universally_isStableUnderBaseChange
      (topologically @IsHomeomorph)).of_isPullback (IsPullback.of_hasPullback g h)
        (inferInstance : UniversalHomeomorphism g).universally_isHomeomorph⟩,
    fun z => pullback_snd_residueFieldMap_isIso g h z (hres (pullback.fst g h z))⟩
  have hIso : IsIso (initial.to idObj).hom.left :=
    (isIso_initialTo_iff_isSeminormal T idObj).2 hT
  let e := asIso (initial.to idObj).hom.left
  let m := initial.to pObj
  have hsource : (initial C).obj.hom = e.hom := by
    simpa [e, idObj] using (initial.to idObj).hom.w.symm
  have hm : m.hom.left ≫ pullback.snd g h = (initial C).obj.hom := by
    simpa [m, pObj] using m.hom.w
  have hsection : (e.inv ≫ m.hom.left) ≫ pullback.snd g h = 𝟙 T := by
    rw [Category.assoc, hm, hsource]
    exact e.inv_hom_id
  refine ⟨(e.inv ≫ m.hom.left) ≫ pullback.fst g h, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hsection, Category.id_comp]

end AlgebraicGeometry

end
