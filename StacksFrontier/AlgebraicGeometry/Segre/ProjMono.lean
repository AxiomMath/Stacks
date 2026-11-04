module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# When a morphism to `Proj` defined by global sections is a monomorphism

Mathlib's `AlgebraicGeometry.Proj.fromOfGlobalSections` turns a ring homomorphism
`f : A →+* Γ(X, 𝒪_X)` out of a graded ring, whose image of the irrelevant ideal is the unit ideal,
into a morphism `X ⟶ Proj 𝒜`. This file identifies a situation in which that morphism is a
**monomorphism**: when `X` is affine, `f` is surjective, and `f t = 1` for some `t` homogeneous of
degree one.

The mechanism is Mathlib's own `AlgebraicGeometry.Proj.fromOfGlobalSections_resLE`: over the
standard open `D₊(t)` the morphism is `AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections`, and
that morphism is, by construction, a composition of isomorphisms with `Spec` of the ring
homomorphism

`(𝒜_t)₀ ⟶ Γ(X, 𝒪_X)_{f t}`,  `a / tⁿ ↦ f a / (f t)ⁿ`.

For `t` of degree one the numerators `a` range over *every* degree, so the image of that ring
homomorphism is the whole image of `f`; with `f t = 1` the denominators are units, and the ring
homomorphism is therefore surjective as soon as `f` is. A `Spec` of a surjective ring homomorphism
is a closed immersion, hence a monomorphism; and `f t = 1` also says `X_{f t} = X`, so the
restriction over `D₊(t)` is the whole of the morphism up to an isomorphism.

The degree-one hypothesis is not cosmetic: an element of `(𝒜_t)₀` is a fraction whose numerator
lies in `𝒜 (n • deg t)`, so for `deg t > 1` the image of the chart comparison only sees the
degrees that are multiples of `deg t` and the conclusion fails.

## Main results

* `AlgebraicGeometry.Proj.surjective_awayMap_algebraMap`: the chart comparison
  `(𝒜_t)₀ ⟶ R_{1}` is surjective when `f` is surjective, `t` is of degree one and `f t = 1`.
* `AlgebraicGeometry.Proj.isClosedImmersion_toBasicOpenOfGlobalSections`: under the same
  hypotheses the chart morphism `X_{f t} ⟶ D₊(t)` is a closed immersion.
* `AlgebraicGeometry.Proj.mono_fromOfGlobalSections`: **the morphism `X ⟶ Proj 𝒜` is a
  monomorphism.**

## Implementation notes

`AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections` takes its target element as an implicit
argument fixed by a hypothesis `f t = x`; the lemmas here therefore carry both that hypothesis
and `x = 1`, so that they apply to Mathlib's `fromOfGlobalSections_resLE`, which instantiates the
first with `rfl`.

Instance search does not find `IsIso (X.toSpecΓ ∣_ PrimeSpectrum.basicOpen x)` — not even with
`IsIso X.toSpecΓ` in context, while the same goal for a generic open of a generic target is found
immediately. `AlgebraicGeometry.IsZariskiLocalAtTarget.restrict` supplies it, at
`IsClosedImmersion` directly, with no transparency option.

## References

* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
-/

@[expose] public section

open CategoryTheory Limits HomogeneousLocalization

universe u

namespace AlgebraicGeometry.Proj

variable {σ A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **The chart comparison of a morphism defined by global sections is surjective.** For `t`
homogeneous of degree one with `f t = 1`, the ring homomorphism `(𝒜_t)₀ ⟶ R_1` sending `a / tⁿ`
to `f a` is surjective as soon as `f` is: a preimage of `f a` is obtained by splitting `a` into
its homogeneous components `a_d` and adding up the fractions `a_d / t ^ d`, which are legitimate
elements of `(𝒜_t)₀` precisely because `t` has degree one. -/
theorem surjective_awayMap_algebraMap {R : Type u} [CommRing R] (f : A →+* R)
    (hf : Function.Surjective f) {t : A} (ht : t ∈ 𝒜 1) (H : f t = 1)
    (hpow : Submonoid.powers t ≤ Submonoid.comap f (Submonoid.powers (1 : R))) :
    Function.Surjective ((IsLocalization.map (Localization.Away (1 : R)) f hpow).comp
      (algebraMap (Away 𝒜 t) (Localization.Away t))) := by
  have key : ∀ (n : ℕ) (b : A) (hb : b ∈ 𝒜 (n • 1)),
      ((IsLocalization.map (Localization.Away (1 : R)) f hpow).comp
        (algebraMap (Away 𝒜 t) (Localization.Away t))) (Away.mk 𝒜 ht n b hb)
        = algebraMap R (Localization.Away (1 : R)) (f b) := by
    intro n b hb
    have hsub : (⟨f (t ^ n), hpow (by exact ⟨n, rfl⟩)⟩ : Submonoid.powers (1 : R)) = 1 :=
      Subtype.ext (by simp [map_pow, H])
    simp only [RingHom.coe_comp, Function.comp_apply, HomogeneousLocalization.algebraMap_apply,
      Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk']
    rw [show (⟨f (t ^ n), _⟩ : Submonoid.powers (1 : R)) = 1 from hsub, IsLocalization.mk'_one]
  intro y
  obtain ⟨⟨g, m⟩, hgm⟩ := IsLocalization.surj (Submonoid.powers (1 : R)) y
  obtain ⟨k, hk⟩ := m.2
  have hm1 : (m : R) = 1 := by simp [← hk]
  have hy : y = algebraMap R (Localization.Away (1 : R)) g := by simpa [hm1] using hgm
  obtain ⟨a, rfl⟩ := hf g
  classical
  refine ⟨∑ i ∈ DFinsupp.support ((DirectSum.decompose 𝒜) a),
    Away.mk 𝒜 ht i ((DirectSum.decompose 𝒜 a) i) (by simp), ?_⟩
  rw [hy, map_sum]
  simp only [key]
  conv_rhs => rw [← DirectSum.sum_support_decompose 𝒜 a]
  rw [map_sum, map_sum]

/-- **The chart of a morphism defined by global sections is a closed immersion**, for `X` affine,
`f` surjective and `f t = 1` with `t` homogeneous of degree one.
`AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections` is by construction a composition of
isomorphisms with `Spec` of the chart comparison, which is surjective by
`AlgebraicGeometry.Proj.surjective_awayMap_algebraMap`. -/
theorem isClosedImmersion_toBasicOpenOfGlobalSections {X : Scheme.{u}} [IsAffine X]
    (f : A →+* Γ(X, ⊤)) (hf : Function.Surjective f) {t : A} (ht : t ∈ 𝒜 1)
    {x : Γ(X, ⊤)} (H : f t = x) (hx : x = 1) :
    IsClosedImmersion (toBasicOpenOfGlobalSections 𝒜 f H Nat.one_pos ht) := by
  subst hx
  have hpow : Submonoid.powers t ≤ Submonoid.comap f (Submonoid.powers (1 : Γ(X, ⊤))) := by
    rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers]
    simp [H]
  have hspec : IsClosedImmersion (Spec.map (CommRingCat.ofHom
      ((IsLocalization.map (Localization.Away (1 : Γ(X, ⊤))) f hpow).comp
        (algebraMap (Away 𝒜 t) (Localization.Away t))))) :=
    IsClosedImmersion.spec_of_surjective _ (surjective_awayMap_algebraMap 𝒜 f hf ht H hpow)
  have hres : IsClosedImmersion (X.toSpecΓ ∣_ PrimeSpectrum.basicOpen (1 : Γ(X, ⊤))) :=
    IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion) inferInstance _
  simp only [toBasicOpenOfGlobalSections]
  infer_instance

/-- **A morphism to `Proj` defined by global sections is a monomorphism**, provided the source is
affine, the ring homomorphism is surjective, and some homogeneous element of degree one is sent to
`1`.

The restriction of the morphism over `D₊(t)` is a closed immersion by
`AlgebraicGeometry.Proj.isClosedImmersion_toBasicOpenOfGlobalSections`, and `f t = 1` makes
`X_{f t}` the whole of `X`, so the morphism itself factors as an isomorphism followed by that
closed immersion followed by the open immersion `D₊(t) ⟶ Proj 𝒜`. -/
theorem mono_fromOfGlobalSections {X : Scheme.{u}} [IsAffine X] (f : A →+* Γ(X, ⊤))
    (hirr : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    (hf : Function.Surjective f) {t : A} (ht : t ∈ 𝒜 1) (hft : f t = 1) :
    Mono (fromOfGlobalSections 𝒜 f hirr) := by
  have hV : X.basicOpen (f t) = ⊤ := by rw [hft]; exact X.basicOpen_one
  have hci : IsClosedImmersion
      (toBasicOpenOfGlobalSections 𝒜 f (rfl : f t = f t) Nat.one_pos ht) :=
    isClosedImmersion_toBasicOpenOfGlobalSections 𝒜 f hf ht rfl hft
  have hle := (fromOfGlobalSections_preimage_basicOpen 𝒜 f hirr Nat.one_pos ht).ge
  have hmono_res : Mono ((fromOfGlobalSections 𝒜 f hirr).resLE _ _ hle) := by
    rw [fromOfGlobalSections_resLE 𝒜 f hirr Nat.one_pos ht]
    infer_instance
  have hcomp : Mono ((X.basicOpen (f t)).ι ≫ fromOfGlobalSections 𝒜 f hirr) := by
    rw [← Scheme.Hom.resLE_comp_ι (fromOfGlobalSections 𝒜 f hirr) hle]
    infer_instance
  have hiso : IsIso (X.basicOpen (f t)).ι := by
    rw [← Scheme.isoOfEq_hom_ι X hV, ← Scheme.topIso_hom]
    infer_instance
  have hfac : fromOfGlobalSections 𝒜 f hirr = inv (X.basicOpen (f t)).ι
      ≫ ((X.basicOpen (f t)).ι ≫ fromOfGlobalSections 𝒜 f hirr) := by
    rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rw [hfac]
  infer_instance

end AlgebraicGeometry.Proj

end
