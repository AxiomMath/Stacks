module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# `Proj` as a scheme over `Spec` of its degree-zero part

For a graded ring `𝒜` the scheme `Proj 𝒜` comes with its structure morphism
`AlgebraicGeometry.Proj.toSpecZero` to `Spec (𝒜 0)`, and a graded ring homomorphism
`f : 𝒜 →+*ᵍ ℬ` with `ℬ₊ ≤ 𝒜₊.map f` induces `AlgebraicGeometry.Proj.map f : Proj ℬ ⟶ Proj 𝒜`.
This file proves two relations between them.

The first is that `Proj.map f` is a morphism *over* `Spec` of the degree-zero parts, that is the
square

```
Proj ℬ  ⟶ Spec (ℬ 0)
  |             |
  v             v
Proj 𝒜  ⟶ Spec (𝒜 0)
```

commutes, where the right-hand map is `Spec` of the degree-zero component of `f`.

The second is that the part of `Proj 𝒜` lying over a standard open `D(g)` of the base, for `g`
of degree zero, is the standard open `D₊(g)` of `Proj 𝒜`.

## Main results

* `AlgebraicGeometry.Proj.map_toSpecZero`: `Proj.map f` is a morphism over `Spec` of the
  degree-zero parts.
* `AlgebraicGeometry.Proj.map_congr`: `Proj.map` depends only on the graded ring homomorphism,
  not on the proof of the hypothesis on irrelevant ideals.
* `AlgebraicGeometry.Proj.opens_eq_of_awayι_preimage_eq`: two opens of `Proj 𝒜` agree as soon as
  they agree on every standard affine chart.
* `AlgebraicGeometry.Proj.awayι_preimage_basicOpen_zero`: the standard open `D₊(g)` of a
  degree-zero `g`, read in the chart `Spec (A_f)₀`, is the standard open of `g / 1`.
* `AlgebraicGeometry.Proj.toSpecZero_preimage_basicOpen`: the preimage of `D(g)` under
  `Proj 𝒜 ⟶ Spec (𝒜 0)` is `D₊(g)`.

## References

* [Stacks Project, Tag 01M3](https://stacks.math.columbia.edu/tag/01M3)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public section

open CategoryTheory Limits HomogeneousIdeal HomogeneousLocalization Graded

universe u

namespace AlgebraicGeometry.Proj

section map

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- `Proj.map f hf` depends only on the graded ring homomorphism `f`, not on the proof `hf` of
`ℬ₊ ≤ 𝒜₊.map f`. -/
theorem map_congr {f g : 𝒜 →+*ᵍ ℬ} (h : f = g) (hf : ℬ₊ ≤ 𝒜₊.map f) (hg : ℬ₊ ≤ 𝒜₊.map g) :
    Proj.map f hf = Proj.map g hg := by
  subst h; rfl

/-- Sending a degree-zero element `a` of `𝒜` to the fraction `f a / 1` in `Away ℬ (f s)` can be
done in either order: invert `s` first and then apply `f`, or apply `f` first and then invert
`f s`. -/
theorem awayMap_comp_fromZeroRingHom (f : 𝒜 →+*ᵍ ℬ) (s : A) :
    (Away.map f s).comp (fromZeroRingHom 𝒜 (Submonoid.powers s)) =
      (fromZeroRingHom ℬ (Submonoid.powers (f s))).comp f.gradedZeroRingHom := by
  ext a
  have h1 : fromZeroRingHom 𝒜 (Submonoid.powers s) a =
      HomogeneousLocalization.mk ⟨0, a, 1, one_mem _⟩ := rfl
  have h2 : fromZeroRingHom ℬ (Submonoid.powers (f s)) (f.gradedZeroRingHom a) =
      HomogeneousLocalization.mk ⟨0, ⟨f a, map_mem f a.2⟩, 1, one_mem _⟩ := rfl
  rw [RingHom.comp_apply, RingHom.comp_apply, h1, h2, HomogeneousLocalization.Away.map,
    HomogeneousLocalization.map_mk]
  simp [HomogeneousLocalization.val_mk]

/-- The chart-local form of `AlgebraicGeometry.Proj.map_toSpecZero`: the two composites agree
after restricting along the open immersion `Spec (Away ℬ (f s)) ⟶ Proj ℬ` attached to a
homogeneous `s : A` of positive degree. -/
theorem awayι_map_toSpecZero (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) {i : ℕ} (hi : 0 < i) (s : A)
    (hs : s ∈ 𝒜 i) :
    awayι ℬ (f s) (map_mem f hs) hi ≫ (Proj.map f hf ≫ toSpecZero 𝒜) =
      awayι ℬ (f s) (map_mem f hs) hi ≫
        (toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom f.gradedZeroRingHom)) := by
  rw [awayι_comp_map_assoc f hf hi s hs, awayι_toSpecZero, ← Category.assoc, awayι_toSpecZero,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, awayMap_comp_fromZeroRingHom]

/-- **`Proj.map` is a morphism over `Spec` of the degree-zero parts.** For a graded ring
homomorphism `f : 𝒜 →+*ᵍ ℬ` whose image contains enough of the irrelevant ideal, the square
formed by `Proj.map f`, the two structure morphisms `Proj.toSpecZero` and `Spec` of the
degree-zero component of `f` commutes. -/
@[reassoc]
theorem map_toSpecZero (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) :
    Proj.map f hf ≫ toSpecZero 𝒜 =
      toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom f.gradedZeroRingHom) :=
  (mapAffineOpenCover f hf).openCover.hom_ext _ _ fun ⟨i, x⟩ ↦
    awayι_map_toSpecZero f hf i.2 (x : A) x.2

end map

section basicOpenZero

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
  [GradedRing 𝒜]

/-- Two opens of `Proj 𝒜` are equal as soon as they have the same preimage in every standard
affine chart `Spec (A_f)₀`, `f` homogeneous of positive degree. -/
theorem opens_eq_of_awayι_preimage_eq {U V : (Proj 𝒜).Opens}
    (h : ∀ {i : ℕ} (hi : 0 < i) (f : A) (hf : f ∈ 𝒜 i),
      awayι 𝒜 f hf hi ⁻¹ᵁ U = awayι 𝒜 f hf hi ⁻¹ᵁ V) : U = V := by
  ext x
  obtain ⟨j, y, rfl⟩ := (affineOpenCover 𝒜).openCover.exists_eq x
  obtain ⟨i, a⟩ := j
  exact congr(y ∈ $(h i.2 (a : A) a.2)).to_iff

/-- The composite `Spec (A_f)₀ ⟶ Proj 𝒜 ⟶ Spec (𝒜 0)` pulls the standard open of a degree-zero
`g` back to the standard open of the fraction `g / 1`. -/
theorem awayι_toSpecZero_preimage_basicOpen (f : A) {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)
    (g : 𝒜 0) :
    (awayι 𝒜 f f_deg hm ≫ toSpecZero 𝒜) ⁻¹ᵁ PrimeSpectrum.basicOpen g =
      PrimeSpectrum.basicOpen (fromZeroRingHom 𝒜 (Submonoid.powers f) g) := by
  rw [awayι_toSpecZero]
  rfl

/-- For `f` homogeneous of degree `m` and `g` of degree zero, the element of `(A_f)₀` that
exhibits `(A_{fg})₀` as a localization of `(A_f)₀` is the `m`-th power of the fraction
`g / 1`. -/
theorem isLocalizationElem_mul_eq_pow (f : A) {m : ℕ} (f_deg : f ∈ 𝒜 m) (g : 𝒜 0)
    (hfg : f * (g : A) ∈ 𝒜 m) :
    Away.isLocalizationElem f_deg hfg = fromZeroRingHom 𝒜 (Submonoid.powers f) g ^ m := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_pow]
  show Localization.mk _ _ = _
  rw [show (fromZeroRingHom 𝒜 (Submonoid.powers f) g).val = Localization.mk (g : A) 1 from rfl,
    Localization.mk_pow, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by push_cast; ring⟩

/-- The standard open `D₊(g)` of a degree-zero `g`, read in the chart `Spec (A_f)₀`, is the
standard open of the fraction `g / 1`. -/
theorem awayι_preimage_basicOpen_zero (f : A) {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) (g : 𝒜 0) :
    awayι 𝒜 f f_deg hm ⁻¹ᵁ basicOpen 𝒜 (g : A) =
      PrimeSpectrum.basicOpen (fromZeroRingHom 𝒜 (Submonoid.powers f) g) := by
  have hfg : f * (g : A) ∈ 𝒜 m := by simpa using SetLike.mul_mem_graded f_deg g.2
  have h1 : awayι 𝒜 f f_deg hm ⁻¹ᵁ basicOpen 𝒜 (f * (g : A)) =
      awayι 𝒜 f f_deg hm ⁻¹ᵁ basicOpen 𝒜 (g : A) := by
    rw [basicOpen_mul, Scheme.Hom.preimage_inf, ← opensRange_awayι 𝒜 f f_deg hm,
      Scheme.Hom.preimage_opensRange, top_inf_eq]
  rw [← h1, awayι_preimage_basicOpen 𝒜 f_deg hm hfg hm, isLocalizationElem_mul_eq_pow 𝒜 f f_deg g,
    PrimeSpectrum.basicOpen_pow _ m hm]

/-- **The part of `Proj 𝒜` over a standard open of the base is a standard open.** For `g` in the
degree-zero part of `𝒜`, the preimage of `D(g) ⊆ Spec (𝒜 0)` under the structure morphism
`Proj.toSpecZero` is the standard open `D₊(g)` of `Proj 𝒜`. -/
theorem toSpecZero_preimage_basicOpen (g : 𝒜 0) :
    toSpecZero 𝒜 ⁻¹ᵁ PrimeSpectrum.basicOpen g = basicOpen 𝒜 (g : A) :=
  opens_eq_of_awayι_preimage_eq 𝒜 fun hi f hf ↦
    (awayι_toSpecZero_preimage_basicOpen 𝒜 f hf hi g).trans
      (awayι_preimage_basicOpen_zero 𝒜 f hf hi g).symm

end basicOpenZero

end AlgebraicGeometry.Proj

end
