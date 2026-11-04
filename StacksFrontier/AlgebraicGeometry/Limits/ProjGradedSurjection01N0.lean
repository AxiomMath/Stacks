module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Blowup.ProjBaseChangeGlobal

/-!
# `Proj` of a surjective graded ring homomorphism is a closed immersion

**Stacks 01N0 part (2)** says that if `ψ : A ⟶ B` is a homomorphism of graded rings which is
surjective in all large degrees, then the induced morphism `r_ψ : Proj B ⟶ Proj A` is defined
everywhere and is a closed immersion. This file proves the part of that statement which applies
when `ψ` is surjective outright, which is how the Stacks proof of the Segre embedding (01WD) and
the construction of closed subschemes of projective space (01N1) use it.

The proof is the Stacks proof, read through Mathlib's `AlgebraicGeometry.Proj.map`. A graded ring
homomorphism which is surjective is surjective on each graded piece, because the decomposition of
a preimage decomposes its image; hence the irrelevant ideal of `B` is contained in the image of
the irrelevant ideal of `A`, which is exactly the hypothesis under which `Proj.map` is defined on
all of `Proj B`; and hence the induced map on the degree-zero parts of the away-localizations,
`A_(s) ⟶ B_(ψ s)`, is surjective, because a fraction `b / ψ(s)^n` is the image of `a / s^n` for
any homogeneous `a` of the same degree lifting `b`. Being a closed immersion is Zariski-local on
the target, and over the standard affine chart `D₊(s)` the morphism is `Spec` of that surjection:
the relevant square is cartesian by `AlgebraicGeometry.Proj.isPullback_awayι_map`.

## Main results

* `AlgebraicGeometry.Proj.gradedAddHom_surjective_of_surjective`: a surjective graded ring
  homomorphism is surjective in every degree.
* `AlgebraicGeometry.Proj.irrelevant_le_map_of_surjective`: hence the hypothesis of
  `AlgebraicGeometry.Proj.map` holds.
* `AlgebraicGeometry.Proj.away_map_surjective_of_surjective`: hence the induced map on
  away-localizations in degree zero is surjective.
* `AlgebraicGeometry.Proj.isClosedImmersion_map_of_surjective'`: **Stacks 01N0 part (2) for a
  surjective homomorphism**, `Proj` of a graded surjection is a closed immersion.

## Implementation notes

No `@[stacks 01N0]` attribute is attached. Tag 01N0 is a three-part statement about the triple
`(U(ψ), r_ψ, θ)` of Stacks 01MY, whose third part concerns the comparison maps
`θ : r_ψ^* O_X(n) ⟶ O_Y(n)` of twisting sheaves, which are not formalized here; and its
hypothesis is surjectivity of `A_d ⟶ B_d` for all `d ≫ 0`, which is weaker than the surjectivity
of `ψ` assumed here. Part (3) itself is formalized elsewhere and carries the attribute there:
surjectivity of `θ` in `StacksFrontier/AlgebraicGeometry/ProjTwistEpi/Basic.lean`, and its
injectivity on the canonical twisted sections, for `𝒜` generated in degree one, in
`StacksFrontier/AlgebraicGeometry/ProjSaturation/QuotientComparison.lean`. What is proved is
part (2) under the stronger hypothesis, for Mathlib's `AlgebraicGeometry.Proj.map`, which is
01MY's `r_ψ` in the case `U(ψ) = Proj B` that part (1) of 01N0 asserts.

## References

* [Stacks Project, Tag 01N0](https://stacks.math.columbia.edu/tag/01N0)
* [Stacks Project, Tag 01N1](https://stacks.math.columbia.edu/tag/01N1)
* [Stacks Project, Tag 01WD](https://stacks.math.columbia.edu/tag/01WD)
-/

@[expose] public section

open CategoryTheory Limits HomogeneousIdeal HomogeneousLocalization Graded CommRingCat

namespace AlgebraicGeometry.Proj

universe u

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- A homogeneous element of the target of a surjective graded homomorphism has a homogeneous
preimage of the same degree. -/
private theorem exists_mem_map_eq_of_surjective (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f)
    {i : ℕ} {b : B} (hb : b ∈ ℬ i) : ∃ a ∈ 𝒜 i, f a = b := by
  obtain ⟨a, ha⟩ := hf b
  exact ⟨DirectSum.decompose 𝒜 a i, SetLike.coe_mem _, by
    rw [GradedRingHom.map_directSumDecompose, ha, DirectSum.decompose_of_mem_same ℬ hb]⟩

/-- **A surjective graded ring homomorphism is surjective in every degree.** Given `b ∈ ℬ i` and
any preimage `a` of `b`, the degree-`i` component of `a` is a preimage of `b` lying in `𝒜 i`,
because a graded homomorphism commutes with the graded decomposition. -/
theorem gradedAddHom_surjective_of_surjective (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f)
    (i : ℕ) : Function.Surjective (f.gradedAddHom i) := by
  intro b
  obtain ⟨a, ha, hab⟩ := exists_mem_map_eq_of_surjective f hf b.2
  exact ⟨⟨a, ha⟩, Subtype.ext hab⟩

/-- **A surjective graded ring homomorphism satisfies the hypothesis of
`AlgebraicGeometry.Proj.map`**: the irrelevant ideal of the target is contained in the image of
the irrelevant ideal of the source, so the induced morphism of projective spectra is defined on
all of `Proj ℬ`. This is Stacks 01N0 part (1) for a surjective homomorphism. -/
theorem irrelevant_le_map_of_surjective (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) :
    ℬ₊ ≤ 𝒜₊.map f := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi x hx
  obtain ⟨a, ha, rfl⟩ := exists_mem_map_eq_of_surjective f hf hx
  exact Ideal.mem_map_of_mem _ (mem_irrelevant_of_mem _ hi ha)

/-- **The induced map of away-localizations in degree zero is surjective.** An element of
`B_(ψ s)` is a fraction `b / ψ(s)^n` with `b` homogeneous of degree `n * deg s`; lifting `b` to a
homogeneous element of the same degree, which is possible because `ψ` is surjective in every
degree, exhibits the fraction as an image. -/
theorem away_map_surjective_of_surjective (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) {i : ℕ}
    {s : A} (hs : s ∈ 𝒜 i) : Function.Surjective (Away.map f s) := by
  intro y
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective ℬ (map_mem f hs) y
  obtain ⟨a, ha, rfl⟩ := exists_mem_map_eq_of_surjective f hf hb
  exact ⟨Away.mk 𝒜 hs n a ha, by rw [Away.map_mk]⟩

/-- A morphism property that respects isomorphisms holds of the canonical base change
`pullback.snd f g` as soon as it holds of the second leg of *some* cartesian square on the
cospan `f`, `g`. This is `CategoryTheory.IsPullback.isoPullback` plus
`CategoryTheory.MorphismProperty.cancel_left_of_respectsIso`, isolated as a lemma so that it is
applied to a goal in which no coercion has to be unfolded. -/
theorem _root_.AlgebraicGeometry.pullback_snd_of_isPullback
    {P : MorphismProperty Scheme.{u}} [P.RespectsIso] {W X Y Z : Scheme.{u}} {fst : W ⟶ X}
    {snd : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (hs : P snd) :
    P (pullback.snd f g) := by
  rw [← h.isoPullback_hom_snd] at hs
  exact (MorphismProperty.cancel_left_of_respectsIso P h.isoPullback.hom _).mp hs

/-- **Stacks 01N0 part (2) for a surjective homomorphism: `Proj` of a graded surjection is a
closed immersion.** Being a closed immersion is Zariski-local on the target, and over the
standard affine chart `D₊(s)` of `Proj 𝒜` the morphism is `Spec` of the surjection
`A_(s) ⟶ B_(ψ s)`, the relevant square being cartesian by
`AlgebraicGeometry.Proj.isPullback_awayι_map`.

This supplies the side condition of `AlgebraicGeometry.Proj.map` itself, from surjectivity
alone; `AlgebraicGeometry.Proj.isClosedImmersion_map_of_surjective` takes the side condition as
a hypothesis, so it applies to any witness of it. -/
theorem isClosedImmersion_map_of_surjective' (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) :
    IsClosedImmersion (Proj.map f (irrelevant_le_map_of_surjective f hf)) := by
  refine IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion)
    (Proj.affineOpenCover 𝒜).openCover ?_
  rintro ⟨i, a⟩
  exact pullback_snd_of_isPullback
    (Proj.isPullback_awayι_map f (irrelevant_le_map_of_surjective f hf) i.2 (a : A) a.2).flip
    (IsClosedImmersion.spec_of_surjective _ (away_map_surjective_of_surjective f hf a.2))

end AlgebraicGeometry.Proj

end
