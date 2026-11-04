module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.SurjectiveReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceCoproduct
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.DescentFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.EtaleSectionDecomposition

/-!
# Splitting off a section in the inductive step of the affine case of topological invariance

Let `f : X ⟶ Y` be a universal homeomorphism of affine schemes. The affine case of the
correspondence of Stacks Project, Tag 04E0 asserts that every affine scheme étale over `X`
descends along `f`, and the source proves it by induction on a bound `n` for the degrees of the
fibres, stated here as `Stacks.Etale.EssSurjAffineEtalePullbackBounded`.

This file carries out the part of the source's inductive step that *drops the bound*, and
reduces the step to a single descent along an étale covering.

## The two steps

`Stacks.Etale.exists_affine_etale_pullback_iso_of_section` is the splitting. If the étale
`p : U ⟶ X` admits a **section** `s : X ⟶ U`, then no induction on coverings is needed at all:
the section is automatically an open immersion
(`AlgebraicGeometry.isOpenImmersion_of_section_of_etale`), so `U` is the disjoint union of the
range of `s` — a copy of `X`, which descends to `Y` itself — and the off-section part, whose
fibre degrees are bounded by `n` rather than `n + 1`
(`AlgebraicGeometry.boundsFiberDegrees_offSection`) and which therefore descends by the
inductive hypothesis. The two descents are assembled by
`Stacks.Etale.exists_etale_pullback_iso_of_isCompl`.

`Stacks.Etale.exists_affine_etale_descent_of_surjective` is the reduction of the step to one
descent. A surjective étale `p : U ⟶ X` is dominated, by Stacks Project, Tag 04DW in the affine
form `Stacks.EtaleCohomology.exists_isAffine_etale_surjective_of_hasPropertyC`, by the base
change `W_X := X ×_Y W` of an affine scheme `W` étale over `Y`; the dominating morphism
`a : W_X ⟶ U` over `X` is exactly a section of the base change `U ×_X W_X ⟶ W_X` of `p`, and
`W_X ⟶ W` is again a universal homeomorphism of affine schemes. So the splitting applies over
`W_X` and produces an affine scheme `T` étale over `W` whose base change to `W_X` is
`U ×_X W_X`. What is left of the step is to descend `T` from `W` to `Y` along `W ⟶ Y`, which is
surjective precisely because `p` is — see
`Stacks.Etale.essSurjAffineEtalePullbackBounded_of_surjective`.

## Main results

* `Stacks.Etale.exists_affine_etale_pullback_iso_of_section` — **the splitting.** An affine
  scheme étale over `X` with fibre degrees bounded by `n + 1` which admits a section descends
  along `f`, granted the affine case for the bound `n`.
* `Stacks.Etale.exists_affine_etale_descent_of_surjective` — **the inductive step up to one
  descent.** The data the source's step produces before invoking effectivity of affine descent.

## Implementation notes

Neither statement carries a tag: both are steps inside the second proof of Stacks Project,
Tag 04DZ, and the tag 04E0 whose essential surjectivity they serve is not closed by them. The
obligation that remains after this file is the descent of `T` along the surjective étale
`W ⟶ Y`; it is discharged in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.DescentEffective`, by
`Stacks.Etale.exists_affine_etale_pullback_iso_of_descentIso`, where effectivity enters as
Stacks Project, Tag 02W8 rather than as the source's Tag 0245.

The affineness of the descended scheme is not produced by
`Stacks.Etale.exists_etale_pullback_iso_of_isCompl`, which knows nothing about affineness; it is
recovered afterwards from `Stacks.Etale.isAffine_of_isAffine_pullback`, Stacks Project,
Tag 05YU, exactly as in `Stacks.Etale.essSurjAffineEtalePullbackBounded_of_surjective`.

## References

* [Stacks Project, Tag 04E0](https://stacks.math.columbia.edu/tag/04E0)
* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 04DW](https://stacks.math.columbia.edu/tag/04DW)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Etale

variable {X Y : Scheme.{u}}

/-! ### The splitting -/

/-- **Splitting off a section drops the bound.** Let `f : X ⟶ Y` be a universal homeomorphism of
affine schemes, let `p : U ⟶ X` be étale with `U` affine and with the degrees of its fibres
bounded by `n + 1`, and suppose that `p` admits a section `s : X ⟶ U`. If the affine case of
Stacks Project, Tag 04E0 holds for the bound `n`, then `U` is, over `X`, the base change along
`f` of an affine scheme étale over `Y`.

This is the heart of the inductive step of the second proof of Stacks Project, Tag 04DZ. A
section of an étale morphism is an open immersion, by
`AlgebraicGeometry.isOpenImmersion_of_section_of_etale`, so the range of `s` and the off-section
part of `U` are complementary open subschemes
(`AlgebraicGeometry.isCompl_opensRange_offSection`). The range of `s` is a copy of `X` over `X`,
which descends to `Y` itself by
`Stacks.Etale.exists_affine_etale_pullback_iso_of_isOpenImmersion` applied to the identity; and
the off-section part is affine (`AlgebraicGeometry.isAffine_offSection`), étale over `X` (its
map to `X` is an open immersion followed by `p`, so Mathlib's instances apply) and has its fibre
degrees bounded by `n` (`AlgebraicGeometry.boundsFiberDegrees_offSection`), so it descends by the
inductive hypothesis. `Stacks.Etale.exists_etale_pullback_iso_of_isCompl` assembles the two. -/
theorem exists_affine_etale_pullback_iso_of_section (n : ℕ)
    (ih : EssSurjAffineEtalePullbackBounded.{u} n) (f : X ⟶ Y)
    [UniversalHomeomorphism f] [IsAffine X] [IsAffine Y]
    {U : Scheme.{u}} (p : U ⟶ X) [Etale p] [IsAffine U] (s : X ⟶ U)
    (hs : s ≫ p = 𝟙 X) (hdeg : BoundsFiberDegrees p ((n + 1 : ℕ) : ℤ)) :
    ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (_ : IsAffine V) (e : pullback q f ≅ U),
      e.hom ≫ p = pullback.snd q f := by
  have hsoi : IsOpenImmersion s := isOpenImmersion_of_section_of_etale p s hs
  -- the range of the section and the off-section part are complementary
  have hcompl : IsCompl s.opensRange ((offSection p s hs).ι).opensRange := by
    rw [Scheme.Opens.opensRange_ι]
    exact isCompl_opensRange_offSection p s hs
  -- the section piece: a copy of `X`, descending to `Y` itself
  have h₁ : ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (e : pullback q f ≅ X),
      e.hom ≫ (s ≫ p) = pullback.snd q f := by
    obtain ⟨V, q, hq, -, e, he⟩ :=
      exists_affine_etale_pullback_iso_of_isOpenImmersion f (𝟙 X) inferInstance
    exact ⟨V, q, hq, e, by rwa [hs]⟩
  -- the off-section piece: bounded by `n`, so the inductive hypothesis applies
  have h₂ : ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q)
      (e : pullback q f ≅ (offSection p s hs).toScheme),
      e.hom ≫ ((offSection p s hs).ι ≫ p) = pullback.snd q f := by
    obtain ⟨V, q, hq, -, e, he⟩ := ih f inferInstance inferInstance inferInstance
      (offSection p s hs).toScheme ((offSection p s hs).ι ≫ p) inferInstance
      (isAffine_offSection p s hs) (boundsFiberDegrees_offSection p s hs n hdeg)
    exact ⟨V, q, hq, e, he⟩
  obtain ⟨V, q, hq, e, he⟩ :=
    exists_etale_pullback_iso_of_isCompl f p s (offSection p s hs).ι hcompl h₁ h₂
  exact ⟨V, q, hq, isAffine_of_isAffine_pullback f q (IsAffine.of_isIso e.hom), e, he⟩

/-! ### The inductive step up to one descent -/

/-- **The inductive step of the affine case, up to a single descent along `W ⟶ Y`.** Let
`f : X ⟶ Y` be a universal homeomorphism of affine schemes and let `p : U ⟶ X` be a surjective
étale morphism with `U` affine and the degrees of its fibres bounded by `n + 1`. Granted the
affine case of Stacks Project, Tag 04E0 for the bound `n`, there is an affine scheme `W` étale
and **surjective** over `Y` and an affine scheme `T` étale over `W` whose base change along
`W ×_Y X ⟶ W` is, over `W ×_Y X`, the base change of `U` along `W ×_Y X ⟶ X`.

Descending `T` along `W ⟶ Y` — by effectivity of affine descent, Stacks Project, Tag 0245 —
and identifying the base change of the result along `f` with `U` is all that remains of the
source's inductive step, and hence of the essential surjectivity of Stacks Project, Tag 04E0.

Stacks Project, Tag 04DW, in the affine form
`Stacks.EtaleCohomology.exists_isAffine_etale_surjective_of_hasPropertyC`, dominates `U` by the
base change `W_X` of an affine `W` étale over `Y` through a morphism `a : W_X ⟶ U` over `X`.
Such an `a` is the same thing as a section of the base change `U ×_X W_X ⟶ W_X` of `p`, so
`Stacks.Etale.exists_affine_etale_pullback_iso_of_section` applies to the universal
homeomorphism `W_X ⟶ W` of affine schemes and yields `T`. Surjectivity of `W ⟶ Y` is forced by
that of `p`: the composite `W_X ⟶ U ⟶ X ⟶ Y` is surjective and factors through `W`. -/
theorem exists_affine_etale_descent_of_surjective (n : ℕ)
    (ih : EssSurjAffineEtalePullbackBounded.{u} n) (f : X ⟶ Y)
    [UniversalHomeomorphism f] [IsAffine X] [IsAffine Y]
    {U : Scheme.{u}} (p : U ⟶ X) [Etale p] [IsAffine U] [Surjective p]
    (hdeg : BoundsFiberDegrees p ((n + 1 : ℕ) : ℤ)) :
    ∃ (W : Scheme.{u}) (w : W ⟶ Y) (_ : Etale w) (_ : IsAffine W) (_ : Surjective w)
      (T : Scheme.{u}) (t : T ⟶ W) (_ : Etale t) (_ : IsAffine T)
      (e : pullback t (pullback.snd f w) ≅ pullback p (pullback.fst f w)),
        e.hom ≫ pullback.snd p (pullback.fst f w) = pullback.snd t (pullback.snd f w) := by
  -- Tag 04DW for a universal homeomorphism, refined to an affine dominating scheme
  obtain ⟨W, w, hw, hWaff, a, hasurj, hacomm⟩ :=
    EtaleCohomology.exists_isAffine_etale_surjective_of_hasPropertyC f
      (hasPropertyC_of_universalHomeomorphism f) p inferInstance
  -- `W_X ⟶ W` is a universal homeomorphism of affine schemes
  have hUH : UniversalHomeomorphism (pullback.snd f w) := by
    rw [universalHomeomorphism_iff]
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f w) ((universalHomeomorphism_iff f).mp inferInstance)
  -- `W ⟶ Y` is surjective because `p` is
  obtain ⟨-, -, hfsurj⟩ :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective f).mp inferInstance
  have hfstsurj : Surjective (pullback.fst f w) := by
    rw [← hacomm]
    infer_instance
  have hcompsurj : Surjective (pullback.snd f w ≫ w) := by
    rw [← pullback.condition]
    infer_instance
  have hwsurj : Surjective w := Surjective.of_comp (pullback.snd f w) w
  -- the base change of `p` to `W_X`, and the section of it given by `a`
  have hdegbc : BoundsFiberDegrees (pullback.snd p (pullback.fst f w)) ((n + 1 : ℕ) : ℤ) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {_ _ : Scheme.{u}} (r : _ ⟶ _) ↦ BoundsFiberDegrees r ((n + 1 : ℕ) : ℤ))
      (IsPullback.of_hasPullback p (pullback.fst f w)) hdeg
  -- the splitting over `W_X`
  exact ⟨W, w, hw, hWaff, hwsurj,
    exists_affine_etale_pullback_iso_of_section n ih (pullback.snd f w)
      (pullback.snd p (pullback.fst f w))
      (pullback.lift a (𝟙 (pullback f w)) (by rwa [Category.id_comp]))
      (pullback.lift_snd _ _ _) hdegbc⟩

end Stacks.Etale

end

end
