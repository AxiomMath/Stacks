module

public import StacksFrontier.AlgebraicGeometry.Etale.UnramifiedTopological.Sections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.AffineCase
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.AffineDomination
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceCoproduct
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.EtaleSectionDecomposition

/-!
# Splitting off the section, and the descent over the dominating scheme

This file carries out the first half of the inductive step of the second proof of Stacks
Project, Tag 04DZ. Let `f : X ⟶ Y` be a universal homeomorphism, and let `p : U ⟶ X` be étale
and affine with `U` affine and with the degrees of its fibres bounded by `n + 1`. Neither `X`
nor `Y` has to be affine: the inductive step is reached, in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.AffineSurjectiveCase`,
only after the target has been restricted to the open image of `U`, which is not affine.

By `Stacks.Etale.exists_isAffine_etale_domination` there is an affine scheme `W` étale over `Y`
and a surjection `h : W_X ⟶ U` over `X`, where `W_X = X ×_Y W`. Base changing `p` along
`W_X ⟶ X` gives an étale morphism `U ×_X W_X ⟶ W_X` of affine schemes, and `h` turns into a
*section* of it. So `U ×_X W_X` splits as `W_X ⨿ R` with `R` the complement of the section, and
the degrees of the fibres of `R ⟶ W_X` are bounded by `n`
(`AlgebraicGeometry.boundsFiberDegrees_offSection`).

The affine case for the bound `n`, applied to the universal homeomorphism `W_X ⟶ W` — which is
a universal homeomorphism of *affine* schemes, which is why `W` had to be made affine — descends
`R` to a scheme étale over `W`. The copy of `W_X` descends trivially, and the two descents
assemble by `Stacks.Etale.exists_etale_pullback_iso_of_isCompl`. The result is an affine scheme
`V''` étale over `W` whose base change to `W_X` is `U ×_X W_X`, which is the input the descent
step of the source's proof consumes.

## Main results

* `Stacks.Etale.exists_isAffine_etale_over_of_boundsFiberDegrees_succ` — the statement above:
  from the affine case at the bound `n`, the data `W`, the surjection `h` and the scheme `V''`
  over `W` together with the identification of its base change with `U ×_X W_X`.

## Implementation notes

Affineness of `W_X`, of `U ×_X W_X` and of `R` is automatic: a universal homeomorphism is an
affine morphism, so `W_X ⟶ W` is affine and `W_X` is affine; `p` is an affine morphism, so
`U ×_X W_X ⟶ W_X` is affine and `U ×_X W_X` is affine; and `R` is an open
subscheme of `U ×_X W_X` whose point set is closed, hence a closed subscheme of an affine
scheme. Affineness of `V''` is recovered afterwards from affineness of its base change, by
`Stacks.Etale.isAffine_of_isAffine_pullback`.

The section of `U ×_X W_X ⟶ W_X` is `CategoryTheory.Limits.pullback.lift h (𝟙 W_X)`, which is
legitimate exactly because `h` is a morphism over `X`. The trivial descent of the copy of `W_X`
is the identity of `W`, whose base change is `W_X` by `CategoryTheory.IsPullback.of_id_snd`.

## References

* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 04DW](https://stacks.math.columbia.edu/tag/04DW)
* [Stacks Project, Tag 03WU](https://stacks.math.columbia.edu/tag/03WU)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Etale

open _root_.AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- **The first half of the inductive step of the second proof of Stacks Project, Tag 04DZ.**
Let `f : X ⟶ Y` be a universal homeomorphism, let `p : U ⟶ X` be étale and affine with `U`
affine, and suppose the degrees of the fibres of `p` are bounded by `n + 1`. Granted the
affine case of Stacks Project, Tag 04E0 for the bound `n`, there are an affine scheme `W` étale
over `Y`, a surjection `X ×_Y W ⟶ U` over `X`, and an affine scheme `V''` étale over `W` whose
base change along `X ×_Y W ⟶ W` is `U ×_X (X ×_Y W)` over `X ×_Y W`.

The surjection splits off a section of `U ×_X (X ×_Y W) ⟶ X ×_Y W`, the complement of the
section has fibre degrees bounded by `n` and descends by the induction hypothesis, and the two
pieces are reassembled by `Stacks.Etale.exists_etale_pullback_iso_of_isCompl`. -/
theorem exists_isAffine_etale_over_of_boundsFiberDegrees_succ (n : ℕ)
    (hn : EssSurjAffineEtalePullbackBounded.{u} n)
    (f : X ⟶ Y) [UniversalHomeomorphism f]
    {U : Scheme.{u}} (p : U ⟶ X) (hp : Etale p) (hU : IsAffine U) (hpaff : IsAffineHom p)
    (hdeg : BoundsFiberDegrees p ((n + 1 : ℕ) : ℤ)) :
    ∃ (W : Scheme.{u}) (w : W ⟶ Y) (_ : Etale w) (_ : IsAffine W) (h : pullback f w ⟶ U),
      Surjective h ∧ h ≫ p = pullback.fst f w ∧
      ∃ (V : Scheme.{u}) (q : V ⟶ W) (_ : Etale q) (_ : IsAffine V)
        (e : pullback q (pullback.snd f w) ≅ pullback p (pullback.fst f w)),
          e.hom ≫ pullback.snd p (pullback.fst f w) = pullback.snd q (pullback.snd f w) := by
  have _ : Etale p := hp
  have _ : IsAffine U := hU
  have _ : IsAffineHom p := hpaff
  obtain ⟨hint, -, -⟩ :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective f).mp inferInstance
  have _ : IsAffineHom f := (IsIntegralHom.iff_universallyClosed_and_isAffineHom.mp hint).2
  obtain ⟨W, w, hw, hWaff, h, hhsurj, hh⟩ := exists_isAffine_etale_domination f p
  have _ : Etale w := hw
  have _ : IsAffine W := hWaff
  -- the base change of `f` along `w`, a universal homeomorphism of affine schemes
  have hfW : UniversalHomeomorphism (pullback.snd f w) := by
    rw [universalHomeomorphism_iff]
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f w) ((universalHomeomorphism_iff f).mp inferInstance)
  have _ : UniversalHomeomorphism (pullback.snd f w) := hfW
  have _ : IsAffine (pullback f w) := inferInstance
  -- the base change of `p` along `X ×_Y W ⟶ X`, with its section coming from `h`
  have _ : Etale (pullback.snd p (pullback.fst f w)) := inferInstance
  have _ : IsSeparated (pullback.snd p (pullback.fst f w)) := inferInstance
  have _ : IsAffine (pullback p (pullback.fst f w)) := inferInstance
  -- an abstract section `s`, which is an open immersion
  obtain ⟨s, hsec, _⟩ : ∃ s : pullback f w ⟶ pullback p (pullback.fst f w),
      s ≫ pullback.snd p (pullback.fst f w) = 𝟙 (pullback f w) ∧ IsOpenImmersion s :=
    have hcomm : h ≫ p = 𝟙 (pullback f w) ≫ pullback.fst f w := by rw [hh, Category.id_comp]
    have hsec := pullback.lift_snd h (𝟙 (pullback f w)) hcomm
    ⟨_, hsec, Unramified.section_isOpenImmersion _ _ hsec⟩
  -- the degree bound drops by one on the complement of the section
  have hπdeg : BoundsFiberDegrees (pullback.snd p (pullback.fst f w)) ((n + 1 : ℕ) : ℤ) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {_ _ : Scheme.{u}} (k : _ ⟶ _) ↦ BoundsFiberDegrees k ((n + 1 : ℕ) : ℤ))
      (IsPullback.of_hasPullback p (pullback.fst f w)) hdeg
  have hRdeg := boundsFiberDegrees_offSection (pullback.snd p (pullback.fst f w))
    s hsec n hπdeg
  -- the induction hypothesis descends the complement of the section
  have hRaff := isAffine_offSection (pullback.snd p (pullback.fst f w))
    s hsec
  obtain ⟨V', q', hq', -, e', he'⟩ := hn (pullback.snd f w) hfW inferInstance inferInstance
    (offSection (pullback.snd p (pullback.fst f w))
      s hsec).toScheme
    ((offSection (pullback.snd p (pullback.fst f w))
      s hsec).ι ≫
        pullback.snd p (pullback.fst f w)) inferInstance hRaff hRdeg
  -- the copy of `X ×_Y W` descends trivially
  have hid : IsPullback (pullback.snd f w) (𝟙 (pullback f w)) (𝟙 W) (pullback.snd f w) :=
    IsPullback.of_id_snd
  have h₁ : ∃ (V : Scheme.{u}) (q : V ⟶ W) (_ : Etale q)
      (e : pullback q (pullback.snd f w) ≅ pullback f w),
      e.hom ≫ (s ≫ pullback.snd p (pullback.fst f w)) = pullback.snd q (pullback.snd f w) := by
    refine ⟨W, 𝟙 W, inferInstance, hid.isoPullback.symm, ?_⟩
    rw [hsec, Category.comp_id, ← cancel_epi hid.isoPullback.hom]
    simp
  -- the two descents assemble
  obtain ⟨V, q, hq, e, he⟩ := exists_etale_pullback_iso_of_isCompl (pullback.snd f w)
    (pullback.snd p (pullback.fst f w)) s
    (offSection (pullback.snd p (pullback.fst f w))
      s hsec).ι
    (by
      rw [Scheme.Opens.opensRange_ι]
      exact isCompl_opensRange_offSection (pullback.snd p (pullback.fst f w))
        s hsec)
    h₁ ⟨V', q', hq', e', he'⟩
  have hVaff : IsAffine V :=
    isAffine_of_isAffine_pullback (pullback.snd f w) q (IsAffine.of_isIso e.hom)
  exact ⟨W, w, hw, hWaff, h, hhsurj, hh, V, q, hq, hVaff, e, he⟩

end Stacks.Etale

end

end
