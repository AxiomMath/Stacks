module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverDenseCompactification
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.NagataCompactification.HasCompactification
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria

/-!
# Closed subspaces and base changes of compactifiable algebraic spaces

Two of the reductions in the proof of Nagata's compactification theorem for algebraic spaces
move a compactification from one space to another.

* If `X` has a compactification `X ⊆ X̄` over `Y` and `Z ⊆ X` is a closed subspace, then the
  scheme-theoretic closure of `Z` in `X̄` is a closed subspace of `X̄`, hence proper over `Y`,
  and `Z` is a quasi-compact open subspace of it, since the composite `Z ⟶ X̄` is a
  quasi-compact immersion.
* If `X` has a compactification `X ⊆ X̄` over `Y` and `Y' ⟶ Y` is a morphism of algebraic
  spaces, then `X ×_Y Y' ⊆ X̄ ×_Y Y'` is a compactification over `Y'`: properness, open
  immersions and quasi-compactness are all stable under base change.

## Main results

* `AlgebraicGeometry.Space.HasCompactification.isIso_comp`: compactifiability is unchanged by
  precomposing with an isomorphism.
* `AlgebraicGeometry.Space.HasCompactification.of_isClosedImmersion`: a closed subspace of a
  compactifiable space is compactifiable.
* `AlgebraicGeometry.Space.HasCompactification.of_isPullback`: compactifiability is stable
  under base change.

## Implementation notes

The base change is stated for an arbitrary cartesian square of presheaves, as for schemes in
`AlgebraicGeometry.HasCompactification.of_isPullback`; the ambient space of the new
compactification is the chosen fibre product, which is algebraic as a fibre product of
algebraic spaces.

## References

* [Stacks Project, Tag 0F4D](https://stacks.math.columbia.edu/tag/0F4D)
* [Stacks Project, Tag 088G](https://stacks.math.columbia.edu/tag/088G)
* [Stacks Project, Tag 04WP](https://stacks.math.columbia.edu/tag/04WP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

namespace HasCompactification

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Compactifiability is unchanged by precomposing with an isomorphism**: the composite of an
isomorphism with a quasi-compact open immersion is a quasi-compact open immersion. -/
theorem isIso_comp {X X' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : X' ⟶ X) [IsIso e]
    {f : X ⟶ Y} (hf : HasCompactification B S hS f) : HasCompactification B S hS (e ≫ f) := by
  obtain ⟨Xc, j, p, hXc, hj, hjqc, hp, rfl⟩ := hf
  rw [← Category.assoc]
  exact of_isOpenImmersion_isProper (e ≫ j) p hXc
    (isOpenImmersion_comp B S hS e j (isOpenImmersion_of_isIso B S hS e) hj)
    (isQuasiCompact_isIso_comp B S hS e hjqc) hp

/-- **A closed subspace of a compactifiable space is compactifiable.** If `f : X ⟶ Y` has a
compactification `X ⊆ X̄` and `i : Z ⟶ X` is a closed immersion, then `Z` is a quasi-compact
open subspace of the scheme-theoretic image of `Z ⟶ X̄`, which is a closed subspace of `X̄` and
so proper over `Y`. -/
theorem of_isClosedImmersion {Z X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (i : Z ⟶ X)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hi : IsClosedImmersion B S hS i) {f : X ⟶ Y} (hf : HasCompactification B S hS f) :
    HasCompactification B S hS (i ≫ f) := by
  obtain ⟨X', j, p, hX', hj, hjqc, hp, rfl⟩ := hf
  have hk : IsImmersion B S hS (i ≫ j) :=
    isImmersion_comp B S hS i j (isImmersion_of_isClosedImmersion B S hS hi)
      (isImmersion_of_isOpenImmersion B S hS hj)
  have hkqc : IsQuasiCompact B S hS (i ≫ j) :=
    IsQuasiCompact.comp B S hS hX hX' (isQuasiCompact_of_isClosedImmersion' B S hS hi) hjqc
  have hC := isClosedSubspace_schemeTheoreticImageSubfunctor B S hS (i ≫ j) hX'
  have hCp : IsProper B S hS ((schemeTheoreticImageSubfunctor B S hS (i ≫ j)).ι ≫ p) :=
    isProper_comp' B S hS _ p hX' hY
      (isProper_of_isClosedImmersion B S hS hC.1 hX' _ hC.2) hp
  have h := of_isOpenImmersion_isProper (toSchemeTheoreticImage B S hS (i ≫ j)) _ hC.1
    (isOpenImmersion_toSchemeTheoreticImage B S hS hX' (i ≫ j) hk hkqc)
    (isQuasiCompact_toSchemeTheoreticImage B S hS (i ≫ j) hkqc) hCp
  rwa [← Category.assoc, toSchemeTheoreticImage_ι, Category.assoc] at h

/-- **Compactifiability is stable under base change.** If `f' : X' ⟶ Y'` is the base change of
`f : X ⟶ Y` along `g : Y' ⟶ Y`, exhibited by a cartesian square, and `f` has a
compactification `X ⊆ X̄`, then `X' ⊆ X̄ ×_Y Y'` is a compactification of `f'`. -/
theorem of_isPullback {X Y X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {q : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback q f' f g)
    (hY : IsAlgebraicSpace B S hS Y) (hY' : IsAlgebraicSpace B S hS Y')
    (hf : HasCompactification B S hS f) : HasCompactification B S hS f' := by
  obtain ⟨Xc, j, p, hXc, hj, hjqc, hp, rfl⟩ := hf
  have hbot : IsPullback (pullback.fst p g) (pullback.snd p g) p g :=
    IsPullback.of_hasPullback p g
  have hP : IsAlgebraicSpace B S hS (pullback p g) :=
    isAlgebraicSpace_pullback B S hS p g hXc hY' hY
  have hp' : IsProper B S hS (pullback.snd p g) :=
    isProper_of_isPullback B S hS hP hXc hY' hY hbot hp
  let ℓ : X' ⟶ pullback p g := pullback.lift (q ≫ j) f' ((Category.assoc _ _ _).trans sq.w)
  have hℓsnd : ℓ ≫ pullback.snd p g = f' := pullback.lift_snd _ _ _
  have htop : IsPullback q ℓ j (pullback.fst p g) :=
    IsPullback.of_bot (by rwa [hℓsnd]) (pullback.lift_fst _ _ _).symm hbot
  have hℓ : IsOpenImmersion B S hS ℓ :=
    (MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).of_isPullback htop hj
  have hℓqc : IsQuasiCompact B S hS ℓ := isQuasiCompact_of_isPullback B S hS htop hjqc
  exact of_eq hℓsnd (of_isOpenImmersion_isProper ℓ _ hP hℓ hℓqc hp')

end HasCompactification

end AlgebraicGeometry.Space

end
