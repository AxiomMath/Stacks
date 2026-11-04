module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.IndQuasiAffine.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineStability
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.IndQuasiAffine

/-!
# Ind-quasi-affine morphisms are stable under base change

Ind-quasi-affineness of a morphism of schemes is determined by its restrictions over the affine
opens of the target, and over an affine target it says exactly that the source is an
ind-quasi-affine scheme. This file records that affine-local description and deduces from it that
ind-quasi-affine morphisms are stable under arbitrary base change.

## Main results

* `AlgebraicGeometry.Scheme.IsQuasiAffine.of_isIndQuasiAffine`: a quasi-compact ind-quasi-affine
  scheme is quasi-affine.
* `AlgebraicGeometry.IsIndQuasiAffine.of_isOpenImmersion`: an open subscheme of an
  ind-quasi-affine scheme is ind-quasi-affine.
* `AlgebraicGeometry.IsIndQuasiAffine.of_isAffineHom`: the source of an affine morphism into an
  ind-quasi-affine scheme is ind-quasi-affine.
* `AlgebraicGeometry.hasAffineProperty_isIndQuasiAffineHom`: ind-quasi-affineness of a morphism
  is the affine-local property that the source is an ind-quasi-affine scheme.
* `AlgebraicGeometry.IsIndQuasiAffineHom.instPullbackSnd` and
  `AlgebraicGeometry.isIndQuasiAffineHom_of_isPullback`: a base change of an ind-quasi-affine
  morphism is ind-quasi-affine.

## Implementation notes

Reduction to an affine base is supplied by Mathlib's `AlgebraicGeometry.HasAffineProperty`
machinery, through `AlgebraicGeometry.hasAffineProperty_isIndQuasiAffineHom`, and over an affine
base the statement is `AlgebraicGeometry.IsIndQuasiAffine.of_isAffineHom`. Given an affine
`h : Z ⟶ Y` with `Y` ind-quasi-affine and a quasi-compact open `W` of `Z`, the image of `W` is a
quasi-compact subset of `Y`, hence — the underlying space of a scheme being prespectral — is
contained in a quasi-compact open `Y₀`. Then `Y₀` is a quasi-affine scheme, the restriction
`h ∣_ Y₀` is affine, so the inverse image of `Y₀` is quasi-affine by
`AlgebraicGeometry.Scheme.IsQuasiAffine.of_isAffineHom`, and `W` is a quasi-compact open
subscheme of it.

## References

* [Stacks Project, Tag 0AP7](https://stacks.math.columbia.edu/tag/0AP7)
* [Stacks Project, Tag 0AP6](https://stacks.math.columbia.edu/tag/0AP6)
* [Stacks Project, Tag 01SO](https://stacks.math.columbia.edu/tag/01SO)
* [Stacks Project, Tag 0BCK](https://stacks.math.columbia.edu/tag/0BCK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A quasi-compact ind-quasi-affine scheme is quasi-affine. -/
lemma Scheme.IsQuasiAffine.of_isIndQuasiAffine (Z : Scheme.{u}) [IsIndQuasiAffine Z]
    [CompactSpace Z] : Z.IsQuasiAffine :=
  have : (⊤ : Z.Opens).toScheme.IsQuasiAffine :=
    IsIndQuasiAffine.isQuasiAffine ⊤ (by simpa using isCompact_univ (X := Z))
  Scheme.IsQuasiAffine.of_isImmersion Z.topIso.inv

/-- A quasi-compact scheme admitting an open immersion into an ind-quasi-affine scheme is
quasi-affine. -/
lemma Scheme.IsQuasiAffine.of_isOpenImmersion_of_isIndQuasiAffine {X V : Scheme.{u}}
    [IsIndQuasiAffine V] (j : X ⟶ V) [IsOpenImmersion j] [CompactSpace X] : X.IsQuasiAffine :=
  have : (j.opensRange).toScheme.IsQuasiAffine :=
    IsIndQuasiAffine.isQuasiAffine j.opensRange (by simpa using isCompact_range j.continuous)
  Scheme.IsQuasiAffine.of_isImmersion j.isoOpensRange.hom

/-- A scheme admitting an open immersion into an ind-quasi-affine scheme is ind-quasi-affine. In
particular an open subscheme of an ind-quasi-affine scheme is ind-quasi-affine. -/
lemma IsIndQuasiAffine.of_isOpenImmersion {X V : Scheme.{u}} [IsIndQuasiAffine V] (j : X ⟶ V)
    [IsOpenImmersion j] : IsIndQuasiAffine X := by
  refine ⟨fun W hW ↦ ?_⟩
  have : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hW
  exact Scheme.IsQuasiAffine.of_isOpenImmersion_of_isIndQuasiAffine (W.ι ≫ j)

/-- The part of an ind-quasi-affine open subscheme lying in another open subscheme is
ind-quasi-affine, viewed as an open subscheme of the latter. -/
lemma IsIndQuasiAffine.opens_ι_preimage {X : Scheme.{u}} (W V : X.Opens)
    [IsIndQuasiAffine V.toScheme] : IsIndQuasiAffine (W.ι ⁻¹ᵁ V).toScheme :=
  IsIndQuasiAffine.of_isOpenImmersion ((X.restrictRestrictComm W V).hom ≫ (V.ι ⁻¹ᵁ W).ι)

/-- The source of an affine morphism into an ind-quasi-affine scheme is ind-quasi-affine. -/
lemma IsIndQuasiAffine.of_isAffineHom {Z Y : Scheme.{u}} (h : Z ⟶ Y) [IsAffineHom h]
    [IsIndQuasiAffine Y] : IsIndQuasiAffine Z := by
  refine ⟨fun W hW ↦ ?_⟩
  obtain ⟨K, hKc, hKo, hKsub, -⟩ := PrespectralSpace.exists_isCompact_and_isOpen_between
    (hW.image h.continuous) isOpen_univ (Set.subset_univ _)
  let Y₀ : Y.Opens := ⟨K, hKo⟩
  have : Y₀.toScheme.IsQuasiAffine := IsIndQuasiAffine.isQuasiAffine Y₀ hKc
  have hle : W ≤ h ⁻¹ᵁ Y₀ := fun x hx ↦ hKsub ⟨x, hx, rfl⟩
  have : IsAffineHom (h ∣_ Y₀) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_morphismRestrict h Y₀).flip inferInstance
  have : (h ⁻¹ᵁ Y₀).toScheme.IsQuasiAffine := Scheme.IsQuasiAffine.of_isAffineHom (h ∣_ Y₀)
  have : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hW
  exact Scheme.IsQuasiAffine.of_isImmersion (Z.homOfLE hle)

/-- Ind-quasi-affineness of a morphism of schemes is the affine-local property that the source
is an ind-quasi-affine scheme. -/
instance hasAffineProperty_isIndQuasiAffineHom :
    HasAffineProperty @IsIndQuasiAffineHom fun X _ _ _ ↦ IsIndQuasiAffine X where
  isLocal_affineProperty := by
    constructor
    · apply AffineTargetMorphismProperty.respectsIso_mk
      · rintro X Y Z e _ _ H
        have : IsIndQuasiAffine Y := H
        exact IsIndQuasiAffine.of_isAffineHom e.hom
      · exact fun _ _ _ ↦ id
    · intro X Y _ f r H
      have : IsIndQuasiAffine X := H
      change IsIndQuasiAffine _
      rw [Scheme.preimage_basicOpen_top]
      exact IsIndQuasiAffine.of_isOpenImmersion (X.basicOpen (f.appTop r)).ι
    · intro X Y _ f S hS hS'
      have hS'' : ∀ r : S, IsIndQuasiAffine (f ⁻¹ᵁ Y.basicOpen r.1).toScheme := hS'
      refine ⟨fun W hW ↦ ?_⟩
      have : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hW
      apply_fun Ideal.map ((W.ι ≫ f).appTop).hom at hS
      rw [Ideal.map_span, Ideal.map_top] at hS
      refine Scheme.IsQuasiAffine.of_span_eq_top _ _ hS ?_
      rintro _ ⟨r, hr, rfl⟩
      have hc : IsCompact (W.toScheme.basicOpen ((W.ι ≫ f).appTop r) : Set W.toScheme) := by
        simpa using isRetrocompact_basicOpen (X := W.toScheme) ((W.ι ≫ f).appTop r)
          isCompact_univ isOpen_univ
      have := hS'' ⟨r, hr⟩
      have hiqa : IsIndQuasiAffine (W.ι ⁻¹ᵁ f ⁻¹ᵁ Y.basicOpen r).toScheme :=
        IsIndQuasiAffine.opens_ι_preimage W (f ⁻¹ᵁ Y.basicOpen r)
      rw [← Scheme.preimage_basicOpen_top, Scheme.Hom.comp_preimage] at hc ⊢
      have : CompactSpace (W.ι ⁻¹ᵁ f ⁻¹ᵁ Y.basicOpen r).toScheme :=
        isCompact_iff_compactSpace.mp hc
      exact Scheme.IsQuasiAffine.of_isIndQuasiAffine _
  eq_targetAffineLocally' := by
    ext X Y f
    simp only [targetAffineLocally, Scheme.affineOpens, Set.coe_ofPred, Set.mem_ofPred_eq,
      Subtype.forall, isIndQuasiAffineHom_iff]

/-- The second projection of a pullback of an ind-quasi-affine morphism is ind-quasi-affine. -/
instance IsIndQuasiAffineHom.instPullbackSnd {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsIndQuasiAffineHom f] : IsIndQuasiAffineHom (pullback.snd f g) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback f g)
    inferInstance

/-- A morphism of schemes that is the base change of an ind-quasi-affine morphism along an
arbitrary morphism is ind-quasi-affine. -/
theorem isIndQuasiAffineHom_of_isPullback {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {p : X' ⟶ X} (H : IsPullback p f' f g) [IsIndQuasiAffineHom f] :
    IsIndQuasiAffineHom f' :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback H inferInstance

end AlgebraicGeometry

end
