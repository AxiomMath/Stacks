module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringRestrictionFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedProperLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedProperTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget

/-!
# An atlas of bounded size for an algebraic space proper over an affine

Let `S` be a scheme contained in a big fppf site `B`. An algebraic space over `S` with values
in `Type (max w u)` which is proper over an affine object `Z` of the big fppf site of `S`
admits a surjective étale atlas by an *affine* object `T` of the site with
`size T ≤ size Z`.

This is the set-theoretic input that makes a coproduct of such algebraic spaces, indexed by the
affine opens of one object of the site, land inside the site: without a *uniform* bound on the
atlases, the disjoint union of them carries no bound below the site's size cutoff, the cutoff
not being known to be regular.

## Main results

* `AlgebraicGeometry.Space.exists_affine_atlas_size_le_of_isProperULift`: the atlas.

## Implementation notes

The three steps are the ones of the closing paragraph of Stacks 04U1, run in the value universe
`max w u` by descending to the value universe of the site. A large-valued algebraic space is the
universe lift of an algebraic space over `S` with values in `Type u`
(`AlgebraicGeometry.Space.exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift`), properness of
a lift is properness of what it lifts
(`AlgebraicGeometry.Space.isProperULift_whiskerRight_iff`, Stacks 03ZM), and down there the
source's chain applies: the target is affine hence quasi-compact, properness is quasi-compact,
so the space is quasi-compact (Stacks 03E3) and therefore has an affine surjective étale atlas
by **Stacks 03H6**; that atlas is locally of finite type over `Z`, being étale followed by a
morphism of finite type (Stacks 03XG), and quasi-compact, so **Stacks 04T7** bounds its size by
that of `Z`. The atlas is then lifted back, the relative surjectivity and étaleness along
`CategoryTheory.uliftYoneda` being the ones along `CategoryTheory.yoneda` carried by the lifting
functor (`AlgebraicGeometry.Space.relative_comp_map_iff`).

## References

* [Stacks Project, Tag 03E3](https://stacks.math.columbia.edu/tag/03E3)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03XG](https://stacks.math.columbia.edu/tag/03XG)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 04T7](https://stacks.math.columbia.edu/tag/04T7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An algebraic space over `S` proper over an affine object of the big fppf site of `S` has
an affine surjective étale atlas of size at most that of the base.**

The space is the universe lift of an algebraic space over `S` in the value universe of the
site, and properness transfers along the lift; down there the space is quasi-compact, so
Stacks 03H6 gives an affine atlas, and Stacks 04T7 bounds its size by that of the affine base
because the atlas is quasi-compact and locally of finite type over it. -/
theorem exists_affine_atlas_size_le_of_isProperULift
    {Z : BigFppfOver B S hS} (hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj Z))
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (hA : IsAlgebraicSpaceULift.{w} B S hS A)
    (p : A ⟶ (uliftYoneda.{w}).obj Z) (hp : IsProperULift.{w} B S hS p) :
    ∃ (T : BigFppfOver B S hS) (a : (uliftYoneda.{w}).obj T ⟶ A),
      IsAffine ((BigFppfOver.toScheme B S hS).obj T) ∧
      (surjectiveOnSite B S hS).relative (uliftYoneda.{w}) a ∧
      (etaleOnSite B S hS).relative (uliftYoneda.{w}) a ∧
      ((BigFppfOver.toScheme B S hS).obj T).size ≤
        ((BigFppfOver.toScheme B S hS).obj Z).size := by
  classical
  let C := BigFppfOver B S hS
  let H := (Functor.whiskeringRight Cᵒᵖ (Type u) (Type (max w u))).obj uliftFunctor.{w}
  let _ : FunctorToTypes.Small.{u} A := small_of_isAlgebraicSpaceULift B S hS hA
  let A' : Cᵒᵖ ⥤ Type u := FunctorToTypes.shrink.{u} A
  let eA : H.obj A' ≅ A := shrinkCompUliftFunctorIso A
  have hA' : IsAlgebraicSpace B S hS A' :=
    (isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS A').mp
      (isAlgebraicSpaceULift_of_iso B S hS eA.symm hA)
  let p' : A' ⟶ yoneda.obj Z := H.preimage (eA.hom ≫ p)
  -- properness descends to the value universe of the site
  have hp' : IsProper B S hS p' := by
    refine (isProperULift_whiskerRight_iff.{w} B S hS p').mp ?_
    have hgoal : Functor.whiskerRight p' uliftFunctor.{w} = eA.hom ≫ p :=
      H.map_preimage _
    rw [hgoal]
    exact isProperULift_precomp B S hS eA p
      (isAlgebraicSpaceULift_of_iso B S hS eA.symm hA) hA
      (isAlgebraicSpaceULift_uliftYoneda.{w} B S hS Z) hp
  -- the space is quasi-compact, the base being affine
  have hAqc : IsQuasiCompactSpace B S hS A' := by
    refine isQuasiCompactSpace_of_iso B S hS
      (asIso (pullback.snd (𝟙 (yoneda.obj Z)) p')) ?_
    exact hp'.2.1.2 _ (isAlgebraicSpace_yoneda B S hS Z)
      (isQuasiCompactSpace_yoneda_of_isAffine B S hS Z hZ) (𝟙 _)
  obtain ⟨T, a', hTaff, hasurj, haet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS A' hA').1 hAqc
  -- Stacks 04T7 bounds the size of the atlas by that of the affine base
  have hsize : ((BigFppfOver.toScheme B S hS).obj T).size ≤
      ((BigFppfOver.toScheme B S hS).obj Z).size := by
    have hcompose : IsLocallyOfFiniteType B S hS (a' ≫ p') :=
      isLocallyOfFiniteType_comp B S hS (isAlgebraicSpace_yoneda B S hS T) hA'
        (isAlgebraicSpace_yoneda B S hS Z) a' p'
        (holdsOnEveryEtaleChart_of_isEtale B S hS
          (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
          (fun _ hg => have := hg; inferInstance) hA' haet)
        hp'.2.1.1
    have hgmap : IsLocallyOfFiniteType B S hS
        (yoneda.map (yoneda.preimage (a' ≫ p'))) := by
      rwa [Functor.map_preimage]
    have _ : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map
        (yoneda.preimage (a' ≫ p'))) :=
      (holdsOnEveryEtaleChart_yoneda_map_iff B S hS
        LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget
        (yoneda.preimage (a' ≫ p'))).1 hgmap
    have _ : CompactSpace ((BigFppfOver.toScheme B S hS).obj T) := by
      have := hTaff
      infer_instance
    exact Scheme.size_le_of_locallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (a' ≫ p')))
  -- the atlas, lifted back
  refine ⟨T, H.map a' ≫ eA.hom, hTaff, ?_, ?_, hsize⟩ <;>
    refine MorphismProperty.RespectsIso.postcomp _ eA.hom _
      ((relative_comp_map_iff yoneda H _ a').mpr ?_)
  · exact hasurj
  · exact (isEtale_iff_presheaf_of_yoneda B S hS a').1 haet

end AlgebraicGeometry.Space

end
