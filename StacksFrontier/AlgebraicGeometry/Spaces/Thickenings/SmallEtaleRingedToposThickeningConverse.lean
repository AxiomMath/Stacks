module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOverFromAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineOfAffineClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SmallEtaleRingedToposThickeningReduction

/-!
# A morphism with an isomorphism of reductions is affine

Let `i : Z ⟶ Z'` be a morphism of algebraic spaces over a scheme `S` such that the induced
morphism of reductions `c : Z_red ⟶ Z'_red` is an isomorphism.  This file proves that `i` is an
affine morphism.  This is a step of the implication (2) ⇒ (1) of Stacks 0D16: there `c` is an
isomorphism by `AlgebraicGeometry.Space.isIso_spaceReductionMap_of_isThickening`.

Let `T` be an affine scheme with a morphism `g : T ⟶ Z'`.  The base change
`R = Z_red ×_{Z'} T` of `i ≫ r = c ≫ r'` along `g` is a closed subspace of `T`, the morphism
`c ≫ r'` being a closed immersion, so `R` is affine.  On the other hand `R` is the base change
along `Z ×_{Z'} T ⟶ Z` of the thickening `Z_red ⟶ Z`, so `R ⟶ Z ×_{Z'} T` is a surjective closed
immersion.  An algebraic space with an affine thickening is affine
(`AlgebraicGeometry.Space.isAffineSpace_of_isClosedImmersion_of_isSurjective`), so
`Z ×_{Z'} T` is affine.

## Main results

* `AlgebraicGeometry.Space.isAffineSpace_pullback_of_isIso_spaceReductionMap`: the base change
  of `i` along a morphism from an affine scheme is affine.
* `AlgebraicGeometry.Space.isAffineHom_of_isIso_spaceReductionMap`: `i` is affine.

## References

* [Stacks Project, Tag 0D16](https://stacks.math.columbia.edu/tag/0D16)
* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An algebraic space with a closed immersion into an affine scheme is affine. -/
theorem isAffineSpace_of_isClosedImmersion_yoneda {R : AlgebraicSpaces B S hS}
    {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (m : R.1 ⟶ yoneda.obj T) (hm : IsClosedImmersion B S hS m) :
    IsAffineSpace B S hS R.1 := by
  obtain ⟨T', snd, fst, sq⟩ := hm.rep (𝟙 (yoneda.obj T))
  have : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map snd) := hm.2 _ _ _ sq
  have : IsIso fst := sq.isIso_fst_of_isIso
  exact ⟨T', isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map snd), ⟨(asIso fst).symm⟩⟩

/-- **The base change of `i` along a morphism from an affine scheme is affine**, when the morphism
of reductions induced by `i` is an isomorphism. -/
theorem isAffineSpace_pullback_of_isIso_spaceReductionMap {Z Z' : AlgebraicSpaces B S hS}
    (i : Z ⟶ Z') (hc : IsIso (spaceReductionMap i)) {T : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (g : schemeSpace T ⟶ Z') :
    IsAffineSpace B S hS (pullback i g).1 := by
  have hr := isThickeningHom_spaceReductionι Z
  have sq0 := IsPullback.of_hasPullback (spaceReductionι Z) (pullback.fst i g)
  have sqo := sq0.paste_vert (IsPullback.of_hasPullback i g)
  rw [← spaceReductionMap_comp i] at sqo
  have hcr : IsClosedImmersion B S hS (spaceReductionMap i ≫ spaceReductionι Z').hom := by
    have : IsIso (spaceReductionMap i).hom := inferInstanceAs (IsIso
      ((ObjectProperty.ι _).map (spaceReductionMap i)))
    let Q := MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
    let _ : Q.RespectsIso := inferInstance
    exact MorphismProperty.RespectsIso.precomp Q (spaceReductionMap i).hom
      (spaceReductionι Z').hom (isThickeningHom_spaceReductionι Z').isClosedImmersion
  exact isAffineSpace_of_isClosedImmersion_of_isSurjective B S hS _
    (pullback (spaceReductionι Z) (pullback.fst i g)).2 (pullback i g).2
    (isClosedImmersion_of_isPullback B S hS sq0 hr.isClosedImmersion)
    ((surjectiveMorphismProperty B S hS).of_isPullback sq0 hr.surjective_pointsMap)
    (isAffineSpace_of_isClosedImmersion_yoneda (T := T)
      (pullback.snd (spaceReductionι Z) (pullback.fst i g) ≫ pullback.snd i g).hom
      (isClosedImmersion_of_isPullback B S hS sqo hcr))

/-- **A morphism of algebraic spaces whose morphism of reductions is an isomorphism is affine.**
Its base change along every affine étale chart of the target is affine. -/
theorem isAffineHom_of_isIso_spaceReductionMap {Z Z' : AlgebraicSpaces B S hS} (i : Z ⟶ Z')
    (hc : IsIso (spaceReductionMap i)) :
    IsAffineHom B S hS i.hom := by
  refine isAffineHom_of_affineChart B S hS (X := Z') Z.2 i.hom fun V hV => ?_
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj V.obj.left) := hV
  let g : schemeSpace V.obj.left ⟶ Z' := ObjectProperty.homMk V.obj.hom
  obtain ⟨T, hT, ⟨e⟩⟩ := isAffineSpace_pullback_of_isIso_spaceReductionMap i hc g
  refine ⟨⟨T, hT⟩, e.inv ≫ (pullback.fst i g).hom,
    yoneda.preimage (e.inv ≫ (pullback.snd i g).hom), ?_⟩
  refine (AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback i g)).of_iso e
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) ?_ (by simp)
    (by simp only [Iso.refl_hom, Category.comp_id]; rfl)
  simp only [Iso.refl_hom, Functor.map_preimage]
  exact (Category.comp_id (pullback.snd i g).hom).trans (e.hom_inv_id_assoc _).symm

end AlgebraicGeometry.Space

end
