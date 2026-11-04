module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties

/-!
# A property local at the source passes from an open cover of an atlas to the atlas

Let `a : yoneda.obj U ⟶ F` be a relatively representable morphism from a representable presheaf
on the big fppf site over `S`, and let the underlying scheme of `U` be covered by the members of
a family of open immersions `Ui i ⟶ U` of the site. If a property `P` of morphisms of schemes
which is Zariski local at the source holds for the base changes of every composite
`yoneda.obj (Ui i) ⟶ yoneda.obj U ⟶ F`, then it holds for the base changes of `a`.

This is the second of the two inputs which the glueing step of Stacks 02WR needs and
`StacksFrontier.AlgebraicGeometry.Spaces.OpenCoverSpace` does not have: with it, étaleness of a
scheme atlas assembled out of the atlases of the members of a cover follows from étaleness of
the members' atlases, because `AlgebraicGeometry.Etale` is Zariski local at the source. The
first input is
`AlgebraicGeometry.BigFppfOver.exists_mem_range_of_mem_topology` in
`StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveSurjective`, whose conclusion is exactly the
joint surjectivity hypothesis consumed here.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.presheaf_inverseImage_of_isZariskiLocalAtSource`: the presheaf
  relativization of a property Zariski local at the source descends along an open cover of the
  source of a relatively representable morphism out of a representable presheaf.

## Implementation notes

The base change of `a` along a section `ξ` of `F` is represented by `hrep.pullback ξ`, and the
first projection out of it is a morphism of *presheaves* to `yoneda.obj U`; the morphism `q` of
the site underlying it is its preimage under the full functor `CategoryTheory.yoneda`. The charts
of the base change are then the fibre products `Ui i ×_U hrep.pullback ξ` formed in the site,
and two facts are read off the squares they sit in. Transported to schemes, where the functor to
schemes preserves fibre products by
`AlgebraicGeometry.Space.preservesLimitsOfShape_walkingCospan_toScheme`, they exhibit an open
cover of the scheme representing the base change: the legs are open immersions by stability of
open immersions under base change, and they are jointly surjective by
`AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving.exists_preimage_snd_triplet_of_prop`,
the point-lifting property which the class of open immersions carries. Transported to presheaves
instead, where `CategoryTheory.yoneda` preserves fibre products, they paste onto the defining
square of `hrep` and so are base-change squares of the composites
`yoneda.map (inj i) ≫ a`; applying the hypothesis to those squares — rather than to the chosen
pullbacks, which is what `CategoryTheory.MorphismProperty.relative.property_snd` would give —
is what avoids comparing two choices of fibre product.

The joint surjectivity hypothesis is stated on points of the underlying schemes rather than as
membership of a covering family in `AlgebraicGeometry.Scheme.zariskiPrecoverage`. That is not
only the form in which the covering is available:
`CategoryTheory.Precoverage.IsStableUnderBaseChange` restricts the index type of a covering
family to `Type (u + 1)`, which the index type of a cover of an object of the site is not, so the
base change of the covering family cannot be taken through that class and the point-lifting is
done directly.

## References

* [Stacks Project, Tag 02WR](https://stacks.math.columbia.edu/tag/02WR)
* [Stacks Project, Tag 03EC](https://stacks.math.columbia.edu/tag/03EC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A property of morphisms of schemes which is Zariski local at the source descends from an
open cover of an atlas to the atlas.** Let `a : yoneda.obj U ⟶ F` be relatively representable
and let the family `inj` of open immersions of the site cover `U`. If the presheaf
relativization of `P` holds for every composite `yoneda.map (inj i) ≫ a`, it holds for `a`.

The charts of the base change of `a` along a section of `F` are the base changes of the `inj i`,
which cover it; the composite of each with the projection is a base change of
`yoneda.map (inj i) ≫ a`, so locality at the source applies. -/
theorem presheaf_inverseImage_of_isZariskiLocalAtSource
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P]
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS}
    {a : yoneda.obj U ⟶ F} (hrep : yoneda.relativelyRepresentable a)
    {I : Type u} {Ui : I → BigFppfOver B S hS} (inj : ∀ i, Ui i ⟶ U)
    (hopen : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (inj i)))
    (hcov : ∀ y : (BigFppfOver.toScheme B S hS).obj U,
      ∃ i, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (inj i)).base)
    (hP : ∀ i, (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf
      (yoneda.map (inj i) ≫ a)) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf a := by
  let _ := B.hasPullbacks_schemes
  let _ : HasPullbacks (BigFppfOver B S hS) := inferInstance
  let _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  refine MorphismProperty.relative_of_snd hrep fun V ξ => ?_
  set T := BigFppfOver.toScheme B S hS with hT
  set q : hrep.pullback ξ ⟶ U := yoneda.preimage (hrep.fst ξ) with hqdef
  have hq : yoneda.map q = hrep.fst ξ := yoneda.map_preimage _
  have hsq : ∀ i, IsPullback (pullback.fst (inj i) q) (pullback.snd (inj i) q) (inj i) q :=
    fun i => IsPullback.of_hasPullback _ _
  have hsqS : ∀ i, IsPullback (T.map (pullback.fst (inj i) q))
      (T.map (pullback.snd (inj i) q)) (T.map (inj i)) (T.map q) :=
    fun i => (hsq i).map T
  have hopenW : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion
      (T.map (pullback.snd (inj i) q)) :=
    fun i => MorphismProperty.IsStableUnderBaseChange.of_isPullback (hsqS i) (hopen i)
  have hcovW : ∀ x : T.obj (hrep.pullback ξ), ∃ i,
      x ∈ Set.range (T.map (pullback.snd (inj i) q)).base := by
    intro x
    obtain ⟨i, v, hv⟩ := hcov ((T.map q).base x)
    have := (hsqS i).hasPullback
    obtain ⟨w, hw⟩ := Scheme.IsJointlySurjectivePreserving.exists_preimage_snd_triplet_of_prop
      (P := (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}))
      (hopen i) v x hv
    refine ⟨i, ((hsqS i).isoPullback.inv).base w, ?_⟩
    rwa [← Scheme.Hom.comp_apply, (hsqS i).isoPullback_inv_snd]
  let 𝒰 : (T.obj (hrep.pullback ξ)).OpenCover :=
    { I₀ := I
      X := fun i => T.obj (pullback (inj i) q)
      f := fun i => T.map (pullback.snd (inj i) q)
      mem₀ := (Scheme.ofArrows_mem_precoverage_iff _).2 ⟨hcovW, hopenW⟩ }
  show P (T.map (hrep.snd ξ))
  refine IsZariskiLocalAtSource.of_openCover 𝒰 fun i => ?_
  have hsq2 : IsPullback (yoneda.map q) (yoneda.map (hrep.snd ξ)) a ξ :=
    hq ▸ hrep.isPullback ξ
  have hbig : IsPullback (yoneda.map (pullback.fst (inj i) q))
      (yoneda.map (pullback.snd (inj i) q ≫ hrep.snd ξ))
      (yoneda.map (inj i) ≫ a) ξ := by
    rw [Functor.map_comp]
    exact ((hsq i).map yoneda).paste_vert hsq2
  have hres := (hP i).property ξ (yoneda.map (pullback.fst (inj i) q))
    (pullback.snd (inj i) q ≫ hrep.snd ξ) hbig
  rwa [MorphismProperty.inverseImage_iff, Functor.map_comp] at hres

end AlgebraicGeometry.Space

end
