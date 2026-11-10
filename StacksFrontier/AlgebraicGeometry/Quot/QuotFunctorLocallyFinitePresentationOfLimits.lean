module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorSeparatedLocallyFinitePresentation

/-!
# `Quot_{F/X/B} ⟶ B` is separated, and locally of finite presentation when `F` is (Stacks 0DM3)

Let `f : X ⟶ B` be a morphism of algebraic spaces of finite presentation and `F` a quasi-coherent
`𝒪_X`-module, the standing data `AlgebraicGeometry.Space.QuotSituation` of Stacks 09TR. Stacks
0DM3 asserts that `Quot_{F/X/B} ⟶ B` is separated and, when `F` is of finite presentation, that it
is also locally of finite presentation. Both clauses are read on the Quot presheaf, in the form of
`AlgebraicGeometry.Space.QuotSituation.isSeparatedULift_quotSitePresheafToBase`.

## Main results

All of these live in the namespace `AlgebraicGeometry.Space.QuotSituation`.

* `exists_stage_lift_quotSitePresheaf`: a section of the Quot presheaf over a cofiltered limit of
  affine schemes, lying over a point of `B` at a stage, comes from a section over a later stage
  lying over the same point.
* `isLocallyOfFinitePresentationULift_quotSitePresheafToBase`: the lfp clause of Stacks 0DM3.
* `isSeparatedULift_and_imp_isLocallyOfFinitePresentationULift_quotSitePresheafToBase`:
  both clauses of Stacks 0DM3.

## References

* [Stacks Project, Tag 0DM3](https://stacks.math.columbia.edu/tag/0DM3)
* [Stacks Project, Tag 09TU](https://stacks.math.columbia.edu/tag/09TU)
* [Stacks Project, Tag 0CM6](https://stacks.math.columbia.edu/tag/0CM6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local implicit_reducible] AlgebraicGeometry.Space.QuotSituation.toCoherentSituation

namespace AlgebraicGeometry.Space.QuotSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : QuotSituation B S hS)

/-- **Quotients lift along cofiltered limits of affine schemes of the site, on the Quot
presheaf.** Let `F` be of finite presentation and `T = lim T_i` a cofiltered limit of affine
schemes of the site, taken in schemes. A section `x` of the Quot presheaf over `T` lying over the
restriction of a point `y` of `B` at a stage `T_i` is the restriction of a section over a later
stage `T_j` lying over the restriction of `y`. -/
theorem exists_stage_lift_quotSitePresheaf (hF : D.F.IsFinitePresentationOnSite) :
    ∀ (I : Type u) [Category.{u} I] [IsCofiltered I]
      (E : I ⥤ BigFppfOver B S hS) (c : Cone E),
      IsLimit ((BigFppfOver.toScheme B S hS).mapCone c) →
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj i))) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt) →
      ∀ (x : D.quotSitePresheaf.obj (op c.pt)) (i : I) (y : D.Y.obj.obj (op (E.obj i))),
        (D.quotSitePresheafToBase.app (op c.pt) x).down = D.Y.obj.map (c.π.app i).op y →
        ∃ (j : I) (g : j ⟶ i) (z : D.quotSitePresheaf.obj (op (E.obj j))),
          (D.quotSitePresheafToBase.app (op (E.obj j)) z).down =
              D.Y.obj.map (E.map g).op y ∧
            D.quotSitePresheaf.map (c.π.app j).op z = x := by
  intro I _ _ Dg c hc haff haffc x i y hxy
  let E : I ⥤ BigAffineFppf B S hS := ObjectProperty.lift _ Dg haff
  let cE : Cone E :=
    { pt := ⟨c.pt, haffc⟩
      π :=
        { app := fun i => ObjectProperty.homMk (c.π.app i)
          naturality := fun i i' f => by
            apply ObjectProperty.hom_ext
            exact c.π.naturality f } }
  have hcE : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone cE) := hc
  let g : (schemeSpaceFunctor B S hS).obj ((BigAffineFppf.inclusion B S hS).obj (E.obj i)) ⟶
      D.Y := ObjectProperty.homMk (yonedaEquiv.symm y)
  obtain ⟨b, K, hK⟩ := x
  have hb : b = (schemeSpaceFunctor B S hS).map
      ((BigAffineFppf.inclusion B S hS).map (cE.π.app i)) ≫ g := by
    apply ObjectProperty.hom_ext
    apply yonedaEquiv.injective
    change yonedaEquiv b.hom = _ at hxy
    rw [hxy]
    exact (yonedaEquiv.apply_symm_apply _).symm.trans <| congrArg yonedaEquiv
      (yonedaEquiv_symm_naturality_left _ _ _).symm
  subst hb
  obtain ⟨m, K', hK', hpull⟩ := D.exists_stage_quotientPullback_eq E cE hcE hF g K hK
  let zm : QuotFamilyOver D (Dg.obj m.left) :=
    ⟨((D.toCoherentSituation.stageTestSystem E g).obj m).hom, K', hK'⟩
  refine ⟨m.left, m.hom, zm, ?_, ?_⟩
  · change yonedaEquiv ((yoneda (C := BigFppfOver B S hS)).map (Dg.map m.hom) ≫
      (yonedaEquiv (F := D.Y.1) (X := Dg.obj i)).symm y) = _
    rw [yonedaEquiv_symm_naturality_left, Equiv.apply_symm_apply]
  · change zm.baseChange (c.π.app m.left) = _
    refine (D.quotFamily_eq_baseChange_of (c.π.app m.left) ⟨_, K, hK⟩ zm ?_
      ((D.toCoherentSituation.stageTestCone E cE g).π.app m) rfl hpull.symm).symm
    change (schemeSpaceFunctor B S hS).map (c.π.app i) ≫ g =
      (schemeSpaceFunctor B S hS).map (c.π.app m.left) ≫
        (schemeSpaceFunctor B S hS).map (Dg.map m.hom) ≫ g
    rw [← Functor.map_comp_assoc, c.w]

/-- If `F` is of finite presentation, then `Quot_{F/X/B} ⟶ B` is locally of finite presentation:
the morphism of schemes underlying every commuting square of étale charts of the Quot presheaf over
`B` is locally of finite presentation. -/
@[stacks 0DM3 "the finite-presentation clause: if F is of finite presentation, \
Quot_{F/X/B} → B is locally of finite presentation"]
theorem isLocallyOfFinitePresentationULift_quotSitePresheafToBase
    (hF : D.F.IsFinitePresentationOnSite) :
    IsLocallyOfFinitePresentationULift.{u + 1} B S hS D.quotSitePresheafToBase :=
  D.isLocallyOfFinitePresentationULift_quotSitePresheafToBase_of_exists_stage_lift
    D.exists_stage_lift_quotSitePresheaf hF

/-- The morphism `Quot_{F/X/B} ⟶ B` is separated, and if `F` is of finite presentation it is also
locally of finite presentation. -/
@[stacks 0DM3]
theorem isSeparatedULift_and_imp_isLocallyOfFinitePresentationULift_quotSitePresheafToBase :
    IsSeparatedULift.{u + 1} B S hS D.quotSitePresheafToBase ∧
      (D.F.IsFinitePresentationOnSite →
        IsLocallyOfFinitePresentationULift.{u + 1} B S hS D.quotSitePresheafToBase) :=
  D.isSeparatedULift_and_isLocallyOfFinitePresentationULift_quotSitePresheafToBase
    D.exists_stage_lift_quotSitePresheaf

end AlgebraicGeometry.Space.QuotSituation

end
