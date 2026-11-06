module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesLocalCompleteIntersection
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.IdentityMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.KoszulLocusOnBaseUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UnramifiedLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence

/-!
# The open locus of the base over which a family of curves is a local complete intersection

For a family of curves `G` over `S` there is an open subspace `W` of `S` such that a family of
curves `F` mapping to `G` has a local complete intersection structure morphism exactly when its
morphism of base schemes factors through `W`. This is condition (o) of Section 0E0E for the
property defining `Curves^{lci}` (Tag 0DZV): `W` is the largest open of `S` over which `G` is a
local complete intersection morphism, and its formation commutes with arbitrary base change, a
morphism of families of curves being a base change.

## Main results

* `AlgebraicGeometry.CurveFamily.exists_isOpenSubspace_lci`: the statement above.

## Implementation notes

The open subspace is `AlgebraicGeometry.Space.koszulLocusOnBase` of Tag 06CE for the triangle
formed by the structure morphism of `G`, the same morphism and the identity of the base: the
structure morphism is flat, locally of finite presentation and closed, the family being proper,
and the identity is flat and locally of finite presentation. Tag 06CE then says that a morphism
into the base factors through `W` exactly when the base change of `G` along it is a local
complete intersection morphism, and for a morphism of families `F ⟶ G` that base change is the
structure morphism of `F` up to isomorphisms on both sides, given by the cartesian square of the
morphism of families and by the identification of the base change of the identity.

## References

* [Stacks Project, Tag 0DZV](https://stacks.math.columbia.edu/tag/0DZV)
* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 06CE](https://stacks.math.columbia.edu/tag/06CE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_CurvesLciOpen :
    HasPullbacks ((BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_CurvesLciOpen
    {X Y Z : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **The open locus of local complete intersection in the base of a family of curves.** For a
family of curves `G` there is an open subspace `W` of its base such that a family of curves `F`
mapping to `G` has a local complete intersection structure morphism exactly when the morphism of
base schemes factors through `W`. -/
theorem CurveFamily.exists_isOpenSubspace_lci (G : CurveFamily B hZ) :
    ∃ W : Subfunctor (schemeSpace G.base).obj,
      Space.IsOpenSubspace B integerBase hZ W ∧
      ∀ (F : CurveFamily B hZ) (a : F ⟶ G),
        IsLciFamily B hZ F ↔
          ∃ t : (schemeSpace F.base).obj ⟶ W.toFunctor,
            t ≫ W.ι = (schemeSpaceMap a.baseMap).hom := by
  let Zs := (schemeSpace G.base).obj
  have hZs : IsAlgebraicSpace B integerBase hZ Zs := (schemeSpace G.base).property
  let p : G.total.obj ⟶ Zs := G.toBase.hom
  have hpc : Space.IsClosedMorphism B integerBase hZ p :=
    Space.isClosed_of_universallyClosed B integerBase hZ hZs p G.proper.2.2
  have hfq : p ≫ 𝟙 Zs = p := Category.comp_id p
  refine ⟨Space.koszulLocusOnBase B integerBase hZ p p,
    Space.isOpenSubspace_koszulLocusOnBase B integerBase hZ hZs p p hpc, fun F a => ?_⟩
  let g : (schemeSpace F.base).obj ⟶ Zs := (schemeSpaceMap a.baseMap).hom
  rw [Space.factorsThrough_koszulLocusOnBase_iff B integerBase hZ G.total.property hZs hZs p p
    (𝟙 Zs) hfq G.flat G.finitePresentation.1 hpc (Space.isFlat_id B integerBase hZ hZs)
    (Space.isLocallyOfFinitePresentation_id B integerBase hZ hZs) _
    (schemeSpace F.base).property g]
  -- the structure morphism of `F` is the projection of the fibre product, up to isomorphism
  have hsq : IsPullback a.totalMap.hom F.toBase.hom p g :=
    AlgebraicSpaces.isPullback_hom B integerBase hZ a.cartesian
  -- the base change of `p` along `g` is that projection, up to the base change of the identity
  have hbc : Space.baseChangeOverBase B integerBase hZ p p (𝟙 Zs) hfq g ≫
      pullback.snd (𝟙 Zs) g = pullback.snd p g := pullback.lift_snd _ _ _
  show Space.IsLocalCompleteIntersection B integerBase hZ F.toBase.hom ↔
    Space.IsLocalCompleteIntersection B integerBase hZ
      (Space.baseChangeOverBase B integerBase hZ p p (𝟙 Zs) hfq g)
  let P : MorphismProperty ((BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u) := fun _ _ f =>
    Space.HoldsOnEveryEtaleChart B integerBase hZ
      (@_root_.AlgebraicGeometry.IsLocalCompleteIntersectionMorphism.{u} :
        MorphismProperty Scheme.{u}) f
  have : P.RespectsIso := Space.holdsOnEveryEtaleChart_respectsIso_presheaf B integerBase hZ _
  have h₂ : P (pullback.snd p g) ↔
      P (Space.baseChangeOverBase B integerBase hZ p p (𝟙 Zs) hfq g) := by
    rw [← hbc]
    exact MorphismProperty.cancel_right_of_respectsIso P _ _
  rw [← hsq.isoPullback_hom_snd]
  exact (MorphismProperty.cancel_left_of_respectsIso P hsq.isoPullback.hom _).trans h₂

end AlgebraicGeometry

end
