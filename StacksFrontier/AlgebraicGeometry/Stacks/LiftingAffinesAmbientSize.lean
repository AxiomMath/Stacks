module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesChart
public import StacksFrontier.AlgebraicGeometry.Size.SmoothCover
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalProperties

/-!
# A uniform bound on the ambient spaces of smooth lifts with quasi-compact ambient space

Let `b : Y₀ ⟶ 𝒳'` be a smooth surjective chart of the target stack by an object of the site. For
every smooth lift `ξ` whose ambient space is represented by a quasi-compact scheme `A'`, the size
of `A'` is at most `2 ^ 2 ^ size Y₀`. The bound depends only on the chart, which is what makes the
disjoint union of the ambient spaces of a family of smooth lifts an object of the site in the
proof of Stacks 0CJU.

## Main results

* `AlgebraicGeometry.Stack.EtaleSmoothLift.size_ambient_le`: the bound.

## Implementation notes

The 2-fibre product `A' ×_{𝒳'} Y₀` is an algebraic space smooth and surjective over `A'` and smooth
over `Y₀`; an atlas of it is a scheme smooth and surjective over `A'` and smooth over `Y₀`, to
which `AlgebraicGeometry.Scheme.size_le_of_smooth_surjective_of_locallyOfFiniteType` applies.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'} {hι : IsThickening ι}
  {W : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
  {hx : AlgebraicStacks.IsSmooth B S hS x}

namespace EtaleSmoothLift

/-- **The ambient spaces of smooth lifts are uniformly bounded by a chart of the target.** -/
theorem size_ambient_le (Y₀ : BigFppfOver B S hS)
    (b : (algebraicSpaceStackFunctor.{u, w} B S hS).obj
      (schemeSpace Y₀) ⟶ 𝒳')
    (hb : AlgebraicStacks.IsSmooth B S hS b) (hbs : IsSurjective B S hS b)
    (ξ : EtaleSmoothLift B S hS ι hι W x hx) (hA : ξ.ambient.obj.IsRepresentable)
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj ξ.ambient.obj.reprX)] :
    ((BigFppfOver.toScheme B S hS).obj ξ.ambient.obj.reprX).size ≤
      (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ ((BigFppfOver.toScheme B S hS).obj Y₀).size := by
  obtain ⟨V, p, q, γ, ⟨hV⟩, hp, hps⟩ := exists_smooth_surjective_twoFibreProduct
    (U := ⟨yoneda.obj Y₀, isAlgebraicSpace_yoneda B S hS Y₀⟩) ξ.ambientMap b
    (isRelativelySmooth_of_isSmooth_space_source b hb)
    (hasRelativeProperty_surjective_of_space_source b hbs)
  have hq : Space.IsSmooth B S hS q.hom :=
    isSmooth_fst_of_isTwoFibreProduct_of_isRelativelySmooth (isTwoFibreProduct_swap hV)
      (isRelativelySmooth_of_isSmooth_space_source ξ.ambientMap ξ.isSmooth_ambientMap)
  obtain ⟨Z₀, a, has, hae⟩ := V.property.exists_atlas
  let iA := ξ.ambient.obj.reprW
  let g₀ : Z₀ ⟶ ξ.ambient.obj.reprX := yoneda.preimage (a ≫ p.hom ≫ iA.inv)
  let h₀ : Z₀ ⟶ Y₀ := yoneda.preimage (a ≫ q.hom)
  have key : ∀ {T : BigFppfOver B S hS} (c : V.obj ⟶ yoneda.obj T), Space.IsSmooth B S hS c →
      Smooth ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (a ≫ c))) := by
    intro T c hc
    rw [← Space.isSmooth_yoneda_map_iff B S hS, yoneda.map_preimage]
    exact Space.isSmooth_comp B S hS (isAlgebraicSpace_yoneda B S hS Z₀) V.property
      (isAlgebraicSpace_yoneda B S hS _) a _
      (Space.isSmooth_of_isEtale B S hS V.property
        (Space.isEtale_of_presheafEtaleProperty B S hS a hae)) hc
  have : Smooth ((BigFppfOver.toScheme B S hS).map g₀) :=
    key _ (Space.isSmooth_comp B S hS V.property ξ.ambient.property
      (isAlgebraicSpace_yoneda B S hS _) _ _ hp (Space.isSmooth_of_isIso B S hS ξ.ambient.property
        (isAlgebraicSpace_yoneda B S hS _) iA.inv))
  have : Surjective ((BigFppfOver.toScheme B S hS).map g₀) := by
    refine ⟨(Space.surjective_pointsMap_yoneda_iff B S hS g₀).1 ?_⟩
    rw [yoneda.map_preimage]
    exact Space.isSurjective_comp B S hS (Space.isSurjective_of_presheafSurjective B S hS a has)
      (Space.isSurjective_comp B S hS hps (Space.isSurjective_of_isIso B S hS iA.inv))
  have := key _ hq
  exact Scheme.size_le_of_smooth_surjective_of_locallyOfFiniteType
    ((BigFppfOver.toScheme B S hS).map g₀) ((BigFppfOver.toScheme B S hS).map h₀)

end EtaleSmoothLift

end AlgebraicGeometry.Stack
