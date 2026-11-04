module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfSiteFunctor
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDecent

/-!
# Finite type points and 1-morphisms locally of finite type (Stacks 06G0)

A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` which is locally of finite type
(**Stacks 06FS**, part (1)) carries the finite type points of `𝒳` (**Stacks 06FY**) into those
of `𝒴`: if `p` is a field-valued point of `𝒳` whose 1-morphism `Spec k ⟶ 𝒳` is locally of
finite type, then the 1-morphism of its image `f ∘ p` is the composite of that 1-morphism with
`f`, which is locally of finite type by **Stacks 06FT**.

The composite and the 1-morphism of the image point are 2-isomorphic rather than equal — both
are 2-Yoneda lifts (**Stacks 004B**) of the same object of the fibre of `𝒴` over the base of
`p` — so local finite type has to be moved along a 2-isomorphism, which is where the universal
smooth-diagram criterion of **Stacks 06FM** is traded for the existential one.

## Main definitions

* `AlgebraicGeometry.Stack.fieldValuedPointStackMorphism_comp_iso`: the 1-morphism of the image
  of a field-valued point is 2-isomorphic to the composite of the point's 1-morphism.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_of_twoIso`: local finite type
  depends only on the 2-isomorphism class of a 1-morphism.
* `AlgebraicGeometry.Stack.mapsTo_finiteTypePoints`: **Stacks 06G0**.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FT](https://stacks.math.columbia.edu/tag/06FT)
* [Stacks Project, Tag 06FY](https://stacks.math.columbia.edu/tag/06FY)
* [Stacks Project, Tag 06G0](https://stacks.math.columbia.edu/tag/06G0)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Being locally of finite type depends only on the 2-isomorphism class of a 1-morphism of
algebraic stacks over `S`: the universal smooth-diagram criterion of Stacks 06FM agrees with the
existential one, and the latter is invariant under a 2-isomorphism because its diagram's 2-cell
can be reindexed by whiskering. -/
theorem AlgebraicStacks.isLocallyOfFiniteType_of_twoIso
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f g : 𝒳 ⟶ 𝒴} (e : f.hom ≅ g.hom)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f) :
    AlgebraicStacks.IsLocallyOfFiniteType B S hS g :=
  (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
      (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
      𝒳.property 𝒴.property g.hom).2
    (hasPropertyOnSomeSmoothDiagram_of_twoIso B S hS
      (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h) e
      ((hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
        (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h)
        (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
        𝒳.property 𝒴.property f.hom).1 hf))

/-- The 1-morphism of the image of a field-valued point under a 1-morphism `f` of algebraic
stacks over `S`, compared with the composite of the point's own 1-morphism with `f`. The two are
2-Yoneda lifts (Stacks 004B) of the same object of the fibre over the point's base, and have the
same source, the algebraic stack of that base. -/
def fieldValuedPointStackMorphism_comp_iso
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (p : FieldValuedPoint B S hS 𝒳.val.val) :
    (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 p ≫ f).hom ≅
      (fieldValuedPointStackMorphism.{u, w} B S hS 𝒴
        (fieldValuedPointMap B S hS 𝒳.val.val f.hom.hom p)).hom :=
  Bicategory.InducedBicategory.isoMk (fieldValuedPointMorphism_comp_iso B S hS f.hom.hom p)

/-- **Stacks 06G0.** A 1-morphism of algebraic stacks over `S` which is locally of finite type
maps the set of finite type points of its source into the set of finite type points of its
target.

A field-valued representative of a finite type point of the source has a locally-of-finite-type
1-morphism, and its image represents the image point; the image's 1-morphism is 2-isomorphic to
the composite of that one with `f`, which is locally of finite type by Stacks 06FT. -/
@[stacks 06G0]
theorem mapsTo_finiteTypePoints {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f) :
    Set.MapsTo
      (Stack.pointsMap B S hS 𝒳.val.val 𝒳.val.property 𝒴.val.property f.hom.hom)
      (finiteTypePoints B S hS 𝒳) (finiteTypePoints B S hS 𝒴) := by
  intro x hx
  obtain ⟨p, hpx, hplft⟩ := hx
  refine ⟨fieldValuedPointMap B S hS 𝒳.val.val f.hom.hom p, ?_, ?_⟩
  · rw [← hpx]; rfl
  · exact AlgebraicStacks.isLocallyOfFiniteType_of_twoIso B S hS
      (fieldValuedPointStackMorphism_comp_iso.{u, w} B S hS f p)
      (AlgebraicStacks.isLocallyOfFiniteType_comp B S hS
        (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 p) f hplft hf)


/-! ### Affine charts of an object of the big fppf site over `S` -/

/-- An affine open of a scheme of the site, as an object of the site over that scheme. -/
public def affChart {B S hS} (U : BigFppfOver B S hS)
    (i : ((BigFppfOver.toScheme B S hS).obj U).affineOpens) : BigFppfOver B S hS :=
  Over.mk (⟨i.1.ι ≫ B.inclusion.map U.hom⟩ :
    B.obj (Scheme.size_lt_of_isOpenImmersion i.1.ι U.left.property) ⟶ B.obj hS)

/-- The inclusion of an affine open of a scheme of the site, as a morphism of the site. -/
public def affChartHom {B S hS} (U : BigFppfOver B S hS)
    (i : ((BigFppfOver.toScheme B S hS).obj U).affineOpens) : affChart U i ⟶ U :=
  Over.homMk ⟨i.1.ι⟩ (by rfl)

/-- The morphism of schemes underlying the inclusion of an affine open chart is the inclusion of
that open subscheme. -/
public theorem affChartHom_toScheme {B S hS} (U : BigFppfOver B S hS)
    (i : ((BigFppfOver.toScheme B S hS).obj U).affineOpens) :
    (BigFppfOver.toScheme B S hS).map (affChartHom U i) = i.1.ι := rfl

/-- An affine open chart of a scheme of the site is affine. -/
public theorem isAffine_affChart {B S hS} (U : BigFppfOver B S hS)
    (i : ((BigFppfOver.toScheme B S hS).obj U).affineOpens) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (affChart U i)) := i.2

/-- The inclusion of an affine open chart is smooth, being an open immersion. -/
public theorem smooth_affChartHom {B S hS} (U : BigFppfOver B S hS)
    (i : ((BigFppfOver.toScheme B S hS).obj U).affineOpens) :
    Smooth ((BigFppfOver.toScheme B S hS).map (affChartHom U i)) := by
  rw [affChartHom_toScheme]
  exact (inferInstance : Smooth (i : ((BigFppfOver.toScheme B S hS).obj U).Opens).ι)


end AlgebraicGeometry.Stack

end
