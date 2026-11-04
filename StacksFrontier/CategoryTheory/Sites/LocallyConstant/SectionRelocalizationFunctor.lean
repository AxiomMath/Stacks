module

public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.MorphismOfTopoiSectionRelocalization

/-!
# Relocalization along a section as a functor between slice topoi

Let `f : Sh(C) ⟶ Sh(D)` be a morphism of topoi between the topoi of sheaves of sets on two small
sites `(C, J)` and `(D, K)`, and let `σ : h_V^# ⟶ f⁻¹h_Y^#` be a section, for objects `V` of `C`
and `Y` of `D`. `MorphismOfTopoi.sectionRelocalizationIso` compares `M × h_Y^#` with
`f⁻¹M × h_V^#` one object at a time. This file packages that transport as a single functor

`MorphismOfTopoi.sectionRelocalization : Sh(D/Y) ⥤ Sh(C/V)`,

namely `j_{Y!}` into the slice `Sh(D)/h_Y^#`, then `f⁻¹` on slices, then base change along `σ`,
then back across Stacks 00Y1 (`CategoryTheory.OverShriek.sheafEquivalence`), and gives the
objectwise isomorphisms as natural isomorphisms of functors.

The relocalization is not a morphism of topoi — no adjoint of the base change along `σ` is
constructed — but it does preserve finite products, each of its four factors doing so: the two
outer ones are halves of the equivalence of Stacks 00Y1, the slice of the left exact `f⁻¹` is left
exact, and base change along `σ` is a right adjoint.

## Main definitions

* `CategoryTheory.OverShriek.starCompSheafFunctorToOverIso` — the functor-level form of
  `CategoryTheory.OverShriek.starObjIso`: taking the product with `h_U^#` is restriction to `U`
  followed by `j_{U!}`.
* `MorphismOfTopoi.sectionRelocalizationNatIso` — the functor-level form of
  `MorphismOfTopoi.sectionRelocalizationIso`: the relocalization square along a section, as a
  natural isomorphism `Over.star h_Y^# ⋙ Over.post f⁻¹ ⋙ Over.pullback σ ≅ f⁻¹ ⋙ Over.star h_V^#`.
* `MorphismOfTopoi.sectionRelocalization` — the relocalization functor `Sh(D/Y) ⥤ Sh(C/V)`
  attached to a section `σ : h_V^# ⟶ f⁻¹h_Y^#`, with
  `MorphismOfTopoi.preservesFiniteProducts_sectionRelocalization`.
* `MorphismOfTopoi.sectionRelocalizationOverPullbackIso` — the relocalization of the restriction
  of `M` to `Y` is the restriction of `f⁻¹M` to `V`, naturally in `M`.
* `MorphismOfTopoi.sectionRelocalizationConstantSheafIso` — the relocalization carries the
  constant sheaf on a set to the constant sheaf on the same set, naturally in the set.

## References

* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
* [Stacks Project, Tag 00Y1](https://stacks.math.columbia.edu/tag/00Y1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.ConstantSheaf

universe w

namespace CategoryTheory.OverShriek

variable {C : Type w} [SmallCategory C] (J : GrothendieckTopology C) (U : C)

/-- Taking the product with `h_U^#` is restriction to `U` followed by `j_{U!}`, the functor-level
form of `CategoryTheory.OverShriek.starObjIso`. -/
public def starCompSheafFunctorToOverIso :
    Over.star ((presheafToSheaf J (Type w)).obj (yoneda.obj U)) ≅
      J.overPullback (Type w) U ⋙ sheafFunctorToOver (U := U) J :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (sheafEquivalence (U := U) J).counitIso.symm ≪≫
    Functor.isoWhiskerRight (starCompInverseIsoOverPullback J U)
      (sheafEquivalence (U := U) J).functor

end CategoryTheory.OverShriek

namespace MorphismOfTopoi

variable {C : Type w} [SmallCategory C] {D : Type w} [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))
  {V : C} {Y : D}
  (σ : (presheafToSheaf J (Type w)).obj (yoneda.obj V) ⟶
    f.inverseImage.obj ((presheafToSheaf K (Type w)).obj (yoneda.obj Y)))

/-- The relocalization square along a section `σ : h_V^# ⟶ f⁻¹h_Y^#`, as a natural isomorphism
of functors: taking the inverse image of an object over `h_Y^#` and then base changing along `σ` is
taking the inverse image and then the product with `h_V^#`. -/
public def sectionRelocalizationNatIso :
    Over.star ((presheafToSheaf K (Type w)).obj (yoneda.obj Y)) ⋙
        Over.post f.inverseImage ⋙ Over.pullback σ ≅
      f.inverseImage ⋙ Over.star ((presheafToSheaf J (Type w)).obj (yoneda.obj V)) :=
  haveI := f.preservesFiniteLimits
  Functor.isoWhiskerRight (starPostIso f.inverseImage _) (Over.pullback σ) ≪≫
    Functor.isoWhiskerLeft f.inverseImage (Over.starPullbackIsoStar σ)

/-- The relocalization functor `Sh(D/Y) ⥤ Sh(C/V)` attached to a section `σ : h_V^# ⟶ f⁻¹h_Y^#`.

A sheaf on `D/Y` is read as a sheaf over `h_Y^#` by `j_{Y!}`, i.e. by the functor of the
equivalence of Stacks 00Y1; the slice of `f⁻¹` carries it to a sheaf over `f⁻¹h_Y^#`; base change
along `σ` brings it over `h_V^#`; and the inverse of the equivalence of Stacks 00Y1 reads the
result back as a sheaf on `C/V`. -/
public def sectionRelocalization : Sheaf (K.over Y) (Type w) ⥤ Sheaf (J.over V) (Type w) :=
  OverShriek.sheafFunctorToOver (U := Y) K ⋙ Over.post f.inverseImage ⋙ Over.pullback σ ⋙
    (OverShriek.sheafEquivalence (U := V) J).inverse

/-- The relocalization functor preserves finite products. -/
public instance preservesFiniteProducts_sectionRelocalization :
    PreservesFiniteProducts (sectionRelocalization J K f σ) := by
  have := f.preservesFiniteLimits
  have : PreservesLimitsOfSize.{0, 0} (Over.pullback σ) :=
    (Over.mapPullbackAdj σ).rightAdjoint_preservesLimits
  unfold sectionRelocalization
  infer_instance

/-- The relocalization square along a section, read on `Sh(C)/h_Y^#` rather than on `Sh(D/Y)`:
the product with `h_Y^#`, relocalized along `σ`, is restriction to `V` after `f⁻¹`. -/
public def sectionRelocalizationStarIso :
    Over.star ((presheafToSheaf K (Type w)).obj (yoneda.obj Y)) ⋙
        Over.post f.inverseImage ⋙ Over.pullback σ ⋙
          (OverShriek.sheafEquivalence (U := V) J).inverse ≅
      f.inverseImage ⋙ J.overPullback (Type w) V :=
  Functor.isoWhiskerRight (sectionRelocalizationNatIso J K f σ)
      (OverShriek.sheafEquivalence (U := V) J).inverse ≪≫
    Functor.isoWhiskerLeft f.inverseImage (OverShriek.starCompInverseIsoOverPullback J V)

/-- The relocalization of the restriction of `M` to `Y` is the restriction of `f⁻¹M` to `V`,
naturally in `M`. -/
public def sectionRelocalizationOverPullbackIso :
    K.overPullback (Type w) Y ⋙ sectionRelocalization J K f σ ≅
      f.inverseImage ⋙ J.overPullback (Type w) V :=
  Functor.isoWhiskerRight (OverShriek.starCompSheafFunctorToOverIso K Y).symm
      (Over.post f.inverseImage ⋙ Over.pullback σ ⋙
        (OverShriek.sheafEquivalence (U := V) J).inverse) ≪≫
    sectionRelocalizationStarIso J K f σ

/-- The relocalization carries the constant sheaf on a set to the constant sheaf on the same set,
naturally in the set. -/
public def sectionRelocalizationConstantSheafIso :
    constantSheaf (K.over Y) (Type w) ⋙ sectionRelocalization J K f σ ≅
      constantSheaf (J.over V) (Type w) :=
  haveI := f.preservesFiniteLimits
  Functor.isoWhiskerRight (overPullbackConstantSheafIsoOfSmallSite K Y).symm
      (sectionRelocalization J K f σ) ≪≫
    Functor.isoWhiskerLeft (constantSheaf K (Type w))
      (sectionRelocalizationOverPullbackIso J K f σ) ≪≫
    Functor.isoWhiskerRight (inverseImageConstantSheafIsoOfSmallSites f.adj)
      (J.overPullback (Type w) V) ≪≫
    overPullbackConstantSheafIsoOfSmallSite J V

end MorphismOfTopoi

end
