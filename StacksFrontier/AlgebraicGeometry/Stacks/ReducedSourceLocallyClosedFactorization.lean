module

public import StacksFrontier.AlgebraicGeometry.Stacks.FibreObjectTwoYoneda
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedStackFactorization
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges

/-!
# Objects over a reduced scheme whose points lie in a locally closed substack

Let `P` cut out a locally closed substack of an algebraic stack `𝒳` over `S`, and let `y` be an
object of `𝒳` over an object `T` of the big fppf site of `S` whose underlying scheme is reduced.
If every point of `T` is carried by `y` into the points of the substack, then `y` itself lies in
the substack.

## Main results

* `AlgebraicGeometry.Space.isClosedImmersion_of_isImmersion_of_isSurjective`: a morphism of
  presheaves on the big fppf site representable by immersions and surjective on points is
  representable by closed immersions.
* `AlgebraicGeometry.Stack.isClosedImmersion_of_isImmersion_of_isSurjective`: the same for a
  1-morphism of algebraic stacks.
* `AlgebraicGeometry.Stack.isImmersion_fullSubcategoryInclusion_inverseImage`: the preimage of a
  locally closed substack under a 1-morphism is a locally closed substack.
* `AlgebraicGeometry.Stack.prop_obj_of_range_pointsMap_subset`: a 1-morphism `f : 𝒴 ⟶ 𝒳` whose
  points land in a locally closed substack carries every object of `𝒴` over a reduced scheme
  into the substack.
* `AlgebraicGeometry.Stack.prop_of_range_pointsMap_subset`: an object of `𝒳` over a reduced
  scheme whose points land in a locally closed substack lies in it.
* `AlgebraicGeometry.Stack.prop_obj_of_forall_pointsMap_mem`,
  `AlgebraicGeometry.Stack.prop_of_forall_pointsMap_mem`: the same with the hypothesis on points
  stated pointwise.

## References

* [Stacks Project, Tag 050A](https://stacks.math.columbia.edu/tag/050A)
* [Stacks Project, Tag 050B](https://stacks.math.columbia.edu/tag/050B)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u w

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism of presheaves on the big fppf site of `S` which is representable by immersions of
schemes and surjective on points is representable by closed immersions. -/
theorem isClosedImmersion_of_isImmersion_of_isSurjective
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) (hi : IsImmersion B S hS f)
    (hs : IsSurjective B S hS f) :
    IsClosedImmersion B S hS f := by
  refine ⟨hi.rep, fun a b g fst snd h => ?_⟩
  have : AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map snd) :=
    hi.2 g fst snd h
  exact .of_isPreimmersion _ (Set.range_eq_univ.mpr (surjective_of_isSurjective_yonedaMap B S hS
    snd (surjective_pointsMap_of_isPullback B S hS h hs)) ▸ isClosed_univ)

end Space

namespace Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A 1-morphism of algebraic stacks which is an immersion and surjective on points is a closed
immersion. -/
theorem isClosedImmersion_of_isImmersion_of_isSurjective {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (hi : AlgebraicStacks.IsImmersion B S hS f) (hs : IsSurjective B S hS f) :
    AlgebraicStacks.IsClosedImmersion B S hS f := by
  have hsurj := (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS f hi.1).mp hs
  exact ⟨hi.1, fun U y hy F hF e =>
    Space.isClosedImmersion_of_isImmersion_of_isSurjective _ (hi.2 U y hy F hF e)
      (hsurj U y hy F hF e)⟩

/-- The preimage of a locally closed substack of `𝒳` under a 1-morphism `f : 𝒴 ⟶ 𝒳` is a locally
closed substack of `𝒴`: its inclusion is an immersion. -/
theorem isImmersion_fullSubcategoryInclusion_inverseImage
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒴 ⟶ 𝒳)
    {P : ObjectProperty 𝒳.val.val.obj} [P.IsClosedUnderIsomorphisms]
    (hA : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (hi : AlgebraicStacks.IsImmersion B S hS (fullSubcategoryInclusion 𝒳 P hA)) :
    AlgebraicStacks.IsImmersion B S hS
      (fullSubcategoryInclusion 𝒴 (P.inverseImage f.hom.hom.toFunctor)
        (isAlgebraicStack_inverseImage f P hA)) :=
  AlgebraicStacks.isImmersion_snd_of_isTwoFibreProduct B S hS (inverseImageSquare f P hA).swap
    (Bicategory.isTwoFibreProduct_swap (isTwoFibreProduct_inverseImageSquare f P hA)) hi

/-- Let `f : 𝒴 ⟶ 𝒳` be a 1-morphism of algebraic stacks over `S` and let `P` cut out a locally
closed substack of `𝒳`. If the image of `|f|` lies in the points of the substack, then `f`
carries every object of `𝒴` lying over an object of the site with reduced underlying scheme into
the substack. -/
theorem prop_obj_of_range_pointsMap_subset {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒴 ⟶ 𝒳)
    {P : ObjectProperty 𝒳.val.val.obj} (hP : IsLocallyClosedSubstack 𝒳 P)
    (hA : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (hsub : Set.range (AlgebraicStacks.pointsMap B S hS f) ⊆
      Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 P hA)))
    {U : BigFppfOver B S hS} (hU : IsReduced ((BigFppfOver.toScheme B S hS).obj U))
    (x : 𝒴.val.val.p.Fiber U) :
    P (f.hom.hom.obj x.1) := by
  have := hP.1
  have hi := isImmersion_fullSubcategoryInclusion_inverseImage B S hS f hA hP.2.choose_spec
  have hs := isSurjective_fullSubcategoryInclusion_inverseImage B S hS f hA hsub
  exact prop_of_isReduced_fiber B S hS (isAlgebraicStack_inverseImage f P hA) hi.1
    (isClosedImmersion_of_isImmersion_of_isSurjective B S hS _ hi hs).2
    ((pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS _ hi.1).mp hs) hU x

/-- `AlgebraicGeometry.Stack.prop_obj_of_range_pointsMap_subset` with the hypothesis on points
stated pointwise, for the algebraicity proof carried by the locally closed substack condition. -/
theorem prop_obj_of_forall_pointsMap_mem {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒴 ⟶ 𝒳)
    {P : ObjectProperty 𝒳.val.val.obj} (hP : IsLocallyClosedSubstack 𝒳 P)
    (hsub : ∀ q : AlgebraicStacks.points B S hS 𝒴, AlgebraicStacks.pointsMap B S hS f q ∈
      Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 P hP.2.choose)))
    {U : BigFppfOver B S hS} (hU : IsReduced ((BigFppfOver.toScheme B S hS).obj U))
    (x : 𝒴.val.val.p.Fiber U) :
    P (f.hom.hom.obj x.1) :=
  prop_obj_of_range_pointsMap_subset B S hS f hP hP.2.choose (Set.range_subset_iff.mpr hsub) hU x

/-- Let `P` cut out a locally closed substack of an algebraic stack `𝒳` over `S` and let `y` be
an object of `𝒳` over an object `T` of the site whose underlying scheme is reduced. If the image
of the map on points of the 1-morphism `(Sch/T)_fppf ⟶ 𝒳` named by `y` lies in the points of the
substack, then `P y`. -/
theorem prop_of_range_pointsMap_subset {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {P : ObjectProperty 𝒳.val.val.obj} (hP : IsLocallyClosedSubstack 𝒳 P)
    (hA : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    {T : BigFppfOver B S hS} (hT : IsReduced ((BigFppfOver.toScheme B S hS).obj T))
    (y : 𝒳.val.val.p.Fiber T)
    (hsub : Set.range (AlgebraicStacks.pointsMap B S hS
        (Bicategory.InducedBicategory.mkHom (X := schemeStack.{u, w} B S hS T) (Y := 𝒳)
          (fibreObjectFibredMap B S hS 𝒳.val T y))) ⊆
      Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 P hA))) :
    P y.1 := by
  have := hP.1
  let L := Functor.TwoYoneda.chosenLift 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids T y (Over.mk (𝟙 T))
  exact prop_of_isHomLift_isIso B S hS (𝟙 T) inferInstance L.φ L.isStronglyCartesian.toIsHomLift
    (prop_obj_of_range_pointsMap_subset B S hS _ hP hA hsub hT ⟨Over.mk (𝟙 T), rfl⟩)

/-- `AlgebraicGeometry.Stack.prop_of_range_pointsMap_subset` with the hypothesis on points
stated pointwise, for the algebraicity proof carried by the locally closed substack condition. -/
theorem prop_of_forall_pointsMap_mem {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {P : ObjectProperty 𝒳.val.val.obj} (hP : IsLocallyClosedSubstack 𝒳 P)
    {T : BigFppfOver B S hS} (hT : IsReduced ((BigFppfOver.toScheme B S hS).obj T))
    (y : 𝒳.val.val.p.Fiber T)
    (hsub : ∀ q : AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS T),
      AlgebraicStacks.pointsMap B S hS
          (Bicategory.InducedBicategory.mkHom (X := schemeStack.{u, w} B S hS T) (Y := 𝒳)
            (fibreObjectFibredMap B S hS 𝒳.val T y)) q ∈
        Set.range (AlgebraicStacks.pointsMap B S hS
          (fullSubcategoryInclusion 𝒳 P hP.2.choose))) :
    P y.1 :=
  prop_of_range_pointsMap_subset B S hS hP hP.2.choose hT y (Set.range_subset_iff.mpr hsub)

end Stack

end AlgebraicGeometry

end
