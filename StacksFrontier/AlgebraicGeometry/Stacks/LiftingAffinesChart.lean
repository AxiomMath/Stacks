module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesCategory
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.UnderlyingTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveProperties

/-!
# Smooth surjective charts and their base changes, read on algebraic spaces

Inputs to Stacks 0CJV: a smooth surjective chart of an algebraic stack by a scheme of the site,
the relative smoothness and surjectivity of 1-morphisms out of algebraic spaces, and the
smoothness and surjectivity of the projections of 2-fibre products of algebraic spaces over an
algebraic stack.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w v

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A smooth surjective chart by a scheme of the site.** Every algebraic stack receives a
smooth 1-morphism, surjective on points, from the algebraic stack of the algebraic space
represented by an object of the big fppf site. -/
theorem exists_smooth_surjective_spaceChart (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    ∃ (U : BigFppfOver B S hS) (b : (algebraicSpaceStackFunctor.{u, w} B S hS).obj
        ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ ⟶ 𝒳),
      AlgebraicStacks.IsSmooth B S hS b ∧ IsSurjective B S hS b := by
  obtain ⟨U₀, a, hasm, hasurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒳
  obtain ⟨e, hesm, hesurj⟩ := exists_smooth_surjective_algebraicSpaceStack_hom.{u, w} B S hS U₀
  exact ⟨U₀, e ≫ a, AlgebraicStacks.isSmooth_comp B S hS e a hesm hasm,
    isSurjective_comp B S hS e a hesurj hasurj⟩

/-- A 1-morphism from the stack of an algebraic space to an algebraic stack is representable by
algebraic spaces. -/
theorem isRepresentableByAlgebraicSpaces_of_space_source {X : AlgebraicSpaces B S hS}
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (b : (algebraicSpaceStackFunctor.{u, w} B S hS).obj X ⟶ 𝒳) :
    IsRepresentableByAlgebraicSpaces B S hS b.hom.hom :=
  isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace_source B S hS
    (SelfIntersection.hasRepresentableDiagonal_of_isAlgebraicStack B S hS 𝒳.val 𝒳.property)
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS X.obj X.property) b.hom

/-- A smooth 1-morphism out of the stack of an algebraic space is smooth in the relative sense
of Stacks 04XB. -/
theorem isRelativelySmooth_of_isSmooth_space_source {X : AlgebraicSpaces B S hS}
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (b : (algebraicSpaceStackFunctor.{u, w} B S hS).obj X ⟶ 𝒳)
    (hb : AlgebraicStacks.IsSmooth B S hS b) :
    IsRelativelySmooth.{u, u, u + 1} B S hS b.hom :=
  ⟨isRepresentableByAlgebraicSpaces_of_space_source b,
    (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u + 1} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS)
      ((algebraicSpaceStackFunctor.{u, w} B S hS).obj X).property 𝒳.property b.hom
      (isRepresentableByAlgebraicSpaces_of_space_source b)).mp hb⟩

/-- A 1-morphism out of the stack of an algebraic space which is surjective on points is
surjective in the relative sense of Stacks 04XB. -/
theorem hasRelativeProperty_surjective_of_space_source {X : AlgebraicSpaces B S hS}
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (b : (algebraicSpaceStackFunctor.{u, w} B S hS).obj X ⟶ 𝒳)
    (hb : IsSurjective B S hS b) :
    HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.surjectiveMorphismProperty B S hS) b.hom
      (isRepresentableByAlgebraicSpaces_of_space_source b) :=
  (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS b
    (isRepresentableByAlgebraicSpaces_of_space_source b)).mp hb

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} {U V I : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor.{u, w} B S hS).obj U ⟶ 𝒳}
  {y : (algebraicSpaceStackFunctor.{u, w} B S hS).obj V ⟶ 𝒳} {p : I ⟶ U} {q : I ⟶ V}
  {γ : (algebraicSpaceStackFunctor.{u, w} B S hS).map p ≫ x ≅
    (algebraicSpaceStackFunctor.{u, w} B S hS).map q ≫ y}

/-- **The first projection of a 2-fibre product of algebraic spaces has every relative property
of the second leg.** -/
theorem prop_fst_of_isTwoFibreProduct (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, v} B S hS)]
    (hP : Bicategory.IsTwoFibreProduct (⟨_, _, _, γ⟩ : Bicategory.TwoCommSq x y))
    (hy : HasRelativeProperty.{u, u, u + 1, v} B S hS P y.hom
      (isRepresentableByAlgebraicSpaces_of_space_source y)) :
    P p := by
  let Q := (⟨_, _, _, γ⟩ : Bicategory.TwoCommSq x y).underlying
  have hQ : Bicategory.IsTwoFibreProduct Q :=
    isTwoFibreProduct_underlying_algebraicStacks B S hS _ hP
  have h := prop_representingMap_of_hasRelativeProperty.{u, v} B S hS P y.hom
    (isRepresentableByAlgebraicSpaces_of_space_source y) hy
    ((algebraicSpaceStackFunctor.{u, w} B S hS).obj U).val x.hom Q hQ I.obj U.obj I.property
    U.property (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
  have hp : (ObjectProperty.homMk (representingMap B S hS Q.pt
      ((algebraicSpaceStackFunctor.{u, w} B S hS).obj U).val I.obj U.obj
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) Q.fst) : I ⟶ U) = p :=
    ObjectProperty.hom_ext _ (representingMap_associatedMap B S hS I.obj U.obj p.hom)
  rwa [hp] at h

/-- The second projection of a 2-fibre product of algebraic spaces is smooth when the first leg
is. -/
theorem isSmooth_fst_of_isTwoFibreProduct_of_isRelativelySmooth
    (hP : Bicategory.IsTwoFibreProduct (⟨_, _, _, γ⟩ : Bicategory.TwoCommSq x y))
    (hy : IsRelativelySmooth.{u, u, u + 1} B S hS y.hom) : Space.IsSmooth B S hS p.hom :=
  prop_fst_of_isTwoFibreProduct.{u, w, u + 1} (Space.smoothMorphismProperty B S hS) hP hy.2

/-- The first projection of a 2-fibre product of algebraic spaces is surjective on points when
the second leg is surjective in the relative sense. -/
theorem isSurjective_fst_of_isTwoFibreProduct_space
    (hP : Bicategory.IsTwoFibreProduct (⟨_, _, _, γ⟩ : Bicategory.TwoCommSq x y))
    (hy : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.surjectiveMorphismProperty B S hS)
      y.hom (isRepresentableByAlgebraicSpaces_of_space_source y)) :
    Space.IsSurjective B S hS p.hom :=
  prop_fst_of_isTwoFibreProduct.{u, w, u + 1} (Space.surjectiveMorphismProperty B S hS) hP hy

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The base change of a chart along a thickening.** For a thickening `ι : 𝒳 ⟶ 𝒳'` and a
smooth surjective 1-morphism `b` out of the stack of an algebraic space `U'`, the 2-fibre product
`U = U' ×_{𝒳'} 𝒳` is an algebraic space; its projection to `𝒳` is smooth and surjective in the
relative sense, and its projection to `U'` is a morphism of algebraic spaces. -/
theorem exists_thickeningChart {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} (ι : 𝒳 ⟶ 𝒳')
    (hι : IsThickening ι) {U' : AlgebraicSpaces B S hS}
    (b : (algebraicSpaceStackFunctor.{u, w} B S hS).obj U' ⟶ 𝒳')
    (hb : AlgebraicStacks.IsSmooth B S hS b) (hbs : IsSurjective B S hS b) :
    ∃ (U : AlgebraicSpaces B S hS) (iU : U ⟶ U')
      (a : (algebraicSpaceStackFunctor.{u, w} B S hS).obj U ⟶ 𝒳)
      (γ : (algebraicSpaceStackFunctor.{u, w} B S hS).map iU ≫ b ≅ a ≫ ι),
      Nonempty (Bicategory.IsTwoFibreProduct (⟨_, _, _, γ⟩ : Bicategory.TwoCommSq b ι)) ∧
      IsRelativelySmooth.{u, u, u + 1} B S hS a.hom ∧
      HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.surjectiveMorphismProperty B S hS) a.hom
        (isRepresentableByAlgebraicSpaces_of_space_source a) := by
  have hrep : IsRepresentableByAlgebraicSpace B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b.hom ι.hom).pt :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS _ _ _ ι.hom b.hom _
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        b.hom ι.hom) hι.1.1
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS U'.obj U'.property)
  obtain ⟨U, c, a, γ, ⟨hγ⟩⟩ := exists_isTwoFibreProduct_algebraicSpaceStackFunctor_obj b ι hrep
  obtain ⟨iU, rfl⟩ : ∃ iU : U ⟶ U', (algebraicSpaceStackFunctor.{u, w} B S hS).map iU = c :=
    ⟨_, algebraicSpaceStackFunctor_map_homMk_representingMap c⟩
  have hsw' := isTwoFibreProduct_underlying_algebraicStacks B S hS _
    (Bicategory.isTwoFibreProduct_swap hγ)
  refine ⟨U, iU, a, γ, ⟨hγ⟩, ?_, ?_⟩
  · exact isRelativelySmooth_baseChange.{u, u, u + 1} B S hS _ _ _ b.hom ι.hom _ hsw'
      (isRelativelySmooth_of_isSmooth_space_source b hb)
  · exact hasRelativeProperty_baseChange.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) _ _ _ b.hom ι.hom _ hsw'
      (isRepresentableByAlgebraicSpaces_of_space_source b)
      (hasRelativeProperty_surjective_of_space_source b hbs)

/-- **The smooth cover `W ×_𝒳 U ⟶ W`.** For a 1-morphism `x` out of the stack of an algebraic
space `W` and a 1-morphism `a` out of the stack of an algebraic space `U` which is smooth and
surjective in the relative sense, the 2-fibre product `V = W ×_𝒳 U` is an algebraic space whose
projection to `W` is smooth and surjective on points. -/
theorem exists_smooth_surjective_twoFibreProduct {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {W U : AlgebraicSpaces B S hS}
    (x : (algebraicSpaceStackFunctor.{u, w} B S hS).obj W ⟶ 𝒳)
    (a : (algebraicSpaceStackFunctor.{u, w} B S hS).obj U ⟶ 𝒳)
    (ha : IsRelativelySmooth.{u, u, u + 1} B S hS a.hom)
    (has : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.surjectiveMorphismProperty B S hS)
      a.hom (isRepresentableByAlgebraicSpaces_of_space_source a)) :
    ∃ (V : AlgebraicSpaces B S hS) (p : V ⟶ W) (q : V ⟶ U)
      (γ : (algebraicSpaceStackFunctor.{u, w} B S hS).map p ≫ x ≅
        (algebraicSpaceStackFunctor.{u, w} B S hS).map q ≫ a),
      Nonempty (Bicategory.IsTwoFibreProduct (⟨_, _, _, γ⟩ : Bicategory.TwoCommSq x a)) ∧
      Space.IsSmooth B S hS p.hom ∧ Space.IsSurjective B S hS p.hom := by
  obtain ⟨V, p, q, γ, ⟨hγ⟩⟩ := exists_isTwoFibreProduct_algebraicSpaceStackFunctor x a
  exact ⟨V, p, q, γ, ⟨hγ⟩, isSmooth_fst_of_isTwoFibreProduct_of_isRelativelySmooth hγ ha,
    isSurjective_fst_of_isTwoFibreProduct_space hγ has⟩

end AlgebraicGeometry.Stack

end
