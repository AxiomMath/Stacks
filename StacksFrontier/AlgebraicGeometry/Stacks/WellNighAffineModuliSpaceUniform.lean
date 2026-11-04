module

public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineModuliSpaceCore
public import StacksFrontier.AlgebraicGeometry.Stacks.UniformCategoricalModuliSpaceAffine
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.AffineMorphismStability
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafRepresentability
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Stability

/-!
# Reduction of Stacks 0DUR to the non-uniform statement

Let `f : 𝒳 ⟶ M` be a 1-morphism from a well-nigh affine algebraic stack to an algebraic space
which is a uniform categorical moduli space in the category of affine algebraic spaces. By
**Stacks 0DUJ** it is a uniform categorical moduli space as soon as its base change along every
flat morphism `T ⟶ M` from an affine scheme is a categorical moduli space. That base change is the
first projection of the canonical 2-fibre product `T ×_M 𝒳`, an algebraic stack by
**Stacks 04T2**, well-nigh affine by **Stacks 0DUN** because its projection to `𝒳` is the base
change of the affine morphism `T ⟶ M` (**Stacks 0CHR**), and a categorical moduli space in the
category of affine algebraic spaces because `f` is uniformly one. This file makes that reduction
(`AlgebraicGeometry.Stack.isUniformCategoricalModuliSpace_of_isWellNighAffine_of`), the
non-uniform statement being supplied as an argument.

## Main results

* `AlgebraicGeometry.Stack.isAffineHom_algebraicSpaceStackMap_of_isAffineSpace`: a morphism from an
  affine object of the site to an affine algebraic space induces an affine 1-morphism of
  algebraic stacks.
* `AlgebraicGeometry.Stack.isUniformCategoricalModuliSpace_of_isWellNighAffine_of`: the
  reduction.

## References

* [Stacks Project, Tag 0DUR](https://stacks.math.columbia.edu/tag/0DUR)
* [Stacks Project, Tag 0DUJ](https://stacks.math.columbia.edu/tag/0DUJ)
-/

universe u w

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A morphism from an affine object of the site to an affine algebraic space is affine.** -/
theorem isAffineHom_yoneda_of_isAffineSpace {T : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (M : AlgebraicSpaces B S hS)
    (hM : Space.IsAffineSpace B S hS M.obj) (a : yoneda.obj T ⟶ M.obj) :
    Space.IsAffineHom B S hS a := by
  obtain ⟨T', _, ⟨e⟩⟩ := hM
  let aA : (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶ M :=
    ObjectProperty.homMk a
  let eA : M ≅ (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS) :=
    ObjectProperty.isoMk _ e
  have h : Space.affineMorphismProperty B S hS (aA ≫ eA.hom) := by
    change Space.IsAffineHom B S hS (a ≫ e.hom)
    rw [← yoneda.map_preimage (a ≫ e.hom)]
    exact Space.isAffineHom_yoneda_map B S hS _
  exact (MorphismProperty.cancel_right_of_respectsIso (Space.affineMorphismProperty B S hS) aA
    eA.hom).1 h

/-- **A morphism from an affine object of the site to an affine algebraic space induces an affine
1-morphism of algebraic stacks.** -/
theorem isAffineHom_algebraicSpaceStackMap_of_isAffineSpace {T : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (M : AlgebraicSpaces B S hS)
    (hM : Space.IsAffineSpace B S hS M.obj) (a : yoneda.obj T ⟶ M.obj) :
    AlgebraicStacks.IsAffineHom B S hS
      (algebraicSpaceStackMap.{u, w} B S hS (isAlgebraicSpace_yoneda B S hS T) M.property a) := by
  have hrep : IsRepresentableByAlgebraicSpaces B S hS (associatedMap B S hS a).1.hom :=
    (isRepresentableByAlgebraicSpaces_iff_associatedMap B S hS a).1
      (Space.isRepresentableByAlgebraicSpaces_of_isAlgebraicSpace B S hS
        (isAlgebraicSpace_yoneda B S hS T) M.property a)
  refine ⟨hrep, ?_⟩
  have _haffBC : (Space.affineMorphismProperty B S hS).IsStableUnderBaseChange :=
    { of_isPullback := fun sq hg => Space.isAffineHom_hom_of_isPullback sq hg }
  have _haffLoc : (Space.affineMorphismProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    have _hfpqc : (Space.affineMorphismProperty B S hS).IsLocalAtTarget
        (Space.Topology.fpqc.precoverage.{u, u} B S hS) :=
      Space.isLocalAtTarget_isAffineHom_fpqc.{u, u} B S hS
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  refine (hasRelativeProperty_iff_prop_representingMap B S hS (Space.affineMorphismProperty B S hS)
    (associatedMap B S hS a).1 hrep (yoneda.obj T) M.obj (isAlgebraicSpace_yoneda B S hS T)
    M.property (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)).2 ?_
  change Space.IsAffineHom B S hS (representingMap B S hS _ _ _ _ _ _ _)
  rw [representingMap_associatedMap B S hS (yoneda.obj T) M.obj a]
  exact isAffineHom_yoneda_of_isAffineSpace B S hS M hM a

/-- **The reduction of Stacks 0DUR to its non-uniform form.** If every 1-morphism from a well-nigh
affine algebraic stack to an algebraic space which is a categorical moduli space among affine
algebraic spaces is a categorical moduli space, then every 1-morphism from a well-nigh affine
algebraic stack to an algebraic space which is a uniform categorical moduli space among affine
algebraic spaces is a uniform categorical moduli space. -/
theorem isUniformCategoricalModuliSpace_of_isWellNighAffine_of
    (H : ∀ (𝒵 : AlgebraicStacks.{u, w} B S hS), IsWellNighAffine.{u, w} B S hS 𝒵 →
      ∀ (N : AlgebraicSpaces B S hS) (g : 𝒵.val ⟶ fibredCategory B S hS N.obj),
        IsCategoricalModuliSpaceIn B S hS (fun W => Space.IsAffineSpace B S hS W.obj) N g →
          IsCategoricalModuliSpace B S hS N g)
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (h𝒳 : IsWellNighAffine.{u, w} B S hS 𝒳)
    (M : AlgebraicSpaces B S hS) (f : 𝒳.val ⟶ fibredCategory B S hS M.obj)
    (hf : IsUniformCategoricalModuliSpaceIn B S hS (fun W => Space.IsAffineSpace B S hS W.obj)
      M f) :
    IsUniformCategoricalModuliSpace B S hS M f := by
  refine isUniformCategoricalModuliSpace_of_affineFlatBaseChange B S hS M f
    fun T hT a ha P hP => ?_
  let aS :=
    algebraicSpaceStackMap.{u, w} B S hS (isAlgebraicSpace_yoneda B S hS T) M.property a.hom
  let fS : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS M.obj M.property :=
    Bicategory.InducedBicategory.mkHom f
  let Q := twoFibreProductSquareAlgebraicStacks B S hS aS fS
  have hQ₀ : Bicategory.IsTwoFibreProduct
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (associatedMap B S hS a.hom).1 f) :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _
  refine isCategoricalModuliSpace_of_isTwoFibreProduct B S hS hP hQ₀ ?_
  have hwn : IsWellNighAffine.{u, w} B S hS Q.pt :=
    isWellNighAffine_of_isAffineHom B S hS Q.snd
      (AlgebraicStacks.isAffineHom_snd_of_isTwoFibreProduct B S hS Q
        (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS aS fS)
        (isAffineHom_algebraicSpaceStackMap_of_isAffineSpace.{u, w} B S hS M hf.1 a.hom)) h𝒳
  exact H Q.pt hwn ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (associatedMap B S hS a.hom).1 f).fst
    (hf.2 _ (Space.isAffineSpace_yoneda B S hS T hT) a ha _ hQ₀)

end AlgebraicGeometry.Stack

end

end
