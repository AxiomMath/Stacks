module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSliceGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactOpenGaloisDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallZariskiSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroScheme

/-!
# Thickenings, open subspaces and Noetherianity across a change of base scheme

Let `g : T ⟶ S` be a morphism of a big fppf site and `Λ_g` the lower-shriek extension
`CategoryTheory.OverShriek.relocalizePresheafFunctor g` of Stacks 03I5 part (2). This file
reflects three conditions along `Λ_g`, in both directions:

* being a thickening of an algebraic space (Stacks 05ZK part (1)),
* being an open subspace (Stacks 02YU part (2)), together with the finite presentation of the
  inclusion of a closed subspace (Stacks 03XP part (3)),
* being Noetherian (Stacks 03EA).

The specialisation to `g : S ⟶ Spec ℤ`, that is to
`AlgebraicGeometry.Space.viewOverIntegers`, is the "we may view `X` as an algebraic space over
`Spec ℤ`" move of several arguments of the source, read backwards: each of the three conditions
holds for the view over the terminal scheme exactly when it holds over `S`.

## Main definitions

* `CategoryTheory.OverShriek.relocalizeSubfunctorPreimage` and
  `CategoryTheory.OverShriek.relocalizeSubfunctorEquiv`: the subfunctors of `Λ_g F` are exactly
  the subfunctors of `F`, cut out by `AlgebraicGeometry.Space.relocalizeSubfunctor`.
* `AlgebraicGeometry.Space.openSubspacesRelocalizeEquiv`,
  `AlgebraicGeometry.Space.closedSubspacesRelocalizeEquiv` and their specialisations
  `AlgebraicGeometry.Space.openSubspacesViewOverIntegersEquiv` and
  `AlgebraicGeometry.Space.closedSubspacesViewOverIntegersEquiv`: the resulting bijections of
  categories of open and of closed subspaces.

## Main results

* `AlgebraicGeometry.Space.isOpenSubspace_relocalizeSubfunctor_iff` and
  `AlgebraicGeometry.Space.isClosedSubspace_relocalizeSubfunctor_iff`: a subfunctor of `F` is an
  open (resp. closed) subspace exactly when the subfunctor of `Λ_g F` it cuts out is.
* `AlgebraicGeometry.Space.isThickening_relocalizeSubfunctor_iff` and
  `AlgebraicGeometry.Space.isThickening_viewOverIntegers_iff`: being a thickening is unchanged.
* `AlgebraicGeometry.Space.dense_subspacePointSet_relocalizeSubfunctor_iff`: so is density of the
  set of points of the subspace, the point spaces being homeomorphic.
* `AlgebraicGeometry.Space.isFinitePresentation_relocalizeSubfunctor_ι_iff`: so is finite
  presentation of the inclusion.
* `AlgebraicGeometry.Space.hasEtaleLocalProperty_relocalize_iff`: so is an étale-local property
  of schemes.
* `AlgebraicGeometry.Space.isNoetherian_viewOverIntegers_iff`: being Noetherian is unchanged by
  the passage to the view over the terminal scheme.

## Implementation notes

**Why subfunctors are reflected, and not merely carried.** A section of `Λ_g F` over `(W, a)` is
a factorization `ψ : W ⟶ T` of `a` through `g` together with a section of `F` over `(W, ψ)`, so
`Λ_g F` *is* the disjoint union of the values of `F` over all factorizations. Reading a subfunctor
of `Λ_g F` at the tautological factorization therefore recovers a subfunctor of `F`, and the two
constructions are mutually inverse: that is
`CategoryTheory.OverShriek.relocalizeSubfunctorEquiv`, whose two round trips are read off
`CategoryTheory.OverShriek.mem_range_relocalizePresheafFunctor_map_ι`. Without it an open
subspace of the view could not be brought back, only pushed forward.

**Each condition is reflected by the conjunct it is made of.** Being an open or closed subspace is
algebraicity of the subfunctor, which is Stacks 04SG
(`AlgebraicGeometry.isAlgebraicSpace_viewOver_iff`), together with the inclusion being an open or
closed immersion, which is a property of a morphism tested on representable base changes
(`AlgebraicGeometry.presheaf_relocalizeMap` and `AlgebraicGeometry.presheaf_relocalizeMap_of`).
Being a thickening adds surjectivity on points, which is the bijectivity of
`AlgebraicGeometry.Space.pointsRelocalize`. Being Noetherian is quasi-compactness
(`AlgebraicGeometry.Space.isQuasiCompactSpace_relocalize_iff`), absolute quasi-separatedness —
which for the view over the terminal scheme is the self-comparison
`AlgebraicGeometry.Space.viewOverIntegersSelfIso` — and local Noetherianity, an étale-local
property of schemes.

**No algebraicity is assumed where it is not needed.** The étale-local reflection
`AlgebraicGeometry.Space.hasEtaleLocalProperty_relocalize_iff` is proved from the fact that every
chart of `Λ_g F` is the extension of a chart (`AlgebraicGeometry.exists_relocalizeChart`), which
needs no algebraicity hypothesis; the one-directional
`AlgebraicGeometry.Space.hasEtaleLocalProperty_of_relocalize` assumes `F` is an algebraic space
because it argues through Stacks 03E8 instead.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
* [Stacks Project, Tag 03EA](https://stacks.math.columbia.edu/tag/03EA)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 0CYZ](https://stacks.math.columbia.edu/tag/0CYZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v w u

namespace CategoryTheory.OverShriek

variable {C : Type w} [Category.{v} C] {U V : C} (f : V ⟶ U)
  {G : (Over V)ᵒᵖ ⥤ Type v}

/-- **The subfunctor of `F` underlying a subfunctor of `Λ_f F`.** A section of `Λ_f F` over
`(W, a)` is a factorization `ψ` of `a` through `f` together with a section of `F` over `(W, ψ)`;
this reads the given subfunctor at the tautological factorization. -/
def relocalizeSubfunctorPreimage
    (A : Subfunctor ((relocalizePresheafFunctor f).obj G)) : Subfunctor G :=
  Subfunctor.preimage (relocalizeRestrictSubfunctor f A) (relocalizeToRestricted f (𝟙 _))

/-- A section of `F` over `(W, ψ)` lies in the subfunctor underlying `A` exactly when the section
`(ψ, s)` of `Λ_f F` over `(W, ψ ≫ f)` lies in `A`. -/
theorem mem_relocalizeSubfunctorPreimage
    (A : Subfunctor ((relocalizePresheafFunctor f).obj G)) (W : (Over V)ᵒᵖ) (s : G.obj W) :
    s ∈ (relocalizeSubfunctorPreimage f A).obj W ↔
      (⟨⟨W.unop.hom, s⟩, rfl⟩ :
          ((relocalizePresheafFunctor f).obj G).obj (op (Over.mk (W.unop.hom ≫ f)))) ∈
        A.obj (op (Over.mk (W.unop.hom ≫ f))) :=
  Iff.rfl

/-- Membership of a section of `Λ_f F` in a subfunctor does not depend on which factorization of
the structure morphism the object of the site is presented by. -/
private theorem mem_mk_iff {A : Subfunctor ((relocalizePresheafFunctor f).obj G)}
    {L : C} {a : L ⟶ U} {ψ : L ⟶ V} (h : ψ ≫ f = a) (s : G.obj (op (Over.mk ψ))) :
    (⟨⟨ψ, s⟩, h⟩ : ((relocalizePresheafFunctor f).obj G).obj (op (Over.mk a))) ∈
        A.obj (op (Over.mk a)) ↔
      (⟨⟨ψ, s⟩, rfl⟩ :
          ((relocalizePresheafFunctor f).obj G).obj (op (Over.mk (ψ ≫ f)))) ∈
        A.obj (op (Over.mk (ψ ≫ f))) := by
  subst h
  rfl

/-- **Every subfunctor of `Λ_f F` is cut out by a subfunctor of `F`**: the image of the extension
of the inclusion of the subfunctor underlying it is itself. -/
theorem range_map_ι_relocalizeSubfunctorPreimage
    (A : Subfunctor ((relocalizePresheafFunctor f).obj G)) :
    Subfunctor.range ((relocalizePresheafFunctor f).map
      (relocalizeSubfunctorPreimage f A).ι) = A := by
  refine Subfunctor.ext (funext fun W => Set.ext fun x => ?_)
  rw [mem_range_relocalizePresheafFunctor_map_ι, mem_relocalizeSubfunctorPreimage]
  exact (mem_mk_iff f x.property x.val.snd).symm

/-- **A subfunctor of `F` is recovered from the subfunctor of `Λ_f F` it cuts out.** -/
theorem relocalizeSubfunctorPreimage_range_map_ι (Z : Subfunctor G) :
    relocalizeSubfunctorPreimage f
      (Subfunctor.range ((relocalizePresheafFunctor f).map Z.ι)) = Z := by
  refine Subfunctor.ext (funext fun W => Set.ext fun s => ?_)
  refine Iff.trans (mem_relocalizeSubfunctorPreimage f _ W s) ?_
  exact mem_range_relocalizePresheafFunctor_map_ι f Z
    (op (Over.mk (W.unop.hom ≫ f))) ⟨⟨W.unop.hom, s⟩, rfl⟩

/-- **The subfunctors of `Λ_f F` are the subfunctors of `F`.** The bijection sends a subfunctor of
`F` to the image of the extension of its inclusion and is inverse to
`CategoryTheory.OverShriek.relocalizeSubfunctorPreimage`. -/
def relocalizeSubfunctorEquiv :
    Subfunctor G ≃ Subfunctor ((relocalizePresheafFunctor f).obj G) where
  toFun Z := Subfunctor.range ((relocalizePresheafFunctor f).map Z.ι)
  invFun := relocalizeSubfunctorPreimage f
  left_inv := relocalizeSubfunctorPreimage_range_map_ι f
  right_inv := range_map_ι_relocalizeSubfunctorPreimage f

end CategoryTheory.OverShriek

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Finite presentation and étale-local properties across a change of base scheme -/

section Properties

variable (B : BigFppfSite.{u}) (T S : Scheme.{u}) (hT : B.Contains T) (hS : B.Contains S)
  (g : B.obj hT ⟶ B.obj hS)

/-- **Being locally of finite presentation is unchanged by the lower-shriek extension of Stacks
03I5 part (2)**, being an every-étale-chart condition. -/
theorem isLocallyOfFinitePresentation_relocalizeMap_iff
    {X Y : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u} (k : X ⟶ Y) :
    IsLocallyOfFinitePresentation B S hS ((OverShriek.relocalizePresheafFunctor g).map k) ↔
      IsLocallyOfFinitePresentation B T hT k :=
  holdsOnEveryEtaleChart_relocalizeMap_iff B T S hT hS g _ k

/-- **Being of finite presentation is unchanged by the lower-shriek extension of Stacks 03I5
part (2)**, Stacks 03XP part (3): each of its three conjuncts is. -/
theorem isFinitePresentation_relocalizeMap_iff
    {X Y : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u} (k : X ⟶ Y) :
    IsFinitePresentation B S hS ((OverShriek.relocalizePresheafFunctor g).map k) ↔
      IsFinitePresentation B T hT k :=
  and_congr (isLocallyOfFinitePresentation_relocalizeMap_iff B T S hT hS g k)
    (and_congr (isQuasiCompact_relocalize_iff B T hT S hS g k)
      (isQuasiSeparated_relocalize_iff B T hT S hS g k))

/-- **An étale-local property of schemes is unchanged by the lower-shriek extension of Stacks
03I5 part (2)**, Stacks 03E6. The extension of a surjective étale atlas is one by the same
scheme, and conversely every chart of the extension is the extension of a chart
(`AlgebraicGeometry.exists_relocalizeChart`), with surjectivity and étaleness unchanged
(`AlgebraicGeometry.presheaf_relocalizeChart_iff`). No algebraicity is needed. -/
theorem hasEtaleLocalProperty_relocalize_iff (P : ObjectProperty Scheme.{u})
    [P.IsLocal Scheme.etalePrecoverage] (F : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u) :
    HasEtaleLocalProperty B S hS ((OverShriek.relocalizePresheafFunctor g).obj F) P ↔
      HasEtaleLocalProperty B T hT F P := by
  have _ : MorphismProperty.RespectsIso (@AlgebraicGeometry.Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : MorphismProperty.RespectsIso (@AlgebraicGeometry.Surjective.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  constructor
  · rintro ⟨U', a', hsurj', hetale', hP'⟩
    obtain ⟨ψ, hψ, a, rfl⟩ := exists_relocalizeChart B T S hT hS g U' a'
    exact ⟨Over.mk ψ, a,
      (presheaf_relocalizeChart_iff B T S hT hS g _ a).1
        ((MorphismProperty.cancel_left_of_respectsIso _ _ _).1 hsurj'),
      (presheaf_relocalizeChart_iff B T S hT hS g _ a).1
        ((MorphismProperty.cancel_left_of_respectsIso _ _ _).1 hetale'), hP'⟩
  · rintro ⟨A, a, hsurj, hetale, hP⟩
    exact ⟨(Over.map g).obj A, relocalizeChart B T S hT hS g a,
      (presheaf_relocalizeChart_iff B T S hT hS g _ a).2 hsurj,
      (presheaf_relocalizeChart_iff B T S hT hS g _ a).2 hetale, hP⟩

end Properties

/-! ### Subspaces across a change of base scheme -/

section Subspaces

variable (B : BigFppfSite.{u}) {T S : Scheme.{u}} (hT : B.Contains T) (hS : B.Contains S)
  (g : B.obj hT ⟶ B.obj hS) {X : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u}

/-- The subfunctor of `Λ_g X` cut out by a subfunctor of `X` is
`CategoryTheory.OverShriek.relocalizeSubfunctorEquiv` of it. -/
theorem relocalizeSubfunctorEquiv_apply (Z : Subfunctor X) :
    OverShriek.relocalizeSubfunctorEquiv g Z = relocalizeSubfunctor B hT hS g Z :=
  rfl

/-- Algebraicity of a subfunctor is unchanged by the lower-shriek extension, Stacks 04SG. -/
private theorem isAlgebraicSpace_relocalizeSubfunctor_iff (Z : Subfunctor X) :
    IsAlgebraicSpace B S hS (relocalizeSubfunctor B hT hS g Z).toFunctor ↔
      IsAlgebraicSpace B T hT Z.toFunctor :=
  ⟨fun h => (isAlgebraicSpace_viewOver_iff B T S hT hS g Z.toFunctor).1
      (h.of_iso (relocalizeSubfunctorIso B hT hS g Z).symm),
    fun h => ((isAlgebraicSpace_viewOver_iff B T S hT hS g Z.toFunctor).2 h).of_iso
      (relocalizeSubfunctorIso B hT hS g Z)⟩

/-- A property of the inclusion of a subfunctor tested on representable base changes is unchanged
by the lower-shriek extension. -/
private theorem presheaf_relocalizeSubfunctor_ι_iff (Q : MorphismProperty Scheme.{u})
    [Q.RespectsIso] (Z : Subfunctor X) :
    (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (relocalizeSubfunctor B hT hS g Z).ι ↔
      (Q.inverseImage (BigFppfOver.toScheme B T hT)).presheaf Z.ι := by
  have _ : (Q.inverseImage (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have hι := relocalizeSubfunctorIso_hom_ι B hT hS g Z
  refine ⟨fun h => presheaf_relocalizeMap_of B T S hT hS g Q Z.ι ?_, fun h => ?_⟩
  · rw [← hι]
    exact MorphismProperty.RespectsIso.precomp _ _ _ h
  · have h' := presheaf_relocalizeMap B T S hT hS g Q Z.ι h
    rw [← hι] at h'
    exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).1 h'

/-- **Being an open subspace is unchanged by the lower-shriek extension of Stacks 03I5 part
(2).** Algebraicity of the subfunctor is Stacks 04SG, and being an open immersion is a property
of a morphism of presheaves tested on representable base changes. -/
theorem isOpenSubspace_relocalizeSubfunctor_iff (Z : Subfunctor X) :
    IsOpenSubspace B S hS (relocalizeSubfunctor B hT hS g Z) ↔ IsOpenSubspace B T hT Z := by
  have _ : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact and_congr (isAlgebraicSpace_relocalizeSubfunctor_iff B hT hS g Z)
    (presheaf_relocalizeSubfunctor_ι_iff B hT hS g
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) Z)

/-- **Being a closed subspace is unchanged by the lower-shriek extension of Stacks 03I5 part
(2).** The implication from `T` to `S` is
`AlgebraicGeometry.Space.isClosedSubspace_relocalizeSubfunctor`. -/
theorem isClosedSubspace_relocalizeSubfunctor_iff (Z : Subfunctor X) :
    IsClosedSubspace B S hS (relocalizeSubfunctor B hT hS g Z) ↔ IsClosedSubspace B T hT Z := by
  have _ : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact ⟨fun h => ⟨(isAlgebraicSpace_relocalizeSubfunctor_iff B hT hS g Z).1 h.1,
      (presheaf_relocalizeSubfunctor_ι_iff B hT hS g
        (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) Z).1 h.2⟩,
    isClosedSubspace_relocalizeSubfunctor B hT hS g⟩

/-- **Reading points over the larger base is a homeomorphism.** It is the bijection
`AlgebraicGeometry.Space.pointsRelocalize_bijective`, continuous and closed. -/
noncomputable def pointsRelocalizeHomeomorph (F : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u) :
    points B T hT F ≃ₜ points B S hS ((OverShriek.relocalizePresheafFunctor g).obj F) :=
  (Equiv.ofBijective _ (pointsRelocalize_bijective B T S hT hS g F)).toHomeomorphOfContinuousClosed
    (continuous_pointsRelocalize B T S hT hS g F) (isClosedMap_pointsRelocalize B T S hT hS g F)

/-- The homeomorphism of point spaces is `AlgebraicGeometry.Space.pointsRelocalize`. -/
theorem pointsRelocalizeHomeomorph_apply (F : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u)
    (x : points B T hT F) :
    pointsRelocalizeHomeomorph B hT hS g F x = pointsRelocalize B T S hT hS g F x :=
  rfl

/-- **The set of points of a subspace is dense exactly when the set of points of the subspace it
cuts out in `Λ_g X` is dense.** The two sets correspond under the homeomorphism
`AlgebraicGeometry.Space.pointsRelocalizeHomeomorph`. -/
theorem dense_subspacePointSet_relocalizeSubfunctor_iff (Z : Subfunctor X) :
    Dense (Set.range (pointsMap B S hS _ (relocalizeSubfunctor B hT hS g Z).ι)) ↔
      Dense (Set.range (pointsMap B T hT _ Z.ι)) := by
  have hbij := pointsRelocalize_bijective B T S hT hS g X
  have hcont := continuous_pointsRelocalize B T S hT hS g X
  have hclosed := isClosedMap_pointsRelocalize B T S hT hS g X
  rw [range_pointsMap_relocalizeSubfunctor_ι B hT hS g Z]
  refine ⟨fun h => ?_, fun h => hbij.2.denseRange.dense_image hcont h⟩
  have hsub : Set.univ ⊆ pointsRelocalize B T S hT hS g X ''
      closure (Set.range (pointsMap B T hT _ Z.ι)) := by
    rw [← h.closure_eq]
    exact closure_minimal (Set.image_mono subset_closure) (hclosed _ isClosed_closure)
  rw [dense_iff_closure_eq]
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨y, hy, hyx⟩ := hsub (Set.mem_univ (pointsRelocalize B T S hT hS g X x))
  exact hbij.1 hyx ▸ hy

/-- **Surjectivity on points of the inclusion of a subspace is unchanged by the lower-shriek
extension.** -/
theorem surjective_pointsMap_relocalizeSubfunctor_ι_iff (Z : Subfunctor X) :
    Function.Surjective (pointsMap B S hS _ (relocalizeSubfunctor B hT hS g Z).ι) ↔
      Function.Surjective (pointsMap B T hT _ Z.ι) := by
  have hbij := pointsRelocalize_bijective B T S hT hS g X
  rw [← Set.range_eq_univ, ← Set.range_eq_univ,
    range_pointsMap_relocalizeSubfunctor_ι B hT hS g Z]
  refine ⟨fun h => Set.eq_univ_of_forall fun x => ?_, fun h => ?_⟩
  · obtain ⟨y, hy, hyx⟩ := h.symm ▸ Set.mem_univ (pointsRelocalize B T S hT hS g X x)
    exact hbij.1 hyx ▸ hy
  · rw [h, Set.image_univ]
    exact hbij.2.range_eq

/-- **Being a thickening of an algebraic space is unchanged by the lower-shriek extension of
Stacks 03I5 part (2)**, Stacks 05ZK part (1): it is being a closed subspace together with
surjectivity on points, and both are unchanged. -/
theorem isThickening_relocalizeSubfunctor_iff (Y : AlgebraicSpaces B T hT) (Z : Subfunctor Y.1) :
    IsThickening B S hS ⟨_, isAlgebraicSpace_relocalize' B hT hS g Y.1 Y.2⟩
        (relocalizeSubfunctor B hT hS g Z) ↔
      IsThickening B T hT Y Z :=
  and_congr (isClosedSubspace_relocalizeSubfunctor_iff B hT hS g Z)
    (surjective_pointsMap_relocalizeSubfunctor_ι_iff B hT hS g Z)

/-- **The open subspaces of `Λ_g F` are the open subspaces of `F`**, Stacks 02YU part (2) across
the equivalence of Stacks 04SG. -/
def openSubspacesRelocalizeEquiv (F : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u) :
    OpenSubspaces B T hT F ≃
      OpenSubspaces B S hS ((OverShriek.relocalizePresheafFunctor g).obj F) :=
  (OverShriek.relocalizeSubfunctorEquiv g).subtypeEquiv fun Z =>
    (isOpenSubspace_relocalizeSubfunctor_iff B hT hS g Z).symm

/-- **The closed subspaces of `Λ_g F` are the closed subspaces of `F`**, Stacks 0CYZ across the
equivalence of Stacks 04SG. This is the essential surjectivity that
`AlgebraicGeometry.Space.exists_closedSubspaces_viewOverIntegers` does not give: that result
carries a family of closed subspaces of `F` forward, while this bijection also brings a closed
subspace of `Λ_g F` back. -/
def closedSubspacesRelocalizeEquiv (F : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u) :
    ClosedSubspaces B T hT F ≃
      ClosedSubspaces B S hS ((OverShriek.relocalizePresheafFunctor g).obj F) :=
  (OverShriek.relocalizeSubfunctorEquiv g).subtypeEquiv fun Z =>
    (isClosedSubspace_relocalizeSubfunctor_iff B hT hS g Z).symm

/-- **Being of finite presentation, for the inclusion of a subspace, is unchanged by the
lower-shriek extension of Stacks 03I5 part (2).** -/
theorem isFinitePresentation_relocalizeSubfunctor_ι_iff (Z : Subfunctor X) :
    IsFinitePresentation B S hS (relocalizeSubfunctor B hT hS g Z).ι ↔
      IsFinitePresentation B T hT Z.ι := by
  refine Iff.trans ?_ (isFinitePresentation_relocalizeMap_iff B T S hT hS g Z.ι)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine isFinitePresentation_of_arrowIso B S hS _ _
      (relocalizeSubfunctorIso B hT hS g Z).inv (𝟙 _) ?_ h
    rw [Category.comp_id, Iso.inv_comp_eq]
    exact (relocalizeSubfunctorIso_hom_ι B hT hS g Z).symm
  · refine isFinitePresentation_of_arrowIso B S hS _ _
      (relocalizeSubfunctorIso B hT hS g Z).hom (𝟙 _) ?_ h
    rw [Category.comp_id]
    exact relocalizeSubfunctorIso_hom_ι B hT hS g Z

end Subspaces

/-! ### The view over the terminal scheme -/

section OverIntegers

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Quasi-separatedness of Stacks 03BS part (3) is unchanged by viewing an algebraic space over
the terminal scheme.** The implication from `S` to `Spec ℤ` is
`AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_viewOverIntegers`; both are the self-
comparison `AlgebraicGeometry.Space.viewOverIntegersSelfIso`. -/
theorem isAbsolutelyQuasiSeparated_viewOverIntegers_iff
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ hZ (viewOverIntegers B S hS hZ F) ↔
      IsAbsolutelyQuasiSeparated B S hS hZ F :=
  ⟨isQuasiSeparatedOver_of_iso B (⊤_ Scheme.{u}) hZ (viewOverIntegersSelfIso B S hS hZ F),
    isAbsolutelyQuasiSeparated_viewOverIntegers B S hS hZ F⟩

/-- **Being Noetherian is unchanged by viewing an algebraic space over the terminal scheme**,
Stacks 03EA: quasi-compactness, absolute quasi-separatedness and local Noetherianity of the
étale charts are each unchanged. -/
theorem isNoetherian_viewOverIntegers_iff (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    IsNoetherian B (⊤_ Scheme.{u}) hZ hZ (viewOverIntegers B S hS hZ F) ↔
      IsNoetherian B S hS hZ F :=
  and_congr
    (isQuasiCompactSpace_relocalize_iff B S hS (⊤_ Scheme.{u}) hZ
      (integersMap B S hS hZ) F)
    (and_congr (isAbsolutelyQuasiSeparated_viewOverIntegers_iff B S hS hZ F)
      (hasEtaleLocalProperty_relocalize_iff B S (⊤_ Scheme.{u}) hS hZ
        (integersMap B S hS hZ) _ F))

/-- **Being a thickening is unchanged by viewing an algebraic space over the terminal scheme**,
Stacks 05ZK part (1). -/
theorem isThickening_viewOverIntegers_iff (Y : AlgebraicSpaces B S hS) (Z : Subfunctor Y.1) :
    IsThickening B (⊤_ Scheme.{u}) hZ
        ⟨_, isAlgebraicSpace_relocalize' B hS hZ (integersMap B S hS hZ) Y.1 Y.2⟩
        (relocalizeSubfunctor B hS hZ (integersMap B S hS hZ) Z) ↔
      IsThickening B S hS Y Z :=
  isThickening_relocalizeSubfunctor_iff B hS hZ (integersMap B S hS hZ) Y Z

/-- **The open subspaces of the view of an algebraic space over the terminal scheme are its open
subspaces**, Stacks 02YU part (2). -/
noncomputable def openSubspacesViewOverIntegersEquiv (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    OpenSubspaces B S hS F ≃
      OpenSubspaces B (⊤_ Scheme.{u}) hZ (viewOverIntegers B S hS hZ F) :=
  openSubspacesRelocalizeEquiv B hS hZ (integersMap B S hS hZ) F

/-- **The closed subspaces of the view of an algebraic space over the terminal scheme are its
closed subspaces**, Stacks 0CYZ. -/
noncomputable def closedSubspacesViewOverIntegersEquiv (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    ClosedSubspaces B S hS F ≃
      ClosedSubspaces B (⊤_ Scheme.{u}) hZ (viewOverIntegers B S hS hZ F) :=
  closedSubspacesRelocalizeEquiv B hS hZ (integersMap B S hS hZ) F

end OverIntegers

end AlgebraicGeometry.Space

end
