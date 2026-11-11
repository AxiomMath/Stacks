module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSliceGlueing.FppfMayerVietoris
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.OverField.SmoothCharacteristicZero
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.TrivialActionSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FlatImageSystem
public import StacksFrontier.Examples.Stacks.NonAlgebraicHomStack.Main

/-!
# A separated target with a non-algebraic Hom-stack

Remark 0AFD of the source observes that Proposition 0AFC contradicts the assertion of the Erratum
to [AokiHomStacks] that `Mor_S(𝒴, 𝒵)` is algebraic as soon as `𝒵` is separated, "as `[S/A]` is
separated". This file proves the form of that assertion for the Hom-stack
`AlgebraicGeometry.Stack.homStack` of Stacks 0AFC: in the situation of Section 0AF8 the
classifying stack `[S/A]` is separated over `S`, while `Mor_S(X, [S/A])` is not algebraic, so the
criterion fails. Stacks 0AFD itself is registered in
`StacksFrontier.Examples.Stacks.HomStackSeparatedTargetCriterionUnconditional`, for absolute
separatedness and an arbitrary assignment of Hom-stacks with a non-effective formal object.

## Main results

* `Stacks.Examples.NonAlgebraicHomStack.Situation.isSeparatedOver_classifyingStackModel`: `[S/A]`
  is separated over `S` (Stacks 0DTY part (6) at the groupoid of the trivial action, `A ⟶ S`
  being proper, flat and of finite presentation).
* `Situation.not_forall_isAlgebraicStack_homStack_of_isSeparatedOver`: the separated-target
  criterion fails for `AlgebraicGeometry.Stack.homStack`, with separatedness over `S`.

## Implementation notes

The Hom-stacks are those `AlgebraicGeometry.Stack.homStack` of a scheme `Y` over `S` (an object
of the big fppf site of `S`) and an algebraic stack `𝒵` over `S`; restricting the source `𝒴` of
the criterion to schemes makes its refutation only stronger. Separatedness is over the base `S`,
`AlgebraicGeometry.Stack.IsSeparatedOver`; `S = Spec k⟦t⟧` is affine, hence separated.

The bibliographic content of the remark (that Stacks 0AFC contradicts Theorem 1.1 of
[AokiHomStacks], and that the separated-target criterion is the Erratum's) is not formalized.

## References

* [Stacks Project, Tag 0AFD](https://stacks.math.columbia.edu/tag/0AFD)
* [Stacks Project, Tag 0AFC](https://stacks.math.columbia.edu/tag/0AFC)
* [Stacks Project, Tag 0DTY](https://stacks.math.columbia.edu/tag/0DTY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Stack MonoidalCategory
open scoped CategoryTheory.MonObj

universe w u

namespace Stacks.Examples.NonAlgebraicHomStack.Situation

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) (hS : B.Contains (base k))

/-- The group algebraic space `A` over `S` is represented by the scheme `A`. -/
def groupSpaceIsoYoneda (sit : Situation k) :
    yoneda.obj (groupObj B (base k) hS sit.abelianScheme (sit.contains_abelianScheme hS)) ≅
      (groupSpace B (base k) hS sit.abelianScheme (sit.contains_abelianScheme hS)).obj.X.left :=
  Space.GroupAlgebraicSpace.ofGroupSchemeInSiteIsoYoneda _ _

/-- The structure morphism of the group algebraic space `A` over `S` is the Yoneda image of the
structure morphism of `A`, up to the identification of `A` with its functor of points. -/
theorem groupSpace_hom_eq (sit : Situation k) :
    (groupSpace B (base k) hS sit.abelianScheme (sit.contains_abelianScheme hS)).obj.X.hom =
      (groupSpaceIsoYoneda B hS sit).inv ≫
        yoneda.map (Over.mkIdTerminal.from
          (groupObj B (base k) hS sit.abelianScheme (sit.contains_abelianScheme hS))) :=
  (Space.isTerminal_yoneda_obj_base B (base k) hS).hom_ext _ _

/-- The structure morphism of the scheme `A` over `S`, as a morphism of the big fppf site. -/
theorem toScheme_map_groupObj (sit : Situation k) :
    (BigFppfOver.toScheme B (base k) hS).map (Over.mkIdTerminal.from
      (groupObj B (base k) hS sit.abelianScheme (sit.contains_abelianScheme hS))) =
      sit.abelianScheme.hom :=
  Space.toScheme_map_mkIdTerminal_from_siteObject B (base k) hS (sit.contains_abelianScheme hS) _

/-- The group algebraic space `A ⟶ S` is proper, `A` being an abelian scheme. -/
theorem isProper_groupSpace_hom (sit : Situation k) :
    Space.IsProper B (base k) hS
      (groupSpace B (base k) hS sit.abelianScheme (sit.contains_abelianScheme hS)).obj.X.hom := by
  have hab : IsAbelianScheme sit.abelianScheme := inferInstance
  rw [groupSpace_hom_eq B hS sit]
  refine Space.isProper_comp B (base k) hS
    (groupSpace B (base k) hS sit.abelianScheme (sit.contains_abelianScheme hS)).property
    (isAlgebraicSpace_yoneda B (base k) hS _) (isAlgebraicSpace_yoneda B (base k) hS _) _ _
    (Space.isProper_of_isIso B (base k) hS _) (Space.isProper_yoneda_map B (base k) hS _ ?_)
  rw [toScheme_map_groupObj B hS sit]
  exact hab.toIsProper

/-- The group algebraic space `A ⟶ S` is flat, `A` being an abelian scheme. -/
theorem isFlat_groupSpace_hom (sit : Situation k) :
    Space.IsFlat B (base k) hS
      (groupSpace B (base k) hS sit.abelianScheme (sit.contains_abelianScheme hS)).obj.X.hom := by
  have hab : IsAbelianScheme sit.abelianScheme := inferInstance
  rw [groupSpace_hom_eq B hS sit]
  refine Space.isFlat_comp B (base k) hS
    (groupSpace B (base k) hS sit.abelianScheme (sit.contains_abelianScheme hS)).property
    (isAlgebraicSpace_yoneda B (base k) hS _) (isAlgebraicSpace_yoneda B (base k) hS _) _ _
    (Space.isFlat_of_isIso _ (isAlgebraicSpace_yoneda B (base k) hS _))
    (Space.isFlat_yoneda_map B (base k) hS _ ?_)
  rw [toScheme_map_groupObj B hS sit]
  exact hab.toFlat

/-- The group algebraic space `A ⟶ S` is locally of finite presentation, `A` being an abelian
scheme. -/
theorem isLocallyOfFinitePresentation_groupSpace_hom (sit : Situation k) :
    Space.IsLocallyOfFinitePresentation B (base k) hS
      (groupSpace B (base k) hS sit.abelianScheme (sit.contains_abelianScheme hS)).obj.X.hom := by
  have hab : IsAbelianScheme sit.abelianScheme := inferInstance
  refine Space.isLocallyOfFinitePresentation_of_arrowIso B (base k) hS
    (yoneda.map (Over.mkIdTerminal.from
      (groupObj B (base k) hS sit.abelianScheme (sit.contains_abelianScheme hS))))
    (groupSpace B (base k) hS sit.abelianScheme (sit.contains_abelianScheme hS)).obj.X.hom
    (groupSpaceIsoYoneda B hS sit).hom (𝟙 _)
    ((Space.isTerminal_yoneda_obj_base B (base k) hS).hom_ext _ _)
    (Space.isLocallyOfFinitePresentation_yoneda_map B (base k) hS _ ?_)
  rw [toScheme_map_groupObj B hS sit]
  exact hab.toLocallyOfFinitePresentation

/-- The quotient by the trivial action of a group algebraic space over an algebraic space `T`
equal to the base is separated over the base, when the group is proper, flat and locally of
finite presentation: `AlgebraicGeometry.Stack.isSeparatedOver_quotientStack_trivialAction`, read
along the equality `T = S`, for any of the (equal) actions of `G` on the monoidal unit. -/
theorem isSeparatedOver_quotientStackOfAction_of_eq_terminalSpace
    (T : AlgebraicSpaces B (base k) hS) (hT : T = Space.terminalSpace B (base k) hS)
    (G : Over T.obj) [GrpObj G] [inst : ModObj G (𝟙_ (Over T.obj))]
    (hG : IsAlgebraicSpace B (base k) hS G.left) (𝒵 : AlgebraicStacks.{u, u} B (base k) hS)
    (hequiv : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (quotientStackOfAction T G (𝟙_ (Over T.obj)) hG T.property).p 𝒵.val.val.p))
    (hproper : Space.IsProper B (base k) hS G.hom) (hflat : Space.IsFlat B (base k) hS G.hom)
    (hlfp : Space.IsLocallyOfFinitePresentation B (base k) hS G.hom) :
    IsSeparatedOver.{u, u} B (base k) hS 𝒵 := by
  subst hT
  obtain rfl : inst = Space.modObjTensorUnit G := by
    obtain ⟨smul, _, _⟩ := inst
    congr
    exact CartesianMonoidalCategory.toUnit_unique _ _
  exact isSeparatedOver_quotientStack_trivialAction.{u, u} G hG
    (Space.groupoidOfAction _ G _ hG (Space.terminalSpace B (base k) hS).property) 𝒵 hequiv
    hproper hflat hlfp

/-- **`[S/A]` is separated over `S`.** By Stacks 0DTY part (6) at the groupoid of the trivial
action of `A` on `S`, whose source and target are the structure morphism of the abelian scheme
`A ⟶ S`, proper, flat and of finite presentation. -/
theorem isSeparatedOver_classifyingStackModel (sit : Situation k) :
    IsSeparatedOver.{u, u} B (base k) hS
      (AlgebraicStacks.smallModel B (base k) hS
        (classifyingStackOfGroupScheme B (base k) hS sit.abelianScheme
          (sit.contains_abelianScheme hS))
        (isAlgebraicStack_classifyingStackOfGroupScheme B (base k) hS sit.abelianScheme
          (sit.contains_abelianScheme hS) sit.smooth_abelianScheme)) :=
  isSeparatedOver_quotientStackOfAction_of_eq_terminalSpace B hS
    (classifyingBaseSpace B (base k) hS) rfl
    (groupSpace B (base k) hS sit.abelianScheme (sit.contains_abelianScheme hS)).obj.X
    (groupSpace B (base k) hS sit.abelianScheme (sit.contains_abelianScheme hS)).property _
    ⟨(sit.classifyingStackModelEquivalenceOver B hS (sit.contains_abelianScheme hS)).symm⟩
    (isProper_groupSpace_hom B hS sit) (isFlat_groupSpace_hom B hS sit)
    (isLocallyOfFinitePresentation_groupSpace_hom B hS sit)

/-- **The separated-target criterion fails for `homStack`** (the argument of Remark 0AFD, for
separatedness over `S`). The criterion that a Hom-stack is algebraic as soon as its target is
separated is false: in the situation of Section 0AF8 it is *not* the case that `Mor_S(Y, 𝒵)` is an
algebraic stack for every scheme `Y` over `S` and every algebraic stack `𝒵` separated over `S`.
Indeed `[S/A]` is separated over `S`
(`Stacks.Examples.NonAlgebraicHomStack.Situation.isSeparatedOver_classifyingStackModel`) and
`Mor_S(X, [S/A])` is not algebraic (Stacks 0AFC). -/
theorem not_forall_isAlgebraicStack_homStack_of_isSeparatedOver (sit : Situation k) :
    ¬ ∀ (Y : BigFppfOver B (base k) hS) (𝒵 : AlgebraicStacks.{u, u} B (base k) hS),
        IsSeparatedOver.{u, u} B (base k) hS 𝒵 →
          IsAlgebraicStack.{u, w} B (base k) hS (homStack Y 𝒵.val.val) :=
  fun h => sit.not_isAlgebraicStack_homStack B hS
    (h _ _ (isSeparatedOver_classifyingStackModel B hS sit))

end Stacks.Examples.NonAlgebraicHomStack.Situation

end
