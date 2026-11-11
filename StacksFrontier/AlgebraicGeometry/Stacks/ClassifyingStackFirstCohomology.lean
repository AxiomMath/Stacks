module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.AbelianGroupDataOfPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.BigFppfAbelianSheaves
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ClassifyingStackEquivalences
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackSmallModel
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothActionQuotientStackAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.SmoothProductProjection
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianSchemeFirstCohomologyGenericPoint

/-!
# The classifying stack of a smooth commutative group scheme and first cohomology

Let `S` be a scheme of a big fppf site and `A ⟶ S` a smooth commutative group scheme of the site,
with abelian sheaf of points `𝒜` (`AlgebraicGeometry.pointsSheaf`). The classifying stack
`[S/A]` — the quotient stack of the trivial action of the group algebraic space `S ×_S A` on
`S` — is an algebraic stack by Stacks 04TK, so it has a small model
`AlgebraicGeometry.Stack.classifyingStackModel` with the universes of the 2-category of
algebraic stacks, equivalent to `[S/A]` over the site.

This file proves that the class in `H¹(U, 𝒜)` of the torsor attached to an object over `U` is a
classifying invariant of that small model, in the sense of
`Deformation.Artin.IsClassifyingInvariant`: it is natural, every class is attained, and two
objects whose classes agree along an isomorphism of their bases are related by a morphism over
that isomorphism. The torsor attached to an object is read along the chain of equivalences of
Stacks 0CQJ, `[S/A] ≌ [[S/A]] ≌ A-Torsors ≌ 𝒜/S-Torsors`, and the class is
`AlgebraicGeometry.Space.SheafTorsors.h1Class`.

## Main definitions

* `AlgebraicGeometry.Stack.classifyingStackOfGroupScheme`: the classifying stack `[S/A]`.
* `AlgebraicGeometry.Stack.classifyingStackModel`: its small model.
* `AlgebraicGeometry.Stack.classifyingStackModelEquivalenceOver`: the equivalence over the site
  of the small model with `[S/A]`.
* `AlgebraicGeometry.Stack.classifyingStackClass`: the class in `H¹` of an object.

## Main results

* `AlgebraicGeometry.Stack.isClassifyingInvariant_classifyingStackClass`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory MonObj

universe u

namespace AlgebraicGeometry.Stack

open Space Stacks.Cohomology.Torsors

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (A : Over S) [GrpObj A] [IsCommMonObj A] (hA : B.Contains A.left) (hsm : Smooth A.hom)

/-- The base `S`, as an algebraic space over itself. -/
abbrev classifyingBaseSpace : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj (Over.mk (𝟙 (B.obj hS))), isAlgebraicSpace_yoneda B S hS _⟩

/-- `A`, as an object of the big fppf site of `S`. -/
abbrev groupObj : BigFppfOver B S hS := siteObject B S hS hA A.hom

/-- The group structure of `A`, on the object of the site it defines. -/
abbrev groupObjGrp : GrpObj ((Space.toSchemeOver B S hS).obj (groupObj B S hS A hA)) :=
  inferInstanceAs (GrpObj A)

/-- The group algebraic space `S ×_S A` over the base. -/
abbrev groupSpace : GroupAlgebraicSpace B S hS (classifyingBaseSpace B S hS).obj
    (classifyingBaseSpace B S hS).property :=
  GroupAlgebraicSpace.ofGroupSchemeInSite B S hS _ _ (groupObj B S hS A hA)
    (groupObjGrp B S hS A hA)

/-- **The classifying stack `[S/A]`**: the quotient stack of the trivial action of `S ×_S A`
on `S`. -/
abbrev classifyingStackOfGroupScheme : BasedCategory (BigFppfOver B S hS) :=
  Stack.quotientStackOfAction (classifyingBaseSpace B S hS) (groupSpace B S hS A hA).obj.X
    (𝟙_ (Over (classifyingBaseSpace B S hS).obj)) (groupSpace B S hS A hA).property
    (classifyingBaseSpace B S hS).property

omit [IsCommMonObj A] in
include hsm in
/-- **The classifying stack of a smooth group scheme is algebraic** (Stacks 04TK). -/
theorem isAlgebraicStack_classifyingStackOfGroupScheme :
    IsAlgebraicStack.{u, u} B S hS (classifyingStackOfGroupScheme B S hS A hA) :=
  isAlgebraicStack_quotientStackOfAction_of_isSmooth (classifyingBaseSpace B S hS) _ _ _ _
    (isSmooth_prod_fst_pointsOnSite B S hS _ (classifyingBaseSpace B S hS).property _ _
      (isSmooth_yoneda_map_mkIdTerminal_from B S hS _ (by
        rw [toScheme_map_mkIdTerminal_from_siteObject]
        exact hsm)))

/-- **The small model of `[S/A]`**, with the universes of the 2-category of algebraic stacks. -/
abbrev classifyingStackModel : BasedCategory.{u, u + 1} (BigFppfOver B S hS) :=
  (AlgebraicStacks.smallModel B S hS (classifyingStackOfGroupScheme B S hS A hA)
    (isAlgebraicStack_classifyingStackOfGroupScheme B S hS A hA hsm)).val.val

/-- The small model of `[S/A]` is equivalent to `[S/A]` over the site. -/
def classifyingStackModelEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver (classifyingStackModel B S hS A hA hsm).p
      (classifyingStackOfGroupScheme B S hS A hA).p :=
  (AlgebraicStacks.smallModelEquivalenceOver B S hS (classifyingStackOfGroupScheme B S hS A hA)
    (isAlgebraicStack_classifyingStackOfGroupScheme B S hS A hA hsm)).symm

/-- The small model of `[S/A]` is equivalent over the site to `𝒢/ℬ-Torsors`, by Stacks 0CQJ. -/
def classifyingStackModelSheafTorsors :
    StacksRepresentableCFG.EquivalenceOver (classifyingStackModel B S hS A hA hsm).p
      (SheafTorsors.projection (groupSpace B S hS A hA).obj) :=
  (classifyingStackModelEquivalenceOver B S hS A hA hsm).trans
    ((classifyingQuotientStackEquivalence (classifyingBaseSpace B S hS).property _).trans
      ((classifyingStackTorsorsEquivalenceOver (classifyingBaseSpace B S hS).property _).trans
        (torsorsSheafTorsorsEquivalenceOver (classifyingBaseSpace B S hS).property _)))

/-- The identification of the points of `S ×_S A` with the sections of the sheaf of points of
`A`. -/
def groupPointsMulEquiv (T : BigFppfOver B S hS) :
    (pointsOnSite B S hS (groupObj B S hS A hA) (groupObjGrp B S hS A hA)).obj (op T) ≃*
      Multiplicative ((pointsSheaf B S hS A hA).obj.obj (op T)) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The datum identifying the acting groups of `[S/A]` with the restrictions of `𝒜`. -/
def classifyingStackGroupData :=
  abelianGroupDataOfPoints B S hS (classifyingBaseSpace B S hS).obj
    (classifyingBaseSpace B S hS).property
    (pointsOnSite B S hS (groupObj B S hS A hA) (groupObjGrp B S hS A hA))
    (pointsOnSiteRepresentableBy B S hS (groupObj B S hS A hA) (groupObjGrp B S hS A hA))
    (pointsSheaf B S hS A hA) (groupPointsMulEquiv B S hS A hA) (fun _ _ => rfl)

variable [HasSheafify (BigFppfOver.topology B S hS) AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf (BigFppfOver.topology B S hS) AddCommGrpCat.{u})]

attribute [local instance] BigFppfOver.hasSheafify_over_abelian BigFppfOver.hasExt_over_abelian
  BigFppfOver.enoughInjectives_abelian BigFppfOver.wEqualsLocallyBijective_abelian

/-- **The class in `H¹(U, 𝒜)` of an object of the small model of `[S/A]` over `U`**: the class
of the `𝒜|_U`-torsor attached to it through Stacks 0CQJ. -/
def classifyingStackClass (z : (classifyingStackModel B S hS A hA hsm).obj) :
    (Sheaf.cohomologyPresheaf (pointsSheaf B S hS A hA) 1 ⋙ forget AddCommGrpCat.{u}).obj
      (op ((classifyingStackModel B S hS A hA hsm).p.obj z)) :=
  (Sheaf.cohomologyPresheaf (pointsSheaf B S hS A hA) 1 ⋙ forget AddCommGrpCat.{u}).map
    (eqToHom (Functor.congr_obj (classifyingStackModelSheafTorsors B S hS A hA hsm).hom.w
      z).symm).op
    (((classifyingStackModelSheafTorsors B S hS A hA hsm).hom.functor.obj z).h1Class
      (classifyingStackGroupData B S hS A hA))

/-- **The class in `H¹` classifies the objects of the small model of `[S/A]`.** -/
theorem isClassifyingInvariant_classifyingStackClass :
    Deformation.Artin.IsClassifyingInvariant
      (Sheaf.cohomologyPresheaf (pointsSheaf B S hS A hA) 1 ⋙ forget AddCommGrpCat.{u})
      (classifyingStackClass B S hS A hA hsm) := by
  let e := classifyingStackModelSheafTorsors B S hS A hA hsm
  have : e.hom.functor.IsEquivalence := e.toEquivalence.isEquivalence_functor
  refine Deformation.Artin.IsClassifyingInvariant.comp e.hom.functor e.hom.w
    (SheafTorsors.isClassifyingInvariant_h1Class (classifyingStackGroupData B S hS A hA)
      (fun U => yoneda.map (Over.mkIdTerminal.from U)) fun U b b' => ?_)
  apply yonedaEquiv.injective
  exact Over.mkIdTerminal.hom_ext _ _

end AlgebraicGeometry.Stack

end
