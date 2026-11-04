module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackAlgebraicUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.PicardForgetTrivializationRepresentable
public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctorAlgebraicSpaceReduction
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackAlgebraic
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackIsAlgebraic
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackSectionSetoid
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackSmallModel
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityTransport
public import StacksFrontier.AlgebraicGeometry.Stacks.StackInSetoidsRepresentableBySpace
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverBased

/-!
# The Picard functor is an algebraic space

Let `S` be a scheme and `f : X ⟶ B` a morphism of algebraic spaces over `S` which is flat, of
finite presentation and proper, such that `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an isomorphism for every
scheme `T` over `B`. Then the relative Picard functor `Pic_{X/B}` is an algebraic space over `B`.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpaceOver_picardFunctor`: the relative Picard functor of a
  flat, finitely presented, proper morphism `f` with `𝒪_T ≅ f_{T, *}𝒪_{X_T}` for all `T` is an
  algebraic space.

## References

* [Stacks Project, Tag 0D2C](https://stacks.math.columbia.edu/tag/0D2C)
* [Stacks Project, Tag 0D04](https://stacks.math.columbia.edu/tag/0D04)
* [Stacks Project, Tag 0D2A](https://stacks.math.columbia.edu/tag/0D2A)
* [Stacks Project, Tag 0D2B](https://stacks.math.columbia.edu/tag/0D2B)
* [Stacks Project, Tag 04SZ](https://stacks.math.columbia.edu/tag/04SZ)
* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **With a section, the rigidified Picard stack is an algebraic space.**  Let `f : X ⟶ B` be
flat, of finite presentation and proper with a section `σ`, and assume that
`𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an isomorphism for every scheme `T` over `B`.  Then
`Picardstack_{X/B, σ}` is representable by an algebraic space. -/
private theorem isRepresentableByAlgebraicSpace_sectionedPicardCFG_aux
    (D : CoherentSituation B S hS) (hflat : IsFlat B S hS D.f.hom)
    (hproper : IsProper B S hS D.f.hom) (σ : D.toPicardSituation.base ⟶ D.toPicardSituation.X)
    (hσ : σ ≫ D.toPicardSituation.f = 𝟙 _) (hstr : D.toPicardSituation.StructureSheafMapIso) :
    Stack.IsRepresentableByAlgebraicSpace B S hS
      (sectionedPicardCFG (modulePushforwardCoherence B S hS)
        (sectionTransportCoherence (modulePushforwardCoherence B S hS) σ hσ)) := by
  let P := sectionedPicardCFG (modulePushforwardCoherence B S hS)
    (sectionTransportCoherence (modulePushforwardCoherence B S hS) σ hσ)
  obtain ⟨-, hj, -, -⟩ := forgetTrivialization_representable_surjective_smooth (s :=
    D.toPicardSituation) σ hσ
  have hP : Stack.IsAlgebraicStack.{u, u} B S hS P.val :=
    Stack.isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces_homUniverse B S hS _ hj
      (isAlgebraicStack_picardCFG.{u, u} D hflat hproper)
  let := Stack.locallySmall_of_isAlgebraicStack B S hS hP
  let Ps : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
    CatFiberedInGroupoids.mk P.val.shrinkHoms
      (BasedCategory.isFiberedInGroupoids_shrinkHoms P.val P.isFiberedInGroupoids)
  have hPs : Stack.IsAlgebraicStack.{u, u} B S hS Ps.val :=
    Stack.isAlgebraicStack_shrinkHoms B S hS hP
  have hset := (sectionedPicardCFG_isFiberedInSetoids_and_isoClassEquiv σ hσ hstr).1
  have hPset : P.val.p.IsStackInSetoids (BigFppfOver.topology B S hS) :=
    ⟨hP.2.1.1, Functor.IsFiberedInSetoids.fiber_isGroupoid _, hset.fiber_isThin⟩
  have hPsset : Ps.val.p.IsStackInSetoids (BigFppfOver.topology B S hS) :=
    (BasedCategory.isStackInSetoids_iff_of_equivalence
      (BasedCategory.shrinkHomsEquivalenceOver P.val).toBasedEquivalence _).1 hPset
  exact Stack.isRepresentableByAlgebraicSpace_of_equivalenceOver
    (BasedCategory.shrinkHomsEquivalenceOver P.val)
    (Stack.isRepresentableByAlgebraicSpace_of_isStackInSetoids B S hS Ps hPs hPsset)

/-- **The Picard functor is an algebraic space.**  Let `S` be a scheme and
`f : X ⟶ Y` a morphism of algebraic spaces over `S` such that

1. `f` is flat, of finite presentation and proper, and
2. `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an isomorphism for all schemes `T` over `Y`.

Then the relative Picard functor `Pic_{X/Y}` is an algebraic space over `Y`. -/
@[stacks 0D2C "the full statement: f flat (hflat), of finite presentation (hfp) and proper \
(hproper), and O_T -> f_{T,*}O_{X_T} an isomorphism for every scheme T over the base (hstr); \
Pic_{X/B} is an algebraic space over B"]
theorem isAlgebraicSpaceOver_picardFunctor {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hflat : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (hproper : IsProper B S hS f.hom)
    (hstr : (PicardSituation.mk X Y f).StructureSheafMapIso) :
    IsAlgebraicSpaceOver (PicardSituation.mk X Y f).picardFunctor := by
  let D : CoherentSituation B S hS := ⟨X, Y, f, hfp⟩
  have hpb := AlgebraicSpaces.isPullback_fiberProduct B S hS D.f D.f
  have := isFlat_isStableUnderBaseChange B S hS
  have hflat' : IsFlat B S hS (D.baseChange D.f).f.hom :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (k : F ⟶ G) => IsFlat B S hS k.hom) hpb hflat
  have hproper' : IsProper B S hS (D.baseChange D.f).f.hom :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (k : F ⟶ G) => IsProper B S hS k.hom) hpb hproper
  exact D.isAlgebraicSpaceOver_picardFunctor_of_isRepresentableByAlgebraicSpace hflat hstr
    (isRepresentableByAlgebraicSpace_sectionedPicardCFG_aux (D.baseChange D.f) hflat' hproper'
      D.diagonalSection D.diagonalSection_comp (D.structureSheafMapIso_baseChange D.f hstr))

end AlgebraicGeometry.Space

end
