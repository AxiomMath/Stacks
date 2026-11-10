module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackBaseChangeRepresentable
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackIsStackInGroupoids
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidPresentationBootstrap
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallySmallAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableMorphismAlgebraicStackUniverses
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverBased
public import StacksFrontier.CategoryTheory.Sites.Stack.Transport.StackTransport

/-!
# Descending algebraicity of `Coh_{X/Y}` along a surjective smooth cover of `Y`

The first step of the proof of Stacks 09DS: let `g : Y' ⟶ Y` be a surjective smooth morphism of
algebraic spaces over `S` (in the source an étale cover by a scheme), and `X' = X ×_Y Y'`. Then
`Coh_{X'/Y'} ⟶ Coh_{X/Y}` is representable by algebraic spaces, surjective and smooth (it is the
base change of `𝒮_{Y'} ⟶ 𝒮_Y` by Stacks 08LP), so if `Coh_{X'/Y'}` is algebraic, so is
`Coh_{X/Y}`, granted the diagonal of `Coh_{X/Y}` is representable (Stacks 08W6).

The morphisms of `Coh_{X/Y}` lie in the universe `u + 1`; the bootstrap is run on the versions
with hom-sets shrunk to `u`, both categories being locally small, and the conclusion carried back
by Stacks 03YQ.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.isAlgebraicStack_of_baseChange`: the reduction.

## References

* [Stacks Project, Tag 09DS](https://stacks.math.columbia.edu/tag/09DS)
* [Stacks Project, Tag 08LP](https://stacks.math.columbia.edu/tag/08LP)
* [Stacks Project, Tag 0301](https://stacks.math.columbia.edu/tag/0301)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Space.CoherentSituation

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : CoherentSituation B S hS) {Y' : AlgebraicSpaces B S hS}

/-- **The étale-descent reduction of Stacks 09DS.** Let `g : Y' ⟶ Y` be surjective and smooth. If
the diagonal of `Coh_{X/Y}` is representable by algebraic spaces and `Coh_{X'/Y'}`,
`X' = X ×_Y Y'`, is an algebraic stack, then `Coh_{X/Y}` is an algebraic stack. -/
theorem isAlgebraicStack_of_baseChange (g : Y' ⟶ D.Y)
    (hg : (Space.surjectiveMorphismProperty B S hS ⊓ Space.smoothMorphismProperty B S hS) g)
    (hdiag : Stack.HasRepresentableDiagonal B S hS D.coherentCFG)
    (h' : Stack.IsAlgebraicStack.{u, w} B S hS (D.baseChange g).coherentCFG.val) :
    Stack.IsAlgebraicStack.{u, w} B S hS D.coherentCFG.val := by
  let β : (D.baseChange g).coherentCFG ⟶ D.coherentCFG := (D.catBaseChangeSquare g).fst
  have hβ : Stack.IsRepresentableByAlgebraicSpaces B S hS β.hom :=
    D.isRepresentableByAlgebraicSpaces_baseChangeMap g
    (isRepresentableByAlgebraicSpaces_baseBasedMap g)
  have hβP : Stack.HasRelativeProperty.{u, u + 1, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS ⊓ Space.smoothMorphismProperty B S hS) β hβ :=
    hasRelativeProperty_baseChangeMap.{u, u} D g
    (Space.surjectiveMorphismProperty B S hS ⊓ Space.smoothMorphismProperty B S hS)
    (isRepresentableByAlgebraicSpaces_baseBasedMap g)
    ((hasRelativeProperty_baseCatMap_iff.{u, u} g _).2 hg)
  have : LocallySmall.{u} D.coherentCFG.val.obj :=
    Stack.locallySmall_of_hasRepresentableDiagonal B S hS D.coherentCFG hdiag
  have : LocallySmall.{u} (D.baseChange g).coherentCFG.val.obj :=
    Stack.locallySmall_of_isAlgebraicStack B S hS h'
  let 𝒲 := Stack.shrinkHomsCFG B S hS (D.baseChange g).coherentCFG
  let 𝒴 := Stack.shrinkHomsCFG B S hS D.coherentCFG
  let q : 𝒲 ⟶ 𝒴 := Stack.shrinkHomsHom B S hS β
  let e𝒴 := StacksRepresentableCFG.shrinkHomsEquivalenceOver.{u} D.coherentCFG.val.p
  have h𝒲 : Stack.IsAlgebraicStack.{u, w} B S hS 𝒲.val :=
    Stack.isAlgebraicStack_of_equivalenceOver B S hS
      (StacksRepresentableCFG.shrinkHomsEquivalenceOver.{u} (D.baseChange g).coherentCFG.val.p) h'
  have hstack : 𝒴.val.p.IsStack (BigFppfOver.topology B S hS) :=
    (StacksRepresentableCFG.EquivalenceOver.toBasedEquivalence e𝒴).isStack _ D.isStack
  have hdiag𝒴 : Stack.HasRepresentableDiagonal B S hS 𝒴 :=
    (Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒴).mpr
      ((Stack.isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS 𝒴).mpr
        (Stack.isRepresentableFromSchemes_of_equivalenceOver B S hS
          (StacksRepresentableCFG.EquivalenceOver.toBasedEquivalence e𝒴)
          ((Stack.isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS
            D.coherentCFG).mp
            ((Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS
              D.coherentCFG).mp hdiag))))
  have hsq : BasedFunctor.comp (Stack.shrinkHomsInverse B S hS (D.baseChange g).coherentCFG)
      β.hom ≅ BasedFunctor.comp q.hom (Stack.shrinkHomsInverse B S hS D.coherentCFG) :=
    BasedNatIso.mkNatIso (Functor.isoWhiskerLeft
      (ShrinkHoms.inverse (D.baseChange g).coherentCFG.val.obj ⋙ β.hom.toFunctor)
      (ShrinkHoms.equivalence D.coherentCFG.val.obj).unitIso)
      (fun a => by
        change D.coherentCFG.val.p.IsHomLift (𝟙 _) (𝟙 _)
        exact IsHomLift.id (BasedFunctor.w_obj β.hom _))
  have hq : Stack.IsRepresentableByAlgebraicSpaces B S hS q.hom :=
    (Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS q.hom β.hom
      (Stack.shrinkHomsInverse B S hS (D.baseChange g).coherentCFG)
      (Stack.shrinkHomsInverse B S hS D.coherentCFG) hsq).mp hβ
  have hqP : Stack.HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS ⊓ Space.smoothMorphismProperty B S hS) q hq :=
    (Stack.hasRelativeProperty_iff_of_equivalences B S hS _ q β
      (Stack.shrinkHomsInverse B S hS (D.baseChange g).coherentCFG)
      (Stack.shrinkHomsInverse B S hS D.coherentCFG) hsq hβ).mp hβP
  have h𝒴 : Stack.IsAlgebraicStack.{u, w} B S hS 𝒴.val :=
    Stack.isAlgebraicStack_of_smoothSurjectiveAlgebraicCover B S hS q h𝒲 hstack
      ((Stack.hasRepresentableDiagonal_iff B S hS 𝒴).1 hdiag𝒴) hq hqP
  exact Stack.isAlgebraicStack_of_equivalenceOver B S hS e𝒴.symm h𝒴

/-- **Algebraicity of `Coh_{X/Y}` is stable under base change of `Y`.** For any morphism
`g : Y' ⟶ Y` of algebraic spaces, `Coh_{X'/Y'} ⟶ Coh_{X/Y}` is representable by algebraic spaces
(Stacks 08LP and 0302), so Stacks 05UM carries algebraicity of `Coh_{X/Y}` to `Coh_{X'/Y'}`. -/
theorem isAlgebraicStack_baseChange (g : Y' ⟶ D.Y)
    (h : Stack.IsAlgebraicStack.{u, w} B S hS D.coherentCFG.val) :
    Stack.IsAlgebraicStack.{u, w} B S hS (D.baseChange g).coherentCFG.val :=
  Stack.isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces_homUniverse B S hS
    (D.catBaseChangeSquare g).fst
    (D.isRepresentableByAlgebraicSpaces_baseChangeMap g
      (isRepresentableByAlgebraicSpaces_baseBasedMap g)) h

end AlgebraicGeometry.Space.CoherentSituation

end
