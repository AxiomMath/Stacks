module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianImmersionQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismDeligneMumford
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemePointBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsoluteSource
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationConstructionAQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative

/-!
# Immersions into Noetherian algebraic stacks

Let `j : 𝒳 ⟶ 𝒴` be an immersion of algebraic stacks over `S`. If `𝒴` is locally Noetherian, then
`j` is quasi-compact; if `𝒴` is Noetherian, then so is `𝒳`.

Quasi-compactness of `j` is taken in the sense of Stacks 03YK: every algebraic space representing
the base change of `j` along a scheme-valued point of `𝒴` has quasi-compact structural morphism.
By Stacks 050T this agrees with the absolute notion
`AlgebraicGeometry.Stack.IsQuasiCompactMorphism` of Stacks 050U. Noetherianity of an algebraic
stack is `AlgebraicGeometry.Stack.IsNoetherianStack` (Stacks 0510): quasi-compact, quasi-separated
and locally Noetherian.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.hasRelativeProperty_quasiCompact_of_isImmersion`: an
  immersion into a locally Noetherian algebraic stack is quasi-compact.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isNoetherianStack_of_isImmersion`: the source of an
  immersion into a Noetherian algebraic stack is Noetherian.

## Implementation notes

`AlgebraicGeometry.Stack.quasiCompactMorphismProperty_isLocalAtTarget_fppf` is a theorem, not a
global instance; it is a local instance in this file, so that quasi-compactness satisfies both
instance hypotheses of `AlgebraicGeometry.Stack.HasRelativeProperty`.

## References

* [Stacks Project, Tag 01OX](https://stacks.math.columbia.edu/tag/01OX)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 041L](https://stacks.math.columbia.edu/tag/041L)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 04AJ](https://stacks.math.columbia.edu/tag/04AJ)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04TA](https://stacks.math.columbia.edu/tag/04TA)
* [Stacks Project, Tag 04XD](https://stacks.math.columbia.edu/tag/04XD)
* [Stacks Project, Tag 04XI](https://stacks.math.columbia.edu/tag/04XI)
* [Stacks Project, Tag 04YG](https://stacks.math.columbia.edu/tag/04YG)
* [Stacks Project, Tag 04ZU](https://stacks.math.columbia.edu/tag/04ZU)
* [Stacks Project, Tag 0504](https://stacks.math.columbia.edu/tag/0504)
* [Stacks Project, Tag 050L](https://stacks.math.columbia.edu/tag/050L)
* [Stacks Project, Tag 050T](https://stacks.math.columbia.edu/tag/050T)
* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 0510](https://stacks.math.columbia.edu/tag/0510)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06MY](https://stacks.math.columbia.edu/tag/06MY)
* [Stacks Project, Tag 0CPM](https://stacks.math.columbia.edu/tag/0CPM)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Quasi-compactness of morphisms of algebraic spaces over `S` is local at the target for the
fppf precoverage. -/
theorem quasiCompactMorphismProperty_isLocalAtTarget_fppf :
    (Space.quasiCompactProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
  .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)

attribute [local instance] quasiCompactMorphismProperty_isLocalAtTarget_fppf

namespace AlgebraicStacks

/-- Let `j : 𝒳 ⟶ 𝒴` be an immersion of algebraic stacks, where `𝒴` has a smooth surjective
scheme atlas with locally Noetherian source. Then `j` is quasi-compact: it has the relative
property of Stacks 03YK at quasi-compactness of morphisms of algebraic spaces. -/
@[stacks 0CPM "part (1): the 1-morphism is quasi-compact, in the sense of Stacks 03YK"]
theorem hasRelativeProperty_quasiCompact_of_isImmersion
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}
    (j : 𝒳 ⟶ 𝒴) (hj : IsImmersion B S hS j)
    (hY : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴) :
    HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.quasiCompactProperty B S hS) j.hom hj.1 := by
  classical
  obtain ⟨V, g, hgsurj, hgsm, hVN⟩ := hY
  have hgrep : IsRepresentableByAlgebraicSpaces B S hS g.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒴.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS V) g.hom
  let a : (schemeSlice B S hS V).val ⥤ᵇ (schemeFibredCategory B S hS V).val :=
    { toFunctor := Over.iteratedSliceBackward V
      w := Over.iteratedSliceBackward_forget V }
  have ha : Functor.IsEquivalence a.toFunctor :=
    (Over.iteratedSliceEquiv V).symm.isEquivalence_functor
  have hb : Functor.IsEquivalence (BasedFunctor.id 𝒴.val.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒴.val.val.obj))
  let y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.val.obj :=
    a.toFunctor ⋙ g.hom.hom.toFunctor
  have hy : y ⋙ 𝒴.val.val.p = Over.map V.hom := by
    show (a.toFunctor ⋙ g.hom.hom.toFunctor) ⋙ 𝒴.val.val.p = Over.map V.hom
    rw [Functor.assoc, g.hom.hom.w]
    exact a.w
  have hg'rep : IsRepresentableByAlgebraicSpaces B S hS
      (schemeSliceMap B S hS V y hy).hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒴.property
      (isRepresentableByAlgebraicSpace_schemeSlice B S hS V) (schemeSliceMap B S hS V y hy)
  have transfer := fun P : MorphismProperty (AlgebraicSpaces B S hS) =>
    relativeProperty_of_equivalences B S hS P (schemeSliceMap B S hS V y hy).hom g.hom.hom
      a (BasedFunctor.id 𝒴.val.val) (Iso.refl _)
  have hg'surj := transfer (Space.surjectiveMorphismProperty B S hS)
    ((pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS g hgrep).mp hgsurj)
  let : MorphismProperty.IsStableUnderBaseChange
      (spaceProperty B S hS (fun _ _ k => Space.IsSmooth B S hS k)) :=
    Space.isSmooth_isStableUnderBaseChange B S hS
  have hg'sm := transfer (spaceProperty B S hS (fun _ _ k => Space.IsSmooth B S hS k))
    ((hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS
      (fun _ _ k => Space.IsSmooth B S hS k)
      (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS)
      (isAlgebraicStack_schemeFibredCategory.{u, w} B S hS V) 𝒴.property g.hom hgrep).mp hgsm)
  obtain ⟨T, hT, ⟨eT⟩⟩ := hj.1 V y hy
  have : MorphismProperty.RespectsIso (Space.immersionProperty B S hS) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine hasRelativeProperty_of_prop_representingMap_of_fppf B S hS
    (Space.quasiCompactProperty B S hS) 𝒳.val 𝒴.val (schemeSlice B S hS V)
    j.hom (schemeSliceMap B S hS V y hy) hj.1 hg'rep (fun U z hz G hG hr =>
      ⟨hg'surj U z hz G hG hr, Space.isFlat_of_isSmooth B S hS _ (hg'sm U z hz G hG hr),
        Space.isLocallyOfFinitePresentation_of_isSmooth B S hS (hg'sm U z hz G hG hr)⟩)
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (schemeSliceMap B S hS V y hy) j.hom)
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      (schemeSliceMap B S hS V y hy) j.hom)
    ((OverShriek.relocalizePresheafFunctor V.hom).obj T) (yoneda.obj V)
    (isAlgebraicSpace_viewOver B V.left.1 S V.left.2 hS V.hom T hT)
    (isAlgebraicSpace_yoneda B S hS V)
    (relocalizeFibreEquivalence B S hS V j.hom y T eT)
    (schemeSliceEquivalenceOver B S hS V) ?_
  rw [representingMap_relocalizeFibre B S hS V j.hom y T eT hy]
  exact Space.isQuasiCompact_of_isImmersion_yoneda B S hS
    ((prop_algebraicSpaceMap_iff B S hS (Space.immersionProperty B S hS) V T hT).mp
      (hj.2 V y hy T hT ⟨eT⟩)) hVN

/-- Let `j : 𝒳 ⟶ 𝒴` be an immersion of algebraic stacks. If `𝒴` is Noetherian, then `𝒳` is
Noetherian. -/
@[stacks 0CPM "part (2): the source is Noetherian"]
theorem isNoetherianStack_of_isImmersion
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}
    (j : 𝒳 ⟶ 𝒴) (hj : IsImmersion B S hS j)
    (hY : IsNoetherianStack.{u, w, w'} B S hS 𝒴) :
    IsNoetherianStack.{u, w, w'} B S hS 𝒳 := by
  obtain ⟨hYqc, hYqs, hYN⟩ := hY
  refine ⟨?_, ?_, isLocallyNoetherian_of_isImmersion B S hS j hj hYN⟩
  · have hjqc : IsQuasiCompactMorphism.{u, w} B S hS j :=
      (isQuasiCompact_iff_baseChange_quasiCompact B S hS j hj.1).mp
        (hasRelativeProperty_quasiCompact_of_isImmersion B S hS j hj hYN)
    refine isQuasiCompactStack_of_isSurjective B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS (𝟙 𝒴) j).snd (hjqc 𝒴 (𝟙 𝒴) hYqc) ?_
    refine isSurjective_of_isTwoFibreProduct B S hS _
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS (𝟙 𝒴) j) ?_
    rw [IsSurjective, AlgebraicStacks.pointsMap_id]
    exact Function.surjective_id
  · exact isQuasiSeparatedAbs_of_isQuasiSeparated B S hS j hYqs
      (isQuasiSeparated_changeBase B S _ hS (contains_specULiftZ B) (toIntObject B S hS) j
        (isQuasiSeparated_of_isMonomorphism B S hS j
          (isMonomorphism_of_isImmersion B S hS j hj)))

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
