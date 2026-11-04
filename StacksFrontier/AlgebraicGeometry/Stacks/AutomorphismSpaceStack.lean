module

public import StacksFrontier.AlgebraicGeometry.Stacks.InertiaAutomorphismCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartSlicingFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismMonotone
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersection
public import StacksFrontier.Deformation.Artin.Infinitesimal.TangentFlatBaseChangeStack

/-!
# The automorphism space of a point, as an algebraic stack over the base of the point

Let `𝒳` be an algebraic stack over `S` and `x` an object of `𝒳` over a scheme `U`. The presheaf
`Mor(x, x)` of Stacks 02ZB, read on the big fppf site of `U` (`AlgebraicGeometry.Stack.autSpace`),
is the automorphism group algebraic space `Isom(x, x)` of the point (Stacks 04YP): every vertical
morphism of a category fibred in groupoids is invertible. It is an algebraic space over `U`
(`AlgebraicGeometry.Stack.isAlgebraicSpace_autSpace`), and it is locally of finite presentation
over `U` as soon as the inertia `ℐ_𝒳 ⟶ 𝒳` is
(`AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_autSpace`), being the base change of the
inertia along `x`.

An algebraic space `F` over a scheme `T` is an algebraic stack over `T` through its category of
elements, and its 1-morphism to the terminal object `T` of the big fppf site of `T`
(`AlgebraicGeometry.Stack.spaceToBase`) passes the smooth-diagram test of Stacks 06Q2 at local
finite presentation exactly when `F ⟶ T` is locally of finite presentation
(`AlgebraicGeometry.Stack.hasPropertyOnEverySmoothDiagram_spaceToBase`). This is the shape in
which Stacks 0DNT asks for finiteness of an algebraic stack over its base.

## Main definitions

* `AlgebraicGeometry.Stack.autSpace`: `Mor(x, x)` on the big fppf site of `U`.
* `AlgebraicGeometry.Stack.spaceToBase`: the 1-morphism from the category of elements of a
  presheaf on the big fppf site of `T` to the terminal object.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicSpace_autSpace`.
* `AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_autSpace`.
* `AlgebraicGeometry.Stack.hasPropertyOnEverySmoothDiagram_spaceToBase`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

section AutSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **`Mor(x, x)` of a point `x` of `𝒳` over `U`, on the big fppf site of `U`.** For a category
fibred in groupoids this is the automorphism presheaf `Isom(x, x)` of Stacks 04YP. -/
abbrev autSpace (U : BigFppfOver B S hS)
    (x : (haveI := 𝒳.val.isFiberedInGroupoids.isFibered; 𝒳.val.val.p.Fiber U)) :
    (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u :=
  letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  (Over.iteratedSliceBackward U).op ⋙ 𝒳.val.val.p.morPresheaf x x

/-- `Isom(x, x)` is the whole of `Mor(x, x)`. -/
def isomSpaceIsoAutSpace (U : BigFppfOver B S hS) (x : 𝒳.val.val.p.Fiber U) :
    isomSpace B S hS 𝒳.val U x x ≅ autSpace 𝒳 U x :=
  letI : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  Functor.isoWhiskerLeft (Over.iteratedSliceBackward U).op
    (isomPresheafIsoMorPresheaf _ 𝒳.val.isFiberedInGroupoids x x)

/-- **The automorphism space of a point of an algebraic stack is an algebraic space.** -/
theorem isAlgebraicSpace_autSpace (U : BigFppfOver B S hS) (x : 𝒳.val.val.p.Fiber U) :
    IsAlgebraicSpace B U.left.1 U.left.2 (autSpace 𝒳 U x) := by
  have : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  obtain ⟨F, hF, ⟨e⟩⟩ := (hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳.val).mp
    (SelfIntersection.hasRepresentableDiagonal_of_isAlgebraicStack B S hS 𝒳.val 𝒳.property) U x x
  let e' : F ≅ isomSpace B S hS 𝒳.val U x x :=
    ((Functor.FullyFaithful.ofFullyFaithful uliftFunctor.{u, u}).whiskeringRight _).preimageIso e
  exact isAlgebraicSpace_of_iso B U.left.1 U.left.2 (e' ≪≫ isomSpaceIsoAutSpace 𝒳 U x).symm hF

/-- **The automorphism space of a point is locally of finite presentation when the inertia is.**
It is the base change of `ℐ_𝒳 ⟶ 𝒳` along the point. -/
theorem isLocallyOfFinitePresentation_autSpace
    (hI : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
      (inertiaProjectionAlgebraicStacks B S hS 𝒳))
    (U : BigFppfOver B S hS) (x : 𝒳.val.val.p.Fiber U) :
    Space.IsLocallyOfFinitePresentation B U.left.1 U.left.2 (terminal.from (autSpace 𝒳 U x)) := by
  have : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  exact isLocallyOfFinitePresentation_terminal_of_iso B U.left.1 U.left.2
    (isomSpaceIsoAutSpace 𝒳 U x)
    ((isLocallyOfFinitePresentation_inertiaProjection_iff_isomSpace B S hS 𝒳).1 hI U x)

end AutSpace

section SpaceToBase

variable (B : BigFppfSite.{u}) (T : Scheme.{u}) (hT : B.Contains T)
  (F : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B T hT F)

/-- **The 1-morphism from the category of elements of a presheaf to the terminal object.** -/
def spaceToBase :
    fibredCategory B T hT F ⟶ schemeFibredCategory B T hT (Over.mk (𝟙 (B.obj hT))) :=
  (algebraicSpaceStackMap.{u, w} B T hT hF (isAlgebraicSpace_yoneda B T hT _)
      (Space.toYonedaId B T hT F)).hom ≫
    equivalenceOverInvMap B T hT (yoneda.obj (Over.mk (𝟙 (B.obj hT))))
      (PresheafOfCategories.sliceElementsEquivalenceOver (Over.mk (𝟙 (B.obj hT))))

/-- The backward 1-morphism of the representing equivalence of the terminal object is smooth. -/
theorem isSmooth_equivalenceOverInvMap_terminal :
    AlgebraicStacks.IsSmooth B T hT
      (Bicategory.InducedBicategory.mkHom
        (equivalenceOverInvMap B T hT (yoneda.obj (Over.mk (𝟙 (B.obj hT))))
          (PresheafOfCategories.sliceElementsEquivalenceOver (Over.mk (𝟙 (B.obj hT))))) :
        algebraicSpaceStack.{u, w} B T hT (yoneda.obj (Over.mk (𝟙 (B.obj hT))))
            (isAlgebraicSpace_yoneda B T hT _) ⟶
          schemeStack.{u, w} B T hT (Over.mk (𝟙 (B.obj hT)))) := by
  let Psm : MorphismProperty ((BigFppfOver B T hT)ᵒᵖ ⥤ Type u) :=
    fun {_ _} q => Space.IsSmooth B T hT q
  have _ : (spaceProperty B T hT Psm).IsStableUnderBaseChange := by
    simpa [Psm, spaceProperty] using Space.isSmooth_isStableUnderBaseChange B T hT
  have _ : (spaceProperty B T hT Psm).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B T hT) :=
    Space.smooth_isLocalAtTarget_fppf B T hT
  obtain ⟨hrep, hrel⟩ := isRelativelySmooth_equivalenceOverInvMap
    (𝒳 := schemeFibredCategory B T hT (Over.mk (𝟙 (B.obj hT)))) B T hT
    (yoneda.obj (Over.mk (𝟙 (B.obj hT)))) (isAlgebraicSpace_yoneda B T hT _)
    (PresheafOfCategories.sliceElementsEquivalenceOver (Over.mk (𝟙 (B.obj hT))))
  exact (hasPropertyOnSomeSmoothDiagram_iff_relative B T hT Psm
    (Space.isSmoothLocalOnSourceAndTarget_smooth B T hT)
    (isAlgebraicStack_fibredCategory.{u, w} B T hT _ (isAlgebraicSpace_yoneda B T hT _))
    (isAlgebraicStack_schemeFibredCategory.{u, w} B T hT _) _ hrep).2 hrel

/-- **The 1-morphism of an algebraic space locally of finite presentation over `T` to `T` is
locally of finite presentation** in the sense of Stacks 06Q2, i.e. passes the smooth-diagram
test of Stacks 06FM. -/
theorem hasPropertyOnEverySmoothDiagram_spaceToBase
    (hlfp : Space.IsLocallyOfFinitePresentation B T hT (terminal.from F)) :
    HasPropertyOnEverySmoothDiagram B T hT
      (fun _ _ g => Space.IsLocallyOfFinitePresentation B T hT g)
      (spaceToBase.{u, w} B T hT F hF) := by
  have h1 : Space.IsLocallyOfFinitePresentation B T hT (Space.toYonedaId B T hT F) :=
    Space.holdsOnEveryEtaleChart_of_isTerminal B T hT terminalIsTerminal
      (Over.mkIdTerminal.isTerminalObj yoneda _) _ _ hlfp
  have h2 := (isLocallyOfFinitePresentation_algebraicSpaceStackMap_iff.{u, w} B T hT hF
    (isAlgebraicSpace_yoneda B T hT _) (Space.toYonedaId B T hT F)).2 h1
  exact AlgebraicStacks.isLocallyOfFinitePresentation_comp B T hT _ _ h2
    (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B T hT _
      (isSmooth_equivalenceOverInvMap_terminal.{u, w} B T hT))

end SpaceToBase

end AlgebraicGeometry.Stack
