module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Groupoid.Discrete
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtale.StandardVCoveringLimits
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableBySpace.Basic
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableBySpace.Characterization
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalOverTerminal
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingOverTerminal
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.Representability
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LimitPreservingOnObjects
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.FiberedCategory.ChoiceOfPullbacks
public import StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoids
public import StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoidsSupplement
public import StacksFrontier.CategoryTheory.FiberedCategory.OfPresheaf
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElements
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElementsEquivalence
public import StacksFrontier.CategoryTheory.FiberedCategory.SliceFunctorComparison
public import StacksFrontier.CategoryTheory.TwoFibreProductOverReindex
public import StacksFrontier.CategoryTheory.TwoYoneda.Fibered
public import StacksFrontier.RingTheory.Algebra.DirectLimit.FinitePresentation
import all StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingRepresentable

/-!
# Supplement to `LimitPreservingRepresentable`

The results of this module extend those of
`StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingRepresentable`.
They use imports, universe variables or `open` declarations that the base module does not
have, and are kept in a module of their own so that its header is unchanged.

## Main results

* `algebraicSpaceMap_property_iff_of_sectionIso_univ`
* `representedAlgebraicSpace_isPullback_of_sectionIso_univ`
* `algebraicSpaceMap_property_of_sectionIso_univ`
* `algebraicSpaceMap_property_of_cover_univ`
* `exists_fiberIso_pullback_of_limitPreserving_univ`
* `exists_sectionIso_of_limitPreserving_univ`
* `exists_sectionIso_of_limitPreserving_smallerBase_univ`
* `exists_representative_with_property_at_affine_finitePresentation_univ`
* `represented_property_of_affine_stage_univ`
* `represented_property_of_affine_presentation_univ`
* `limitPreserving_small_univ`
* `represented_property_of_affine_chart_univ`
* `hasRelativeProperty_of_affine_locallyOfFinitePresentation_univ`
-/

/-! ### The generalizations made by this development

The declarations below restate, under weaker hypotheses or at more general universes, declarations
of this file whose statements are kept as they are above. Each carries the name of the declaration
it generalizes with the suffix `_univ` (or `Univ` for a definition). -/

universe u u₁ u₂ v₁ v₂ v w vI wI vC uC uS uX uY uZ uD vX vY vZ vD

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion
  Functor.ChoiceOfPullbacks.sliceFunctor

attribute [local implicit_reducible] TwoFibreProductOver.reindex
  TwoFibreProductOver.reindexSymm TwoFibreProductOver.fst

-- The fibre of the reindexed 2-fibre product is given by a chain of definitions, and the
-- components of one of its morphisms are typed through that chain; unification has to see
-- through it to recognise the base component as an identity.

private theorem algebraicSpaceMap_property_iff_of_sectionIso_univ
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.RespectsIso]
    {𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (BigFppfOver B S hS)}
    {𝒴 : CatFiberedInGroupoids.{u, v₁, u + 1, v₂}
      (BigFppfOver B S hS)} (f : 𝒳.val ⥤ᵇ 𝒴.val)
    (U : BigFppfOver B S hS)
    (y y' : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (α : y ≅ y')
    (hα : ∀ W, 𝒴.val.p.IsHomLift (𝟙 ((Over.map U.hom).obj W)) (α.hom.app W))
    (F G : AlgebraicSpaces B U.left.1 U.left.2)
    (eF : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        f.toFunctor) (PresheafOfCategories.discreteProjection F.obj))
    (eG : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y'
        f.toFunctor) (PresheafOfCategories.discreteProjection G.obj)) :
    P (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor
        B U.left.1 S U.left.2 hS U.hom).obj F)) ↔
    P (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor
        B U.left.1 S U.left.2 hS U.hom).obj G)) := by
  let e := representedPresheafIsoOfSectionIso α hα F.obj G.obj eF eG
  exact algebraicSpaceMap_property_iff_of_iso B S hS P U F G {
    hom := ObjectProperty.homMk e.hom
    inv := ObjectProperty.homMk e.inv
    hom_inv_id := by
      apply ObjectProperty.hom_ext
      exact e.hom_inv_id
    inv_hom_id := by
      apply ObjectProperty.hom_ext
      exact e.inv_hom_id }

/-- Pushing forward along `h.left` and then along `U.hom` is pushing forward along `V.hom`. -/
private theorem overMap_left_comp_overMap_hom
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {V U : BigFppfOver B S hS} (h : V ⟶ U) :
    Over.map h.left ⋙ Over.map U.hom = Over.map V.hom := by
  rw [← Over.mapComp_eq, Over.w h]

private theorem representedAlgebraicSpace_isPullback_of_sectionIso_univ
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (BigFppfOver B S hS)}
    {𝒴 : CatFiberedInGroupoids.{u, v₁, u + 1, v₂}
      (BigFppfOver B S hS)} (f : 𝒳.val ⥤ᵇ 𝒴.val)
    {V U : BigFppfOver B S hS} (h : V ⟶ U)
    (yU : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (yV : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.obj)
    (a : yV ≅ Over.map h.left ⋙ yU)
    (ha : ∀ W, 𝒴.val.p.IsHomLift (𝟙 ((Over.map V.hom).obj W)) (a.hom.app W))
    (F : AlgebraicSpaces B U.left.1 U.left.2)
    (G : AlgebraicSpaces B V.left.1 V.left.2)
    (eF : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p yU
        f.toFunctor) (PresheafOfCategories.discreteProjection F.obj))
    (eG : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map V.hom) 𝒳.val.p 𝒴.val.p yV
        f.toFunctor) (PresheafOfCategories.discreteProjection G.obj)) :
    ∃ t, IsPullback t
      (algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor
          B V.left.1 S V.left.2 hS V.hom).obj G))
      (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor
          B U.left.1 S U.left.2 hS U.hom).obj F))
      (ObjectProperty.homMk (yoneda.map h)) := by
  let e := composeEquivalenceOver (reverseEquivalenceOver (reindexEquivalenceOver a ha)) eG
  let e' : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map h.left ⋙ Over.map U.hom)
        𝒳.val.p 𝒴.val.p (Over.map h.left ⋙ yU) f.toFunctor)
      (PresheafOfCategories.discreteProjection G.obj) := by
    rw [overMap_left_comp_overMap_hom h]
    exact e
  let i := representedPresheafRestrictionIso (Over.map U.hom) 𝒳.val.p 𝒴.val.p
    yU f.toFunctor (Over.map h.left) F.obj G.obj eF e'
  exact algebraicSpaceMap_isPullback_of_restrictionIso B S hS h F G i

private theorem algebraicSpaceMap_property_of_sectionIso_univ
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    {𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (BigFppfOver B S hS)}
    {𝒴 : CatFiberedInGroupoids.{u, v₁, u + 1, v₂}
      (BigFppfOver B S hS)} (f : 𝒳.val ⥤ᵇ 𝒴.val)
    {V U : BigFppfOver B S hS} (h : V ⟶ U)
    (yU : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (yV : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.obj)
    (a : yV ≅ Over.map h.left ⋙ yU)
    (ha : ∀ W, 𝒴.val.p.IsHomLift (𝟙 ((Over.map V.hom).obj W)) (a.hom.app W))
    (F : AlgebraicSpaces B U.left.1 U.left.2)
    (G : AlgebraicSpaces B V.left.1 V.left.2)
    (eF : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p yU
        f.toFunctor) (PresheafOfCategories.discreteProjection F.obj))
    (eG : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map V.hom) 𝒳.val.p 𝒴.val.p yV
        f.toFunctor) (PresheafOfCategories.discreteProjection G.obj))
    (hF : P (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor
        B U.left.1 S U.left.2 hS U.hom).obj F))) :
    P (algebraicSpaceMap B S hS V
      ((spacesOverSmallerBaseFunctor
        B V.left.1 S V.left.2 hS V.hom).obj G)) := by
  obtain ⟨t, ht⟩ := representedAlgebraicSpace_isPullback_of_sectionIso_univ B S hS f h
    yU yV a ha F G eF eG
  exact P.of_isPullback ht hF

private theorem algebraicSpaceMap_property_of_cover_univ
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, vI} B S hS)]
    {𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (BigFppfOver B S hS)}
    {𝒴 : CatFiberedInGroupoids.{u, v₁, u + 1, v₂}
      (BigFppfOver B S hS)} (f : 𝒳.val ⥤ᵇ 𝒴.val)
    (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (F : AlgebraicSpaces B U.left.1 U.left.2)
    (eF : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        f.toFunctor) (PresheafOfCategories.discreteProjection F.obj))
    (I : Type vI) (V : I → BigFppfOver B S hS) (g : ∀ i, V i ⟶ U)
    (hcover : Space.Topology.fppf.IsCovering B S hS
      (fun i => yoneda.obj (V i)) (fun i => yoneda.map (g i)))
    (htest : ∀ i, ∃ G : AlgebraicSpaces B (V i).left.1 (V i).left.2,
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map (V i).hom) 𝒳.val.p 𝒴.val.p
          (Over.map (g i).left ⋙ y) f.toFunctor)
        (PresheafOfCategories.discreteProjection G.obj)) ∧
      P (algebraicSpaceMap B S hS (V i)
        ((spacesOverSmallerBaseFunctor
          B (V i).left.1 S (V i).left.2 hS (V i).hom).obj G))) :
    P (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor
        B U.left.1 S U.left.2 hS U.hom).obj F)) := by
  let Vi : I → AlgebraicSpaces B S hS := fun i =>
    ⟨yoneda.obj (V i), isAlgebraicSpace_yoneda B S hS (V i)⟩
  let gi : ∀ i, Vi i ⟶
      (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :
        AlgebraicSpaces B S hS) :=
    fun i => ObjectProperty.homMk (yoneda.map (g i))
  have hR : Presieve.ofArrows Vi gi ∈
      (Space.Topology.fppf.precoverage.{u, vI} B S hS).coverings
        (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :
          AlgebraicSpaces B S hS) :=
    ⟨I, Vi, gi, rfl, hcover⟩
  apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd hR
  rintro W h hh ⟨i⟩
  obtain ⟨G, ⟨eG⟩, hG⟩ := htest i
  have ha : ∀ T, 𝒴.val.p.IsHomLift (𝟙 ((Over.map (V i).hom).obj T))
      ((Iso.refl (Over.map (g i).left ⋙ y)).hom.app T) := by
    intro T
    have ht : 𝒴.val.p.obj ((Over.map (g i).left ⋙ y).obj T) =
        (Over.map (V i).hom).obj T := by
      have hm : (Over.map (g i).left ⋙ y) ⋙ 𝒴.val.p = Over.map (V i).hom := by
        rw [Functor.assoc, hy, overMap_left_comp_overMap_hom]
      exact Functor.congr_obj hm T
    exact IsHomLift.of_fac' _ _ _ ht ht (by simp)
  obtain ⟨t, ht⟩ := representedAlgebraicSpace_isPullback_of_sectionIso_univ B S hS f (g i)
    y (Over.map (g i).left ⋙ y) (Iso.refl _) ha F G eF eG
  rwa [← ht.isoPullback_inv_snd, P.cancel_left_of_respectsIso]

attribute [local instance] AffinePresentationData.partialOrder AffinePresentationData.nonempty
  AffinePresentationData.directed AffinePresentationData.commRing
  AffinePresentationData.algebra AffinePresentationData.directedSystem

private theorem exists_fiberIso_pullback_of_limitPreserving_univ
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒴 : CatFiberedInGroupoids.{u, v₁, u + 1, v₂}
      (BigFppfOver B S hS))
    (hlimit : IsLimitPreservingOverTerminal.{u, u, u} B S hS 𝒴)
    (I : Type u) [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ BigAffineFppf B S hS) (c : Cone D)
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c))
    (x : 𝒴.val.p.Fiber ((BigAffineFppf.inclusion B S hS).obj c.pt))
    (pullbacks : Functor.ChoiceOfPullbacks 𝒴.val.p) :
    ∃ (i : I) (xi : 𝒴.val.p.Fiber
        ((BigAffineFppf.inclusion B S hS).obj (D.obj i))),
      Nonempty (x ≅ pullbacks.obj
        ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) xi) := by
  have : Nonempty I := IsCofiltered.nonempty
  let i : I := Classical.arbitrary I
  let inc := BigAffineFppf.inclusion B S hS
  let γ : 𝒴.val.p.obj x.1 ⟶ inc.obj (D.obj i) :=
    eqToHom x.2 ≫ inc.map (c.π.app i)
  have hγ : (𝟭 (BigFppfOver B S hS)).IsHomLift
      (inc.map (c.π.app i)) γ :=
    IsHomLift.of_fac' _ _ _ x.2 rfl (by simp [γ])
  have : (terminalCFG B S hS).val.p.IsHomLift
      (inc.map (c.π.app i)) γ := hγ
  have hγcart : (𝟭 (BigFppfOver B S hS)).IsStronglyCartesian
      (inc.map (c.π.app i)) γ :=
    (terminalCFG B S hS).2.isStronglyCartesian_homLift _ γ
  obtain ⟨i', _, xi, _, δ, β, _, hδ, hβ, hβiso, _, _⟩ :=
    hlimit I D c hc i ⟨inc.obj (D.obj i), rfl⟩ x γ hγcart
  have := hβiso
  exact ⟨i', xi, ⟨fibreIsoOfCartesianIso 𝒴.val.p pullbacks _ β hβ δ hδ⟩⟩

private theorem exists_sectionIso_of_limitPreserving_univ
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒴 : CatFiberedInGroupoids.{u, v₁, u + 1, v₂}
      (BigFppfOver B S hS))
    (hlimit : IsLimitPreservingOverTerminal.{u, u, u} B S hS 𝒴)
    (I : Type u) [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ BigAffineFppf B S hS) (c : Cone D)
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c))
    (G : Over ((BigAffineFppf.inclusion B S hS).obj c.pt) ⥤ 𝒴.val.obj)
    (hG : G ⋙ 𝒴.val.p = Over.forget ((BigAffineFppf.inclusion B S hS).obj c.pt))
    (pullbacks : Functor.ChoiceOfPullbacks 𝒴.val.p) :
    ∃ (i : I) (x : 𝒴.val.p.Fiber
        ((BigAffineFppf.inclusion B S hS).obj (D.obj i)))
      (a : G ≅ Over.map
        ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) ⋙
          pullbacks.sliceFunctor x),
      ∀ W, 𝒴.val.p.IsHomLift (𝟙 W.left) (a.hom.app W) := by
  obtain ⟨i, x, ⟨e⟩⟩ := exists_fiberIso_pullback_of_limitPreserving_univ
    B S hS 𝒴 hlimit I D c hc (Functor.ChoiceOfPullbacks.sliceObj G hG) pullbacks
  exact ⟨i, x, exists_sectionIso_of_fiberIso 𝒴.val.p
    (CatFiberedInGroupoids.isFiberedInGroupoids 𝒴) pullbacks
    ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) G hG x e⟩

-- The comparison isomorphism is transported along the iterated-slice equivalence, so the
-- components to be identified are typed through it.

private theorem exists_sectionIso_of_limitPreserving_smallerBase_univ
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒴 : CatFiberedInGroupoids.{u, v₁, u + 1, v₂}
      (BigFppfOver B S hS))
    (hlimit : IsLimitPreservingOverTerminal.{u, u, u} B S hS 𝒴)
    (I : Type u) [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ BigAffineFppf B S hS) (c : Cone D)
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c))
    (y : BigFppfOver B
      ((BigAffineFppf.inclusion B S hS).obj c.pt).left.1
      ((BigAffineFppf.inclusion B S hS).obj c.pt).left.2 ⥤ 𝒴.val.obj)
    (hy : y ⋙ 𝒴.val.p = Over.map
      ((BigAffineFppf.inclusion B S hS).obj c.pt).hom) :
    ∃ (i : I) (x : 𝒴.val.p.Fiber
        ((BigAffineFppf.inclusion B S hS).obj (D.obj i))),
      ∃ (a : y ≅ Over.map
        ((BigAffineFppf.inclusion B S hS).map (c.π.app i)).left ⋙
        sectionFromFiberObject B S hS 𝒴
          ((BigAffineFppf.inclusion B S hS).obj (D.obj i)) x),
        ∀ W, 𝒴.val.p.IsHomLift (𝟙 ((Over.map
          ((BigAffineFppf.inclusion B S hS).obj c.pt).hom).obj W))
          (a.hom.app W) := by
  let U := (BigAffineFppf.inclusion B S hS).obj c.pt
  let : 𝒴.val.p.IsFibered :=
    (CatFiberedInGroupoids.isFiberedInGroupoids 𝒴).isFibered
  let pullbacks := Functor.chosenPullbacks 𝒴.val.p
  have hG : (Over.iteratedSliceForward U ⋙ y) ⋙ 𝒴.val.p = Over.forget U := by
    rw [Functor.assoc, hy]
    exact iteratedSliceForward_overMap_eq_forget B U
  obtain ⟨i, x, a, ha⟩ := exists_sectionIso_of_limitPreserving_univ B S hS 𝒴
    hlimit I D c hc (Over.iteratedSliceForward U ⋙ y) hG pullbacks
  let V := (BigAffineFppf.inclusion B S hS).obj (D.obj i)
  let q : U ⟶ V := (BigAffineFppf.inclusion B S hS).map (c.π.app i)
  let a' : y ≅ Over.map q.left ⋙ V.iteratedSliceBackward ⋙
      pullbacks.sliceFunctor x := sectionIso_of_iteratedSlice q y
        (pullbacks.sliceFunctor x) a
  exact ⟨i, x, a', sectionIso_of_iteratedSlice_isHomLift q 𝒴.val.p y
    (pullbacks.sliceFunctor x) hy (pullbacks.sliceFunctor_comp x) a ha⟩

private theorem exists_representative_with_property_at_affine_finitePresentation_univ
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    {𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (BigFppfOver B S hS)}
    {𝒴 : CatFiberedInGroupoids.{u, v₁, u + 1, v₂}
      (BigFppfOver B S hS)}
    (f : 𝒳.val ⥤ᵇ 𝒴.val)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f)
    (hlocal : ∀ (U : BigFppfOver B S hS),
      IsAffine U.left.1 →
      LocallyOfFinitePresentation (B.inclusion.map U.hom) →
      ∀ (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
        (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
            f.toFunctor)
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor
            B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)))
    (U : BigFppfOver B S hS) (hU : IsAffine U.left.1)
    (hfp : LocallyOfFinitePresentation (B.inclusion.map U.hom))
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (hy : y ⋙ 𝒴.val.p = Over.map U.hom) :
    ∃ (F : AlgebraicSpaces B U.left.1 U.left.2),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          f.toFunctor)
        (PresheafOfCategories.discreteProjection F.obj)) ∧
      P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor
          B U.left.1 S U.left.2 hS U.hom).obj F)) := by
  obtain ⟨F, hF, ⟨e⟩⟩ := hf U y hy
  exact ⟨⟨F, hF⟩, ⟨e⟩, hlocal U hU hfp y hy F hF ⟨e⟩⟩

private theorem represented_property_of_affine_stage_univ
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    {𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (BigFppfOver B S hS)}
    {𝒴 : CatFiberedInGroupoids.{u, v₁, u + 1, v₂}
      (BigFppfOver B S hS)}
    (f : 𝒳.val ⥤ᵇ 𝒴.val)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f)
    (hlocal : ∀ (U : BigFppfOver B S hS),
      IsAffine U.left.1 →
      LocallyOfFinitePresentation (B.inclusion.map U.hom) →
      ∀ (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
        (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
            f.toFunctor)
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor
            B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)))
    {U V : BigFppfOver B S hS} (q : U ⟶ V)
    (hV : IsAffine V.left.1)
    (hVfp : LocallyOfFinitePresentation (B.inclusion.map V.hom))
    (yV : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.obj)
    (hyV : yV ⋙ 𝒴.val.p = Over.map V.hom)
    (yU : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (a : yU ≅ Over.map q.left ⋙ yV)
    (ha : ∀ W, 𝒴.val.p.IsHomLift (𝟙 ((Over.map U.hom).obj W)) (a.hom.app W))
    (F : AlgebraicSpaces B U.left.1 U.left.2)
    (eF : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p yU
        f.toFunctor) (PresheafOfCategories.discreteProjection F.obj)) :
    P (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor
        B U.left.1 S U.left.2 hS U.hom).obj F)) := by
  obtain ⟨G, ⟨eG⟩, hG⟩ :=
    exists_representative_with_property_at_affine_finitePresentation_univ
      B S hS P f hf hlocal V hV hVfp yV hyV
  exact algebraicSpaceMap_property_of_sectionIso_univ
    B S hS P f q yV yU a ha G F eG eF hG

private theorem represented_property_of_affine_presentation_univ
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    {𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (BigFppfOver B S hS)}
    {𝒴 : CatFiberedInGroupoids.{u, v₁, u + 1, v₂}
      (BigFppfOver B S hS)}
    (f : 𝒳.val ⥤ᵇ 𝒴.val)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f)
    (hlimit : IsLimitPreservingOverTerminal.{u, u, u} B S hS 𝒴)
    (hlocal : ∀ (U : BigFppfOver B S hS),
      IsAffine U.left.1 →
      LocallyOfFinitePresentation (B.inclusion.map U.hom) →
      ∀ (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
        (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
            f.toFunctor)
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor
            B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)))
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (hR : B.Contains (Spec (.of R)))
    (g : Spec (.of R) ⟶ S) [LocallyOfFinitePresentation g]
    (hA : B.Contains (Spec (.of A)))
    (D : AffinePresentationData R A)
    (y : BigFppfOver B
      ((BigAffineFppf.inclusion B S hS).obj
        (affinePresentation_siteConeOver B hR S hS g hA D).pt).left.1
      ((BigAffineFppf.inclusion B S hS).obj
        (affinePresentation_siteConeOver B hR S hS g hA D).pt).left.2 ⥤ 𝒴.val.obj)
    (hy : y ⋙ 𝒴.val.p = Over.map
      ((BigAffineFppf.inclusion B S hS).obj
        (affinePresentation_siteConeOver B hR S hS g hA D).pt).hom)
    (F : AlgebraicSpaces B
      ((BigAffineFppf.inclusion B S hS).obj
        (affinePresentation_siteConeOver B hR S hS g hA D).pt).left.1
      ((BigAffineFppf.inclusion B S hS).obj
        (affinePresentation_siteConeOver B hR S hS g hA D).pt).left.2)
    (eF : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map
        ((BigAffineFppf.inclusion B S hS).obj
          (affinePresentation_siteConeOver B hR S hS g hA D).pt).hom)
        𝒳.val.p 𝒴.val.p y f.toFunctor)
      (PresheafOfCategories.discreteProjection F.obj)) :
    P (algebraicSpaceMap B S hS
      ((BigAffineFppf.inclusion B S hS).obj
        (affinePresentation_siteConeOver B hR S hS g hA D).pt)
      ((spacesOverSmallerBaseFunctor B
        ((BigAffineFppf.inclusion B S hS).obj
          (affinePresentation_siteConeOver B hR S hS g hA D).pt).left.1
        S _ hS _).obj F)) := by
  let c := affinePresentation_siteConeOver B hR S hS g hA D
  let D' := affinePresentation_siteDiagramOver B hR S hS g D
  obtain ⟨i, x, a, ha⟩ := exists_sectionIso_of_limitPreserving_smallerBase_univ
    B S hS 𝒴 hlimit _ D' c
      (affinePresentation_siteConeOver_isLimit B hR S hS g hA D) y hy
  let V := (BigAffineFppf.inclusion B S hS).obj (D'.obj i)
  let q := (BigAffineFppf.inclusion B S hS).map (c.π.app i)
  let yV := sectionFromFiberObject B S hS 𝒴 V x
  have hyV : yV ⋙ 𝒴.val.p = Over.map V.hom :=
    sectionFromFiberObject_comp B S hS 𝒴 V x
  have hV : IsAffine V.left.1 := (D'.obj i).property
  have hfp : LocallyOfFinitePresentation (B.inclusion.map V.hom) :=
    affinePresentation_stageOver_map_locallyOfFinitePresentation B hR S hS g D i
  exact represented_property_of_affine_stage_univ B S hS P f hf hlocal q
    hV hfp yV hyV y a ha F eF

private theorem limitPreserving_small_univ
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒴 : CatFiberedInGroupoids.{u, v₁, u + 1, v₂}
      (BigFppfOver B S hS))
    (h : IsLimitPreservingOverTerminal.{u, max u vI, max u wI} B S hS 𝒴) :
    IsLimitPreservingOverTerminal.{u, u, u} B S hS 𝒴 := by
  intro I _ _ D c hc i y x γ hγ
  let : Category.{u} (ULift.{max u vI} I) := uliftCategory I
  let : Category.{max u wI}
      (ULiftHom.{max u wI} (ULift.{max u vI} I)) := ULiftHom.category
  let E : I ≌ ULiftHom.{max u wI} (ULift.{max u vI} I) :=
    ULiftHomULiftCategory.equiv I
  let D' := E.inverse ⋙ D
  let c' := c.whisker E.inverse
  have hc' : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c') :=
    (hc.whiskerEquivalence E.symm).ofIsoLimit
      ((BigAffineFppf.toScheme B S hS).mapConeWhisker (c := c) (E := E.inverse)).symm
  obtain ⟨i', j, rest⟩ := h _ D' c' hc' (E.functor.obj i) y x γ hγ
  exact ⟨E.inverse.obj i', E.inverse.map j, rest⟩

private theorem represented_property_of_affine_chart_univ
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    {𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (BigFppfOver B S hS)}
    {𝒴 : CatFiberedInGroupoids.{u, v₁, u + 1, v₂}
      (BigFppfOver B S hS)}
    (f : 𝒳.val ⥤ᵇ 𝒴.val)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f)
    (hlimit : IsLimitPreservingOverTerminal.{u, u, u} B S hS 𝒴)
    (hlocal : ∀ (U : BigFppfOver B S hS),
      IsAffine U.left.1 →
      LocallyOfFinitePresentation (B.inclusion.map U.hom) →
      ∀ (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
        (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
            f.toFunctor)
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor
            B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)))
    (U : BigFppfOver B S hS) (hU : IsAffine U.left.1)
    (V : Scheme.{u}) [IsAffine V] (hV : B.Contains V)
    (g : V ⟶ S) [LocallyOfFinitePresentation g]
    (k : U.left.1 ⟶ V) (hk : k ≫ g = B.inclusion.map U.hom)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (F : AlgebraicSpaces B U.left.1 U.left.2)
    (eF : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        f.toFunctor) (PresheafOfCategories.discreteProjection F.obj)) :
    P (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor
        B U.left.1 S U.left.2 hS U.hom).obj F)) := by
  obtain ⟨I, hI, hcof, D, c, ⟨hc⟩, hfp, hpt⟩ :=
    exists_affine_limit_presentation B S hS U hU V hV g k hk
  let := hI
  let := hcof
  obtain rfl : (BigAffineFppf.inclusion B S hS).obj c.pt = U :=
    congrArg (BigAffineFppf.inclusion B S hS).obj hpt
  obtain ⟨i, x, a, ha⟩ := exists_sectionIso_of_limitPreserving_smallerBase_univ
    B S hS 𝒴 hlimit I D c hc y hy
  exact represented_property_of_affine_stage_univ B S hS P f hf hlocal
    ((BigAffineFppf.inclusion B S hS).map (c.π.app i))
    (D.obj i).property (hfp i) (sectionFromFiberObject B S hS 𝒴 _ x)
    (sectionFromFiberObject_comp B S hS 𝒴 _ x) y a ha F eF

-- The affine refinement of the chart cover is indexed by a dependent pair, which unification
-- sees only after unfolding the two layers of `bind`.
attribute [local implicit_reducible] PreZeroHypercover.bind
  Precoverage.ZeroHypercover.bind PreZeroHypercover.pullback₁
  Precoverage.ZeroHypercover.pullback₁ in
/-- A base-change-stable, fppf-local property of a representable morphism can
be checked on affine bases locally of finite presentation when the target is
limit preserving on objects. -/
public theorem hasRelativeProperty_of_affine_locallyOfFinitePresentation_univ
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    {𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (BigFppfOver B S hS)}
    {𝒴 : CatFiberedInGroupoids.{u, v₁, u + 1, v₂}
      (BigFppfOver B S hS)}
    (f : 𝒳.val ⥤ᵇ 𝒴.val)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f)
    (hlimit : IsLimitPreservingOverTerminal.{u, max u vI, max u wI} B S hS 𝒴)
    (hlocal : ∀ (U : BigFppfOver B S hS),
      IsAffine U.left.1 →
      LocallyOfFinitePresentation (B.inclusion.map U.hom) →
      ∀ (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
        (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
            f.toFunctor)
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor
            B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))) :
    HasRelativePropertyBased B S hS P f hf := by
  classical
  intro U y hy F hF ⟨eF⟩
  let p : U.left.1 ⟶ S := B.inclusion.map U.hom
  let C := S.affineCover.pullback₁ p
  let W := C.bind fun i => (C.X i).affineCover
  let hW (i : W.I₀) : B.Contains (W.X i) :=
    Scheme.size_lt_of_isOpenImmersion (W.f i) U.left.2
  let V (i : W.I₀) : BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk (W.f i ≫ p) : B.obj (hW i) ⟶ B.obj hS)
  let g (i : W.I₀) : V i ⟶ U :=
    Over.homMk (ObjectProperty.homMk (W.f i)) rfl
  apply algebraicSpaceMap_property_of_cover_univ B S hS P f U y hy ⟨F, hF⟩ eF
    W.I₀ V g
  · exact fppfCovering_yoneda_of_open_cover B S hS U W.I₀ V g
      (fun i => inferInstanceAs (IsOpenImmersion (W.f i))) (Scheme.Cover.exists_eq W)
  · rintro ⟨i, j⟩
    let yV := Over.map (g ⟨i, j⟩).left ⋙ y
    have hyV : yV ⋙ 𝒴.val.p = Over.map (V ⟨i, j⟩).hom := by
      rw [Functor.assoc, hy, overMap_left_comp_overMap_hom]
    obtain ⟨G, hG, ⟨eG⟩⟩ := hf (V ⟨i, j⟩) yV hyV
    refine ⟨⟨G, hG⟩, ⟨eG⟩, ?_⟩
    let k : (V ⟨i, j⟩).left.1 ⟶ S.affineCover.X i :=
      (C.X i).affineCover.f j ≫ S.affineCover.pullbackHom p i
    have hk : k ≫ S.affineCover.f i = B.inclusion.map (V ⟨i, j⟩).hom :=
      calc k ≫ S.affineCover.f i
          = (C.X i).affineCover.f j ≫
              S.affineCover.pullbackHom p i ≫ S.affineCover.f i := Category.assoc _ _ _
        _ = (C.X i).affineCover.f j ≫ C.f i ≫ p :=
              congrArg (fun m => (C.X i).affineCover.f j ≫ m)
                (pullback.condition : C.f i ≫ p =
                  S.affineCover.pullbackHom p i ≫ S.affineCover.f i).symm
        _ = ((C.X i).affineCover.f j ≫ C.f i) ≫ p := (Category.assoc _ _ _).symm
        _ = B.inclusion.map (V ⟨i, j⟩).hom := rfl
    exact represented_property_of_affine_chart_univ B S hS P f hf
      (limitPreserving_small_univ B S hS 𝒴 hlimit) hlocal (V ⟨i, j⟩)
      (inferInstanceAs (IsAffine ((C.X i).affineCover.X j)))
      (S.affineCover.X i)
      (Scheme.size_lt_of_isOpenImmersion (S.affineCover.f i) hS)
      (S.affineCover.f i) k hk yV hyV ⟨G, hG⟩ eG

end AlgebraicGeometry.Stack

end
