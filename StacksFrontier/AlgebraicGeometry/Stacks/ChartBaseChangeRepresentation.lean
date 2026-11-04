module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChartBaseChangeRelation
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySchemeMap
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat

/-!
# The relation of a base-changed chart is an affine scheme of the site (proof of Stacks 0DUQ)

Let `x : 𝒮_U ⟶ 𝒳` be a chart whose self-intersection `R = 𝒮_U ×_𝒳 𝒮_U` is represented by an
object `V` of the site with finite locally free source and target `s, t : V ⟶ U`, and let
`x' : 𝒮_W ⟶ 𝒳'` be its base change along `h : 𝒳' ⟶ 𝒳` (with `𝒮_W ≃ 𝒳' ×_𝒳 𝒮_U`). Then the
self-intersection `R'` of `x'` is represented by the fibre product `V' = V ×_{s, U} W` of the
site, and its source and target `s', t' : V' ⟶ W` are finite locally free: they are base changes
of `s` and `t` by the two cartesian squares of
`AlgebraicGeometry.Stack.ChartBaseChange.isPullback_relationSource` and
`AlgebraicGeometry.Stack.ChartBaseChange.isPullback_relationTarget`. In the source's words,
"`R' = U' ×_{𝒳'} U'`", and `V'` is affine when `W` is.

## Main results

* `AlgebraicGeometry.Stack.ChartBaseChange.exists_relation'_representation`: the representing
  object `V'` of `R'`, with the Yoneda forms of `s'`, `t'` and of `R' ⟶ R`, and the cartesian
  squares and finite local freeness on underlying schemes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ChartBaseChange

/-- A cartesian square of represented presheaves of the site is a cartesian square of the
underlying schemes. -/
theorem isPullback_toScheme_of_isPullback_yoneda {P X Y Z : BigFppfOver B S hS}
    {a : P ⟶ X} {b : P ⟶ Y} {c : X ⟶ Z} {d : Y ⟶ Z}
    (h : IsPullback (yoneda.map a) (yoneda.map b) (yoneda.map c) (yoneda.map d)) :
    IsPullback ((BigFppfOver.toScheme B S hS).map a) ((BigFppfOver.toScheme B S hS).map b)
      ((BigFppfOver.toScheme B S hS).map c) ((BigFppfOver.toScheme B S hS).map d) := by
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B S hS
  exact (IsPullback.of_map yoneda (yoneda.map_injective
    (by rw [Functor.map_comp, Functor.map_comp]; exact h.w)) h).map _

/-- A finite locally free morphism of schemes is stable under base change. -/
theorem isFiniteLocallyFree_of_isPullback {P X Y Z : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y}
    {c : X ⟶ Z} {d : Y ⟶ Z} (h : IsPullback a b c d)
    (hc : Stacks.Morphisms.IsFiniteLocallyFree c) : Stacks.Morphisms.IsFiniteLocallyFree b := by
  rw [Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation] at hc ⊢
  obtain ⟨h₁, h₂, h₃⟩ := hc
  exact ⟨MorphismProperty.of_isPullback h h₁, MorphismProperty.of_isPullback h h₂,
    MorphismProperty.of_isPullback h h₃⟩

variable {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} (h : 𝒳' ⟶ 𝒳) {U W : BigFppfOver B S hS}
  (x : schemeStack.{u, w} B S hS U ⟶ 𝒳)
  (eK : StacksRepresentableCFG.EquivalenceOver (schemeStack.{u, w} B S hS W).val.val.p
    (chartBaseChangeSquare h x).pt.val.val.p)

/-- **The relation of the base-changed chart is represented by an object of the site**, whose
source and target are finite locally free when those of `R` are, and which is affine when `W`
is. -/
theorem exists_relation'_representation {V : BigFppfOver B S hS}
    (eR : StacksRepresentableCFG.EquivalenceOver (rel x).val.p
      (presheafOfCategories (yoneda.obj V ⋙ typeToCat)).p)
    (s t : V ⟶ U)
    (hs : yoneda.map s = SelfIntersection.relationSourceMap
      (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (R := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
      (PresheafOfCategories.sliceElementsEquivalenceOver U) eR)
    (ht : yoneda.map t = SelfIntersection.relationTargetMap
      (U := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (R := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
      (PresheafOfCategories.sliceElementsEquivalenceOver U) eR)
    (hsF : Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map s))
    (htF : Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map t))
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W)) (fU : W ⟶ U)
    (hfU : yoneda.map fU = representingMap B S hS _ _ (yoneda.obj W) (yoneda.obj U)
      (PresheafOfCategories.sliceElementsEquivalenceOver W)
      (PresheafOfCategories.sliceElementsEquivalenceOver U) (chartMap h x eK)) :
    ∃ (V' : BigFppfOver B S hS)
      (eR' : StacksRepresentableCFG.EquivalenceOver (rel' h x eK).val.p
        (presheafOfCategories (yoneda.obj V' ⋙ typeToCat)).p)
      (s' t' : V' ⟶ W) (fV : V' ⟶ V),
      yoneda.map s' = SelfIntersection.relationSourceMap
        (U := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩)
        (R := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩)
        (PresheafOfCategories.sliceElementsEquivalenceOver W) eR' ∧
      yoneda.map t' = SelfIntersection.relationTargetMap
        (U := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩)
        (R := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩)
        (PresheafOfCategories.sliceElementsEquivalenceOver W) eR' ∧
      yoneda.map fV = representingMap B S hS _ _ (yoneda.obj V') (yoneda.obj V) eR' eR
        (relationMap h x eK) ∧
      IsPullback (yoneda.map fV) (yoneda.map s') (yoneda.map s) (yoneda.map fU) ∧
      IsPullback (yoneda.map fV) (yoneda.map t') (yoneda.map t) (yoneda.map fU) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj V') ∧
      Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map s') ∧
      Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map t') := by
  let eU := PresheafOfCategories.sliceElementsEquivalenceOver U
  let eW := PresheafOfCategories.sliceElementsEquivalenceOver W
  -- the relation `R'` is represented by an algebraic space (Stacks 04T4 (1))
  obtain ⟨F, hF, ⟨eF⟩⟩ :=
    SelfIntersection.isRepresentableByAlgebraicSpace_relation_of_isAlgebraicStack
      B S hS (schemeStack.{u, w} B S hS W).val 𝒳'.val (chart' h x eK).hom 𝒳'.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W)
  -- the source square for that representation identifies it with `V ×_{s, U} W`
  have hpb₀ := isPullback_relationSource (U₀ := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
    (U₀' := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩)
    (R₀ := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
    (R₀' := ⟨F, hF⟩) h x eK eU eW eR eF
  rw [← hs, ← hfU] at hpb₀
  have hyP : IsPullback (yoneda.map (pullback.fst s fU)) (yoneda.map (pullback.snd s fU))
      (yoneda.map s) (yoneda.map fU) := (IsPullback.of_hasPullback s fU).map yoneda
  let i : F ≅ yoneda.obj (pullback s fU) := hpb₀.isoIsPullback _ _ hyP
  let eR' : StacksRepresentableCFG.EquivalenceOver (rel' h x eK).val.p
      (presheafOfCategories (yoneda.obj (pullback s fU) ⋙ typeToCat)).p :=
    eF.trans (PresheafOfCategories.equivalenceOverOfIso i)
  -- the two squares for the new representation
  have hsq := isPullback_relationSource (U₀ := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
    (U₀' := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩)
    (R₀ := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
    (R₀' := ⟨yoneda.obj (pullback s fU), isAlgebraicSpace_yoneda B S hS _⟩) h x eK eU eW eR eR'
  have htq := isPullback_relationTarget (U₀ := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
    (U₀' := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩)
    (R₀ := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
    (R₀' := ⟨yoneda.obj (pullback s fU), isAlgebraicSpace_yoneda B S hS _⟩) h x eK eU eW eR eR'
  rw [← hs, ← hfU] at hsq
  rw [← ht, ← hfU] at htq
  obtain ⟨s', hs'⟩ := yoneda.map_surjective (SelfIntersection.relationSourceMap
    (U := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩)
    (R := ⟨yoneda.obj (pullback s fU), isAlgebraicSpace_yoneda B S hS _⟩) eW eR')
  obtain ⟨t', ht'⟩ := yoneda.map_surjective (SelfIntersection.relationTargetMap
    (U := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩)
    (R := ⟨yoneda.obj (pullback s fU), isAlgebraicSpace_yoneda B S hS _⟩) eW eR')
  obtain ⟨fV, hfV⟩ := yoneda.map_surjective (representingMap B S hS _ _
    (yoneda.obj (pullback s fU)) (yoneda.obj V) eR' eR (relationMap h x eK))
  rw [← hs', ← hfV] at hsq
  rw [← ht', ← hfV] at htq
  have hs'F := isFiniteLocallyFree_of_isPullback (isPullback_toScheme_of_isPullback_yoneda hsq) hsF
  have ht'F := isFiniteLocallyFree_of_isPullback (isPullback_toScheme_of_isPullback_yoneda htq) htF
  have hV' : IsAffine ((BigFppfOver.toScheme B S hS).obj (pullback s fU)) := by
    have h₁ := hs'F
    rw [Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation] at h₁
    have := h₁.1
    exact isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map s')
  exact ⟨pullback s fU, eR', s', t', fV, hs', ht', hfV, hsq, htq, hV', hs'F, ht'F⟩

end ChartBaseChange

end AlgebraicGeometry.Stack

end
