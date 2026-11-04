module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ComparisonAlgebraicSpacesTransport
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackTransitionReindex

/-!
# The unit condition for the transition morphism of Stacks 06WT

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces, `ℱ` a quasi-coherent module on the
quotient stack `[U/R]`, and `α : t^*𝒢 ⟶ s^*𝒢` the transition morphism of `𝒢 = x^*ℱ|_{U_étale}`
(`AlgebraicGeometry.Stack.quotientStackTransition`).  This file proves the unit condition of
Stacks 0441 for `(𝒢, α)`: the reindexing of `α` along the unit `e : U ⟶ R` is the transport along
`e ≫ t = e ≫ s`.  The 2-morphism of Stacks 044S is, at the identity arrow of a point, the image of
an arrow of `𝒮_U`; so the two comparison maps of equation 076R over `U` (through `t ∘ e` and
through `s ∘ e`) differ by that transport, and the reindexing computation
`AlgebraicGeometry.Stack.groupoidPullbackTransition_quotientStackTransition` concludes.

## Main results

* `AlgebraicGeometry.Stack.reindexTarget_comparisonMorphism_identityArrow`: the comparison
  morphisms of the two triangles over `U` agree.
* `AlgebraicGeometry.Stack.groupoidPullbackTransition_quotientStackTransition_identityArrow`:
  the unit condition.

## References

* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
* [Stacks Project, Tag 044S](https://stacks.math.columbia.edu/tag/044S)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry.GroupoidInAlgebraicSpaces

universe u

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)

/-- The two composites of the unit with the target and with the source agree. -/
theorem identityArrow_comp_target_eq_source :
    identityArrow G ≫ G.target = identityArrow G ≫ G.source :=
  (identityArrow_comp_target G).trans (identityArrow_comp_source G).symm

/-- The base of a transport in the category fibred in sets attached to a presheaf. -/
theorem fibredCategory_eqToHom_base {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    {X Y : (fibredCategory C S hS F).val.obj} (h : X = Y) :
    (eqToHom h).base = eqToHom (congrArg Pseudofunctor.CoGrothendieck.base h) := by
  cases h
  rfl

/-- **The comparison morphisms of the two triangles over the unit agree.**  At the identity arrow
of a point, the 2-morphism of Stacks 044S is the image of an arrow of `𝒮_U` over the identity, so
the comparison morphism through `t ∘ e` (carried by that 2-morphism) is the comparison morphism
through `s ∘ e` (carried by the identity). -/
theorem reindexTarget_comparisonMorphism_identityArrow
    (d : Space.ChartDiagram C S hS G.objects.obj G.objects.obj
      (identityArrow G ≫ G.target).hom) :
    Space.comparisonMorphism C S hS (fibredCategory C S hS G.objects.obj).val.p
        (fibredCategory C S hS G.objects.obj).val.p
        (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS G.objects.obj).val.p)
        (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS G.objects.obj).val.p)
        (reindexLeg G (identityArrow G) ⋙ quotientStackTargetLeg G)
        (reindexLeg G (identityArrow G) ⋙ (quotientStackSourceLeg G ⋙ quotientStackProj G))
        (quotientStackProj G)
        (Functor.isoWhiskerLeft (reindexLeg G (identityArrow G)) (quotientStackTwoArrowIso G))
        (identityArrow G ≫ G.target) (reindexTargetChartIso G (identityArrow G)) d =
      Space.comparisonMorphism C S hS (fibredCategory C S hS G.objects.obj).val.p
        (fibredCategory C S hS G.objects.obj).val.p
        (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS G.objects.obj).val.p)
        (StacksRepresentableCFG.EquivalenceOver.refl (fibredCategory C S hS G.objects.obj).val.p)
        (reindexLeg G (identityArrow G) ⋙ quotientStackSourceLeg G)
        (reindexLeg G (identityArrow G) ⋙ (quotientStackSourceLeg G ⋙ quotientStackProj G))
        (quotientStackProj G) (Iso.refl _) (identityArrow G ≫ G.source)
        (reindexSourceChartIso G (identityArrow G))
        (d.transport C S hS (identityArrow_comp_target_eq_source G)) := by
  set Y := (Space.restrictionFunctor C S hS G.objects.obj
      (fibredCategory C S hS G.objects.obj).val.p
      (StacksRepresentableCFG.EquivalenceOver.refl
        (fibredCategory C S hS G.objects.obj).val.p)).obj d.U
  set X := (reindexLeg G (identityArrow G)).obj Y with hX
  obtain ⟨g, hg₁, hg₂, hg₃⟩ := quotientStackTwoArrow_app G X
  simp only [Space.comparisonMorphism, Space.comparisonChartHom, reindexTargetChartIso,
    reindexSourceChartIso, quotientStackTwoArrowIso, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Iso.symm_inv, asIso_hom]
  have h1 : (quotientStackTwoArrowNat G).app X =
      (pointwiseToQuotientStack G).map g := eq_of_heq hg₃
  rw [h1]
  have hs : ∀ (T : (BigFppfOver C S hS)ᵒᵖ) (x : G.objects.obj.obj T),
      G.source.hom.app T ((identityArrow G).hom.app T x) = x := fun T x =>
    congrArg (fun k => k.hom.app T x) (identityArrow_comp_source G)
  have hfib : G.source.hom.app (op X.base) X.fiber.as = G.target.hom.app (op X.base) X.fiber.as :=
    (congrArg (fun k => k.hom.app (op X.base) Y.fiber.as)
      (identityArrow_comp_target_eq_source G)).symm
  have hobj : (quotientStackSourceLeg G).obj X = (quotientStackTargetLeg G).obj X :=
    (associatedMap_obj C S hS G.source.hom X).trans (Eq.trans
      (congrArg (fun a => (⟨X.base, Discrete.mk a⟩ : (fibredCategory C S hS G.objects.obj).val.obj))
        hfib) (associatedMap_obj C S hS G.target.hom X).symm)
  have hk : (pointwiseToQuotientStack G).map g = (quotientStackProj G).map (eqToHom hobj) := by
    change _ = (pointwiseToQuotientStack G).map ((pointwiseObjectInclusion G).map (eqToHom hobj))
    congr 1
    apply pointwiseHom_ext G.toGroupoidInFunctors
    · exact hg₁.trans (fibredCategory_eqToHom_base hobj).symm
    · refine hg₂.trans (Eq.trans ?_
        (evaluationArrow_eqToHom_identity G.toGroupoidInFunctors _
          (Discrete.eq_of_hom (eqToHom hobj).fiber)).symm)
      refine (identityArrow_hom_app G _ Y.fiber.as).trans ?_
      exact congrArg (G.toGroupoidInFunctors.identity _) (hs _ _).symm
  rw [hk, ← Functor.map_comp]
  refine Eq.trans ?_ (Category.id_comp _).symm
  refine congrArg (quotientStackProj G).map (fibredCategory_hom_ext _ _ ?_)
  change (eqToHom hobj).base ≫ _ = _
  refine (congrArg (· ≫ _) ((fibredCategory_eqToHom_base hobj).trans (eqToHom_refl _ _))).trans ?_
  refine (Category.id_comp _).trans ?_
  rfl

variable (F : QuotientStackModules G) (hF : F.IsQuasicoherentOnSite)

include hF in
/-- **The comparison map through `s ∘ a` is an isomorphism** for a quasi-coherent module on
`[U/R]` and any morphism `a : P ⟶ R` of algebraic spaces. -/
theorem isIso_reindexSourceComparison {P : AlgebraicSpaces C S hS} (a : P ⟶ G.arrows) :
    IsIso (reindexSourceComparison G a F) :=
  Space.isIso_comparisonAlgebraicSpacesModules C S hS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun _ _ k hx hy => bijective_restrictionBaseChange_fibredRings_of_isQuasicoherentOnSite C S hS
      (quotientStack G).p (isFiberedInGroupoids_quotientStack G) F hF k hx hy)
    (isQuasicoherentOnSite_quotientStackObjectRestriction G F hF)

/-- Over the unit, the transport along `e ≫ t = e ≫ s` followed by the comparison map through
`s ∘ e` is the comparison map through `t ∘ e`. -/
theorem pullbackTransport_comp_reindexSourceComparison_identityArrow :
    Space.pullbackTransport _ (identityArrow_comp_target_eq_source G) ≫
        reindexSourceComparison G (identityArrow G) F =
      reindexTargetComparison G (identityArrow G) F :=
  Space.pullbackTransport_comp_comparisonAlgebraicSpacesModules C S hS _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ (identityArrow_comp_target_eq_source G)
    (fun d => by exact reindexTarget_comparisonMorphism_identityArrow G d) _

include hF in
/-- The unit condition, with the transport read on the module of the comparison maps.  It is a
separate declaration because the kernel does not check the cancellation against the statement
of `groupoidPullbackTransition_quotientStackTransition_identityArrow` directly. -/
private theorem groupoidPullbackTransition_identityArrow_eq_pullbackTransport :
    Space.groupoidPullbackTransition C S hS G _ (quotientStackTransition G F hF)
        (identityArrow G) = Space.pullbackTransport _ (identityArrow_comp_target_eq_source G) := by
  have := isIso_reindexSourceComparison G F hF (identityArrow G)
  have e1 := groupoidPullbackTransition_quotientStackTransition G (identityArrow G) F hF
  have e2 := pullbackTransport_comp_reindexSourceComparison_identityArrow G F
  exact (Iso.cancel_iso_hom_right _ _
    (asIso (reindexSourceComparison G (identityArrow G) F))).1 (e1.trans e2.symm)

include hF in
/-- **The unit condition of Stacks 0441 for the transition morphism of Stacks 06WT**: the
reindexing of `α` along the unit `e : U ⟶ R` is the transport along `e ≫ t = e ≫ s`. -/
theorem groupoidPullbackTransition_quotientStackTransition_identityArrow :
    Space.groupoidPullbackTransition C S hS G (quotientStackObjectRestriction G F)
        (quotientStackTransition G F hF) (identityArrow G) =
      Space.pullbackTransport (quotientStackObjectRestriction G F)
        ((identityArrow_comp_target G).trans (identityArrow_comp_source G).symm) :=
  groupoidPullbackTransition_identityArrow_eq_pullbackTransport G F hF

end AlgebraicGeometry.Stack

end
