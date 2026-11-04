module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStack
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.ActionGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack

/-!
# An affine group with a smooth classifying-stack covering is of finite type (Stacks 04AH)

Let `k` be a field and let `G` be an affine group scheme over `k`. If the classifying stack
`[Spec(k)/G]` admits a smooth surjective covering by a scheme, then `G` is of finite type
over `k`.

## Main definitions

* `AlgebraicGeometry.Stack.classifyingStack`: the classifying stack `[Spec(k)/G]` of a group
  algebraic space over a field, i.e. the quotient stack of the trivial action of `G` on the base.

## Main results

* `AlgebraicGeometry.Stack.isFiniteType_of_smoothSchemeCovering_classifyingStack`:
  **Stacks 04AH**.

## Implementation notes

An affine group scheme over `k` is a group algebraic space over the final algebraic space of the
big fppf site of `Spec(k)` — `AlgebraicGeometry.Space.GroupAlgebraicSpace`, which carries
**Stacks 06DX** for exactly this situation — whose structure morphism is affine in the sense of
**Stacks 03WF**; affineness of the structure morphism is what makes the group a scheme, and an
affine one. Its classifying stack is the quotient stack (**Stacks 044Q**) of the action groupoid
(**Stacks 0444**) of the trivial action of `G` on the monoidal unit of the slice over the base,
whose underlying algebraic space is the base itself. "Of finite type over `k`" is
`AlgebraicGeometry.Space.IsFiniteType`, part (3) of **Stacks 03XF**: locally of finite type and
quasi-compact.

"Has a smooth covering by a scheme" is the third clause of **Stacks 026O**
(`AlgebraicGeometry.Stack.IsAlgebraicStack`), written out for the classifying stack: a
1-morphism from the category represented by a scheme `U` over `Spec(k)`, representable by
algebraic spaces, every algebraic space representing whose base change along a scheme-valued
point of the stack has surjective and smooth structural morphism. Only that clause is assumed,
not algebraicity of the stack.

Two inputs the library does not have are carried as hypotheses and named in the tag clause.
**Stacks 04WZ**, representability of the diagonal of a quotient stack, is available here only
through `AlgebraicGeometry.Stack.hasRepresentableDiagonal_quotientStack_of_isomPresheafAlgebraic`,
which rests on **Stacks 04TB**; its conclusion is taken as the hypothesis `hdiag`. The implication
of **Stacks 06PL** that an algebraic classifying stack has a group locally of finite presentation
over the base is taken as the hypothesis `hfp`. The remaining two clauses of Stacks 026O are
discharged from the library: the quotient stack is fibred in groupoids and is a stack for the fppf
topology by `AlgebraicGeometry.Stack.isFiberedInGroupoids_quotientStack`,
`AlgebraicGeometry.Stack.isStack_quotientStack` and
`AlgebraicGeometry.Stack.isStackInGroupoids_quotientStack`.

Quasi-compactness of the structure morphism is derived from its affineness rather than assumed:
by **Stacks 03WF** every base change of it to an affine object of the site is represented by an
affine object, which is a quasi-compact algebraic space, and quasi-compactness of a morphism may
be tested on those base changes
(`AlgebraicGeometry.Space.isQuasiCompact_of_isQuasiCompactSpace_pullback_affine`).

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 04AH](https://stacks.math.columbia.edu/tag/04AH)
* [Stacks Project, Tag 04WZ](https://stacks.math.columbia.edu/tag/04WZ)
* [Stacks Project, Tag 06PL](https://stacks.math.columbia.edu/tag/06PL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry.Stack

universe u

/-- **An affine morphism of algebraic spaces over `S` is quasi-compact.** Quasi-compactness may
be tested on the base changes to the affine objects of the site, and by Stacks 03WF each of those
is represented by an affine object, hence is a quasi-compact algebraic space. -/
private theorem isQuasiCompact_of_isAffineHom
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (f : F ⟶ G) (hf : Space.IsAffineHom B S hS f) :
    Space.IsQuasiCompact B S hS f := by
  refine Space.isQuasiCompact_of_isQuasiCompactSpace_pullback_affine B S hS hF hG f ?_
  intro T hT g
  obtain ⟨W, p, q, hpb⟩ := hf ⟨T, hT⟩ g
  exact Space.isQuasiCompactSpace_of_iso B S hS
    (hpb.flip.isoIsPullback _ _ (IsPullback.of_hasPullback g f))
    (Space.isQuasiCompactSpace_yoneda_of_isAffine B S hS _ W.property)

variable {k : Type u} [Field k] (C : BigFppfSite.{u})
  (hk : C.Contains (Spec (.of k)))

/-- The classifying stack `[Spec(k)/G]` of a group algebraic space `G` over a field `k`: the
quotient stack of the action groupoid of the trivial action of `G` on the base. -/
noncomputable def classifyingStack
    (G : Space.GroupAlgebraicSpace C (Spec (.of k)) hk
      (Space.terminalSpace C (Spec (.of k)) hk).obj
      (Space.terminalSpace C (Spec (.of k)) hk).property) :
    CatFiberedInGroupoids (BigFppfOver C (Spec (.of k)) hk) :=
  letI : ModObj G.obj.X (𝟙_ (Over (Space.terminalSpace C (Spec (.of k)) hk).obj)) :=
    ModObj.trivialAction _ _
  CatFiberedInGroupoids.mk
    (quotientStack (Space.groupoidOfAction (Space.terminalSpace C (Spec (.of k)) hk)
      G.obj.X (𝟙_ (Over (Space.terminalSpace C (Spec (.of k)) hk).obj)) G.property
      (Space.terminalSpace C (Spec (.of k)) hk).property).groupoid)
    (isFiberedInGroupoids_quotientStack _)

/-- **Stacks 04AH.** Let `k` be a field and let `G` be an affine group scheme over `k`. If the
classifying stack `[Spec(k)/G]` has a smooth surjective covering by a scheme, then `G` is of
finite type over `k`.

The covering hypothesis is the third clause of Stacks 026O for the classifying stack. The
hypotheses `hdiag` and `hfp` are Stacks 04WZ and the forward implication of Stacks 06PL, which
this library does not have. -/
@[stacks 04AH "conditional on Stacks 04WZ, that the diagonal of a quotient stack is representable \
by algebraic spaces, and on the implication of Stacks 06PL that an algebraic classifying stack \
has a group locally of finite presentation over the base"]
theorem isFiniteType_of_smoothSchemeCovering_classifyingStack
    (G : Space.GroupAlgebraicSpace C (Spec (.of k)) hk
      (Space.terminalSpace C (Spec (.of k)) hk).obj
      (Space.terminalSpace C (Spec (.of k)) hk).property)
    (hAffine : Space.IsAffineHom C (Spec (.of k)) hk G.obj.X.hom)
    (hdiag : HasRepresentableDiagonal C (Spec (.of k)) hk (classifyingStack C hk G))
    (hfp : IsAlgebraicStack.{u, u} C (Spec (.of k)) hk (classifyingStack C hk G).val →
      Space.IsLocallyOfFinitePresentation C (Spec (.of k)) hk G.obj.X.hom)
    (hcov :
      ∃ (U : BigFppfOver C (Spec (.of k)) hk)
        (f : (schemeFibredCategory C (Spec (.of k)) hk U).val ⥤ᵇ
          (classifyingStack C hk G).val),
        IsRepresentableByAlgebraicSpaces C (Spec (.of k)) hk f ∧
          ∀ (V : BigFppfOver C (Spec (.of k)) hk)
            (y : BigFppfOver C V.left.1 V.left.2 ⥤ (classifyingStack C hk G).val.obj)
            (_hy : y ⋙ (classifyingStack C hk G).val.p = Over.map V.hom)
            (F : (BigFppfOver C V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
            (hF : IsAlgebraicSpace C V.left.1 V.left.2 F),
            Nonempty (StacksRepresentableCFG.EquivalenceOver
              (TwoFibreProductOver.fst (Over.map V.hom)
                (schemeFibredCategory C (Spec (.of k)) hk U).val.p
                (classifyingStack C hk G).val.p y f.toFunctor)
              (presheafOfCategories (F ⋙ typeToCat)).p) →
              (let g := (algebraicSpaceMap C (Spec (.of k)) hk V
                ((spacesOverSmallerBaseFunctor C V.left.1 (Spec (.of k)) V.left.2 hk
                  V.hom).obj ⟨F, hF⟩)).hom
               Space.IsSurjective C (Spec (.of k)) hk g ∧
                 Space.IsSmooth C (Spec (.of k)) hk g)) :
    Space.IsFiniteType C (Spec (.of k)) hk G.obj.X.hom :=
  ⟨Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation C (Spec (.of k)) hk
      (hfp ⟨(classifyingStack C hk G).isFiberedInGroupoids,
        ⟨isStack_quotientStack _, isStackInGroupoids_quotientStack _⟩, hdiag, hcov⟩),
    isQuasiCompact_of_isAffineHom C (Spec (.of k)) hk G.property
      (Space.terminalSpace C (Spec (.of k)) hk).property G.obj.X.hom hAffine⟩

end AlgebraicGeometry.Stack

end
