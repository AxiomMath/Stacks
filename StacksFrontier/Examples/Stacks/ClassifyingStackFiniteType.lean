module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.TrivialActionAlgebraicIff
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackRepresentableDiagonal
public import StacksFrontier.Examples.Stacks.ClassifyingStackSmoothCovering

/-!
# An affine group with a smooth classifying-stack covering is of finite type (Stacks 04AH)

Let `k` be a field and let `G` be an affine group scheme over `k`. If the classifying stack
`[Spec(k)/G]` admits a smooth surjective covering by a scheme, then `G` is of finite type
over `k`.

## Main results

* `AlgebraicGeometry.Stack.isFiniteType_classifyingStack_of_smoothSchemeCovering`:
  **Stacks 04AH**.

## Implementation notes

The classifying stack, the meaning of "affine group scheme over `k`" and the covering hypothesis
are those of `StacksFrontier.Examples.Stacks.ClassifyingStackSmoothCovering`. The covering is the
third clause of **Stacks 026O**; the other two hold for every quotient stack. The diagonal of a
quotient stack is representable by algebraic spaces by **Stacks 04WZ**
(`AlgebraicGeometry.Stack.hasRepresentableDiagonal_quotientStack`), so the classifying stack is
an algebraic stack, and the half of **Stacks 06PL** going from algebraicity of `[B/G]` to
flatness and local finite presentation of `G`,
`isFlat_and_isLocallyOfFinitePresentation_of_isAlgebraicStack_trivialAction`, makes `G`
locally of finite presentation over `k`. These are the two inputs
`AlgebraicGeometry.Stack.isFiniteType_of_smoothSchemeCovering_classifyingStack` takes; that
theorem gives local finite type from local finite presentation and quasi-compactness from
affineness. Both inputs are theorems of the library, so the statement below assumes nothing
beyond the source's data: the field, the affine group and the covering.

The source's argument is the discussion before the lemma: it chooses a `k`-point of a nonempty
smooth scheme over the covering, writes `G` as a base change of `U ×_[Spec(k)/G] U ⟶ U ×_k U`, and
concludes local finite type from smoothness of the projections (Stacks 01T8). Here local finite
type comes from Stacks 06PL instead; the statement is the same.

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

variable {k : Type u} [Field k] (C : BigFppfSite.{u})
  (hk : C.Contains (Spec (.of k)))

/-- **Stacks 04AH.** Let `k` be a field and let `G` be an affine group scheme over `k`. If the
classifying stack `[Spec(k)/G]` has a smooth surjective covering by a scheme, then `G` is of
finite type over `k`.

The covering hypothesis is the third clause of Stacks 026O for the classifying stack. By
Stacks 04WZ the classifying stack is then algebraic, and by the half of Stacks 06PL going from
algebraicity to flatness and local finite presentation, the group is locally of finite
presentation over `k`. -/
@[stacks 04AH]
theorem isFiniteType_classifyingStack_of_smoothSchemeCovering
    (G : Space.GroupAlgebraicSpace C (Spec (.of k)) hk
      (Space.terminalSpace C (Spec (.of k)) hk).obj
      (Space.terminalSpace C (Spec (.of k)) hk).property)
    (hAffine : Space.IsAffineHom C (Spec (.of k)) hk G.obj.X.hom)
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
    Space.IsFiniteType C (Spec (.of k)) hk G.obj.X.hom := by
  have hdiag : HasRepresentableDiagonal C (Spec (.of k)) hk (classifyingStack C hk G) := by
    let : ModObj G.obj.X (𝟙_ (Over (Space.terminalSpace C (Spec (.of k)) hk).obj)) :=
      ModObj.trivialAction _ _
    exact hasRepresentableDiagonal_quotientStack
      (Space.groupoidOfAction (Space.terminalSpace C (Spec (.of k)) hk) G.obj.X
        (𝟙_ (Over (Space.terminalSpace C (Spec (.of k)) hk).obj)) G.property
        (Space.terminalSpace C (Spec (.of k)) hk).property).groupoid
  -- The trivial action of the classifying stack and the one of Stacks 06PL are two module
  -- structures on a terminal object, hence equal.
  have hm : ∀ m₁ m₂ : ModObj G.obj.X (𝟙_ (Over (Space.terminalSpace C (Spec (.of k)) hk).obj)),
      m₁ = m₂ := by
    intro m₁ m₂
    obtain ⟨s₁, -, -⟩ := m₁
    obtain ⟨s₂, -, -⟩ := m₂
    obtain rfl : s₁ = s₂ := toUnit_unique s₁ s₂
    rfl
  have hfp : ∀ [m : ModObj G.obj.X (𝟙_ (Over (Space.terminalSpace C (Spec (.of k)) hk).obj))],
      IsAlgebraicStack.{u, u} C (Spec (.of k)) hk
        (quotientStack (Space.groupoidOfAction (Space.terminalSpace C (Spec (.of k)) hk) G.obj.X
          (𝟙_ (Over (Space.terminalSpace C (Spec (.of k)) hk).obj)) G.property
          (Space.terminalSpace C (Spec (.of k)) hk).property).groupoid) →
      Space.IsLocallyOfFinitePresentation C (Spec (.of k)) hk G.obj.X.hom := by
    intro m halg
    obtain rfl := hm m (Space.modObjTensorUnit G.obj.X)
    exact (isFlat_and_isLocallyOfFinitePresentation_of_isAlgebraicStack_trivialAction.{u, u}
      (Space.terminalSpace C (Spec (.of k)) hk) G.obj.X G.property
      (Space.groupoidOfAction (Space.terminalSpace C (Spec (.of k)) hk) G.obj.X
        (𝟙_ (Over (Space.terminalSpace C (Spec (.of k)) hk).obj)) G.property
        (Space.terminalSpace C (Spec (.of k)) hk).property) halg).2
  exact isFiniteType_of_smoothSchemeCovering_classifyingStack C hk G hAffine hdiag
    (fun halg => hfp (m := ModObj.trivialAction _ _) halg) hcov

end AlgebraicGeometry.Stack

end
