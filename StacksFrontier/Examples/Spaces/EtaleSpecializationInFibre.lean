module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegerShiftQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional

/-!
# A nontrivial specialization inside a fibre of an étale morphism of algebraic spaces

An étale, or more generally a locally quasi-finite, morphism of *schemes* admits no
specializations between points of a fibre (Stacks 06RT). For algebraic spaces this fails.
The counterexample of Stacks 06UK is the quotient of `U = Spec K[y, x_n : n ∈ ℤ]` by the
integer shift `y ↦ y - 1`, `x_n ↦ x_{n - 1}`, over a field `K` of characteristic zero: the
action is free — no nonidentity element fixes a point together with its residue field — so
`U → U/ℤ` is a surjective étale chart of an algebraic space, while the tail primes
`p_n = (x_n, x_{n + 1}, \ldots)` of `U` form a decreasing chain inside a single orbit. So
`p_{n + 1}` specializes to `p_n` and the two have the same image in `U/ℤ`.

## Main results

* `Stacks.Examples.EtaleSpecialization.exists_isEtale_specializes_pointsMap_eq`:
  **Stacks 06UK**, the counterexample.

## Implementation notes

The chain and the orbit both come from
`StacksFrontier/AlgebraicGeometry/Spaces/IntegerShiftQuotient.lean`, which builds the action and
its quotient. What is added here is the transport to the point spaces of Stacks 03BU: the
points of the chart's functor of points are identified with the points of `U` by
`AlgebraicGeometry.Space.schemePointsHomeomorph`, clause (1) of Stacks 03BX, and the equality
of images in the quotient is `AlgebraicGeometry.Space.Presentation.pointsRelation_iff`,
Stacks 03BW, applied to the presentation that the étale equivalence relation provides. The
witness of the relation is the copy of the chart inside the relation scheme indexed by the
generator of the action.

That the quotient is an algebraic space is
`AlgebraicGeometry.Space.isAlgebraicSpace_quotient_unconditional`, the algebraicity half of
**Stacks 02WW** for an étale equivalence relation on an arbitrary object of the site. It needs
no hypothesis: its one descent input is effective descent along the covering sieves of the site
at the monomorphisms locally of finite type, and that is a theorem,
`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft`. The older
`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf`, which routes the chart through the
property of Stacks 02W8 and so asks for a second, unproved descent input, is not used here.

## References

* [Stacks Project, Tag 06UK](https://stacks.math.columbia.edu/tag/06UK)
* [Stacks Project, Tag 06RT](https://stacks.math.columbia.edu/tag/06RT)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.IntegerShift CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Examples.EtaleSpecialization

attribute [local instance] AlgebraicGeometry.Space.pointTopology

variable (K : Type u) [Field K] (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of K)))

/-- The point of the functor of points of the chart `Spec K[y, x_n : n ∈ ℤ]` given by the
`n`-th tail prime, through the identification of the points of a represented presheaf with
the points of the representing scheme (clause (1) of Stacks 03BX). -/
def tailPoint (n : ℤ) :
    Space.points B (Spec (.of K)) hS (yoneda.obj (shiftChart K B hS)) :=
  (Space.schemePointsHomeomorph B (Spec (.of K)) hS (shiftChart K B hS)).symm
    (chartPoint K B hS n)

/-- The tail point of the chart's functor of points lies over the tail point of the chart. -/
theorem pointsToScheme_tailPoint (n : ℤ) :
    Space.pointsToScheme B (Spec (.of K)) hS (shiftChart K B hS) (tailPoint K B hS n) =
      chartPoint K B hS n :=
  (Space.schemePointsHomeomorph B (Spec (.of K)) hS (shiftChart K B hS)).apply_symm_apply _

/-- **Stacks 06UK.** Tail points at different indices are different points of the chart. -/
theorem tailPoint_injective : Function.Injective (tailPoint K B hS) := fun _ _ h ↦
  chartPoint_injective K B hS
    ((Space.schemePointsHomeomorph B (Spec (.of K)) hS
      (shiftChart K B hS)).symm.injective h)

/-- **Stacks 06UK.** A later tail point of the chart specializes to an earlier one. -/
theorem tailPoint_specializes_of_le {m n : ℤ} (h : m ≤ n) :
    tailPoint K B hS n ⤳ tailPoint K B hS m :=
  (chartPoint_specializes_of_le K B hS h).map
    (Space.schemePointsHomeomorph B (Spec (.of K)) hS (shiftChart K B hS)).symm.continuous

variable [CharZero K]

section Sheafify

variable [HasSheafify (BigFppfOver.topology B (Spec (.of K)) hS) (Type u)]

/-- The integer shift quotient is an algebraic space. -/
private theorem isAlgebraicSpace_shiftQuotient :
    IsAlgebraicSpace B (Spec (.of K)) hS (shiftQuotient K B hS) :=
  Space.isAlgebraicSpace_quotient_unconditional B (Spec (.of K)) hS
    (shiftRelationSource K B hS) (shiftRelationTarget K B hS)

/-- **Stacks 06UK.** Consecutive tail points of the chart have the same image in the
quotient: the copy of the chart inside the relation scheme indexed by the generator of the
action carries one to the other. -/
theorem pointsMap_shiftQuotientMap_tailPoint (n : ℤ) :
    Space.pointsMap B (Spec (.of K)) hS (yoneda.obj (shiftChart K B hS))
        (shiftQuotientMap K B hS) (tailPoint K B hS (n + 1)) =
      Space.pointsMap B (Spec (.of K)) hS (yoneda.obj (shiftChart K B hS))
        (shiftQuotientMap K B hS) (tailPoint K B hS n) := by
  have hQ := isAlgebraicSpace_shiftQuotient K B hS
  have hrel : ∃ r : Space.points B (Spec (.of K)) hS (yoneda.obj (shiftRelationObj K B hS)),
      Space.pointsMap B (Spec (.of K)) hS (yoneda.obj (shiftRelationObj K B hS))
          (yoneda.map (shiftRelationTarget K B hS)) r = tailPoint K B hS (n + 1) ∧
        Space.pointsMap B (Spec (.of K)) hS (yoneda.obj (shiftRelationObj K B hS))
          (yoneda.map (shiftRelationSource K B hS)) r = tailPoint K B hS n := by
    refine ⟨Space.pointsMap B (Spec (.of K)) hS (yoneda.obj (shiftChart K B hS))
      (yoneda.map (generatorSummand K B hS)) (tailPoint K B hS n), ?_, ?_⟩
    · refine (Space.schemePointsHomeomorph B (Spec (.of K)) hS
        (shiftChart K B hS)).injective ?_
      rw [Space.schemePointsHomeomorph_apply, Space.schemePointsHomeomorph_apply,
        Space.pointsToScheme_pointsMap, Space.pointsToScheme_pointsMap,
        pointsToScheme_tailPoint, pointsToScheme_tailPoint]
      exact toScheme_map_shiftRelationTarget_generatorSummand_chartPoint K B hS n
    · rw [← Space.pointsMap_comp_apply, ← Functor.map_comp,
        generatorSummand_comp_shiftRelationSource, CategoryTheory.Functor.map_id,
        Space.pointsMap_id, id_eq]
  exact (Space.Presentation.pointsRelation_iff
    (Space.quotientPresentation B (Spec (.of K)) hS (shiftRelationSource K B hS)
      (shiftRelationTarget K B hS) hQ) _ _).mp hrel

end Sheafify

/-- **Stacks 06UK.** There is an étale morphism of algebraic spaces `f : X ⟶ Y` and a
nontrivial specialization of points `x ⤳ x'` in `|X|` with `f x = f x'` in `|Y|`.

The witness is the chart `X = Spec K[y, x_n : n ∈ ℤ]` of its own quotient `Y = X/ℤ` by the
integer shift, at the tail points `x = p_1` and `x' = p_0`: the shift carries `p_0` to `p_1`,
so the two have the same image in `Y`, while `p_1 ⊂ p_0` gives the specialization.

That `Y` is an algebraic space is the algebraicity half of Stacks 02WW,
`AlgebraicGeometry.Space.isAlgebraicSpace_quotient_unconditional`, which is a theorem. -/
@[stacks 06UK "a specialization inside a fibre of an étale morphism of algebraic spaces"]
theorem exists_isEtale_specializes_pointsMap_eq :
    ∃ (X Y : (BigFppfOver B (Spec (.of K)) hS)ᵒᵖ ⥤ Type u)
      (_ : IsAlgebraicSpace B (Spec (.of K)) hS X)
      (_ : IsAlgebraicSpace B (Spec (.of K)) hS Y)
      (f : X ⟶ Y) (x x' : Space.points B (Spec (.of K)) hS X),
      Space.IsEtale B (Spec (.of K)) hS f ∧ x ≠ x' ∧ x ⤳ x' ∧
        Space.pointsMap B (Spec (.of K)) hS X f x =
          Space.pointsMap B (Spec (.of K)) hS X f x' := by
  have : HasSheafify (BigFppfOver.topology B (Spec (.of K)) hS) (Type u) :=
    BigFppfOver.hasSheafify_type B (Spec (.of K)) hS
  have hQ := isAlgebraicSpace_shiftQuotient K B hS
  refine ⟨yoneda.obj (shiftChart K B hS), shiftQuotient K B hS,
    isAlgebraicSpace_yoneda B (Spec (.of K)) hS (shiftChart K B hS), hQ,
    shiftQuotientMap K B hS, tailPoint K B hS 1, tailPoint K B hS 0,
    Space.isEtale_of_presheaf_etale B (Spec (.of K)) hS
      (Space.quotientMap_etale B (Spec (.of K)) hS (shiftRelationSource K B hS)
        (shiftRelationTarget K B hS)
        (Space.relativelyRepresentable_quotientMap_of_isAlgebraicSpace B (Spec (.of K)) hS
          (shiftRelationSource K B hS) (shiftRelationTarget K B hS) hQ)),
    fun h ↦ one_ne_zero (tailPoint_injective K B hS h),
    tailPoint_specializes_of_le K B hS (by norm_num), ?_⟩
  simpa using pointsMap_shiftQuotientMap_tailPoint K B hS 0

end Stacks.Examples.EtaleSpecialization

end
