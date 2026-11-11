module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyTranslate
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionDominant

/-!
# A general line of projective transformations moves `X` to meet `Y` properly

Let `V` be a vector space of dimension `n + 1` over an algebraically closed field `k`, and let
`X, Y` be closed subvarieties of `𝐏(V)` which intersect properly, with `X ≠ 𝐏(V)` and
`X ∩ Y ≠ ∅`. For a general line `ℓ` of the parameter space `𝐏 = 𝐏((End V)ᵛ)` through `[id_V]`,
every `[g] ∈ ℓ` satisfies `X ⊆ U(g)`, and then `g(X) = r_g(X)` is a closed subvariety of `𝐏(V)`
which intersects `Y` properly in the sense of `AlgebraicGeometry.IntersectProperly` (Tag 0AZQ).

## Main results

* `…exists_isOpen_forall_closedPoint_line_subset_endDomain_intersectProperly`:
  **Tag 0B1S**, both clauses along a general line through `[id_V]`, clause (2) stated with
  `AlgebraicGeometry.IntersectProperly` itself.

## Implementation notes

**"For a general line".** There is a nonempty Zariski open subset `U` of `𝐏` such that every
closed point `q ∈ U` lies, together with `[id_V]`, on a line `ℓ ⊆ 𝐏` along which both clauses
hold. For `q ≠ [id_V]` that line is the unique line through `[id_V]` and `q`, and projection from
`[id_V]` is open, so the lines obtained form a nonempty open subset of the space of lines through
`[id_V]`: this is the source's "general line", read as in Tag 0B2T. A line is a
`AlgebraicGeometry.ProjectiveSpaceOfModule.linearSubspace` cut out by a submodule of corank two.

**Points and representatives.** The points of `ℓ` the source speaks of are the classes `[g]` of
nonzero endomorphisms, which are the closed points of `𝐏`; the clauses are asserted for every
representative `g` of such a class.

**Clause (2).** For `X ⊆ U(g)` the image `r_g(X)` is closed
(`AlgebraicGeometry.ProjectiveSpaceOfModule.isClosed_endProjectionImage`) and irreducible
(`AlgebraicGeometry.ProjectiveSpaceOfModule.isIrreducible_endProjectionImage`), so it is a closed
subvariety `W` of `𝐏(V)`, and the conclusion is `IntersectProperly W Y` for that `W`.

The proof is
`…ProjectiveSpaceOfModule.exists_isOpen_forall_closedPoint_line_isGood_of_intersectProperly`,
which states clause (2) as the dimension criterion on the image set, together with
`AlgebraicGeometry.ProjectiveSpaceOfModule.isGoodEndomorphism_iff_intersectProperly`.

## References

* [Stacks Project, Tag 0B1S](https://stacks.math.columbia.edu/tag/0B1S)
* [Stacks Project, Tag 0B2T](https://stacks.math.columbia.edu/tag/0B2T)
* [Stacks Project, Tag 0AZQ](https://stacks.math.columbia.edu/tag/0AZQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V] [IsAlgClosed k]
  [FiniteDimensional k V] [Nontrivial V]

/-- **Stacks Project, Tag 0B1S.** Let `X, Y` be closed subvarieties of `𝐏(V)` which intersect
properly, with `X ≠ 𝐏(V)` and `X ∩ Y ≠ ∅`. Then for a general line `ℓ ⊆ 𝐏 = 𝐏((End V)ᵛ)` with
`[id_V] ∈ ℓ` — that is, for the line through `[id_V]` and any closed point of a nonempty Zariski
open subset of `𝐏` — every representative `g` of every closed point `[g]` of `ℓ` satisfies

1. `X ⊆ U(g)`, and
2. `g(X) = r_g(X)` is a closed subvariety `W` of `𝐏(V)` which intersects `Y` properly. -/
@[stacks 0B1S "both clauses (1) X ⊆ U(g) and (2) g(X) intersects Y properly, for every [g] \
on a general line through [id_V], at the source's hypotheses; 'general' means: there is a \
nonempty Zariski open subset of 𝐏 = 𝐏((End V)ᵛ) each of whose closed points lies with [id_V] \
on such a line (as in Tag 0B2T); clause (2) is IntersectProperly (Tag 0AZQ) of the closed \
subvariety r_g(X) with Y"]
public theorem exists_isOpen_forall_closedPoint_line_subset_endDomain_intersectProperly
    (X Y : IrreducibleCloseds (projectiveSpaceOfModule k V)) (hXY : IntersectProperly X Y)
    (hXne : (X : Set (projectiveSpaceOfModule k V)) ≠ Set.univ)
    (hXYne : ((X : Set (projectiveSpaceOfModule k V)) ∩
      (Y : Set (projectiveSpaceOfModule k V))).Nonempty) :
    ∃ U : Set (projectiveSpaceOfModule k (ParameterModule k V)), IsOpen U ∧ U.Nonempty ∧
      ∀ q ∈ U, IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V))) →
        ∃ L : Submodule k (ParameterModule k V),
          Module.finrank k (ParameterModule k V ⧸ L) = 2 ∧
          identityParameterPoint k V ∈ linearSubspace k (ParameterModule k V) L ∧
          q ∈ linearSubspace k (ParameterModule k V) L ∧
          ∀ p : ClosedPoints k (ParameterModule k V),
            (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈
              linearSubspace k (ParameterModule k V) L →
            ∀ g : V →ₗ[k] V, RepresentsParameterPoint k V p g →
              (X : Set (projectiveSpaceOfModule k V)) ⊆
                  (endDomain k V g : Set (projectiveSpaceOfModule k V)) ∧
                ∃ W : IrreducibleCloseds (projectiveSpaceOfModule k V),
                  (W : Set (projectiveSpaceOfModule k V)) =
                      endProjectionImage k V g (X : Set (projectiveSpaceOfModule k V)) ∧
                    IntersectProperly W Y := by
  obtain ⟨U, hUo, hUne, hU⟩ :=
    exists_isOpen_forall_closedPoint_line_isGood_of_intersectProperly k V X Y hXY hXne hXYne
  refine ⟨U, hUo, hUne, fun q hq hqc => ?_⟩
  obtain ⟨L, hL2, hidL, hqL, hgood⟩ := hU q hq hqc
  refine ⟨L, hL2, hidL, hqL, fun p hpL g hg => ?_⟩
  have hG := hgood p hpL g hg
  have hdom : (X : Set (projectiveSpaceOfModule k V)) ⊆
      (endDomain k V g : Set (projectiveSpaceOfModule k V)) := hG.1
  let W : IrreducibleCloseds (projectiveSpaceOfModule k V) :=
    ⟨endProjectionImage k V g X, isIrreducible_endProjectionImage k V g hdom X.isIrreducible',
      isClosed_endProjectionImage k V g X.isClosed' hdom⟩
  exact ⟨hdom, W, rfl, ((isGoodEndomorphism_iff_intersectProperly k V X Y W g rfl).mp hG).2⟩

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
