module

public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.StableModelUniqueness
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.Terminal
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesStable
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.NodalSpecialFibre

/-!
# The stable contraction of a smooth curve is an isomorphism

Let `X` be a smooth proper curve over a field `k` with `H⁰(X, 𝒪_X) = k` and genus at least two.
Then `X` has no rational tail and no rational bridge (it is irreducible), so the identity of `X`
is a contraction to a stable curve in the sense of [Stacks, Tag 0E7Q], and by the uniqueness in
that lemma every such contraction `X ⟶ Y` is an isomorphism. This is the step "since the generic
fibre already is stable, it does not get changed by this procedure" of the proof of
[Stacks, Tag 0E8D].

## Main results

* `Stacks.Curves.StableModel.isStableContraction_id_of_smooth`: the identity of a smooth proper
  curve of genus at least two with `H⁰ = k` satisfies the conditions of Stacks 0E7Q.
* `Stacks.Curves.StableModel.isIso_of_isStableContraction_of_smooth`: every contraction of it to
  a stable curve is an isomorphism.

## References

* [Stacks Project, Tag 0E7Q](https://stacks.math.columbia.edu/tag/0E7Q)
* [Stacks Project, Tag 0E8D](https://stacks.math.columbia.edu/tag/0E8D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Curves.StableModel

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- **The identity of a smooth curve of genus at least two is a stable contraction.** The curve
is irreducible, being smooth and proper with `H⁰ = k`, so it has neither a rational tail nor a
rational bridge, and the identity is the empty chain of contractions of rational bridges
([Stacks, Tag 0E3Q]). -/
theorem isStableContraction_id_of_smooth (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (hdim : topologicalKrullDim X = 1)
    (hg : 2 ≤ genus f) : IsStableContraction f f (𝟙 X) := by
  have := irreducibleSpace_of_smooth_of_isIso_appTop k f inferInstance
  let : X.Over (Spec (.of k)) := ⟨f⟩
  have : Smooth (X ↘ Spec (.of k)) := ‹Smooth f›
  have hnod := Stacks.Curves.hasAtWorstNodalSingularities_of_smooth k X
  exact (IsIteratedContractionOfRationalBridges.identity (k := k) X f).isStableContraction hdim
    hnod (not_isRationalTail_of_irreducibleSpace k X) hg
    (fun C _ => not_isRationalBridge_of_irreducibleSpace k X C)

/-- **A contraction of a smooth curve of genus at least two to a stable curve is an
isomorphism**, by the uniqueness in [Stacks, Tag 0E7Q] compared with the identity. -/
theorem isIso_of_isStableContraction_of_smooth (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (hdim : topologicalKrullDim X = 1)
    (hg : 2 ≤ genus f) {gY : Y ⟶ Spec (.of k)} {c : X ⟶ Y} (hc : IsStableContraction f gY c) :
    IsIso c := by
  let : X.Over (Spec (.of k)) := ⟨f⟩
  have : Smooth (X ↘ Spec (.of k)) := ‹Smooth f›
  obtain ⟨e, he, -⟩ := existsUnique_iso_of_isStableContraction f hdim hg
    (Stacks.Curves.hasAtWorstNodalSingularities_of_smooth k X)
    (isStableContraction_id_of_smooth f hdim hg) hc
  rw [← he, Category.id_comp]
  infer_instance

end Stacks.Curves.StableModel

end
