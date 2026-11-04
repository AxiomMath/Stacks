module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietorisAndHom.HomComplexEvaluation
public import StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.TensorTotalComplex
public import StacksCore.Tactic.StacksAttribute

/-!
# Evaluation for internal Hom complexes of modules on a ringed space

Let `(X, O_X)` be a ringed space and let `K`, `L` and `M` be complexes of `O_X`-modules.
Evaluation gives a canonical morphism from the total tensor product of the internal Hom complex
from `L` to `M` with `K` to the internal Hom complex from the internal Hom complex from `K` to
`L` to `M`, and this morphism is functorial in all three complexes.

Nothing is built here. A topological space with a sheaf of commutative rings *is* a ringed site,
namely the site of its opens with the open-cover topology, and
`Stacks.Cohomology.evaluationConstruction` already supplies the evaluation morphism and its
naturality for a ringed site. The two declarations below read those off along
`Stacks.SheafOfModules.ringedSite`, in the vocabulary of
`StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.TensorTotalComplex`.

## Main definitions

* `Stacks.SheafOfModules.evaluationConstruction`: the canonical evaluation morphisms, specified
  by the signed evaluation formula on homogeneous local pure tensors.
* `Stacks.SheafOfModules.evaluateAndMore`: the canonical evaluation morphism attached to three
  complexes.

## Main results

* `Stacks.SheafOfModules.evaluateAndMore_natural` (Stacks 0A8P): evaluation is natural in `K`,
  contranatural in `L` and natural in `M`.

## Implementation notes

`ringedSite` is an abbreviation, so `(ringedSite Rc).ringSheaf` is `structureSheaf Rc` and
`SheafOfModules (ringedSite Rc).ringSheaf` is `StructureSheafModules Rc`; and the space-level
`sheafHomComplex`, `tensorTotal`, `tensorTotalSection` and `applyHomSection` are by definition
the site-level ones along `ringedSite` and `ofSite`. So no comparison layer is needed between
the two settings, and neither declaration below requires a transparency option: both are the
site-level term, type-checked against the space-level statement.

## References

* [Stacks Project, Tag 0A8P](https://stacks.math.columbia.edu/tag/0A8P)
* [Stacks Project, Tag 0A92](https://stacks.math.columbia.edu/tag/0A92)
* [Stacks Project, Tag 0A60](https://stacks.math.columbia.edu/tag/0A60)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.SheafOfModules

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)

/-- **Stacks 0A8P.** The canonical evaluation morphisms for internal Hom complexes of modules
on a ringed space, specified on homogeneous local pure tensors by the signed formula
`φ ⊗ k ↦ (-1)^(r + (-a) * r) (ψ ↦ φ (ψ k))`. It is the evaluation morphism of the ringed site
of opens of the space. -/
@[stacks 0A8P "canonical evaluation morphism"]
noncomputable def evaluationConstruction : EvaluationConstruction Rc where
  evaluate K L M := Cohomology.evaluation (ringedSite Rc) K L M
  evaluate_tmul K L M U t r s a p hra hap φ k ψ :=
    (Cohomology.evaluationConstruction (ringedSite Rc)).evaluate_tmul
      K L M U t r s a p hra hap φ k ψ

/-- The canonical evaluation morphism from the total tensor product of the internal Hom complex
from `L` to `M` with `K` to the iterated internal Hom complex. -/
noncomputable abbrev evaluateAndMore (K L M : CochainComplex (StructureSheafModules Rc) ℤ) :
    tensorTotal Rc (sheafHomComplex Rc L M).obj K ⟶
      (sheafHomComplex Rc (sheafHomComplex Rc K L).obj M).obj :=
  (evaluationConstruction Rc).evaluate K L M

/-- **Stacks 0A8P.** Evaluation is covariant in `K` and `M` and contravariant in `L`. -/
@[stacks 0A8P "functoriality in all three complexes"]
theorem evaluateAndMore_natural
    {K K' L L' M M' : CochainComplex (StructureSheafModules Rc) ℤ}
    (k : K ⟶ K') (l : L' ⟶ L) (m : M ⟶ M') :
    tensorTotalMap Rc (sheafHomComplexMap Rc l m) k ≫
        evaluateAndMore Rc K' L' M' =
      evaluateAndMore Rc K L M ≫
        sheafHomComplexMap Rc (sheafHomComplexMap Rc k l) m :=
  Cohomology.evaluation_natural (ringedSite Rc) k l m

end Stacks.SheafOfModules

end
