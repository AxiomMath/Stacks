module

public import StacksFrontier.AlgebraicGeometry.CurveEulerBridge.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingDimensionDuality
public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.TopSectionsLinear
public import StacksFrontier.AlgebraicGeometry.InvertibleDual.FiniteLocallyFreeHomSection
import StacksCore.Tactic.StacksAttribute

/-!
# The duality of dimensions on a proper curve, at a vector bundle

Let `k` be a field, `X` a proper `k`-scheme of topological Krull dimension at most one and
`ω_X = H^{-1}(f^×(𝒪_{Spec k}))` the dualizing sheaf of [Stacks, Tag 0BS2]. For `ℰ` a sheaf of
`𝒪_X`-modules which is finite locally free of constant rank this file proves

  `dim_k H¹(X, ℰ) = dim_k H⁰(X, ℰ^∨ ⊗_{𝒪_X} ω_X)`,

the duality of dimensions of [Stacks, Tag 0BS6] clause (3) at `i = 1`, without the Gorenstein
and equidimensionality hypotheses of that tag.

## Main results

* `AlgebraicGeometry.finrank_cohomologyOverField_zero_dualTensorDualizingSheafOverField_eq_one`:
  `dim_k H⁰(X, ℰ^∨ ⊗ ω_X) = dim_k H¹(X, ℰ)` for `ℰ` finite locally free of constant rank.

## References

* [Stacks Project, Tag 0BS6](https://stacks.math.columbia.edu/tag/0BS6)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0BS3](https://stacks.math.columbia.edu/tag/0BS3)
* [Stacks Project, Tag 0882](https://stacks.math.columbia.edu/tag/0882)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- `dim_k H⁰(X, ℰ^∨ ⊗ ω_X) = dim_k H¹(X, ℰ)` for a sheaf of `𝒪_X`-modules `ℰ` which is finite
locally free of constant rank on a proper scheme `X` of dimension at most one over a field `k`,
with `ω_X = H^{-1}(f^×(𝒪_{Spec k}))` the dualizing sheaf of [Stacks, Tag 0BS2]: the duality of
dimensions of [Stacks, Tag 0BS6], clause (3), at `i = 1`. -/
public theorem finrank_cohomologyOverField_zero_dualTensorDualizingSheafOverField_eq_one
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    Module.finrank k (cohomologyOverField k f
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨X.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj)
                (forget₂ CommRingCat RingCat) (X.ringCatSheaf.property)⟩).obj
            ((Stacks.SheafOfModules.dualSheaf X.sheaf.obj X.ringCatSheaf.property E))).obj
          ((Stacks.Duality.dualizingSheafOverField f)))) 0) =
      Module.finrank k (cohomologyOverField k f E 1) := by
  let := Scheme.Modules.linearOverBase f
  let : Functor.Linear k (globalSectionsOver f) := globalSectionsOver_linear_linearOverBase f
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : SheafOfModules.IsFiniteLocallyFree.{u, u, u} E :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E r
  let : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k f E r
  refine Eq.trans ?_ (finrank_hom_dualizingSheafOverField_eq_finrank_cohomologyOverField_one f
    hdim E (Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E))
  refine Eq.trans ?_ (finrank_hom_eq_finrank_globalSectionsOver_sheafHom f E
    (Stacks.Duality.dualizingSheafOverField f)).symm
  refine Eq.trans ?_ (cohomologyOverFieldZeroLinearEquivGlobalSectionsOver f _).finrank_eq
  exact (((cohomologyOverFieldFunctor k f 0).mapIso
    (Stacks.SheafOfModules.Scheme.dualTensorIsoSheafHomOfRank E
      (Stacks.Duality.dualizingSheafOverField f) r)).toLinearEquiv).finrank_eq

end AlgebraicGeometry

end
