module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.FunctionFieldTranscendenceDegreeOne
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointHigherDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MultiplicativeGroupEtaleOverField
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.MultiplicativeGroupTranscendenceDegreeOneVanishing

/-!
# Vanishing of `R^q j_* 𝐆_m` along the generic point of a smooth curve

Let `k` be an algebraically closed field, `X` a smooth curve over `k`, `η` its generic point and
`j : η ⟶ X` the inclusion. Then `R^q j_* 𝐆_{m,η} = 0` for every `q ≥ 1` (Stacks 03RJ), with no
hypothesis carried.

## Main results

* `isZero_rightDerived_genericPointDirectImage_multiplicativeSheaf_smoothCurve`: for a smooth
  curve over an algebraically closed field, `R^q j_* 𝐆_{m,η} = 0` for every `q ≥ 1`.

## Implementation notes

The statement
`Stacks.EtaleCohomology.isZero_rightDerived_genericPointDirectImage_multiplicativeSheaf` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointHigherDirectImageVanishing`
carries the stalk computation (`h03Q9`) and the vanishing criterion (`h03RG`) as hypotheses. The
declaration here carries neither.

The proof does not go through the geometric stalks. The higher direct image `R^q j_* 𝐆_{m,η}` is
the sheafification of `V ↦ H^q_étale(η ×_X V, 𝐆_m)` on `X_étale` (Stacks 03Q8), and each
`η ×_X V` is étale over `η = Spec k(X)`, hence a disjoint union of spectra of finite separable
extensions of `k(X)` (Stacks 02GL). This reduction is
`Stacks.EtaleCohomology.isZero_rightDerived_etaleAbelianDirectImage_multiplicativeSheaf_of_field`.
What remains is the vanishing of `H^q_étale(Spec L, 𝐆_m)` for every finite separable extension
`L` of `k(X)`. Such an `L` is algebraic over `k(X)`, so it has transcendence degree one over `k`
(`Stacks.EtaleCohomology.trdeg_eq_one_of_isAlgebraic`, since `k(X)` has transcendence degree one
by `AlgebraicGeometry.trdeg_functionField_eq_one`), and then Stacks 03RG
(`Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_spec_of_trdeg_eq_one`)
gives the vanishing. The source applies Stacks 03RG in the same way, at the algebraic extension
`K^{sh}_{x̄}` of `k(X)`, after passing to the limit over the étale neighbourhoods. Working at
each étale neighbourhood before the limit means that limit is never needed.

Coefficients and universes are those of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointHigherDirectImageVanishing`:
abelian sheaves in `AddCommGrpCat.{u + 1}` for `X : Scheme.{u}`, with the Grothendieck abelian
structure pinned to that coefficient universe.

## References

* [Stacks Project, Tag 03RJ](https://stacks.math.columbia.edu/tag/03RJ)
* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
* [Stacks Project, Tag 02GL](https://stacks.math.columbia.edu/tag/02GL)
* [Stacks Project, Tag 03RG](https://stacks.math.columbia.edu/tag/03RG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- **Stacks Project, Tag 03RJ.** Let `k` be an algebraically closed field, `X` a smooth curve
over `k` with structure morphism `g`, `η = Spec k(X)` its generic point and `j : η ⟶ X` the
inclusion of the generic point. Then

`R^q j_* 𝐆_{m,η} = 0` for every `q ≥ 1`.

No hypothesis is carried. The higher direct image is killed on the étale neighbourhoods by
`Stacks.EtaleCohomology.isZero_rightDerived_etaleAbelianDirectImage_multiplicativeSheaf_of_field`,
which leaves the vanishing of `H^q_étale(Spec L, 𝐆_m)` at each finite separable extension `L` of
`k(X)`. That is Stacks 03RG, since `L` has transcendence degree one over `k`.

Smoothness is in the statement because the source assumes it. The proof does not use it: the
curve hypothesis is enough. -/
@[stacks 03RJ]
theorem isZero_rightDerived_genericPointDirectImage_multiplicativeSheaf_smoothCurve
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
    [IsCurve k g] [Smooth g] (q : ℕ) (hq : 1 ≤ q) :
    IsZero (((etaleAbelianDirectImage.{u, u + 1} (genericPointInclusion X)).rightDerived q).obj
      (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec X.functionField))) := by
  let := functionFieldAlgebra k g
  have hK := trdeg_functionField_eq_one k g
  refine isZero_rightDerived_etaleAbelianDirectImage_multiplicativeSheaf_of_field
    ↥X.functionField (genericPointInclusion X) q hq fun L _ _ _ _ ↦ ?_
  let : Algebra k L :=
    ((algebraMap X.functionField L).comp (algebraMap k X.functionField)).toAlgebra
  have : IsScalarTower k X.functionField L := .of_algebraMap_eq' rfl
  exact subsingleton_sheafH_multiplicativeSheaf_spec_of_trdeg_eq_one k L
    (trdeg_eq_one_of_isAlgebraic k X.functionField hK L) q hq

end Stacks.EtaleCohomology

end
