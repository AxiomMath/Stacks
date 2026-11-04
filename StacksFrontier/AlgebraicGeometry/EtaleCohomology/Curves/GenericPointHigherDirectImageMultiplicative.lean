module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.MultiplicativeGroupTranscendenceDegreeOneVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MultiplicativeGroupEtaleOverField
import StacksCore.Tactic.StacksAttribute

/-!
# Vanishing of the higher direct images of `𝐆_m` along the generic point

Let `k` be an algebraically closed field, let `X` be an integral scheme whose function field
`K = k(X)` has transcendence degree one over `k` — a smooth curve over `k` is the source's
situation — and let `j : Spec K ⟶ X` be the inclusion of the generic point. Then

`R^q j_* 𝐆_{m,K} = 0` for every `q ≥ 1` (Stacks 03RJ).

## Main results

* `isZero_rightDerived_genericPointDirectImage_multiplicativeSheaf_of_trdeg_eq_one`:
  `R^q j_* 𝐆_{m,K} = 0` for every `q ≥ 1`.

## Implementation notes

The higher direct image is the sheafification of the presheaf `V ↦ H^q_étale(Spec K ×_X V, 𝐆_m)`
on `X_étale` (Stacks 03Q8), and the objects with affine source are a dense subsite, so it is
enough to kill that presheaf. Each base change `Spec K ×_X V` is étale over `Spec K`, hence a
disjoint union of spectra of finite separable extensions of `K` (Stacks 02GL), and the sections
of a sheaf over a coproduct are the product of the sections. That reduction is
`Stacks.EtaleCohomology.isZero_rightDerived_etaleAbelianDirectImage_multiplicativeSheaf_of_field`.
Over each summand the vanishing is Stacks 03RG, at a finite separable, hence algebraic, extension
of `K`: `Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_spec_of_isAlgebraic`.

This is not the source's proof, which computes the geometric stalks of `R^q j_* 𝐆_{m,K}` through
the strict henselisations of the local rings of `X` (Stacks 03Q9). Staying at the étale
neighbourhoods, where the base changes are already disjoint unions of spectra of finite separable
extensions, makes the passage to the limit unnecessary.

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

/-- **Stacks Project, Tag 03RJ.** Let `k` be an algebraically closed field, let `X` be an
integral scheme whose function field `K = k(X)` has transcendence degree one over `k`, and let
`j : Spec K ⟶ X` be the inclusion of the generic point. Then

`R^q j_* 𝐆_{m,K} = 0` for every `q ≥ 1`.

A smooth curve over `k` satisfies the hypotheses, by
`AlgebraicGeometry.trdeg_functionField_eq_one`, so this is more general than the tag. -/
@[stacks 03RJ, sga "4½ Arcata 3.3.2" "more general"]
theorem isZero_rightDerived_genericPointDirectImage_multiplicativeSheaf_of_trdeg_eq_one
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} [IsIntegral X]
    [Algebra k X.functionField] (hK : Algebra.trdeg k X.functionField = 1)
    (q : ℕ) (hq : 1 ≤ q) :
    IsZero (((etaleAbelianDirectImage.{u, u + 1} (genericPointInclusion X)).rightDerived q).obj
      (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec X.functionField))) :=
  isZero_rightDerived_etaleAbelianDirectImage_multiplicativeSheaf_of_field
    ↥X.functionField (genericPointInclusion X) q hq fun L _ _ _ _ ↦
      subsingleton_sheafH_multiplicativeSheaf_spec_of_isAlgebraic k ↥X.functionField hK L q hq

end Stacks.EtaleCohomology

end
