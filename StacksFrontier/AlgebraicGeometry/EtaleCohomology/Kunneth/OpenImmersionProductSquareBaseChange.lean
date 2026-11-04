module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.HypercohomologyIsoOfProperFactorProof
import StacksCore.Tactic.StacksAttribute

/-!
# Base change for the product square of an open immersion over a field (Stacks 0F1H)

Let `K` be a field, `j : U ⟶ X` an open immersion of schemes of finite type over `K`, and `Y` a
scheme of finite type over `K`. In the diagram
```
Y ×_K X  ←-h-  Y ×_K U
   |q              |p
   X     ←-j-      U
```
the base change map `q⁻¹Rj_*𝓕 ⟶ Rh_*p⁻¹𝓕` is an isomorphism for every abelian sheaf `𝓕` on
`U_étale` whose stalks are torsion of orders invertible in `K` ([Stacks, Tag 0F1H]).

## Implementation notes

The proof, `isIso_baseChangeMap_of_hypercohomologyIsoOfProperFactor`, runs the torsion
reduction, the induction on `dim(X) + dim(Y)`, the reductions to affine `X` and `Y` and to a
projective `Y`, the passage to `K^{sep}` and [Stacks, Tag 0F1G], given the Künneth computation
of the last paragraph, which is `hypercohomologyIsoOfProperFactor` ([Stacks, Tag 0F14]).

## Main results

* `Stacks.EtaleCohomology.OpenImmersionProductSquare.isIso_baseChangeMap`: the base change map
  `q⁻¹Rj_*𝓕 ⟶ Rh_*p⁻¹𝓕` is an isomorphism.

## References

* [Stacks Project, Tag 0F1H](https://stacks.math.columbia.edu/tag/0F1H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.OpenImmersionProductSquare

/-- Let `K` be a field, `j : U ⟶ X` an open immersion of schemes of finite type over `K` and `Y`
a scheme of finite type over `K`. For every abelian sheaf `𝓕` on `U_étale` whose stalks are
torsion of orders invertible in `K`, the base change map `q⁻¹Rj_*𝓕 ⟶ Rh_*p⁻¹𝓕` of the square
```
Y ×_K X  ←-h-  Y ×_K U
   |q              |p
   X     ←-j-      U
```
is an isomorphism (in `D⁺((Y ×_K X)_étale)`, `𝓕` placed in degree zero). -/
@[stacks 0F1H]
theorem isIso_baseChangeMap {K : Type u} [Field K] {X U Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) (sU : U ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K))
    (j : U ⟶ X) [IsOpenImmersion j] (hj : j ≫ sX = sU) [LocallyOfFiniteType sX] [QuasiCompact sX]
    [LocallyOfFiniteType sU] [QuasiCompact sU] [LocallyOfFiniteType sY] [QuasiCompact sY]
    (𝓕 : Sheaf (smallEtaleTopology U) Ab.{u + 1})
    (h𝓕 : ∀ (t : GeometricPoint U) (a : (smallEtaleStalkAb t.hom).obj 𝓕),
      ∃ n : ℕ, 0 < n ∧ IsUnit ((n : ℤ) : K) ∧ n • a = 0) :
    IsIso (baseChangeMap sX sU sY j hj 𝓕) :=
  isIso_baseChangeMap_of_hypercohomologyIsoOfProperFactor sX sU sY j hj
    hypercohomologyIsoOfProperFactor 𝓕 h𝓕

end Stacks.EtaleCohomology.OpenImmersionProductSquare

end
