module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.FiniteCoverKilling
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.IntegralCoverVanishing
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 09ZD: the affine analogue of proper base change

Let `X` be an affine scheme.

1. There is an integral surjective morphism `X' ⟶ X` such that `H^q_ét(Z', M) = 0` for every
   closed subscheme `Z' ⊂ X'`, every finite abelian group `M` and every `q ≥ 1`:
   `Stacks.EtaleCohomology.exists_isIntegralHom_surjective_forall_subsingleton_H`.
2. For every closed subscheme `Z ⊂ X`, finite abelian group `M`, `q ≥ 1` and
   `ξ ∈ H^q_ét(Z, M)` there is a finite surjective morphism `X' ⟶ X` of finite presentation such
   that `ξ` pulls back to zero in `H^q_ét(X' ×_X Z, M)`:
   `Stacks.EtaleCohomology.exists_isFinite_surjective_restriction_constantSheaf_eq_zero`.

Both parts are already proved, with the source's hypotheses and the source's proof, in
`IntegralCoverVanishing.lean` and `FiniteCoverKilling.lean`; only the tag registration is new
here, so that no second provider of the same statements is created.

## References

* [Stacks Project, Tag 09ZD](https://stacks.math.columbia.edu/tag/09ZD)
-/

add_to_stacks 09ZD "part (1): an affine scheme has an integral surjective cover X' → X such that
  every closed subscheme Z' of X' has H^q_ét(Z', M) = 0 for every finite abelian group M and
  every q ≥ 1" Stacks.EtaleCohomology.exists_isIntegralHom_surjective_forall_subsingleton_H

add_to_stacks 09ZD "part (2): for a closed subscheme Z of an affine X, a finite abelian group M,
  q ≥ 1 and ξ ∈ H^q_ét(Z, M), some finite surjective X' → X of finite presentation makes ξ pull
  back to zero in H^q_ét(X' ×_X Z, M)"
  Stacks.EtaleCohomology.exists_isFinite_surjective_restriction_constantSheaf_eq_zero
