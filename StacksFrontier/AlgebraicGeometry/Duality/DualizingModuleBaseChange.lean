module

public import StacksFrontier.AlgebraicGeometry.Different.DualizingModulesQuasi.BaseChange

/-!
# Base change for relative dualizing modules

Let `A → B` be a quasi-finite map of rings and `A → B' → B` a finite-open factorization of it, so
that the relative dualizing module is `ω_{B/A} = Hom_A(B', A) ⊗_{B'} B` (Tag 0BSZ). Given a further
ring map `A → A₁`, the ring maps `A₁ → A₁ ⊗[A] B' → A₁ ⊗[A] B` are again a finite-open
factorization, and there is a canonical base change map `ω_{B/A} ⟶ ω_{(A₁ ⊗[A] B)/A₁}` of
Tag 0BVB, `B`-linear for the `B`-action on the target obtained by restriction along
`B → A₁ ⊗[A] B`.

The mathematics lives in
`StacksFrontier.AlgebraicGeometry.Different.DualizingModulesQuasi.BaseChange`, which this module
re-exports: `Stacks.Discriminant.FiniteOpenFactorization.baseChangeAlgebra`, `…baseChange`,
the two spectral conditions, and `Stacks.Discriminant.dualizingModule.baseChange` together with
its pure-tensor formula, carrying `@[stacks 0BVB]`.

## References

* [Stacks Project, Tag 0BVB](https://stacks.math.columbia.edu/tag/0BVB)
* [Stacks Project, Tag 0BSZ](https://stacks.math.columbia.edu/tag/0BSZ)
-/
