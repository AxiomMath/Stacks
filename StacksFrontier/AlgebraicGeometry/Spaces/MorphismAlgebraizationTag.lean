module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismAlgebraization

/-!
# Grothendieck's algebraization of morphisms of algebraic spaces (Stacks 0A4Z)

Let `A` be a Noetherian ring complete with respect to an ideal `I`, `S = Spec A`,
`S_n = Spec(A / I^{n+1})`, and `X`, `Y` algebraic spaces over `S` with `X ⟶ S` proper and
`Y ⟶ S` separated of finite type.  A compatible system of morphisms `g_n : X_n ⟶ Y_n` over the
`S_n` between the adic fibres is the system of adic fibres of a unique morphism `g : X ⟶ Y` over
`S`.  This is `AlgebraicGeometry.Space.existsUnique_adicFibreMap_eq`
(`StacksFrontier/AlgebraicGeometry/Spaces/MorphismAlgebraization.lean`), registered here.

The index `n` stands for the source's `n + 1`: `X 0 = X_1`, `S 0 = S_1`.

## References

* [Stacks Project, Tag 0A4Z](https://stacks.math.columbia.edu/tag/0A4Z)
-/

add_to_stacks 0A4Z AlgebraicGeometry.Space.existsUnique_adicFibreMap_eq
