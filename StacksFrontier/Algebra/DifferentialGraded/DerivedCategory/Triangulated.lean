module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DGA.Octahedron

/-!
# The homotopy category of differential graded modules is triangulated

For a differential graded algebra `(A, d)` over a commutative ring `R`, the homotopy category
`K(A, d)` of right differential graded `A`-modules satisfies the octahedron axiom, so it is a
triangulated category.

That is `DifferentialGradedModule.instIsTriangulatedHomotopyCategory` of
`StacksDraft.Ch22.Sec10.Tag09KI`, proved there from the octahedron of two composable
homomorphisms: every object of `K(A, d)` is the class of a differential graded module and every
morphism the class of a homomorphism, so every composable pair is isomorphic to one for which the
cone octahedron supplies the data the axiom asks for. This file records that declaration as the
formalization of Tag 09KJ rather than proving it a second time.

## References

* [Stacks Project, Tag 09KJ](https://stacks.math.columbia.edu/tag/09KJ)
-/

@[expose] public section

add_to_stacks 09KJ "the homotopy category is triangulated"
  DifferentialGradedModule.instIsTriangulatedHomotopyCategory

end
