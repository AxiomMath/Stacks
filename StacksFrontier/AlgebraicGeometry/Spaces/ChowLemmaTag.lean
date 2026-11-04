module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ChowLemma.Main

/-!
# Stacks 088U, Chow's lemma for algebraic spaces

Let `f : X ⟶ Y` be a separated morphism of finite type of algebraic spaces over `S`, with `Y`
separated and Noetherian. Then there are a dense open subspace `U ⊆ X`, a `U`-admissible blowup
`π : X' ⟶ X` and an immersion `i : X' ⟶ ℙⁿ_Y` with `π ≫ f = i ≫ pr₁`.

The statement is proved, at exactly these hypotheses, as
`AlgebraicGeometry.Space.C1573.exists_isAdmissibleBlowup_isImmersion_projectiveSpace` in
`StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ChowLemma.Main`. This
file attaches the tag to it.

## References

* [Stacks Project, Tag 088U](https://stacks.math.columbia.edu/tag/088U)
-/

@[expose] public section

add_to_stacks 088U
  AlgebraicGeometry.Space.C1573.exists_isAdmissibleBlowup_isImmersion_projectiveSpace

end
