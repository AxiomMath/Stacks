module

public import StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.SheafCondition
public import StacksCore.Tactic.StacksAttribute

/-!
# The Koszul complex of a finite family of sections of the structure sheaf

Let `X` be a ringed space and let `f₁, …, f_r ∈ Γ(X, O_X)`. The Koszul complex
`K_•(O_X, f_•)` is the complex of sheaves of `O_X`-modules whose degree-`n` term is
`⋀^n_{O_X}(O_X^{⊕ r})` and whose differential is contraction by `(f₁, …, f_r)`. It is the
complex whose acyclicity governs Koszul-regularity and `H₁`-regularity of the family.

## References

* [Stacks Project, Tag 063A](https://stacks.math.columbia.edu/tag/063A)
* [Stacks Project, Tag 062L](https://stacks.math.columbia.edu/tag/062L)
-/

@[expose] public section

add_to_stacks 063A "the notation `K_•(O_X, f_•)` of the section on regular ideal sheaves: the
Koszul complex of Modules, Definition 17.24.2 (Tag 062L) for the structure sheaf of a ringed
space and a finite family of its global sections."
  Stacks.AlgebraicGeometry.SeqKoszul.sheafComplex

end
