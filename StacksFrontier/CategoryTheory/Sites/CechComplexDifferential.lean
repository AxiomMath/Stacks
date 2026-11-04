module

public import StacksFrontier.CategoryTheory.Sites.CechComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.CechGaps.Decode
public import StacksCore.Tactic.StacksAttribute

/-!
# The formula for the Čech differential

Let `𝒰 : U = ⋃ᵢ Uᵢ` be an open covering of a topological space and `F` an abelian presheaf.
The Čech complex `Č^•(𝒰, F)` has degree `p` term `∏_{i₀ … i_p} F(U_{i₀ … i_p})` and
differential given, on a cochain `s`, by the alternating sum of restrictions
`d(s)_{i₀ … i_{p+1}} = ∑_{j=0}^{p+1} (-1)ʲ s_{i₀ … î_j … i_{p+1}}|_{U_{i₀ … i_{p+1}}}`.

Here the Čech complex is `CategoryTheory.cechComplexFunctor`, the alternating coface map complex
of a cosimplicial object built from formal coproducts. The formula holds for it in two forms,
writing `y ∘ Fin.succAbove j` for the tuple `i₀ … î_j … i_{p+1}` obtained by omitting the `j`-th
index of `y = (i₀, …, i_{p+1})`:

* `Stacks.CategoryTheory.CechComplex.d_comp_π`: for a presheaf `P : Cᵒᵖ ⥤ A` with values in a
  preadditive category, on a category `C` with finite products, the component of the
  differential at a tuple `y : Fin (p + 2) → ι` is
  `∑ⱼ (-1)ʲ • (π_{y ∘ Fin.succAbove j} ≫ P.map (restriction))`, an identity of morphisms;
  for `C = Opens X` the products of opens are their intersections
  (`Stacks.CategoryTheory.CechComplex.inter_eq_iInf`).
* `Stacks.CechGaps.cech_d_apply`: for an abelian presheaf on a topological space, the same
  formula evaluated on a cochain `s`, which is the displayed equation literally.

## References

* [Stacks Project, Equation 01EE](https://stacks.math.columbia.edu/tag/01EE)
-/

@[expose] public section

add_to_stacks 01EE "the components of the Čech differential, for a presheaf with values in a
  preadditive category on a category with finite products"
  Stacks.CategoryTheory.CechComplex.d_comp_π

add_to_stacks 01EE "the Čech differential evaluated on a cochain, for an abelian presheaf on a
  topological space" Stacks.CechGaps.cech_d_apply
