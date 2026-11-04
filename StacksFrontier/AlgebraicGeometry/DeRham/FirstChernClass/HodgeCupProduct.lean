module

public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.HodgeCupProduct.Construction
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.HodgeCupProduct.GradedPieceShift
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.HodgeCupProduct.AbelianShift
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.HodgeCupProduct.GradedPieceCup

/-!
# The cup product on Hodge cohomology

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space `X`, with
relative de Rham complex `Ω^•_{𝒪_X/A}`. The cup product of Cohomology, Section 0FKU along the
wedge product `Ω^p ⊗_A Ω^q ⟶ Ω^{p + q}` of Tag 0FM2, the three sheaves placed in degree `0`, is
the cup product on Hodge cohomology (Tag 0FM4)

`∪ : H^i(X, Ω^p) × H^j(X, Ω^q) ⟶ H^{i + j}(X, Ω^{p + q})`.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.hodgeSingle`: the sheaf `Ω^p` placed in degree `0`.
* `AlgebraicGeometry.SheafOfModules.hodgeSingleWedge`: the wedge product
  `Tot(Ω^p[0] ⊗_A Ω^q[0]) ⟶ Ω^{p + q}[0]`.
* `AlgebraicGeometry.SheafOfModules.hodgeCup`: **the cup product on Hodge cohomology**.

## References

* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0FM4](https://stacks.math.columbia.edu/tag/0FM4)
* [Stacks Project, Tag 0FM2](https://stacks.math.columbia.edu/tag/0FM2)
-/
