module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FibreProduct.AffinePushout
public import StacksFrontier.AlgebraicGeometry.Crystalline.FibreProduct.AffineChart
public import StacksFrontier.AlgebraicGeometry.Crystalline.FibreProduct.Gluing
public import StacksFrontier.AlgebraicGeometry.Crystalline.FibreProduct.Existence

/-!
# Fibre products of divided power schemes

Divided power schemes have fibre products, the underlying scheme of a divided power fibre product
is a closed subscheme of the ordinary fibre product, and its closed fibre is the fibre product of
the closed fibres ([Stacks Project, Tag 07ME](https://stacks.math.columbia.edu/tag/07ME)).
This file re-exports the parts of the construction: the affine pushout comparisons and
localizations (`FibreProduct.AffinePushout`), open subschemes and affine charts
(`FibreProduct.AffineChart`), the gluing and its universal property (`FibreProduct.Gluing`), and
the main results (`FibreProduct.Existence`).
-/
