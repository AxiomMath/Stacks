module

public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.Functoriality.AffineChartMap
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.Functoriality.ChartGluing
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.Functoriality.ConormalAlgebraHom

/-!
# Functoriality of the conormal algebra

The canonical morphism `f^* 𝒞_{Z'/X',*} ⟶ 𝒞_{Z/X,*}` of conormal graded algebras induced by a
commutative square of schemes with immersions (Stacks Tag 0634) is split over three files:
`Functoriality.AffineChartMap` (the affine charts of the square and the chart-level map of
associated graded algebras), `Functoriality.ChartGluing` (the chart maps on sections and their
compatibility on overlaps) and `Functoriality.ConormalAlgebraHom` (morphisms of conormal
algebras over the square, their affine characterisation, and the canonical morphism).
-/
