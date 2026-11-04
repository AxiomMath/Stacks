module

public import StacksFrontier.Homology.HomComplex.RHom.BaseChange.HomComplexChangeOfRings
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange.ModelRestrictScalars
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange.BaseChangeMap
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange.ProjectionFormula
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange.HomComplexAdjunction
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange.ModelCriterion
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange.Invertibility

/-!
# Derived Hom, extension of scalars, and base change

The canonical change-of-rings isomorphism for derived Hom (Stacks 0E1W), the derived-Hom
base-change map `RHom_R(K, M) ⊗ᴸ_R A ⟶ RHom_A(K ⊗ᴸ_R A, M ⊗ᴸ_R A)` (Stacks 0E1X), and its
invertibility (Stacks 0A6A). The material is split into
`StacksFrontier.Homology.HomComplex.RHom.BaseChange.HomComplexChangeOfRings` (change of rings on Hom
complexes), `...ModelRestrictScalars` (the change-of-rings isomorphism, on models and in general),
`...BaseChangeMap` (the base-change map),
`...ProjectionFormula` (unit comparisons and the projection formula),
`...HomComplexAdjunction` (base change and tensor--Hom adjunction on Hom complexes),
`...ModelCriterion` (reduction to a model criterion) and `...Invertibility` (the four cases of
invertibility).
-/
