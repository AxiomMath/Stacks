module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DGCategory

/-!
# Composition in the differential graded category of differential graded modules

Composition of homogeneous right `A`-linear maps of right differential graded modules adds their
degrees. The resulting operation is bilinear over the base ring, obeys the graded Leibniz rule
with respect to the differential of the Hom modules, and is associative and unital with closed
identities. Together with the differential graded Hom modules this is exactly the data making
the differential graded modules into a differential graded category.

## Main results

Composition is `DifferentialGradedModule.homogeneousMapComp`, and the differential graded
category it belongs to is `DifferentialGradedModule.dgCategory`. The laws it satisfies are the
corresponding projections of `DGCategory`: `DGCategory.comp_add_left`,
`DGCategory.comp_add_right`, `DGCategory.comp_smul_left`, `DGCategory.comp_smul_right`,
`DGCategory.leibniz`, `DGCategory.assoc`, `DGCategory.id_comp`, `DGCategory.comp_id` and
`DGCategory.d_id`.

## Implementation notes

A differential graded category encodes composition as a morphism out of the tensor product of
two Hom complexes, by requiring it to be graded bilinear and to satisfy the Leibniz rule. Those
two requirements are the projections `DGCategory.comp_add_left` … `DGCategory.leibniz` of
`DifferentialGradedModule.dgCategory`, so the tensor-product form of composition and its
category laws are already stated by that construction and no second composition is built here.
This file therefore only records which declarations carry the source's statement.

## References

* [Stacks Project, Tag 09LC](https://stacks.math.columbia.edu/tag/09LC)
-/

add_to_stacks 09LC "composition" DifferentialGradedModule.dgCategory
add_to_stacks 09LC "composition" DifferentialGradedModule.homogeneousMapComp
add_to_stacks 09LC "composition" DGCategory.comp_add_left
add_to_stacks 09LC "composition" DGCategory.comp_add_right
add_to_stacks 09LC "composition" DGCategory.comp_smul_left
add_to_stacks 09LC "composition" DGCategory.comp_smul_right
add_to_stacks 09LC "composition" DGCategory.leibniz
add_to_stacks 09LC "composition" DGCategory.assoc
add_to_stacks 09LC "composition" DGCategory.id_comp
add_to_stacks 09LC "composition" DGCategory.comp_id
add_to_stacks 09LC "composition" DGCategory.d_id
