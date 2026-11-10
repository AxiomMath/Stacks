module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.DeterminantChangeOfEquations.Subfamily
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.DeterminantChangeOfEquations.Cocycle
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.DeterminantChangeOfEquations.ClassTarget

/-!
# Changing the equations by a matrix multiplies the fraction class by its determinant

Let `X` be a scheme, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` cut out the closed subscheme `Z ⊆ X` and let
`ℱ` be an `𝒪_X`-module, as in Stacks 0G7I.  Let `a_{ji} ∈ Γ(X, 𝒪_X)` be a `c × c` matrix of
global functions and set `g_j = ∑_i a_{ji} f_i`.  Stacks 0G7S says that if `g₁, …, g_c` cut out
`Z` scheme theoretically and `ℱ` is quasi-coherent, then the classes of Stacks 0G7Q satisfy

`c_{f₁,…,f_c} = det(a_{ji}) c_{g₁,…,g_c}`.

The source proves this by introducing the extended alternating Čech complex `𝓕''^•` of the
*mixed* family `f₁, …, f_c, g₁, …, g_c` of `2c` equations, projecting it onto the complexes of
the two halves, and exhibiting one explicit degree-`c` cocycle on `𝓕''^•` whose two projections
are `s / (f₁ ⋯ f_c)` and `det(a_{ji}) s / (g₁ ⋯ g_c)`; it then identifies the degree-`c`
cohomology of all three complexes with `i_*ℋ^c_Z(ℱ)`, so that the two projections of the single
class of `σ` become the two sides of the displayed equation.  Both halves are carried out here:
`mixedFractionHom_projections` and `mixedFractionHom_comp_cokernelπ` state the cocycle and its
two projections at the level of the complexes, and
`supportedFractionClass_eq_det_smul` states the displayed equation itself, as one equation of
maps into the single object `i_*ℋ^c_Z(ℱ)`.

## Main definitions

* `subfamilyProd` and `subfamilyCplxMap`: the projection of the extended alternating Čech
  complex of a family of equations onto the complex of a subfamily, in one degree and as a
  morphism of complexes, the identity in degree `0`.
* `mixedEquations`, `mixedRows` and `mixedMinor`: the mixed family of `2c` equations, the
  `2c × c` matrix expressing each of its members in terms of `f₁, …, f_c`, and the `c × c` minor
  of that matrix selected by an increasing `c`-tuple of the `2c` indices.
* `minorSmul` and `mixedFractionHom`: the cocycle `σ` of the source, whose component at an
  increasing `c`-tuple `q` is `det(minor at q) · s / (product of the equations of q)`.
* `supportPush` and `supportPushCounit`: `i_* R𝓗_T` and the canonical map `i_* R𝓗_T(K) ⟶ K` of
  Stacks 0G72.
* `cechToDerivedSupport`: **the canonical comparison `𝓕^• ⟶ i_* R𝓗_T(ℱ)` of Stacks 0G7L**, as a
  term.
* `cocycleClass` and `cechCocycleClass`: the cohomology class of a cocycle, in general and on
  the extended alternating Čech complex.
* `supportCohomologySheaf`: the sheaf `i_*ℋ^p_T(ℱ)`.
* `cokernelLastDifIsoHomology`, `cechHomologyToSupport` and `cokernelLastDifToSupport`: the two
  identifications through which the class map of Stacks 0G7Q is read in `i_*ℋ^c_T(ℱ)`, and
  their composite.

## Main results

* `cofactorSum_eq_zero`: the cofactor identity behind the cocycle condition — for `c + 1` rows
  of a `c`-column matrix, the signed sum of `(row ⬝ f) · det(the other rows)` vanishes.
* `mixedFractionHom_difSucc`: `σ` is a cocycle.
* `mixedFractionHom_subfamilyProd_castAdd` and `mixedFractionHom_subfamilyProd_natAdd`: its two
  projections are `s / (f₁ ⋯ f_c)` and `det(a_{ji}) s / (g₁ ⋯ g_c)`.
* `mixedFractionHom_projections` and `mixedFractionHom_comp_cokernelπ`: **Stacks 0G7S** at the
  level of the complexes, the three statements together, and the same read on the class maps
  `supportedFractionClass` of Stacks 0G7Q.
* `supportedFractionClass_eq_det_smul`: **Stacks 0G7S**, the equation
  `c_{f₁,…,f_c} = det(a_{ji}) c_{g₁,…,g_c}` of maps into the single object `i_*ℋ^c_Z(ℱ)`.
* `isIso_cokernelLastDifToSupport`: that identification is an isomorphism, which is
  **Stacks 0G7M**; `isIso_supportPush_map_augmentation` and `isIso_cechToSupport` are its two
  halves.
* `homologyMap_subfamilyCplxMap_comp_cechHomologyToSupport`: the projections out of a family
  onto a subfamily all induce the same map on `i_*ℋ^p_Z(ℱ)`.
* `cohomologySupportedOn_cech`: the extended alternating Čech complex is supported on the common
  zero locus of its equations.
* `isIso_derivedSupportedSectionsToId_cech`: **Stacks 0G7M** with the comparison as a canonical
  term — the counit `i_* R𝓗_T(𝓕^•) ⟶ 𝓕^•` is invertible.
* `cechToDerivedSupport_comp_derivedSupportedSectionsToId`: **the commuting triangle of
  Stacks 0G7L**, in the shape the remark displays it — the augmentation `𝓕^• ⟶ ℱ` factors as the
  comparison followed by the counit at `ℱ[0]`.  Its counterpart
  `derivedSupportedSectionsToId_comp_cechToDerivedSupport` is the characterisation by the counit
  at `𝓕^•`, which is how the comparison is built.
* `Q_map_extendMap_subfamilyCplxMap_comp_cechToDerivedSupport`: the subfamily projections are
  compatible with the comparison of Stacks 0G7L, which is the source's step that the projections
  out of the mixed complex "represent the identity on `i_* R𝓗_Z(ℱ)`".

## Implementation notes

The mixed family is `Fin.append f g`, so `Fin.append f g ∘ Fin.castAdd c` is `f` only
propositionally; `prodTermCongr` transports along such an equality of families, and
`fractionHom_prodTermCongr` moves the fraction morphism across it.  A *subfamily* in the sense of
`subfamilyProd`, by contrast, is given as `e ∘ φ` for an order embedding `φ`, which makes the
principal-open intersections and the restricted modules of the two families definitionally equal,
so the projection needs no transport at all.

The coefficient `λ` of the source — the coefficient of `e₁ ∧ ⋯ ∧ e_c` in a wedge of `c` vectors —
is realised as the determinant `mixedMinor` of a square submatrix of `Fin.append 1 a`, which is
what turns the source's cocycle condition into `cofactorSum_eq_zero`, an expansion of a
determinant with a repeated column along its first column.

The derived-category material uses the standard model of the derived category at priority
`10000`: the locally small model arrives as a global instance through the imports, and every
library statement used here is elaborated at the standard model.  This is the convention of
`Stacks.Perfect.SupportedQuasicoherent`.

## References

* [Stacks Project, Tag 0G7S](https://stacks.math.columbia.edu/tag/0G7S)
* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
* [Stacks Project, Tag 0G7L](https://stacks.math.columbia.edu/tag/0G7L)
* [Stacks Project, Tag 0G7M](https://stacks.math.columbia.edu/tag/0G7M)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G72](https://stacks.math.columbia.edu/tag/0G72)

The content is split into `Subfamily`, `Cocycle` and `ClassTarget`.
-/
