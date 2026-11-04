module

public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.DecompositionTransport
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.Existence
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.FlatRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.Intersection
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.UnionRegularity
public import StacksCore.Tactic.StacksAttribute

/-!
# The diagram of Tag 0F97

Let `Y` be a scheme, let `L₁`, `L₂` be invertible `𝒪_Y`-modules, let `s` be a global section of
`L₁ ⊗_{𝒪_Y} L₂` and let `i : D → Y` be the zero scheme of `s`. [Stacks, Tag 0F97] asserts that
there is a commutative diagram

  `D₁ --i₁--> L <--i₂-- D₂`,   `p : L ⟶ Y`,   `pᵢ : Dᵢ ⟶ D`,   `i ∘ pᵢ = p ∘ iᵢ`,

and sections `sᵢ` of `p^*Lᵢ` such that

1. `p^*s = s₁ ⊗ s₂`,
2. `p` is of finite type and flat of relative dimension `1`,
3. `Dᵢ` is the zero scheme of `sᵢ`,
4. `Dᵢ ≅ \underline{\Spec}(\Sym^*(L_{3-i}^{⊗ -1})|_D)` over `D`,
5. `p^{-1}D = D₁ ∪ D₂` (scheme-theoretic union),
6. `D₁ ∩ D₂` (scheme-theoretic intersection) maps isomorphically to `D`, and
7. `D₁ ∩ D₂ ⟶ Dᵢ` is the zero section of the line bundle `Dᵢ ⟶ D`,

and that the formation of the diagram and of the sections commutes with arbitrary base change.

The diagram, the sections and the seven conditions are the record
`Stacks.Chow.TensorZeroScheme.Decomposition`, and the base-change clause is the property
`Stacks.Chow.TensorZeroScheme.Decomposition.IsStableUnderBaseChange` of such a record. The
diagram is the one of the source's proof: `L` is cut out by `z₁ ⊗ z₂ - q^*s` in the fibre
product of the line bundles of `L₁^{⊗ -1}` and `L₂^{⊗ -1}`, so that over an affine open
`Spec B` of `Y` trivializing both modules `L` is `Spec B[z₁, z₂]/(z₁z₂ - f)`.

## Main definitions

* `Stacks.Chow.TensorZeroScheme.decomposition`: the diagram, the sections and the seven
  conditions, for every scheme, every pair of invertible modules and every section.

## Main results

* `Stacks.Chow.TensorZeroScheme.exists_decomposition`: **[Stacks, Tag 0F97]**.

## Implementation notes

Condition (2) is `Stacks.Chow.TensorZeroScheme.locallyOfFiniteType_proj`, `quasiCompact_proj`,
`flat_proj` and `relativeDimension_proj`; condition (4) is `branchIso₁` and `branchIso₂`;
condition (6) is `isIso_intersection_proj₁`; condition (7) is `intersection_comp_branchIso₁` and
`intersection_comp_branchIso₂`; and condition (5) is
`comap_zeroIdeal_proj_eq_inf_of_zeroSection`, which deduces it from conditions (4), (6) and (7)
through the regularity of the tautological section of a line bundle ([Stacks, Tag 0F96](1)).
The base-change clause holds for every diagram as in the tag,
`Stacks.Chow.TensorZeroScheme.Decomposition.isStableUnderBaseChange`.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow.TensorZeroScheme

variable (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
  [hL₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [hL₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤))

include hL₁ hL₂ in
/-- **The diagram of [Stacks, Tag 0F97]**, with its two sections and its seven conditions, for
an arbitrary scheme `Y`, arbitrary invertible `L₁`, `L₂` and an arbitrary global section `s` of
`L₁ ⊗ L₂`. -/
def decomposition : Decomposition Y L₁ L₂ s :=
  decompositionOfClauses Y L₁ L₂ s (flat_proj Y L₁ L₂ s) (relativeDimension_proj Y L₁ L₂ s)
    (branchIso₁ Y L₁ L₂ s) (branchIso₁_hom_comp_totalSpaceToBase Y L₁ L₂ s)
    (branchIso₂ Y L₁ L₂ s) (branchIso₂_hom_comp_totalSpaceToBase Y L₁ L₂ s)
    (comap_zeroIdeal_proj_eq_inf_of_zeroSection Y L₁ L₂ s (branchIso₁ Y L₁ L₂ s)
      (isIso_intersection_proj₁ Y L₁ L₂ s) (intersection_comp_branchIso₁ Y L₁ L₂ s))
    (isIso_intersection_proj₁ Y L₁ L₂ s) (intersection_comp_branchIso₁ Y L₁ L₂ s)
    (intersection_comp_branchIso₂ Y L₁ L₂ s)

include hL₁ hL₂ in
/-- **[Stacks, Tag 0F97].** Let `Y` be a scheme, `L₁`, `L₂` invertible `𝒪_Y`-modules, `s` a
global section of `L₁ ⊗ L₂` and `i : D → Y` its zero scheme. There is a commutative diagram
`D₁ → L ← D₂` over `D → Y ← D`, with `p : L ⟶ Y`, and sections `sᵢ` of `p^*Lᵢ` such that
`p^*s = s₁ ⊗ s₂`; `p` is of finite type and flat of relative dimension `1`; `Dᵢ` is the zero
scheme of `sᵢ`; `Dᵢ ≅ \underline{\Spec}(\Sym^*(L_{3-i}^{⊗ -1})|_D)` over `D`;
`p^{-1}D = D₁ ∪ D₂`; `D₁ ∩ D₂ ⟶ D` is an isomorphism; and `D₁ ∩ D₂ ⟶ Dᵢ` is the zero section of
the line bundle `Dᵢ ⟶ D` (the record `Stacks.Chow.TensorZeroScheme.Decomposition`). Moreover the
formation of the diagram and of the sections commutes with arbitrary base change
(`Stacks.Chow.TensorZeroScheme.Decomposition.IsStableUnderBaseChange`). -/
@[stacks 0F97]
theorem exists_decomposition : ∃ R : Decomposition Y L₁ L₂ s, R.IsStableUnderBaseChange :=
  ⟨decomposition Y L₁ L₂ s, (decomposition Y L₁ L₂ s).isStableUnderBaseChange⟩

end Stacks.Chow.TensorZeroScheme

end
