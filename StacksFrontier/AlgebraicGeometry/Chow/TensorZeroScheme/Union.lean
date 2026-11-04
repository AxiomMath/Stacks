module

public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.Branches
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeTensorInf

/-!
# The inverse image of `D` is the union of the two branches

Let `Y` be a scheme, let `L₁` and `L₂` be invertible `𝒪_Y`-modules, let `s` be a global section
of `L₁ ⊗_{𝒪_Y} L₂` and let `i : D → Y` be the zero scheme of `s`. Condition (5) of [Stacks, Tag
0F97] asserts that the scheme-theoretic inverse image `p^{-1}D` is the scheme-theoretic union
`D₁ ∪ D₂` of the two branches.

One half, `p^{-1}D ≤ D₁ ⊓ D₂` in the order on ideal sheaves — which is the order on ideals and so
opposite to inclusion of subschemes — is
`Stacks.Chow.TensorZeroScheme.comap_zeroIdeal_proj_le_inf`. This file supplies the other half, by
specializing the general statement
`Stacks.Divisors.zeroScheme_tensorSection_eq_inf`: the zero scheme of a product of two sections
of invertible modules is the union of the two zero schemes as soon as the second section restricts
to a regular section of the zero scheme of the first.

## Main results

* `Stacks.Chow.TensorZeroScheme.comap_zeroIdeal_proj_eq_inf`: **Tag 0F97(5)**, `p^{-1}D = D₁ ∪ D₂`,
  given that `s₂` restricts to a regular section of `p^*L₂` on the branch `D₁`.

## Implementation notes

The regularity hypothesis is the one the general theorem asks for, written with the zero scheme
`Z(s₁)` spelled out rather than as `Stacks.Chow.TensorZeroScheme.branch₁`. The two are the same
ideal sheaf — that is `Stacks.Chow.TensorZeroScheme.branch₁_eq_zeroScheme`, which holds by
`rfl` — but writing the branch instead makes the elaborator check that identity through two
`Scheme.IdealSheafData.subscheme`s and a sheaf of modules, which exceeds the heartbeat limit.
Under condition (4) it holds because the
restriction of `s₂` to `D₁` is, through the identification of `D₁` with a line bundle over `D`,
the tautological section of that line bundle, which is regular by [Stacks, Tag 0F96](1)
(`Stacks.LineBundle.Situation.isRegularSection_tautologicalSection`); it is not an extra
assumption on the data.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Chow.TensorZeroScheme

variable (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
  [hL₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [hL₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤))

include hL₁ hL₂ in
/-- **Stacks Project, Tag 0F97(5)**: the scheme-theoretic inverse image `p^{-1}D` is the
scheme-theoretic union `D₁ ∪ D₂` of the two branches, given that the second section restricts to
a regular section on the first branch. In the order on `Scheme.IdealSheafData`, which is the order
on ideals and so opposite to inclusion of subschemes, the union is the meet. -/
theorem comap_zeroIdeal_proj_eq_inf
    (hreg : AlgebraicGeometry.IsRegularSection
      (Stacks.Divisors.zeroScheme (spaceIdeal Y L₁ L₂ s).subscheme
          ((Scheme.Modules.pullback (proj Y L₁ L₂ s)).obj L₁)
          (section₁ Y L₁ L₂ s)).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme (spaceIdeal Y L₁ L₂ s).subscheme
          ((Scheme.Modules.pullback (proj Y L₁ L₂ s)).obj L₁)
          (section₁ Y L₁ L₂ s)).subscheme.ringCatSheaf.property
      (Stacks.SheafOfModules.sectionsOfTop
        ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme (spaceIdeal Y L₁ L₂ s).subscheme
            ((Scheme.Modules.pullback (proj Y L₁ L₂ s)).obj L₁)
            (section₁ Y L₁ L₂ s)).subschemeι).obj
          ((Scheme.Modules.pullback (proj Y L₁ L₂ s)).obj L₂))
        (AlgebraicGeometry.pullbackGlobalSections
          (Stacks.Divisors.zeroScheme (spaceIdeal Y L₁ L₂ s).subscheme
            ((Scheme.Modules.pullback (proj Y L₁ L₂ s)).obj L₁)
            (section₁ Y L₁ L₂ s)).subschemeι
          ((Scheme.Modules.pullback (proj Y L₁ L₂ s)).obj L₂) (section₂ Y L₁ L₂ s)))) :
    (zeroIdeal Y L₁ L₂ s).comap (proj Y L₁ L₂ s) =
      branch₁ Y L₁ L₂ s ⊓ branch₂ Y L₁ L₂ s := by
  rw [comap_zeroIdeal_proj]
  exact (Stacks.Divisors.zeroScheme_tensorSection_eq_inf
    ((Scheme.Modules.pullback (proj Y L₁ L₂ s)).obj L₁)
    ((Scheme.Modules.pullback (proj Y L₁ L₂ s)).obj L₂)
    (section₁ Y L₁ L₂ s) (section₂ Y L₁ L₂ s) hreg).symm

end Stacks.Chow.TensorZeroScheme

end
