module

public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.DecompositionBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.Union

/-!
# The regularity condition (5) of Tag 0F97 asks for, and the condition itself

Let `Y` be a scheme, let `L₁` and `L₂` be invertible `𝒪_Y`-modules, let `s` be a global section
of `L₁ ⊗_{𝒪_Y} L₂` and let `i : D → Y` be the zero scheme of `s`. Condition (5) of [Stacks, Tag
0F97] asserts that the scheme-theoretic inverse image `p^{-1}D` is the scheme-theoretic union
`D₁ ∪ D₂` of the two branches of the construction.

`Stacks.Chow.TensorZeroScheme.comap_zeroIdeal_proj_eq_inf` proves that from one hypothesis: that
`s₂` restricts to a *regular* section of `p^*L₂` on the branch `D₁`. This file discharges that
hypothesis from conditions (4), (6) and (7) — the identification of `D₁` with the line bundle
`\underline{\Spec}_D(\Sym^*(L₂^{⊗ -1}|_D))` over `D`, the fact that `D₁ ∩ D₂` maps isomorphically
to `D`, and the fact that `D₁ ∩ D₂ ⟶ D₁` is the zero section of that line bundle — and so proves
condition (5) itself. Those three conditions are exactly the parameters
`Stacks.Chow.TensorZeroScheme.decompositionOfClauses` already takes for the record
`Stacks.Chow.TensorZeroScheme.Decomposition`, so condition (5) is no longer a separate input to
the record: it follows from the conditions beside it.

## Main results

* `Stacks.Chow.TensorZeroScheme.isRegularSection_section₂_restrict`: **the restriction of `s₂` to
  the branch `D₁` is a regular section of `p^*L₂|_{D₁}`**, given conditions (4), (6) and (7) for
  that branch.
* `Stacks.Chow.TensorZeroScheme.comap_zeroIdeal_proj_eq_inf_of_zeroSection`: **Tag 0F97(5)**,
  `p^{-1}D = D₁ ∪ D₂`, given conditions (4), (6) and (7) for that branch and nothing else.

## Implementation notes

The hypotheses are stated exactly as the corresponding parameters of
`Stacks.Chow.TensorZeroScheme.decompositionOfClauses`, and the conclusion of the second theorem
exactly as that definition's parameter `hunion`, so that it can be substituted for it with no
rewriting. In the order on `AlgebraicGeometry.Scheme.IdealSheafData`, which is the order on
ideals and so opposite to inclusion of subschemes, the scheme-theoretic union is the meet and the
scheme-theoretic intersection the join.

The regularity itself is `Stacks.LineBundle.isRegularSection_restrict_of_inf_eq_zeroSection`,
which asks for the data of the three conditions and for nothing about how the branches were
built; the branches of the construction are the zero schemes of the two sections by definition
(`Stacks.Chow.TensorZeroScheme.branch₁_eq_zeroScheme` and `branch₂_eq_zeroScheme`), which is what
lets the general statement be read at them.

No `@[stacks]` attribute is attached: condition (5) is one clause of the tag, and the tag is
registered on the statement of the whole diagram.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
* [Stacks Project, Tag 02OO](https://stacks.math.columbia.edu/tag/02OO)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
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
/-- **The restriction of `s₂` to the branch `D₁` is a regular section**, given conditions (4),
(6) and (7) of [Stacks, Tag 0F97] for that branch: an identification `e₁` of `D₁` with the line
bundle `\underline{\Spec}_D(\Sym^*(L₂^{⊗ -1}|_D))`, the fact that the scheme-theoretic
intersection `D₁ ∩ D₂` maps isomorphically to `D`, and the fact that, read through `e₁`, the
inclusion `D₁ ∩ D₂ ⟶ D₁` is the zero section of that line bundle.

This is the hypothesis of `Stacks.Chow.TensorZeroScheme.comap_zeroIdeal_proj_eq_inf`, and hence
all that condition (5) of the tag needs beyond the conditions beside it. -/
theorem isRegularSection_section₂_restrict
    (e₁ : (branch₁ Y L₁ L₂ s).subscheme ≅ (branchSituation Y L₁ L₂ s L₂).totalSpace)
    (hiso : IsIso (Scheme.IdealSheafData.inclusion
      (le_sup_left : branch₁ Y L₁ L₂ s ≤ branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s) ≫
        proj₁ Y L₁ L₂ s))
    (hzero₁ : Scheme.IdealSheafData.inclusion
        (le_sup_left : branch₁ Y L₁ L₂ s ≤ branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s) ≫ e₁.hom =
      (Scheme.IdealSheafData.inclusion
          (le_sup_left : branch₁ Y L₁ L₂ s ≤ branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s) ≫
        proj₁ Y L₁ L₂ s) ≫ (branchSituation Y L₁ L₂ s L₂).zeroSection) :
    AlgebraicGeometry.IsRegularSection (branch₁ Y L₁ L₂ s).subscheme.sheaf.obj
      (branch₁ Y L₁ L₂ s).subscheme.ringCatSheaf.property
      (Stacks.SheafOfModules.sectionsOfTop
        ((Scheme.Modules.pullback (branch₁ Y L₁ L₂ s).subschemeι).obj
          ((Scheme.Modules.pullback (proj Y L₁ L₂ s)).obj L₂))
        (AlgebraicGeometry.pullbackGlobalSections (branch₁ Y L₁ L₂ s).subschemeι
          ((Scheme.Modules.pullback (proj Y L₁ L₂ s)).obj L₂) (section₂ Y L₁ L₂ s))) :=
  Stacks.LineBundle.isRegularSection_restrict_of_inf_eq_zeroSection
    (branch₁ Y L₁ L₂ s) (branch₂ Y L₁ L₂ s)
    ((Scheme.Modules.pullback (proj Y L₁ L₂ s)).obj L₂) (section₂ Y L₁ L₂ s)
    (branch₂_eq_zeroScheme Y L₁ L₂ s) (branchSituation Y L₁ L₂ s L₂) e₁
    (Scheme.IdealSheafData.inclusion
        (le_sup_left : branch₁ Y L₁ L₂ s ≤ branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s) ≫
      proj₁ Y L₁ L₂ s) hiso hzero₁

include hL₁ hL₂ in
/-- **Stacks Project, Tag 0F97(5)**: the scheme-theoretic inverse image `p^{-1}D` is the
scheme-theoretic union `D₁ ∪ D₂` of the two branches. The only inputs are conditions (4), (6) and
(7) of the tag for the first branch, in the form
`Stacks.Chow.TensorZeroScheme.decompositionOfClauses` takes them.

In the order on `AlgebraicGeometry.Scheme.IdealSheafData`, which is the order on ideals and so
opposite to inclusion of subschemes, the union is the meet. -/
theorem comap_zeroIdeal_proj_eq_inf_of_zeroSection
    (e₁ : (branch₁ Y L₁ L₂ s).subscheme ≅ (branchSituation Y L₁ L₂ s L₂).totalSpace)
    (hiso : IsIso (Scheme.IdealSheafData.inclusion
      (le_sup_left : branch₁ Y L₁ L₂ s ≤ branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s) ≫
        proj₁ Y L₁ L₂ s))
    (hzero₁ : Scheme.IdealSheafData.inclusion
        (le_sup_left : branch₁ Y L₁ L₂ s ≤ branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s) ≫ e₁.hom =
      (Scheme.IdealSheafData.inclusion
          (le_sup_left : branch₁ Y L₁ L₂ s ≤ branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s) ≫
        proj₁ Y L₁ L₂ s) ≫ (branchSituation Y L₁ L₂ s L₂).zeroSection) :
    (zeroIdeal Y L₁ L₂ s).comap (proj Y L₁ L₂ s) =
      branch₁ Y L₁ L₂ s ⊓ branch₂ Y L₁ L₂ s :=
  comap_zeroIdeal_proj_eq_inf Y L₁ L₂ s
    (isRegularSection_section₂_restrict Y L₁ L₂ s e₁ hiso hzero₁)

end Stacks.Chow.TensorZeroScheme

end
