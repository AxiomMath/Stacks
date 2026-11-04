module

public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.FiniteType
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.WholeTag

/-!
# The decomposition of [Stacks, Tag 0F97]

Let `Y` be a scheme, let `L₁` and `L₂` be invertible `𝒪_Y`-modules, let `s` be a global section of
`L₁ ⊗_{𝒪_Y} L₂` and let `i : D → Y` be its zero scheme. The construction of [Stacks, Tag 0F97] —
the scheme `L` cut out by `z₁ ⊗ z₂ - q^*s` inside `Tot(L₁^{⊗ -1}) ×_Y Tot(L₂^{⊗ -1})`, its
structure morphism `p`, its two sections `s₁`, `s₂` and its two branches `D₁`, `D₂` — is in
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.Basic`, and the two projections `p₁`, `p₂` of
the tag's diagram are in `…TensorZeroScheme.Branches`.

This file assembles those objects, together with the tag's numbered conditions, into the record
`Stacks.Chow.TensorZeroScheme.Decomposition` of
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.WholeTag`.

## Main definitions

* `Stacks.Chow.TensorZeroScheme.decompositionOfClauses`: **the decomposition of the tag**, built
  from the construction together with those of the tag's conditions that are not proved in the
  construction itself.

## Implementation notes

The conditions already proved by the construction are filled in here and are not parameters:
condition (1) is `Stacks.Chow.TensorZeroScheme.pullbackTensorSection_proj`, condition (3) is
`branch₁_eq_zeroScheme` and `branch₂_eq_zeroScheme`, the two commuting squares of the diagram are
`branch₁_subschemeι_comp_proj` and `branch₂_subschemeι_comp_proj`, and the finite-type half of
condition (2) is `locallyOfFiniteType_proj` together with `quasiCompact_proj`. What remains as
parameters is exactly the flatness and relative dimension of condition (2), condition (4) for each
branch, condition (5), condition (6) and condition (7) for each branch.

The relative-dimension parameter is stated under the same `letI` as the field it fills, so that
the `AlgebraicGeometry.RelativeDimension` of the parameter and of the field are the same term;
`LocallyOfFiniteType` is a `Prop`-valued class, so the choice of instance does not matter.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
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
/-- **The decomposition of [Stacks, Tag 0F97]**, assembled from the construction and from those
of the tag's conditions that the construction does not itself prove. -/
def decompositionOfClauses
    (hflat : AlgebraicGeometry.Flat (proj Y L₁ L₂ s))
    (hdim : letI : LocallyOfFiniteType (proj Y L₁ L₂ s) := locallyOfFiniteType_proj Y L₁ L₂ s
      AlgebraicGeometry.RelativeDimension (proj Y L₁ L₂ s) 1)
    (e₁ : (branch₁ Y L₁ L₂ s).subscheme ≅ (branchSituation Y L₁ L₂ s L₂).totalSpace)
    (he₁ : e₁.hom ≫ (branchSituation Y L₁ L₂ s L₂).totalSpaceToBase = proj₁ Y L₁ L₂ s)
    (e₂ : (branch₂ Y L₁ L₂ s).subscheme ≅ (branchSituation Y L₁ L₂ s L₁).totalSpace)
    (he₂ : e₂.hom ≫ (branchSituation Y L₁ L₂ s L₁).totalSpaceToBase = proj₂ Y L₁ L₂ s)
    (hunion : (zeroIdeal Y L₁ L₂ s).comap (proj Y L₁ L₂ s) =
      branch₁ Y L₁ L₂ s ⊓ branch₂ Y L₁ L₂ s)
    (hiso : IsIso (Scheme.IdealSheafData.inclusion
      (le_sup_left : branch₁ Y L₁ L₂ s ≤ branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s) ≫
        proj₁ Y L₁ L₂ s))
    (hzero₁ : Scheme.IdealSheafData.inclusion
        (le_sup_left : branch₁ Y L₁ L₂ s ≤ branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s) ≫ e₁.hom =
      (Scheme.IdealSheafData.inclusion
          (le_sup_left : branch₁ Y L₁ L₂ s ≤ branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s) ≫
        proj₁ Y L₁ L₂ s) ≫ (branchSituation Y L₁ L₂ s L₂).zeroSection)
    (hzero₂ : Scheme.IdealSheafData.inclusion
        (le_sup_right : branch₂ Y L₁ L₂ s ≤ branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s) ≫ e₂.hom =
      (Scheme.IdealSheafData.inclusion
          (le_sup_right : branch₂ Y L₁ L₂ s ≤ branch₁ Y L₁ L₂ s ⊔ branch₂ Y L₁ L₂ s) ≫
        proj₂ Y L₁ L₂ s) ≫ (branchSituation Y L₁ L₂ s L₁).zeroSection) :
    Decomposition Y L₁ L₂ s where
  total := (spaceIdeal Y L₁ L₂ s).subscheme
  p := proj Y L₁ L₂ s
  D₁ := branch₁ Y L₁ L₂ s
  D₂ := branch₂ Y L₁ L₂ s
  p₁ := proj₁ Y L₁ L₂ s
  p₂ := proj₂ Y L₁ L₂ s
  comm₁ := branch₁_subschemeι_comp_proj Y L₁ L₂ s
  comm₂ := branch₂_subschemeι_comp_proj Y L₁ L₂ s
  s₁ := section₁ Y L₁ L₂ s
  s₂ := section₂ Y L₁ L₂ s
  pullback_section_eq := pullbackTensorSection_proj Y L₁ L₂ s
  p_locallyOfFiniteType := locallyOfFiniteType_proj Y L₁ L₂ s
  p_quasiCompact := quasiCompact_proj Y L₁ L₂ s
  p_flat := hflat
  p_relativeDimension := hdim
  zeroScheme₁ := branch₁_eq_zeroScheme Y L₁ L₂ s
  zeroScheme₂ := branch₂_eq_zeroScheme Y L₁ L₂ s
  branch₁ := e₁
  branch₁_toBase := he₁
  branch₂ := e₂
  branch₂_toBase := he₂
  preimage_eq_union := hunion
  intersection_isIso := hiso
  intersection_zeroSection₁ := hzero₁
  intersection_zeroSection₂ := hzero₂

end Stacks.Chow.TensorZeroScheme

end
