module

public import StacksFrontier.AlgebraicGeometry.Etale.FlatFiniteTypeNeighborhood
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniGenericMember

/-!
# Base change of a closed immersion, read on structure sheaves

For a morphism of schemes `f : X ⟶ Y` and a quasi-coherent ideal sheaf `J` on `Y` cutting out
the closed subscheme `Z = Z(J)` with inclusion `i : Z ⟶ Y`, the inverse image ideal sheaf
`J.comap f` cuts out the scheme-theoretic inverse image `Z' = f⁻¹(Z)` with inclusion
`i' : Z' ⟶ X`, and

`f^*(i_* 𝒪_Z) ≅ i'_* 𝒪_{Z'}`.

In other words `f^*(𝒪_Y/J) = 𝒪_X/(J · 𝒪_X)`: forming the quotient by a closed subscheme commutes
with base change. No hypothesis on `f` is needed — not flatness, not quasi-compactness.

## Main results

* `Stacks.IdealSheaf.comapStructureSheafIso`: the isomorphism above.

## Why no hypothesis on `f` is needed

The comparison `g^*f_*F ⟶ f'_*(g')^*F` of a cartesian square is an isomorphism for a
quasi-coherent `F` as soon as the morphism being pushed forward is **affine** — this is
[Stacks, Tag 02KG], proved as
`Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom` and
packaged as `AlgebraicGeometry.affinePushforwardBaseChangeIso`. Here the morphism being pushed
forward is the closed immersion `i`, which is affine, so the hypothesis falls on `i` and not on
`f`. The flat version `Stacks.FundamentalGroup.flatBaseChangeUnitIso` asks instead for `f` to be
flat, quasi-compact and quasi-separated, which rules out such morphisms as the blowdown
`p : Bl_I(Spec A) ⟶ Spec A`; that is why this statement is not an instance of it.

The square is cartesian by `Stacks.Bertini.isPullback_subschemeι_comap`: the subscheme of an
inverse image ideal sheaf *is* the fibre product, by Mathlib's
`AlgebraicGeometry.Scheme.IdealSheafData.comapIso`. The remaining `(g')^*𝒪_Z` on the right-hand
side of the base-change isomorphism is `𝒪_{Z'}` by
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.IdealSheaf

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (J : Y.IdealSheafData)

/-- **`f^*(𝒪_{Z(J)}) ≅ 𝒪_{Z(J · 𝒪_X)}`**: the inverse image along `f : X ⟶ Y` of the structure
sheaf of the closed subscheme cut out by an ideal sheaf `J` on `Y` is the structure sheaf of the
closed subscheme cut out by the inverse image ideal sheaf `J.comap f`, both read as sheaves on
the ambient scheme through the closed immersion.

This is the base change of a closed immersion at the level of structure sheaves. It holds for an
arbitrary `f`, because the hypothesis of the affine base-change theorem [Stacks, Tag 02KG] falls
on the closed immersion `J.subschemeι` — which is affine — rather than on `f`. -/
noncomputable def comapStructureSheafIso :
    (Scheme.Modules.pullback f).obj
        ((Scheme.Modules.pushforward J.subschemeι).obj (Scheme.unitModule J.subscheme)) ≅
      (Scheme.Modules.pushforward (J.comap f).subschemeι).obj
        (Scheme.unitModule (J.comap f).subscheme) :=
  AlgebraicGeometry.affinePushforwardBaseChangeIso
      (Stacks.Bertini.isPullback_subschemeι_comap J f).flip _ ≪≫
    (Scheme.Modules.pushforward (J.comap f).subschemeι).mapIso
      (Scheme.Modules.pullbackUnitIso _)

end Stacks.IdealSheaf

end
