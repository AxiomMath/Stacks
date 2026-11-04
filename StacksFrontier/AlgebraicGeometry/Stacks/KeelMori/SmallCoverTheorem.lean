module

public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.UniformModuliSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMoriEtaleLocal.ModuliPieces

/-!
# The Keel–Mori theorem for a small Keel–Mori cover (Stacks 0DUT)

For a small Keel–Mori cover `C` of an algebraic stack `𝒳`
(`AlgebraicGeometry.Stack.KeelMoriCover.IsSmall`), the moduli map `f : 𝒳 ⟶ M = U/R` is a
uniform categorical moduli space, separated, quasi-compact and a universal homeomorphism, and
the pieces `𝒳 i ⟶ M i ⟶ M` of the cover exhibit it as built from the moduli spaces of
well-nigh affine stacks along étale morphisms covering `M`
(`AlgebraicGeometry.Stack.HasWellNighAffineModuliPieces`, the input of Stacks 0DUV).

## Main results

* `AlgebraicGeometry.Stack.KeelMoriCover.hasWellNighAffineModuliPieces_moduliMap`
* `AlgebraicGeometry.Stack.KeelMoriCover.exists_keelMoriModuliSpace_of_isSmall`
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.KeelMoriCover

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} {C : KeelMoriCover B S hS 𝒳} (hC : C.IsSmall)

attribute [local instance] hasSheafify_bigFppfOver

/-- **The moduli map of a small Keel–Mori cover has well-nigh affine moduli pieces**: the members
`𝒳 i`, their moduli spaces `M i`, and the étale `u i : M i ⟶ M`, jointly surjective, with the
squares `𝒳 i = M i ×_M 𝒳` 2-cartesian. -/
theorem hasWellNighAffineModuliPieces_moduliMap :
    HasWellNighAffineModuliPieces B S hS (M := Msp' hC) (moduliMap hC) :=
  ⟨C.ι, C.obj, C.map, C.M, C.f, uSp hC, fun i => (map_comp_moduliMap hC i).symm,
    C.wellNighAffine, C.isUniformCategoricalModuliSpace_f, isEtale_u hC,
    iUnion_range_pointsMap_u hC, nonempty_isTwoFibreProduct_square hC⟩

include hC in
/-- **The Keel–Mori theorem for a small Keel–Mori cover** (Stacks 0DUT), with the pieces the
moduli space is built from. -/
theorem exists_keelMoriModuliSpace_of_isSmall :
    ∃ (M : AlgebraicSpaces B S hS) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS M.obj M.property),
      IsUniformCategoricalModuliSpace B S hS M f.hom ∧ AlgebraicStacks.IsSeparated B S hS f ∧
        IsQuasiCompactMorphism.{u, w} B S hS f ∧ UniversalHomeomorphism B S hS f ∧
          HasWellNighAffineModuliPieces B S hS f :=
  ⟨Msp' hC, moduliMap hC, isUniformCategoricalModuliSpace_moduliMap hC,
    isSeparated_moduliMap hC, isQuasiCompactMorphism_moduliMap hC,
    universalHomeomorphism_moduliMap hC, hasWellNighAffineModuliPieces_moduliMap hC⟩

end AlgebraicGeometry.Stack.KeelMoriCover

end
