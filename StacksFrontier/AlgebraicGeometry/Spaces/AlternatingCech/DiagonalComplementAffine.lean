module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.DiagonalComplementClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SelfProdUnderlying
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions

/-!
# The self-products of an affine étale chart are affine over the base

Let `U` be an algebraic space étale over an algebraic space `X` over a scheme `S` whose
structure morphism `U ⟶ X` is affine — for instance an affine scheme mapping to a separated
algebraic space, by [Stacks, Tag 08GB].  Then every finite self-product `U ×_X ⋯ ×_X U` of `U`
in the spaces-étale site of `X` is affine over `X`, being an iterated base change of `U ⟶ X`,
and so is the complement `W_n` of the diagonals in it, whose inclusion is a closed immersion.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.isAffineHom_selfProd_hom`: the structure morphism of a
  finite self-product of `U` is affine.
* `AlgebraicGeometry.Space.SpacesEtale.isAffineHom_diagonalComplement_hom`: so is that of the
  complement of the diagonals.

## References

* [Stacks Project, Tag 072B](https://stacks.math.columbia.edu/tag/072B)
* [Stacks Project, Tag 08GB](https://stacks.math.columbia.edu/tag/08GB)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe u

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

attribute [local instance] CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback
  CategoryTheory.Over.over_hasTerminal hasFiniteProducts_of_has_binary_and_terminal

/-- The identification of the `(n+1)`-fold self-product with a fibre product over `X` is
compatible with the structure morphisms to `X`. -/
theorem underlyingSelfProdSuccIso_hom_comp (U : SpacesEtale B S hS X) (n : ℕ) :
    (underlyingSelfProdSuccIso B S hS X U n).hom ≫
        pullback.fst ((inclusion B S hS X).obj U).hom
          ((inclusion B S hS X).obj (selfProd B S hS X U n)).hom ≫
        ((inclusion B S hS X).obj U).hom =
      ((inclusion B S hS X).obj (selfProd B S hS X U (n + 1))).hom := by
  let E := inclusionSelfProdSuccIso B S hS X U n ≪≫
    (prodIsProd ((inclusion B S hS X).obj U)
      ((inclusion B S hS X).obj (selfProd B S hS X U n))).conePointUniqueUpToIso
      (IsLimit.pullbackConeEquivBinaryFanFunctor
        (pullbackIsPullback ((inclusion B S hS X).obj U).hom
          ((inclusion B S hS X).obj (selfProd B S hS X U n)).hom))
  exact Over.w E.hom

variable {B S hS X}

/-- The presheaf morphism underlying an isomorphism of algebraic spaces is an isomorphism. -/
theorem isIso_hom_of_isIso {F G : AlgebraicSpaces B S hS} (f : F ⟶ G) [IsIso f] :
    IsIso f.hom :=
  (ObjectProperty.ι _).map_isIso f

/-- Precomposing an affine morphism with an isomorphism of algebraic spaces gives an affine
morphism. -/
private theorem isAffineHom_comp_of_isIso {F G H : AlgebraicSpaces B S hS} (f : F ⟶ G) [IsIso f]
    {g : G ⟶ H} (hg : IsAffineHom B S hS g.hom) : IsAffineHom B S hS (f ≫ g).hom :=
  have := isIso_hom_of_isIso f
  isAffineHom_comp B S hS _ _ (isAffineHom_of_isIso _) hg

/-- **The nonempty finite self-products of an object affine over `X` are affine over `X`.** -/
theorem isAffineHom_selfProd_hom (U : SpacesEtale B S hS X)
    (hU : IsAffineHom B S hS U.obj.hom.hom) (n : ℕ) :
    IsAffineHom B S hS ((inclusion B S hS X).obj (selfProd B S hS X U (n + 1))).hom.hom := by
  induction n with
  | zero =>
    let e := productUniqueIso fun _ : Fin 1 => U
    have h : ((inclusion B S hS X).map e.hom).left ≫ ((inclusion B S hS X).obj U).hom =
        ((inclusion B S hS X).obj (selfProd B S hS X U 1)).hom :=
      Over.w ((inclusion B S hS X).map e.hom)
    rw [← h]
    have : IsIso ((inclusion B S hS X).map e.hom).left :=
      (Over.forget X).map_isIso ((inclusion B S hS X).map e.hom)
    exact isAffineHom_comp_of_isIso _ hU
  | succ n ih =>
    rw [← underlyingSelfProdSuccIso_hom_comp B S hS X U (n + 1)]
    refine isAffineHom_comp_of_isIso _ ?_
    refine isAffineHom_comp B S hS _ _ ?_ hU
    exact IsAffineHom.of_isPullback
      (AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback _ _).flip) ih

/-- **The complement of the diagonals in a self-product of an object affine over `X` is affine
over `X`**: its inclusion into the self-product is a closed immersion. -/
theorem isAffineHom_diagonalComplement_hom (U : SpacesEtale B S hS X)
    (hU : IsAffineHom B S hS U.obj.hom.hom) (m : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) :
    IsAffineHom B S hS (diagonalComplement B S hS X U (m + 1) hsep).obj.hom.hom := by
  rw [← hom_toSpaces_map_comp_structure B S hS X
    (diagonalComplementι B S hS X U (m + 1) hsep)]
  exact isAffineHom_comp B S hS _ _
    (isAffineHom_of_isClosedImmersion B S hS _
      (isClosedImmersion_diagonalComplementι B S hS X U (m + 1) hsep))
    (isAffineHom_selfProd_hom U hU m)

end AlgebraicGeometry.Space.SpacesEtale
