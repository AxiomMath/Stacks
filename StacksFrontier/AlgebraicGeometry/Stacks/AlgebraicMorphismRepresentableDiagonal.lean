module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaProductsToDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaRepresentableSources
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityComp
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityInvariance
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# An algebraic morphism inherits a representable diagonal (Stacks 0D3R)

Let `S` be a scheme contained in a big fppf site `B` and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
stacks in groupoids over the big fppf site of `S` which is *algebraic* in the sense of
Stacks 06CF, i.e. whose 2-fibre product with every scheme-valued point of `𝒴` is an algebraic
stack. If the diagonal of `𝒴` is representable by algebraic spaces then so is the diagonal
of `𝒳`.

## Main results

* `AlgebraicGeometry.Stack.hasRepresentableDiagonal_of_isAlgebraicMorphism`: **Stacks 0D3R**.

## Implementation notes

The criterion used throughout is condition (3) of Stacks 045G: a diagonal is representable by
algebraic spaces exactly when every 1-morphism from a category represented by a scheme is. So
fix a scheme `U` over `S` and a 1-morphism `x` from the category it represents into `𝒳`. The
relocalization `CategoryTheory.Over.map U.hom` is a representable category fibred in groupoids
`𝒜` equivalent to that one, and `x` factors through the 2-fibre product `𝒵 = 𝒜 ×_𝒴 𝒳` of its
composite with `f` and of `f` itself. Both legs of that factorization are representable by
algebraic spaces: the projection `𝒵 ⟶ 𝒳` is a base change of `𝒜 ⟶ 𝒴` (Stacks 0302), which is
representable because the diagonal of `𝒴` is, and the section `𝒜 ⟶ 𝒵` is representable
because `𝒵` is an algebraic stack and so has a representable diagonal. Stacks 0301 composes
them and Stacks 0457 transports the conclusion back along the equivalence.

The canonical 2-fibre product square of the cospan and its universal property are
`CategoryTheory.CatFiberedInGroupoids.twoFibreProductSquare` and
`CategoryTheory.CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare`; the apex of the
square for the cospan `(y, f)` is on the nose the category Stacks 06CF asserts to be an
algebraic stack, and `CategoryTheory.Bicategory.TwoCommSq.swap` exchanges its two projections so
that the abstract-square form of Stacks 0302 yields the projection to `𝒳`.

## References

* [Stacks Project, Tag 0D3R](https://stacks.math.columbia.edu/tag/0D3R)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.RepresentableMorphism

universe v₁ u₁

/-- **A slice relocalization is a representable category fibred in groupoids.** For an object
`U` of a category `𝒞`, the functor `CategoryTheory.Over.map U.hom : 𝒞/U.left ⥤ 𝒞` is equivalent
over `𝒞` to the slice `𝒞/U`, by the iterated-slice equivalence; so it is the fibration
represented by `U` in the sense of Stacks 02Y3. -/
theorem isRepresentableCFG_overMap {𝒞 : Type u₁} [Category.{v₁} 𝒞] {X : 𝒞} (U : Over X) :
    IsRepresentableCFG (Over.map U.hom) := by
  apply isRepresentableCFG_of_isRepresentable
  refine ⟨U, ⟨{
    hom := ⟨Over.iteratedSliceBackward U, rfl⟩
    inv := ⟨Over.iteratedSliceForward U, Over.iteratedSliceForward_comp_map U⟩
    unitIso := (Over.iteratedSliceEquiv U).counitIso.symm
    counitIso := (Over.iteratedSliceEquiv U).unitIso.symm
    unit_over := ?_
    counit_over := ?_ }⟩⟩
  all_goals
    ext V
    simp [Over.eqToHom_left, eqToHom_app, Over.iteratedSliceEquiv]
    rfl

end Stacks.RepresentableMorphism

namespace AlgebraicGeometry.Stack

universe u w w'

/-- Condition (3) of Stacks 045G from condition (1): if the diagonal of `𝒳` is representable by
algebraic spaces, then so is every 1-morphism into `𝒳` from the category represented by a
scheme over `S`. -/
private theorem isRepresentableFromSchemes_of_hasRepresentableDiagonal
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : HasRepresentableDiagonal B S hS 𝒳) :
    IsRepresentableFromSchemes B S hS 𝒳 :=
  (isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS 𝒳).mp
    ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳).mp h𝒳)

/-- Condition (5) of Stacks 045G from condition (1): if the diagonal of `𝒳` is representable by
algebraic spaces, then so is every 1-morphism into `𝒳` from a representable category fibred in
groupoids. -/
private theorem isRepresentableFromRepresentableCategories_of_hasRepresentableDiagonal
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : HasRepresentableDiagonal B S hS 𝒳) :
    IsRepresentableFromRepresentableCategories.{u, u, u + 1, u, u + 1} B S hS 𝒳 :=
  (hasAlgebraicSpaceSchemePointProducts_iff_isRepresentableFromRepresentableCategories.{
      u, u, u + 1, u, u + 1} B S hS 𝒳).mp
    ((isRepresentableFromSchemes_iff_hasAlgebraicSpaceSchemePointProducts B S hS 𝒳).mp
      (isRepresentableFromSchemes_of_hasRepresentableDiagonal B S hS 𝒳 h𝒳))

/-- **Stacks 0D3R.** An algebraic 1-morphism of stacks in groupoids over the big fppf site of
`S` inherits a diagonal representable by algebraic spaces from its target. -/
@[stacks 0D3R]
theorem hasRepresentableDiagonal_of_isAlgebraicMorphism
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : StackInGroupoids.{w, u, u, u + 1, u + 1}
      (BigFppfOver B S hS) (BigFppfOver.topology B S hS)}
    (f : 𝒳 ⟶ 𝒴)
    (hf : IsAlgebraicMorphism.{u, w, w, w'} B S hS (𝒳 := 𝒳) (𝒴 := 𝒴) f.hom)
    (h𝒴 : HasRepresentableDiagonal B S hS
      (CatFiberedInGroupoids.mk 𝒴.toBasedCategory
        𝒴.isStackInGroupoids.isFiberedInGroupoids)) :
    HasRepresentableDiagonal B S hS
      (CatFiberedInGroupoids.mk 𝒳.toBasedCategory
        𝒳.isStackInGroupoids.isFiberedInGroupoids) := by
  let X := CatFiberedInGroupoids.mk 𝒳.toBasedCategory
    𝒳.isStackInGroupoids.isFiberedInGroupoids
  let Y := CatFiberedInGroupoids.mk 𝒴.toBasedCategory
    𝒴.isStackInGroupoids.isFiberedInGroupoids
  let F : X ⟶ Y := Bicategory.InducedBicategory.mkHom f.hom
  apply (hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS X).mpr
  apply (isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS X).mpr
  intro U x
  -- `𝒜`, the relocalization of the site at `U`, is a representable category fibred in groupoids
  have hA : Stacks.RepresentableMorphism.IsRepresentableCFG (Over.map U.hom) :=
    Stacks.RepresentableMorphism.isRepresentableCFG_overMap U
  let A := CatFiberedInGroupoids.mk (BasedCategory.ofFunctor (Over.map U.hom))
    (Functor.IsFiberedInGroupoids.over_map U.hom)
  let back : A.val ⥤ᵇ (schemeFibredCategory B S hS U).val :=
    ⟨Over.iteratedSliceBackward U, rfl⟩
  let xa : A ⟶ X := Bicategory.InducedBicategory.mkHom (BasedFunctor.comp back x)
  let ya : A ⟶ Y := xa ≫ F
  -- the 2-fibre product `𝒜 ×_𝒴 𝒳`, with its two projections exchanged so that Stacks 0302
  -- speaks about the projection to `𝒳`
  let P : Bicategory.TwoCommSq F ya :=
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} ya F).swap
  have hπ : IsRepresentableByAlgebraicSpaces B S hS P.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS A Y X ya F P
      (Bicategory.isTwoFibreProduct_swap
        (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} ya F))
      (isRepresentableFromRepresentableCategories_of_hasRepresentableDiagonal B S hS Y h𝒴 A hA
        ya.hom)
  -- the tautological section of the 2-fibre product over `𝒜`
  let j : A ⟶ P.pt := Bicategory.InducedBicategory.mkHom
    ⟨TwoFibreProductOver.lift A.val.p X.val.p Y.val.p ya.hom.toFunctor F.hom.toFunctor A.val.p
      (𝟭 A.val.obj) xa.hom.toFunctor (Functor.id_comp _) xa.hom.w (Iso.refl _)
      (fun q => IsHomLift.id (ya.hom.w_obj q)),
      TwoFibreProductOver.lift_comp_structureFunctor ..⟩
  have hj : IsRepresentableByAlgebraicSpaces B S hS j.hom :=
    isRepresentableFromRepresentableCategories_of_hasRepresentableDiagonal B S hS P.pt
      (hf U ya.hom.toFunctor ya.hom.w).choose_spec.2.1 A hA j.hom
  have : back.toFunctor.IsEquivalence :=
    inferInstanceAs (Over.iteratedSliceEquiv U).inverse.IsEquivalence
  have : (BasedFunctor.id X.val).toFunctor.IsEquivalence :=
    inferInstanceAs (𝟭 X.val.obj).IsEquivalence
  exact (isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS
    (𝒳' := A) (𝒳 := schemeFibredCategory B S hS U) (𝒴' := X) (𝒴 := X)
    xa.hom x back (BasedFunctor.id X.val) (Iso.refl _)).mpr
    (isRepresentableByAlgebraicSpaces_comp B S hS j P.fst hj hπ)

end AlgebraicGeometry.Stack

end
