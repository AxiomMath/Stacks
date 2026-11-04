module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningFunctorLimitPreserving

/-!
# Flatness of a module over a limit of affine test schemes holds at a stage

Let `f : X ⟶ Y` be a quasi-compact morphism of algebraic spaces over a scheme `S` which is
locally of finite presentation, and let `F` be a quasi-coherent `𝒪_X`-module of finite
presentation. Let `T = lim T_i` be a cofiltered limit of affine schemes over `Y`. If the pullback
`F_T` of `F` to `X_T = X ×_Y T` is flat over `T`, then the pullback `F_{T_i}` to `X_{T_i}` is flat
over `T_i` for some `i`.

This is the content of limit preservation of the flattening functor `F_flat` (Stacks 0CWZ,
part (2)), read without the functor: `F_flat` takes values in the sets with at most one element,
so its limit preservation is exactly the existence of such a stage. It is the descent of
flatness along limits of algebraic spaces of Stacks 08K0 for a limit of affine schemes, stated
over the test schemes of `Y`.

## Main results

* `AlgebraicGeometry.Space.FlatnessSituation.exists_isFlatAfterBaseChange_of_isLimit`: the
  statement above.

## References

* [Stacks Project, Tag 0CWZ](https://stacks.math.columbia.edu/tag/0CWZ)
* [Stacks Project, Tag 08K0](https://stacks.math.columbia.edu/tag/08K0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.FlatnessSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Flatness over a cofiltered limit of affine test schemes holds at a stage.** For `f`
quasi-compact and locally of finite presentation and `F` of finite presentation, if `F_T` is flat
over the limit `T = lim T_i` of affine test schemes over `Y`, then `F_{T_i}` is flat over `T_i`
for some `i`. -/
theorem exists_isFlatAfterBaseChange_of_isLimit (D : FlatnessSituation.{u} B S hS)
    (hqc : IsQuasiCompact B S hS D.f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS D.f.hom)
    (hFfp : SheafOfModules.IsFinitePresentationOnSite D.F)
    {I : Type u} [Category.{u} I] [IsCofiltered I] (E : I ⥤ SchemesOver D.Y) (c : Cone E)
    (hc : IsLimit (D.testScheme.mapCone c)) (haff : ∀ i, IsAffine (D.testScheme.obj (E.obj i)))
    (hpt : IsAffine (D.testScheme.obj c.pt)) (hflat : D.IsFlatAfterBaseChange c.pt) :
    ∃ i, D.IsFlatAfterBaseChange (E.obj i) :=
  (D.flatFunctor_limitPreserving_iff.mp (D.flatFunctor_limitPreserving hqc hlfp hFfp)) I E c hc
    haff hpt hflat

end AlgebraicGeometry.Space.FlatnessSituation

end
