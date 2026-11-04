module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallIsom
public import StacksFrontier.AlgebraicGeometry.Quot.IsomorphismLocusInRelativeMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricFibreConnected
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalenceUniverses
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaProductsToDiagonal

/-!
# The diagonal of `Curves` from the algebraicity of the `Isom` functors (towards Stacks 0D53)

Stacks 0D53 says that the diagonal of the stack of curves is representable by algebraic spaces.
By criterion (2) of Stacks 045G this is the statement that for every scheme `U` and all objects
`x`, `y` of the fibre over `U` the isomorphism sheaf `Isom(x, y)` is an algebraic space over `U`.
This file reduces it to the concrete statement
`AlgebraicGeometry.C1590Private.CurveIsomFunctorsAlgebraic`: for all families of curves `F`, `G`
over a common base `U`, the functor `Isom_U(F, G)` of `AlgebraicGeometry.CurveFamily.isomFunctor`
(Stacks 0DPP), a presheaf on the big fppf site of `Spec(ℤ)`, is an algebraic space.

* On the small model `AlgebraicGeometry.curvesSmall`, the isomorphism sheaf of two objects over
  `U`, viewed over `Spec(ℤ)` (Stacks 04SG), is `Isom_U(F, G)`:
  `AlgebraicGeometry.curvesSmall.nonempty_arrowIso_isomFunctorProjection`. A presheaf over `U`
  whose extension to `Spec(ℤ)` is an algebraic space is an algebraic space over `U`
  (the converse of Stacks 03I5 (2)), which gives criterion (2) of Stacks 045G for the small model.
* The diagonal clause passes from the small model to `AlgebraicGeometry.curvesFiberedCategory`
  along `AlgebraicGeometry.curvesSmallEquivalenceOver`, through condition (3) of Stacks 045G,
  which transports along equivalences over the site in independent universes.

## Main definitions

* `AlgebraicGeometry.C1590Private.CurveIsomFunctorsAlgebraic`: every `Isom_U(F, G)` is an
  algebraic space.
* `AlgebraicGeometry.C1590Private.CurveMorFunctorsAlgebraic`: every `Mor_U(F, G)` is an
  algebraic space.

## Main results

* `AlgebraicGeometry.C1590Private.isAlgebraicSpace_of_isAlgebraicSpace_relocalizePresheaf`: the
  converse of Stacks 03I5 (2).
* `AlgebraicGeometry.C1590Private.curveIsomFunctorsAlgebraic_of_curveMorFunctorsAlgebraic`:
  `Isom_U(F, G)` is open in `Mor_U(F, G)` (Stacks 0DPP).
* `AlgebraicGeometry.C1590Private.hasRepresentableDiagonal_curvesFiberedCategory_of_curvesSmall`:
  the diagonal clause passes from the small model to the stack of curves.
* `C1590Private.hasRepresentableDiagonal_curvesFiberedCategory_of_curveIsomFunctorsAlgebraic`:
  the reduction.

## Implementation notes

Nothing here carries a `stacks` attribute: the last result takes the algebraicity of the `Isom`
functors, which the source proves, as an argument.

## References

* [Stacks Project, Tag 0D53](https://stacks.math.columbia.edu/tag/0D53)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.C1590Private

/-- **The converse of Stacks 03I5 part (2).** If the lower-shriek extension of a presheaf `F` on
the big fppf site of `T` along `g : T ⟶ S` is an algebraic space over `S`, then `F` is an
algebraic space over `T`: by `CategoryTheory.OverShriek.isPullback_relocalizeUnit` it is the
fibre product of the restriction of the extension with the representable presheaf of `T`, over
the restriction of the representable presheaf of `g`, all three algebraic spaces over `T` by
Stacks 03I5 part (1). -/
theorem isAlgebraicSpace_of_isAlgebraicSpace_relocalizePresheaf (B : BigFppfSite.{u})
    {S : Scheme.{u}} {hS : B.Contains S} (T : Scheme.{u}) (hT : B.Contains T)
    (g : B.obj hT ⟶ B.obj hS) (F : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS ((OverShriek.relocalizePresheafFunctor g).obj F)) :
    IsAlgebraicSpace B T hT F := by
  have hH : IsAlgebraicSpace B T hT
      ((OverShriek.relocalizeRestrict g).obj (yoneda.obj (Over.mk g))) :=
    isAlgebraicSpace_relocalizeRestrict B T S hT hS g (yoneda.obj (Over.mk g))
      (isAlgebraicSpace_yoneda B S hS (Over.mk g))
  exact isAlgebraicSpace_of_isPullback
    (isAlgebraicSpace_relocalizeRestrict B T S hT hS g _ hF)
    (isAlgebraicSpace_yoneda B T hT (Over.mk (𝟙 (B.obj hT))))
    hH.isSheaf hH.diagonal_representable (OverShriek.isPullback_relocalizeUnit g F)

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **The `Isom` functors of families of curves are algebraic spaces.** For all families of
curves `F` and `G` over a common base `U` (the family `G` read over the base of `F` through
`h`), the functor `Isom_U(F, G)` of Stacks 0DPP on the big fppf site of `Spec(ℤ)` is an
algebraic space. -/
def CurveIsomFunctorsAlgebraic : Prop :=
  ∀ (F G : CurveFamily B hZ) (h : G.base = F.base),
    IsAlgebraicSpace B integerBase hZ
      (CurveFamily.isomFunctor F G (G.toBase.hom ≫ yoneda.map (eqToHom h))).toFunctor

/-- **The relative morphism functors of families of curves are algebraic spaces.** For all
families of curves `F` and `G` over a common base `U` (the family `G` read over the base of `F`
through `h`), the functor `Mor_U(F, G)` of Stacks 05Y2 on the big fppf site of `Spec(ℤ)` is an
algebraic space. -/
def CurveMorFunctorsAlgebraic : Prop :=
  ∀ (F G : CurveFamily B hZ) (h : G.base = F.base),
    IsAlgebraicSpace B integerBase hZ
      (Space.relativeHom B integerBase hZ F.total.obj G.total.obj (schemeSpace F.base).obj
        F.toBase.hom (G.toBase.hom ≫ yoneda.map (eqToHom h)) F.total.property
        G.total.property (schemeSpace F.base).property)

/-- **`Isom_U(F, G)` from `Mor_U(F, G)`.** If the relative morphism functors of families of
curves are algebraic spaces, so are their `Isom` functors: `Isom_U(F, G)` is an open subspace of
`Mor_U(F, G)` by Stacks 0DPP, the family `F` being of finite presentation, flat and proper and
`G` proper over the common base. -/
theorem curveIsomFunctorsAlgebraic_of_curveMorFunctorsAlgebraic
    (hM : CurveMorFunctorsAlgebraic B hZ) : CurveIsomFunctorsAlgebraic B hZ := by
  intro F G h
  have hxp : Space.IsProper B integerBase hZ (G.toBase.hom ≫ yoneda.map (eqToHom h)) :=
    (Space.isProper_comp_isIso_iff B integerBase hZ _ (yoneda.map (eqToHom h))).2 G.proper
  exact (Space.isOpenSubspace_isomSubfunctor B integerBase hZ F.total.obj G.total.obj
    (schemeSpace F.base).obj F.toBase.hom (G.toBase.hom ≫ yoneda.map (eqToHom h))
    F.total.property G.total.property (schemeSpace F.base).property F.finitePresentation F.flat
    F.proper hxp (hM F G h)).1

/-- **The diagonal of `Curves` from that of its small model.** Condition (1) of Stacks 045G for
`AlgebraicGeometry.curvesSmall` gives condition (3), which transports along the equivalence
over the site `AlgebraicGeometry.curvesSmallEquivalenceOver` in independent universes, and
condition (3) for `AlgebraicGeometry.curvesFiberedCategory` gives back condition (1). -/
theorem hasRepresentableDiagonal_curvesFiberedCategory_of_curvesSmall
    (h : Stack.HasRepresentableDiagonal B integerBase hZ (curvesSmall B hZ)) :
    Stack.HasRepresentableDiagonal B integerBase hZ (curvesFiberedCategory B hZ) := by
  rw [Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf,
    Stack.isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes] at h ⊢
  exact Stack.isRepresentableFromSchemes_of_equivalenceOver B integerBase hZ
    (curvesSmallEquivalenceOver B hZ).symm.toBasedEquivalence h

variable {B hZ} in
/-- **The isomorphism sheaf of two objects of the small model of `Curves` is an algebraic space**
over their common base `U`, as soon as the `Isom` functors of families of curves are: viewed over
`Spec(ℤ)` it is `Isom_U(F, G)`
(`AlgebraicGeometry.curvesSmall.nonempty_arrowIso_isomFunctorProjection`). -/
theorem isAlgebraicSpace_isomSpace_curvesSmall (hI : CurveIsomFunctorsAlgebraic B hZ)
    {U : BigFppfOver B integerBase hZ} (y₁ y₂ : (curvesSmall B hZ).val.p.Fiber U) :
    IsAlgebraicSpace B U.left.1 U.left.2
      (Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y₁ y₂) := by
  obtain ⟨e⟩ := curvesSmall.nonempty_arrowIso_isomFunctorProjection y₁ y₂
  have hG := hI (ShrinkHoms.fromShrinkHoms y₁.1 : CurveFamily B hZ)
    (ShrinkHoms.fromShrinkHoms y₂.1 : CurveFamily B hZ) (y₂.2.trans y₁.2.symm)
  refine isAlgebraicSpace_of_isAlgebraicSpace_relocalizePresheaf B U.left.1 U.left.2 U.hom _ ?_
  exact isAlgebraicSpace_of_iso B integerBase hZ (Arrow.leftFunc.mapIso e) hG

/-- **Stacks 0D53 from the algebraicity of the `Isom` functors.** If `Isom_U(F, G)` is an
algebraic space for all families of curves `F`, `G` over a common base, then the diagonal of the
stack of curves is representable by algebraic spaces: criterion (2) of Stacks 045G holds for the
small model (`AlgebraicGeometry.C1590Private.isAlgebraicSpace_isomSpace_curvesSmall`), and the
diagonal clause passes to `AlgebraicGeometry.curvesFiberedCategory`. -/
theorem hasRepresentableDiagonal_curvesFiberedCategory_of_curveIsomFunctorsAlgebraic
    (hI : CurveIsomFunctorsAlgebraic B hZ) :
    Stack.HasRepresentableDiagonal B integerBase hZ (curvesFiberedCategory B hZ) :=
  hasRepresentableDiagonal_curvesFiberedCategory_of_curvesSmall B hZ
    ((Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B integerBase hZ
      (curvesSmall B hZ)).mpr fun _ y₁ y₂ =>
        ⟨_, isAlgebraicSpace_isomSpace_curvesSmall hI y₁ y₂, ⟨Iso.refl _⟩⟩)

end AlgebraicGeometry.C1590Private

end
