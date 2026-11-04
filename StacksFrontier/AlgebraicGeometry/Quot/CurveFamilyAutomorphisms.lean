module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies
public import StacksFrontier.AlgebraicGeometry.Quot.IsomorphismLocusInRelativeMorphisms

/-!
# The Isom and Aut functors of families of curves

Let `F` and `G` be families of curves with `G` lying over the base `U` of `F`. The functor
`Isom_U(F, G)` on schemes over `U` takes `T` to the `T`-isomorphisms `F_T ≅ G_T`, and
`Aut_U(F) = Isom_U(F, F)`. These are the objects of Stacks 0DSQ, whose proof computes the
diagonal of `Curves` through them, and of Stacks 0DSW and 0E6G, which ask when `Aut_U(F)` is
unramified over `U`.

Both are thin instances of the subfunctor `Isom_Q(Z, X) ⊆ Mor_Q(Z, X)` of relative isomorphisms
of Stacks 0DPP (`AlgebraicGeometry.Space.isomSubfunctor`), at the total spaces of the families
over the scheme `U` read as an algebraic space.

## Main definitions

* `AlgebraicGeometry.CurveFamily.isomFunctor`: `Isom_U(F, G)`, for `F` over `U` and a structure
  morphism of the total space of `G` to `U`.
* `AlgebraicGeometry.CurveFamily.isomFunctorProjection`: its projection to `U`.
* `AlgebraicGeometry.CurveFamily.autFunctor`: `Aut_U(F) = Isom_U(F, F)`.
* `AlgebraicGeometry.CurveFamily.autFunctorProjection`: its projection to `U`.

## References

* [Stacks Project, Tag 0DPP](https://stacks.math.columbia.edu/tag/0DPP)
* [Stacks Project, Tag 0DSQ](https://stacks.math.columbia.edu/tag/0DSQ)
* [Stacks Project, Tag 0DSW](https://stacks.math.columbia.edu/tag/0DSW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace CurveFamily

/-- **`Isom_U(F, G)`.** For a family of curves `F` over `U` and a family `G` whose total space is
given the structure morphism `x` to `U`, the subfunctor of `Mor_U(F, G)` whose sections over a
scheme `T` over `U` are the pairs whose morphism of base changes `F_T ⟶ G_T` is an isomorphism
(Stacks 0DPP). -/
noncomputable def isomFunctor (F G : CurveFamily B hZ)
    (x : G.total.obj ⟶ (schemeSpace F.base).obj) :
    Subfunctor (Space.relativeHom B integerBase hZ F.total.obj G.total.obj
      (schemeSpace F.base).obj F.toBase.hom x F.total.property G.total.property
      (schemeSpace F.base).property) :=
  Space.isomSubfunctor B integerBase hZ F.total.obj G.total.obj
    (schemeSpace F.base).obj F.toBase.hom x F.total.property G.total.property
    (schemeSpace F.base).property

/-- The sections of `Isom_U(F, G)` over a scheme are the pairs of Stacks 05Y1 which are relative
isomorphisms. -/
theorem mem_isomFunctor_iff (F G : CurveFamily B hZ)
    (x : G.total.obj ⟶ (schemeSpace F.base).obj) (T : BigFppfOver B integerBase hZ)
    (s : (Space.relativeHom B integerBase hZ F.total.obj G.total.obj
      (schemeSpace F.base).obj F.toBase.hom x F.total.property G.total.property
      (schemeSpace F.base).property).obj (Opposite.op T)) :
    s ∈ (isomFunctor F G x).obj (Opposite.op T) ↔
      (Space.relativeHomSections B integerBase hZ F.total.obj G.total.obj
        (schemeSpace F.base).obj F.toBase.hom x F.total.property
        G.total.property (schemeSpace F.base).property T s).IsRelativeIso :=
  Iff.rfl

/-- The projection `Isom_U(F, G) ⟶ U`. -/
noncomputable def isomFunctorProjection (F G : CurveFamily B hZ)
    (x : G.total.obj ⟶ (schemeSpace F.base).obj) :
    (isomFunctor F G x).toFunctor ⟶ (schemeSpace F.base).obj :=
  (isomFunctor F G x).ι ≫ Space.relativeHomProjection B integerBase hZ F.total.obj G.total.obj
    (schemeSpace F.base).obj F.toBase.hom x F.total.property G.total.property
    (schemeSpace F.base).property

/-- **`Aut_U(F)`.** The automorphism functor of a family of curves `F` over `U`: the sections
over a scheme `T` over `U` are the automorphisms of `F_T` over `T`. It is `Isom_U(F, F)`. -/
noncomputable abbrev autFunctor (F : CurveFamily B hZ) :
    Subfunctor (Space.relativeHom B integerBase hZ F.total.obj F.total.obj
      (schemeSpace F.base).obj F.toBase.hom F.toBase.hom F.total.property
      F.total.property (schemeSpace F.base).property) :=
  isomFunctor F F F.toBase.hom

/-- The projection `Aut_U(F) ⟶ U`. -/
noncomputable abbrev autFunctorProjection (F : CurveFamily B hZ) :
    (autFunctor F).toFunctor ⟶ (schemeSpace F.base).obj :=
  isomFunctorProjection F F F.toBase.hom

end CurveFamily

end AlgebraicGeometry
