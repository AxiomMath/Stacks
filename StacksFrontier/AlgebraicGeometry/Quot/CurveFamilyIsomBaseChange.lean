module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyAutomorphisms
public import StacksFrontier.AlgebraicGeometry.Quot.IsomorphismLocusBaseChange

/-!
# Base change of `Isom_U(Y, X)` for families of curves

Let `Y ⟶ U` and `X ⟶ U` be families of curves over a common base `U`, and let `U' ⟶ U` be a
morphism of schemes. The morphisms of `AlgebraicGeometry.CurveFamily` are cartesian, so two
morphisms `Y' ⟶ Y` and `X' ⟶ X` of families of curves over `U' ⟶ U` present `Y'` and `X'` as
base changes of `Y` and `X`. Then the projection `Isom_{U'}(Y', X') ⟶ U'` is a base change of
the projection `Isom_U(Y, X) ⟶ U` along `U' ⟶ U`: this is Stacks 05Y4 for the subfunctor of
isomorphisms (`AlgebraicGeometry.Space.exists_isPullback_isomSubfunctor_of_isPullback`).

This is the base change step of the quasi-compactness argument for `Isom_U(Y, X)` in the proof
of Stacks 0DSQ: quasi-compactness of `Isom_U(Y, X) ⟶ U` is tested on affine schemes over `U`,
over which the families descend to a Noetherian base.

## Main results

* `AlgebraicGeometry.CurveFamily.exists_isPullback_isomFunctorProjection`: for a morphism
  `X' ⟶ X` of families whose total spaces are given structure morphisms to the bases of `Y'`
  and `Y` forming a cartesian square.
* `AlgebraicGeometry.CurveFamily.exists_isPullback_isomFunctorProjection_eqToHom`: the same for
  families over the same bases as `Y'` and `Y`, read over them through the identifications of the
  bases, which is the form of the projections in the proof of Stacks 0DSQ.

## References

* [Stacks Project, Tag 05Y4](https://stacks.math.columbia.edu/tag/05Y4)
* [Stacks Project, Tag 0DPP](https://stacks.math.columbia.edu/tag/0DPP)
* [Stacks Project, Tag 0DSQ](https://stacks.math.columbia.edu/tag/0DSQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace CurveFamily

/-- **`Isom_{U'}(Y', X') = U' ×_U Isom_U(Y, X)`.** For a morphism `φ : Y' ⟶ Y` of families of
curves over `b : U' ⟶ U`, and structure morphisms `x` and `x'` of the total spaces of families
`X` and `X'` to `U` and `U'` with a morphism `ψ : X' ⟶ X` of total spaces making the square over
`b` cartesian, the projection `Isom_{U'}(Y', X') ⟶ U'` is a base change of the projection
`Isom_U(Y, X) ⟶ U` along `b`. -/
theorem exists_isPullback_isomFunctorProjection {F G F' G' : CurveFamily B hZ} (φ : F' ⟶ F)
    (ψ : G'.total ⟶ G.total) (x : G.total.obj ⟶ (schemeSpace F.base).obj)
    (x' : G'.total.obj ⟶ (schemeSpace F'.base).obj)
    (hx : IsPullback ψ.hom x' x (yoneda.map φ.baseMap)) :
    ∃ g : (isomFunctor F' G' x').toFunctor ⟶ (isomFunctor F G x).toFunctor,
      IsPullback g (isomFunctorProjection F' G' x') (isomFunctorProjection F G x)
        (yoneda.map φ.baseMap) :=
  Space.exists_isPullback_isomSubfunctor_of_isPullback F.toBase.hom x (yoneda.map φ.baseMap)
    F'.toBase.hom x' φ.totalMap.hom ψ.hom
    (AlgebraicSpaces.isPullback_hom B integerBase hZ φ.cartesian) hx _ _ _ _ _ _

/-- **`Isom_{U'}(Y', X') = U' ×_U Isom_U(Y, X)`, for families over the bases of `Y'` and `Y`.**
For morphisms `φ : Y' ⟶ Y` and `ψ : X' ⟶ X` of families of curves whose base maps agree under
identifications `X.base = Y.base` and `X'.base = Y'.base`, the projection
`Isom_{U'}(Y', X') ⟶ U'` is a base change of the projection `Isom_U(Y, X) ⟶ U` along the base
map of `φ`, the families `X` and `X'` being read over the bases of `Y` and `Y'` through the two
identifications. -/
theorem exists_isPullback_isomFunctorProjection_eqToHom {F G F' G' : CurveFamily B hZ}
    (φ : F' ⟶ F) (ψ : G' ⟶ G) (hb : G.base = F.base) (hb' : G'.base = F'.base)
    (hφψ : ψ.baseMap ≫ eqToHom hb = eqToHom hb' ≫ φ.baseMap) :
    ∃ g : (isomFunctor F' G' (G'.toBase.hom ≫ yoneda.map (eqToHom hb'))).toFunctor ⟶
        (isomFunctor F G (G.toBase.hom ≫ yoneda.map (eqToHom hb))).toFunctor,
      IsPullback g (isomFunctorProjection F' G' (G'.toBase.hom ≫ yoneda.map (eqToHom hb')))
        (isomFunctorProjection F G (G.toBase.hom ≫ yoneda.map (eqToHom hb)))
        (yoneda.map φ.baseMap) := by
  have hsq : IsPullback (yoneda.map ψ.baseMap) (yoneda.map (eqToHom hb'))
      (yoneda.map (eqToHom hb)) (yoneda.map φ.baseMap) :=
    IsPullback.of_vert_isIso ⟨by rw [← Functor.map_comp, ← Functor.map_comp, hφψ]⟩
  exact exists_isPullback_isomFunctorProjection φ ψ.totalMap _ _
    ((AlgebraicSpaces.isPullback_hom B integerBase hZ ψ.cartesian).paste_vert hsq)

end CurveFamily

end AlgebraicGeometry

end
