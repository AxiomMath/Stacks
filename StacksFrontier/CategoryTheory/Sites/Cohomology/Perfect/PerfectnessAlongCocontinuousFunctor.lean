module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectnessAlongAnExactFunctor

/-!
# Perfectness along a cocontinuous functor of sites with exact slice squares

Let `(C, O)` and `(D, O')` be ringed sites, let `v : C ⥤ D` be a cocontinuous functor and let
`F : Mod(O') ⥤ Mod(O)` be an additive functor.  Suppose that for every object `U` of `C` there is
an exact additive functor `F_U : Mod(O'|_{v(U)}) ⥤ Mod(O|_U)` carrying the unit to the unit,
together with a *localization square*

```
  (- |_{v(U)}) ⋙ F_U  ≅  F ⋙ (- |_U) .
```

Then `F` carries a perfect complex of `O'`-modules to a perfect complex of `O`-modules, and —
when `F` is itself exact — a perfect object of `D(O')` to a perfect object of `D(O)`.

This is the companion of
`AlgebraicGeometry.RingedSite.isPerfectComplex_mapHomologicalComplex`, whose functor of sites
`u : D ⥤ C` runs from the source of `F` to its target and whose image covers the final object.
Here the functor of sites runs the other way, from the target of `F` to its source, and what
replaces the covering hypothesis is cocontinuity: a covering of `v(U)` on which the source complex
has local models pulls back to a covering of `U`.  That is the shape of the two transports this
development needs:

* restriction of sections along a continuous functor `v` — the pullback of modules along an étale
  morphism of algebraic spaces is restriction along postcomposition of charts, which is
  cocontinuous and is an equivalence on every slice;
* reindexing along an equivalence of sites, `v` being the functor of the equivalence.

In both cases the slice functor `F_U` is restriction along the induced equivalence of slices, and
the square holds with the identity comparison of sections.

## Main results

* `AlgebraicGeometry.RingedSite.hasStrictlyPerfectQuasiIso_map_of_square`: the square at one
  object carries a strictly perfect local model over `v(U)` to one over `U`.
* `AlgebraicGeometry.RingedSite.isPerfectComplex_mapHomologicalComplex_of_isCocontinuous`: the
  transfer of perfectness of complexes.
* `AlgebraicGeometry.RingedSite.isPerfect_mapDerivedCategory_of_isCocontinuous`: the transfer in
  the derived category, for `F` exact, with the typeclass hypotheses on `F` and the `F_U` passed
  explicitly so that it can be applied at concrete sites whose structure sheaves are spelled
  differently from `AlgebraicGeometry.RingedSite.ringSheaf`.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uX vX uY vY w dX dY

namespace AlgebraicGeometry.RingedSite

section Cocontinuous

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ W : Y.C, HasSheafify (Y.J.over W) AddCommGrpCat.{w}]
  [∀ W : Y.C, (Y.J.over W).WEqualsLocallyBijective AddCommGrpCat.{w}]

variable (v : X.C ⥤ Y.C)

/-- **The image of a strictly perfect local model over `v(U)` is one over `U`.**  Apply `F_U`
degreewise: strict perfectness is preserved because `F_U` is additive, preserves finite colimits
and carries the unit to the unit; the quasi-isomorphism is preserved because `F_U` is exact; and
the target is identified with `(F K)|_U` by the localization square read on complexes. -/
theorem hasStrictlyPerfectQuasiIso_map_of_square
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) [F.Additive]
    (G : ∀ U : X.C,
      SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over (v.obj U)) ⥤
        SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    (U : X.C) [(G U).Additive]
    [PreservesFiniteLimits (G U)] [PreservesFiniteColimits (G U)]
    (ηG : (G U).obj (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over (v.obj U))) ≅
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    (sq : SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (v.obj U) ⋙
        G U ≅ F ⋙ SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (h : Y.HasStrictlyPerfectQuasiIso K (v.obj U)) :
    X.HasStrictlyPerfectQuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) U := by
  obtain ⟨P, hP, q, hq⟩ := h
  have hSP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)
      (((G U).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
    SheafOfModules.isStrictlyPerfect_map.{max uY vY, max uX vX, vY, vX, w} (G U) ηG hP
  let hcmp :
      (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
          (v.obj U)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (G U).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          U).mapHomologicalComplex (ComplexShape.up ℤ) :=
    Functor.mapHomologicalComplexCompIso
        (Iso.refl (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
          (v.obj U) ⋙ G U)) (ComplexShape.up ℤ) ≪≫
      NatIso.mapHomologicalComplex sq (ComplexShape.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso
          (Iso.refl (F ⋙ SheafOfModules.overFunctor.{w}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)) (ComplexShape.up ℤ)).symm
  have := hq
  exact ⟨_, hSP, ((G U).mapHomologicalComplex (ComplexShape.up ℤ)).map q ≫ (hcmp.app K).hom,
    inferInstance⟩

/-- **Perfectness of complexes transfers along an additive functor with exact localization
squares over a cocontinuous functor of sites.**  If `K` is a perfect complex of `O'`-modules then
the degreewise image `F K` is a perfect complex of `O`-modules.

Over an object `U` of `C`, perfectness of `K` at `v(U)` gives a covering presieve of `v(U)` all of
whose members carry strictly perfect local models.  The sieve it generates pulls back along `v`
to a covering sieve of `U`, by cocontinuity.  For an arrow `g : V ⟶ U` of that sieve, `v(g)`
factors through a member of the presieve, so the model descends to `v(V)`
(`hasStrictlyPerfectQuasiIso_of_hom`) and is carried to `V` by `F_V`
(`hasStrictlyPerfectQuasiIso_map_of_square`). -/
theorem isPerfectComplex_mapHomologicalComplex_of_isCocontinuous
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) [F.Additive]
    (G : ∀ U : X.C,
      SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over (v.obj U)) ⥤
        SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    [v.IsCocontinuous X.J Y.J]
    [∀ U : X.C, (G U).Additive]
    [∀ U : X.C, PreservesFiniteLimits (G U)]
    [∀ U : X.C, PreservesFiniteColimits (G U)]
    (ηG : ∀ U : X.C, (G U).obj (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over (v.obj U))) ≅
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    (sq : ∀ U : X.C,
      SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (v.obj U) ⋙
        G U ≅ F ⋙ SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Y.IsPerfectComplex K) :
    X.IsPerfectComplex ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  rw [isPerfectComplex_iff]
  intro U
  obtain ⟨S, hS, hmodels⟩ := (isPerfectComplex_iff Y K).1 hK (v.obj U)
  refine ⟨((Sieve.generate S).functorPullback v).arrows, ?_, ?_⟩
  · rw [Sieve.generate_sieve]
    exact v.cover_lift X.J Y.J hS
  · intro V g hg
    obtain ⟨W, h, k, hk, hfac⟩ := hg
    exact hasStrictlyPerfectQuasiIso_map_of_square v F G V (ηG V) (sq V) K
      (hasStrictlyPerfectQuasiIso_of_hom Y K h (hmodels k hk))

/-- **Perfectness in the derived category transfers along an exact additive functor with exact
localization squares over a cocontinuous functor of sites.**  If `E` is a perfect object of
`D(O')` then `F.mapDerivedCategory.obj E` is a perfect object of `D(O)`.

The typeclass hypotheses on `F` and on the `F_U` are explicit arguments, so that the statement
applies at concrete sites where those instances are stated at a spelling of the structure sheaves
that instance search does not identify with `AlgebraicGeometry.RingedSite.ringSheaf`. -/
theorem isPerfect_mapDerivedCategory_of_isCocontinuous
    [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasDerivedCategory.{dY} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    [HasDerivedCategory.{dX} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (G : ∀ U : X.C,
      SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over (v.obj U)) ⥤
        SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    (hFadd : F.Additive) (hFlim : PreservesFiniteLimits F) (hFcolim : PreservesFiniteColimits F)
    (hGadd : ∀ U : X.C, (G U).Additive)
    (hGlim : ∀ U : X.C, PreservesFiniteLimits (G U))
    (hGcolim : ∀ U : X.C, PreservesFiniteColimits (G U))
    (hv : v.IsCocontinuous X.J Y.J)
    (ηG : ∀ U : X.C, (G U).obj (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over (v.obj U))) ≅
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    (sq : ∀ U : X.C,
      SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (v.obj U) ⋙
        G U ≅ F ⋙ SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hE : Y.IsPerfect E) :
    haveI := hFadd
    haveI := hFlim
    haveI := hFcolim
    X.IsPerfect (F.mapDerivedCategory.obj E) := by
  have := hFadd
  have := hFlim
  have := hFcolim
  have := hGadd
  have := hGlim
  have := hGcolim
  have := hv
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  refine ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K,
    isPerfectComplex_mapHomologicalComplex_of_isCocontinuous v F G ηG sq K hK, ⟨?_⟩⟩
  exact (F.mapDerivedCategoryFactors.app K).symm ≪≫ F.mapDerivedCategory.mapIso e

end Cocontinuous

end AlgebraicGeometry.RingedSite

end
