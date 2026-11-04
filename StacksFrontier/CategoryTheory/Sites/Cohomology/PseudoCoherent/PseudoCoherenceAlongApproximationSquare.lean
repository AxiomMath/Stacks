module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherenceAlongAnExactFunctor

/-!
# Pseudo-coherence along a functor whose localizations preserve approximations

Let `(C, O)` and `(D, O')` be ringed sites, let `u : D ⥤ C` be a continuous functor whose image
covers the final object of `Sh(C)`, let `F : Mod(O') ⥤ Mod(O)` be an additive functor and `K` a
complex of `O'`-modules.  Suppose that for every object `W` of `D` there is an additive
`F_W : Mod(O'|_W) ⥤ Mod(O|_{u(W)})` preserving finite colimits and carrying the unit to the
unit, with a localization square `(- |_W) ⋙ F_W ≅ F ⋙ (- |_{u(W)})`, and that `F_W` carries a
strictly perfect approximation of `K|_W` in degrees `> m` to an approximation in degrees `> m`.
If `K` is `m`-pseudo-coherent, then so is the degreewise image `F K`.

`AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_mapHomologicalComplex` is the case
where every `F_W` is exact, in which the preservation of approximations is automatic.  The form
here is the one the derived pullback along a morphism of ringed topoi needs, Stacks 08H4: the
localized pullbacks are not exact, but they do preserve an approximation between K-flat
complexes with flat terms.

## Main results

* `AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_mapHomologicalComplex_of_approx`:
  the transfer of `m`-pseudo-coherence of complexes.

## References

* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08H4](https://stacks.math.columbia.edu/tag/08H4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uX vX uY vY w

namespace AlgebraicGeometry.RingedSite

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ W : Y.C, HasSheafify (Y.J.over W) AddCommGrpCat.{w}]
  [∀ W : Y.C, (Y.J.over W).WEqualsLocallyBijective AddCommGrpCat.{w}]

variable (u : Y.C ⥤ X.C)
  (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  (G : ∀ W : Y.C, SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W) ⥤
    SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (u.obj W)))

/-- **The image of a strictly perfect approximation is one over the image object**, for a
localized functor which preserves approximations of `K|_W`. -/
theorem hasStrictlyPerfectApproximation_map_of_approx [F.Additive] (W : Y.C) [(G W).Additive]
    [PreservesFiniteColimits (G W)]
    (ηG : (G W).obj (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W)) ≅
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (u.obj W)))
    (sq : SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) W ⋙ G W ≅
      F ⋙ SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (u.obj W))
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (m : ℤ)
    (happrox : ∀ (P : CochainComplex
        (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W)) ℤ),
      IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W) P →
      ∀ α : P ⟶ Y.restrictComplex K W,
        (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) →
        Epi (HomologicalComplex.homologyMap α m) →
        (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap
          (((G W).mapHomologicalComplex (ComplexShape.up ℤ)).map α) j)) ∧
        Epi (HomologicalComplex.homologyMap
          (((G W).mapHomologicalComplex (ComplexShape.up ℤ)).map α) m))
    (h : Y.HasStrictlyPerfectApproximation K m W) :
    X.HasStrictlyPerfectApproximation
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) m (u.obj W) := by
  obtain ⟨P, hP, α, hiso, hepi⟩ := h
  have hSP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (u.obj W))
      (((G W).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
    SheafOfModules.isStrictlyPerfect_map.{max uY vY, max uX vX, vY, vX, w} (G W) ηG hP
  have hcmp := (squareComplexIso u F G W sq).app K
  obtain ⟨hiso', hepi'⟩ := happrox P hP α hiso hepi
  refine ⟨_, hSP, ((G W).mapHomologicalComplex (ComplexShape.up ℤ)).map α ≫ hcmp.hom, ?_, ?_⟩
  · exact fun j hj => isIso_homologyMap_comp_iso _ hcmp j (hiso' j hj)
  · exact epi_homologyMap_comp_iso _ hcmp m hepi'

/-- **Pseudo-coherence of complexes transfers along an additive functor whose localizations
preserve approximations.**  If `K` is an `m`-pseudo-coherent complex of `O'`-modules, every
localized functor `F_W` is additive, preserves finite colimits, carries the unit to the unit and
carries a strictly perfect approximation of `K|_W` in degrees `> m` to one, then the degreewise
image `F K` is an `m`-pseudo-coherent complex of `O`-modules. -/
theorem isPseudoCoherentComplexFrom_mapHomologicalComplex_of_approx (hFadd : F.Additive)
    (hu : u.IsContinuous Y.J X.J) (hTop : X.J.CoversTop u.obj)
    (hGadd : ∀ W : Y.C, (G W).Additive)
    (hGcolim : ∀ W : Y.C, PreservesFiniteColimits (G W))
    (ηG : ∀ W : Y.C,
      (G W).obj (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W)) ≅
        SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (u.obj W)))
    (sq : ∀ W : Y.C,
      SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) W ⋙ G W ≅
        F ⋙ SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (u.obj W))
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (m : ℤ)
    (happrox : ∀ (W : Y.C) (P : CochainComplex
        (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W)) ℤ),
      IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W) P →
      ∀ α : P ⟶ Y.restrictComplex K W,
        (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) →
        Epi (HomologicalComplex.homologyMap α m) →
        (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap
          (((G W).mapHomologicalComplex (ComplexShape.up ℤ)).map α) j)) ∧
        Epi (HomologicalComplex.homologyMap
          (((G W).mapHomologicalComplex (ComplexShape.up ℤ)).map α) m))
    (hK : Y.IsPseudoCoherentComplexFrom K m) :
    X.IsPseudoCoherentComplexFrom
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) m := by
  have := hFadd
  have := hu
  have := hGadd
  have := hGcolim
  have hcover : X.J.CoversTop
      (fun W : {W : Y.C // Y.HasStrictlyPerfectApproximation K m W} => u.obj W.val) :=
    CategoryTheory.GrothendieckTopology.coversTop_obj_subtype u Y.J X.J hTop
      (Y.HasStrictlyPerfectApproximation K m) hK
  rw [isPseudoCoherentComplexFrom_iff]
  intro U
  refine ⟨(Sieve.ofObjects
    (fun W : {W : Y.C // Y.HasStrictlyPerfectApproximation K m W} => u.obj W.val) U).arrows,
    ?_, ?_⟩
  · rw [Sieve.generate_sieve]
    exact hcover U
  · rintro V g ⟨⟨W, hW⟩, ⟨k⟩⟩
    exact hasStrictlyPerfectApproximation_of_hom X _ m k
      (hasStrictlyPerfectApproximation_map_of_approx u F G W (ηG W) (sq W) K m
        (happrox W) hW)

end AlgebraicGeometry.RingedSite

end
