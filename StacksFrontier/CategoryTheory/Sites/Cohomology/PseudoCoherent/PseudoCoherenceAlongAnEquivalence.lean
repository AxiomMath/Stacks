module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectnessAlongAnEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherenceAlongAnExactFunctor

/-!
# Pseudo-coherence along an equivalence of ringed sites

Let `e : C ≌ D` be an equivalence between the underlying sites of two ringed sites `(C, O_C)` and
`(D, O_D)`, continuous in both directions, with an isomorphism of sheaves of rings
`ρ : O_C ⟶ e_* O_D`. The induced equivalence `D(O_D) ≌ D(O_C)` carries `m`-pseudo-coherent
objects (Stacks 08FT) to `m`-pseudo-coherent objects.

## Main results

* `RingedSite.isPseudoCoherentFrom_mapDerivedCategory_pushforwardEquivalenceOfIsIso`:
  `m`-pseudo-coherence is carried across the equivalence.
* `RingedSite.isPseudoCoherentFrom_mapDerivedCategory_pushforwardEquivalenceOfIsIso_iff`:
  and it is reflected.

## References

* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe uX vX uY vY w dX dY

namespace AlgebraicGeometry.RingedSite

open Stacks.SheafOfModules.InternalHom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
  (eqv : X.C ≌ Y.C) [hfun : eqv.functor.IsContinuous X.J Y.J]
  [hinv : eqv.inverse.IsContinuous Y.J X.J]
  (ρ : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
    (eqv.functor.sheafPushforwardContinuous RingCat.{w} X.J Y.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  [hρ : IsIso ρ]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ W : Y.C, HasSheafify (Y.J.over W) AddCommGrpCat.{w}]
  [∀ W : Y.C, (Y.J.over W).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{dY} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [HasDerivedCategory.{dX} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- **`m`-pseudo-coherence is invariant under an equivalence of ringed sites.** The derived functor
of the pushforward along an equivalence of sites with an invertible structure map carries an
`m`-pseudo-coherent object of `D(O_D)` to an `m`-pseudo-coherent object of `D(O_C)`. -/
theorem isPseudoCoherentFrom_mapDerivedCategory_pushforwardEquivalenceOfIsIso
    (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) (m : ℤ)
    (hK : Y.IsPseudoCoherentFrom K m) :
    X.IsPseudoCoherentFrom
      ((pushforwardEquivalenceOfIsIso eqv ρ).functor.mapDerivedCategory.obj K) m := by
  have hψ (W : Y.C) : IsIso (AnyUniverse.siteEquivPsiOver (X := X) (Y := Y) eqv.symm ρ W) := by
    have : IsIso ((sheafToPresheaf _ _).map
        (AnyUniverse.siteEquivPsiOver (X := X) (Y := Y) eqv.symm ρ W)) :=
      inferInstanceAs (IsIso (Functor.whiskerLeft (Over.forget (eqv.symm.functor.obj W)).op ρ.hom))
    exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)
  have hη : ∀ W : Y.C, IsIso (SheafOfModules.unitToPushforwardObjUnit
      (AnyUniverse.siteEquivPsiOver (X := X) (Y := Y) eqv.symm ρ W)) := fun W =>
    have := hψ W
    Stacks.SheafOfModules.isIso_unitToPushforwardObjUnit _
  have hTop : X.J.CoversTop eqv.inverse.obj := fun U =>
    X.J.superset_covering (fun V f _ => ⟨eqv.functor.obj U, ⟨f ≫ eqv.unit.app U⟩⟩) (X.J.top_mem U)
  exact isPseudoCoherentFrom_mapDerivedCategory_of_hypotheses (X := X) (Y := Y) eqv.inverse
    (pushforwardEquivalenceOfIsIso eqv ρ).functor
    (fun W => (pushforwardEquivalenceOfIsIsoOver eqv ρ W).inverse)
    inferInstance inferInstance inferInstance
    (fun W => Functor.additive_of_preserves_binary_products _)
    (fun W => inferInstance) (fun W => inferInstance) inferInstance hTop
    (fun W => (@asIso _ _ _ _ _ (hη W)).symm)
    (fun W => Iso.refl _) K m hK

/-- The inverse structure map of an equivalence of ringed sites with an invertible structure
map is invertible. -/
instance isIso_anyUniversePsiOfIso : IsIso (AnyUniverse.psiOfIso eqv ρ) := by
  have : IsIso ((sheafToPresheaf _ _).map (AnyUniverse.psiOfIso eqv ρ)) := by
    change IsIso (Functor.whiskerRight (NatTrans.op eqv.counit)
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj ≫
      Functor.whiskerLeft eqv.inverse.op (inv ρ.hom))
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun W => ?_
    exact @IsIso.comp_isIso _ _ _ _ _ _ _
      (Functor.map_isIso (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj
        (eqv.counit.app W.unop).op)
      (inferInstanceAs (IsIso ((inv ρ.hom).app _)))
  exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)

/-- **`m`-pseudo-coherence is invariant under an equivalence of ringed sites, in both
directions.** An object of `D(O_D)` is `m`-pseudo-coherent exactly when its image under the
equivalence `D(O_D) ≌ D(O_C)` is. -/
theorem isPseudoCoherentFrom_mapDerivedCategory_pushforwardEquivalenceOfIsIso_iff
    (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (m : ℤ) :
    X.IsPseudoCoherentFrom
        ((pushforwardEquivalenceOfIsIso eqv ρ).functor.mapDerivedCategory.obj K) m ↔
      Y.IsPseudoCoherentFrom K m := by
  refine ⟨fun h => ?_,
    isPseudoCoherentFrom_mapDerivedCategory_pushforwardEquivalenceOfIsIso eqv ρ K m⟩
  set e := pushforwardEquivalenceOfIsIso eqv ρ
  have h' := isPseudoCoherentFrom_mapDerivedCategory_pushforwardEquivalenceOfIsIso eqv.symm
    (AnyUniverse.psiOfIso eqv ρ) _ m h
  change Y.IsPseudoCoherentFrom
    (e.inverse.mapDerivedCategory.obj (e.functor.mapDerivedCategory.obj K)) m at h'
  let K₀ := DerivedCategory.Q.objPreimage K
  let eK : DerivedCategory.Q.obj K₀ ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let c : DerivedCategory.Q.obj K₀ ≅
      e.inverse.mapDerivedCategory.obj (e.functor.mapDerivedCategory.obj K) :=
    DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).app
        K₀ ≪≫ ((Functor.mapHomologicalComplexCompIso e.unitIso.symm
          (ComplexShape.up ℤ)).app K₀).symm) ≪≫
      (e.inverse.mapDerivedCategoryFactors.app _).symm ≪≫
      e.inverse.mapDerivedCategory.mapIso ((e.functor.mapDerivedCategoryFactors.app K₀).symm ≪≫
        e.functor.mapDerivedCategory.mapIso eK)
  obtain ⟨L, hL, ⟨eL⟩⟩ := h'
  exact ⟨L, hL, ⟨eL ≪≫ c.symm ≪≫ eK⟩⟩

end AlgebraicGeometry.RingedSite

end
