module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineEtaleReductionEquivalence
public import StacksFrontier.AlgebraicGeometry.FormalSpace.StructureSheaf.Construction

/-!
# Reduction squares for the functor `U ↦ U_red` of Stacks 0DEH

Let `X` be a formal algebraic space over `S` with a reduction `X_red`, and let
`E = AlgebraicGeometry.FormalSpace.affineEtaleReductionFunctor` be the functor `U ↦ U_red` of
Stacks 0DEH from the affine étale formal charts over `X` to `X_affine,étale`. This file exhibits
`E(U)` as the fibre product `U ×_X X_red`, naturally in `U`, and deduces that when `E` is an
equivalence of categories — which is Stacks 0DEH — the correspondence
`AlgebraicGeometry.FormalSpace.Reduction.AffineEtaleCorrespondence` holds.

## Main definitions

* `AlgebraicGeometry.FormalSpace.reductionFunctorSquareMap`: the morphism `E(U) ⟶ U` of the
  reduction square of `U`.

## Main results

* `AlgebraicGeometry.FormalSpace.isReductionSquare_reductionFunctorSquareMap`: the square is
  cartesian.
* `AlgebraicGeometry.FormalSpace.reductionFunctorSquareMap_naturality`: it is natural in `U`.
* `AlgebraicGeometry.FormalSpace.affineEtaleCorrespondence_of_isEquivalence`: Stacks 0DEH, in the
  form of an equivalence, gives the correspondence of reduction squares.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : FppfSheaf B S hS}
  (hX : IsFormalAlgebraicSpace B S hS X) (R : Reduction B S hS X)

/-- The reduction of a chart `U` chosen by the comparison functor of Stacks 0DEG. -/
noncomputable abbrev chartReduction (U : AffineEtaleFormalCharts B S hS X) :
    Reduction B S hS U.obj.left :=
  objReduction hX R U.toRepresentableEtale

/-- The scheme underlying `E(U)` is, as an algebraic space, the reduction of `U`. -/
noncomputable def reductionFunctorSpaceIso (U : AffineEtaleFormalCharts B S hS X) :
    (schemeSpaceFunctor B S hS).obj (R.affineChartObj ((affineEtaleReductionFunctor hX R).obj U)) ≅
      (chartReduction hX R U).space :=
  (ObjectProperty.ι _ ⋙ Over.forget R.space).mapIso
    ((affineEtaleReductionFunctorCompIso hX R).app U)

/-- The identification of `E(U)` with `U_red`, followed by the structure morphism
`U_red ⟶ X_red`, is the structure morphism of `E(U)` over `X_red`. -/
theorem reductionFunctorSpaceIso_hom_comp (U : AffineEtaleFormalCharts B S hS X) :
    (reductionFunctorSpaceIso hX R U).hom ≫ (chartReduction hX R U).map R U.obj.hom =
      R.affineChartSpaceMap ((affineEtaleReductionFunctor hX R).obj U) :=
  Over.w ((affineEtaleReductionFunctorCompIso hX R).app U).hom.hom

/-- The morphism `E(U) ⟶ U` of the reduction square of `U`: the identification of `E(U)` with the
reduction `U_red`, followed by the inclusion of the reduction. -/
noncomputable def reductionFunctorSquareMap (U : AffineEtaleFormalCharts B S hS X) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        (R.affineChartObj ((affineEtaleReductionFunctor hX R).obj U)) ⟶ U.obj.left :=
  (liftSheafYonedaSpaceIsoSheafifiedYoneda B S hS _).inv ≫
    liftSheafMap B S hS (reductionFunctorSpaceIso hX R U).hom ≫
      (chartReduction hX R U).inclusion

/-- **`E(U)` is `U ×_X X_red`.** -/
theorem isReductionSquare_reductionFunctorSquareMap (U : AffineEtaleFormalCharts B S hS X) :
    R.IsReductionSquare U ((affineEtaleReductionFunctor hX R).obj U)
      (reductionFunctorSquareMap hX R U) := by
  have hsq := isPullback_inclusion_liftSheafMap_map hX R
    (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS U.property.1) U.property.2
    (chartReduction hX R U)
  let e := reductionFunctorSpaceIso hX R U
  let ι := liftSheafYonedaSpaceIsoSheafifiedYoneda B S hS
    (R.affineChartObj ((affineEtaleReductionFunctor hX R).obj U))
  have key : ∀ {Z} (k : _ ⟶ Z), (liftSheafMap B S hS e.inv ≫ ι.hom) ≫
      ι.inv ≫ liftSheafMap B S hS e.hom ≫ k = k := fun k => by
    rw [Category.assoc, ι.hom_inv_id_assoc, ← Category.assoc, ← liftSheafMap_comp, e.inv_hom_id,
      liftSheafMap_id, Category.id_comp]
  refine hsq.of_iso ((liftSheafFunctor B S hS).mapIso e.symm ≪≫ ι) (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · exact (Category.comp_id _).trans (key _).symm
  · change _ ≫ 𝟙 _ = (liftSheafMap B S hS e.inv ≫ ι.hom) ≫
      (ι.inv ≫ liftSheafMap B S hS (R.affineChartSpaceMap _))
    rw [← reductionFunctorSpaceIso_hom_comp hX R U, liftSheafMap_comp]
    exact (Category.comp_id _).trans (key _).symm

/-- The reduction squares of the functor `U ↦ U_red` are natural in `U`. -/
theorem reductionFunctorSquareMap_naturality {U V : AffineEtaleFormalCharts B S hS X}
    (g : U ⟶ V) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((Space.AffineEtale.toOver B S hS R.space.obj).map
          ((affineEtaleReductionFunctor hX R).map g)) ≫ reductionFunctorSquareMap hX R V =
      reductionFunctorSquareMap hX R U ≫ g.hom.left := by
  have hnat : (schemeSpaceFunctor B S hS).map ((Space.AffineEtale.toOver B S hS R.space.obj).map
        ((affineEtaleReductionFunctor hX R).map g)) ≫ (reductionFunctorSpaceIso hX R V).hom =
      (reductionFunctorSpaceIso hX R U).hom ≫
        (chartReduction hX R U).map (chartReduction hX R V) g.hom.left :=
    congrArg (fun k => k.hom.left) ((affineEtaleReductionFunctorCompIso hX R).hom.naturality g)
  calc (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((Space.AffineEtale.toOver B S hS R.space.obj).map
          ((affineEtaleReductionFunctor hX R).map g)) ≫ reductionFunctorSquareMap hX R V
      = (liftSheafYonedaSpaceIsoSheafifiedYoneda B S hS _).inv ≫
          liftSheafMap B S hS ((schemeSpaceFunctor B S hS).map
            ((Space.AffineEtale.toOver B S hS R.space.obj).map
              ((affineEtaleReductionFunctor hX R).map g)) ≫
            (reductionFunctorSpaceIso hX R V).hom) ≫ (chartReduction hX R V).inclusion := by
        rw [reductionFunctorSquareMap, ← Category.assoc,
          sheafifiedYoneda_map_liftSheafYonedaSpaceIsoSheafifiedYoneda_inv, liftSheafMap_comp,
          Category.assoc, Category.assoc]
    _ = (liftSheafYonedaSpaceIsoSheafifiedYoneda B S hS _).inv ≫
          liftSheafMap B S hS (reductionFunctorSpaceIso hX R U).hom ≫
            (liftSheafMap B S hS ((chartReduction hX R U).map (chartReduction hX R V) g.hom.left) ≫
              (chartReduction hX R V).inclusion) := by
        rw [hnat, liftSheafMap_comp, Category.assoc]
    _ = reductionFunctorSquareMap hX R U ≫ g.hom.left := by
        rw [(chartReduction hX R U).liftSheafMap_map (chartReduction hX R V) g.hom.left,
          reductionFunctorSquareMap, Category.assoc, Category.assoc]

/-- **Stacks 0DEH gives the correspondence of reduction squares.** If the functor `U ↦ U_red` of
Stacks 0DEH is an equivalence, then every chart has a reduction, every affine object of
`X_affine,étale` is the reduction of a chart, and a morphism of reductions lifts uniquely to a
morphism of charts. -/
theorem affineEtaleCorrespondence_of_isEquivalence
    [(affineEtaleReductionFunctor hX R).IsEquivalence] : R.AffineEtaleCorrespondence where
  exists_square U := ⟨_, _, isReductionSquare_reductionFunctorSquareMap hX R U⟩
  exists_chart W := by
    obtain ⟨U, ⟨ι⟩⟩ := Functor.EssSurj.mem_essImage (F := affineEtaleReductionFunctor hX R) W
    refine ⟨U, (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
      ((Space.AffineEtale.toOver B S hS R.space.obj).map ι.inv) ≫
        reductionFunctorSquareMap hX R U, ?_⟩
    refine (isReductionSquare_reductionFunctorSquareMap hX R U).of_iso
      ((Space.AffineEtale.toOver B S hS R.space.obj ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).mapIso ι)
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
    · rw [Functor.mapIso_hom, Functor.comp_map, ← Category.assoc,
        ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, ι.hom_inv_id,
        CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
        Iso.refl_hom, Category.comp_id]
    · rw [Functor.mapIso_hom, Functor.comp_map, R.map_affineChartMap, Iso.refl_hom,
        Category.comp_id]
  existsUnique_hom U V W W' a a' ha ha' h := by
    let E := affineEtaleReductionFunctor hX R
    let sY := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
    let toOver := Space.AffineEtale.toOver B S hS R.space.obj
    have hU := isReductionSquare_reductionFunctorSquareMap hX R U
    have hV := isReductionSquare_reductionFunctorSquareMap hX R V
    -- the comparisons of `W` with `E U` and of `W'` with `E V`
    obtain ⟨μ, hμ⟩ := R.exists_affineEtale_hom_of_isPullback ha hU (𝟙 U)
    obtain ⟨ν, hν⟩ := R.exists_affineEtale_hom_of_isPullback hU ha (𝟙 U)
    obtain ⟨κ, hκ⟩ := R.exists_affineEtale_hom_of_isPullback ha' hV (𝟙 V)
    replace hμ := hμ.trans (Category.comp_id _)
    replace hν := hν.trans (Category.comp_id _)
    replace hκ := hκ.trans (Category.comp_id _)
    have hμν : μ ≫ ν = 𝟙 W := by
      refine R.affineEtale_hom_ext_of_isPullback (a := a) ha (𝟙 U) ?_ ?_
      · rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc,
          hν, hμ]
        exact (Category.comp_id a).symm
      · rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
        exact (Category.comp_id a).symm
    -- a morphism of charts compatible with `h` is the preimage of `ν ≫ h ≫ κ`
    have hcomp : ∀ g' : U ⟶ V, sY.map (toOver.map h) ≫ a' = a ≫ g'.hom.left →
        sY.map (toOver.map (ν ≫ h ≫ κ)) ≫ reductionFunctorSquareMap hX R V =
          reductionFunctorSquareMap hX R U ≫ g'.hom.left := by
      intro g' hg'
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
        CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc,
        Category.assoc, hκ, hg', ← Category.assoc, hν]
    let g := E.preimage (ν ≫ h ≫ κ)
    have hg : E.map g = ν ≫ h ≫ κ := E.map_preimage _
    refine ⟨g, ?_, fun g' hg' => E.map_injective ?_⟩
    · calc sY.map (toOver.map h) ≫ a'
          = sY.map (toOver.map (μ ≫ ν ≫ h ≫ κ)) ≫ reductionFunctorSquareMap hX R V := by
            rw [← Category.assoc μ, hμν, Category.id_comp, CategoryTheory.Functor.map_comp,
              CategoryTheory.Functor.map_comp, Category.assoc, hκ]
        _ = sY.map (toOver.map μ) ≫ sY.map (toOver.map (E.map g)) ≫
              reductionFunctorSquareMap hX R V := by
            rw [hg, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
              Category.assoc]
        _ = a ≫ g.hom.left := by
            rw [reductionFunctorSquareMap_naturality, ← Category.assoc, hμ]
    · rw [hg]
      exact R.affineEtale_hom_ext_of_isPullback hV g'
        (reductionFunctorSquareMap_naturality hX R g') (hcomp g' hg')

end AlgebraicGeometry.FormalSpace

end
