module

public import StacksFrontier.AlgebraicGeometry.Spaces.DualityBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityPullbackComparisonBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityPullbackComparisonCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackTensorComp
public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMapSndBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackRightUnitor

/-!
# The map of Stacks 0E5P under Tor independent base change

For a cartesian square of quasi-compact quasi-separated algebraic spaces with `X` and `Y'` Tor
independent over `Y`, and `K ∈ D_QCoh(𝒪_Y)`, the square

```
L(g')^*(Lf^*K ⊗^L a(𝒪_Y)) ⟶ L(g')^* a(K)
          |                         |
L(f')^*Lg^*K ⊗^L a'(𝒪_{Y'}) ⟶ a'(Lg^*K)
```

commutes; the horizontal arrows are the maps of Stacks 0E5P, the right one is the base change map
of Stacks 0E5D, and the left one is Stacks 07A4 for `g'`, the identification of the two iterated
pullbacks around the square, and Stacks 0E5D at `𝒪_Y` followed by `Lg^*𝒪_Y ≅ 𝒪_{Y'}`.

## Main results

* `AlgebraicGeometry.Space.quasicoherentDualityData_projectionFormulaMap_baseChange`: the hexagon
  of Stacks 0E48 on `D_QCoh`.
* `AlgebraicGeometry.Space.quasicoherentDerivedPullbackTensorComparison_unit`: Stacks 07A4 and
  the right unitors on `D_QCoh`.
* `AlgebraicGeometry.Space.quasicoherentDerivedCompareWithPullback_baseChange`: the map of
  Stacks 0E5P commutes with Tor independent base change (Stacks 0E5R).

## References

* [Stacks Project, Tag 0E5R](https://stacks.math.columbia.edu/tag/0E5R)
* [Stacks Project, Tag 0E48](https://stacks.math.columbia.edu/tag/0E48)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Prod

universe u

namespace Stacks.AffineProjectionFormula

variable {S : Type*} {T : Type*} {S' : Type*} {T' : Type*}
  [Category S] [Category T] [Category S'] [Category T']
  {Lf : S ⥤ T} {Rf : T ⥤ S} {Lf' : S' ⥤ T'} {Rf' : T' ⥤ S'}
  {Lg : S ⥤ S'} {Lg' : T ⥤ T'} {Lc : S ⥤ T'}
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
  (A : S ⥤ S ⥤ S) (A' : S' ⥤ S' ⥤ S') (B : T ⥤ T ⥤ T) (B' : T' ⥤ T' ⥤ T')
  (αf : Functor.uncurry.obj A ⋙ Lf ⟶ Lf.prod Lf ⋙ Functor.uncurry.obj B)
  (αf' : Functor.uncurry.obj A' ⋙ Lf' ⟶ Lf'.prod Lf' ⋙ Functor.uncurry.obj B')
  (αg : Functor.uncurry.obj A ⋙ Lg ⟶ Lg.prod Lg ⋙ Functor.uncurry.obj A')
  (αg' : Functor.uncurry.obj B ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ Functor.uncurry.obj B')

/-- `adjunctionTensorMapSnd_baseChange_square` for curried bifunctors. -/
theorem adjunctionTensorMapSnd_baseChange_square_curried (H : S) (G : T)
    (hsq : TensorComparisonCompatible eg ef (Functor.uncurry.obj A) (Functor.uncurry.obj A')
      (Functor.uncurry.obj B) (Functor.uncurry.obj B') αf αf' αg αg' H (Rf.obj G)) :
    αg.app (H, Rf.obj G) ≫
        (A'.obj (Lg.obj H)).map (Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef G) ≫
          Stacks.ProjectionFormula.adjunctionTensorMapSnd adjf' (Functor.uncurry.obj A')
            (Functor.uncurry.obj B') αf' (Lg.obj H) (Lg'.obj G) =
      Lg.map (Stacks.ProjectionFormula.adjunctionTensorMapSnd adjf (Functor.uncurry.obj A)
          (Functor.uncurry.obj B) αf H G) ≫
        Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef ((B.obj (Lf.obj H)).obj G) ≫
          Rf'.map (αg'.app (Lf.obj H, G) ≫
            (B'.map (ef.hom.app H ≫ eg.inv.app H)).app (Lg'.obj G)) := by
  have h := adjunctionTensorMapSnd_baseChange_square adjf adjf' eg ef _ _ _ _ αf αf' αg αg' H G hsq
  simp only [Functor.uncurry_obj_map, Functor.prod_obj, CategoryTheory.Functor.map_id,
    NatTrans.id_app, Category.id_comp, Category.comp_id, squareCompositeIso_inv_app] at h
  exact h

end Stacks.AffineProjectionFormula

namespace CategoryTheory.ObjectProperty

/-- An equation between two composites of three morphisms of a full subcategory holds as soon
as it holds for the underlying morphisms. -/
lemma comp₃_eq_comp₃_of_hom {C : Type*} [Category C] {P : ObjectProperty C}
    {X₁ X₂ X₃ X₄ Y₂ Y₃ : P.FullSubcategory} (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃) (c : X₃ ⟶ X₄)
    (d : X₁ ⟶ Y₂) (e : Y₂ ⟶ Y₃) (f : Y₃ ⟶ X₄)
    {c' : X₃.obj ⟶ X₄.obj} {d' : X₁.obj ⟶ Y₂.obj} {f' : Y₃.obj ⟶ X₄.obj} (hc : c.hom = c')
    (hd : d.hom = d') (hf : f.hom = f')
    (h : a.hom ≫ b.hom ≫ c' = d' ≫ e.hom ≫ f') : a ≫ b ≫ c = d ≫ e ≫ f := by
  subst hc hd hf
  exact P.hom_ext h

end CategoryTheory.ObjectProperty

namespace CategoryTheory.NatTrans

/-- Naturality of a comparison `F(T(K₂, K₁)) ⟶ T'(F K₂, F K₁)` in its first variable, for
the exchanged uncurried bifunctors. -/
lemma swap_uncurry_naturality_fst {C D : Type*} [Category C] [Category D] {T : C ⥤ C ⥤ C}
    {T' : D ⥤ D ⥤ D} {F : C ⥤ D}
    (α : (CategoryTheory.Prod.swap C C ⋙ Functor.uncurry.obj T) ⋙ F ⟶
      F.prod F ⋙ (CategoryTheory.Prod.swap D D ⋙ Functor.uncurry.obj T'))
    (K : C) {L L' : C} (φ : L ⟶ L') :
    α.app (L, K) ≫ (T'.obj (F.obj K)).map (F.map φ) =
      F.map ((T.obj K).map φ) ≫ α.app (L', K) := by
  simpa only [Functor.comp_map, Functor.uncurry_obj_map, Prod.swap_map, Functor.prod_map,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, Functor.comp_obj,
    Prod.swap_obj, Functor.prod_obj] using
    (α.naturality ((φ, 𝟙 K) : ((L, K) : C × C) ⟶ (L', K))).symm

end CategoryTheory.NatTrans

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-! ### The hexagon of Stacks 0E48 on `D_QCoh` -/

section Hexagon

variable {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
  {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
  (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
  (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
  (hY'qc : IsQuasiCompactSpace B S hS Y'.1) (hY'qs : IsAbsolutelyQuasiSeparated B S hS hZ Y'.1)

/-- **The hexagon of Stacks 0E48 on `D_QCoh`** for the projection formula maps of the data of
Stacks 0E5P along `f` and `f'` and the base change map of the square. -/
theorem quasicoherentDualityData_projectionFormulaMap_baseChange
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    (quasicoherentDerivedPullbackTensorComparison g).app
          ((quasicoherentDualityData hZ f hXqc hXqs hYqs).pushforward.obj E, K) ≫
        ((quasicoherentDerivedTensor B S hS Y').obj
            ((quasicoherentDerivedModulePullback g).obj K)).map
          ((squareBaseChange hZ sq hXqc hXqs hYqs hY'qc hY'qs).app E) ≫
          (quasicoherentDualityData hZ f' (isQuasiCompactSpace_of_isPullback hZ sq hXqc hYqs hY'qc)
            (isAbsolutelyQuasiSeparated_of_isPullback hZ sq hXqs hY'qs) hY'qs).projectionFormulaMap
            ((quasicoherentDerivedModulePullback g').obj E)
            ((quasicoherentDerivedModulePullback g).obj K) =
      (quasicoherentDerivedModulePullback g).map
          ((quasicoherentDualityData hZ f hXqc hXqs hYqs).projectionFormulaMap E K) ≫
        (squareBaseChange hZ sq hXqc hXqs hYqs hY'qc hY'qs).app
          (((quasicoherentDerivedTensor B S hS X).obj
            ((quasicoherentDerivedModulePullback f).obj K)).obj E) ≫
          (quasicoherentDualityData hZ f' (isQuasiCompactSpace_of_isPullback hZ sq hXqc hYqs hY'qc)
            (isAbsolutelyQuasiSeparated_of_isPullback hZ sq hXqs hY'qs) hY'qs).pushforward.map
            ((quasicoherentDerivedPullbackTensorComparison g').app
                (E, (quasicoherentDerivedModulePullback f).obj K) ≫
              ((quasicoherentDerivedTensor B S hS X').map
                (ObjectProperty.homMk
                  ((smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' sq.w).hom.app K.obj ≫
                    (smallEtaleDerivedModulePullbackCompIso B S hS f' g).inv.app K.obj) :
                  (quasicoherentDerivedModulePullback g').obj
                      ((quasicoherentDerivedModulePullback f).obj K) ⟶
                    (quasicoherentDerivedModulePullback f').obj
                      ((quasicoherentDerivedModulePullback g).obj K))).app
                ((quasicoherentDerivedModulePullback g').obj E)) := by
  have h := Stacks.AffineProjectionFormula.adjunctionTensorMapSnd_baseChange_square_curried
    (smallEtaleDerivedModuleAdjunction B S hS f) (smallEtaleDerivedModuleAdjunction B S hS f')
    (smallEtaleDerivedModulePullbackCompIso B S hS f' g)
    (smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' sq.w)
    (smallEtaleDerivedTensor B S hS Y) (smallEtaleDerivedTensor B S hS Y')
    (smallEtaleDerivedTensor B S hS X) (smallEtaleDerivedTensor B S hS X')
    (smallEtaleDerivedPullbackTensorIso f).hom (smallEtaleDerivedPullbackTensorIso f').hom
    (smallEtaleDerivedPullbackTensorIso g).hom (smallEtaleDerivedPullbackTensorIso g').hom
    K.obj E.obj
    (tensorComparisonCompatible_smallEtaleDerivedPullbackTensorIso f g f' g' sq.w K.obj _)
  have hf : ((quasicoherentDualityData hZ f'
      (isQuasiCompactSpace_of_isPullback hZ sq hXqc hYqs hY'qc)
            (isAbsolutelyQuasiSeparated_of_isPullback hZ sq hXqs hY'qs) hY'qs).pushforward.map
      ((quasicoherentDerivedPullbackTensorComparison g').app
          (E, (quasicoherentDerivedModulePullback f).obj K) ≫
        ((quasicoherentDerivedTensor B S hS X').map
          (ObjectProperty.homMk
                  ((smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' sq.w).hom.app K.obj ≫
                    (smallEtaleDerivedModulePullbackCompIso B S hS f' g).inv.app K.obj) :
                  (quasicoherentDerivedModulePullback g').obj
                      ((quasicoherentDerivedModulePullback f).obj K) ⟶
                    (quasicoherentDerivedModulePullback f').obj
                      ((quasicoherentDerivedModulePullback g).obj K))).app
          ((quasicoherentDerivedModulePullback g').obj E))).hom =
      (derivedModulePushforward B S hS f').map
        (((quasicoherentDerivedPullbackTensorComparison g').app
          (E, (quasicoherentDerivedModulePullback f).obj K)).hom ≫
            ((smallEtaleDerivedTensor B S hS X').map
              ((smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' sq.w).hom.app K.obj ≫
                (smallEtaleDerivedModulePullbackCompIso B S hS f' g).inv.app K.obj)).app
              ((quasicoherentDerivedModulePullback g').obj E).obj) :=
    rfl
  exact ObjectProperty.comp₃_eq_comp₃_of_hom _ _ _ _ _ _
    (quasicoherentPullbackComparisonData_projectionFormulaMap_hom f' _ _ _ _)
    (congrArg (smallEtaleDerivedModulePullback B S hS g).map
      (quasicoherentPullbackComparisonData_projectionFormulaMap_hom f _ _ E K)) hf h

omit hZ in
/-- **Stacks 07A4 and the right unitors on `D_QCoh`**: `Lg^*(K ⊗^L 𝒪_Y) ⟶ Lg^*K ⊗^L Lg^*𝒪_Y`,
followed by `Lg^*𝒪_Y ≅ 𝒪_{Y'}` and the unit law, is `Lg^*` of the unit law. -/
theorem quasicoherentDerivedPullbackTensorComparison_unit
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    (quasicoherentDerivedPullbackTensorComparison g).app (derivedStructureSheaf B S hS Y.1 Y.2, K) ≫
        ((quasicoherentDerivedTensor B S hS Y').obj
            ((quasicoherentDerivedModulePullback g).obj K)).map
          (ObjectProperty.homMk
            (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) g).hom :
            (quasicoherentDerivedModulePullback g).obj (derivedStructureSheaf B S hS Y.1 Y.2) ⟶
              derivedStructureSheaf B S hS Y'.1 Y'.2) ≫
          (quasicoherentDerivedTensorRightUnitor B S hS Y').hom.app
            ((quasicoherentDerivedModulePullback g).obj K) =
      (quasicoherentDerivedModulePullback g).map
        ((quasicoherentDerivedTensorRightUnitor B S hS Y).hom.app K) :=
  ObjectProperty.hom_ext _
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorIso_hom_app_unit
      (smallEtaleRingedToposHom B S hS g) (smallEtaleDerivedTensorProduct B S hS Y')
      (smallEtaleDerivedTensorProduct B S hS Y) K.obj)

end Hexagon

/-! ### Stacks 0E5R -/

section CompareWithPullback

variable {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
  {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
  (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
  (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
  (hY'qc : IsQuasiCompactSpace B S hS Y'.1) (hY'qs : IsAbsolutelyQuasiSeparated B S hS hZ Y'.1)
  (hTor : TorIndependent X.2 Y'.2 Y.2 f.hom g.hom)

include hTor in
/-- For a cartesian square of quasi-compact quasi-separated algebraic spaces
with `X` and `Y'` Tor independent over `Y` and `K ∈ D_QCoh(𝒪_Y)`, the square

`L(g')^*(Lf^*K ⊗^L a(𝒪_Y)) ⟶ L(g')^*a(K) ⟶ a'(Lg^*K)` (`L(g')^*` of Stacks 0E5P, then the base
change map of Stacks 0E5D)

equals `L(g')^*(Lf^*K ⊗^L a(𝒪_Y)) ⟶ L(g')^*Lf^*K ⊗^L L(g')^*a(𝒪_Y) ⟶ L(f')^*Lg^*K ⊗^L a'(𝒪_{Y'})
⟶ a'(Lg^*K)`: Stacks 07A4 for `g'`, the identification of the two iterated pullbacks around the
square and Stacks 0E5D at `𝒪_Y` followed by `a'(Lg^*𝒪_Y ≅ 𝒪_{Y'})`, then Stacks 0E5P for `f'`. -/
@[stacks 0E5R]
theorem quasicoherentDerivedCompareWithPullback_baseChange
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    (quasicoherentDerivedModulePullback g').map
          ((quasicoherentDerivedCompareWithPullback hZ f hXqc hXqs hYqs).app K) ≫
        (quasicoherentDerivedRightAdjointBaseChangeMap hZ sq hXqc hXqs hYqs hY'qc hY'qs
          hTor).app K =
      (quasicoherentDerivedPullbackTensorComparison g').app
          ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj
            (derivedStructureSheaf B S hS Y.1 Y.2), (quasicoherentDerivedModulePullback f).obj K) ≫
        ((quasicoherentDerivedTensor B S hS X').map
            (ObjectProperty.homMk
              ((smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' sq.w).hom.app K.obj ≫
                (smallEtaleDerivedModulePullbackCompIso B S hS f' g).inv.app K.obj) :
              (quasicoherentDerivedModulePullback g').obj
                  ((quasicoherentDerivedModulePullback f).obj K) ⟶
                (quasicoherentDerivedModulePullback f').obj
                  ((quasicoherentDerivedModulePullback g).obj K))).app
            ((quasicoherentDerivedModulePullback g').obj
              ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj
                (derivedStructureSheaf B S hS Y.1 Y.2))) ≫
          ((quasicoherentDerivedTensor B S hS X').obj ((quasicoherentDerivedModulePullback f').obj
              ((quasicoherentDerivedModulePullback g).obj K))).map
            ((quasicoherentDerivedRightAdjointBaseChangeMap hZ sq hXqc hXqs hYqs hY'qc hY'qs
                hTor).app (derivedStructureSheaf B S hS Y.1 Y.2) ≫
              (quasicoherentDerivedRightAdjoint hZ f'
                (isQuasiCompactSpace_of_isPullback hZ sq hXqc hYqs hY'qc)
                (isAbsolutelyQuasiSeparated_of_isPullback hZ sq hXqs hY'qs) hY'qs).map
                (ObjectProperty.homMk
                  (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) g).hom :
                  (quasicoherentDerivedModulePullback g).obj
                      (derivedStructureSheaf B S hS Y.1 Y.2) ⟶
                    derivedStructureSheaf B S hS Y'.1 Y'.2)) ≫
            (quasicoherentDerivedCompareWithPullback hZ f'
              (isQuasiCompactSpace_of_isPullback hZ sq hXqc hYqs hY'qc)
              (isAbsolutelyQuasiSeparated_of_isPullback hZ sq hXqs hY'qs) hY'qs).app
              ((quasicoherentDerivedModulePullback g).obj K) :=
  have := isIso_squareBaseChange hZ sq hXqc hXqs hYqs hY'qc hY'qs hTor
  have hX'qc := isQuasiCompactSpace_of_isPullback hZ sq hXqc hYqs hY'qc
  have hX'qs := isAbsolutelyQuasiSeparated_of_isPullback hZ sq hXqs hY'qs
  CategoryTheory.Adjunction.comparison_baseChange_unit
    (quasicoherentDualityAdjunction hZ f hXqc hXqs hYqs)
    (quasicoherentDualityAdjunction hZ f' hX'qc hX'qs hY'qs)
    (quasicoherentDualityData hZ f hXqc hXqs hYqs).projectionFormulaMap
    (quasicoherentDualityData hZ f' hX'qc hX'qs hY'qs).projectionFormulaMap
    (fun φ K => (quasicoherentDualityData hZ f' hX'qc hX'qs hY'qs)
        |>.projectionFormulaMap_naturality_right φ K)
    (quasicoherentDerivedCompareWithPullbackTensor hZ f hXqc hXqs hYqs)
    ((quasicoherentDualityData hZ f hXqc hXqs hYqs).map_compareWithPullbackTensor_comp_counit
      (quasicoherentDualityAdjunction hZ f hXqc hXqs hYqs))
    (quasicoherentDerivedCompareWithPullbackTensor hZ f' hX'qc hX'qs hY'qs)
    ((quasicoherentDualityData hZ f' hX'qc hX'qs hY'qs)
        |>.map_compareWithPullbackTensor_comp_counit
      (quasicoherentDualityAdjunction hZ f' hX'qc hX'qs hY'qs))
    (quasicoherentDerivedModulePullback g) (quasicoherentDerivedModulePullback g')
    (fun E => (squareBaseChange hZ sq hXqc hXqs hYqs hY'qc hY'qs).app E)
    (fun φ => (squareBaseChange hZ sq hXqc hXqs hYqs hY'qc hY'qs).naturality φ)
    (fun L => (quasicoherentDerivedRightAdjointBaseChangeMap hZ sq hXqc hXqs hYqs hY'qc hY'qs
      hTor).app L)
    (quasicoherentDerivedRightAdjointBaseChangeMap_trace hZ sq hXqc hXqs hYqs hY'qc hY'qs hTor)
    (fun K => (ObjectProperty.homMk
              ((smallEtaleDerivedModulePullbackSquareIso B S hS f g f' g' sq.w).hom.app K.obj ≫
                (smallEtaleDerivedModulePullbackCompIso B S hS f' g).inv.app K.obj) :
              (quasicoherentDerivedModulePullback g').obj
                  ((quasicoherentDerivedModulePullback f).obj K) ⟶
                (quasicoherentDerivedModulePullback f').obj
                  ((quasicoherentDerivedModulePullback g).obj K)))
    (fun K L => (quasicoherentDerivedPullbackTensorComparison g).app (L, K))
    (fun K _ _ φ => NatTrans.swap_uncurry_naturality_fst
      (quasicoherentDerivedPullbackTensorComparison g) K φ)
    (fun M N => (quasicoherentDerivedPullbackTensorComparison g').app (N, M))
    (quasicoherentDualityData_projectionFormulaMap_baseChange hZ sq hXqc hXqs hYqs hY'qc hY'qs)
    (derivedStructureSheaf B S hS Y.1 Y.2) (derivedStructureSheaf B S hS Y'.1 Y'.2)
    (ObjectProperty.homMk
      (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) g).hom :
      (quasicoherentDerivedModulePullback g).obj (derivedStructureSheaf B S hS Y.1 Y.2) ⟶
        derivedStructureSheaf B S hS Y'.1 Y'.2)
    (quasicoherentDerivedTensorRightUnitor B S hS Y).hom
    (quasicoherentDerivedTensorRightUnitor B S hS Y').hom
    quasicoherentDerivedPullbackTensorComparison_unit
    (fun φ => (quasicoherentDerivedRightAdjointBaseChangeMap hZ sq hXqc hXqs hYqs hY'qc hY'qs
      hTor).naturality φ)
    (fun K _ _ φ => (quasicoherentDualityData hZ f' hX'qc hX'qs hY'qs)
        |>.compareWithPullbackTensor_naturality_right
      (quasicoherentDualityAdjunction hZ f' hX'qc hX'qs hY'qs) K φ)
    K

end CompareWithPullback

end AlgebraicGeometry.Space

end
