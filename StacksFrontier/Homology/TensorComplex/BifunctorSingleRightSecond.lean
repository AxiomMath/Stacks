module

public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.CanonicalSheafCertificate

/-!
# `Tot(F(-, N[0]))` is `F(-, N)` degreewise, naturally in `N` as well

`HomologicalComplex.map₂SingleRightNatIso` identifies `F(-, N)` applied degreewise with
`Tot(F(-, N[0]))`, naturally in the complex and for a *fixed* object `N` of the second variable.
This file adds the naturality of that identification in `N`.

The two statements are proved the same way — degreewise, through the inclusion
`HomologicalComplex.singleRightι` of the only surviving summand — and the only input beyond the
earlier one is `HomologicalComplex.single_map_f_self`, which says that a morphism between
complexes concentrated in degree zero is the morphism of their degree-zero terms conjugated by
`HomologicalComplex.singleObjXSelf`.

## Main results

* `HomologicalComplex.singleRightι_mapBifunctorMap_snd`: the bidegree-`(i, 0)` inclusion is
  natural in the object of the second variable.
* `HomologicalComplex.singleRightIsoMapBifunctor_naturality_snd`: so is the degreewise
  identification, at a fixed complex.
* `HomologicalComplex.map₂SingleRightNatIso_naturality_snd`: hence the natural isomorphism
  itself is natural in `N`.

## References

* [Stacks Project, Tag 0662](https://stacks.math.columbia.edu/tag/0662)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe v₁ v₂ v u₁ u₂ u'

variable {C₁ : Type u₁} {C₂ : Type u₂} {D : Type u'} [Category.{v₁} C₁] [Category.{v₂} C₂]
  [Category.{v} D] [Preadditive C₁] [Preadditive C₂] [Preadditive D] [HasZeroObject C₂]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ M : C₁, (F.obj M).PreservesZeroMorphisms]
  [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ),
    HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]

/-- The bidegree-`(i, 0)` inclusion into `Tot(F(K, N[0]))` is natural in `N`: a morphism of the
second variable acts on that summand by its degree-zero component. -/
theorem singleRightι_mapBifunctorMap_snd (K : CochainComplex C₁ ℤ) {N N' : C₂} (g : N ⟶ N')
    (i : ℤ) :
    singleRightι F K N i ≫
        (mapBifunctorMap (𝟙 K) ((CochainComplex.singleFunctor C₂ 0).map g) F
          (ComplexShape.up ℤ)).f i =
      (F.obj (K.X i)).map (((CochainComplex.singleFunctor C₂ 0).map g).f 0) ≫
        singleRightι F K N' i := by
  simp [singleRightι]

variable [∀ N : C₂, (F.flip.obj N).Additive]

/-- The identification of `F(-, N)` applied degreewise with `Tot(F(-, N[0]))` is natural in
`N`. -/
theorem singleRightIsoMapBifunctor_naturality_snd (K : CochainComplex C₁ ℤ) {N N' : C₂}
    (g : N ⟶ N') :
    (NatTrans.mapHomologicalComplex (F.flip.map g) (ComplexShape.up ℤ)).app K ≫
        (singleRightIsoMapBifunctor F K N').hom =
      (singleRightIsoMapBifunctor F K N).hom ≫
        mapBifunctorMap (𝟙 K) ((CochainComplex.singleFunctor C₂ 0).map g) F
          (ComplexShape.up ℤ) := by
  ext i
  change (F.obj (K.X i)).map g ≫ (mapBifunctorSingleRightXIso F K N' i).inv =
    (mapBifunctorSingleRightXIso F K N i).inv ≫
      (mapBifunctorMap (𝟙 K) ((CochainComplex.singleFunctor C₂ 0).map g) F
        (ComplexShape.up ℤ)).f i
  have hg : ((CochainComplex.singleFunctor C₂ 0).map g).f 0 =
      (singleObjXSelf (ComplexShape.up ℤ) 0 N).hom ≫ g ≫
        (singleObjXSelf (ComplexShape.up ℤ) 0 N').inv :=
    single_map_f_self (ComplexShape.up ℤ) 0 g
  rw [mapBifunctorSingleRightXIso_inv, mapBifunctorSingleRightXIso_inv, Category.assoc,
    singleRightι_mapBifunctorMap_snd F K g i, ← Category.assoc, ← Category.assoc,
    ← (F.obj (K.X i)).map_comp, ← (F.obj (K.X i)).map_comp, hg, Iso.inv_hom_id_assoc]

/-- **`Tot(F(-, N[0]))` is `F(-, N)` applied degreewise, naturally in `N`.** -/
theorem map₂SingleRightNatIso_naturality_snd {N N' : C₂} (g : N ⟶ N') :
    NatTrans.mapHomologicalComplex (F.flip.map g) (ComplexShape.up ℤ) ≫
        (map₂SingleRightNatIso F N').hom =
      (map₂SingleRightNatIso F N).hom ≫
        F.map₂CochainComplex.flip.map ((CochainComplex.singleFunctor C₂ 0).map g) :=
  NatTrans.ext (funext fun K ↦ singleRightIsoMapBifunctor_naturality_snd F K g)

end HomologicalComplex

end
