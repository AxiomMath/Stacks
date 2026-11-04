module

public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.LinearCupProductFamily

/-!
# Naturality of the total-complex comparison of a bifunctor comparison

`Stacks.Cohomology.LinearCupProductFamily.mapBifunctorTotalMap` turns a degreewise comparison
`ε : E'(Φ₁ a, Φ₂ b) ⟶ Φ(E(a, b))` of two bifunctors into a morphism of total complexes
`Tot(E'(Φ₁ K, Φ₂ L)) ⟶ Φ(Tot(E(K, L)))`.  This file proves that it is natural in the two complexes
`K` and `L`.

These are the properties the projection map of the second diagram of [Stacks, Remark 0GL6] needs
at the level of complexes, where `E` and `E'` are tensor products with constant sheaves and `Φ`
is a direct image.

## Main results

* `Stacks.Cohomology.LinearCupProductFamily.mapBifunctorBicomplexMap_naturality`: naturality of
  the comparison of bicomplexes.
* `Stacks.Cohomology.LinearCupProductFamily.mapBifunctorTotalMap_naturality`: naturality in
  `K` and `L`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.LinearCupProductFamily

universe vA vB vD vA' vB' vD' uA uB uD uA' uB' uD'

variable {CA : Type uA} {CB : Type uB} {CD : Type uD} {CA' : Type uA'} {CB' : Type uB'}
  {CD' : Type uD'} [Category.{vA} CA] [Category.{vB} CB] [Category.{vD} CD]
  [Category.{vA'} CA'] [Category.{vB'} CB'] [Category.{vD'} CD']
  [Preadditive CA] [Preadditive CB] [Preadditive CD]
  [Preadditive CA'] [Preadditive CB'] [Preadditive CD']
  (E : CA ⥤ CB ⥤ CD) (E' : CA' ⥤ CB' ⥤ CD')
  [E.PreservesZeroMorphisms] [∀ a, (E.obj a).PreservesZeroMorphisms]
  [E'.PreservesZeroMorphisms] [∀ a, (E'.obj a).PreservesZeroMorphisms]
  (Φ₁ : CA ⥤ CA') (Φ₂ : CB ⥤ CB') (Φ : CD ⥤ CD') [Φ₁.Additive] [Φ₂.Additive] [Φ.Additive]
  (ε : ∀ (a : CA) (b : CB), (E'.obj (Φ₁.obj a)).obj (Φ₂.obj b) ⟶ Φ.obj ((E.obj a).obj b))
  (hε₁ : ∀ {a a' : CA} (f : a ⟶ a') (b : CB),
    (E'.map (Φ₁.map f)).app (Φ₂.obj b) ≫ ε a' b = ε a b ≫ Φ.map ((E.map f).app b))
  (hε₂ : ∀ (a : CA) {b b' : CB} (g : b ⟶ b'),
    (E'.obj (Φ₁.obj a)).map (Φ₂.map g) ≫ ε a b' = ε a b ≫ Φ.map ((E.obj a).map g))
  {I₁ I₂ : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)
  {I₁₂ : Type*} (c : ComplexShape I₁₂) [TotalComplexShape c₁ c₂ c] [DecidableEq I₁₂]

/-- **The comparison of bicomplexes is natural in the two complexes.** -/
theorem mapBifunctorBicomplexMap_naturality {K K' : HomologicalComplex CA c₁}
    {L L' : HomologicalComplex CB c₂} (f : K ⟶ K') (g : L ⟶ L') :
    (((E'.mapBifunctorHomologicalComplex c₁ c₂).map ((Φ₁.mapHomologicalComplex c₁).map f)).app
          ((Φ₂.mapHomologicalComplex c₂).obj L) ≫
        ((E'.mapBifunctorHomologicalComplex c₁ c₂).obj
          ((Φ₁.mapHomologicalComplex c₁).obj K')).map ((Φ₂.mapHomologicalComplex c₂).map g)) ≫
      mapBifunctorBicomplexMap E E' Φ₁ Φ₂ Φ ε hε₁ hε₂ c₁ c₂ K' L' =
    mapBifunctorBicomplexMap E E' Φ₁ Φ₂ Φ ε hε₁ hε₂ c₁ c₂ K L ≫
      ((Φ.mapHomologicalComplex c₂).mapHomologicalComplex c₁).map
        (((E.mapBifunctorHomologicalComplex c₁ c₂).map f).app L ≫
          ((E.mapBifunctorHomologicalComplex c₁ c₂).obj K').map g) := by
  ext i₁ i₂
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Functor.mapBifunctorHomologicalComplex_map_app_f_f,
    Functor.mapBifunctorHomologicalComplex_obj_map_f_f, mapBifunctorBicomplexMap, Category.assoc]
  refine (congrArg (_ ≫ ·) (hε₂ (K'.X i₁) (g.f i₂))).trans ?_
  refine ((reassoc_of% (hε₁ (f.f i₁) (L.X i₂))) _).trans ?_
  exact congrArg (ε (K.X i₁) (L.X i₂) ≫ ·) (Φ.map_comp _ _).symm

/-- **The comparison of total complexes is natural in the two complexes.** -/
theorem mapBifunctorTotalMap_naturality {K K' : HomologicalComplex CA c₁}
    {L L' : HomologicalComplex CB c₂} (f : K ⟶ K') (g : L ⟶ L')
    [HomologicalComplex.HasMapBifunctor K L E c]
    [HomologicalComplex.HasMapBifunctor ((Φ₁.mapHomologicalComplex c₁).obj K)
      ((Φ₂.mapHomologicalComplex c₂).obj L) E' c]
    [HomologicalComplex₂.HasTotal (HomologicalComplex₂.mapBicomplex Φ
      (((E.mapBifunctorHomologicalComplex c₁ c₂).obj K).obj L)) c]
    [HomologicalComplex.HasMapBifunctor K' L' E c]
    [HomologicalComplex.HasMapBifunctor ((Φ₁.mapHomologicalComplex c₁).obj K')
      ((Φ₂.mapHomologicalComplex c₂).obj L') E' c]
    [HomologicalComplex₂.HasTotal (HomologicalComplex₂.mapBicomplex Φ
      (((E.mapBifunctorHomologicalComplex c₁ c₂).obj K').obj L')) c] :
    HomologicalComplex.mapBifunctorMap ((Φ₁.mapHomologicalComplex c₁).map f)
        ((Φ₂.mapHomologicalComplex c₂).map g) E' c ≫
      mapBifunctorTotalMap E E' Φ₁ Φ₂ Φ ε hε₁ hε₂ c₁ c₂ c K' L' =
    mapBifunctorTotalMap E E' Φ₁ Φ₂ Φ ε hε₁ hε₂ c₁ c₂ c K L ≫
      (Φ.mapHomologicalComplex c).map (HomologicalComplex.mapBifunctorMap f g E c) := by
  dsimp only [mapBifunctorTotalMap, HomologicalComplex.mapBifunctorMap]
  rw [← Category.assoc, ← HomologicalComplex₂.total.map_comp,
    mapBifunctorBicomplexMap_naturality, HomologicalComplex₂.total.map_comp, Category.assoc,
    HomologicalComplex₂.totalMap_naturality, Category.assoc]

end Stacks.Cohomology.LinearCupProductFamily

end
