module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.SiteEquivalenceKFlatTransport

/-!
# Flatness and K-flatness transported along the inverse of a reindexing

Let `e : C' ≌ C` be an equivalence of sites and `𝒪` a sheaf of commutative rings on `(C, J)`,
and let `Φ` be the reindexing of `𝒪`-modules along `e`,
`Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.reindexMod`.  The functor of `Φ` carries
flat modules and K-flat complexes to flat modules and K-flat complexes:
`Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.isFlat_reindexMod_functor_obj` and
`kFlat_reindexMod_mapHomologicalComplex`.  This file proves the same for the *inverse* of `Φ`,
which is the direction a consumer needs when the equivalence of module categories it works with
is `Φ.symm`: a relocalization of modules along an equivalence of small étale sites, for
instance, is stated as such a `symm`.

## Main results

* `CochainComplex.KFlatBifunctor.exactFunctor_flip_obj_of_exactFunctor_flip_obj_map` and
  `CochainComplex.KFlatBifunctor.kFlat_of_kFlat_map_of_equivalence`: an equivalence carrying a
  bifunctor `F` to a bifunctor `F'` *reflects* flatness and K-flatness.
* `CochainComplex.KFlatBifunctor.exactFunctor_flip_obj_inverse_of_equivalence` and
  `CochainComplex.KFlatBifunctor.kFlat_map_inverse_of_equivalence`: its inverse preserves them.
* `Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.isFlat_reindexMod_inverse_obj` and
  `kFlat_reindexMod_inverse_mapHomologicalComplex`, in the same namespace: the inverse of the
  reindexing carries flat modules to flat modules and K-flat complexes to K-flat complexes.

## Implementation notes

Only the comparison `ε : e(F(a, b)) ≅ F'(e a, e b)` of the *functor* of the equivalence is used,
with its naturality squares; no comparison for the inverse is built.  Reflection is read off the
same comparison: `F(-, M)` is `e⁻¹ ∘ F'(-, e M) ∘ e` up to `ε` and the unit, and a complex is
acyclic as soon as its image under `e` is.  Preservation by the inverse is then reflection
applied to `e(e⁻¹ M) ≅ M`, through the counit.  For the reindexing, `ε` is the comparison of
tensor products of [Stacks, Tag 01CU], `Stacks.SheafOfModules.TensorPower.whiskerTensorSheafIso`,
exactly as in the forward direction.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v' u' v u

namespace CochainComplex.KFlatBifunctor

section Flat

variable {A A' : Type*} [Category A] [Category A'] [Abelian A] [Abelian A']
  (F : A ⥤ A ⥤ A) (F' : A' ⥤ A' ⥤ A') (e : A ≌ A')
  (ε : ∀ a b : A, e.functor.obj ((F.obj a).obj b) ≅
    (F'.obj (e.functor.obj a)).obj (e.functor.obj b))
  (hε₁ : ∀ {a a' : A} (f : a ⟶ a') (b : A),
    e.functor.map ((F.map f).app b) ≫ (ε a' b).hom =
      (ε a b).hom ≫ (F'.map (e.functor.map f)).app (e.functor.obj b))

omit [Abelian A] [Abelian A'] in
include hε₁ in
/-- **An equivalence carrying `F` to `F'` reflects flatness**, flatness of `M` being exactness of
`F(-, M)`.  Up to `ε` and the unit of `e`, `F(-, M)` is `e⁻¹ ∘ F'(-, e M) ∘ e`, a composite of
exact functors. -/
theorem exactFunctor_flip_obj_of_exactFunctor_flip_obj_map (M : A)
    (hM : exactFunctor A' A' (F'.flip.obj (e.functor.obj M))) :
    exactFunctor A A (F.flip.obj M) := by
  let σ : F.flip.obj M ⋙ e.functor ≅ e.functor ⋙ F'.flip.obj (e.functor.obj M) :=
    NatIso.ofComponents (fun G => ε G M) (fun g => hε₁ g M)
  let iso : e.functor ⋙ F'.flip.obj (e.functor.obj M) ⋙ e.inverse ≅ F.flip.obj M :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight σ.symm e.inverse ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (F.flip.obj M) e.unitIso.symm ≪≫
      Functor.rightUnitor _
  obtain ⟨_, _⟩ := (exactFunctor_iff _).1 hM
  exact (exactFunctor _ _).prop_of_iso iso
    ((exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩)

omit [Abelian A] [Abelian A'] in
include hε₁ in
/-- **The inverse of an equivalence carrying `F` to `F'` carries flat objects to flat objects.**
`F'(-, M')` is `F'(-, e(e⁻¹ M'))` through the counit, and flatness of `e⁻¹ M'` is reflected from
it by `CochainComplex.KFlatBifunctor.exactFunctor_flip_obj_of_exactFunctor_flip_obj_map`. -/
theorem exactFunctor_flip_obj_inverse_of_equivalence (M' : A')
    (hM : exactFunctor A' A' (F'.flip.obj M')) :
    exactFunctor A A (F.flip.obj (e.inverse.obj M')) :=
  exactFunctor_flip_obj_of_exactFunctor_flip_obj_map F F' e ε hε₁ (e.inverse.obj M')
    ((exactFunctor _ _).prop_of_iso (F'.flip.mapIso (e.counitIso.app M')).symm hM)

end Flat

section KFlat

variable {A A' : Type*} [Category A] [Category A'] [Abelian A] [Abelian A']
  (F : A ⥤ A ⥤ A) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ K₂ : CochainComplex A ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]
  (F' : A' ⥤ A' ⥤ A') [F'.Additive] [∀ X, (F'.obj X).Additive]
  [∀ (K₁ K₂ : CochainComplex A' ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ F' (ComplexShape.up ℤ)]
  (e : A ≌ A') [e.functor.Additive] [e.inverse.Additive]
  (ε : ∀ a b : A, e.functor.obj ((F.obj a).obj b) ≅
    (F'.obj (e.functor.obj a)).obj (e.functor.obj b))
  (hε₁ : ∀ {a a' : A} (f : a ⟶ a') (b : A),
    e.functor.map ((F.map f).app b) ≫ (ε a' b).hom =
      (ε a b).hom ≫ (F'.map (e.functor.map f)).app (e.functor.obj b))
  (hε₂ : ∀ (a : A) {b b' : A} (g : b ⟶ b'),
    e.functor.map ((F.obj a).map g) ≫ (ε a b').hom =
      (ε a b).hom ≫ (F'.obj (e.functor.obj a)).map (e.functor.map g))

/-- **The unit of `e`, read on cochain complexes**: applying `e⁻¹` to the image of a complex
under `e` gives the complex back.  This is the companion of
`CochainComplex.KFlatBifunctor.equivalenceCounitComplexIso`. -/
def equivalenceUnitComplexIso (G : CochainComplex A ℤ) :
    (e.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((e.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj G) ≅ G :=
  HomologicalComplex.Hom.isoOfComponents (fun i => e.unitIso.symm.app (G.X i))
    (fun i j _ => by simp)

include ε hε₁ hε₂

/-- **An equivalence carrying `F` to `F'` reflects K-flat complexes.**  For an acyclic `G`, the
complex `e G` is acyclic, so `Tot(F'(e G, e L))` is acyclic by hypothesis; it is
`e(Tot(F(G, L)))` by the comparison, and a complex whose image under `e` is acyclic is acyclic,
`e⁻¹` being exact and the unit of `e` an isomorphism. -/
theorem kFlat_of_kFlat_map_of_equivalence (L : CochainComplex A ℤ)
    (hL : KFlat F' ((e.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) :
    KFlat F L := by
  let := fun K L => hasTotal_mapBicomplex_of_equivalence F F' e ε hε₁ hε₂ K L
  intro G hG
  have h : ((e.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (totalComplex F G L)).Acyclic := fun i =>
    HomologicalComplex.ExactAt.of_iso (hL _ (hG.map e.functor) i)
      (transportComplexIso F F' e.functor e.functor e.functor ε hε₁ hε₂ G L).symm
  exact fun i => HomologicalComplex.ExactAt.of_iso ((h.map e.inverse) i)
    (equivalenceUnitComplexIso e (totalComplex F G L))

/-- **The inverse of an equivalence carrying `F` to `F'` carries K-flat complexes to K-flat
complexes.**  `L'` is `e(e⁻¹ L')` through the counit, and K-flatness of `e⁻¹ L'` is reflected
from it by `CochainComplex.KFlatBifunctor.kFlat_of_kFlat_map_of_equivalence`. -/
theorem kFlat_map_inverse_of_equivalence (L' : CochainComplex A' ℤ) (hL : KFlat F' L') :
    KFlat F ((e.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj L') :=
  kFlat_of_kFlat_map_of_equivalence F F' e ε hε₁ hε₂ _
    (KFlat.of_iso F' hL (equivalenceCounitComplexIso e L').symm)

end KFlat

end CochainComplex.KFlatBifunctor

namespace Stacks.SheafOfModules.SiteEquivalenceDerivedTensor

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {J : GrothendieckTopology C} (J' : GrothendieckTopology C')
  (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  [e.functor.IsCocontinuous J' J]
  (O : Sheaf J CommRingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify J' AddCommGrpCat.{w}] [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The inverse of the reindexing along an equivalence of ringed sites carries flat modules to
flat modules.**  This is
`CochainComplex.KFlatBifunctor.exactFunctor_flip_obj_inverse_of_equivalence` at the comparison of
tensor products of [Stacks, Tag 01CU], the input of
`Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.isFlat_reindexMod_functor_obj`. -/
theorem isFlat_reindexMod_inverse_obj
    (M : _root_.SheafOfModules.{w} (Tensor.ringSheaf.{u', v', w} (reindexCommRingGeneral J' e O)))
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{v', u', w, w}
      (O := reindexCommRingGeneral J' e O) M) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := O)
      ((reindexMod J' e O).inverse.obj M) :=
  CochainComplex.KFlatBifunctor.exactFunctor_flip_obj_inverse_of_equivalence
    (Tensor.sheafTensor.{u, v, w} O)
    (Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O)) (reindexMod J' e O)
    (TensorPower.whiskerTensorSheafIso (J' := J') O.val (Tensor.ringSheaf.{u, v, w} O).cond
      e.functor)
    (fun f N => reindexTensorIso_naturality_left J' e O f N) M hM

/-- **The inverse of the reindexing along an equivalence of ringed sites carries K-flat complexes
to K-flat complexes.**  This is `CochainComplex.KFlatBifunctor.kFlat_map_inverse_of_equivalence`
at the comparison of tensor products of [Stacks, Tag 01CU]; with
`Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.isFlat_reindexMod_inverse_obj` it carries the
K-flat complexes with flat terms, the resolving class of the derived pullback of Stacks 06YY,
into the same class. -/
theorem kFlat_reindexMod_inverse_mapHomologicalComplex
    [(Tensor.sheafTensor.{u, v, w} O).Additive]
    [∀ M, ((Tensor.sheafTensor.{u, v, w} O).obj M).Additive]
    [∀ (K L : CochainComplex (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u, v, w} O)) ℤ),
      HomologicalComplex.HasMapBifunctor K L (Tensor.sheafTensor.{u, v, w} O) (ComplexShape.up ℤ)]
    [(Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O)).Additive]
    [∀ M, ((Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O)).obj M).Additive]
    [∀ (K L : CochainComplex
        (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u', v', w} (reindexCommRingGeneral J' e O)))
        ℤ),
      HomologicalComplex.HasMapBifunctor K L
        (Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O)) (ComplexShape.up ℤ)]
    (K : CochainComplex
      (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u', v', w} (reindexCommRingGeneral J' e O))) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O)) K) :
    CochainComplex.KFlatBifunctor.KFlat (Tensor.sheafTensor.{u, v, w} O)
      (((reindexMod J' e O).inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  CochainComplex.KFlatBifunctor.kFlat_map_inverse_of_equivalence (Tensor.sheafTensor.{u, v, w} O)
    (Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O)) (reindexMod J' e O)
    (TensorPower.whiskerTensorSheafIso (J' := J') O.val (Tensor.ringSheaf.{u, v, w} O).cond
      e.functor)
    (fun f N => reindexTensorIso_naturality_left J' e O f N)
    (fun M {_ _} g => reindexTensorIso_naturality_right J' e O M g) K hK

end Stacks.SheafOfModules.SiteEquivalenceDerivedTensor

end
