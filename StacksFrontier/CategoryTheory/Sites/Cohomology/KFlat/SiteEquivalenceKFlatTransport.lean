module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.SiteEquivalenceDerivedTensorTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRetract
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove

/-!
# Flatness and K-flatness transported along an equivalence of ringed sites

Let `e : C' ≌ C` be an equivalence of categories which is an equivalence of sites for topologies
`J'` on `C'` and `J` on `C`, and let `𝒪` be a sheaf of commutative rings on `(C, J)`.  The
reindexing `Φ` of sheaves of modules along `e`
(`Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.reindexMod`) carries

* a flat `𝒪`-module to a flat `𝒪|_{C'}`-module, and
* a K-flat complex of `𝒪`-modules to a K-flat complex of `𝒪|_{C'}`-modules,

so that it carries the resolving class of K-flat complexes with flat terms, the class the derived
pullback of Stacks 06YY is computed on, into the same class on the other site.

## Main results

* `Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.isFlat_reindexMod_functor_obj`: flatness is
  preserved by the reindexing.
* `Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.kFlat_reindexMod_mapHomologicalComplex`:
  K-flatness is preserved by the reindexing.

## Implementation notes

Both are read off the comparison of tensor products along the reindexing,
`Stacks.SheafOfModules.TensorPower.whiskerTensorSheafIso` ([Stacks, Tag 01CU]), together with its
naturality in the first variable,
`Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.reindexTensorIso_naturality_left`.  For
K-flatness the general engine `CochainComplex.KFlatBifunctor.kFlat_map_of_equivalence` consumes
exactly that comparison.  For flatness, which is exactness of `- ⊗ M`, the comparison exhibits
`- ⊗ Φ M` as `Φ ∘ (- ⊗ M) ∘ Φ⁻¹`, a composite of exact functors.

The sections universe `w` is independent of the two site universes, so the sheaf-condition
composition through which flatness is stated is supplied by
`Stacks.hasSheafCompose_forget₂_commRingCat`, as in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FlatRetract.lean`.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v' u' v u

namespace CochainComplex.KFlatBifunctor

section Generic

variable {A A' : Type*} [Category A] [Category A'] [Abelian A] [Abelian A']
  (F : A ⥤ A ⥤ A) (F' : A' ⥤ A' ⥤ A') (e : A ≌ A')
  (ε : ∀ a b : A, e.functor.obj ((F.obj a).obj b) ≅
    (F'.obj (e.functor.obj a)).obj (e.functor.obj b))
  (hε₁ : ∀ {a a' : A} (f : a ⟶ a') (b : A),
    e.functor.map ((F.map f).app b) ≫ (ε a' b).hom =
      (ε a b).hom ≫ (F'.map (e.functor.map f)).app (e.functor.obj b))

omit [Abelian A] [Abelian A'] in
include hε₁ in
/-- **An equivalence carrying `F` to `F'` carries flat objects to flat objects**, flatness of `M`
being exactness of `F(-, M)`.  Up to `ε` and the counit of `e`, `F'(-, e M)` is
`e ∘ F(-, M) ∘ e⁻¹`, a composite of exact functors. -/
theorem exactFunctor_flip_obj_of_equivalence (M : A) (hM : exactFunctor A A (F.flip.obj M)) :
    exactFunctor A' A' (F'.flip.obj (e.functor.obj M)) := by
  let iso : e.inverse ⋙ F.flip.obj M ⋙ e.functor ≅ F'.flip.obj (e.functor.obj M) :=
    NatIso.ofComponents (fun G => ε (e.inverse.obj G) M ≪≫
      (F'.mapIso (e.counitIso.app G)).app (e.functor.obj M)) (by
      intro G G' g
      simp only [Functor.comp_map, Functor.flip_obj_map, Iso.trans_hom, Iso.app_hom,
        Functor.mapIso_hom]
      rw [← Category.assoc, hε₁, Category.assoc, Category.assoc, ← NatTrans.comp_app,
        ← Functor.map_comp, ← NatTrans.comp_app, ← Functor.map_comp]
      congr 3
      exact e.counitIso.hom.naturality g)
  have hM' := (exactFunctor_iff _).1 hM
  have := hM'.1
  have := hM'.2
  have hcomp : exactFunctor _ _ (e.inverse ⋙ F.flip.obj M ⋙ e.functor) :=
    (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩
  exact (exactFunctor _ _).prop_of_iso iso hcomp

end Generic

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

/-- **The reindexing along an equivalence of ringed sites carries flat modules to flat
modules.**  Tensoring with `Φ M` is `Φ ∘ (- ⊗ M) ∘ Φ⁻¹` up to the comparison of tensor products
of [Stacks, Tag 01CU] and the counit of the equivalence, and a composite of exact functors is
exact. -/
theorem isFlat_reindexMod_functor_obj
    (M : _root_.SheafOfModules.{w} (Tensor.ringSheaf.{u, v, w} O))
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := O) M) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v', u', w, w} (O := reindexCommRingGeneral J' e O)
      ((reindexMod J' e O).functor.obj M) :=
  CochainComplex.KFlatBifunctor.exactFunctor_flip_obj_of_equivalence
    (Tensor.sheafTensor.{u, v, w} O)
    (Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O)) (reindexMod J' e O)
    (TensorPower.whiskerTensorSheafIso (J' := J') O.obj (Tensor.ringSheaf.{u, v, w} O).property
      e.functor)
    (fun f N => reindexTensorIso_naturality_left J' e O f N) M hM

/-- **The reindexing along an equivalence of ringed sites carries K-flat complexes to K-flat
complexes.**  This is `CochainComplex.KFlatBifunctor.kFlat_map_of_equivalence` at the comparison
of tensor products of [Stacks, Tag 01CU]. -/
theorem kFlat_reindexMod_mapHomologicalComplex
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
    (K : CochainComplex (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u, v, w} O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Tensor.sheafTensor.{u, v, w} O) K) :
    CochainComplex.KFlatBifunctor.KFlat
      (Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O))
      (((reindexMod J' e O).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  CochainComplex.KFlatBifunctor.kFlat_map_of_equivalence (Tensor.sheafTensor.{u, v, w} O)
    (Tensor.sheafTensor.{u', v', w} (reindexCommRingGeneral J' e O)) (reindexMod J' e O)
    (TensorPower.whiskerTensorSheafIso (J' := J') O.obj (Tensor.ringSheaf.{u, v, w} O).property
      e.functor)
    (fun f N => reindexTensorIso_naturality_left J' e O f N)
    (fun M {_ _} g => reindexTensorIso_naturality_right J' e O M g) K hK

end Stacks.SheafOfModules.SiteEquivalenceDerivedTensor

end
