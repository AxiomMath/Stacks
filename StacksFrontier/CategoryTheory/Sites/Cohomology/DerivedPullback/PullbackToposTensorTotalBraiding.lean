module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposUnitorCoherence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetrySummand

/-! # The comparison of total tensor complexes under pullback is braided

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi presented by a functor `f.u`
of the underlying sites which is a morphism of sites, and let `f^*` be the pullback of sheaves of
modules attached to that presentation. For unbounded cochain complexes `K`, `L` of
`𝒪_D`-modules there are two isomorphisms in play: the comparison of total tensor complexes

`f^*Tot(K ⊗_{𝒪_D} L) ≅ Tot(f^*K ⊗_{𝒪_C} f^*L)`

of `Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso`, and the Koszul symmetry
`Tot(K ⊗_R L) ≅ Tot(L ⊗_R K)` of `Stacks.SheafOfModules.Tensor.tensorComplexFlipIso`, over `𝒪_D`
and over `𝒪_C`. The square they form commutes, provided the comparison
`f^*(A ⊗_{𝒪_D} B) ⟶ f^*A ⊗_{𝒪_C} f^*B` intertwines the sectionwise symmetries of the tensor
product sheaf in each bidegree. Neither complex is assumed bounded or flat.

## Main results

* `Stacks.Sheaves.DerivedPullback.hom_ext_pullbackToposTotal`: two morphisms out of
  `f^*Tot(K ⊗_{𝒪_D} L)` in a given total degree agree as soon as they agree after the
  `f^*`-image of each summand inclusion.
* `Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso_braiding_of_module`: the
  comparison of total tensor complexes is braided for the Koszul symmetry, granted the
  module-level braiding in each bidegree.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Section 20.48 (Tag 06YM)](https://stacks.math.columbia.edu/tag/06YM)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.DerivedPullback.KFlatPullback

namespace Stacks.Sheaves.DerivedPullback

/-! ## Reassociation around a Koszul sign -/

section Generic

variable {Z : Type*} [Category Z] [Preadditive Z]

/-- Reassociation of `a ≫ b ≫ t` when `a ≫ b` is a signed composite `s • (x ≫ y)` and
`y ≫ t = m ≫ j`. -/
lemma units_smul_comp_reassoc {A B D E G H : Z} (s : ℤˣ)
    {a : A ⟶ B} {b : B ⟶ D} {t : D ⟶ G}
    {x : A ⟶ E} {y : E ⟶ D} {m : E ⟶ H} {j : H ⟶ G}
    (hFirst : a ≫ b = s • (x ≫ y)) (hTail : y ≫ t = m ≫ j) :
    a ≫ b ≫ t = s • ((x ≫ m) ≫ j) := by
  rw [← Category.assoc, hFirst, Linear.units_smul_comp, Category.assoc, hTail, ← Category.assoc]

/-- Reassociation of `a ≫ c ≫ w` when `a ≫ c = m ≫ i` and the tail `i ≫ w` is a signed
composite `s • (b ≫ j)`. -/
lemma comp_units_smul_reassoc {A B D E G H : Z} (s : ℤˣ)
    {a : A ⟶ B} {c : B ⟶ D} {w : D ⟶ G}
    {m : A ⟶ E} {i : E ⟶ D} {b : E ⟶ H} {j : H ⟶ G}
    (hFirst : a ≫ c = m ≫ i) (hTail : i ≫ w = s • (b ≫ j)) :
    a ≫ c ≫ w = s • ((m ≫ b) ≫ j) := by
  rw [← Category.assoc, hFirst, Category.assoc, hTail, Linear.comp_units_smul, ← Category.assoc]

end Generic

section SiteMorphism

universe u

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y)

/-- Two morphisms out of `f^*Tot(K ⊗_{𝒪_D} L)` in a given total degree agree as soon as they
agree after the `f^*`-image of each summand inclusion. -/
lemma hom_ext_pullbackToposTotal (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (n : ℤ) {A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {u v : ((pullbackComplex f).obj (HomologicalComplex.mapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ))).X n ⟶ A}
    (h : ∀ (p q : ℤ) (hpq : p + q = n),
      f.pullbackTopos.map (HomologicalComplex.ιMapBifunctor K L
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
            (ComplexShape.up ℤ) p q n hpq) ≫ u =
        f.pullbackTopos.map (HomologicalComplex.ιMapBifunctor K L
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
            (ComplexShape.up ℤ) p q n hpq) ≫ v) :
    u = v := by
  refine (cancel_epi ((pullbackModulesSiteIso f hmos).app
      ((HomologicalComplex.mapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
          (ComplexShape.up ℤ)).X n)).hom).mp
    (hom_ext_pullbackTotal (modulesHomOfSiteHom f hmos) K L n (fun p q hpq => ?_))
  exact ((pullbackModulesSiteIso f hmos).hom.naturality_assoc _ u).trans
    ((congrArg (fun m => (pullbackModulesSiteIso f hmos).hom.app _ ≫ m) (h p q hpq)).trans
      ((pullbackModulesSiteIso f hmos).hom.naturality_assoc _ v).symm)

/-- The comparison of total tensor complexes `f^*Tot(K ⊗ L) ≅ Tot(f^*K ⊗ f^*L)` intertwines the
Koszul symmetries over `𝒪_D` and over `𝒪_C`, provided the module-level comparison intertwines the
symmetries of the tensor product sheaf in each bidegree (`hmod`). -/
theorem pullbackToposTensorTotalIso_braiding_of_module (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hmod : ∀ p q : ℤ,
      f.pullbackTopos.map
            (((Stacks.SheafOfModules.Tensor.sheafTensorBraiding Y.O).hom.app (K.X p)).app
              (L.X q)) ≫
          pullbackToposTensorMapDeg f hmos L K q p =
        pullbackToposTensorMapDeg f hmos K L p q ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding X.O).hom.app
            (((pullbackComplex f).obj K).X p)).app (((pullbackComplex f).obj L).X q)) :
    (pullbackComplex f).map (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso Y.O K L).hom ≫
        (pullbackToposTensorTotalIso f hmos L K).hom =
      (pullbackToposTensorTotalIso f hmos K L).hom ≫
        (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso X.O
          ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)).hom := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  refine hom_ext_pullbackToposTotal f hmos K L n (fun p q hpq => ?_)
  have hqp : q + p = n := by lia
  have hFirst :
      f.pullbackTopos.map (HomologicalComplex.ιMapBifunctor K L
            (sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ) p q n hpq) ≫
          f.pullbackTopos.map
            ((Stacks.SheafOfModules.Tensor.tensorComplexFlipIso Y.O K L).hom.f n) =
        ((p * q).negOnePow : ℤˣ) •
          (f.pullbackTopos.map
              (((Stacks.SheafOfModules.Tensor.sheafTensorBraiding Y.O).hom.app (K.X p)).app
                (L.X q)) ≫
            f.pullbackTopos.map (HomologicalComplex.ιMapBifunctor L K
              (sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ) q p n hqp)) :=
    (f.pullbackTopos.map_comp _ _).symm.trans
      ((congrArg f.pullbackTopos.map
          (Stacks.SheafOfModules.Tensor.ι_tensorComplexFlipIso_hom Y.O K L p q n hpq hqp)).trans
        ((f.pullbackTopos.map_units_smul _ _).trans
          (congrArg (fun morphism => ((p * q).negOnePow : ℤˣ) • morphism)
            (f.pullbackTopos.map_comp _ _))))
  exact (units_smul_comp_reassoc _ hFirst
      (ι_pullbackToposTensorTotalIso_hom f hmos L K q p n hqp)).trans
    ((congrArg (fun morphism => ((p * q).negOnePow : ℤˣ) •
        (morphism ≫ HomologicalComplex.ιMapBifunctor ((pullbackComplex f).obj L)
          ((pullbackComplex f).obj K) (sheafTensor.{u, u, u, u, u} X.O)
          (ComplexShape.up ℤ) q p n hqp)) (hmod p q)).trans
      (comp_units_smul_reassoc _ (ι_pullbackToposTensorTotalIso_hom f hmos K L p q n hpq)
        (Stacks.SheafOfModules.Tensor.ι_tensorComplexFlipIso_hom X.O
          ((pullbackComplex f).obj K) ((pullbackComplex f).obj L) p q n hpq hqp)).symm)

end SiteMorphism

end Stacks.Sheaves.DerivedPullback

end
