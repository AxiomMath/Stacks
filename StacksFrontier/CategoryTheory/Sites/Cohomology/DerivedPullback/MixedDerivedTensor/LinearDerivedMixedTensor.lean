module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MixedTensorBifunctor
public import StacksFrontier.Homology.KFlat.BifunctorOneSidedDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.MixedDerivedTensor.DerivedMixedTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.MixedDerivedTensor.LinearMixedDerivedTensor

/-!
# Stacks 08I6 in `D(O)`

Let `f : (Sh(C), O) ⟶ (Sh(C'), O')` be a morphism of ringed topoi.  Stacks 08I6 asserts a
canonical bifunctorial isomorphism

`F ⊗^L_O Lf^*G ≅ F ⊗^L_{f⁻¹O'} f⁻¹G`

for `F` in `D(O)` and `G` in `D(O')`.  Both sides are objects of `D(O)`: on the right the
tensor product over the smaller sheaf of rings `f⁻¹O' ⟶ O` carries the `O`-action of its first
factor.  This file constructs the derived tensor product over `f⁻¹O'` of a complex of
`O`-modules and a complex of `f⁻¹O'`-modules as an object of `D(O)` and proves the tag there.

The derived mixed tensor product is the derived bifunctor of the mixed tensor product of
sheaves of modules `(H, N) ↦ (H ⊗_{f⁻¹O'} N)^#` (`Stacks.MixedBaseChange.mixedSheafTensor`),
computed by K-flat resolutions with flat terms of the second factor: for such an `N` the total
complex `Tot(H ⊗_{f⁻¹O'} N)` inverts quasi-isomorphisms in `H` and is invariant under
quasi-isomorphisms of `N`, because `H ⊗_{f⁻¹O'} N ≅ H ⊗_O (O ⊗_{f⁻¹O'} N)` as sheaves of
`O`-modules and `O ⊗_{f⁻¹O'} N` is K-flat with flat terms over `O` (Stacks 0G7E).

The proof of the tag is the source's: on a complex `F` of `O`-modules and a K-flat complex `G`
of `O'`-modules with flat terms both sides are total complexes, and the underived identity
`F ⊗_O f^*G ≅ F ⊗_{f⁻¹O'} f⁻¹G` of sheaves of `O`-modules identifies them in each bidegree.

## Main definitions

* `Stacks.Cohomology.MixedDerivedTensor.mixedTensorBifunctor`: the mixed tensor product over
  `f⁻¹O'`, a bifunctor from sheaves of `O`-modules and sheaves of `f⁻¹O'`-modules to sheaves of
  `O`-modules.
* `Stacks.Cohomology.MixedDerivedTensor.mixedDerivedTensor`: **the derived tensor product over
  `f⁻¹O'`**, `D(O) ⥤ D(f⁻¹O') ⥤ D(O)`.
* `Stacks.Cohomology.MixedDerivedTensor.linearMixedDerivedTensorInverseImage`: the right-hand
  bifunctor `D(O) × D(O') ⥤ D(O)` of the tag, through `mixedDerivedTensor`; the left-hand one is
  `Stacks.Cohomology.MixedDerivedTensor.linearDerivedTensorPullback`.
* `Stacks.Cohomology.MixedDerivedTensor.linearDerivedMixedTensorIso`: **Stacks 08I6**, in
  `D(O)`.

## Main results

* `Stacks.Cohomology.MixedDerivedTensor.mixedDerivedTensorComparison`: the derived mixed tensor
  product of a complex `H` of `O`-modules and a K-flat complex `N` of `f⁻¹O'`-modules with flat
  terms is the class of `Tot(H ⊗_{f⁻¹O'} N)`, naturally in both
  (`mixedDerivedTensorComparison_naturality`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Sheaves.DerivedPullback Stacks.Sheaves.DerivedPullback.KFlatPullback

namespace Stacks.Cohomology.MixedDerivedTensor

open StacksPullbackFactorization

/-! ### Total complexes of two bifunctors identified in each bidegree -/

section TotalTransport

variable {A B B' E D : Type*} [Category A] [Category B] [Category B'] [Category E] [Category D]
  [HasZeroMorphisms A] [HasZeroMorphisms B] [HasZeroMorphisms B'] [HasZeroMorphisms E]
  [Preadditive D]
  (M : A ⥤ B ⥤ D) (T : A ⥤ B' ⥤ D)
  [M.PreservesZeroMorphisms] [∀ X, (M.obj X).PreservesZeroMorphisms]
  [T.PreservesZeroMorphisms] [∀ X, (T.obj X).PreservesZeroMorphisms]
  (Φ : E ⥤ B) (Ψ : E ⥤ B') [Φ.PreservesZeroMorphisms] [Ψ.PreservesZeroMorphisms]
  (ε : ∀ (a : A) (e : E), (M.obj a).obj (Φ.obj e) ≅ (T.obj a).obj (Ψ.obj e))
  (h₁ : ∀ {a a' : A} (u : a ⟶ a') (e : E),
    (M.map u).app (Φ.obj e) ≫ (ε a' e).hom = (ε a e).hom ≫ (T.map u).app (Ψ.obj e))
  (h₂ : ∀ (a : A) {e e' : E} (v : e ⟶ e'),
    (M.obj a).map (Φ.map v) ≫ (ε a e').hom = (ε a e).hom ≫ (T.obj a).map (Ψ.map v))

/-- The double complexes `(p, q) ↦ M(K^p, Φ L^q)` and `(p, q) ↦ T(K^p, Ψ L^q)` are isomorphic,
given an identification `ε` of the two bifunctors natural in both variables. -/
def transportBicomplexIso (K : CochainComplex A ℤ) (L : CochainComplex E ℤ) :
    ((M.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj
        ((Φ.mapHomologicalComplex (.up ℤ)).obj L) ≅
      ((T.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj
        ((Ψ.mapHomologicalComplex (.up ℤ)).obj L) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ HomologicalComplex.Hom.isoOfComponents (fun q ↦ ε (K.X p) (L.X q))
      (fun q q' _ ↦ (h₂ (K.X p) (L.d q q')).symm))
    (fun p p' _ ↦ by
      ext q
      exact (h₁ (K.d p p') (L.X q)).symm)

section Pair

variable (K : CochainComplex A ℤ) (L : CochainComplex E ℤ)
  [HomologicalComplex.HasMapBifunctor K ((Φ.mapHomologicalComplex (.up ℤ)).obj L) M (.up ℤ)]
  [HomologicalComplex.HasMapBifunctor K ((Ψ.mapHomologicalComplex (.up ℤ)).obj L) T (.up ℤ)]

/-- **The total complexes `Tot(M(K, Φ L))` and `Tot(T(K, Ψ L))` are isomorphic**, given an
identification `ε` of the two bifunctors natural in both variables. -/
def transportTotalIso :
    HomologicalComplex.mapBifunctor K ((Φ.mapHomologicalComplex (.up ℤ)).obj L) M (.up ℤ) ≅
      HomologicalComplex.mapBifunctor K ((Ψ.mapHomologicalComplex (.up ℤ)).obj L) T (.up ℤ) :=
  HomologicalComplex₂.total.mapIso (transportBicomplexIso M T Φ Ψ ε h₁ h₂ K L) (.up ℤ)

/-- The isomorphism of total complexes acts on the summand of bidegree `(p, q)` by `ε`. -/
@[reassoc]
lemma ι_transportTotalIso_hom (p q n : ℤ) (h : p + q = n) :
    HomologicalComplex.ιMapBifunctor K ((Φ.mapHomologicalComplex (.up ℤ)).obj L) M (.up ℤ)
        p q n h ≫ (transportTotalIso M T Φ Ψ ε h₁ h₂ K L).hom.f n =
      (ε (K.X p) (L.X q)).hom ≫
        HomologicalComplex.ιMapBifunctor K ((Ψ.mapHomologicalComplex (.up ℤ)).obj L) T (.up ℤ)
          p q n h :=
  HomologicalComplex₂.ιTotal_map _ _ (transportBicomplexIso M T Φ Ψ ε h₁ h₂ K L).hom
    (.up ℤ) p q n h

end Pair

omit [HasZeroMorphisms A] [HasZeroMorphisms E] [M.PreservesZeroMorphisms]
  [∀ X, (M.obj X).PreservesZeroMorphisms] [T.PreservesZeroMorphisms]
  [∀ X, (T.obj X).PreservesZeroMorphisms] [Φ.PreservesZeroMorphisms]
  [Ψ.PreservesZeroMorphisms] [HasZeroMorphisms B] [HasZeroMorphisms B'] [Preadditive D] in
include h₁ h₂ in
/-- The two naturality squares of `ε`, merged. -/
lemma transport_square {a a' : A} (u : a ⟶ a') {e e' : E} (v : e ⟶ e') :
    (M.map u).app (Φ.obj e) ≫ (M.obj a').map (Φ.map v) ≫ (ε a' e').hom =
      (ε a e).hom ≫ (T.map u).app (Ψ.obj e) ≫ (T.obj a').map (Ψ.map v) := by
  rw [h₂ a' v, ← Category.assoc, h₁ u e, Category.assoc]

include h₁ h₂ in
/-- **The isomorphism of total complexes is natural in both complexes.** -/
lemma transportTotalIso_hom_naturality {K K' : CochainComplex A ℤ} {L L' : CochainComplex E ℤ}
    (u : K ⟶ K') (v : L ⟶ L')
    [HomologicalComplex.HasMapBifunctor K ((Φ.mapHomologicalComplex (.up ℤ)).obj L) M (.up ℤ)]
    [HomologicalComplex.HasMapBifunctor K ((Ψ.mapHomologicalComplex (.up ℤ)).obj L) T (.up ℤ)]
    [HomologicalComplex.HasMapBifunctor K' ((Φ.mapHomologicalComplex (.up ℤ)).obj L') M (.up ℤ)]
    [HomologicalComplex.HasMapBifunctor K' ((Ψ.mapHomologicalComplex (.up ℤ)).obj L') T
      (.up ℤ)] :
    HomologicalComplex.mapBifunctorMap u ((Φ.mapHomologicalComplex (.up ℤ)).map v) M (.up ℤ) ≫
        (transportTotalIso M T Φ Ψ ε h₁ h₂ K' L').hom =
      (transportTotalIso M T Φ Ψ ε h₁ h₂ K L).hom ≫
        HomologicalComplex.mapBifunctorMap u ((Ψ.mapHomologicalComplex (.up ℤ)).map v) T
          (.up ℤ) := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.ι_mapBifunctorMap_assoc, ι_transportTotalIso_hom_assoc,
    ι_transportTotalIso_hom, HomologicalComplex.ι_mapBifunctorMap]
  simp only [Functor.mapHomologicalComplex_map_f]
  have hsq := transport_square M T Φ Ψ ε h₁ h₂ (u.f p) (v.f q)
  simp only [← Category.assoc] at hsq ⊢
  exact congrArg (· ≫ _) hsq

end TotalTransport

attribute [local instance] HasDerivedCategory.standard

attribute [local instance]
  AlgebraicGeometry.SheafOfModules.isRightAdjoint_sheafPushforwardContinuous_commRingCat

universe u

section Underived

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposSiteHom X Y)

/-! ### The mixed tensor product over `f⁻¹O'` -/

/-- **The mixed tensor product over `f⁻¹O'`**: a sheaf `H` of `O`-modules and a sheaf `N` of
`f⁻¹O'`-modules are carried to `(H ⊗_{f⁻¹O'} N)^#`, a sheaf of `O`-modules through `H`. -/
def mixedTensorBifunctor :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (auxTopos f).O) ⥤
        SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  Stacks.MixedBaseChange.mixedSheafTensor ((auxHomH f).fSharp)

/-- The mixed tensor product over `f⁻¹O'` is additive in the first variable. -/
instance mixedTensorBifunctor_additive : (mixedTensorBifunctor f).Additive :=
  Stacks.MixedBaseChange.mixedSheafTensor_additive _

/-- For a fixed sheaf `H` of `O`-modules, `N ↦ (H ⊗_{f⁻¹O'} N)^#` is additive. -/
instance mixedTensorBifunctor_obj_additive
    (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    ((mixedTensorBifunctor f).obj H).Additive :=
  Stacks.MixedBaseChange.mixedSheafTensor_obj_additive _ H

/-- The mixed tensor product of a complex of `O`-modules and a complex of `f⁻¹O'`-modules
admits a total complex. -/
instance hasMapBifunctor_mixedTensorBifunctor
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (L : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (auxTopos f).O)) ℤ) :
    HomologicalComplex.HasMapBifunctor K L (mixedTensorBifunctor f) (ComplexShape.up ℤ) :=
  inferInstance

/-- **The mixed tensor product over `f⁻¹O'` is the tensor product over `O` with the extension of
scalars**: `H ⊗_{f⁻¹O'} N ≅ H ⊗_O h^*N` as sheaves of `O`-modules. -/
def mixedTensorExtendIso (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (auxTopos f).O)) :
    ((mixedTensorBifunctor f).obj H).obj N ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj H).obj
        ((auxHomH f).pullbackTopos.obj N) :=
  ((Stacks.MixedBaseChange.mixedSheafBaseChangeNatIso ((auxHomH f).fSharp) N).app H).symm ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).flip.mapIso
      ((extendScalarsIsoPullbackAuxHomH f).app N)).app H

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- `mixedTensorExtendIso` is natural in the sheaf of `O`-modules. -/
lemma mixedTensorExtendIso_naturality_fst
    {H H' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : H ⟶ H')
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (auxTopos f).O)) :
    ((mixedTensorBifunctor f).map φ).app N ≫ (mixedTensorExtendIso f H' N).hom =
      (mixedTensorExtendIso f H N).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).map φ).app
          ((auxHomH f).pullbackTopos.obj N) :=
  Stacks.MixedBaseChange.paste_squares
    ((Stacks.MixedBaseChange.mixedSheafBaseChangeNatIso ((auxHomH f).fSharp) N).inv.naturality φ)
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).flip.mapIso
      ((extendScalarsIsoPullbackAuxHomH f).app N)).hom.naturality φ)

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- `mixedTensorExtendIso` is natural in the sheaf of `f⁻¹O'`-modules. -/
lemma mixedTensorExtendIso_naturality_snd
    (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {N N' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (auxTopos f).O)}
    (v : N ⟶ N') :
    ((mixedTensorBifunctor f).obj H).map v ≫ (mixedTensorExtendIso f H N').hom =
      (mixedTensorExtendIso f H N).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj H).map
          ((auxHomH f).pullbackTopos.map v) :=
  Stacks.MixedBaseChange.paste_squares
    (Stacks.MixedBaseChange.conj_square
      ((Stacks.MixedBaseChange.mixedSheafBaseChangeNatIso ((auxHomH f).fSharp) N).app H)
      ((Stacks.MixedBaseChange.mixedSheafBaseChangeNatIso ((auxHomH f).fSharp) N').app H)
      (Stacks.MixedBaseChange.mixedSheafBaseChange_naturality_snd ((auxHomH f).fSharp) v H).symm)
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj H).map_comp
      _ _).symm.trans
      ((congrArg ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj H).map
        ((extendScalarsIsoPullbackAuxHomH f).hom.naturality v)).trans
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj H).map_comp _ _)))

/-- **The underived identity of Stacks 08I6 as sheaves of `O`-modules**:
`H ⊗_{f⁻¹O'} f⁻¹G ≅ H ⊗_O f^*G`. -/
def mixedTensorPullbackIso (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    ((mixedTensorBifunctor f).obj H).obj ((auxHomG f).pullbackTopos.obj G) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj H).obj
        (f.pullbackTopos.obj G) :=
  mixedTensorExtendIso f H ((auxHomG f).pullbackTopos.obj G) ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj H).mapIso
      ((pullbackFactorIso f).app G)

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The underived identity is natural in the sheaf of `O`-modules. -/
lemma mixedTensorPullbackIso_naturality_fst
    {H H' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : H ⟶ H')
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    ((mixedTensorBifunctor f).map φ).app ((auxHomG f).pullbackTopos.obj G) ≫
        (mixedTensorPullbackIso f H' G).hom =
      (mixedTensorPullbackIso f H G).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).map φ).app
          (f.pullbackTopos.obj G) :=
  Stacks.MixedBaseChange.paste_squares
    (mixedTensorExtendIso_naturality_fst f φ ((auxHomG f).pullbackTopos.obj G))
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).map φ).naturality
      ((pullbackFactorIso f).hom.app G)).symm

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The underived identity is natural in the sheaf of `O'`-modules. -/
lemma mixedTensorPullbackIso_naturality_snd
    (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {G G' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)} (v : G ⟶ G') :
    ((mixedTensorBifunctor f).obj H).map ((auxHomG f).pullbackTopos.map v) ≫
        (mixedTensorPullbackIso f H G').hom =
      (mixedTensorPullbackIso f H G).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj H).map
          (f.pullbackTopos.map v) :=
  Stacks.MixedBaseChange.paste_squares
    (mixedTensorExtendIso_naturality_snd f H ((auxHomG f).pullbackTopos.map v))
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj H).map_comp
      _ _).symm.trans
      ((congrArg ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj H).map
        ((pullbackFactorIso f).hom.naturality v)).trans
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj H).map_comp _ _)))

end Underived


/-- If a square commutes and its horizontal sides are isomorphisms, the right side is an
isomorphism as soon as the left side is. -/
lemma isIso_of_square {D : Type*} [Category D] {A B A' B' : D} {a : A ⟶ A'} {b : B ⟶ B'}
    (e : A ≅ B) (e' : A' ≅ B') (h : a ≫ e'.hom = e.hom ≫ b) [IsIso a] : IsIso b := by
  have hb : b = e.inv ≫ a ≫ e'.hom := by rw [h, Iso.inv_hom_id_assoc]
  rw [hb]
  infer_instance

/-- If a square commutes and its horizontal sides are isomorphisms, the left side is an
isomorphism as soon as the right side is. -/
lemma isIso_of_square' {D : Type*} [Category D] {A B A' B' : D} {a : A ⟶ A'} {b : B ⟶ B'}
    (e : A ≅ B) (e' : A' ≅ B') (h : a ≫ e'.hom = e.hom ≫ b) [IsIso b] : IsIso a := by
  have ha : a = e.hom ≫ b ≫ e'.inv := by rw [← reassoc_of% h, Iso.hom_inv_id, Category.comp_id]
  rw [ha]
  infer_instance

/-- Naturality of `T.mapIso (Iso.refl ⊠ e)` in the second variable, from naturality of `e`. -/
private theorem map_prod_refl_iso_naturality {C D E : Type*} [Category C] [Category D]
    [Category E] (T : C × D ⥤ E) {x x' : C} (φ : x ⟶ x') {y y' z z' : D} (m : y ⟶ y')
    (n : z ⟶ z') (e : y ≅ z) (e' : y' ≅ z') (h : m ≫ e'.hom = e.hom ≫ n) :
    T.map (φ, m) ≫ (T.mapIso ((Iso.refl x').prod e')).hom =
      (T.mapIso ((Iso.refl x).prod e)).hom ≫ T.map (φ, n) := by
  rw [Functor.mapIso_hom, Functor.mapIso_hom, ← T.map_comp, ← T.map_comp]
  exact congrArg T.map (Prod.ext ((Category.comp_id _).trans (Category.id_comp _).symm) h)

/-! ### The derived tensor product over `f⁻¹O'`, with values in `D(O)` -/

section Derived

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y)
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing f)).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing f)).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (invRing f))) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing f)) (ComplexShape.up ℤ)]

/-- **`Tot(H ⊗_{f⁻¹O'} N) ≅ Tot(H ⊗_O h^*N)`**, for a complex `H` of `O`-modules and a complex
`N` of `f⁻¹O'`-modules: `mixedTensorExtendIso` in each bidegree. -/
def mixedTotalExtendIso
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (N : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (auxTopos f).O)) ℤ) :
    HomologicalComplex.mapBifunctor K N (mixedTensorBifunctor f) (ComplexShape.up ℤ) ≅
      HomologicalComplex.mapBifunctor K ((pullbackComplex (auxHomH f)).obj N)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ) :=
  transportTotalIso (mixedTensorBifunctor f)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
    (𝟭 _) (auxHomH f).pullbackTopos (mixedTensorExtendIso f)
    (fun u e ↦ mixedTensorExtendIso_naturality_fst f u e)
    (fun a _ _ v ↦ mixedTensorExtendIso_naturality_snd f a v) K N

omit [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (invRing f))) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing f)) (ComplexShape.up ℤ)]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing f)).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing f)).obj M).Additive] in
/-- `mixedTotalExtendIso` is natural in both complexes. -/
lemma mixedTotalExtendIso_hom_naturality
    {K K' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {N N' : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (auxTopos f).O)) ℤ}
    (u : K ⟶ K') (v : N ⟶ N') :
    HomologicalComplex.mapBifunctorMap u v (mixedTensorBifunctor f) (ComplexShape.up ℤ) ≫
        (mixedTotalExtendIso f K' N').hom =
      (mixedTotalExtendIso f K N).hom ≫
        HomologicalComplex.mapBifunctorMap u ((pullbackComplex (auxHomH f)).map v)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ) :=
  transportTotalIso_hom_naturality (mixedTensorBifunctor f)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (𝟭 _) (auxHomH f).pullbackTopos
    (mixedTensorExtendIso f) (fun u e ↦ mixedTensorExtendIso_naturality_fst f u e)
    (fun a _ _ v ↦ mixedTensorExtendIso_naturality_snd f a v) u v

/-- The K-flat complexes of `f⁻¹O'`-modules with flat terms: the resolutions of the second
factor by which the derived mixed tensor product is computed. -/
abbrev mixedModelsRight :
    ObjectProperty (HomotopyCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (auxTopos f).O))
      (ComplexShape.up ℤ)) :=
  IsKFlat (Y := auxTopos f)

omit
  [∀ (A B : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (invRing f))) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing f)) (ComplexShape.up ℤ)]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing f)).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing f)).obj M).Additive]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The mixed tensor product with a K-flat complex of `f⁻¹O'`-modules with flat terms is
K-flat in the first variable.**  `Tot(G ⊗_{f⁻¹O'} N) ≅ Tot(G ⊗_O h^*N)`, and `h^*N` is K-flat
over `O` by Stacks 0G7E. -/
theorem mixedModelsRight_le :
    mixedModelsRight f ≤
      CochainComplex.KFlatBifunctor.kFlatObjects (mixedTensorBifunctor f) := by
  intro N hN G hG n
  exact (kFlat_pullbackComplex' (auxHomH f) (isMorphismOfSites_auxHomH f) N.as hN.1 hN.2 G hG
    n).of_iso (mixedTotalExtendIso f G N.as).symm

omit
  [∀ (A B : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The mixed tensor product with a fixed complex of `O`-modules carries quasi-isomorphisms
between K-flat complexes of `f⁻¹O'`-modules with flat terms to quasi-isomorphisms.**  After
`Tot(- ⊗_{f⁻¹O'} -) ≅ Tot(- ⊗_O h^*-)`, this is the invariance of the one-sided K-flat
comparison of Stacks 06YU over `O`, because `h^*` carries such a quasi-isomorphism to a
quasi-isomorphism of K-flat complexes (Stacks 06YY). -/
theorem quasiIso_mixedTensor_map
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {N N' : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (auxTopos f).O)) ℤ} (b : N ⟶ N')
    (hN : mixedModelsRight f ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N))
    (hN' : mixedModelsRight f ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N'))
    (hb : QuasiIso b) :
    QuasiIso ((((mixedTensorBifunctor f).map₂HomologicalComplex (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).map b) := by
  have := Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy
    (auxHomH f) (isMorphismOfSites_auxHomH f)
  have hQb : IsIso (DerivedCategory.Q.map b) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hb
  have hh : IsIso (DerivedCategory.Q.map ((pullbackComplex (auxHomH f)).map b)) :=
    isIso_of_square _ _ (flatPullbackIso_naturality (auxHomH f) (isMorphismOfSites_auxHomH f) b
      hN.1 hN'.1 hN.2 hN'.2)
  have hL := kFlat_pullbackComplex' (auxHomH f) (isMorphismOfSites_auxHomH f) N hN.1 hN.2
  have hL' := kFlat_pullbackComplex' (auxHomH f) (isMorphismOfSites_auxHomH f) N' hN'.1 hN'.2
  have hT : IsIso (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 K)
      ((pullbackComplex (auxHomH f)).map b)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
      (ComplexShape.up ℤ))) := by
    have h := (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
      X.O).comparisonRight_naturality (𝟙 K) ((pullbackComplex (auxHomH f)).map b) hL hL'
    rw [DerivedCategory.Q.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp] at h
    exact isIso_of_square _ _ h
  have hM : IsIso (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 K) b
      (mixedTensorBifunctor f) (ComplexShape.up ℤ))) :=
    isIso_of_square' (DerivedCategory.Q.mapIso (mixedTotalExtendIso f K N))
      (DerivedCategory.Q.mapIso (mixedTotalExtendIso f K N'))
      ((DerivedCategory.Q.map_comp _ _).symm.trans
        ((congrArg DerivedCategory.Q.map (mixedTotalExtendIso_hom_naturality f (𝟙 K) b)).trans
          (DerivedCategory.Q.map_comp _ _)))
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 hM

/-- The homotopy category of K-flat complexes of `f⁻¹O'`-modules with flat terms, localized at
the quasi-isomorphisms, is the derived category of `f⁻¹O'`-modules. -/
instance mixedModelsRight_isLocalization :
    (CochainComplex.KFlatBifunctor.modelsRightQ (mixedModelsRight f)).IsLocalization
      (CochainComplex.KFlatBifunctor.modelsRightW (mixedModelsRight f)) :=
  flatKFlatModelsQ_isLocalization (auxTopos f)

/-- **The derived tensor product over `f⁻¹O'`**, `D(O) ⥤ D(f⁻¹O') ⥤ D(O)`: the derived
bifunctor of the mixed tensor product `(H, N) ↦ (H ⊗_{f⁻¹O'} N)^#`, computed by K-flat
resolutions with flat terms of the second factor (Stacks 06YS).  Its values are `O`-modules
through the first factor. -/
def mixedDerivedTensor :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (auxTopos f).O)) ⥤
        DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  CochainComplex.KFlatBifunctor.derivedBifunctorOfRight (mixedTensorBifunctor f)
    (mixedModelsRight f) (mixedModelsRight_le f)
    (fun K _ _ b hN hN' hb ↦ quasiIso_mixedTensor_map f K b hN hN' hb)

/-- **A K-flat complex of `f⁻¹O'`-modules with flat terms computes the derived mixed tensor
product**: its value at a complex `H` of `O`-modules and such a complex `N` is the class of
`Tot(H ⊗_{f⁻¹O'} N)`. -/
def mixedDerivedTensorComparison
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (N : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (auxTopos f).O)) ℤ)
    (hN : mixedModelsRight f ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N)) :
    ((mixedDerivedTensor f).obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj N) ≅
      DerivedCategory.Q.obj
        (HomologicalComplex.mapBifunctor K N (mixedTensorBifunctor f) (ComplexShape.up ℤ)) :=
  CochainComplex.KFlatBifunctor.comparisonOfRight (mixedTensorBifunctor f)
    (mixedModelsRight f) (mixedModelsRight_le f)
    (fun K _ _ b hN hN' hb ↦ quasiIso_mixedTensor_map f K b hN hN' hb) K N hN

omit
  [∀ (A B : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The comparison is natural in both complexes. -/
lemma mixedDerivedTensorComparison_naturality
    {K K' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {N N' : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (auxTopos f).O)) ℤ}
    (u : K ⟶ K') (v : N ⟶ N')
    (hN : mixedModelsRight f ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N))
    (hN' : mixedModelsRight f ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N')) :
    ((mixedDerivedTensor f).map (DerivedCategory.Q.map u)).app (DerivedCategory.Q.obj N) ≫
        ((mixedDerivedTensor f).obj (DerivedCategory.Q.obj K')).map (DerivedCategory.Q.map v) ≫
        (mixedDerivedTensorComparison f K' N' hN').hom =
      (mixedDerivedTensorComparison f K N hN).hom ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap u v (mixedTensorBifunctor f) (ComplexShape.up ℤ)) :=
  CochainComplex.KFlatBifunctor.comparisonOfRight_naturality (mixedTensorBifunctor f)
    (mixedModelsRight f) (mixedModelsRight_le f)
    (fun K _ _ b hN hN' hb ↦ quasiIso_mixedTensor_map f K b hN hN' hb) u v hN hN'

end Derived

/-! ### Stacks 08I6 in `D(O)` -/

section Tag

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y)
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing f)).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing f)).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (invRing f))) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing f)) (ComplexShape.up ℤ)]
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (auxHomG f)).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]

/-- **The right-hand bifunctor of Stacks 08I6 in `D(O)`**: `(F, G) ↦ F ⊗^L_{f⁻¹O'} f⁻¹G`, the
derived mixed tensor product of `F` with the derived inverse image `Lf⁻¹G`, an object of `D(O)`
through `F`. -/
abbrev linearMixedDerivedTensorInverseImage :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ×
        DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (𝟭 _).prod (derivedPullback (auxHomG f)) ⋙ Functor.uncurry.obj (mixedDerivedTensor f)

/-- `Tot(F ⊗_{f⁻¹O'} f⁻¹G) ≅ Tot(F ⊗_O f^*G)` as complexes of `O`-modules: the underived
identity of Stacks 08I6 in each bidegree. -/
def mixedTotalPullbackIso
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    HomologicalComplex.mapBifunctor F ((pullbackComplex (auxHomG f)).obj G)
        (mixedTensorBifunctor f) (ComplexShape.up ℤ) ≅
      HomologicalComplex.mapBifunctor F ((pullbackComplex f).obj G)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ) :=
  transportTotalIso (mixedTensorBifunctor f)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
    (auxHomG f).pullbackTopos f.pullbackTopos (mixedTensorPullbackIso f)
    (fun u e ↦ mixedTensorPullbackIso_naturality_fst f u e)
    (fun a _ _ v ↦ mixedTensorPullbackIso_naturality_snd f a v) F G

omit
  [∀ (A B : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (invRing f))) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing f)) (ComplexShape.up ℤ)]
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (auxHomG f)).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing f)).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing f)).obj M).Additive]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The identification of total complexes is natural in both complexes. -/
lemma mixedTotalPullbackIso_hom_naturality
    {F F' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {G G' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (φ : F ⟶ F') (a : G ⟶ G') :
    HomologicalComplex.mapBifunctorMap φ ((pullbackComplex (auxHomG f)).map a)
          (mixedTensorBifunctor f) (ComplexShape.up ℤ) ≫
        (mixedTotalPullbackIso f F' G').hom =
      (mixedTotalPullbackIso f F G).hom ≫
        HomologicalComplex.mapBifunctorMap φ ((pullbackComplex f).map a)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ) :=
  transportTotalIso_hom_naturality (mixedTensorBifunctor f)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (auxHomG f).pullbackTopos
    f.pullbackTopos
    (mixedTensorPullbackIso f) (fun u e ↦ mixedTensorPullbackIso_naturality_fst f u e)
    (fun a _ _ v ↦ mixedTensorPullbackIso_naturality_snd f a v) φ a

variable (hmos : f.u.IsMorphismOfSites Y.J X.J)

omit
  [∀ (A B : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (auxHomG f)).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))] in
include hmos in
omit
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive] in
/-- The inverse image of a K-flat complex of `O'`-modules with flat terms is a K-flat complex of
`f⁻¹O'`-modules with flat terms. -/
theorem mixedModelsRight_pullbackComplex
    (G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hG : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) G)
    (hflatG : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (G.X i)) :
    mixedModelsRight f ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      ((pullbackComplex (auxHomG f)).obj G)) :=
  ⟨kFlat_pullbackComplex' (auxHomG f) hmos G hG hflatG,
    fun i ↦ RingedToposSiteHom.pullbackPreservesIsFlat (auxHomG f) hmos _ (hflatG i)⟩

section Models

variable (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
  (G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
  (hG : CochainComplex.KFlatBifunctor.KFlat
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) G)
  (hflatG : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (G.X i))

/-- The left-hand side of Stacks 08I6 at a K-flat complex of `O'`-modules with flat terms is the
class of `Tot(F ⊗_O f^*G)`. -/
def linearModelLeft :
    (linearDerivedTensorPullback f).obj (DerivedCategory.Q.obj F, DerivedCategory.Q.obj G) ≅
      DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor F ((pullbackComplex f).obj G)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)) :=
  (Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor).mapIso
      ((Iso.refl (DerivedCategory.Q.obj F)).prod (flatPullbackIso f hmos G hG hflatG)) ≪≫
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparisonRight
      F ((pullbackComplex f).obj G) (kFlat_pullbackComplex' f hmos G hG hflatG)

/-- The right-hand side of Stacks 08I6 at a K-flat complex of `O'`-modules with flat terms is
the class of `Tot(F ⊗_{f⁻¹O'} f⁻¹G)`, which the underived identity identifies with
`Tot(F ⊗_O f^*G)`. -/
def linearModelRight :
    (linearMixedDerivedTensorInverseImage f).obj
        (DerivedCategory.Q.obj F, DerivedCategory.Q.obj G) ≅
      DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor F ((pullbackComplex f).obj G)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)) :=
  (Functor.uncurry.obj (mixedDerivedTensor f)).mapIso
      ((Iso.refl (DerivedCategory.Q.obj F)).prod
        (flatPullbackIso (auxHomG f) hmos G hG hflatG)) ≪≫
    mixedDerivedTensorComparison f F ((pullbackComplex (auxHomG f)).obj G)
      (mixedModelsRight_pullbackComplex f hmos G hG hflatG) ≪≫
    DerivedCategory.Q.mapIso (mixedTotalPullbackIso f F G)

/-- **Stacks 08I6 in `D(O)` at a K-flat complex of `O'`-modules with flat terms.** -/
def linearModelIso :
    (linearDerivedTensorPullback f).obj (DerivedCategory.Q.obj F, DerivedCategory.Q.obj G) ≅
      (linearMixedDerivedTensorInverseImage f).obj
        (DerivedCategory.Q.obj F, DerivedCategory.Q.obj G) :=
  linearModelLeft f hmos F G hG hflatG ≪≫ (linearModelRight f hmos F G hG hflatG).symm

end Models

section Naturality

variable {F F' : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ} (φ : F ⟶ F')
  {G G' : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ} (a : G ⟶ G')
  (hG : CochainComplex.KFlatBifunctor.KFlat
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) G)
  (hG' : CochainComplex.KFlatBifunctor.KFlat
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) G')
  (hflatG : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (G.X i))
  (hflatG' : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (G'.X i))

omit [(pullbackOnHomotopy (auxHomG f)).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (ComplexShape.up ℤ))]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (invRing f))) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing f)) (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing f)).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing f)).obj M).Additive] in
/-- The left-hand side of Stacks 08I6 at the models is natural in the pair of complexes. -/
lemma linearModelLeft_naturality :
    (linearDerivedTensorPullback f).map
          ((DerivedCategory.Q.map φ, DerivedCategory.Q.map a) :
            ((DerivedCategory.Q.obj F, DerivedCategory.Q.obj G) : _ × _) ⟶
              (DerivedCategory.Q.obj F', DerivedCategory.Q.obj G')) ≫
        (linearModelLeft f hmos F' G' hG' hflatG').hom =
      (linearModelLeft f hmos F G hG hflatG).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap φ ((pullbackComplex f).map a)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)) := by
  have h1 := map_prod_refl_iso_naturality
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor)
    (DerivedCategory.Q.map φ) _ _ _ _ (flatPullbackIso_naturality f hmos a hG hG' hflatG hflatG')
  have h2 : (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor).map
          ((DerivedCategory.Q.map φ,
              DerivedCategory.Q.map ((pullbackComplex f).map a)) :
            ((DerivedCategory.Q.obj F,
                DerivedCategory.Q.obj ((pullbackComplex f).obj G)) : _ × _) ⟶
              (DerivedCategory.Q.obj F',
                DerivedCategory.Q.obj ((pullbackComplex f).obj G'))) ≫
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparisonRight
          F' ((pullbackComplex f).obj G') (kFlat_pullbackComplex' f hmos G' hG' hflatG')).hom =
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparisonRight
          F ((pullbackComplex f).obj G) (kFlat_pullbackComplex' f hmos G hG hflatG)).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap φ
          ((pullbackComplex f).map a) (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
          (ComplexShape.up ℤ)) := by
    simpa only [Functor.uncurry_obj_map, Category.assoc] using
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparisonRight_naturality
        φ ((pullbackComplex f).map a) (kFlat_pullbackComplex' f hmos G hG hflatG)
        (kFlat_pullbackComplex' f hmos G' hG' hflatG')
  rw [Functor.comp_map]
  exact trans_naturality h1 h2

omit
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))] in
/-- The right-hand side of Stacks 08I6 at the models is natural in the pair of complexes. -/
lemma linearModelRight_naturality :
    (linearMixedDerivedTensorInverseImage f).map
          ((DerivedCategory.Q.map φ, DerivedCategory.Q.map a) :
            ((DerivedCategory.Q.obj F, DerivedCategory.Q.obj G) : _ × _) ⟶
              (DerivedCategory.Q.obj F', DerivedCategory.Q.obj G')) ≫
        (linearModelRight f hmos F' G' hG' hflatG').hom =
      (linearModelRight f hmos F G hG hflatG).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap φ ((pullbackComplex f).map a)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)) := by
  have h1 := map_prod_refl_iso_naturality (Functor.uncurry.obj (mixedDerivedTensor f))
    (DerivedCategory.Q.map φ) _ _ _ _
    (flatPullbackIso_naturality (auxHomG f) hmos a hG hG' hflatG hflatG')
  have h2 : (Functor.uncurry.obj (mixedDerivedTensor f)).map
          ((DerivedCategory.Q.map φ,
              DerivedCategory.Q.map ((pullbackComplex (auxHomG f)).map a)) :
            ((DerivedCategory.Q.obj F,
                DerivedCategory.Q.obj ((pullbackComplex (auxHomG f)).obj G)) : _ × _) ⟶
              (DerivedCategory.Q.obj F',
                DerivedCategory.Q.obj ((pullbackComplex (auxHomG f)).obj G'))) ≫
        (mixedDerivedTensorComparison f F' ((pullbackComplex (auxHomG f)).obj G')
          (mixedModelsRight_pullbackComplex f hmos G' hG' hflatG')).hom =
      (mixedDerivedTensorComparison f F ((pullbackComplex (auxHomG f)).obj G)
          (mixedModelsRight_pullbackComplex f hmos G hG hflatG)).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap φ
          ((pullbackComplex (auxHomG f)).map a) (mixedTensorBifunctor f) (ComplexShape.up ℤ)) := by
    simpa only [Functor.uncurry_obj_map, Category.assoc] using
      mixedDerivedTensorComparison_naturality f φ ((pullbackComplex (auxHomG f)).map a)
        (mixedModelsRight_pullbackComplex f hmos G hG hflatG)
        (mixedModelsRight_pullbackComplex f hmos G' hG' hflatG')
  have h3 : DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap φ
          ((pullbackComplex (auxHomG f)).map a) (mixedTensorBifunctor f) (ComplexShape.up ℤ)) ≫
        (DerivedCategory.Q.mapIso (mixedTotalPullbackIso f F' G')).hom =
      (DerivedCategory.Q.mapIso (mixedTotalPullbackIso f F G)).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap φ ((pullbackComplex f).map a)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)) := by
    rw [CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.mapIso_hom,
      ← Functor.map_comp, ← Functor.map_comp, mixedTotalPullbackIso_hom_naturality f φ a]
  rw [Functor.comp_map]
  exact trans_naturality h1 (trans_naturality h2 h3)

/-- **Stacks 08I6 in `D(O)` at the models is natural in the pair of complexes.** -/
lemma linearModelIso_naturality :
    (linearDerivedTensorPullback f).map
          ((DerivedCategory.Q.map φ, DerivedCategory.Q.map a) :
            ((DerivedCategory.Q.obj F, DerivedCategory.Q.obj G) : _ × _) ⟶
              (DerivedCategory.Q.obj F', DerivedCategory.Q.obj G')) ≫
        (linearModelIso f hmos F' G' hG' hflatG').hom =
      (linearModelIso f hmos F G hG hflatG).hom ≫
        (linearMixedDerivedTensorInverseImage f).map
          ((DerivedCategory.Q.map φ, DerivedCategory.Q.map a) :
            ((DerivedCategory.Q.obj F, DerivedCategory.Q.obj G) : _ × _) ⟶
              (DerivedCategory.Q.obj F', DerivedCategory.Q.obj G')) :=
  isoOverCommonTarget_naturality
    (linearModelLeft_naturality f hmos φ a hG hG' hflatG hflatG')
    (linearModelRight_naturality f hmos φ a hG hG' hflatG hflatG')

end Naturality

/-- The isomorphism of Stacks 08I6 in `D(O)` at the models, as an isomorphism of the two
functors on the category of pairs of models. -/
def linearModelsTensorIso :
    mixedModelsQ (X := X) (Y := Y) ⋙ linearDerivedTensorPullback f ≅
      mixedModelsQ (X := X) (Y := Y) ⋙ linearMixedDerivedTensorInverseImage f :=
  NatIso.ofComponents
    (fun P =>
      (linearDerivedTensorPullback f).mapIso (mixedModelsIso P) ≪≫
        linearModelIso f hmos P.1 P.2.obj.as P.2.property.1 P.2.property.2 ≪≫
          ((linearMixedDerivedTensorInverseImage f).mapIso (mixedModelsIso P)).symm)
    (fun {P R} g => transportedIso_naturality
      (linearDerivedTensorPullback f) (linearMixedDerivedTensorInverseImage f)
      (mixedModelsIso P) (mixedModelsIso R)
      (linearModelIso f hmos P.1 P.2.obj.as P.2.property.1 P.2.property.2)
      (linearModelIso f hmos R.1 R.2.obj.as R.2.property.1 R.2.property.2)
      ((mixedModelsQ (X := X) (Y := Y)).map g)
      ((DerivedCategory.Q.map g.1, DerivedCategory.Q.map g.2.hom.out) :
        ((DerivedCategory.Q.obj P.1, DerivedCategory.Q.obj P.2.obj.as) : _ × _) ⟶
          (DerivedCategory.Q.obj R.1, DerivedCategory.Q.obj R.2.obj.as))
      (mixedModelsIso_naturality g)
      (linearModelIso_naturality f hmos g.1 g.2.hom.out
        P.2.property.1 R.2.property.1 P.2.property.2 R.2.property.2))

/-- **Stacks 08I6 in `D(O)`.**  The canonical bifunctorial isomorphism

`F ⊗^L_O Lf^*G ≅ F ⊗^L_{f⁻¹O'} f⁻¹G`

of objects of `D(O)`, for a morphism of ringed topoi `f : (Sh(C), O) ⟶ (Sh(C'), O')`, `F` in
`D(O)` and `G` in `D(O')`.  The right-hand side is the derived tensor product over `f⁻¹O'` of
`F` and `Lf⁻¹G` (`mixedDerivedTensor`), an object of `D(O)` through `F`.  It is stated between
the two uncurried bifunctors on `D(O) × D(O')`, so that bifunctoriality is part of its type.

At a complex `F` of `O`-modules and a K-flat complex `G` of `O'`-modules with flat terms both
sides are total complexes and the isomorphism is the underived identity
`F ⊗_O f^*G ≅ F ⊗_{f⁻¹O'} f⁻¹G` in each bidegree (`linearModelIso`); the passage to arbitrary
objects is the descent along the localization of pairs of models. -/
def linearDerivedMixedTensorIso :
    linearDerivedTensorPullback f ≅ linearMixedDerivedTensorInverseImage f := by
  letI : (mixedModelsQ (X := X) (Y := Y)).IsLocalization (mixedModelsW (X := X) (Y := Y)) :=
    mixedModelsQ_isLocalization
  letI : Localization.Lifting (mixedModelsQ (X := X) (Y := Y))
      (mixedModelsW (X := X) (Y := Y))
      (mixedModelsQ (X := X) (Y := Y) ⋙ linearDerivedTensorPullback f)
      (linearDerivedTensorPullback f) := ⟨Iso.refl _⟩
  letI : Localization.Lifting (mixedModelsQ (X := X) (Y := Y))
      (mixedModelsW (X := X) (Y := Y))
      (mixedModelsQ (X := X) (Y := Y) ⋙ linearMixedDerivedTensorInverseImage f)
      (linearMixedDerivedTensorInverseImage f) := ⟨Iso.refl _⟩
  exact Localization.liftNatIso (mixedModelsQ (X := X) (Y := Y))
    (mixedModelsW (X := X) (Y := Y)) _ _ _ _ (linearModelsTensorIso f hmos)

end Tag

end Stacks.Cohomology.MixedDerivedTensor

end
