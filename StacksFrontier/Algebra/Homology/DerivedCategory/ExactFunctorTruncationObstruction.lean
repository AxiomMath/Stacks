module

public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.ExactFunctorSingleHomology

/-!
# The top cohomology of a truncation, transported along an exact functor

Let `C` be an abelian category and `K` an object of `D(C)`. The truncation `τ^{<q+1}K` maps to
its top piece `τ^{≥q}τ^{<q+1}K ≅ H^q(K)[-q]`; call this the *obstruction map*
`τ^{<q+1}K ⟶ H^q(K)[-q]`: a morphism `Z ⟶ τ^{<q+1}K` factors through `τ^{<q}τ^{<q+1}K` exactly
when its composite with the obstruction map vanishes (the truncation triangle).

Now let `G : C₁ ⥤ C₂` be exact, `K` in `D(C₁)`, `K₂` in `D(C₂)` and `b : G(K) ⟶ K₂`. Since `G` is
t-exact, `G(τ^{<q+1}K)` lies in `D^{≤ q}`, so `G(τ^{<q+1}K ⟶ K) ≫ b` lifts uniquely to
`τ^{<q+1}K₂`. This file proves that this lift carries the obstruction map of `K` to the
obstruction map of `K₂`, read through `G(H^q(K)[-q]) ≅ G(H^q K)[-q]` and the map
`G(H^q K) ≅ H^q(G K) ⟶ H^q(K₂)` induced by `b` on cohomology.

## Main definitions

* `Stacks.TruncationObstruction.obstructionMap`: `τ^{<q+1}K ⟶ H^q(K)[-q]`.
* `Stacks.TruncationObstruction.liftMap`: the lift `G(τ^{<q+1}K) ⟶ τ^{<q+1}K₂` of a morphism
  `b : G K ⟶ K₂`.

## Main results

* `Stacks.TruncationObstruction.homologyFunctor_map_obstructionMap`: on `H^q`, the obstruction map
  is the map induced by `τ^{<q+1}K ⟶ K`.
* `Stacks.TruncationObstruction.hom_ext_of_isLE`: morphisms from an object of `D^{≤ q}` to an
  object `B[-q]` are determined by their effect on `H^q`.
* `Stacks.TruncationObstruction.liftMap_comp_obstructionMap`: the transport of obstruction maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w w₁ w₂ v v₁ v₂ u u₁ u₂

namespace Stacks.TruncationObstruction

open DerivedCategory

section One

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- **The obstruction map** `τ^{<q+1}K ⟶ τ^{≥q}τ^{<q+1}K ≅ H^q(K)[-q]`. -/
def obstructionMap (q : ℤ) (K : DerivedCategory C) :
    (TStructure.t.truncLT (q + 1)).obj K ⟶
      (singleFunctor C q).obj ((homologyFunctor C q).obj K) :=
  (TStructure.t.truncGEπ q).app ((TStructure.t.truncLT (q + 1)).obj K) ≫
    (truncGELTIsoHomologyFunctorCompSingleFunctor q).hom.app K

/-- The obstruction map is natural in `K`. -/
lemma obstructionMap_naturality (q : ℤ) {K L : DerivedCategory C} (f : K ⟶ L) :
    (TStructure.t.truncLT (q + 1)).map f ≫ obstructionMap q L =
      obstructionMap q K ≫ (singleFunctor C q).map ((homologyFunctor C q).map f) := by
  have h := (truncGELTIsoHomologyFunctorCompSingleFunctor (C := C) q).hom.naturality f
  have h2 := (TStructure.t.truncGEπ q).naturality ((TStructure.t.truncLT (q + 1)).map f)
  dsimp at h h2
  simp only [obstructionMap, Category.assoc]
  rw [reassoc_of% h2, h]

/-- The shape of `DerivedCategory.truncGELTIsoHomologyFunctorCompSingleFunctor`: an isomorphism
`T ≅ H^q ⋙ single q` obtained from a factorisation `e₁ : L ⋙ single q ≅ T` and an
identification `φ : T ⋙ H^q ≅ H^q` induces `φ` on `H^q`. -/
private lemma homologyFunctor_map_essImageLift_hom_app (q : ℤ)
    (L : DerivedCategory C ⥤ C) (T : DerivedCategory C ⥤ DerivedCategory C)
    (e₁ : L ⋙ singleFunctor C q ≅ T) (φ : T ⋙ homologyFunctor C q ≅ homologyFunctor C q)
    (K : DerivedCategory C) :
    (homologyFunctor C q).map ((e₁.symm ≪≫ Functor.isoWhiskerRight
        (L.rightUnitor.symm ≪≫
          Functor.isoWhiskerLeft L (singleFunctorCompHomologyFunctorIso C q).symm ≪≫
            (Functor.associator _ _ _).symm ≪≫
              Functor.isoWhiskerRight e₁ (homologyFunctor C q) ≪≫ φ)
        (singleFunctor C q)).hom.app K) ≫
      (singleFunctorCompHomologyFunctorIso C q).hom.app ((homologyFunctor C q).obj K) =
    φ.hom.app K := by
  set e₂ : L ≅ homologyFunctor C q := L.rightUnitor.symm ≪≫
    Functor.isoWhiskerLeft L (singleFunctorCompHomologyFunctorIso C q).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight e₁ (homologyFunctor C q) ≪≫ φ with he₂
  have key : e₂.hom.app K = (singleFunctorCompHomologyFunctorIso C q).inv.app (L.obj K) ≫
      (homologyFunctor C q).map (e₁.hom.app K) ≫ φ.hom.app K := by
    simp [e₂]
  have hs := (singleFunctorCompHomologyFunctorIso C q).hom.naturality (e₂.hom.app K)
  dsimp at hs
  calc (homologyFunctor C q).map ((e₁.symm ≪≫ Functor.isoWhiskerRight e₂
          (singleFunctor C q)).hom.app K) ≫
        (singleFunctorCompHomologyFunctorIso C q).hom.app ((homologyFunctor C q).obj K)
      = (homologyFunctor C q).map (e₁.inv.app K) ≫
          (homologyFunctor C q).map ((singleFunctor C q).map (e₂.hom.app K)) ≫
          (singleFunctorCompHomologyFunctorIso C q).hom.app ((homologyFunctor C q).obj K) := by
        rw [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]
        rfl
    _ = (homologyFunctor C q).map (e₁.inv.app K) ≫
          (singleFunctorCompHomologyFunctorIso C q).hom.app (L.obj K) ≫ e₂.hom.app K := by
        rw [hs]
    _ = φ.hom.app K := by
        rw [key, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
          CategoryTheory.Functor.map_id, Category.id_comp]

/-- **On `H^q`, the obstruction map is the map induced by `τ^{<q+1}K ⟶ K`**, once `H^q(B[-q])` is
identified with `B`. -/
lemma homologyFunctor_map_obstructionMap (q : ℤ) (K : DerivedCategory C) :
    (homologyFunctor C q).map (obstructionMap q K) ≫
        (singleFunctorCompHomologyFunctorIso C q).hom.app ((homologyFunctor C q).obj K) =
      (homologyFunctor C q).map ((TStructure.t.truncLTι (q + 1)).app K) := by
  rw [obstructionMap, Functor.map_comp, Category.assoc]
  dsimp only [truncGELTIsoHomologyFunctorCompSingleFunctor]
  rw [homologyFunctor_map_essImageLift_hom_app]
  simp [truncGELTCompHomologyFunctorIso, truncGECompHomologyFunctorIso,
    truncLTCompHomologyFunctorIso]

/-- **Morphisms from `D^{≤ q}` to an object placed in degree `q` are determined on `H^q`.** -/
lemma hom_ext_of_isLE {q : ℤ} {X : DerivedCategory C} [X.IsLE q] {B : C}
    {f g : X ⟶ (singleFunctor C q).obj B}
    (h : (homologyFunctor C q).map f = (homologyFunctor C q).map g) : f = g := by
  rw [← sub_eq_zero]
  set d := f - g
  have hd : (homologyFunctor C q).map d = 0 := by
    simp [d, Functor.map_sub, h]
  let t := TStructure.t (C := C)
  let T := (t.truncGE q).obj X
  have hT₁ : T.IsGE q := by dsimp [T]; infer_instance
  have hT₂ : T.IsLE q := by dsimp [T]; infer_instance
  let d' : T ⟶ (singleFunctor C q).obj B := t.descTruncGE d q
  have hdd' : (t.truncGEπ q).app X ≫ d' = d := t.π_descTruncGE d q
  obtain ⟨M, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE T q
  obtain ⟨k, hk⟩ := (singleFunctor C q).map_surjective (e.inv ≫ d')
  have hπ : IsIso ((homologyFunctor C q).map ((t.truncGEπ q).app X)) :=
    isIso_homologyMap_truncGEπ_app q q le_rfl X
  have hd' : (homologyFunctor C q).map d' = 0 := by
    rw [← cancel_epi ((homologyFunctor C q).map ((t.truncGEπ q).app X)), ← Functor.map_comp,
      hdd', hd, comp_zero]
  have hk0 : k = 0 := by
    have hs := (singleFunctorCompHomologyFunctorIso C q).hom.naturality k
    dsimp at hs
    rw [hk, Functor.map_comp, hd', comp_zero, zero_comp] at hs
    simpa using hs.symm
  have : d' = 0 := by
    rw [← cancel_epi e.inv, ← hk, hk0, Functor.map_zero, comp_zero]
  rw [← hdd', this, comp_zero]

end One

section Two

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  (G : C₁ ⥤ C₂) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The functor induced on derived categories by an exact functor carries `D^{≤ n}` to
`D^{≤ n}`: its cohomology objects are the images of those of the source. -/
lemma isLE_mapDerivedCategory_obj (X : DerivedCategory C₁) (n : ℤ) [X.IsLE n] :
    (G.mapDerivedCategory.obj X).IsLE n := by
  rw [isLE_iff]
  intro i hi
  exact (G.map_isZero (isZero_of_isLE X n i hi)).of_iso
    ((G.mapDerivedCategoryHomologyIso i).app X)

/-- The image under an exact functor of the truncation `τ^{<q+1}K` lies in `D^{≤ q}`. -/
instance (q : ℤ) (K : DerivedCategory C₁) :
    (G.mapDerivedCategory.obj ((TStructure.t.truncLT (q + 1)).obj K)).IsLE q :=
  isLE_mapDerivedCategory_obj G _ q

/-- **The lift of `b : G K ⟶ K₂` to the truncations**: the unique morphism
`G(τ^{<q+1}K) ⟶ τ^{<q+1}K₂` over `G(τ^{<q+1}K ⟶ K) ≫ b`. -/
def liftMap (q : ℤ) {K : DerivedCategory C₁} {K₂ : DerivedCategory C₂}
    (b : G.mapDerivedCategory.obj K ⟶ K₂) :
    G.mapDerivedCategory.obj ((TStructure.t.truncLT (q + 1)).obj K) ⟶
      (TStructure.t.truncLT (q + 1)).obj K₂ :=
  TStructure.t.liftTruncLT
    (G.mapDerivedCategory.map ((TStructure.t.truncLTι (q + 1)).app K) ≫ b) q (q + 1) rfl

/-- The lift of `b` followed by `τ^{<q+1}K₂ ⟶ K₂` is `G(τ^{<q+1}K ⟶ K) ≫ b`. -/
@[reassoc (attr := simp)]
lemma liftMap_ι (q : ℤ) {K : DerivedCategory C₁} {K₂ : DerivedCategory C₂}
    (b : G.mapDerivedCategory.obj K ⟶ K₂) :
    liftMap G q b ≫ (TStructure.t.truncLTι (q + 1)).app K₂ =
      G.mapDerivedCategory.map ((TStructure.t.truncLTι (q + 1)).app K) ≫ b :=
  TStructure.t.liftTruncLT_ι _ _ _ _

/-- **The obstruction maps are carried to one another.** For `G` exact and `b : G K ⟶ K₂`, the
lift `G(τ^{<q+1}K) ⟶ τ^{<q+1}K₂` of `b` followed by the obstruction map of `K₂` is `G` of the
obstruction map of `K`, followed by `G(H^q(K)[-q]) ≅ (G H^q K)[-q]` and by the map
`G(H^q K) ≅ H^q(G K) ⟶ H^q(K₂)` induced by `b`. -/
theorem liftMap_comp_obstructionMap (q : ℤ) {K : DerivedCategory C₁} {K₂ : DerivedCategory C₂}
    (b : G.mapDerivedCategory.obj K ⟶ K₂) :
    liftMap G q b ≫ obstructionMap q K₂ =
      G.mapDerivedCategory.map (obstructionMap q K) ≫
        (G.mapDerivedCategorySingleFunctor q).hom.app ((homologyFunctor C₁ q).obj K) ≫
        (singleFunctor C₂ q).map ((G.mapDerivedCategoryHomologyIso q).inv.app K ≫
          (homologyFunctor C₂ q).map b) := by
  apply hom_ext_of_isLE
  rw [← cancel_mono ((singleFunctorCompHomologyFunctorIso C₂ q).hom.app
    ((homologyFunctor C₂ q).obj K₂))]
  have hs := (singleFunctorCompHomologyFunctorIso C₂ q).hom.naturality
    ((G.mapDerivedCategoryHomologyIso q).inv.app K ≫ (homologyFunctor C₂ q).map b)
  dsimp at hs
  have hS := Stacks.ExactFunctorSingleHomology.homologyMap_mapDerivedCategorySingleFunctor G q
    ((homologyFunctor C₁ q).obj K)
  have hn₁ := (G.mapDerivedCategoryHomologyIso q).hom.naturality (obstructionMap q K)
  have hn₂ := (G.mapDerivedCategoryHomologyIso q).hom.naturality
    ((TStructure.t.truncLTι (q + 1)).app K)
  dsimp at hn₁ hn₂
  have hE₁ := homologyFunctor_map_obstructionMap q K
  have hE₂ := homologyFunctor_map_obstructionMap q K₂
  calc (homologyFunctor C₂ q).map (liftMap G q b ≫ obstructionMap q K₂) ≫
        (singleFunctorCompHomologyFunctorIso C₂ q).hom.app ((homologyFunctor C₂ q).obj K₂)
      = (homologyFunctor C₂ q).map (G.mapDerivedCategory.map
          ((TStructure.t.truncLTι (q + 1)).app K)) ≫ (homologyFunctor C₂ q).map b := by
        rw [Functor.map_comp, Category.assoc, hE₂, ← Functor.map_comp, liftMap_ι,
          Functor.map_comp]
    _ = (homologyFunctor C₂ q).map (G.mapDerivedCategory.map (obstructionMap q K)) ≫
          (G.mapDerivedCategoryHomologyIso q).hom.app _ ≫
          G.map ((singleFunctorCompHomologyFunctorIso C₁ q).hom.app _) ≫
          (G.mapDerivedCategoryHomologyIso q).inv.app K ≫ (homologyFunctor C₂ q).map b := by
        rw [reassoc_of% hn₁, ← G.map_comp_assoc, hE₁, ← reassoc_of% hn₂,
          Iso.hom_inv_id_app_assoc]
    _ = _ := by
        rw [← reassoc_of% hS]
        simp only [Functor.map_comp, Category.assoc] at hs ⊢
        rw [hs]

end Two

end Stacks.TruncationObstruction

end
