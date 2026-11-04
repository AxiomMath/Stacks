module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleDescentBridge

/-!
# The transitions of a sheaf on `U_étale`, read on spaces-étale sheaves

Let `a : U → X` be an augmented simplicial algebraic space and `G` a sheaf on its small étale
site `U_étale` (Section 0DE7 of the Stacks project). Under the identifications `E_n` of the
component sheaves with sheaves on `U_{n, spaces, étale}`, the canonical transitions of Stacks 09WF
become morphisms `U(φ)^* G_m ⟶ G_n` of spaces-étale sheaves, which compose through the
compositors of the spaces-étale inverse images. For `G = a⁻¹F` they are, through the
identifications `G_n ≅ a_n^* F`, the compositors `U(φ)^* a_m^* F ≅ a_n^* F` themselves.

## Main definitions

* `AlgebraicGeometry.Space.EtaleComponent.spacesComponent`: the component `G_n` of `G`, as a
  sheaf on `U_{n, spaces, étale}`.
* `AlgebraicGeometry.Space.EtaleComponent.spacesTransition`: the transition `U(φ)^* G_m ⟶ G_n`.

## Main results

* `AlgebraicGeometry.Space.EtaleComponent.spacesTransition_comp`: the transitions compose.

## References

* [Stacks Project, Tag 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.EtaleComponent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : SimplicialObject.Augmented (AlgebraicSpaces B S hS)}

section Transitions

variable (G : Sheaf (situation A).totalTopology (Type (u + 1)))

/-- The component of degree `n` of a sheaf on `U_étale`, as a sheaf on `U_{n, spaces, étale}`. -/
abbrev spacesComponent (n : SimplexCategory) : spacesEtaleSheafCat B S hS (A.left.obj (op n)) :=
  (compEquiv n).functor.obj (((situation A).restrict n).obj G)

/-- The transition of a sheaf on `U_étale` along `φ : [m] → [n]`, read on spaces-étale sheaves:
`U(φ)^* G_m ⟶ G_n`. -/
def spacesTransition {m n : SimplexCategory} (φ : m ⟶ n) :
    (spacesEtaleInverseImage B S hS (A.left.map φ.op)).obj (spacesComponent G m) ⟶
      spacesComponent G n :=
  (transInvIso φ).inv.app (((situation A).restrict m).obj G) ≫
    (compEquiv n).functor.map (((situation A).fiberTransition φ).app G)

/-- The transitions of a cartesian sheaf are invertible. -/
theorem isIso_spacesTransition (hG : SimplicialSiteSituation.IsCartesianSheaf (situation A) G)
    {m n : SimplexCategory} (φ : m ⟶ n) : IsIso (spacesTransition G φ) := by
  have := hG φ
  exact (((transInvIso φ).app (((situation A).restrict m).obj G)).symm ≪≫
    (compEquiv n).functor.mapIso (asIso (((situation A).fiberTransition φ).app G))).isIso_hom

/-- **The transitions compose**, through the compositors of the spaces-étale inverse images. -/
theorem spacesTransition_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (e : A.left.map φ.op ≫ A.left.map ψ.op = A.left.map (ψ ≫ φ).op) :
    spacesTransition G (ψ ≫ φ) =
      (eqToHom (congrArg (fun k => spacesEtaleInverseImage B S hS k) e.symm)).app
          (spacesComponent G l) ≫
        (spacesEtaleInverseImage_comp B S hS (A.left.map φ.op) (A.left.map ψ.op)).hom.app
          (spacesComponent G l) ≫
        (spacesEtaleInverseImage B S hS (A.left.map φ.op)).map (spacesTransition G ψ) ≫
        spacesTransition G φ := by
  have k1 := NatTrans.congr_app (pasteIso_bridge_natTrans (A := A) ψ φ)
    (((situation A).restrict l).obj G)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp] at k1
  have hp := (situation A).pasteIso_comp_fiberTransition G ψ φ
  set w := (compEquiv n).functor.map
        (((situation A).canonicalCompositionComparison ψ φ).inv.app
          (((situation A).restrict l).obj G)) ≫
        (transInvIso (ψ ≫ φ)).hom.app (((situation A).restrict l).obj G) with hw
  have hk : w ≫ spacesTransition G (ψ ≫ φ) =
      (compEquiv n).functor.map (((situation A).transitionMorphism φ).inverseImage.map
        (((situation A).fiberTransition ψ).app G) ≫ ((situation A).fiberTransition φ).app G) := by
    rw [← hp, hw]
    dsimp only [spacesTransition, Functor.comp_obj]
    rw [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp]
    rfl
  have : IsIso w := by
    rw [k1]; infer_instance
  rw [← cancel_epi w, hk, k1]
  dsimp only [spacesTransition, Functor.comp_obj]
  simp only [Functor.map_comp, Category.assoc, eqToHom_app, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Iso.inv_hom_id_app_assoc]
  rw [← Iso.app_hom (transInvIso ψ), ← Iso.app_inv (transInvIso ψ), Iso.map_hom_inv_id_assoc]
  have hn := (transInvIso φ).hom.naturality (((situation A).fiberTransition ψ).app G)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  rw [← reassoc_of% hn, Iso.hom_inv_id_app_assoc]

end Transitions

section Generic

variable {C D : Type*} [Category C] [Category D] (E : C ⥤ D)

/-- A naturality square for a morphism that is conjugate, through two isomorphisms, to a
morphism with a known naturality square. Used where the conjugating isomorphisms live in
categories that are equal only up to unfolding, so that rewriting in place is not possible. -/
theorem map_comp_mapIso_hom_comp_eq {x x' y y' : C} {z z' : D} (a : x ≅ x') (b : y ≅ y')
    (r : x ⟶ y) (X : x' ⟶ y') (c : E.obj x' ⟶ z) (c' : E.obj y' ⟶ z') (m : z ⟶ z')
    (h₁ : r = a.hom ≫ X ≫ b.inv) (h₂ : E.map X ≫ c' = c ≫ m) :
    E.map r ≫ (E.mapIso b).hom ≫ c' = ((E.mapIso a).hom ≫ c) ≫ m := by
  subst h₁
  rw [Functor.mapIso_hom, Functor.mapIso_hom, Functor.map_comp, Functor.map_comp, Category.assoc,
    Category.assoc, ← Functor.map_comp_assoc E b.inv b.hom, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, h₂, Category.assoc]

/-- Pasting a naturality square for `E.map X` with one for `X`. -/
theorem comp_map_comp_map_eq {a b : D} {x x'' y y' : C} (t : a ⟶ E.obj x) (f : x ⟶ y)
    (r : y ⟶ y') (s : a ⟶ b) (t' : b ⟶ E.obj x'') (X : x ⟶ x'') (f' : x'' ⟶ y')
    (h₁ : X ≫ f' = f ≫ r) (h₂ : s ≫ t' = t ≫ E.map X) :
    (t ≫ E.map f) ≫ E.map r = s ≫ t' ≫ E.map f' := by
  rw [Category.assoc, ← E.map_comp, ← h₁, E.map_comp, ← Category.assoc, ← h₂, Category.assoc]

end Generic

section InverseImage

variable (F : spacesEtaleSheafCat B S hS A.right)

/-- The components of the inverse image `a⁻¹F` of a spaces-étale sheaf on `X` are the
spaces-étale inverse images `a_n^* F`. -/
def inverseImageComponentIso (n : SimplexCategory) :
    spacesComponent ((etaleAugmentationMorphism A).inverseImage.obj F) n ≅
      (spacesEtaleInverseImage B S hS (A.hom.app (op n))).obj F :=
  (compEquiv n).functor.mapIso
      (SimplicialSiteSituation.Augmentation.componentRestrictionIso (situation A) _ _
        (etaleAugmentation A) F n) ≪≫
    (augInvIso n).app F

/-- The identification `(a⁻¹F)_n ≅ a_n^* F` is natural in `F`. -/
theorem inverseImageComponentIso_naturality {F F' : spacesEtaleSheafCat B S hS A.right}
    (u : F ⟶ F') (n : SimplexCategory) :
    (compEquiv n).functor.map (((situation A).restrict n).map
        ((etaleAugmentationMorphism A).inverseImage.map u)) ≫
        (inverseImageComponentIso F' n).hom =
      (inverseImageComponentIso F n).hom ≫
        (spacesEtaleInverseImage B S hS (A.hom.app (op n))).map u := by
  have h₁ : ((situation A).restrict n).map ((etaleAugmentationMorphism A).inverseImage.map u) =
      (SimplicialSiteSituation.Augmentation.componentRestrictionIso (situation A) _ _
          (etaleAugmentation A) F n).hom ≫ (compAug A n).inverseImage.map u ≫
        (SimplicialSiteSituation.Augmentation.componentRestrictionIso (situation A) _ _
          (etaleAugmentation A) F' n).inv :=
    SimplicialSiteSituation.Augmentation.restrict_map_inverseImage_map (situation A) _ _
      (etaleAugmentation A) F F' u n
  have h₂ := (augInvIso (A := A) n).hom.naturality u
  dsimp only [Functor.comp_obj, Functor.comp_map] at h₂
  simp only [inverseImageComponentIso, Iso.trans_hom, Iso.app_hom]
  exact map_comp_mapIso_hom_comp_eq (compEquiv n).functor _ _ _ _ _ _ _ h₁ h₂

/-- **The transitions of `a⁻¹F` are the compositors**: under the identifications
`(a⁻¹F)_n ≅ a_n^* F`, the transition along `φ` is the spaces-étale compositor
`U(φ)^* a_m^* F ≅ a_n^* F` for `a_n = a_m ∘ U(φ)`. -/
theorem spacesTransition_inverseImage {m n : SimplexCategory} (φ : m ⟶ n)
    (e : A.left.map φ.op ≫ A.hom.app (op m) = A.hom.app (op n)) :
    spacesTransition ((etaleAugmentationMorphism A).inverseImage.obj F) φ =
      (spacesEtaleInverseImage B S hS (A.left.map φ.op)).map (inverseImageComponentIso F m).hom ≫
        (spacesEtaleInverseImage_comp B S hS (A.left.map φ.op) (A.hom.app (op m))).inv.app F ≫
        (eqToHom (congrArg (fun k => spacesEtaleInverseImage B S hS k) e)).app F ≫
        (inverseImageComponentIso F n).inv := by
  have k2 := NatTrans.congr_app (augmentation_bridge_natTrans (A := A) φ e) F
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp] at k2
  have k2' := (k2 =≫ (augInvIso n).inv.app F)
  rw [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] at k2'
  have hf := SimplicialSiteSituation.Augmentation.fiberTransition_inverseImageSheaf
    (situation A) _ _ (etaleAugmentation A) F φ
  have hn := (transInvIso φ).inv.naturality
    (SimplicialSiteSituation.Augmentation.componentRestrictionIso (situation A) _ _
      (etaleAugmentation A) F m).hom
  dsimp only [spacesTransition, inverseImageComponentIso, Iso.trans_hom, Iso.trans_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv]
  change (transInvIso φ).inv.app (((situation A).restrict m).obj
      (SimplicialSiteSituation.Augmentation.inverseImageSheaf (situation A) _ _
        (etaleAugmentation A) F)) ≫
    (compEquiv n).functor.map (((situation A).fiberTransition φ).app
      (SimplicialSiteSituation.Augmentation.inverseImageSheaf (situation A) _ _
        (etaleAugmentation A) F)) = _
  rw [hf, Functor.map_comp, Functor.map_comp, k2']
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn ⊢
  rw [← reassoc_of% hn]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp]
  rfl

end InverseImage

end AlgebraicGeometry.Space.EtaleComponent
