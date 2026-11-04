module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleCartesianDescentDatum
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationCartesian
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianPairFunctor
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringDescent
public import StacksFrontier.Topology.Simplicial.ProperHypercoveringFullyFaithful

/-!
# Inverse images along fppf hypercoverings of algebraic spaces, from effective descent

Let `a : U → X` be an augmentation of a simplicial algebraic space over `S` which is an fppf
hypercovering of `X`, and let `a : Sh(U_étale) → Sh(X_spaces,étale)` be the morphism of topoi of
Section 0DE7. This file proves the statement of Stacks 0DH6 for this morphism — `a⁻¹` is fully
faithful on sheaves of sets and of abelian groups, with essential image the cartesian sheaves and
quasi-inverse `a_*` — from effective descent of spaces-étale sheaves along flat, locally finitely
presented, surjective morphisms of algebraic spaces, the statement
`AlgebraicGeometry.Space.EffectiveFppfDescent`.

The argument runs through the augmentation `a_0 : U_0 → X`, which is an fppf covering:

* the degree-`n` components of `a⁻¹F` are `a_n^* F`; a morphism `w : a⁻¹F ⟶ a⁻¹F'` gives
  morphisms `a_n^* F ⟶ a_n^* F'` (`componentHom`), compatible with the pullbacks along the face
  maps (`pullHom_componentHom`);
* its degree-zero part pulls back to the same morphism along the two projections of
  `U_0 ×_X U_0`, after pulling back further along the fppf covering `U_1 → U_0 ×_X U_0`; so it
  descends to `F ⟶ F'`, and `a⁻¹` is full; faithfulness is faithfulness of `a_0^*`;
* a cartesian sheaf `G` gives the descent datum `cartesianDescentDatum` along `a_0`; by effective
  descent it comes from a sheaf `F` on `X`, and the pair of Stacks 0D7I attached to `a⁻¹F` is
  isomorphic to the pair attached to `G`, so `a⁻¹F ≅ G`;
* the unit and counit statements follow formally, and the abelian statements follow by
  forgetting the group structures.

## Main results

* `AlgebraicGeometry.Space.EtaleComponent.inverseImage_fullyFaithful_of_effectiveDescent`:
  sheaves of sets.
* `AlgebraicGeometry.Space.EtaleComponent.abelianInverseImage_fullyFaithful_of_effectiveDescent`:
  sheaves of abelian groups.

## References

* [Stacks Project, Tag 0DH6](https://stacks.math.columbia.edu/tag/0DH6)
* [Stacks Project, Tag 0D7I](https://stacks.math.columbia.edu/tag/0D7I)
* [Stacks Project, Tag 0GFW](https://stacks.math.columbia.edu/tag/0GFW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Pseudofunctor
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open scoped Simplicial

universe u

namespace AlgebraicGeometry.Space.EtaleComponent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : SimplicialObject.Augmented (AlgebraicSpaces B S hS)}

section Generic

variable {C₁ C₂ : Type*} [Category C₁] [Category C₂] (P : C₁ ⥤ C₂)

/-- Pulling back a morphism conjugated by identifications `Γ_m` along a functor `P`, when the
identifications in the target degree are expressed through those of the source degree by the
transitions `t`, `t'`. -/
theorem conj_map_eq_of_transition {x x' y y' : C₁} {z z' t t' : C₂} (Γm : x ≅ y) (Γm' : x' ≅ y')
    (wm : x ⟶ x') (Γn : z ≅ t) (Γn' : z' ≅ t') (wn : z ⟶ z') (c : t ⟶ P.obj y)
    (ci : P.obj y ⟶ t) (hc : c ≫ ci = 𝟙 t) (ci' : P.obj y' ⟶ t') (tF : P.obj x ⟶ z)
    (tF' : P.obj x' ⟶ z') (htF : tF = P.map Γm.hom ≫ ci ≫ Γn.inv)
    (htF' : tF' = P.map Γm'.hom ≫ ci' ≫ Γn'.inv) (hnat : tF ≫ wn = P.map wm ≫ tF') :
    c ≫ P.map (Γm.inv ≫ wm ≫ Γm'.hom) ≫ ci' = Γn.inv ≫ wn ≫ Γn'.hom := by
  subst htF htF'
  have h₂ : P.map wm ≫ P.map Γm'.hom ≫ ci' = P.map Γm.hom ≫ ci ≫ Γn.inv ≫ wn ≫ Γn'.hom := by
    rw [← cancel_mono Γn'.inv]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    simpa only [Category.assoc] using hnat.symm
  rw [P.map_comp, P.map_comp, Category.assoc, Category.assoc, h₂, ← P.map_comp_assoc,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% hc]

/-- A morphism whose composite with an isomorphism is known, read through a functor and
identifications of the source and target. -/
theorem map_eq_of_comp_eq (E : C₁ ⥤ C₂) {x y z : C₁} {p s : C₂} (cI : x ⟶ y) (f₀ : y ⟶ z)
    (f₁ : x ⟶ z) [IsIso f₀] (hcomp : cI ≫ f₀ = f₁) (τ₁ : E.obj x ≅ p) (τ₀ : E.obj y ≅ s)
    (cC : p ⟶ s) (hcC : cC ≫ τ₀.inv ≫ E.map f₀ = τ₁.inv ≫ E.map f₁) :
    E.map cI = τ₁.hom ≫ cC ≫ τ₀.inv := by
  rw [← cancel_mono (E.map f₀), ← E.map_comp, hcomp, Category.assoc, Category.assoc, hcC,
    Iso.hom_inv_id_assoc]

/-- Transporting a commutative square of comparison morphisms through a functor and
identifications of its corners. -/
theorem map_comp_eq_map_comp_of_conj (E : C₁ ⥤ C₂) {a b c d : C₁} {p q s t : C₂} (T₁ : a ⟶ b)
    (cI₁ : a ⟶ c) (cI₂ : b ⟶ d) (T₀ : c ⟶ d) (τ₁X : E.obj a ≅ p) (τ₁Y : E.obj b ≅ q)
    (τ₀X : E.obj c ≅ s) (τ₀Y : E.obj d ≅ t) (d₁ : p ⟶ q) (d₀ : s ⟶ t) (cC₁ : p ⟶ s)
    (cC₂ : q ⟶ t) (hc₁ : E.map cI₁ = τ₁X.hom ≫ cC₁ ≫ τ₀X.inv)
    (hc₂ : E.map cI₂ = τ₁Y.hom ≫ cC₂ ≫ τ₀Y.inv) (n₁ : E.map T₁ ≫ τ₁Y.hom = τ₁X.hom ≫ d₁)
    (n₀ : E.map T₀ ≫ τ₀Y.hom = τ₀X.hom ≫ d₀) (hm : d₁ ≫ cC₂ = cC₁ ≫ d₀) :
    E.map (T₁ ≫ cI₂) = E.map (cI₁ ≫ T₀) := by
  have h₀ : d₀ ≫ τ₀Y.inv = τ₀X.inv ≫ E.map T₀ := by
    rw [Iso.eq_inv_comp, ← reassoc_of% n₀, Iso.hom_inv_id, Category.comp_id]
  rw [E.map_comp, E.map_comp, hc₁, hc₂, reassoc_of% n₁, reassoc_of% hm, h₀]
  simp only [Category.assoc]

/-- A square through an isomorphism, conjugated by a further isomorphism. -/
theorem map_comp_eq_of_conj (P₁ P₀ : C₁ ⥤ C₂) {x y z : C₁} (g : x ≅ y) (ψ : y ⟶ z)
    (c : P₁.obj z ⟶ P₀.obj z) {w : C₂} (k₁ : P₁.obj y ⟶ w) (k₂ : w ⟶ P₀.obj y)
    (h : P₁.map ψ ≫ c = (k₁ ≫ k₂) ≫ P₀.map ψ) (cX : P₁.obj x ⟶ P₀.obj x)
    (hX : cX = P₁.map g.hom ≫ k₁ ≫ k₂ ≫ P₀.map g.inv) :
    P₁.map (g.hom ≫ ψ) ≫ c = cX ≫ P₀.map (g.hom ≫ ψ) := by
  subst hX
  rw [P₁.map_comp, Category.assoc, h, P₀.map_comp, Category.assoc, Category.assoc,
    Category.assoc, Category.assoc, ← P₀.map_comp_assoc g.inv g.hom, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

end Generic

section ComponentHom

/-- Opposite and `toLoc` turn a factorisation `f ≫ g = k` into one in the reverse order. -/
private theorem toLoc_op_comp_eq {D : Type*} [Category D] {x y z : D} {f : x ⟶ y} {g : y ⟶ z}
    {k : x ⟶ z} (h : f ≫ g = k) : g.op.toLoc ≫ f.op.toLoc = k.op.toLoc := by
  rw [← Quiver.Hom.comp_toLoc, ← op_comp, h]

variable {F F' : (spacesEtalePseudofunctor B S hS).obj (.mk (op A.right))}

/-- The morphism `a_n^* F ⟶ a_n^* F'` induced in degree `n` by a morphism `a⁻¹F ⟶ a⁻¹F'`. -/
def componentHom (w : invImage A F ⟶ invImage A F') (n : SimplexCategory) :
    ((spacesEtalePseudofunctor B S hS).map (augF A n).op.toLoc).toFunctor.obj F ⟶
      ((spacesEtalePseudofunctor B S hS).map (augF A n).op.toLoc).toFunctor.obj F' :=
  (inverseImageCompIso F n).inv ≫ (compEquiv n).functor.map (((situation A).restrict n).map w) ≫
    (inverseImageCompIso F' n).hom

/-- The morphism induced in degree `n` by `a⁻¹u` is `a_n^* u`. -/
theorem componentHom_map (u : F ⟶ F') (n : SimplexCategory) :
    componentHom (F := F) (F' := F') ((etaleAugmentationMorphism A).inverseImage.map u) n =
      ((spacesEtalePseudofunctor B S hS).map (augF A n).op.toLoc).toFunctor.map u :=
  (Iso.inv_comp_eq _).mpr (inverseImageCompIso_naturality u n)

/-- **The induced morphisms are compatible with the face maps**: pulling back the morphism
induced in degree `m` along `U(φ) : U_n → U_m` gives the morphism induced in degree `n`. -/
theorem pullHom_componentHom (w : invImage A F ⟶ invImage A F') {m n : SimplexCategory}
    (φ : m ⟶ n) :
    pullHom (F := spacesEtalePseudofunctor B S hS) (componentHom w m) (A.left.map φ.op)
        (augF A n) (augF A n) (map_comp_augF φ) (map_comp_augF φ) = componentHom w n := by
  have hφ := toLoc_op_comp_eq (map_comp_augF (A := A) φ)
  exact conj_map_eq_of_transition
    ((spacesEtalePseudofunctor B S hS).map (A.left.map φ.op).op.toLoc).toFunctor
    (inverseImageCompIso F m) (inverseImageCompIso F' m) _ (inverseImageCompIso F n)
    (inverseImageCompIso F' n) _
    (((spacesEtalePseudofunctor B S hS).mapComp' (augF A m).op.toLoc (A.left.map φ.op).op.toLoc
      (augF A n).op.toLoc hφ).hom.toNatTrans.app F) _
    (Cat.Hom.hom_inv_id_toNatTrans_app ((spacesEtalePseudofunctor B S hS).mapComp'
      (augF A m).op.toLoc (A.left.map φ.op).op.toLoc (augF A n).op.toLoc hφ) F) _
    (transitionF (invImage A F) φ) (transitionF (invImage A F') φ)
    (transitionF_inverseImage F φ hφ) (transitionF_inverseImage F' φ hφ)
    (transitionF_naturality w φ)

variable (F) in
/-- **Stacks 0D7H (1)**, for the augmentation of `U_étale`: `a⁻¹F` is cartesian. -/
theorem isCartesianSheaf_invImage :
    SimplicialSiteSituation.IsCartesianSheaf (situation A) (invImage A F) :=
  SimplicialSiteSituation.Augmentation.isCartesianSheaf_totalMorphismOfTopoi_inverseImage
    (situation A) _ _ (etaleAugmentation A) F

/-- A morphism `a⁻¹F ⟶ a⁻¹F'` is determined by the morphism it induces in degree zero. -/
theorem componentHom_injective {w w' : invImage A F ⟶ invImage A F'}
    (h : componentHom w ⦋0⦌ = componentHom w' ⦋0⦌) : w = w' := by
  have h₀ : ((situation A).restrict ⦋0⦌).map w = ((situation A).restrict ⦋0⦌).map w' :=
    (compEquiv ⦋0⦌).functor.map_injective <|
      (Iso.cancel_iso_hom_right _ _ (inverseImageCompIso F' ⦋0⦌)).mp
        ((Iso.cancel_iso_inv_left (inverseImageCompIso F ⦋0⦌) _ _).mp h)
  let X : (situation A).CartesianSheaf := ⟨invImage A F, isCartesianSheaf_invImage F⟩
  let Y : (situation A).CartesianSheaf := ⟨invImage A F', isCartesianSheaf_invImage F'⟩
  exact congrArg (fun t => t.hom) ((situation A).cartesianPairFunctor.map_injective (X := X)
    (Y := Y) (a₁ := ObjectProperty.homMk w) (a₂ := ObjectProperty.homMk w')
    (SimplicialSiteSituation.CartesianPair.hom_ext _ h₀))

end ComponentHom

section Pairs

/-- The comparison isomorphism of a cartesian sheaf is pinned by the transitions. -/
theorem cartesianComparison_comp_transitionF (G : Sheaf (situation A).totalTopology (Type (u + 1)))
    (hG : SimplicialSiteSituation.IsCartesianSheaf (situation A) G) :
    cartesianComparison G hG ≫ transitionF G (vertex₁ 0) = transitionF G (vertex₁ 1) := by
  rw [cartesianComparison, Category.assoc, ← transitionIso_hom G hG (vertex₁ 0), Iso.inv_hom_id,
    Category.comp_id]

/-- **The comparison isomorphism of the pair of Stacks 0D7I** attached to a cartesian sheaf,
read on `U_{1, spaces, étale}`, is the comparison isomorphism `cartesianComparison`. -/
theorem compEquiv_map_cartesianIso_hom (G : Sheaf (situation A).totalTopology (Type (u + 1)))
    (hG : SimplicialSiteSituation.IsCartesianSheaf (situation A) G) :
    (compEquiv ⦋1⦌).functor.map ((situation A).cartesianIso ⟨G, hG⟩).hom =
      ((transInvIso (vertex₁ 1)).app (((situation A).restrict ⦋0⦌).obj G)).hom ≫
        cartesianComparison G hG ≫
        ((transInvIso (vertex₁ 0)).app (((situation A).restrict ⦋0⦌).obj G)).inv := by
  have := hG (vertex₁ 0)
  exact map_eq_of_comp_eq (compEquiv ⦋1⦌).functor _ _ _
    ((situation A).cartesianIso_hom_comp ⟨G, hG⟩) _ _ _
    (cartesianComparison_comp_transitionF G hG)

/-- **A morphism of degree-zero components is a morphism of pairs** as soon as it is
compatible with the comparison isomorphisms on `U_{1, spaces, étale}`. -/
theorem cartesianPair_comm {G₁ G₂ : Sheaf (situation A).totalTopology (Type (u + 1))}
    (h₁ : SimplicialSiteSituation.IsCartesianSheaf (situation A) G₁)
    (h₂ : SimplicialSiteSituation.IsCartesianSheaf (situation A) G₂)
    (r : ((situation A).restrict ⦋0⦌).obj G₁ ⟶ ((situation A).restrict ⦋0⦌).obj G₂)
    (m : compF G₁ ⦋0⦌ ⟶ compF G₂ ⦋0⦌) (hr : (compEquiv ⦋0⦌).functor.map r = m)
    (hm : ((spacesEtalePseudofunctor B S hS).map (face₁ A 1).op.toLoc).toFunctor.map m ≫
        cartesianComparison G₂ h₂ =
      cartesianComparison G₁ h₁ ≫
        ((spacesEtalePseudofunctor B S hS).map (face₁ A 0).op.toLoc).toFunctor.map m) :
    ((situation A).transitionMorphism (SimplexCategory.δ (1 : Fin 2))).inverseImage.map r ≫
        ((situation A).cartesianIso ⟨G₂, h₂⟩).hom =
      ((situation A).cartesianIso ⟨G₁, h₁⟩).hom ≫
        ((situation A).transitionMorphism (SimplexCategory.δ (0 : Fin 2))).inverseImage.map r := by
  subst hr
  apply (compEquiv ⦋1⦌).functor.map_injective
  have n₁ := (transInvIso (A := A) (vertex₁ 1)).hom.naturality r
  have n₀ := (transInvIso (A := A) (vertex₁ 0)).hom.naturality r
  dsimp only [Functor.comp_map] at n₁ n₀
  exact map_comp_eq_map_comp_of_conj (compEquiv ⦋1⦌).functor _ _ _ _ _ _ _ _ _ _ _ _
    (compEquiv_map_cartesianIso_hom G₁ h₁) (compEquiv_map_cartesianIso_hom G₂ h₂) n₁ n₀ hm

end Pairs

section Descent

variable (hyp : IsFppfHypercovering A) (hdesc : EffectiveFppfDescent B S hS)
include hyp hdesc

/-- **`a⁻¹` is faithful.** -/
theorem inverseImage_faithful_of_effectiveDescent :
    (etaleAugmentationMorphism A).inverseImage.Faithful where
  map_injective {F F'} {u v} h :=
    hdesc.map_injective hyp.map_zero ((componentHom_map (F := F) (F' := F') u ⦋0⦌).symm.trans
      ((congrArg (fun t => componentHom t ⦋0⦌) h).trans (componentHom_map v ⦋0⦌)))

/-- **Morphisms between inverse images descend**: every morphism `a⁻¹F ⟶ a⁻¹F'` is `a⁻¹u`. -/
theorem exists_inverseImage_map_eq {F F' : (spacesEtalePseudofunctor B S hS).obj
      (.mk (op A.right))} (w : invImage A F ⟶ invImage A F') :
    ∃ u : F ⟶ F', (etaleAugmentationMorphism A).inverseImage.map u = w := by
  have he : edgeMap A ≫ (descentPullback A).p = augF A ⦋1⦌ := by
    rw [← (descentPullback A).hp₁, ← Category.assoc, edgeMap_p₁, map_comp_augF]
  have H : pullHom (F := spacesEtalePseudofunctor B S hS) (componentHom w ⦋0⦌)
      (descentPullback A).p₁ (descentPullback A).p (descentPullback A).p
      (descentPullback A).hp₁ (descentPullback A).hp₁ =
      pullHom (F := spacesEtalePseudofunctor B S hS) (componentHom w ⦋0⦌)
      (descentPullback A).p₂ (descentPullback A).p (descentPullback A).p
      (descentPullback A).hp₂ (descentPullback A).hp₂ := by
    refine pullHom_injective (edgeMap A) (augF A ⦋1⦌) (augF A ⦋1⦌) he he
      (fun a b h => hdesc.map_injective (fppfSurjective_edgeMap hyp) h) ?_
    rw [pullHom_pullHom, pullHom_pullHom,
      pullHom_congr_left _ edgeMap_p₁ _ _ _ _ (map_comp_augF _) (map_comp_augF _),
      pullHom_congr_left _ edgeMap_p₂ _ _ _ _ (map_comp_augF _) (map_comp_augF _),
      pullHom_componentHom, pullHom_componentHom]
  obtain ⟨u, hu⟩ := hdesc.exists_map_eq hyp.map_zero (descentPullback A) (componentHom w ⦋0⦌)
    (descentSquareApp_comm_of_pullHom_eq (descentPullback A) _ H)
  exact ⟨u, componentHom_injective ((componentHom_map u ⦋0⦌).trans hu)⟩

/-- **`a⁻¹` is full.** -/
theorem inverseImage_full_of_effectiveDescent :
    (etaleAugmentationMorphism A).inverseImage.Full where
  map_surjective {F F'} w := exists_inverseImage_map_eq hyp hdesc (F := F) (F' := F') w

/-- **Cartesian sheaves are inverse images**: every cartesian sheaf on `U_étale` is isomorphic
to `a⁻¹F` for a sheaf `F` on `X`. -/
theorem exists_inverseImage_iso (G : Sheaf (situation A).totalTopology (Type (u + 1)))
    (hG : SimplicialSiteSituation.IsCartesianSheaf (situation A) G) :
    ∃ F : (spacesEtalePseudofunctor B S hS).obj (.mk (op A.right)),
      Nonempty (invImage A F ≅ G) := by
  obtain ⟨F, ⟨ψ⟩⟩ := hdesc.exists_iso (f := augF A ⦋0⦌) hyp.map_zero
    (cartesianDescentDatum hyp hdesc G hG)
  have hψ : ((spacesEtalePseudofunctor B S hS).map (face₁ A 1).op.toLoc).toFunctor.map
        (ψ.hom.hom ()) ≫ cartesianComparison G hG =
      (((spacesEtalePseudofunctor B S hS).mapComp' (augF A ⦋0⦌).op.toLoc
          (face₁ A 1).op.toLoc (augF A ⦋1⦌).op.toLoc
          (toLoc_op_comp_eq (map_comp_augF _))).inv.toNatTrans.app F ≫
        ((spacesEtalePseudofunctor B S hS).mapComp' (augF A ⦋0⦌).op.toLoc
          (face₁ A 0).op.toLoc (augF A ⦋1⦌).op.toLoc
          (toLoc_op_comp_eq (map_comp_augF _))).hom.toNatTrans.app F) ≫
        ((spacesEtalePseudofunctor B S hS).map (face₁ A 0).op.toLoc).toFunctor.map
          (ψ.hom.hom ()) := by
    rw [← cartesianDescentDatum_hom_edge hyp hdesc G hG]
    exact ψ.hom.comm (augF A ⦋1⦌) (face₁ A 1) (face₁ A 0) (map_comp_augF _) (map_comp_augF _)
  let ψ₀ : ((spacesEtalePseudofunctor B S hS).map (augF A ⦋0⦌).op.toLoc).toFunctor.obj F ≅
      compF G ⦋0⦌ :=
    { hom := ψ.hom.hom ()
      inv := ψ.inv.hom ()
      hom_inv_id := congrArg (fun t => t.hom ()) ψ.hom_inv_id
      inv_hom_id := congrArg (fun t => t.hom ()) ψ.inv_hom_id }
  let m : compF (invImage A F) ⦋0⦌ ≅ compF G ⦋0⦌ := inverseImageCompIso F ⦋0⦌ ≪≫ ψ₀
  have hF := isCartesianSheaf_invImage (A := A) F
  have hm := map_comp_eq_of_conj
    ((spacesEtalePseudofunctor B S hS).map (face₁ A 1).op.toLoc).toFunctor
    ((spacesEtalePseudofunctor B S hS).map (face₁ A 0).op.toLoc).toFunctor
    (inverseImageCompIso F ⦋0⦌) (ψ.hom.hom ()) _ _ _ hψ (cartesianComparison (invImage A F) hF)
    (cartesianComparison_inverseImage F hF _ _)
  let r : ((situation A).restrict ⦋0⦌).obj (invImage A F) ≅ ((situation A).restrict ⦋0⦌).obj G :=
    (compEquiv ⦋0⦌).fullyFaithfulFunctor.preimageIso m
  let X : (situation A).CartesianSheaf := ⟨invImage A F, hF⟩
  let Y : (situation A).CartesianSheaf := ⟨G, hG⟩
  let e : (situation A).cartesianPairFunctor.obj X ≅ (situation A).cartesianPairFunctor.obj Y :=
    SimplicialSiteSituation.CartesianPair.isoMk _ r (cartesianPair_comm hF hG r.hom m.hom
      ((compEquiv ⦋0⦌).fullyFaithfulFunctor.map_preimage m.hom) hm)
  exact ⟨F, ⟨(ObjectProperty.ι _).mapIso
    ((Functor.FullyFaithful.ofFullyFaithful (situation A).cartesianPairFunctor).preimageIso e)⟩⟩

end Descent

/-! ### The statement of Stacks 0DH6, from effective descent -/

/-- **Inverse images along fppf hypercoverings of algebraic spaces, sheaves of sets**, from
effective descent along fppf coverings. Let `a : U → X` be an augmentation of a simplicial
algebraic space over `S` which is an fppf hypercovering of `X`. If spaces-étale sheaves satisfy
effective descent along flat, locally finitely presented, surjective morphisms, then
`a⁻¹ : Sh(X_spaces,étale) ⥤ Sh(U_étale)` is fully faithful, its essential image consists
exactly of the cartesian sheaves, and `a_*` is a quasi-inverse: the unit of `a⁻¹ ⊣ a_*` is
invertible, and so is its counit at every cartesian sheaf. -/
theorem inverseImage_fullyFaithful_of_effectiveDescent (hyp : IsFppfHypercovering A)
    (hdesc : EffectiveFppfDescent B S hS) :
    (etaleAugmentationMorphism A).inverseImage.Full ∧
      (etaleAugmentationMorphism A).inverseImage.Faithful ∧
      (∀ G, (etaleAugmentationMorphism A).inverseImage.essImage G ↔
        SimplicialSiteSituation.IsCartesianSheaf (etaleSimplicialSite A).situation G) ∧
      (∀ F, IsIso ((etaleAugmentationMorphism A).adj.unit.app F)) ∧
      (∀ G, SimplicialSiteSituation.IsCartesianSheaf (etaleSimplicialSite A).situation G →
        IsIso ((etaleAugmentationMorphism A).adj.counit.app G)) := by
  have := inverseImage_full_of_effectiveDescent hyp hdesc
  have := inverseImage_faithful_of_effectiveDescent hyp hdesc
  have hess : ∀ G, (etaleAugmentationMorphism A).inverseImage.essImage G ↔
      SimplicialSiteSituation.IsCartesianSheaf (etaleSimplicialSite A).situation G :=
    fun G => ⟨fun ⟨F, ⟨e⟩⟩ => SimplicialSiteSituation.isCartesianSheaf_of_iso _ e
      (isCartesianSheaf_invImage F), exists_inverseImage_iso hyp hdesc G⟩
  exact ⟨inferInstance, inferInstance, hess, fun F => inferInstance, fun G hG =>
    ((etaleAugmentationMorphism A).adj.isIso_counit_app_iff_mem_essImage).mpr ((hess G).mpr hG)⟩

/-- **Inverse images along fppf hypercoverings of algebraic spaces, sheaves of abelian groups**,
from effective descent along fppf coverings. Let `a : U → X` be an augmentation of a simplicial
algebraic space over `S` which is an fppf hypercovering of `X`. If spaces-étale sheaves satisfy
effective descent along flat, locally finitely presented, surjective morphisms, then
`a⁻¹ : Ab(X_spaces,étale) ⥤ Ab(U_étale)` is fully faithful, its essential image consists
exactly of the cartesian abelian sheaves, and `a_*` is a quasi-inverse: the unit of
`a⁻¹ ⊣ a_*` is invertible, and so is its counit at every cartesian abelian sheaf. -/
theorem abelianInverseImage_fullyFaithful_of_effectiveDescent (hyp : IsFppfHypercovering A)
    (hdesc : EffectiveFppfDescent B S hS) :
    (Sites.abelianInverseImage (etaleAugmentationMorphism A)).Full ∧
      (Sites.abelianInverseImage (etaleAugmentationMorphism A)).Faithful ∧
      (∀ G, (Sites.abelianInverseImage (etaleAugmentationMorphism A)).essImage G ↔
        SimplicialSiteSituation.IsCartesianAbSheaf (etaleSimplicialSite A).situation G) ∧
      (∀ F, IsIso ((Stacks.Topos.AbelianPushforward.abelianInverseImageAdjPushforward
        (etaleSimplicialSite A).totalTopology (etaleAugmentationMorphism A)).unit.app F)) ∧
      (∀ G, SimplicialSiteSituation.IsCartesianAbSheaf (etaleSimplicialSite A).situation G →
        IsIso ((Stacks.Topos.AbelianPushforward.abelianInverseImageAdjPushforward
          (etaleSimplicialSite A).totalTopology (etaleAugmentationMorphism A)).counit.app G)) := by
  obtain ⟨-, -, -, hunit, hcounit⟩ := inverseImage_fullyFaithful_of_effectiveDescent hyp hdesc
  let J := (etaleSimplicialSite A).totalTopology
  let K := SpacesEtale.topology B S hS A.right
  let adj := Stacks.Topos.AbelianPushforward.abelianInverseImageAdjPushforward J
    (etaleAugmentationMorphism A)
  have hunitAb : ∀ F, IsIso (adj.unit.app F) := by
    intro F
    rw [← isIso_iff_of_reflects_iso _ (sheafCompose K (forget AddCommGrpCat.{u + 1})),
      Stacks.Topos.AbelianPushforward.abelianInverseImageAdjPushforward_unit_forget J
        (etaleAugmentationMorphism A) F]
    exact hunit _
  have hcounitAb : ∀ G, SimplicialSiteSituation.IsCartesianAbSheaf
      (etaleSimplicialSite A).situation G → IsIso (adj.counit.app G) := by
    intro G hG
    rw [← isIso_iff_of_reflects_iso _ (sheafCompose J (forget AddCommGrpCat.{u + 1})),
      Stacks.Topos.AbelianPushforward.abelianInverseImageAdjPushforward_counit_forget J
        (etaleAugmentationMorphism A) G]
    exact hcounit _ hG
  have : IsIso adj.unit := NatIso.isIso_of_isIso_app _
  have hff := adj.fullyFaithfulLOfIsIsoUnit
  have := hff.full
  have := hff.faithful
  refine ⟨inferInstance, inferInstance, fun G => ⟨fun hG => ?_, fun hG =>
    (adj.isIso_counit_app_iff_mem_essImage).mp (hcounitAb G hG)⟩, hunitAb, hcounitAb⟩
  have hc : IsIso (adj.counit.app G) := (adj.isIso_counit_app_iff_mem_essImage).mpr hG
  have hc' : IsIso ((etaleAugmentationMorphism A).adj.counit.app
      ((sheafCompose J (forget AddCommGrpCat.{u + 1})).obj G)) := by
    rw [← Stacks.Topos.AbelianPushforward.abelianInverseImageAdjPushforward_counit_forget J
      (etaleAugmentationMorphism A) G]
    exact ((sheafCompose J (forget AddCommGrpCat.{u + 1})).mapIso
      (@asIso _ _ _ _ (adj.counit.app G) hc)).isIso_hom
  exact SimplicialSiteSituation.isCartesianSheaf_of_iso _
    (@asIso _ _ _ _ ((etaleAugmentationMorphism A).adj.counit.app
      ((sheafCompose J (forget AddCommGrpCat.{u + 1})).obj G)) hc')
    (isCartesianSheaf_invImage _)

end AlgebraicGeometry.Space.EtaleComponent
