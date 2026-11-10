module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleSpacesTransitions
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.FppfDescent
public import StacksFrontier.CategoryTheory.Sites.Descent.SingletonCoalgebraObj

/-!
# The comparison isomorphism of a cartesian sheaf on `U_étale`, on spaces-étale sheaves

Let `G` be a cartesian sheaf on the small étale site of an augmented simplicial algebraic space
`a : U → X`. Its transitions `U(θ)^* G_0 ⟶ G_n` along the vertices `θ : [0] → [n]` are
invertible, and the comparison `α : d₁^* G_0 ≅ d₀^* G_0` over `U_1` is the composite of the
transitions along the two vertices of `[1]`. Pulled back along an edge `U(ε) : U_n → U_1`, `α`
becomes the composite of the transitions along the two vertices of the edge; this is the
cocycle condition of `α` over `U_2`, and it says that `α` is the identity over the degenerate
edges.

All statements are made with the compositors of the pseudofunctor of spaces-étale inverse
images, which is the language of descent data.

## Main results

* `AlgebraicGeometry.Space.EtaleComponent.mapComp'_hom_app_eq`: the compositor of the
  pseudofunctor is the compositor of the spaces-étale inverse images.
* `AlgebraicGeometry.Space.EtaleComponent.spacesTransition_comp'`: the transitions compose.
* `AlgebraicGeometry.Space.EtaleComponent.pullHom_cartesianComparison`: the pullback of the
  comparison along an edge.

## References

* [Stacks Project, Tag 0D7I](https://stacks.math.columbia.edu/tag/0D7I)
* [Stacks Project, Tag 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Pseudofunctor
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open scoped Simplicial

universe u

namespace AlgebraicGeometry.Space.EtaleComponent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : SimplicialObject.Augmented (AlgebraicSpaces B S hS)}

/-- The compositor of the pseudofunctor of spaces-étale inverse images is the compositor of the
spaces-étale inverse images. -/
theorem mapComp'_hom_app_eq {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (h : f ≫ g = fg) (M : spacesEtaleSheafCat B S hS Z) :
    ((spacesEtalePseudofunctor B S hS).mapComp' g.op.toLoc f.op.toLoc fg.op.toLoc
        (by rw [← h]; rfl)).hom.toNatTrans.app M =
      (eqToHom (congrArg (fun k => spacesEtaleInverseImage B S hS k) h.symm)).app M ≫
        (spacesEtaleInverseImage_comp B S hS f g).hom.app M := by
  subst h
  exact (congrArg (fun e => e.hom.toNatTrans.app M)
    (mapComp'_eq_mapComp (spacesEtalePseudofunctor B S hS) g.op.toLoc f.op.toLoc)).trans
    (Category.id_comp _).symm

/-- **The transitions compose**, through the compositors of the pseudofunctor of spaces-étale
inverse images. -/
theorem spacesTransition_comp' (G : Sheaf (situation A).totalTopology (Type (u + 1)))
    {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) (θ : l ⟶ n) (hθ : ψ ≫ φ = θ)
    (h : (A.left.map ψ.op).op.toLoc ≫ (A.left.map φ.op).op.toLoc = (A.left.map θ.op).op.toLoc) :
    spacesTransition G θ =
      ((spacesEtalePseudofunctor B S hS).mapComp' (A.left.map ψ.op).op.toLoc
          (A.left.map φ.op).op.toLoc (A.left.map θ.op).op.toLoc h).hom.toNatTrans.app
          (spacesComponent G l) ≫
        (spacesEtaleInverseImage B S hS (A.left.map φ.op)).map (spacesTransition G ψ) ≫
        spacesTransition G φ := by
  subst hθ
  have e : A.left.map φ.op ≫ A.left.map ψ.op = A.left.map (ψ ≫ φ).op := by
    rw [op_comp, A.left.map_comp]
  rw [spacesTransition_comp G ψ φ e, mapComp'_hom_app_eq _ _ _ e]
  exact (Category.assoc _ _ _).symm

/-! ### The comparison isomorphism over `U_1` -/

/-- The two vertices `[0] → [1]`. -/
abbrev vertex₁ (i : Fin 2) : ⦋0⦌ ⟶ ⦋1⦌ := SimplexCategory.δ i

variable (A) in
/-- The two face maps `U_1 → U_0`. -/
abbrev face₁ (i : Fin 2) : A.left.obj (op ⦋1⦌) ⟶ A.left.obj (op ⦋0⦌) :=
  A.left.map (vertex₁ i).op

section Cartesian

variable (G : Sheaf (situation A).totalTopology (Type (u + 1)))
  (hG : SimplicialSiteSituation.IsCartesianSheaf (situation A) G)

/-- The component of degree `n` of a sheaf on `U_étale`, as an object of the fibre of the
pseudofunctor of spaces-étale inverse images. -/
def compF (n : SimplexCategory) :
    (spacesEtalePseudofunctor B S hS).obj (.mk (op (A.left.obj (op n)))) :=
  spacesComponent G n

/-- The transition of a sheaf on `U_étale`, typed through the pseudofunctor of spaces-étale
inverse images. -/
def transitionF {m n : SimplexCategory} (φ : m ⟶ n) :
    ((spacesEtalePseudofunctor B S hS).map (A.left.map φ.op).op.toLoc).toFunctor.obj
        (compF G m) ⟶ compF G n :=
  spacesTransition G φ

/-- **The transitions compose**, in the language of the pseudofunctor. -/
theorem transitionF_comp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) (θ : l ⟶ n)
    (hθ : ψ ≫ φ = θ)
    (h : (A.left.map ψ.op).op.toLoc ≫ (A.left.map φ.op).op.toLoc = (A.left.map θ.op).op.toLoc) :
    transitionF G θ =
      ((spacesEtalePseudofunctor B S hS).mapComp' (A.left.map ψ.op).op.toLoc
          (A.left.map φ.op).op.toLoc (A.left.map θ.op).op.toLoc h).hom.toNatTrans.app
          (compF G l) ≫
        ((spacesEtalePseudofunctor B S hS).map (A.left.map φ.op).op.toLoc).toFunctor.map
          (transitionF G ψ) ≫ transitionF G φ :=
  spacesTransition_comp' G ψ φ θ hθ h

/-- The transition of a cartesian sheaf, as an isomorphism. -/
def transitionIso {m n : SimplexCategory} (φ : m ⟶ n) :
    ((spacesEtalePseudofunctor B S hS).map (A.left.map φ.op).op.toLoc).toFunctor.obj
        (compF G m) ≅ compF G n :=
  @asIso _ _ _ _ (transitionF G φ) (isIso_spacesTransition G hG φ)

/-- The forward map of `transitionIso G hG φ` is the transition `transitionF G φ`. -/
@[simp]
theorem transitionIso_hom {m n : SimplexCategory} (φ : m ⟶ n) :
    (transitionIso G hG φ).hom = transitionF G φ := rfl

/-- **The comparison isomorphism of a cartesian sheaf**, `d₁^* G_0 ≅ d₀^* G_0` over `U_1`: the
transition along the source vertex followed by the inverse of the transition along the target
vertex. -/
def cartesianComparison :
    ((spacesEtalePseudofunctor B S hS).map (face₁ A 1).op.toLoc).toFunctor.obj (compF G ⦋0⦌) ⟶
      ((spacesEtalePseudofunctor B S hS).map (face₁ A 0).op.toLoc).toFunctor.obj
        (compF G ⦋0⦌) :=
  transitionF G (vertex₁ 1) ≫ (transitionIso G hG (vertex₁ 0)).inv

/-- **The comparison isomorphism pulled back along an edge** `ε : [1] → [n]` is the composite of
the transition along the source vertex of the edge with the inverse of the transition along its
target vertex. -/
theorem pullHom_cartesianComparison {n : SimplexCategory} (ε : ⦋1⦌ ⟶ n) (a b : ⦋0⦌ ⟶ n)
    (ha : vertex₁ 1 ≫ ε = a) (hb : vertex₁ 0 ≫ ε = b)
    (h₁ : A.left.map ε.op ≫ face₁ A 1 = A.left.map a.op)
    (h₂ : A.left.map ε.op ≫ face₁ A 0 = A.left.map b.op) :
    pullHom (F := spacesEtalePseudofunctor B S hS) (cartesianComparison G hG) (A.left.map ε.op)
        (A.left.map a.op) (A.left.map b.op) h₁ h₂ =
      transitionF G a ≫ (transitionIso G hG b).inv := by
  have hta := transitionF_comp G (vertex₁ 1) ε a ha
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h₁])
  have htb := transitionF_comp G (vertex₁ 0) ε b hb
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h₂])
  have hα : cartesianComparison G hG ≫ transitionF G (vertex₁ 0) = transitionF G (vertex₁ 1) := by
    rw [cartesianComparison, Category.assoc, ← transitionIso_hom G hG (vertex₁ 0),
      Iso.inv_hom_id, Category.comp_id]
  rw [← cancel_mono (transitionIso G hG b).hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    transitionIso_hom, htb, hta]
  dsimp only [pullHom]
  simp only [Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app_assoc]
  rw [← Functor.map_comp_assoc, hα]

/-! ### The cocycle condition and the degenerate edges -/

/-- The three vertices `[0] → [2]`. -/
abbrev vertex₂ (k : Fin 3) : ⦋0⦌ ⟶ ⦋2⦌ := SimplexCategory.const ⦋0⦌ ⦋2⦌ k

/-- The three edges `[1] → [2]`. -/
abbrev edge₂ (j : Fin 3) : ⦋1⦌ ⟶ ⦋2⦌ := SimplexCategory.δ j

/-- **The cocycle condition of the comparison isomorphism**, over `U_2`. -/
theorem cartesianComparison_cocycle :
    pullHom (F := spacesEtalePseudofunctor B S hS) (cartesianComparison G hG)
        (A.left.map (edge₂ 2).op) (A.left.map (vertex₂ 0).op) (A.left.map (vertex₂ 1).op)
        (by rw [← A.left.map_comp, ← op_comp, SimplexCategory.delta_one_comp_delta_two])
        (by rw [← A.left.map_comp, ← op_comp, SimplexCategory.delta_zero_comp_delta_two]) ≫
      pullHom (F := spacesEtalePseudofunctor B S hS) (cartesianComparison G hG)
        (A.left.map (edge₂ 0).op) (A.left.map (vertex₂ 1).op) (A.left.map (vertex₂ 2).op)
        (by rw [← A.left.map_comp, ← op_comp, SimplexCategory.delta_one_comp_delta_zero])
        (by rw [← A.left.map_comp, ← op_comp, SimplexCategory.delta_zero_comp_delta_zero]) =
      pullHom (F := spacesEtalePseudofunctor B S hS) (cartesianComparison G hG)
        (A.left.map (edge₂ 1).op) (A.left.map (vertex₂ 0).op) (A.left.map (vertex₂ 2).op)
        (by rw [← A.left.map_comp, ← op_comp, SimplexCategory.delta_one_comp_delta_one])
        (by rw [← A.left.map_comp, ← op_comp, SimplexCategory.delta_zero_comp_delta_one]) := by
  rw [pullHom_cartesianComparison G hG _ _ _ SimplexCategory.delta_one_comp_delta_two
      SimplexCategory.delta_zero_comp_delta_two,
    pullHom_cartesianComparison G hG _ _ _ SimplexCategory.delta_one_comp_delta_zero
      SimplexCategory.delta_zero_comp_delta_zero,
    pullHom_cartesianComparison G hG _ _ _ SimplexCategory.delta_one_comp_delta_one
      SimplexCategory.delta_zero_comp_delta_one]
  simp only [Category.assoc, ← transitionIso_hom G hG (vertex₂ 1), Iso.inv_hom_id_assoc]

/-- **The comparison isomorphism is the identity over the degenerate edges.** -/
theorem pullHom_cartesianComparison_degenerate :
    pullHom (F := spacesEtalePseudofunctor B S hS) (cartesianComparison G hG)
        (A.left.map (SimplexCategory.σ 0 : ⦋1⦌ ⟶ ⦋0⦌).op) (A.left.map (𝟙 ⦋0⦌).op)
        (A.left.map (𝟙 ⦋0⦌).op)
        (by rw [← A.left.map_comp, ← op_comp, Subsingleton.elim (vertex₁ 1 ≫ _) (𝟙 ⦋0⦌)])
        (by rw [← A.left.map_comp, ← op_comp, Subsingleton.elim (vertex₁ 0 ≫ _) (𝟙 ⦋0⦌)]) =
      𝟙 _ := by
  rw [pullHom_cartesianComparison G hG _ _ _ (Subsingleton.elim _ _) (Subsingleton.elim _ _),
    ← transitionIso_hom G hG (𝟙 ⦋0⦌), Iso.hom_inv_id]

/-- **The cocycle condition of the comparison isomorphism, pulled back along any morphism to
`U_2`.** -/
theorem cartesianComparison_cocycle_pullHom {W : AlgebraicSpaces B S hS}
    (σ : W ⟶ A.left.obj (op ⦋2⦌)) :
    pullHom (F := spacesEtalePseudofunctor B S hS) (cartesianComparison G hG)
        (σ ≫ A.left.map (edge₂ 2).op) (σ ≫ A.left.map (vertex₂ 0).op)
        (σ ≫ A.left.map (vertex₂ 1).op)
        (by rw [Category.assoc, ← A.left.map_comp, ← op_comp,
          SimplexCategory.delta_one_comp_delta_two])
        (by rw [Category.assoc, ← A.left.map_comp, ← op_comp,
          SimplexCategory.delta_zero_comp_delta_two]) ≫
      pullHom (F := spacesEtalePseudofunctor B S hS) (cartesianComparison G hG)
        (σ ≫ A.left.map (edge₂ 0).op) (σ ≫ A.left.map (vertex₂ 1).op)
        (σ ≫ A.left.map (vertex₂ 2).op)
        (by rw [Category.assoc, ← A.left.map_comp, ← op_comp,
          SimplexCategory.delta_one_comp_delta_zero])
        (by rw [Category.assoc, ← A.left.map_comp, ← op_comp,
          SimplexCategory.delta_zero_comp_delta_zero]) =
      pullHom (F := spacesEtalePseudofunctor B S hS) (cartesianComparison G hG)
        (σ ≫ A.left.map (edge₂ 1).op) (σ ≫ A.left.map (vertex₂ 0).op)
        (σ ≫ A.left.map (vertex₂ 2).op)
        (by rw [Category.assoc, ← A.left.map_comp, ← op_comp,
          SimplexCategory.delta_one_comp_delta_one])
        (by rw [Category.assoc, ← A.left.map_comp, ← op_comp,
          SimplexCategory.delta_zero_comp_delta_one]) := by
  have := congrArg (fun t => pullHom (F := spacesEtalePseudofunctor B S hS) t σ
    (σ ≫ A.left.map (vertex₂ 0).op) (σ ≫ A.left.map (vertex₂ 2).op) rfl rfl)
    (cartesianComparison_cocycle G hG)
  simp only [pullHom_comp (gf₂ := σ ≫ A.left.map (vertex₂ 1).op) (hgf₂ := rfl),
    pullHom_pullHom] at this
  exact this

/-- **The comparison isomorphism is the identity over the degenerate edges**, pulled back along
any morphism to `U_0`. -/
theorem cartesianComparison_degenerate_pullHom {W : AlgebraicSpaces B S hS}
    (y : W ⟶ A.left.obj (op ⦋0⦌)) :
    pullHom (F := spacesEtalePseudofunctor B S hS) (cartesianComparison G hG)
        (y ≫ A.left.map (SimplexCategory.σ 0 : ⦋1⦌ ⟶ ⦋0⦌).op) y y
        (by rw [Category.assoc, ← A.left.map_comp, ← op_comp,
          Subsingleton.elim (vertex₁ 1 ≫ _) (𝟙 ⦋0⦌), op_id, A.left.map_id, Category.comp_id])
        (by rw [Category.assoc, ← A.left.map_comp, ← op_comp,
          Subsingleton.elim (vertex₁ 0 ≫ _) (𝟙 ⦋0⦌), op_id, A.left.map_id, Category.comp_id]) =
      𝟙 _ := by
  have := congrArg (fun t => pullHom (F := spacesEtalePseudofunctor B S hS) t y y y
    (by rw [op_id, A.left.map_id, Category.comp_id])
    (by rw [op_id, A.left.map_id, Category.comp_id]))
    (pullHom_cartesianComparison_degenerate G hG)
  simp only [pullHom_pullHom, pullHom_id_eq_id] at this
  exact this

end Cartesian

/-- **The transitions are natural** in the sheaf on `U_étale`. -/
theorem transitionF_naturality {G G' : Sheaf (situation A).totalTopology (Type (u + 1))}
    (w : G ⟶ G') {m n : SimplexCategory} (φ : m ⟶ n) :
    transitionF G φ ≫ (compEquiv n).functor.map (((situation A).restrict n).map w) =
      ((spacesEtalePseudofunctor B S hS).map (A.left.map φ.op).op.toLoc).toFunctor.map
          ((compEquiv m).functor.map (((situation A).restrict m).map w)) ≫
        transitionF G' φ := by
  have h₁ := ((situation A).fiberTransition φ).naturality w
  have h₂ := (transInvIso φ).inv.naturality (((situation A).restrict m).map w)
  dsimp only [Functor.comp_obj, Functor.comp_map] at h₁ h₂
  exact comp_map_comp_map_eq (compEquiv n).functor _ _ _ _ _ _ _ h₁ h₂

/-! ### The comparison isomorphism of an inverse image -/

/-- The inverse of the compositor of the pseudofunctor of spaces-étale inverse images is the
inverse of the compositor of the spaces-étale inverse images. -/
theorem mapComp'_inv_app_eq {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (h : f ≫ g = fg) (M : (spacesEtalePseudofunctor B S hS).obj (.mk (op Z))) :
    ((spacesEtalePseudofunctor B S hS).mapComp' g.op.toLoc f.op.toLoc fg.op.toLoc
        (by rw [← h]; rfl)).inv.toNatTrans.app M =
      (spacesEtaleInverseImage_comp B S hS f g).inv.app M ≫
        (eqToHom (congrArg (fun k => spacesEtaleInverseImage B S hS k) h)).app M := by
  subst h
  exact (congrArg (fun e => e.inv.toNatTrans.app M)
    (mapComp'_eq_mapComp (spacesEtalePseudofunctor B S hS) g.op.toLoc f.op.toLoc)).trans
    (Category.comp_id _).symm

section InverseImage

variable (F : (spacesEtalePseudofunctor B S hS).obj (.mk (op A.right)))

variable (A) in
/-- The augmentation `a_n : U_n → X`, with the base of the augmentation as its target. -/
def augF (n : SimplexCategory) : A.left.obj (op n) ⟶ A.right := A.hom.app (op n)

/-- The augmentation is compatible with the simplicial structure maps: for `φ : m ⟶ n`, the
composite of `A.left.map φ.op` with `a_m` is `a_n`. -/
theorem map_comp_augF {m n : SimplexCategory} (φ : m ⟶ n) :
    A.left.map φ.op ≫ augF A m = augF A n :=
  hom_app_comp (A := A) φ

variable (A) in
/-- The inverse image `a⁻¹F` along the augmentation `a : U → X`, as a sheaf on the total site of
the simplicial-site situation of `U_étale`. -/
def invImage : Sheaf (situation A).totalTopology (Type (u + 1)) :=
  (etaleAugmentationMorphism A).inverseImage.obj F

/-- The sheaf `invImage A F` is the inverse image of `F` along the augmentation morphism. -/
theorem invImage_eq : invImage A F = (etaleAugmentationMorphism A).inverseImage.obj F := rfl

/-- The components of `a⁻¹F` are the inverse images `a_n^* F`, in the fibres of the
pseudofunctor. -/
def inverseImageCompIso (n : SimplexCategory) :
    compF (invImage A F) n ≅
      ((spacesEtalePseudofunctor B S hS).map (augF A n).op.toLoc).toFunctor.obj F :=
  inverseImageComponentIso F n

/-- The identification of the components of `a⁻¹F` with `a_n^* F` is natural in `F`. -/
theorem inverseImageCompIso_naturality {F F' : (spacesEtalePseudofunctor B S hS).obj
      (.mk (op A.right))} (u : F ⟶ F') (n : SimplexCategory) :
    (compEquiv n).functor.map (((situation A).restrict n).map
        ((etaleAugmentationMorphism A).inverseImage.map u)) ≫
        (inverseImageCompIso F' n).hom =
      (inverseImageCompIso F n).hom ≫
        ((spacesEtalePseudofunctor B S hS).map (augF A n).op.toLoc).toFunctor.map u :=
  inverseImageComponentIso_naturality u n

/-- **The transitions of `a⁻¹F` are the compositors of the pseudofunctor.** -/
theorem transitionF_inverseImage {m n : SimplexCategory} (φ : m ⟶ n)
    (h : (augF A m).op.toLoc ≫ (A.left.map φ.op).op.toLoc = (augF A n).op.toLoc) :
    transitionF (invImage A F) φ =
      ((spacesEtalePseudofunctor B S hS).map (A.left.map φ.op).op.toLoc).toFunctor.map
          (inverseImageCompIso F m).hom ≫
        ((spacesEtalePseudofunctor B S hS).mapComp' (augF A m).op.toLoc
          (A.left.map φ.op).op.toLoc (augF A n).op.toLoc h).inv.toNatTrans.app F ≫
        (inverseImageCompIso F n).inv := by
  rw [mapComp'_inv_app_eq _ _ _ (map_comp_augF φ)]
  exact (spacesTransition_inverseImage F φ (map_comp_augF φ)).trans
    (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm)

set_option maxHeartbeats 1000000 in
-- rewriting with large `mapComp'` terms of the étale pseudofunctor
/-- **The comparison isomorphism of `a⁻¹F` is the canonical comparison of the descent datum of
`F` along `a_0`**, under the identification of the degree-zero component with `a_0^* F`. -/
theorem cartesianComparison_inverseImage
    (hF : SimplicialSiteSituation.IsCartesianSheaf (situation A) (invImage A F))
    (h₁ : (augF A ⦋0⦌).op.toLoc ≫ (face₁ A 1).op.toLoc = (augF A ⦋1⦌).op.toLoc)
    (h₀ : (augF A ⦋0⦌).op.toLoc ≫ (face₁ A 0).op.toLoc = (augF A ⦋1⦌).op.toLoc) :
    cartesianComparison (invImage A F) hF =
      ((spacesEtalePseudofunctor B S hS).map (face₁ A 1).op.toLoc).toFunctor.map
          (inverseImageCompIso F ⦋0⦌).hom ≫
        ((spacesEtalePseudofunctor B S hS).mapComp' (augF A ⦋0⦌).op.toLoc
          (face₁ A 1).op.toLoc (augF A ⦋1⦌).op.toLoc h₁).inv.toNatTrans.app F ≫
        ((spacesEtalePseudofunctor B S hS).mapComp' (augF A ⦋0⦌).op.toLoc
          (face₁ A 0).op.toLoc (augF A ⦋1⦌).op.toLoc h₀).hom.toNatTrans.app F ≫
        ((spacesEtalePseudofunctor B S hS).map (face₁ A 0).op.toLoc).toFunctor.map
          (inverseImageCompIso F ⦋0⦌).inv := by
  have hτ1 := transitionF_inverseImage F (vertex₁ 1) h₁
  have hτ0 := transitionF_inverseImage F (vertex₁ 0) h₀
  have hinv : (transitionIso _ hF (vertex₁ 0)).inv = (inverseImageCompIso F ⦋1⦌).hom ≫
      ((spacesEtalePseudofunctor B S hS).mapComp' (augF A ⦋0⦌).op.toLoc
        (face₁ A 0).op.toLoc (augF A ⦋1⦌).op.toLoc h₀).hom.toNatTrans.app F ≫
      ((spacesEtalePseudofunctor B S hS).map (face₁ A 0).op.toLoc).toFunctor.map
        (inverseImageCompIso F ⦋0⦌).inv := by
    apply Iso.inv_ext
    rw [transitionIso_hom, hτ0]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    dsimp only [face₁]
    rw [map_mapComp'_inv_hom_map, Iso.hom_inv_id]
    exact ((spacesEtalePseudofunctor B S hS).map (face₁ A 0).op.toLoc).toFunctor.map_id _
  rw [cartesianComparison, hτ1, hinv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end InverseImage

end AlgebraicGeometry.Space.EtaleComponent
