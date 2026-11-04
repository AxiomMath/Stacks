module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianPair

/-!
# The pair attached to a cartesian sheaf of sets on a simplicial site

Let `S` be a simplicial-site situation. A cartesian sheaf of sets `F` on its total site has a
degree-zero restriction `F₀` and an invertible canonical transition `(f_{δ¹ₖ})⁻¹F₀ ⟶ F₁` for each
of the two faces `δ¹ₖ`; comparing the two gives an isomorphism
`α : (f_{δ¹₁})⁻¹F₀ ≅ (f_{δ¹₀})⁻¹F₀` satisfying the cocycle condition, so `F` determines a
`CategoryTheory.SimplicialSiteSituation.CartesianPair`. This file builds that functor and shows
it is fully faithful.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.CartesianSheaf`: the category of cartesian sheaves of
  sets on the total site, as a full subcategory.
* `CategoryTheory.SimplicialSiteSituation.cartesianIso`: the comparison `α` of a cartesian
  sheaf.
* `CategoryTheory.SimplicialSiteSituation.cartesianPairFunctor`: the functor to pairs.
* `CategoryTheory.SimplicialSiteSituation.cartesianHomAlong`: the candidate morphism of
  restrictions in degree `n` determined by a morphism of degree-zero restrictions and a vertex.

## Main results

* `CategoryTheory.SimplicialSiteSituation.cartesianIso_cocycle`: the comparison of a cartesian
  sheaf satisfies the cocycle condition of Stacks 0D7I.
* `CategoryTheory.SimplicialSiteSituation.cartesianPairFunctor_faithful` and
  `.cartesianPairFunctor_full`: the functor to pairs is fully faithful.
* `CategoryTheory.SimplicialSiteSituation.cartesianIso_hom_comp` and
  `.cartesianPairFunctor_obj_iso`: the comparison is pinned by its composite with the canonical
  transition for `δ¹₀`, so the functor is not an abstract choice.

## Implementation notes

The cocycle condition is checked by comparing both sides with the composites
`faceSquareTransition` of the canonical transitions along the two faces, which are invertible
because the sheaf is cartesian; the three canonical identifications of the cocycle condition are
carried to those composites by `glueOfEq_comp_fiberTransition`.

Faithfulness is `total_hom_ext` of Stacks 09WF together with the fact that, for a cartesian
sheaf, the transition along the last vertex of `⦋n⦌` is invertible, so the restriction in degree
`n` is determined by the restriction in degree zero. Fullness builds the candidate family
`cartesianHomAlong` along the last vertices; `cartesianHomAlong_vertex_eq` — whose proof is the
only place the cocycle compatibility of a morphism of pairs is used — makes the candidate
independent of the vertex, and `totalHomOfFamily` of Stacks 09WF assembles the family.

Taken with essential surjectivity, which is not formalized here, these results would give the
equivalence of Stacks 0D7I for sheaves of sets; no declaration in this file carries that tag.

## References

* [Stacks Project, Tag 0D7I](https://stacks.math.columbia.edu/tag/0D7I)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u})

/-! ### The pair attached to a cartesian sheaf -/

/-- The category of cartesian sheaves of sets on the total site of a simplicial-site
situation. -/
abbrev CartesianSheaf (S : SimplicialSiteSituation.{u}) :=
  ObjectProperty.FullSubcategory (IsCartesianSheaf S)

/-- For a cartesian sheaf of sets, the comparison isomorphism
`(f_{δ¹₁})⁻¹F₀ ≅ (f_{δ¹₀})⁻¹F₀` obtained from the two canonical transitions to degree one. -/
noncomputable def cartesianIso (F : CartesianSheaf S) :
    (S.transitionMorphism (SimplexCategory.δ (1 : Fin 2))).inverseImage.obj
        ((S.restrict ⦋0⦌).obj F.obj) ≅
      (S.transitionMorphism (SimplexCategory.δ (0 : Fin 2))).inverseImage.obj
        ((S.restrict ⦋0⦌).obj F.obj) := by
  let := F.property (SimplexCategory.δ (1 : Fin 2))
  let := F.property (SimplexCategory.δ (0 : Fin 2))
  exact asIso ((S.fiberTransition (SimplexCategory.δ (1 : Fin 2))).app F.obj) ≪≫
    (asIso ((S.fiberTransition (SimplexCategory.δ (0 : Fin 2))).app F.obj)).symm

/-- The comparison isomorphism of a cartesian sheaf composed with the canonical transition for
`δ¹₀` is the canonical transition for `δ¹₁`. -/
theorem cartesianIso_hom_comp (F : CartesianSheaf S) :
    (S.cartesianIso F).hom ≫ (S.fiberTransition (SimplexCategory.δ (0 : Fin 2))).app F.obj =
      (S.fiberTransition (SimplexCategory.δ (1 : Fin 2))).app F.obj := by
  let := F.property (SimplexCategory.δ (0 : Fin 2))
  simp [cartesianIso]

/-- The composite `(f_{δ²ⱼ})⁻¹(f_{δ¹ᵢ})⁻¹F₀ ⟶ F₂` of the canonical transitions of a sheaf on
the total site along the two faces. -/
noncomputable def faceSquareTransition (F : Sheaf S.totalTopology (Type u)) (i : Fin 2)
    (j : Fin 3) :
    (S.transitionMorphism (SimplexCategory.δ j)).inverseImage.obj
        ((S.transitionMorphism (SimplexCategory.δ i)).inverseImage.obj
          ((S.restrict ⦋0⦌).obj F)) ⟶ (S.restrict ⦋2⦌).obj F :=
  (S.transitionMorphism (SimplexCategory.δ j)).inverseImage.map
      ((S.fiberTransition (SimplexCategory.δ i)).app F) ≫
    (S.fiberTransition (SimplexCategory.δ j)).app F

/-- For a cartesian sheaf the composites of canonical transitions along two faces are
invertible. -/
instance faceSquareTransition_isIso (F : CartesianSheaf S) (i : Fin 2) (j : Fin 3) :
    IsIso (S.faceSquareTransition F.obj i j) := by
  let := F.property (SimplexCategory.δ i)
  let := F.property (SimplexCategory.δ j)
  dsimp only [faceSquareTransition]
  infer_instance

/-- The inverse image to degree two of the comparison isomorphism of a cartesian sheaf,
expressed through the composites of canonical transitions along the faces. -/
theorem map_cartesianIso_hom (F : CartesianSheaf S) (j : Fin 3) :
    (S.transitionMorphism (SimplexCategory.δ j)).inverseImage.map (S.cartesianIso F).hom =
      S.faceSquareTransition F.obj 1 j ≫ inv (S.faceSquareTransition F.obj 0 j) := by
  let := F.property (SimplexCategory.δ (1 : Fin 2))
  let := F.property (SimplexCategory.δ (0 : Fin 2))
  let := F.property (SimplexCategory.δ j)
  simp only [cartesianIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, Functor.map_comp,
    faceSquareTransition, IsIso.inv_comp, Functor.map_inv, Category.assoc,
    IsIso.hom_inv_id_assoc]

/-- Solving for the inverse of an identification that is compatible with two invertible maps to
a common target. -/
theorem iso_inv_eq_of_comp {C : Type*} [Category C] {X Y Z : C} (e : X ≅ Y) (a : X ⟶ Z)
    (b : Y ⟶ Z) [IsIso a] (h : e.hom ≫ b = a) : e.inv = b ≫ inv a := by
  have hb : e.inv ≫ a = b := by rw [← h, Iso.inv_hom_id_assoc]
  rw [← hb, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- Solving for an identification that is compatible with two invertible maps to a common
target. -/
theorem iso_hom_eq_of_comp {C : Type*} [Category C] {X Y Z : C} (e : X ≅ Y) (a : X ⟶ Z)
    (b : Y ⟶ Z) [IsIso b] (h : e.hom ≫ b = a) : e.hom = a ≫ inv b := by
  rw [← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- **Stacks 0D7I.** The comparison isomorphism of a cartesian sheaf satisfies the cocycle
condition. -/
theorem cartesianIso_cocycle (F : CartesianSheaf S) :
    (S.transitionMorphism (SimplexCategory.δ (1 : Fin 3))).inverseImage.map
        (S.cartesianIso F).hom =
      (S.glueLeft ((S.restrict ⦋0⦌).obj F.obj)).inv ≫
        (S.transitionMorphism (SimplexCategory.δ (2 : Fin 3))).inverseImage.map
          (S.cartesianIso F).hom ≫
        (S.glueMiddle ((S.restrict ⦋0⦌).obj F.obj)).hom ≫
        (S.transitionMorphism (SimplexCategory.δ (0 : Fin 3))).inverseImage.map
          (S.cartesianIso F).hom ≫
        (S.glueRight ((S.restrict ⦋0⦌).obj F.obj)).hom := by
  have hL : (S.glueLeft ((S.restrict ⦋0⦌).obj F.obj)).hom ≫
      S.faceSquareTransition F.obj 1 1 = S.faceSquareTransition F.obj 1 2 :=
    S.glueOfEq_comp_fiberTransition F.obj _ _ _ _ _ SimplexCategory.delta_one_comp_delta_two
      SimplexCategory.delta_one_comp_delta_one
  have hM : (S.glueMiddle ((S.restrict ⦋0⦌).obj F.obj)).hom ≫
      S.faceSquareTransition F.obj 1 0 = S.faceSquareTransition F.obj 0 2 :=
    S.glueOfEq_comp_fiberTransition F.obj _ _ _ _ _
      SimplexCategory.delta_zero_comp_delta_two SimplexCategory.delta_one_comp_delta_zero
  have hR : (S.glueRight ((S.restrict ⦋0⦌).obj F.obj)).hom ≫
      S.faceSquareTransition F.obj 0 1 = S.faceSquareTransition F.obj 0 0 :=
    S.glueOfEq_comp_fiberTransition F.obj _ _ _ _ _ SimplexCategory.delta_zero_comp_delta_zero
      SimplexCategory.delta_zero_comp_delta_one
  rw [S.map_cartesianIso_hom F 1, S.map_cartesianIso_hom F 2, S.map_cartesianIso_hom F 0,
    iso_inv_eq_of_comp _ _ _ hL, iso_hom_eq_of_comp _ _ _ hM, iso_hom_eq_of_comp _ _ _ hR]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc]

/-- **Stacks 0D7I.** The pair attached to a cartesian sheaf of sets: its degree-zero restriction
with the comparison isomorphism built from the canonical transitions. -/
noncomputable def pairOfCartesianSheaf (F : CartesianSheaf S) : CartesianPair S where
  sheaf := (S.restrict ⦋0⦌).obj F.obj
  iso := S.cartesianIso F
  cocycle := S.cartesianIso_cocycle F

/-- The comparison isomorphisms of cartesian sheaves are natural. -/
theorem cartesianIso_naturality {F G : CartesianSheaf S} (f : F ⟶ G) :
    (S.transitionMorphism (SimplexCategory.δ (1 : Fin 2))).inverseImage.map
          ((S.restrict ⦋0⦌).map f.hom) ≫ (S.cartesianIso G).hom =
      (S.cartesianIso F).hom ≫
        (S.transitionMorphism (SimplexCategory.δ (0 : Fin 2))).inverseImage.map
          ((S.restrict ⦋0⦌).map f.hom) := by
  let := G.property (SimplexCategory.δ (0 : Fin 2))
  have h₁ := (S.fiberTransition (SimplexCategory.δ (1 : Fin 2))).naturality f.hom
  have h₀ := (S.fiberTransition (SimplexCategory.δ (0 : Fin 2))).naturality f.hom
  dsimp only [Functor.comp_map] at h₁ h₀
  refine (cancel_mono ((S.fiberTransition (SimplexCategory.δ (0 : Fin 2))).app G.obj)).mp ?_
  simp only [Category.assoc]
  rw [S.cartesianIso_hom_comp G, h₁, h₀, reassoc_of% (S.cartesianIso_hom_comp F)]

/-- **Stacks 0D7I.** The functor from cartesian sheaves of sets on the total site to pairs. -/
noncomputable def cartesianPairFunctor : CartesianSheaf S ⥤ CartesianPair S where
  obj := S.pairOfCartesianSheaf
  map f := ⟨(S.restrict ⦋0⦌).map f.hom, S.cartesianIso_naturality f⟩
  map_id F := CartesianPair.hom_ext S ((S.restrict ⦋0⦌).map_id F.obj)
  map_comp f g := CartesianPair.hom_ext S ((S.restrict ⦋0⦌).map_comp f.hom g.hom)

/-- The degree-zero sheaf of the pair attached to a cartesian sheaf is its degree-zero
restriction. -/
theorem cartesianPairFunctor_obj_sheaf (F : CartesianSheaf S) :
    (S.cartesianPairFunctor.obj F).sheaf = (S.restrict ⦋0⦌).obj F.obj := rfl

/-- The comparison isomorphism of the pair attached to a cartesian sheaf is the comparison of
the two canonical transitions to degree one; it is pinned by
`CategoryTheory.SimplicialSiteSituation.cartesianIso_hom_comp`. -/
theorem cartesianPairFunctor_obj_iso (F : CartesianSheaf S) :
    (S.cartesianPairFunctor.obj F).iso = S.cartesianIso F := rfl

/-- The morphism of degree-zero sheaves underlying the image of a morphism of cartesian sheaves
is its degree-zero restriction. -/
theorem cartesianPairFunctor_map_map {F G : CartesianSheaf S} (f : F ⟶ G) :
    (S.cartesianPairFunctor.map f).map = (S.restrict ⦋0⦌).map f.hom := rfl

/-- For a cartesian sheaf, the edge transports of the associated pair are the comparisons
between the canonical transitions along the two vertices of the edge. -/
theorem edgeTransport_cartesianIso (F : CartesianSheaf S) {n : ℕ} (i j : Fin (n + 1))
    (h : i ≤ j) :
    S.edgeTransport ((S.restrict ⦋0⦌).obj F.obj) (S.cartesianIso F) i j h ≫
        (S.fiberTransition
          (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n) j)).app F.obj =
      (S.fiberTransition
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n) i)).app F.obj := by
  have h₁ := S.pasteIsoOfEq_comp_fiberTransition F.obj (SimplexCategory.δ (1 : Fin 2))
    (SimplexCategory.mkOfLe i j h) _ (SimplexCategory.delta_one_comp_mkOfLe n i j h)
  have h₀ := S.pasteIsoOfEq_comp_fiberTransition F.obj (SimplexCategory.δ (0 : Fin 2))
    (SimplexCategory.mkOfLe i j h) _ (SimplexCategory.delta_zero_comp_mkOfLe n i j h)
  refine (cancel_epi (S.pasteIsoOfEq (SimplexCategory.δ (1 : Fin 2))
    (SimplexCategory.mkOfLe i j h) _
    (SimplexCategory.delta_one_comp_mkOfLe n i j h) ((S.restrict ⦋0⦌).obj F.obj)).hom).mp ?_
  rw [reassoc_of% (S.pasteIsoOfEq_comp_edgeTransport ((S.restrict ⦋0⦌).obj F.obj)
      (S.cartesianIso F) i j h), h₀, h₁, ← Functor.map_comp_assoc, S.cartesianIso_hom_comp F]

/-! ### Fullness and faithfulness -/

/-- For a cartesian sheaf, the candidate morphism of restrictions in degree `n` determined by a
morphism of degree-zero restrictions and a choice of vertex `⦋0⦌ ⟶ n`. -/
noncomputable def cartesianHomAlong {F G : CartesianSheaf S}
    (a : (S.restrict ⦋0⦌).obj F.obj ⟶ (S.restrict ⦋0⦌).obj G.obj) {n : SimplexCategory}
    (ψ : ⦋0⦌ ⟶ n) : (S.restrict n).obj F.obj ⟶ (S.restrict n).obj G.obj := by
  let := F.property ψ
  exact inv ((S.fiberTransition ψ).app F.obj) ≫
    (S.transitionMorphism ψ).inverseImage.map a ≫ (S.fiberTransition ψ).app G.obj

/-- At the identity vertex of `⦋0⦌` the candidate morphism is the given one. -/
theorem cartesianHomAlong_id {F G : CartesianSheaf S}
    (a : (S.restrict ⦋0⦌).obj F.obj ⟶ (S.restrict ⦋0⦌).obj G.obj) :
    S.cartesianHomAlong (F := F) (G := G) a (𝟙 ⦋0⦌) = a := by
  let := F.property (𝟙 ⦋0⦌)
  refine (cancel_epi ((S.fiberTransition (𝟙 ⦋0⦌)).app F.obj)).mp ?_
  simp only [cartesianHomAlong, IsIso.hom_inv_id_assoc]
  rw [fiberTransition_id, fiberTransition_id]
  exact (canonicalIdentityComparison S ⦋0⦌).hom.naturality a

/-- The candidate morphisms attached to a vertex and to its image under a simplex map are
compatible with the canonical transitions. -/
theorem cartesianHomAlong_comp {F G : CartesianSheaf S}
    (a : (S.restrict ⦋0⦌).obj F.obj ⟶ (S.restrict ⦋0⦌).obj G.obj) {m n : SimplexCategory}
    (ψ : ⦋0⦌ ⟶ m) (φ : m ⟶ n) :
    (S.fiberTransition φ).app F.obj ≫ S.cartesianHomAlong (F := F) (G := G) a (ψ ≫ φ) =
      (S.transitionMorphism φ).inverseImage.map
          (S.cartesianHomAlong (F := F) (G := G) a ψ) ≫ (S.fiberTransition φ).app G.obj := by
  let (p q : SimplexCategory) (χ : p ⟶ q) : IsIso ((S.fiberTransition χ).app F.obj) :=
    F.property χ
  refine (cancel_epi ((S.transitionMorphism φ).inverseImage.map
    ((S.fiberTransition ψ).app F.obj))).mp ?_
  simp only [cartesianHomAlong, Functor.map_comp, Functor.map_inv, Category.assoc,
    IsIso.hom_inv_id_assoc]
  rw [← reassoc_of% (S.pasteIso_comp_fiberTransition F.obj ψ φ)]
  simp only [IsIso.hom_inv_id_assoc]
  rw [← reassoc_of% (S.pasteIso_naturality ψ φ a), S.pasteIso_comp_fiberTransition G.obj ψ φ]

/-- The candidate morphisms attached to two vertices of a simplex joined by an edge agree, for
the morphism of degree-zero restrictions underlying a morphism of the associated pairs. -/
theorem cartesianHomAlong_vertex_eq {F G : CartesianSheaf S}
    (b : (S.restrict ⦋0⦌).obj F.obj ⟶ (S.restrict ⦋0⦌).obj G.obj)
    (hb : (S.transitionMorphism (SimplexCategory.δ (1 : Fin 2))).inverseImage.map b ≫
        (S.cartesianIso G).hom =
      (S.cartesianIso F).hom ≫
        (S.transitionMorphism (SimplexCategory.δ (0 : Fin 2))).inverseImage.map b) {n : ℕ}
    (i j : Fin (n + 1)) (h : i ≤ j) :
    S.cartesianHomAlong (F := F) (G := G) b
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n) i) =
      S.cartesianHomAlong (F := F) (G := G) b
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n) j) := by
  let (p q : SimplexCategory) (χ : p ⟶ q) : IsIso ((S.fiberTransition χ).app F.obj) :=
    F.property χ
  have hn : (S.transitionMorphism
          (SimplexCategory.const ⦋0⦌ ⦋n⦌ i)).inverseImage.map b ≫
        S.edgeTransport ((S.restrict ⦋0⦌).obj G.obj) (S.cartesianIso G) i j h =
      S.edgeTransport ((S.restrict ⦋0⦌).obj F.obj) (S.cartesianIso F) i j h ≫
        (S.transitionMorphism
          (SimplexCategory.const ⦋0⦌ ⦋n⦌ j)).inverseImage.map b :=
    S.edgeTransport_naturality
      (⟨b, hb⟩ : S.pairOfCartesianSheaf F ⟶ S.pairOfCartesianSheaf G) i j h
  refine (cancel_epi ((S.fiberTransition
    (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk n) i)).app F.obj)).mp ?_
  simp only [cartesianHomAlong, IsIso.hom_inv_id_assoc]
  rw [← S.edgeTransport_cartesianIso F i j h, ← S.edgeTransport_cartesianIso G i j h]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, hn, Category.assoc]

/-- The candidate morphisms attached to the last vertices are compatible with the canonical
transitions. -/
theorem cartesianHomAlong_naturality {F G : CartesianSheaf S}
    (b : (S.restrict ⦋0⦌).obj F.obj ⟶ (S.restrict ⦋0⦌).obj G.obj)
    (hb : (S.transitionMorphism (SimplexCategory.δ (1 : Fin 2))).inverseImage.map b ≫
        (S.cartesianIso G).hom =
      (S.cartesianIso F).hom ≫
        (S.transitionMorphism (SimplexCategory.δ (0 : Fin 2))).inverseImage.map b)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.transitionMorphism φ).inverseImage.map
          (S.cartesianHomAlong (F := F) (G := G) b
            (SimplexCategory.const (SimplexCategory.mk 0) m (Fin.last m.len))) ≫
        (S.fiberTransition φ).app G.obj =
      (S.fiberTransition φ).app F.obj ≫
        S.cartesianHomAlong (F := F) (G := G) b
          (SimplexCategory.const (SimplexCategory.mk 0) n (Fin.last n.len)) := by
  rw [show SimplexCategory.const ⦋0⦌ n (Fin.last n.len) =
    SimplexCategory.const ⦋0⦌ ⦋n.len⦌ (Fin.last n.len) from rfl]
  rw [← S.cartesianHomAlong_vertex_eq b hb (φ.toOrderHom (Fin.last m.len)) (Fin.last n.len)
    (Fin.le_last _)]
  rw [show SimplexCategory.const ⦋0⦌ ⦋n.len⦌ (φ.toOrderHom (Fin.last m.len)) =
    SimplexCategory.const ⦋0⦌ m (Fin.last m.len) ≫ φ from (SimplexCategory.vertexMap_comp φ _).symm]
  exact (S.cartesianHomAlong_comp b (SimplexCategory.const ⦋0⦌ m (Fin.last m.len)) φ).symm

/-- **Stacks 0D7I.** The functor to pairs is faithful. -/
instance cartesianPairFunctor_faithful : S.cartesianPairFunctor.Faithful where
  map_injective {F G} {f g} hfg := by
    have h0 : (S.restrict ⦋0⦌).map f.hom = (S.restrict ⦋0⦌).map g.hom :=
      congrArg CartesianPair.Hom.map hfg
    refine ObjectProperty.hom_ext _ (S.total_hom_ext fun n => ?_)
    let := F.property (SimplexCategory.const (SimplexCategory.mk 0) n (Fin.last n.len))
    have hf := (S.fiberTransition
      (SimplexCategory.const ⦋0⦌ n (Fin.last n.len))).naturality f.hom
    have hg := (S.fiberTransition
      (SimplexCategory.const ⦋0⦌ n (Fin.last n.len))).naturality g.hom
    dsimp only [Functor.comp_map] at hf hg
    refine (cancel_epi ((S.fiberTransition
      (SimplexCategory.const (SimplexCategory.mk 0) n (Fin.last n.len))).app F.obj)).mp ?_
    rw [← hf, ← hg, h0]

/-- **Stacks 0D7I.** The functor to pairs is full. -/
instance cartesianPairFunctor_full : S.cartesianPairFunctor.Full where
  map_surjective {F G} a := by
    have hb : (S.transitionMorphism (SimplexCategory.δ (1 : Fin 2))).inverseImage.map a.map ≫
          (S.cartesianIso G).hom =
        (S.cartesianIso F).hom ≫
          (S.transitionMorphism (SimplexCategory.δ (0 : Fin 2))).inverseImage.map a.map :=
      a.comm
    have hβ : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
        S.cartesianHomAlong (F := F) (G := G) a.map
            (SimplexCategory.const ⦋0⦌ m (Fin.last m.len)) ≫
            (S.restrictTransition φ).app G.obj =
          (S.restrictTransition φ).app F.obj ≫ (S.transitionMorphism φ).pushforward.map
            (S.cartesianHomAlong (F := F) (G := G) a.map
              (SimplexCategory.const ⦋0⦌ n (Fin.last n.len))) := by
      intro m n φ
      rw [← fiberTransition_adj, ← fiberTransition_adj]
      exact Adjunction.homEquiv_naturality_left_square _ _ _ _ _
        (S.cartesianHomAlong_naturality a.map hb φ)
    refine ⟨⟨S.totalHomOfFamily
      (fun n => S.cartesianHomAlong (F := F) (G := G) a.map
        (SimplexCategory.const ⦋0⦌ n (Fin.last n.len)))
      hβ⟩, CartesianPair.hom_ext S ?_⟩
    rw [cartesianPairFunctor_map_map, S.restrict_map_totalHomOfFamily _ hβ ⦋0⦌,
      show SimplexCategory.const ⦋0⦌ ⦋0⦌ (Fin.last ⦋0⦌.len) = 𝟙 ⦋0⦌ from by decide]
    exact S.cartesianHomAlong_id a.map

end CategoryTheory.SimplicialSiteSituation

end
