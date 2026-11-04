module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianTransitionCocycle
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianPair

/-!
# Pairs with a cocycle isomorphism on a simplicial site, for sheaves of abelian groups

Let `S` be a simplicial-site situation. The abelian analogue of
`CategoryTheory.SimplicialSiteSituation.CartesianPair` is a pair `(ℱ, α)` consisting of a sheaf of
abelian groups `ℱ` on the degree-zero component together with an isomorphism
`α : (f_{δ¹₁})⁻¹ℱ ≅ (f_{δ¹₀})⁻¹ℱ` of sheaves of abelian groups on the degree-one component
satisfying the cocycle condition on the degree-two component. The inverse image is the exact
inverse image of abelian sheaves of Stacks 04JC attached to the actual transition morphism of
topoi, `CategoryTheory.abelianTransition`, and the identifications used to state the cocycle
condition are its compositors.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.abelianPasteIso`: the compositor
  `(f_φ)⁻¹(f_ψ)⁻¹ℱ ≅ (f_{ψ ≫ φ})⁻¹ℱ` for sheaves of abelian groups.
* `CategoryTheory.SimplicialSiteSituation.CartesianAbPair`: the category of abelian pairs.
* `CategoryTheory.SimplicialSiteSituation.abelianPairForget`: the functor to pairs of sheaves of
  sets obtained by forgetting the abelian group structure.

## Main results

* `CategoryTheory.SimplicialSiteSituation.abelianPairForget_faithful`: forgetting the group
  structure of a pair is faithful.

## References

* [Stacks Project, Tag 0D7I](https://stacks.math.columbia.edu/tag/0D7I)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 0D9G](https://stacks.math.columbia.edu/tag/0D9G)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sites
open scoped Simplicial

universe u

namespace CategoryTheory

/-- A functor takes the inverse of an isomorphism to the inverse of any isomorphism whose forward
map it takes the forward map to. -/
theorem Functor.map_inv_of_map_hom {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) {X Y : C} (e : X ≅ Y) (e' : F.obj X ≅ F.obj Y) (h : F.map e.hom = e'.hom) :
    F.map e.inv = e'.inv :=
  congrArg Iso.inv (Iso.ext h : F.mapIso e = e')

namespace SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u})

/-- Forgetting the abelian group structure of a sheaf on a component of a simplicial site. -/
abbrev abelianForget (n : SimplexCategory) :
    Sheaf (S.componentTopology n) Ab.{u} ⥤ Sheaf (S.componentTopology n) (Type u) :=
  sheafCompose (S.componentTopology n) (forget Ab.{u})

/-- The abelian inverse image of a morphism is the geometric inverse image of the underlying
morphism of sheaves of sets. -/
theorem abelianForget_map_abelianTransition_map {m n : SimplexCategory} (φ : m ⟶ n)
    {F G : Sheaf (S.componentTopology m) Ab.{u}} (f : F ⟶ G) :
    (S.abelianForget n).map ((abelianTransition S φ).map f) =
      (S.transitionMorphism φ).inverseImage.map ((S.abelianForget m).map f) := rfl

/-! ### The compositor for sheaves of abelian groups -/

/-- The canonical identification `(f_φ)⁻¹(f_ψ)⁻¹ℱ ≅ (f_{ψ ≫ φ})⁻¹ℱ` for sheaves of abelian groups,
given by the compositor of the abelian inverse image. -/
noncomputable def abelianPasteIso {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (F : Sheaf (S.componentTopology l) Ab.{u}) :
    (abelianTransition S φ).obj ((abelianTransition S ψ).obj F) ≅
      (abelianTransition S (ψ ≫ φ)).obj F :=
  ((abelianCompIso S ψ φ).app F).symm

/-- The underlying map of sheaves of sets of the abelian compositor is the compositor. -/
theorem abelianForget_map_abelianPasteIso_hom {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (F : Sheaf (S.componentTopology l) Ab.{u}) :
    (S.abelianForget n).map (S.abelianPasteIso ψ φ F).hom =
      (S.pasteIso ψ φ ((S.abelianForget l).obj F)).hom :=
  (S.abelianForget n).map_inv_of_map_hom ((abelianCompIso S ψ φ).app F)
    ((canonicalCompositionComparison S ψ φ).app ((S.abelianForget l).obj F))
    (forget_map_abelianCompIso_app S ψ φ F)

/-- The underlying map of sheaves of sets of the inverse of the abelian compositor is the inverse
of the compositor. -/
theorem abelianForget_map_abelianPasteIso_inv {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (F : Sheaf (S.componentTopology l) Ab.{u}) :
    (S.abelianForget n).map (S.abelianPasteIso ψ φ F).inv =
      (S.pasteIso ψ φ ((S.abelianForget l).obj F)).inv :=
  (S.abelianForget n).map_inv_of_map_hom _ _ (S.abelianForget_map_abelianPasteIso_hom ψ φ F)

/-- The abelian compositor, written at a chosen factorization of a simplex map. -/
noncomputable def abelianPasteIsoOfEq {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (θ : l ⟶ n) (h : ψ ≫ φ = θ) (F : Sheaf (S.componentTopology l) Ab.{u}) :
    (abelianTransition S φ).obj ((abelianTransition S ψ).obj F) ≅
      (abelianTransition S θ).obj F :=
  S.abelianPasteIso ψ φ F ≪≫
    eqToIso (congrArg (fun k => (abelianTransition S k).obj F) h)

/-- The underlying map of sheaves of sets of the abelian compositor at a factorization is the
compositor at that factorization. -/
theorem abelianForget_map_abelianPasteIsoOfEq_hom {l m n : SimplexCategory} (ψ : l ⟶ m)
    (φ : m ⟶ n) (θ : l ⟶ n) (h : ψ ≫ φ = θ) (F : Sheaf (S.componentTopology l) Ab.{u}) :
    (S.abelianForget n).map (S.abelianPasteIsoOfEq ψ φ θ h F).hom =
      (S.pasteIsoOfEq ψ φ θ h ((S.abelianForget l).obj F)).hom := by
  subst h
  simp only [abelianPasteIsoOfEq, pasteIsoOfEq, Iso.trans_hom, eqToIso.hom, eqToHom_refl,
    Category.comp_id]
  exact S.abelianForget_map_abelianPasteIso_hom ψ φ F

/-- The identification of the inverse images of an abelian sheaf along two factorizations of one
simplex map, built from the abelian compositor at each. -/
noncomputable def abelianGlueOfEq {l m n : SimplexCategory} (ψ ψ' : l ⟶ m) (φ φ' : m ⟶ n)
    (v : l ⟶ n) (h : ψ ≫ φ = v) (h' : ψ' ≫ φ' = v)
    (F : Sheaf (S.componentTopology l) Ab.{u}) :
    (abelianTransition S φ).obj ((abelianTransition S ψ).obj F) ≅
      (abelianTransition S φ').obj ((abelianTransition S ψ').obj F) :=
  S.abelianPasteIsoOfEq ψ φ v h F ≪≫ (S.abelianPasteIsoOfEq ψ' φ' v h' F).symm

/-- The underlying map of sheaves of sets of the identification of two factorizations is the
identification of those factorizations. -/
theorem abelianForget_map_abelianGlueOfEq_hom {l m n : SimplexCategory} (ψ ψ' : l ⟶ m)
    (φ φ' : m ⟶ n) (v : l ⟶ n) (h : ψ ≫ φ = v) (h' : ψ' ≫ φ' = v)
    (F : Sheaf (S.componentTopology l) Ab.{u}) :
    (S.abelianForget n).map (S.abelianGlueOfEq ψ ψ' φ φ' v h h' F).hom =
      (S.glueOfEq ψ ψ' φ φ' v h h' ((S.abelianForget l).obj F)).hom := by
  rw [abelianGlueOfEq, glueOfEq_hom, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.map_comp, S.abelianForget_map_abelianPasteIsoOfEq_hom ψ φ v h F]
  congr 1
  exact (S.abelianForget n).map_inv_of_map_hom _ _
    (S.abelianForget_map_abelianPasteIsoOfEq_hom ψ' φ' v h' F)

/-- The underlying map of sheaves of sets of the inverse of the identification of two
factorizations is the inverse of that identification. -/
theorem abelianForget_map_abelianGlueOfEq_inv {l m n : SimplexCategory} (ψ ψ' : l ⟶ m)
    (φ φ' : m ⟶ n) (v : l ⟶ n) (h : ψ ≫ φ = v) (h' : ψ' ≫ φ' = v)
    (F : Sheaf (S.componentTopology l) Ab.{u}) :
    (S.abelianForget n).map (S.abelianGlueOfEq ψ ψ' φ φ' v h h' F).inv =
      (S.glueOfEq ψ ψ' φ φ' v h h' ((S.abelianForget l).obj F)).inv :=
  (S.abelianForget n).map_inv_of_map_hom _ _
    (S.abelianForget_map_abelianGlueOfEq_hom ψ ψ' φ φ' v h h' F)

/-! ### The three identifications occurring in the cocycle condition -/

/-- The abelian analogue of `CategoryTheory.SimplicialSiteSituation.glueLeft`, along
`δ¹₁ ≫ δ²₂ = δ¹₁ ≫ δ²₁`. -/
noncomputable def abelianGlueLeft (F : Sheaf (S.componentTopology ⦋0⦌) Ab.{u}) :
    (abelianTransition S (SimplexCategory.δ (2 : Fin 3))).obj
        ((abelianTransition S (SimplexCategory.δ (1 : Fin 2))).obj F) ≅
      (abelianTransition S (SimplexCategory.δ (1 : Fin 3))).obj
        ((abelianTransition S (SimplexCategory.δ (1 : Fin 2))).obj F) :=
  S.abelianGlueOfEq _ _ _ _ _ SimplexCategory.delta_one_comp_delta_two
    SimplexCategory.delta_one_comp_delta_one F

/-- The abelian analogue of `CategoryTheory.SimplicialSiteSituation.glueMiddle`, along
`δ¹₀ ≫ δ²₂ = δ¹₁ ≫ δ²₀`. -/
noncomputable def abelianGlueMiddle (F : Sheaf (S.componentTopology ⦋0⦌) Ab.{u}) :
    (abelianTransition S (SimplexCategory.δ (2 : Fin 3))).obj
        ((abelianTransition S (SimplexCategory.δ (0 : Fin 2))).obj F) ≅
      (abelianTransition S (SimplexCategory.δ (0 : Fin 3))).obj
        ((abelianTransition S (SimplexCategory.δ (1 : Fin 2))).obj F) :=
  S.abelianGlueOfEq _ _ _ _ _ SimplexCategory.delta_zero_comp_delta_two
    SimplexCategory.delta_one_comp_delta_zero F

/-- The abelian analogue of `CategoryTheory.SimplicialSiteSituation.glueRight`, along
`δ¹₀ ≫ δ²₀ = δ¹₀ ≫ δ²₁`. -/
noncomputable def abelianGlueRight (F : Sheaf (S.componentTopology ⦋0⦌) Ab.{u}) :
    (abelianTransition S (SimplexCategory.δ (0 : Fin 3))).obj
        ((abelianTransition S (SimplexCategory.δ (0 : Fin 2))).obj F) ≅
      (abelianTransition S (SimplexCategory.δ (1 : Fin 3))).obj
        ((abelianTransition S (SimplexCategory.δ (0 : Fin 2))).obj F) :=
  S.abelianGlueOfEq _ _ _ _ _ SimplexCategory.delta_zero_comp_delta_zero
    SimplexCategory.delta_zero_comp_delta_one F

/-! ### The category of abelian pairs -/

/-- **Stacks 0D7I.** A pair `(ℱ, α)` of sheaves of abelian groups: a sheaf of abelian groups on the
degree-zero component of a simplicial-site situation together with an isomorphism
`α : (f_{δ¹₁})⁻¹ℱ ≅ (f_{δ¹₀})⁻¹ℱ` of sheaves of abelian groups on the degree-one component
satisfying the cocycle condition `(f_{δ²₁})⁻¹α = (f_{δ²₀})⁻¹α ∘ (f_{δ²₂})⁻¹α` on the degree-two
component. -/
structure CartesianAbPair (S : SimplicialSiteSituation.{u}) where
  /-- The sheaf of abelian groups on the degree-zero component. -/
  sheaf : Sheaf (S.componentTopology ⦋0⦌) Ab.{u}
  /-- The comparison isomorphism between the two inverse images to degree one. -/
  iso : (abelianTransition S (SimplexCategory.δ (1 : Fin 2))).obj sheaf ≅
    (abelianTransition S (SimplexCategory.δ (0 : Fin 2))).obj sheaf
  /-- The cocycle condition on the degree-two component. -/
  cocycle :
    (abelianTransition S (SimplexCategory.δ (1 : Fin 3))).map iso.hom =
      (S.abelianGlueLeft sheaf).inv ≫
        (abelianTransition S (SimplexCategory.δ (2 : Fin 3))).map iso.hom ≫
        (S.abelianGlueMiddle sheaf).hom ≫
        (abelianTransition S (SimplexCategory.δ (0 : Fin 3))).map iso.hom ≫
        (S.abelianGlueRight sheaf).hom

namespace CartesianAbPair

/-- A morphism of abelian pairs is a morphism of the degree-zero sheaves commuting with the
comparison isomorphisms. -/
structure Hom (A B : CartesianAbPair S) where
  /-- The morphism of the degree-zero sheaves of abelian groups. -/
  map : A.sheaf ⟶ B.sheaf
  /-- Compatibility with the comparison isomorphisms. -/
  comm : (abelianTransition S (SimplexCategory.δ (1 : Fin 2))).map map ≫ B.iso.hom =
    A.iso.hom ≫ (abelianTransition S (SimplexCategory.δ (0 : Fin 2))).map map

/-- Abelian pairs form a category, with composition that of the morphisms of degree-zero
sheaves. -/
instance : Category (CartesianAbPair S) where
  Hom A B := Hom S A B
  id A := { map := 𝟙 A.sheaf, comm := by simp }
  comp f g :=
    { map := f.map ≫ g.map
      comm := by
        simp only [CategoryTheory.Functor.map_comp, Category.assoc, g.comm,
          reassoc_of% f.comm] }

/-- The identity morphism of abelian pairs is the identity of the degree-zero sheaf. -/
@[simp] theorem id_map (A : CartesianAbPair S) : Hom.map (𝟙 A) = 𝟙 A.sheaf := rfl

/-- Composition of morphisms of abelian pairs composes the morphisms of degree-zero sheaves. -/
@[simp] theorem comp_map {A B C : CartesianAbPair S} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).map = f.map ≫ g.map := rfl

/-- A morphism of abelian pairs is determined by its morphism of degree-zero sheaves. -/
theorem hom_ext {A B : CartesianAbPair S} {f g : A ⟶ B} (h : f.map = g.map) : f = g := by
  obtain ⟨f, hf⟩ := f
  obtain ⟨g, hg⟩ := g
  subst h
  rfl

/-- An isomorphism of degree-zero sheaves compatible with the comparison isomorphisms is an
isomorphism of abelian pairs. -/
def isoMk {A B : CartesianAbPair S} (e : A.sheaf ≅ B.sheaf)
    (h : (abelianTransition S (SimplexCategory.δ (1 : Fin 2))).map e.hom ≫ B.iso.hom =
      A.iso.hom ≫ (abelianTransition S (SimplexCategory.δ (0 : Fin 2))).map e.hom) : A ≅ B where
  hom := ⟨e.hom, h⟩
  inv :=
    ⟨e.inv, by
      rw [← cancel_epi ((abelianTransition S (SimplexCategory.δ (1 : Fin 2))).map e.hom),
        reassoc_of% h]
      simp only [← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp,
        e.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]⟩
  hom_inv_id := hom_ext S (by simp)
  inv_hom_id := hom_ext S (by simp)

end CartesianAbPair

/-! ### Forgetting the group structure of an abelian pair -/

/-- The pair of sheaves of sets underlying an abelian pair. -/
noncomputable def abelianPairUnderlying (A : CartesianAbPair S) : CartesianPair S where
  sheaf := (S.abelianForget ⦋0⦌).obj A.sheaf
  iso := (S.abelianForget ⦋1⦌).mapIso A.iso
  cocycle := by
    have h := congrArg (S.abelianForget ⦋2⦌).map A.cocycle
    simp only [CategoryTheory.Functor.map_comp, abelianGlueLeft, abelianGlueMiddle,
      abelianGlueRight, S.abelianForget_map_abelianGlueOfEq_hom,
      S.abelianForget_map_abelianGlueOfEq_inv,
      S.abelianForget_map_abelianTransition_map] at h
    exact h

/-- The degree-zero sheaf of the pair underlying an abelian pair. -/
theorem abelianPairUnderlying_sheaf (A : CartesianAbPair S) :
    (S.abelianPairUnderlying A).sheaf = (S.abelianForget ⦋0⦌).obj A.sheaf := rfl

/-- The comparison isomorphism of the pair underlying an abelian pair. -/
theorem abelianPairUnderlying_iso_hom (A : CartesianAbPair S) :
    (S.abelianPairUnderlying A).iso.hom = (S.abelianForget ⦋1⦌).map A.iso.hom := rfl

/-- Forgetting the abelian group structure of a pair. -/
noncomputable def abelianPairForget : CartesianAbPair S ⥤ CartesianPair S where
  obj := S.abelianPairUnderlying
  map f :=
    ⟨(S.abelianForget ⦋0⦌).map f.map, by
      have h := congrArg (S.abelianForget ⦋1⦌).map f.comm
      simp only [CategoryTheory.Functor.map_comp,
        S.abelianForget_map_abelianTransition_map] at h
      exact h⟩
  map_id A := CartesianPair.hom_ext S ((S.abelianForget ⦋0⦌).map_id _)
  map_comp f g := CartesianPair.hom_ext S ((S.abelianForget ⦋0⦌).map_comp _ _)

/-- Forgetting the abelian group structure of a pair is faithful. -/
instance abelianPairForget_faithful : S.abelianPairForget.Faithful where
  map_injective {A B} f g h := by
    apply CartesianAbPair.hom_ext S
    apply (S.abelianForget ⦋0⦌).map_injective
    exact congrArg CartesianPair.Hom.map h

end SimplicialSiteSituation

end CategoryTheory

end
