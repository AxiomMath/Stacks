module

public import StacksFrontier.AlgebraicTopology.SimplicialObject.CopowerHomology
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriekFreeModuleBaseChange

/-!
# Multiplying by `Δ[n] × K` for a set `K`

Let `P` be a simplicial object of a category with coproducts, let `n` be an object of `Δ` and
`K` a set. The product of `P` with the simplicial set `Δ[n] × K` (with `K` constant) maps to the
product of `P` with `K` by forgetting the simplex coordinate. Since `Δ[n]` is contractible
(Stacks 08QD), every functor inverting homotopy equivalences inverts that map; in particular it
induces an isomorphism on the homology of the Moore complex.

## Main definitions

* `CategoryTheory.SimplicialObject.simplexProd`: the simplicial set `[m] ↦ (m ⟶ n) × K`.
* `CategoryTheory.SimplicialObject.simplexProdProj`: its projection to the constant `K`.

## Main results

* `CategoryTheory.SimplicialObject.isIso_map_copowerMap_simplexProdProj`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u v

namespace CategoryTheory.SimplicialObject

/-- The simplicial set `[m] ↦ (m ⟶ n) × K`. -/
@[simps]
def simplexProd (n : SimplexCategory) (K : Type u) : SimplicialObject (Type u) where
  obj m := (m.unop ⟶ n) × K
  map φ := TypeCat.ofHom fun x => (φ.unop ≫ x.1, x.2)
  map_id _ := by ext ⟨a, b⟩ <;> simp
  map_comp _ _ := by ext ⟨a, b⟩ <;> simp

/-- The projection `Δ[n] × K ⟶ K`. -/
@[simps]
def simplexProdProj (n : SimplexCategory) (K : Type u) :
    simplexProd n K ⟶ (Functor.const SimplexCategoryᵒᵖ).obj K where
  app _ := TypeCat.ofHom fun x => x.2

/-- The universe-lifted standard simplex `[m] ↦ ULift (m ⟶ n)`. -/
abbrev liftedSimplex (n : SimplexCategory) : SimplicialObject (Type u) :=
  ((𝟭 SimplexCategory).op ⋙ yoneda.obj n) ⋙ uliftFunctor.{u}

/-- The lifted standard simplex is contractible. -/
theorem liftedSimplex_contractible (n : SimplexCategory) :
    ∃ f : liftedSimplex.{u} n ⟶ (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1},
      homotopyEquivalences (Type u) f := by
  obtain ⟨f₀, hf₀⟩ := Stacks.ChaoticSite.isPointResolution_id_simplexCategory n
  let e : (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{1} ⋙ uliftFunctor.{u} ≅
      (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1} :=
    Functor.constComp _ _ _ ≪≫
      (Functor.const _).mapIso (Equiv.toIso (Equiv.ulift.trans Equiv.punitEquivPUnit))
  have h := homotopyEquivalences_iso_comp_iso (Iso.refl _) _ e
    (homotopyEquivalences_whiskering_map uliftFunctor.{u} hf₀)
  rw [Iso.refl_hom, Category.id_comp] at h
  exact ⟨_, h⟩

variable {A : Type v} [Category A] [HasCoproducts.{u} A] (P : SimplicialObject A)
  (n : SimplexCategory) (K : Type u)

/-- `∐_{α × β} X ≅ ∐_{α} ∐_{β} X`. -/
def sigmaProdIso (α : Type) (β : Type u) (X : A) :
    (∐ fun _ : α × β => X) ≅ ∐ fun _ : ULift.{u} α => ∐ fun _ : β => X where
  hom := Sigma.desc fun x => Sigma.ι (fun _ : β => X) x.2 ≫
    Sigma.ι (fun _ : ULift.{u} α => ∐ fun _ : β => X) (ULift.up x.1)
  inv := Sigma.desc fun a => Sigma.desc fun k => Sigma.ι (fun _ : α × β => X) (a.down, k)
  hom_inv_id := Sigma.hom_ext _ _ fun _ => by simp
  inv_hom_id := Sigma.hom_ext _ _ fun _ => Sigma.hom_ext _ _ fun _ => by simp

/-- The forward map of `sigmaProdIso` sends the summand at `(a, b)` to the summand `b` of the
summand `a`. -/
@[reassoc (attr := simp)]
lemma ι_sigmaProdIso_hom (α : Type) (β : Type u) (X : A) (x : α × β) :
    Sigma.ι (fun _ : α × β => X) x ≫ (sigmaProdIso α β X).hom =
      Sigma.ι (fun _ : β => X) x.2 ≫
        Sigma.ι (fun _ : ULift.{u} α => ∐ fun _ : β => X) (ULift.up x.1) :=
  Sigma.ι_desc _ _

/-- `P × (Δ[n] × K) ≅ (P × K) × Δ[n]`. -/
def copowerSimplexProdIso :
    P.copower (simplexProd n K) ≅
      (P.copower ((Functor.const SimplexCategoryᵒᵖ).obj K)).copower (liftedSimplex.{u} n) :=
  NatIso.ofComponents (fun m => sigmaProdIso (m.unop ⟶ n) K (P.obj m))
    (fun {m m'} φ => by
      refine Sigma.hom_ext _ _ fun (x : (m.unop ⟶ n) × K) => ?_
      change Sigma.ι (fun _ : (m.unop ⟶ n) × K => P.obj m) x ≫
          Sigma.map' (fun y : (m.unop ⟶ n) × K => (φ.unop ≫ y.1, y.2)) (fun _ => P.map φ) ≫
            (sigmaProdIso (m'.unop ⟶ n) K (P.obj m')).hom =
        Sigma.ι (fun _ : (m.unop ⟶ n) × K => P.obj m) x ≫
          (sigmaProdIso (m.unop ⟶ n) K (P.obj m)).hom ≫
            Sigma.map' (fun a : ULift.{u} (m.unop ⟶ n) => ULift.up (φ.unop ≫ a.down))
              (fun _ => Sigma.map' (fun k : K => k) fun _ => P.map φ)
      rw [Sigma.ι_comp_map'_assoc, ι_sigmaProdIso_hom, ι_sigmaProdIso_hom_assoc,
        Sigma.ι_comp_map', ← Category.assoc (Sigma.ι _ x.2), Sigma.ι_comp_map', Category.assoc])

/-- Under `copowerSimplexProdIso`, the projection `(P × K) × Δ[n] ⟶ P × K` is the map
`P × (Δ[n] × K) ⟶ P × K` induced by `simplexProdProj`. -/
lemma copowerSimplexProdIso_hom_comp_copowerProj :
    (copowerSimplexProdIso P n K).hom ≫
        (P.copower ((Functor.const SimplexCategoryᵒᵖ).obj K)).copowerProj (liftedSimplex.{u} n) =
      Functor.copowerMap (𝟙 P) (simplexProdProj n K) := by
  ext m
  refine Sigma.hom_ext _ _ fun (x : (m.unop ⟶ n) × K) => ?_
  change Sigma.ι (fun _ : (m.unop ⟶ n) × K => P.obj m) x ≫
      (sigmaProdIso (m.unop ⟶ n) K (P.obj m)).hom ≫
        Sigma.desc (fun _ : ULift.{u} (m.unop ⟶ n) => 𝟙 (∐ fun _ : K => P.obj m)) =
    Sigma.ι (fun _ : (m.unop ⟶ n) × K => P.obj m) x ≫
      Sigma.map' (fun y : (m.unop ⟶ n) × K => y.2) (fun _ => 𝟙 (P.obj m))
  rw [ι_sigmaProdIso_hom_assoc, Sigma.ι_desc, Category.comp_id, Sigma.ι_comp_map',
    Category.id_comp]

/-- **Forgetting the simplex coordinate of `P × (Δ[n] × K)` is inverted by every functor which
inverts homotopy equivalences.** -/
theorem isIso_map_copowerMap_simplexProdProj {D : Type*} [Category* D]
    (F : SimplicialObject A ⥤ D) (hF : (homotopyEquivalences A).IsInvertedBy F) :
    IsIso (F.map (Functor.copowerMap (𝟙 P) (simplexProdProj n K))) := by
  have := isIso_map_copowerProj F hF (P.copower ((Functor.const SimplexCategoryᵒᵖ).obj K))
    (liftedSimplex.{u} n) (liftedSimplex_contractible n)
  rw [← copowerSimplexProdIso_hom_comp_copowerProj, F.map_comp]
  infer_instance

end CategoryTheory.SimplicialObject
