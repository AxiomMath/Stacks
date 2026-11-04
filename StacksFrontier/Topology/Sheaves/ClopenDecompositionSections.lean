module

public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Algebra.Category.Grp.Abelian

/-!
# Sections of a sheaf along a decomposition into disjoint open subsets

Let `X` be a topological space which is the union of pairwise disjoint open subsets `U i`, let
`F` be a sheaf of abelian groups on `X` and let `φ i : F ⟶ G i` be morphisms of sheaves of abelian
groups such that

* `G i` only sees `U i`: restriction `G i (W) ⟶ G i (W ∩ U i)` is bijective for every open `W`;
* `φ i` is bijective on sections over every open `W ⊆ U i`.

Then `F(W) ⟶ ∏ᵢ G i (W)`, `x ↦ (φ i x)ᵢ`, is bijective for every open `W`: the sections of `F` over
`W` are the families of sections over the disjoint pieces `W ∩ U i`, and over these `φ i` is
bijective. In particular `F ⟶ ⨁ᵢ G i` is an isomorphism when the family is finite.

## Main results

* `Stacks.ClopenDecomposition.bijective_sections`: the bijection on sections.
* `Stacks.ClopenDecomposition.isIso_biproductLift`: the isomorphism of sheaves.

## References

* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace CategoryTheory.Limits

/-- **An additive functor to abelian groups carries a finite biproduct to the product**, read on a
morphism into the biproduct: `F(lift g)` is bijective exactly when `x ↦ (F(g j) x)_j` is. -/
theorem bijective_map_biproduct_lift_iff {C : Type*} [Category* C] [Preadditive C]
    [HasFiniteBiproducts C] (F : C ⥤ AddCommGrpCat.{u}) [F.Additive] {J : Type} [Finite J]
    {A : C} (B : J → C) (g : ∀ j, A ⟶ B j) :
    Function.Bijective (F.map (biproduct.lift g)) ↔
      Function.Bijective (fun x : ToType (F.obj A) => fun j => F.map (g j) x) := by
  let Θ := (F.mapBiproduct B).hom ≫ (AddCommGrpCat.biproductIsoPi (fun j => F.obj (B j))).hom
  have hΘ : Function.Bijective Θ := ConcreteCategory.bijective_of_isIso Θ
  have hπ : ∀ (w : ToType (⨁ fun j => F.obj (B j))) (j : J),
      (AddCommGrpCat.biproductIsoPi (fun j => F.obj (B j))).hom w j =
        biproduct.π (fun j => F.obj (B j)) j w := by
    intro w j
    have h := AddCommGrpCat.biproductIsoPi_inv_comp_π_apply (fun j => F.obj (B j)) j
      ((AddCommGrpCat.biproductIsoPi (fun j => F.obj (B j))).hom w)
    rw [Iso.hom_inv_id_apply] at h
    exact h.symm
  have hcomp : ∀ x, Θ (F.map (biproduct.lift g) x) = fun j => F.map (g j) x := by
    intro x
    funext j
    refine (hπ ((F.mapBiproduct B).hom (F.map (biproduct.lift g) x)) j).trans ?_
    rw [Functor.mapBiproduct_hom, ← ConcreteCategory.comp_apply, biproduct.lift_π,
      ← ConcreteCategory.comp_apply, ← F.map_comp, biproduct.lift_π]
  rw [← hΘ.of_comp_iff' (F.map (biproduct.lift g))]
  exact iff_of_eq (congrArg Function.Bijective (funext hcomp))

end CategoryTheory.Limits

namespace Stacks.ClopenDecomposition

variable {X : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} X) {ι : Type}
  (U : ι → Opens X) (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j)) (hcov : (⨆ i, U i) = ⊤)
  (G : ι → TopCat.Sheaf AddCommGrpCat.{u} X) (φ : ∀ i, F ⟶ G i)

include hdisj in
/-- Sections over the intersection of two different pieces are unique: the intersection is
empty. -/
theorem subsingleton_inter (W : Opens X) {i j : ι} (hij : i ≠ j) :
    Subsingleton (ToType (F.obj.obj (op ((W ⊓ U i) ⊓ (W ⊓ U j))))) := by
  have h : (W ⊓ U i) ⊓ (W ⊓ U j) = ⊥ :=
    (Disjoint.mono inf_le_right inf_le_right (hdisj i j hij)).eq_bot
  have hZ := (TopCat.Sheaf.isTerminalOfEqEmpty F h).isZero
  have hz : ∀ a : ToType (F.obj.obj (op ((W ⊓ U i) ⊓ (W ⊓ U j)))), a = 0 := fun a => by
    simpa using ConcreteCategory.congr_hom (hZ.eq_of_src (𝟙 _) 0) a
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

include hcov in
/-- An open `W` is covered by its intersections with the pieces `U i`. -/
theorem le_iSup_inf (W : Opens X) : W ≤ ⨆ i, W ⊓ U i := by
  rw [← inf_iSup_eq, hcov, inf_top_eq]

include hdisj hcov in
/-- **Sections along a decomposition into disjoint open subsets.** If every `G i` only sees `U i`
and `φ i` is bijective over the opens of `U i`, then `F(W) ⟶ ∏ᵢ G i (W)` is bijective. -/
theorem bijective_sections
    (hG : ∀ i (W : Opens X), Function.Bijective
      ((G i).obj.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op))
    (hφ : ∀ i (W : Opens X), W ≤ U i → Function.Bijective ((φ i).hom.app (op W)))
    (W : Opens X) :
    Function.Bijective (fun x : ToType (F.obj.obj (op W)) => fun i => (φ i).hom.app (op W) x) := by
  have hnat : ∀ i (x : ToType (F.obj.obj (op W))),
      (G i).obj.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op ((φ i).hom.app (op W) x) =
        (φ i).hom.app (op (W ⊓ U i)) (F.obj.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op x) :=
    fun i x => (ConcreteCategory.congr_hom ((φ i).hom.naturality
      (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op) x).symm
  constructor
  · intro x y hxy
    refine TopCat.Sheaf.eq_of_locally_eq' F (fun i => W ⊓ U i) W
      (fun i => homOfLE inf_le_left) (le_iSup_inf U hcov W) x y fun i => ?_
    refine (hφ i (W ⊓ U i) inf_le_right).1 ?_
    rw [← hnat, ← hnat]
    exact congrArg _ (congrFun hxy i)
  · intro g
    choose s hs using fun i => (hφ i (W ⊓ U i) inf_le_right).2
      ((G i).obj.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op (g i))
    have hcomp : TopCat.Presheaf.IsCompatible F.obj (fun i => W ⊓ U i) s := by
      intro i j
      by_cases hij : i = j
      · subst hij
        rfl
      · exact (subsingleton_inter F U hdisj W hij).elim _ _
    obtain ⟨x, hx, -⟩ := TopCat.Sheaf.existsUnique_gluing' F (fun i => W ⊓ U i) W
      (fun i => homOfLE inf_le_left) (le_iSup_inf U hcov W) s hcomp
    refine ⟨x, funext fun i => (hG i W).1 ?_⟩
    rw [hnat, hx i, hs i]

/-- Sheaves of abelian groups on a space have finite biproducts: they have finite products and are
preadditive. -/
instance hasFiniteBiproducts_abelianSheaf :
    HasFiniteBiproducts (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Taking sections over an open is additive. -/
instance sheafSections_additive (W : (Opens X)ᵒᵖ) :
    ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj W).Additive where
  map_add := rfl

include hdisj hcov in
/-- **A sheaf decomposed along disjoint open pieces is the biproduct of the pieces**: under the
hypotheses of `Stacks.ClopenDecomposition.bijective_sections`, `F ⟶ ⨁ᵢ G i` is an isomorphism. -/
theorem isIso_biproduct_lift [Finite ι]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (G : ι → Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (φ : ∀ i, F ⟶ G i)
    (hG : ∀ i (W : Opens X), Function.Bijective
      ((G i).obj.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op))
    (hφ : ∀ i (W : Opens X), W ≤ U i → Function.Bijective ((φ i).hom.app (op W))) :
    IsIso (biproduct.lift φ) := by
  have : IsIso ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
      (biproduct.lift φ)) := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun W => ?_
    refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
    exact (CategoryTheory.Limits.bijective_map_biproduct_lift_iff
      ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj W) G φ).2
      (bijective_sections F U hdisj hcov G φ hG hφ W.unop)
  exact isIso_of_reflects_iso _ (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

end Stacks.ClopenDecomposition

end
