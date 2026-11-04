module

public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Algebra.Category.Grp.Basic

/-!
# Surjectivity of a comparison map from a cover by graphs

Let `L : D ⥤ C` and `R : C ⥤ D` be functors, let `G` be a separated presheaf of abelian groups
on a site `(D, J)`, and let `θ : H ⟶ R.op ⋙ G` be a map from a presheaf `H` on `C`. Suppose each
object `W` of `D` carries a morphism `graph W : W ⟶ R.obj (L.obj W)` and a map
`η W : G(W) ⟶ H(L.obj W)`, such that `θ` applied to `η W s` restricts along `graph W` to `s`.

Then `θ` is surjective at any object `Q` of `C` which is covered by finitely many graphs: if
there are `W i` and isomorphisms `L.obj (W i) ≅ Q` whose graphs generate a covering sieve of
`R.obj Q`, and if the image of `η (W i) s` restricts to zero along every *other* graph, then
every section of `G` over `R.obj Q` is `θ` of the sum of the sections `η (W i)` of its
restrictions to the `i`-th graph.

## Main results

* `CategoryTheory.Presheaf.app_sum_eq_of_graphCover`: the explicit preimage of a section at an
  object covered by finitely many graphs.
* `CategoryTheory.Presheaf.surjective_app_of_graphCover`: surjectivity of the comparison map at
  an object covered by finitely many graphs.

## References

* [Stacks Project, Tag 03S7](https://stacks.math.columbia.edu/tag/03S7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v v₁ v₂ u₁ u₂

namespace CategoryTheory.Presheaf

/-- **The explicit preimage over a cover by finitely many graphs.** A section `s` of `G` over
`R.obj Q` is the image under `θ` of the sum over `i` of the sections `η (W i)` of its
restrictions to the `i`-th graph, transported to `Q`. -/
public theorem app_sum_eq_of_graphCover
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (L : D ⥤ C) (R : C ⥤ D)
    (J : GrothendieckTopology D) (G : Dᵒᵖ ⥤ AddCommGrpCat.{v})
    (hG : Presheaf.IsSeparated J G)
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{v}) (θ : H ⟶ R.op ⋙ G)
    (η : ∀ W, G.obj (Opposite.op W) ⟶ H.obj (Opposite.op (L.obj W)))
    (graph : ∀ W, W ⟶ R.obj (L.obj W))
    (hdiag : ∀ W s, G.map (graph W).op (θ.app _ (η W s)) = s)
    {Q : C} {ι : Type*} [Fintype ι] (W : ι → D) (e : ∀ i, L.obj (W i) ≅ Q)
    (hcov : Sieve.generate (Presieve.ofArrows W
      (fun i => graph (W i) ≫ R.map (e i).hom)) ∈ J (R.obj Q))
    (hoff : ∀ i j, i ≠ j → ∀ s,
      G.map ((graph (W j) ≫ R.map (e j).hom) ≫ R.map (e i).inv).op
        (θ.app _ (η (W i) s)) = 0)
    (s : G.obj (Opposite.op (R.obj Q))) :
    θ.app (Opposite.op Q) (∑ i, H.map (e i).inv.op
      (η (W i) (G.map (graph (W i) ≫ R.map (e i).hom).op s))) = s := by
  classical
  let g i := graph (W i) ≫ R.map (e i).hom
  let t i := G.map (g i).op s
  let x i := H.map (e i).inv.op (η (W i) (t i))
  show θ.app (Opposite.op Q) (∑ i, x i) = s
  rw [map_sum]
  apply hG (R.obj Q) _ hcov
  intro T f hf
  obtain ⟨Z, a, b, hb, hab⟩ := hf
  obtain ⟨j⟩ := hb
  have hres : G.map (g j).op (∑ i, θ.app (Opposite.op Q) (x i)) =
      G.map (g j).op s := by
    have key : ∀ i, G.map (g j).op (θ.app (Opposite.op Q) (x i)) =
        G.map (g j ≫ R.map (e i).inv).op (θ.app _ (η (W i) (t i))) := fun i ↦ by
      change G.map (g j).op ((H.map (e i).inv.op ≫ θ.app _) (η (W i) (t i))) = _
      rw [θ.naturality]
      exact (Functor.map_comp_apply ..).symm
    rw [map_sum, Finset.sum_eq_single j]
    · rw [key]
      change _ = t j
      simpa [g, ← R.map_comp] using hdiag (W j) (t j)
    · intro i hi hij
      rw [key]
      exact hoff i j hij (t i)
    · simp
  rw [← hab, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hres]

/-- A section of `G` over `R.obj Q` is the image under `θ` of a finite sum of sections coming
from the graphs covering `R.obj Q`, so `θ` is surjective at `Q`. -/
public theorem surjective_app_of_graphCover
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (L : D ⥤ C) (R : C ⥤ D)
    (J : GrothendieckTopology D) (G : Dᵒᵖ ⥤ AddCommGrpCat.{v})
    (hG : Presheaf.IsSeparated J G)
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{v}) (θ : H ⟶ R.op ⋙ G)
    (η : ∀ W, G.obj (Opposite.op W) ⟶ H.obj (Opposite.op (L.obj W)))
    (graph : ∀ W, W ⟶ R.obj (L.obj W))
    (hdiag : ∀ W s, G.map (graph W).op (θ.app _ (η W s)) = s)
    {Q : C} {ι : Type*} [Finite ι] (W : ι → D) (e : ∀ i, L.obj (W i) ≅ Q)
    (hcov : Sieve.generate (Presieve.ofArrows W
      (fun i => graph (W i) ≫ R.map (e i).hom)) ∈ J (R.obj Q))
    (hoff : ∀ i j, i ≠ j → ∀ s,
      G.map ((graph (W j) ≫ R.map (e j).hom) ≫ R.map (e i).inv).op
        (θ.app _ (η (W i) s)) = 0) :
    Function.Surjective (θ.app (Opposite.op Q)) := by
  have := Fintype.ofFinite ι
  exact fun s ↦ ⟨_, app_sum_eq_of_graphCover L R J G hG H θ η graph hdiag W e hcov hoff s⟩

end CategoryTheory.Presheaf

end
