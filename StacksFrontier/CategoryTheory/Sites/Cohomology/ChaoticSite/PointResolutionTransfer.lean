module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.CosimplicialResolution
import StacksCore.Tactic.StacksAttribute

/-!
# Transferring the point-resolution hypothesis of Tag 08Q9

The criterion of Tag 08Q9 (`Stacks.ChaoticSite.leftDerivedColimitNatIso`) asks of a cosimplicial
object `U_•` of a small category `C` that every simplicial set `Mor_C(U_•, W)` be homotopy
equivalent to a singleton — `Stacks.ChaoticSite.IsPointResolution`. That hypothesis survives the
move one needs in order to apply the criterion to a small *model* of a large category: reading
`U_•` inside the larger ambient category through a fully faithful functor, and replacing the
result by an isomorphic cosimplicial object there. This file records that, together with the one
fact about homotopy equivalences of simplicial objects it rests on.

## Main results

* `CategoryTheory.SimplicialObject.homotopyEquivalences_iso_comp`: precomposing a homotopy
  equivalence with an isomorphism gives a homotopy equivalence.
* `Stacks.ChaoticSite.yonedaCosimplicialFullyFaithfulIso`: for `G` fully faithful,
  `Mor_C(U_•, W) ≅ Mor_D(G(U_•), G(W))`.
* `Stacks.ChaoticSite.isPointResolution_of_fullyFaithful`: hence `U_•` is a point resolution of
  `C` as soon as `G(U_•)` satisfies the condition of Tag 08Q9 at the objects `G(W)`.

## Implementation notes

The hypothesis of `Stacks.ChaoticSite.isPointResolution_of_fullyFaithful` quantifies over the
objects of the *small* category `C` only, so it is implied by — and strictly weaker than — the
condition of Tag 08Q9 for `G(U_•)` at every object of the ambient category `D`. That is what
makes it usable: a large site may fail the smallness hypothesis of Tag 08Q9 while a small model
of it satisfies the criterion, with the homotopy equivalences supplied once and for all in the
large site.

The ambient category `D` is taken with morphisms in the same universe `u` as the small category
`C`, because `Stacks.ChaoticSite.IsPointResolution` is a statement about simplicial sets valued
in `Type u` and the comparison identifies the sections of two such.

## References

* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 019N](https://stacks.math.columbia.edu/tag/019N)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace CategoryTheory.SimplicialObject

universe v u

variable {C : Type u} [Category.{v} C]

/-- Precomposing a homotopy equivalence of simplicial objects with an isomorphism gives a
homotopy equivalence: a homotopy inverse of `α.hom ≫ f` is `b ≫ α.inv` for `b` a homotopy
inverse of `f`, conjugation by `α` carrying homotopies to homotopies. -/
lemma homotopyEquivalences_iso_comp {U U' V : SimplicialObject C} (α : U ≅ U') {f : U' ⟶ V}
    (hf : homotopyEquivalences C f) : homotopyEquivalences C (α.hom ≫ f) := by
  obtain ⟨b, h₁, h₂⟩ := hf
  refine ⟨b ≫ α.inv, ?_, ?_⟩
  · have e₁ : (α.hom ≫ f) ≫ b ≫ α.inv = α.hom ≫ (f ≫ b) ≫ α.inv := by simp
    have e₂ : α.hom ≫ (𝟙 U' : U' ⟶ U') ≫ α.inv = 𝟙 U := by simp
    rw [e₁, ← e₂]
    exact Relation.EqvGen.map (fun g : U' ⟶ U' => α.hom ≫ g ≫ α.inv)
      (fun _ _ ⟨H⟩ => ⟨(H.postcomp α.inv).precomp α.hom⟩) h₁
  · have e : (b ≫ α.inv) ≫ α.hom ≫ f = b ≫ f := by simp
    rw [e]
    exact h₂

end CategoryTheory.SimplicialObject

namespace Stacks.ChaoticSite

universe u₂ u

variable {C : Type u} [SmallCategory C]

/-- For a fully faithful `G : C ⥤ D`, the simplicial set `Mor_C(U_•, W)` of morphisms from a
cosimplicial object of `C` to an object `W` is the simplicial set `Mor_D(G(U_•), G(W))`: in each
degree the comparison is `G` on morphisms, a bijection by full faithfulness. -/
def yonedaCosimplicialFullyFaithfulIso {D : Type u₂} [Category.{u} D] {G : C ⥤ D}
    (hG : G.FullyFaithful) (U : CosimplicialObject C) (W : C) :
    U.op ⋙ yoneda.obj W ≅ (U ⋙ G).op ⋙ yoneda.obj (G.obj W) :=
  NatIso.ofComponents (fun _ => Equiv.toIso hG.homEquiv) (by intro _ _ _; ext x; simp)

/-- **The point-resolution hypothesis of Tag 08Q9 descends along a fully faithful functor.** Let
`G : C ⥤ D` be fully faithful with `C` small, let `U_•` be a cosimplicial object of `C` and let
`V_•` be a cosimplicial object of `D` isomorphic to `G(U_•)`. If for every object `W` of `D` the
simplicial set `Mor_D(V_•, W)` is homotopy equivalent to a singleton, then `U_•` is a point
resolution of `C`.

This is the step that lets the criterion of Tag 08Q9 be applied to a small model `C` of a large
category `D`: the homotopy equivalences are proved once in `D`, where the cosimplicial object
lives naturally, and the criterion is then applied in `C`, where the smallness hypothesis holds.
Only the objects of the form `G(W)` are used, so the hypothesis is weaker than it looks. -/
lemma isPointResolution_of_fullyFaithful {D : Type u₂} [Category.{u} D] {G : C ⥤ D}
    (hG : G.FullyFaithful) (U : CosimplicialObject C) {V : CosimplicialObject D}
    (α : U ⋙ G ≅ V)
    (h : ∀ W : D, ∃ f : V.op ⋙ yoneda.obj W ⟶
        (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1},
      SimplicialObject.homotopyEquivalences (Type u) f) :
    IsPointResolution U := fun W => by
  obtain ⟨f, hf⟩ := h (G.obj W)
  refine ⟨(yonedaCosimplicialFullyFaithfulIso hG U W ≪≫
    (Functor.isoWhiskerRight (NatIso.op α) (yoneda.obj (G.obj W))).symm).hom ≫ f,
    SimplicialObject.homotopyEquivalences_iso_comp _ hf⟩

end Stacks.ChaoticSite

end
