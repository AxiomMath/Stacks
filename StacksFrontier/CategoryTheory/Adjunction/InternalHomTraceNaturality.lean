module

public import StacksFrontier.CategoryTheory.Adjunction.InternalHomTrace

/-!
# Naturality of the trace map in its source variable

In the setting of `StacksFrontier/CategoryTheory/Adjunction/InternalHomTrace.lean` (an adjunction
`F ⊣ G`, tensor bifunctors compared along `F`, internal Hom bifunctors with `- ⊗ P ⊣ H(P, -)`),
suppose the hom-set bijections of `- ⊗ P ⊣ H(P, -)` are dinatural in `P`: the transpose of
`θ ≫ H(u, M)` is `A ⊗ u` followed by the transpose of `θ`. Then the evaluation morphisms
`H(P, M) ⊗ P ⟶ M` are dinatural in `P`, and the trace map `G H_C(L, A) ⟶ H_D(G L, K)` of
[Stacks, Tag 0E57] is natural in `L`.

## Main results

* `CategoryTheory.InternalHomTrace.counit_dinaturality`: dinaturality of the evaluation.
* `CategoryTheory.InternalHomTrace.pushforwardTrace_naturality_source`: naturality of the trace
  map in `L`.

## References

* [Stacks Project, Tag 0E57](https://stacks.math.columbia.edu/tag/0E57)
-/

@[expose] public noncomputable section

namespace CategoryTheory.InternalHomTrace

open Opposite Stacks.Cohomology.RelativeCupProductOnRingedTopoi
open scoped CategoryTheory.Prod

variable {C D : Type*} [Category C] [Category D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
  (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
  (α : Functor.uncurry.obj TD ⋙ F ⟶ F.prod F ⋙ Functor.uncurry.obj TC)
  (HC : Cᵒᵖ ⥤ C ⥤ C) (HD : Dᵒᵖ ⥤ D ⥤ D)
  (adjC : ∀ P : C, TC.flip.obj P ⊣ HC.obj (op P))
  (adjD : ∀ P : D, TD.flip.obj P ⊣ HD.obj (op P))

/-- **The evaluation morphisms are dinatural in the internal Hom source.** If the hom-set
bijections of `- ⊗ P ⊣ H(P, -)` are dinatural in `P`, then for `u : P' ⟶ P` the two morphisms
`H(P, M) ⊗ P' ⟶ M` obtained from `H(u, M) ⊗ P'` and `H(P, M) ⊗ u` followed by evaluation
agree. -/
theorem counit_dinaturality
    (hdin : ∀ {P' P : C} (u : P' ⟶ P) {A M : C} (θ : A ⟶ (HC.obj (op P)).obj M),
      ((adjC P').homEquiv A M).symm (θ ≫ (HC.map u.op).app M) =
        (TC.obj A).map u ≫ ((adjC P).homEquiv A M).symm θ)
    {P' P : C} (u : P' ⟶ P) (M : C) :
    (TC.map ((HC.map u.op).app M)).app P' ≫ (adjC P').counit.app M =
      (TC.obj ((HC.obj (op P)).obj M)).map u ≫ (adjC P).counit.app M := by
  have h := hdin u (𝟙 ((HC.obj (op P)).obj M))
  rw [Category.id_comp, Adjunction.homEquiv_counit, Adjunction.homEquiv_counit] at h
  simpa using h

/-- The relative cup product is natural in its first object. -/
theorem adjunctionCupProduct_naturality_left {N N' : C} (x : N ⟶ N') (L : C) :
    (TD.map (G.map x)).app (G.obj L) ≫
        adjunctionCupProduct adj (Functor.uncurry.obj TD) (Functor.uncurry.obj TC) α N' L =
      adjunctionCupProduct adj (Functor.uncurry.obj TD) (Functor.uncurry.obj TC) α N L ≫
        G.map ((TC.map x).app L) := by
  simpa using adjunctionCupProduct_natural adj (Functor.uncurry.obj TD) (Functor.uncurry.obj TC) α
    x (𝟙 L)

/-- The relative cup product is natural in its second object. -/
theorem adjunctionCupProduct_naturality_right (N : C) {L L' : C} (y : L ⟶ L') :
    (TD.obj (G.obj N)).map (G.map y) ≫
        adjunctionCupProduct adj (Functor.uncurry.obj TD) (Functor.uncurry.obj TC) α N L' =
      adjunctionCupProduct adj (Functor.uncurry.obj TD) (Functor.uncurry.obj TC) α N L ≫
        G.map ((TC.obj N).map y) := by
  simpa using adjunctionCupProduct_natural adj (Functor.uncurry.obj TD) (Functor.uncurry.obj TC) α
    (𝟙 N) y

/-- **The trace map is natural in its source.** If the hom-set bijections of both families
`- ⊗ P ⊣ H(P, -)` are dinatural in `P`, then for `u : L' ⟶ L` the trace maps
`G H_C(L, A) ⟶ H_D(G L, K)` and `G H_C(L', A) ⟶ H_D(G L', K)` are intertwined by `G H_C(u, A)`
and `H_D(G u, K)`. -/
theorem pushforwardTrace_naturality_source
    (hdinC : ∀ {P' P : C} (u : P' ⟶ P) {A M : C} (θ : A ⟶ (HC.obj (op P)).obj M),
      ((adjC P').homEquiv A M).symm (θ ≫ (HC.map u.op).app M) =
        (TC.obj A).map u ≫ ((adjC P).homEquiv A M).symm θ)
    (hdinD : ∀ {P' P : D} (u : P' ⟶ P) {A M : D} (θ : A ⟶ (HD.obj (op P)).obj M),
      ((adjD P').homEquiv A M).symm (θ ≫ (HD.map u.op).app M) =
        (TD.obj A).map u ≫ ((adjD P).homEquiv A M).symm θ)
    {L' L : C} (u : L' ⟶ L) {A : C} {K : D} (ε : G.obj A ⟶ K) :
    G.map ((HC.map u.op).app A) ≫ pushforwardTrace adj TC TD α HC HD adjC adjD L' ε =
      pushforwardTrace adj TC TD α HC HD adjC adjD L ε ≫ (HD.map (G.map u).op).app K := by
  apply ((adjD (G.obj L')).homEquiv _ _).symm.injective
  rw [homEquiv_symm_comp_pushforwardTrace, hdinD,
    ← Category.id_comp (pushforwardTrace adj TC TD α HC HD adjC adjD L ε),
    homEquiv_symm_comp_pushforwardTrace, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp,
    reassoc_of% (adjunctionCupProduct_naturality_left adj TC TD α ((HC.map u.op).app A) L'),
    reassoc_of% (adjunctionCupProduct_naturality_right adj TC TD α ((HC.obj (op L)).obj A) u),
    ← G.map_comp_assoc, ← G.map_comp_assoc, counit_dinaturality TC HC adjC hdinC u A]

end CategoryTheory.InternalHomTrace

end
