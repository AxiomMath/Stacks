module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RelativeCupProduct
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardTensorMap

/-!
# The trace map of a right adjoint of pushforward, for abstract tensor–Hom data

Let `F ⊣ G` be an adjunction with `G : C ⥤ D` (a direct image `Rf_*`, with `F = Lf^*`), let
`T_C`, `T_D` be tensor bifunctors compared along `F` by `α : F(K ⊗ L) ⟶ F K ⊗ F L`, and let
`H_C`, `H_D` be internal Hom bifunctors with `- ⊗ P ⊣ H(P, -)` for every `P`. For `L`, `M` in `C`
there is the canonical map

`G H_C(L, M) ⟶ H_D(G L, G M)`,

adjoint to the relative cup product followed by `G` of the evaluation `H_C(L, M) ⊗ L ⟶ M`
(the map of [Stacks, Tag 0B6D]); followed by `H_D(G L, ε)` for a morphism `ε : G A ⟶ K` (the
counit of a right adjoint `a` of `G` at `K`, with `A = a K`) it is the map of [Stacks, Tag 0E57].

The main result is the chain of bijections of the proof of [Stacks, Tag 0E58]: if the
projection formula map `M ⊗ G L ⟶ G(F M ⊗ L)` is invertible and `v ↦ G v ≫ ε` is a bijection
`Hom(F M ⊗ L, A) ≃ Hom(G(F M ⊗ L), K)`, then postcomposition with the trace map is a bijection
`Hom(M, G H_C(L, A)) ≃ Hom(M, H_D(G L, K))`.

## Main definitions

* `CategoryTheory.InternalHomTrace.pushforwardInternalHomMap`: `G H_C(L, M) ⟶ H_D(G L, G M)`.
* `CategoryTheory.InternalHomTrace.pushforwardTrace`: its composite with `H_D(G L, ε)`.

## Main results

* `CategoryTheory.InternalHomTrace.bijective_comp_pushforwardTrace`: the chain of bijections.
* `CategoryTheory.InternalHomTrace.isIso_map_of_bijective_comp`: a morphism inducing bijections on
  morphisms out of a full subcategory becomes invertible under a right adjoint of its inclusion.

## References

* [Stacks Project, Tag 0B6D](https://stacks.math.columbia.edu/tag/0B6D)
* [Stacks Project, Tag 0E57](https://stacks.math.columbia.edu/tag/0E57)
* [Stacks Project, Tag 0E58](https://stacks.math.columbia.edu/tag/0E58)
-/

@[expose] public noncomputable section

namespace CategoryTheory.InternalHomTrace

open Opposite Stacks.Cohomology.RelativeCupProductOnRingedTopoi Stacks.ProjectionFormula
open scoped CategoryTheory.Prod

variable {C D : Type*} [Category C] [Category D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
  (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
  (α : Functor.uncurry.obj TD ⋙ F ⟶ F.prod F ⋙ Functor.uncurry.obj TC)
  (HC : Cᵒᵖ ⥤ C ⥤ C) (HD : Dᵒᵖ ⥤ D ⥤ D)
  (adjC : ∀ P : C, TC.flip.obj P ⊣ HC.obj (op P))
  (adjD : ∀ P : D, TD.flip.obj P ⊣ HD.obj (op P))

/-- **The map `G H_C(L, M) ⟶ H_D(G L, G M)`** of [Stacks, Tag 0B6D]: the adjunct, for
`- ⊗ G L ⊣ H_D(G L, -)`, of the relative cup product `G H_C(L, M) ⊗ G L ⟶ G(H_C(L, M) ⊗ L)`
followed by `G` of the evaluation `H_C(L, M) ⊗ L ⟶ M`. -/
def pushforwardInternalHomMap (L M : C) :
    G.obj ((HC.obj (op L)).obj M) ⟶ (HD.obj (op (G.obj L))).obj (G.obj M) :=
  (adjD (G.obj L)).homEquiv _ _
    (adjunctionCupProduct adj (Functor.uncurry.obj TD) (Functor.uncurry.obj TC) α
        ((HC.obj (op L)).obj M) L ≫
      G.map ((adjC L).counit.app M))

/-- **The trace map `G H_C(L, A) ⟶ H_D(G L, K)`** of [Stacks, Tag 0E57] for a morphism
`ε : G A ⟶ K`: the map of [Stacks, Tag 0B6D] followed by `H_D(G L, ε)`. -/
def pushforwardTrace (L : C) {A : C} {K : D} (ε : G.obj A ⟶ K) :
    G.obj ((HC.obj (op L)).obj A) ⟶ (HD.obj (op (G.obj L))).obj K :=
  pushforwardInternalHomMap adj TC TD α HC HD adjC adjD L A ≫ (HD.obj (op (G.obj L))).map ε

/-- The trace map is the map of [Stacks, Tag 0B6D] followed by `H_D(G L, ε)`. -/
theorem pushforwardTrace_eq (L : C) {A : C} {K : D} (ε : G.obj A ⟶ K) :
    pushforwardTrace adj TC TD α HC HD adjC adjD L ε =
      pushforwardInternalHomMap adj TC TD α HC HD adjC adjD L A ≫
        (HD.obj (op (G.obj L))).map ε :=
  rfl

/-- The adjunct of a morphism `φ : M ⟶ G H_C(L, A)` followed by the trace map: `φ ⊗ G L`, the
relative cup product, `G` of the evaluation, and `ε`. -/
theorem homEquiv_symm_comp_pushforwardTrace (L : C) {A : C} {K : D} (ε : G.obj A ⟶ K)
    {M : D} (φ : M ⟶ G.obj ((HC.obj (op L)).obj A)) :
    ((adjD (G.obj L)).homEquiv M K).symm
        (φ ≫ pushforwardTrace adj TC TD α HC HD adjC adjD L ε) =
      (TD.map φ).app (G.obj L) ≫
        adjunctionCupProduct adj (Functor.uncurry.obj TD) (Functor.uncurry.obj TC) α
          ((HC.obj (op L)).obj A) L ≫ G.map ((adjC L).counit.app A) ≫ ε := by
  rw [pushforwardTrace, pushforwardInternalHomMap, ← Category.assoc,
    ← Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right_symm,
    Equiv.symm_apply_apply]
  simp only [Functor.flip_obj_map, Category.assoc]

/-- **The relative cup product against the projection formula map.** For
`φ : M ⟶ G N`, tensoring `φ` with `G L` and following with the relative cup product is the
projection formula map `M ⊗ G L ⟶ G(F M ⊗ L)` followed by `G` of the adjunct of `φ` tensored
with `L`. -/
theorem cupProduct_comp_eq_projection {M : D} {N : C} (L : C) (φ : M ⟶ G.obj N) :
    (TD.map φ).app (G.obj L) ≫
        adjunctionCupProduct adj (Functor.uncurry.obj TD) (Functor.uncurry.obj TC) α N L =
      adjunctionTensorMapSnd adj (Functor.uncurry.obj TD) (Functor.uncurry.obj TC) α M L ≫
        G.map ((TC.map ((adj.homEquiv M N).symm φ)).app L) := by
  have h1 : (TD.map φ).app (G.obj L) =
      (Functor.uncurry.obj TD).map (φ ×ₘ 𝟙 (G.obj L)) := by
    simp
  have h2 : (TC.map ((adj.homEquiv M N).symm φ)).app L =
      (Functor.uncurry.obj TC).map ((adj.homEquiv M N).symm φ ×ₘ 𝟙 L) := by
    simp
  rw [h1, h2, adjunctionCupProduct, adjunctionTensorMapSnd, Adjunction.homEquiv_unit,
    Adjunction.homEquiv_unit]
  have hη : (Functor.uncurry.obj TD).map (φ ×ₘ 𝟙 (G.obj L)) ≫
      adj.unit.app ((Functor.uncurry.obj TD).obj (G.obj N, G.obj L)) =
        adj.unit.app ((Functor.uncurry.obj TD).obj (M, G.obj L)) ≫
          G.map (F.map ((Functor.uncurry.obj TD).map (φ ×ₘ 𝟙 (G.obj L)))) :=
    adj.unit.naturality _
  have hα : F.map ((Functor.uncurry.obj TD).map (φ ×ₘ 𝟙 (G.obj L))) ≫
      α.app (G.obj N, G.obj L) =
        α.app (M, G.obj L) ≫ (Functor.uncurry.obj TC).map (F.map φ ×ₘ F.map (𝟙 (G.obj L))) :=
    α.naturality _
  rw [← Category.assoc, hη, Category.assoc, Category.assoc, ← G.map_comp, ← G.map_comp]
  congr 2
  rw [← Category.assoc, hα, Category.assoc, Category.assoc, ← Functor.map_comp,
    ← Functor.map_comp]
  congr 2
  apply Prod.ext
  · simp [Adjunction.homEquiv_counit]
  · simp

/-- **The chain of bijections of [Stacks, Tag 0E58].** If the projection formula map
`M ⊗ G L ⟶ G(F M ⊗ L)` is invertible and `v ↦ G v ≫ ε` is a bijection
`Hom(F M ⊗ L, A) ⟶ Hom(G(F M ⊗ L), K)`, then postcomposition with the trace map is a bijection
`Hom(M, G H_C(L, A)) ⟶ Hom(M, H_D(G L, K))`. -/
theorem bijective_comp_pushforwardTrace (L : C) {A : C} {K : D} (ε : G.obj A ⟶ K) (M : D)
    (hproj : IsIso (adjunctionTensorMapSnd adj (Functor.uncurry.obj TD)
      (Functor.uncurry.obj TC) α M L))
    (hε : Function.Bijective fun v : (TC.obj (F.obj M)).obj L ⟶ A => G.map v ≫ ε) :
    Function.Bijective fun φ : M ⟶ G.obj ((HC.obj (op L)).obj A) =>
      φ ≫ pushforwardTrace adj TC TD α HC HD adjC adjD L ε := by
  let p := adjunctionTensorMapSnd adj (Functor.uncurry.obj TD) (Functor.uncurry.obj TC) α M L
  let e₁ := (adj.homEquiv M ((HC.obj (op L)).obj A)).symm
  let e₂ := ((adjC L).homEquiv (F.obj M) A).symm
  let e₃ := Equiv.ofBijective _ hε
  let e₄ : (G.obj ((TC.obj (F.obj M)).obj L) ⟶ K) ≃ ((TD.obj M).obj (G.obj L) ⟶ K) :=
    { toFun := fun u => p ≫ u
      invFun := fun w => inv p ≫ w
      left_inv := fun u => by simp
      right_inv := fun w => by simp }
  let e₅ := (adjD (G.obj L)).homEquiv M K
  have key : (fun φ : M ⟶ G.obj ((HC.obj (op L)).obj A) =>
      φ ≫ pushforwardTrace adj TC TD α HC HD adjC adjD L ε) =
        e₁.trans (e₂.trans (e₃.trans (e₄.trans e₅))) := by
    funext φ
    change φ ≫ _ = (adjD (G.obj L)).homEquiv M K (p ≫ G.map
      (((adjC L).homEquiv (F.obj M) A).symm ((adj.homEquiv M _).symm φ)) ≫ ε)
    refine (Equiv.symm_apply_eq _).1 ?_
    rw [homEquiv_symm_comp_pushforwardTrace, ← Category.assoc,
      cupProduct_comp_eq_projection adj TC TD α L φ, Adjunction.homEquiv_counit,
      Adjunction.homEquiv_counit,
      Functor.flip_obj_map]
    simp only [p, Category.assoc, Functor.map_comp]
  rw [key]
  exact Equiv.bijective _

/-- **A morphism inducing bijections on morphisms out of a full subcategory becomes invertible
under a right adjoint of its inclusion.** Let `R` be right adjoint to the inclusion of a full
subcategory `P` of `D`. If `φ : A ⟶ B` induces a bijection `Hom(ι M, A) ⟶ Hom(ι M, B)` for every
`M` in `P`, then `R φ` is an isomorphism. -/
theorem isIso_map_of_bijective_comp {P : ObjectProperty D} {R : D ⥤ P.FullSubcategory}
    (adjP : P.ι ⊣ R) {A B : D} (φ : A ⟶ B)
    (h : ∀ M : P.FullSubcategory, Function.Bijective fun g : P.ι.obj M ⟶ A => g ≫ φ) :
    IsIso (R.map φ) := by
  refine isIso_of_yoneda_map_bijective _ fun M => ?_
  have key : (fun g : M ⟶ R.obj A => g ≫ R.map φ) =
      (adjP.homEquiv M B) ∘ (fun g : P.ι.obj M ⟶ A => g ≫ φ) ∘ (adjP.homEquiv M A).symm := by
    funext g
    simp only [Function.comp_apply, adjP.homEquiv_naturality_right, Equiv.apply_symm_apply]
  rw [key]
  exact (adjP.homEquiv M B).bijective.comp ((h M).comp (adjP.homEquiv M A).symm.bijective)

/-- **Bijective postcomposition on morphisms out of a class of objects transports along
isomorphisms of arrows.** -/
theorem bijective_comp_of_arrow_iso {P : ObjectProperty D} {A B A' B' : D} {φ : A ⟶ B}
    {φ' : A' ⟶ B'} (h : ∀ M : D, P M → Function.Bijective fun g : M ⟶ A => g ≫ φ)
    (e₁ : A ≅ A') (e₂ : B ≅ B') (w : φ ≫ e₂.hom = e₁.hom ≫ φ') (M : D) (hM : P M) :
    Function.Bijective fun g : M ⟶ A' => g ≫ φ' := by
  have key : (fun g : M ⟶ A' => g ≫ φ') =
      (fun k : M ⟶ B => k ≫ e₂.hom) ∘ (fun g : M ⟶ A => g ≫ φ) ∘
        (fun g : M ⟶ A' => g ≫ e₁.inv) := by
    funext g
    simp [w]
  rw [key]
  exact e₂.homToEquiv.bijective.comp ((h M hM).comp e₁.symm.homToEquiv.bijective)

/-- **Bijective postcomposition on morphisms out of a shift-stable class of objects passes to
shifts.** -/
theorem bijective_comp_shift [HasShift D ℤ] {P : ObjectProperty D} {A B : D} (φ : A ⟶ B)
    (hP : ∀ (n : ℤ) (M : D), P M → P (M⟦n⟧))
    (h : ∀ M : D, P M → Function.Bijective fun g : M ⟶ A => g ≫ φ) (n : ℤ) (M : D)
    (hM : P M) : Function.Bijective fun g : M ⟶ A⟦n⟧ => g ≫ φ⟦n⟧' := by
  let adj := (shiftEquiv' D (-n) n (by simp)).toAdjunction
  have key : (fun g : M ⟶ A⟦n⟧ => g ≫ φ⟦n⟧') =
      (adj.homEquiv M B) ∘ (fun g : M⟦-n⟧ ⟶ A => g ≫ φ) ∘ (adj.homEquiv M A).symm := by
    funext g
    change g ≫ φ⟦n⟧' = adj.homEquiv M B ((adj.homEquiv M A).symm g ≫ φ)
    rw [Adjunction.homEquiv_naturality_right]
    exact congrArg (· ≫ φ⟦n⟧') ((adj.homEquiv M A).apply_symm_apply g).symm
  rw [key]
  exact (adj.homEquiv M B).bijective.comp ((h _ (hP (-n) M hM)).comp
    (adj.homEquiv M A).symm.bijective)

end CategoryTheory.InternalHomTrace

end
