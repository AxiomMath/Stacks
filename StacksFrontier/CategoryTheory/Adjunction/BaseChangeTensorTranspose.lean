module

public import StacksFrontier.CategoryTheory.Adjunction.ConjugateHorizontalOfBaseChange
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardTensorMap

/-!
# The transpose of a base change map followed by a tensor factor

Consider the base change square of `Stacks.CategoryTheory.BaseChange`: left adjoints
`Lf : A ⥤ B`, `Lf' : A' ⥤ B'` with right adjoints `Rf`, `Rf'`, and horizontal left adjoints
`Lg : A ⥤ A'`, `Lg' : B ⥤ B'` with right adjoints `Rg`, `Rg'`. Let `B`, `B'` carry bifunctors
`TB`, `TB'` (tensor products) with a comparison `μ : TB ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ TB'`.

For `E, K : B`, `Kₙ : B'` and `τ : Lg' K ⟶ Kₙ` with adjoint `u : K ⟶ Rg' Kₙ`, the map
`Lg Rf(E ⊗ K) ⟶ Rf' Lg'(E ⊗ K) ⟶ Rf'(Lg' E ⊗ Kₙ)` (base change, then `μ` and `τ`) has as transpose
under `Lg ⊣ Rg` the map `Rf(E ⊗ K) ⟶ Rf(E ⊗ Rg' Kₙ) ⟶ Rf Rg'(Lg' E ⊗ Kₙ) ⟶ Rg Rf'(Lg' E ⊗ Kₙ)`:
`Rf` of `E ⊗ u` and of the projection formula map with the counit in the second factor, then the
conjugate comparison `Rg' ⋙ Rf ⟶ Rf' ⋙ Rg` of the composite right adjoints.

In the application ([Stacks, Tag 0DIM]) `Rf = RΓ(X, -)` over `A`, `Lg = - ⊗^L_A Aₙ`,
`Lg' = Lpₙ^*`, and this identifies the canonical map `RΓ(X, E ⊗ K) ⊗^L_A Aₙ ⟶ RΓ(Xₙ, Lpₙ^*E ⊗ Kₙ)`
with the transpose of the projection `RΓ(X, E ⊗ K) ⟶ RΓ(X, E ⊗ Rpₙ,* Kₙ) = RΓ(Xₙ, Lpₙ^*E ⊗ Kₙ)`.

## Main results

* `Stacks.ProjectionFormula.adjunctionTensorMapSnd_comp_homEquiv`: the projection formula map
  precomposed with `E ⊗ u` is the transpose of `μ` followed by `E ⊗ τ`.
* `Stacks.CategoryTheory.BaseChange.homEquiv_map_comp_tensor`: the transpose of the base change
  map followed by `μ` and `τ`.
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.Prod

namespace Stacks.ProjectionFormula

universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)

/-- **The projection formula map precomposed with a transpose.** For `τ : L K ⟶ G` with transpose
`u : K ⟶ R G`, `A(H, u)` followed by the projection formula map at `(H, G)` is the transpose of
`α` followed by `B(L H, τ)`. -/
lemma adjunctionTensorMapSnd_comp_homEquiv (H K : C) (G : D) (τ : L.obj K ⟶ G) :
    A.map (𝟙 H ×ₘ adj.homEquiv _ _ τ) ≫ adjunctionTensorMapSnd adj A B α H G =
      adj.homEquiv _ _ (α.app (H, K) ≫ B.map (𝟙 (L.obj H) ×ₘ τ)) := by
  rw [adjunctionTensorMapSnd, ← Adjunction.homEquiv_naturality_left]
  congr 1
  have ha := α.naturality (𝟙 H ×ₘ adj.homEquiv _ _ τ)
  change L.map (A.map (𝟙 H ×ₘ adj.homEquiv _ _ τ)) ≫ α.app (H, R.obj G) =
    α.app (H, K) ≫ B.map (L.map (𝟙 H) ×ₘ L.map (adj.homEquiv _ _ τ)) at ha
  rw [← Category.assoc, ha, Category.assoc, ← Functor.map_comp]
  congr 2
  apply Prod.ext <;> simp [Adjunction.homEquiv_unit]

end Stacks.ProjectionFormula

namespace Stacks.CategoryTheory.BaseChange

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} {B : Type u₂} {A' : Type u₃} {B' : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} A'] [Category.{v₄} B']
  {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf' : A' ⥤ B'} {Rf' : B' ⥤ A'}
  {Lg : A ⥤ A'} {Rg : A' ⥤ A} {Lh : B ⥤ B'} {Rh : B' ⥤ B}
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (ag : Lg ⊣ Rg) (ah : Lh ⊣ Rh)
  (e : Lg ⋙ Lf' ≅ Lf ⋙ Lh)
  (TB : B × B ⥤ B) (TB' : B' × B' ⥤ B') (μ : TB ⋙ Lh ⟶ Lh.prod Lh ⋙ TB')

/-- **The transpose of the base change map followed by a tensor factor.** For `E, K : B`,
`Kₙ : B'` and `τ : Lh K ⟶ Kₙ`, the transpose under `Lg ⊣ Rg` of the base change map of the square
`e` at `TB (E, K)` followed by `Rf'` of `μ` and `TB'(Lh E, τ)` is `Rf` of `TB(E, u)` (`u` the
transpose of `τ`) and of the projection formula map, followed by the conjugate comparison
`Rh ⋙ Rf ⟶ Rf' ⋙ Rg` of `e` at `TB'(Lh E, Kₙ)`. -/
theorem homEquiv_map_comp_tensor (E K : B) (Kₙ : B') (τ : Lh.obj K ⟶ Kₙ) :
    ag.homEquiv _ _ (map adjf adjf' e (Iso.refl _) (TB.obj (E, K)) ≫
        Rf'.map (μ.app (E, K) ≫ TB'.map (𝟙 (Lh.obj E) ×ₘ τ))) =
      Rf.map (TB.map (𝟙 E ×ₘ ah.homEquiv _ _ τ) ≫
          ProjectionFormula.adjunctionTensorMapSnd ah TB TB' μ E Kₙ) ≫
        (conjugateEquiv (adjf.comp ah) (ag.comp adjf') e.hom).app (TB'.obj (Lh.obj E, Kₙ)) := by
  apply ((ag.comp adjf').homEquiv _ _).symm.injective
  rw [Adjunction.comp_homEquiv]
  simp only [Equiv.symm_trans_apply, Equiv.symm_apply_apply]
  rw [Adjunction.homEquiv_naturality_right_symm, homEquiv_symm_map,
    Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  simp only [Iso.refl_inv, NatTrans.id_app, Category.id_comp, Functor.map_comp, Category.assoc]
  rw [conjugateEquiv_counit_comp adjf adjf' ag ah e.hom]
  have key {X Y : B} (f : X ⟶ Y) :
      Lf'.map (Lg.map (Rf.map f)) ≫ e.hom.app (Rf.obj Y) ≫ Lh.map (adjf.counit.app Y) =
        e.hom.app (Rf.obj X) ≫ Lh.map (adjf.counit.app X) ≫ Lh.map f := by
    erw [e.hom.naturality_assoc]
    simp only [Functor.comp_map, ← Functor.map_comp]
    exact congrArg _ (congrArg Lh.map (adjf.counit.naturality f))
  rw [reassoc_of% key (ProjectionFormula.adjunctionTensorMapSnd ah TB TB' μ E Kₙ),
    reassoc_of% key (TB.map (𝟙 E ×ₘ ah.homEquiv _ _ τ))]
  congr 2
  rw [← Functor.map_comp_assoc,
    ProjectionFormula.adjunctionTensorMapSnd_comp_homEquiv ah TB TB' μ E K Kₙ τ,
    ← Adjunction.homEquiv_counit, Equiv.symm_apply_apply]

end Stacks.CategoryTheory.BaseChange
