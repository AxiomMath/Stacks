module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExtCharacterization.StageSteps

/-!
# The stagewise identification of [Stacks, Tag 0DJV]

For `f : X ⟶ S`, `E` in `D(𝒪_X)` and a perfect `P` in `D(𝒪_X)` with `M(P) = Rf_*R𝓗om(P, E)`
perfect, put `L(P) = M(P)^∨`. This file constructs a unit `u_P : P ⟶ E ⊗^L Lf^*L(P)` such that
composing with it identifies `Hom(L(P), N)` with `Hom(P, E ⊗^L Lf^*N)` whenever the projection
formula map at `(R𝓗om(P, E), N)` is invertible, and proves that `u_P` is natural in `P`. These
are the stages of the homotopy colimit of [Stacks, Tag 0DJU].

## Main definitions

* `stageMap`: The map `Hom(L(P), N) ⟶ Hom(P, E ⊗^L Lf^*N)`.
* `stageUnit`: The unit `u_P : P ⟶ E ⊗^L Lf^*L(P)`.

## Main results

* `bijective_stageUnit_comp`: Composition with `u_P` is a bijection
  `Hom(L(P), N) ≃ Hom(P, E ⊗^L Lf^*N)` when the projection formula map is invertible.
* `stageUnit_comp`: The unit `u_P` is natural in `P`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open AlgebraicGeometry

universe u

attribute [local implicit_reducible] TopCat.Sheaf structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

namespace Stacks.AlgebraicGeometry.RelativeExtCharacterization

open Stacks.SheafOfModules Stacks.AlgebraicGeometry.RelativeDerivedHomDual

attribute [local instance] derivedMonoidalStructure derivedSymmetricStructure

section Stage

variable {X S : Scheme.{u}} (f : X ⟶ S) (E : DStd X)

/-- The functor `N ↦ E ⊗^L Lf^*N`. -/
abbrev tensorPull : DStd S ⥤ DStd X := pullStd f ⋙ (derivedTensor X.sheaf).obj E

/-- `M(P) = Rf_* R𝓗om(P, E)`. -/
abbrev stageM (P : DStd X) : DStd S := (pushStd f).obj (rhom P E)

/-- `L(P) = M(P)^∨`. -/
abbrev stageL (P : DStd X) : DStd S := rhom (stageM f E P) (unitObj S)

/-- The map `M(P') ⟶ M(P)` induced by `k : P ⟶ P'`. -/
abbrev stageMMap {P P' : DStd X} (k : P ⟶ P') : stageM f E P' ⟶ stageM f E P :=
  (pushStd f).map (rhomMapL k E)

/-- The map `L(P) ⟶ L(P')` induced by `k : P ⟶ P'`. -/
abbrev stageLMap {P P' : DStd X} (k : P ⟶ P') : stageL f E P ⟶ stageL f E P' :=
  rhomMapL (stageMMap f E k) (unitObj S)

/-- **The stagewise identification** `Hom(L(P), N) ⟶ Hom(P, E ⊗ Lf^*N)` for a perfect `P` with
`M(P)` perfect. -/
def stageMap (P : DStd X) (hP : IsPerfectSite P) (hM : IsPerfectSite (stageM f E P))
    (N : DStd S) : (stageL f E P ⟶ N) → (P ⟶ (tensorPull f E).obj N) :=
  finalStep f P (E ⊗ (pullStd f).obj N) ∘
    (· ≫ (targetIso P hP E ((pullStd f).obj N)).hom) ∘
    ((adjStd f).homEquiv (unitObj S)
      (((tensorPF X).obj (rhom P E)).obj ((pullStd f).obj N))).symm ∘
    pfStep f (rhom P E) N ∘ baseStep (stageM f E P) hM N

/-- The stagewise identification is bijective when the projection formula map at
`(R𝓗om(P, E), N)` is invertible. -/
theorem stageMap_bijective (P : DStd X) (hP : IsPerfectSite P)
    (hM : IsPerfectSite (stageM f E P)) (N : DStd S) (h : IsIso (pfMap f (rhom P E) N)) :
    Function.Bijective (stageMap f E P hP hM N) :=
  (finalStep_bijective f P (E ⊗ (pullStd f).obj N)).comp
    ((bijective_comp_iso (Y := (pullStd f).obj (unitObj S))
      (targetIso P hP E ((pullStd f).obj N))).comp
    (((adjStd f).homEquiv (unitObj S)
      (((tensorPF X).obj (rhom P E)).obj ((pullStd f).obj N))).symm.bijective.comp
      ((pfStep_bijective f (rhom P E) N h).comp (baseStep_bijective _ hM N))))

/-- The stagewise identification is natural in `N`. -/
theorem stageMap_naturality_right (P : DStd X) (hP : IsPerfectSite P)
    (hM : IsPerfectSite (stageM f E P)) {N N' : DStd S} (g : N ⟶ N') (x : stageL f E P ⟶ N) :
    stageMap f E P hP hM N' (x ≫ g) = stageMap f E P hP hM N x ≫ (tensorPull f E).map g := by
  simp only [stageMap, Function.comp_apply]
  rw [baseStep_naturality_right, pfStep_naturality_right,
    Adjunction.homEquiv_naturality_right_symm, Category.assoc, targetIso_naturality_right,
    ← Category.assoc, finalStep_naturality_right]
  rfl

/-- The stagewise identification is natural in `P`. -/
theorem stageMap_naturality_left {P P' : DStd X} (k : P ⟶ P') (hP : IsPerfectSite P)
    (hP' : IsPerfectSite P') (hM : IsPerfectSite (stageM f E P))
    (hM' : IsPerfectSite (stageM f E P')) (N : DStd S) (x : stageL f E P' ⟶ N) :
    stageMap f E P hP hM N (stageLMap f E k ≫ x) = k ≫ stageMap f E P' hP' hM' N x := by
  simp only [stageMap, Function.comp_apply]
  rw [baseStep_naturality_left _ hM hM', pfStep_naturality_left,
    Adjunction.homEquiv_naturality_right_symm, Category.assoc, targetIso_naturality_left _ hP hP',
    ← Category.assoc, finalStep_naturality_left]

/-- **The stagewise unit** `P ⟶ E ⊗ Lf^*L(P)`. -/
def stageUnit (P : DStd X) (hP : IsPerfectSite P) (hM : IsPerfectSite (stageM f E P)) :
    P ⟶ (tensorPull f E).obj (stageL f E P) :=
  stageMap f E P hP hM _ (𝟙 _)

/-- The stagewise identification sends `x : L(P) ⟶ N` to `u_P ≫ (E ⊗^L Lf^*x)`. -/
theorem stageMap_eq (P : DStd X) (hP : IsPerfectSite P) (hM : IsPerfectSite (stageM f E P))
    (N : DStd S) (x : stageL f E P ⟶ N) :
    stageMap f E P hP hM N x = stageUnit f E P hP hM ≫ (tensorPull f E).map x := by
  rw [stageUnit, ← stageMap_naturality_right, Category.id_comp]

/-- Naturality of the stagewise unit: for `k : P ⟶ P'`, `k ≫ u_{P'} = u_P ≫ (E ⊗^L Lf^*L(k))`. -/
theorem stageUnit_comp {P P' : DStd X} (k : P ⟶ P') (hP : IsPerfectSite P)
    (hP' : IsPerfectSite P') (hM : IsPerfectSite (stageM f E P))
    (hM' : IsPerfectSite (stageM f E P')) :
    k ≫ stageUnit f E P' hP' hM' =
      stageUnit f E P hP hM ≫ (tensorPull f E).map (stageLMap f E k) := by
  rw [stageUnit, ← stageMap_naturality_left _ _ k hP hP' hM hM', Category.comp_id, stageMap_eq]

/-- Composition with the stagewise unit, `x ↦ u_P ≫ (E ⊗^L Lf^*x)`, is a bijection
`Hom(L(P), N) ⟶ Hom(P, E ⊗^L Lf^*N)` when the projection formula map at `(R𝓗om(P, E), N)` is
invertible. -/
theorem bijective_stageUnit_comp (P : DStd X) (hP : IsPerfectSite P)
    (hM : IsPerfectSite (stageM f E P)) (N : DStd S) (h : IsIso (pfMap f (rhom P E) N)) :
    Function.Bijective
      (fun x : stageL f E P ⟶ N ↦ stageUnit f E P hP hM ≫ (tensorPull f E).map x) := by
  convert stageMap_bijective f E P hP hM N h using 1
  funext x
  exact (stageMap_eq f E P hP hM N x).symm

end Stage

end Stacks.AlgebraicGeometry.RelativeExtCharacterization
