module

public import Mathlib.CategoryTheory.Sites.CoverLifting

/-! # Almost cocontinuous functors

## Main results

* `SheafTheoreticallyEmptySite`: an object of a site is sheaf theoretically empty exactly when
  the empty sieve on it is a covering sieve.
* `IsAlmostCocontinuous`: the notion of an *almost cocontinuous* functor between sites
  (Stacks 04B7).
* `isAlmostCocontinuous_of_isCocontinuous`: a cocontinuous functor is almost cocontinuous.

Tags covered: 04B7.
-/

@[expose] public section

open CategoryTheory

variable {C : Type*} [Category C] {D : Type*} [Category D]

/-- An object `X` of a site `(D, K)` is *sheaf theoretically empty* if the empty sieve on `X`
is a covering sieve for `K`. -/
def SheafTheoreticallyEmptySite
    (K : GrothendieckTopology D) (X : D) : Prop :=
  (⊥ : Sieve X) ∈ K X

/-- **Stacks 04B7.** A functor `u : C ⥤ D` between sites `(C, J)` and `(D, K)` is *almost
cocontinuous* if for every object `U` of `C` and every covering sieve `S` of `u U` there is a
covering sieve `T` of `U` such that each arrow `f : V ⟶ U` in `T` either has `u V` sheaf
theoretically empty, or has `u f` in `S`. -/
@[stacks 04B7]
def IsAlmostCocontinuous (u : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) : Prop :=
  ∀ (U : C) {S : Sieve (u.obj U)}, S ∈ K (u.obj U) →
    ∃ T : Sieve U, T ∈ J U ∧
      ∀ ⦃V : C⦄ (f : V ⟶ U), T f →
        SheafTheoreticallyEmptySite K (u.obj V) ∨ S (u.map f)

/-- A cocontinuous functor between sites is almost cocontinuous: the sieve lifted by
cocontinuity already satisfies the second alternative for every one of its arrows. -/
theorem isAlmostCocontinuous_of_isCocontinuous
    (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsCocontinuous J K] : IsAlmostCocontinuous u J K :=
  fun _ _ hS ↦ ⟨_, Functor.IsCocontinuous.cover_lift hS, fun _ _ hf ↦ Or.inr hf⟩
