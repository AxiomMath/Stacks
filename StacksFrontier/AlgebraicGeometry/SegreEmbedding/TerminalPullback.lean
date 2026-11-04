module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Base change of a morphism of products over the terminal object

Let `C` be a category with a terminal object and all pullbacks, and read `X × Y` for
`pullback (terminal.from X) (terminal.from Y)`, the product over the terminal object, with the
first projection as its structure morphism over `X`.  This file records that the fibre product
over `S` of `S × A` and `S × B` is a base change of `A × B`: a morphism `σ : A × B ⟶ D` induces
`(S × A) ×_S (S × B) ⟶ S × D` over `S`, and the resulting square is cartesian.

The point of stating this for an arbitrary category is that the three objects `A`, `B`, `D` are
then opaque, so the construction is forced to use nothing but the universal property of the
pullback.  It is applied to relative projective space over a base scheme, where `A`, `B` and `D`
are the integral models of `ℙⁿ`, `ℙᵐ` and `ℙᴺ` and `σ` is an absolute Segre morphism.

## What is proved, and the route

* `Stacks.CategoryTheory.TerminalPullback.prodMap`: the morphism
  `(S × A) ×_S (S × B) ⟶ A × B` assembled from the two second projections.
* `Stacks.CategoryTheory.TerminalPullback.baseChangeMap`: the morphism
  `(S × A) ×_S (S × B) ⟶ S × D` induced by `σ`.  It is a `pullback.lift` whose first component
  is the structure morphism over `S`, so
  `Stacks.CategoryTheory.TerminalPullback.baseChangeMap_comp_fst` — the statement that it is a
  morphism over `S` — holds for every `σ`.
* `Stacks.CategoryTheory.TerminalPullback.isPullback_baseChangeMap`: the square whose two
  verticals are `baseChangeMap` and `σ` and whose bottom is the second projection
  `S × D ⟶ D` is cartesian.  The lift of an arbitrary cone is
  `Stacks.CategoryTheory.TerminalPullback.coneLift`, built from two nested applications of the
  universal property; the three equations it has to satisfy are
  `coneLift_comp_prodMap`, `coneLift_comp_baseChangeMap` and `eq_coneLift`.
* `Stacks.CategoryTheory.TerminalPullback.isPullback_prodSnd`: the same fibre product is also
  `(S × A) × B`, the product over the terminal object of `S × A` with `B`.
* `Stacks.CategoryTheory.TerminalPullback.baseMap` and
  `Stacks.CategoryTheory.TerminalPullback.isPullback_baseMap`: **a product over the terminal
  object is stable under base change in its first factor**, `S' × A = (S × A) ×_S S'`.  For
  relative projective space this is the statement that `ℙⁿ_{S'}` is `ℙⁿ_S ×_S S'`.

## Implementation notes

Every composite of `prodMap`, `baseChangeMap` and `coneLift` with a projection of its target is
exported as a named equation, and the proofs use only those equations together with
`CategoryTheory.Limits.pullback.hom_ext`.  None of the three definitions is ever unfolded inside
a proof: `CategoryTheory.Limits.pullback.lift_fst` does not match through a definition, and
rewriting with the defining equation of one of them inside a composite is exactly the situation
where the motive is not found.

All statements are written with `CategoryTheory.Limits.pullback.fst` and
`CategoryTheory.Limits.pullback.snd` applied to `CategoryTheory.Limits.terminal.from`, in the
same shape that `CategoryTheory.Limits.pullback.hom_ext` produces, so that every rewrite in the
proofs is a syntactic match.

## What is not done

Nothing here constructs a morphism `σ`; the file is purely a transfer result, and it says
nothing about any property of `σ` other than those stable under base change.
-/

@[expose] public section

open CategoryTheory Limits

namespace Stacks.CategoryTheory.TerminalPullback

universe v u

variable {C : Type u} [Category.{v} C] [HasTerminal C] [HasPullbacks C] (S A B D : C)

/-- `Pair S A B` is the fibre product over `S` of the two products `S × A` and `S × B` taken over
the terminal object, each with its first projection as structure morphism over `S`. -/
public noncomputable abbrev Pair : C :=
  pullback (pullback.fst (terminal.from S) (terminal.from A))
    (pullback.fst (terminal.from S) (terminal.from B))

/-! ### The morphism to the product of the two factors -/

/-- The morphism `(S × A) ×_S (S × B) ⟶ A × B` assembled from the two second projections. -/
public noncomputable def prodMap : Pair S A B ⟶ pullback (terminal.from A) (terminal.from B) :=
  pullback.lift
    (pullback.fst (pullback.fst (terminal.from S) (terminal.from A))
        (pullback.fst (terminal.from S) (terminal.from B)) ≫
      pullback.snd (terminal.from S) (terminal.from A))
    (pullback.snd (pullback.fst (terminal.from S) (terminal.from A))
        (pullback.fst (terminal.from S) (terminal.from B)) ≫
      pullback.snd (terminal.from S) (terminal.from B))
    (terminal.hom_ext _ _)

/-- The first component of `prodMap` is the projection `(S × A) ×_S (S × B) ⟶ A`. -/
@[reassoc]
public theorem prodMap_comp_fst :
    prodMap S A B ≫ pullback.fst (terminal.from A) (terminal.from B) =
      pullback.fst (pullback.fst (terminal.from S) (terminal.from A))
          (pullback.fst (terminal.from S) (terminal.from B)) ≫
        pullback.snd (terminal.from S) (terminal.from A) :=
  pullback.lift_fst _ _ _

/-- The second component of `prodMap` is the projection `(S × A) ×_S (S × B) ⟶ B`. -/
@[reassoc]
public theorem prodMap_comp_snd :
    prodMap S A B ≫ pullback.snd (terminal.from A) (terminal.from B) =
      pullback.snd (pullback.fst (terminal.from S) (terminal.from A))
          (pullback.fst (terminal.from S) (terminal.from B)) ≫
        pullback.snd (terminal.from S) (terminal.from B) :=
  pullback.lift_snd _ _ _

/-! ### The base change of a morphism of products -/

variable (σ : pullback (terminal.from A) (terminal.from B) ⟶ D)

/-- The base change to `S` of a morphism `σ : A × B ⟶ D` of products over the terminal object. -/
public noncomputable def baseChangeMap :
    Pair S A B ⟶ pullback (terminal.from S) (terminal.from D) :=
  pullback.lift
    (pullback.fst (pullback.fst (terminal.from S) (terminal.from A))
        (pullback.fst (terminal.from S) (terminal.from B)) ≫
      pullback.fst (terminal.from S) (terminal.from A))
    (prodMap S A B ≫ σ) (terminal.hom_ext _ _)

/-- The base change of `σ` is a morphism over `S`, through the first projection.  This holds for
every `σ`. -/
@[reassoc]
public theorem baseChangeMap_comp_fst :
    baseChangeMap S A B D σ ≫ pullback.fst (terminal.from S) (terminal.from D) =
      pullback.fst (pullback.fst (terminal.from S) (terminal.from A))
          (pullback.fst (terminal.from S) (terminal.from B)) ≫
        pullback.fst (terminal.from S) (terminal.from A) :=
  pullback.lift_fst _ _ _

/-- The second component of `baseChangeMap` is `prodMap` followed by `σ`. -/
@[reassoc]
public theorem baseChangeMap_comp_snd :
    baseChangeMap S A B D σ ≫ pullback.snd (terminal.from S) (terminal.from D) =
      prodMap S A B ≫ σ :=
  pullback.lift_snd _ _ _

/-! ### The cartesian square -/

/-- The lift of a cone over `σ` and the second projection `S × D ⟶ D`. -/
public noncomputable def coneLift
    (s : PullbackCone σ (pullback.snd (terminal.from S) (terminal.from D))) :
    s.pt ⟶ Pair S A B :=
  pullback.lift
    (pullback.lift (s.snd ≫ pullback.fst (terminal.from S) (terminal.from D))
      (s.fst ≫ pullback.fst (terminal.from A) (terminal.from B)) (terminal.hom_ext _ _))
    (pullback.lift (s.snd ≫ pullback.fst (terminal.from S) (terminal.from D))
      (s.fst ≫ pullback.snd (terminal.from A) (terminal.from B)) (terminal.hom_ext _ _))
    (by rw [pullback.lift_fst, pullback.lift_fst])

/-- The component of `coneLift` in `S × A` is the lift of the `S`- and `A`-coordinates of `s`. -/
@[reassoc]
public theorem coneLift_comp_pair_fst
    (s : PullbackCone σ (pullback.snd (terminal.from S) (terminal.from D))) :
    coneLift S A B D σ s ≫ pullback.fst (pullback.fst (terminal.from S) (terminal.from A))
        (pullback.fst (terminal.from S) (terminal.from B)) =
      pullback.lift (s.snd ≫ pullback.fst (terminal.from S) (terminal.from D))
        (s.fst ≫ pullback.fst (terminal.from A) (terminal.from B)) (terminal.hom_ext _ _) :=
  pullback.lift_fst _ _ _

/-- The component of `coneLift` in `S × B` is the lift of the `S`- and `B`-coordinates of `s`. -/
@[reassoc]
public theorem coneLift_comp_pair_snd
    (s : PullbackCone σ (pullback.snd (terminal.from S) (terminal.from D))) :
    coneLift S A B D σ s ≫ pullback.snd (pullback.fst (terminal.from S) (terminal.from A))
        (pullback.fst (terminal.from S) (terminal.from B)) =
      pullback.lift (s.snd ≫ pullback.fst (terminal.from S) (terminal.from D))
        (s.fst ≫ pullback.snd (terminal.from A) (terminal.from B)) (terminal.hom_ext _ _) :=
  pullback.lift_snd _ _ _

/-- `coneLift` followed by `prodMap` is the first leg of the cone `s`. -/
@[reassoc]
public theorem coneLift_comp_prodMap
    (s : PullbackCone σ (pullback.snd (terminal.from S) (terminal.from D))) :
    coneLift S A B D σ s ≫ prodMap S A B = s.fst := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, prodMap_comp_fst, coneLift_comp_pair_fst_assoc, pullback.lift_snd]
  · rw [Category.assoc, prodMap_comp_snd, coneLift_comp_pair_snd_assoc, pullback.lift_snd]

/-- `coneLift` followed by `baseChangeMap` is the second leg of the cone `s`. -/
@[reassoc]
public theorem coneLift_comp_baseChangeMap
    (s : PullbackCone σ (pullback.snd (terminal.from S) (terminal.from D))) :
    coneLift S A B D σ s ≫ baseChangeMap S A B D σ = s.snd := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, baseChangeMap_comp_fst, coneLift_comp_pair_fst_assoc, pullback.lift_fst]
  · rw [Category.assoc, baseChangeMap_comp_snd, coneLift_comp_prodMap_assoc]
    exact s.condition

/-- A morphism compatible with both legs of the cone `s` is `coneLift`. -/
public theorem eq_coneLift
    (s : PullbackCone σ (pullback.snd (terminal.from S) (terminal.from D)))
    (k : s.pt ⟶ Pair S A B) (h₁ : k ≫ prodMap S A B = s.fst)
    (h₂ : k ≫ baseChangeMap S A B D σ = s.snd) :
    k = coneLift S A B D σ s := by
  refine pullback.hom_ext (pullback.hom_ext ?_ ?_) (pullback.hom_ext ?_ ?_)
  · rw [coneLift_comp_pair_fst, pullback.lift_fst, Category.assoc, ← baseChangeMap_comp_fst,
      ← Category.assoc, h₂]
  · rw [coneLift_comp_pair_fst, pullback.lift_snd, Category.assoc, ← prodMap_comp_fst,
      ← Category.assoc, h₁]
  · rw [coneLift_comp_pair_snd, pullback.lift_fst, Category.assoc, ← pullback.condition,
      ← baseChangeMap_comp_fst, ← Category.assoc, h₂]
  · rw [coneLift_comp_pair_snd, pullback.lift_snd, Category.assoc, ← prodMap_comp_snd,
      ← Category.assoc, h₁]

/-- The square exhibiting `baseChangeMap` as a base change of `σ`: its two verticals are
`baseChangeMap S A B D σ` and `σ`, and its bottom is the second projection `S × D ⟶ D`. -/
public theorem isPullback_baseChangeMap :
    IsPullback (prodMap S A B) (baseChangeMap S A B D σ) σ
      (pullback.snd (terminal.from S) (terminal.from D)) := by
  have hcomm : prodMap S A B ≫ σ =
      baseChangeMap S A B D σ ≫ pullback.snd (terminal.from S) (terminal.from D) :=
    (baseChangeMap_comp_snd S A B D σ).symm
  exact IsPullback.of_isLimit' ⟨hcomm⟩ (PullbackCone.IsLimit.mk hcomm (coneLift S A B D σ)
    (coneLift_comp_prodMap S A B D σ) (coneLift_comp_baseChangeMap S A B D σ)
    (fun s k h₁ h₂ => eq_coneLift S A B D σ s k h₁ h₂))

/-- A morphism property stable under base change passes from `σ` to its base change. -/
public theorem baseChangeMap_mem (P : MorphismProperty C) [P.IsStableUnderBaseChange]
    (hσ : P σ) : P (baseChangeMap S A B D σ) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (isPullback_baseChangeMap S A B D σ) hσ

/-! ### The fibre product as a product with the second factor -/

/-- The second projection of `(S × A) ×_S (S × B)` onto `B`. -/
public noncomputable def prodSnd : Pair S A B ⟶ B :=
  pullback.snd (pullback.fst (terminal.from S) (terminal.from A))
      (pullback.fst (terminal.from S) (terminal.from B)) ≫
    pullback.snd (terminal.from S) (terminal.from B)

/-- The lift of a cone over the two morphisms to the terminal object. -/
public noncomputable def prodConeLift
    (s : PullbackCone (terminal.from (pullback (terminal.from S) (terminal.from A)))
      (terminal.from B)) : s.pt ⟶ Pair S A B :=
  pullback.lift s.fst
    (pullback.lift (s.fst ≫ pullback.fst (terminal.from S) (terminal.from A)) s.snd
      (terminal.hom_ext _ _))
    (pullback.lift_fst _ _ _).symm

/-- The component of `prodConeLift` in `S × A` is the first leg of the cone `s`. -/
@[reassoc]
public theorem prodConeLift_comp_pair_fst
    (s : PullbackCone (terminal.from (pullback (terminal.from S) (terminal.from A)))
      (terminal.from B)) :
    prodConeLift S A B s ≫ pullback.fst (pullback.fst (terminal.from S) (terminal.from A))
        (pullback.fst (terminal.from S) (terminal.from B)) = s.fst :=
  pullback.lift_fst _ _ _

/-- The component of `prodConeLift` in `S × B` is the lift of `s.fst ≫ fst` and `s.snd`. -/
@[reassoc]
public theorem prodConeLift_comp_pair_snd
    (s : PullbackCone (terminal.from (pullback (terminal.from S) (terminal.from A)))
      (terminal.from B)) :
    prodConeLift S A B s ≫ pullback.snd (pullback.fst (terminal.from S) (terminal.from A))
        (pullback.fst (terminal.from S) (terminal.from B)) =
      pullback.lift (s.fst ≫ pullback.fst (terminal.from S) (terminal.from A)) s.snd
        (terminal.hom_ext _ _) :=
  pullback.lift_snd _ _ _

/-- The defining equation of `prodSnd`. -/
@[reassoc]
public theorem prodSnd_eq :
    prodSnd S A B =
      pullback.snd (pullback.fst (terminal.from S) (terminal.from A))
          (pullback.fst (terminal.from S) (terminal.from B)) ≫
        pullback.snd (terminal.from S) (terminal.from B) :=
  rfl

/-- The fibre product over `S` of `S × A` and `S × B` is the product over the terminal object of
`S × A` with `B`. -/
public theorem isPullback_prodSnd :
    IsPullback (pullback.fst (pullback.fst (terminal.from S) (terminal.from A))
        (pullback.fst (terminal.from S) (terminal.from B))) (prodSnd S A B)
      (terminal.from (pullback (terminal.from S) (terminal.from A))) (terminal.from B) := by
  have hcomm : pullback.fst (pullback.fst (terminal.from S) (terminal.from A))
        (pullback.fst (terminal.from S) (terminal.from B)) ≫
      terminal.from (pullback (terminal.from S) (terminal.from A)) =
        prodSnd S A B ≫ terminal.from B := terminal.hom_ext _ _
  refine IsPullback.of_isLimit' ⟨hcomm⟩ (PullbackCone.IsLimit.mk hcomm (prodConeLift S A B)
    (prodConeLift_comp_pair_fst S A B) (fun s => ?_) (fun s k h₁ h₂ => ?_))
  · rw [prodSnd_eq, prodConeLift_comp_pair_snd_assoc, pullback.lift_snd]
  · refine pullback.hom_ext ?_ (pullback.hom_ext ?_ ?_)
    · rw [prodConeLift_comp_pair_fst]
      exact h₁
    · rw [prodConeLift_comp_pair_snd, pullback.lift_fst, Category.assoc, ← pullback.condition,
        ← Category.assoc, h₁]
    · rw [prodConeLift_comp_pair_snd, pullback.lift_snd, Category.assoc, ← prodSnd_eq]
      exact h₂

/-! ### Changing the base of a product over the terminal object -/

section BaseMap

variable {S S' : C} (A : C) (b : S' ⟶ S)

/-- **Changing the base of a product over the terminal object.** A morphism `b : S' ⟶ S` induces
`S' × A ⟶ S × A`, acting as `b` on the first factor and as the identity on the second. -/
public noncomputable def baseMap :
    pullback (terminal.from S') (terminal.from A) ⟶
      pullback (terminal.from S) (terminal.from A) :=
  pullback.map _ _ _ _ b (𝟙 A) (𝟙 _) (terminal.hom_ext _ _) (terminal.hom_ext _ _)

/-- `baseMap A b` acts as `b` on the first factor. -/
@[reassoc]
public theorem baseMap_comp_fst :
    baseMap A b ≫ pullback.fst (terminal.from S) (terminal.from A) =
      pullback.fst (terminal.from S') (terminal.from A) ≫ b :=
  pullback.lift_fst _ _ _

/-- `baseMap A b` acts as the identity on the second factor `A`. -/
@[reassoc]
public theorem baseMap_comp_snd :
    baseMap A b ≫ pullback.snd (terminal.from S) (terminal.from A) =
      pullback.snd (terminal.from S') (terminal.from A) := by
  rw [baseMap, pullback.lift_snd, Category.comp_id]

/-- **A product over the terminal object is stable under base change in its first factor**: the
square whose two verticals are the first projections and whose bottom is `b` is cartesian.

Applied to relative projective space this says that `ℙⁿ_{S'}` is `ℙⁿ_S ×_S S'`, which is what
makes being an isomorphism over `S` a Zariski-local condition on `S`. The lift of a cone
`(h : T ⟶ S × A, k : T ⟶ S')` is `pullback.lift k (h ≫ pullback.snd _ _)`: a cone determines its
`S'`-coordinate directly and takes its `A`-coordinate from `h`. -/
public theorem isPullback_baseMap :
    IsPullback (baseMap A b) (pullback.fst (terminal.from S') (terminal.from A))
      (pullback.fst (terminal.from S) (terminal.from A)) b := by
  refine IsPullback.of_isLimit' ⟨baseMap_comp_fst A b⟩
    (PullbackCone.IsLimit.mk (baseMap_comp_fst A b)
      (fun s => pullback.lift (PullbackCone.snd s)
        (PullbackCone.fst s ≫ pullback.snd (terminal.from S) (terminal.from A))
        (terminal.hom_ext _ _)) (fun s => ?_) (fun s => ?_) (fun s k h₁ h₂ => ?_))
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, baseMap_comp_fst, ← Category.assoc, pullback.lift_fst]
      exact (PullbackCone.condition s).symm
    · rw [Category.assoc, baseMap_comp_snd, pullback.lift_snd]
  · exact pullback.lift_fst _ _ _
  · refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst]; exact h₂
    · rw [pullback.lift_snd, ← baseMap_comp_snd A b, ← Category.assoc, h₁]

end BaseMap

end Stacks.CategoryTheory.TerminalPullback

end
