module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Logic.Small.Set
public import StacksCore.Tactic.StacksAttribute

/-! # The stagewise construction of a small closed object property

The construction behind Stacks 0010 and Stacks 05PQ: starting from a family `A : S → 𝒜` and a
unary operation `E : 𝒜 → 𝒜`, build a `max v w`-small object property of `𝒜` that contains every
`A s` and is closed under zero, binary biproducts, kernels, cokernels and `E`. A *stage* is a
small carrier type with an embedding into `𝒜`; each stage is enlarged by adding the objects the
closure conditions demand, and `generated E A` is the union of the resulting chain.

Taking `E = Injective.under` gives closure under injective envelopes, which is what Stacks 0010
needs; taking `E = id` imposes no extra closure condition and needs no hypothesis on `𝒜` beyond
being abelian, which is what Stacks 05PQ needs.

The closure conditions themselves, and the theorems carrying the tags, are in
`StacksFrontier.CategoryTheory.Abelian.SmallSubcategory.AbelianOnly` and
`StacksFrontier.CategoryTheory.Abelian.SmallSubcategory`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v w u

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable {S : Type w}

namespace AbClosureConstr

/-- A stage: a `max v w`-small carrier type with an embedding into `𝒜`. -/
structure Stage (𝒜 : Type u) [Category.{v} 𝒜] : Type (max (u+1) (v+1) (w+1)) where
  /-- The (small) carrier type of generators at this stage. -/
  Ty : Type (max v w)
  /-- The embedding of generators into `𝒜`. -/
  emb : Ty → 𝒜

/-- One-step successor of a stage: adjoins biproducts, kernels, cokernels and the values of the
unary operation `E` on the previous generators. -/
noncomputable def nextStage (E : 𝒜 → 𝒜) (s : Stage.{v, w, u} 𝒜) : Stage.{v, w, u} 𝒜 :=
  haveI : LocallySmall.{max v w} 𝒜 := locallySmall_max.{w}
  { Ty := s.Ty
        ⊕ (s.Ty × s.Ty)
        ⊕ (Σ a b : s.Ty, Shrink.{max v w} (s.emb a ⟶ s.emb b))
        ⊕ (Σ a b : s.Ty, Shrink.{max v w} (s.emb a ⟶ s.emb b))
        ⊕ s.Ty
    emb := fun
      | .inl a => s.emb a
      | .inr (.inl (a, b)) => s.emb a ⊞ s.emb b
      | .inr (.inr (.inl ⟨_, _, f⟩)) => kernel ((equivShrink _).symm f)
      | .inr (.inr (.inr (.inl ⟨_, _, f⟩))) => cokernel ((equivShrink _).symm f)
      | .inr (.inr (.inr (.inr a))) => E (s.emb a) }

/-- Stage 0: the zero object and every `A s`. -/
noncomputable def stage0 (A : S → 𝒜) : Stage.{v, w, u} 𝒜 :=
  { Ty := ULift.{max v w} (Option S)
    emb := fun x => x.down.elim (HasZeroObject.zero (C := 𝒜)).choose A }

/-- The sequence of stages built by iterating `nextStage E` from `stage0`. -/
noncomputable def stageSeq (E : 𝒜 → 𝒜) (A : S → 𝒜) : ℕ → Stage.{v, w, u} 𝒜
  | 0 => stage0 A
  | (n+1) => nextStage E (stageSeq E A n)

/-- The global carrier map: a generator at stage `n` maps to its embedded object. -/
noncomputable def carrier (E : 𝒜 → 𝒜) (A : S → 𝒜) :
    (Σ n : ℕ, (stageSeq E A n).Ty) → 𝒜 :=
  fun x => (stageSeq E A x.fst).emb x.snd

/-- The object property: the range of `carrier E A`. -/
def generated (E : 𝒜 → 𝒜) (A : S → 𝒜) : ObjectProperty 𝒜 := fun Y => ∃ g, carrier E A g = Y

variable {A : S → 𝒜}

/-- One-step bump: injecting stage `n` into stage `n+1` preserves `emb`. -/
theorem bump1_emb (E : 𝒜 → 𝒜) (n : ℕ) (a : (stageSeq E A n).Ty) :
    (stageSeq E A (n+1)).emb (Sum.inl a) = (stageSeq E A n).emb a := rfl

/-- A kernel generator at stage `n + 1` embeds as the kernel of its morphism. -/
theorem kernel_emb (E : 𝒜 → 𝒜) (n : ℕ) (a b : (stageSeq E A n).Ty)
    (f : haveI : LocallySmall.{max v w} 𝒜 := locallySmall_max.{w}
      Shrink.{max v w} ((stageSeq E A n).emb a ⟶ (stageSeq E A n).emb b)) :
    haveI : LocallySmall.{max v w} 𝒜 := locallySmall_max.{w}
    (stageSeq E A (n+1)).emb (Sum.inr (Sum.inr (Sum.inl ⟨a, b, f⟩))) =
      kernel ((equivShrink _).symm f) := rfl

/-- A cokernel generator at stage `n + 1` embeds as the cokernel of its morphism. -/
theorem cokernel_emb (E : 𝒜 → 𝒜) (n : ℕ) (a b : (stageSeq E A n).Ty)
    (f : haveI : LocallySmall.{max v w} 𝒜 := locallySmall_max.{w}
      Shrink.{max v w} ((stageSeq E A n).emb a ⟶ (stageSeq E A n).emb b)) :
    haveI : LocallySmall.{max v w} 𝒜 := locallySmall_max.{w}
    (stageSeq E A (n+1)).emb (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨a, b, f⟩)))) =
      cokernel ((equivShrink _).symm f) := rfl

/-- Bump a generator from stage `n` up to stage `n + k`. -/
noncomputable def bumpAdd (E : 𝒜 → 𝒜) (A : S → 𝒜) (n : ℕ) :
    (k : ℕ) → (stageSeq E A n).Ty → (stageSeq E A (n+k)).Ty
  | 0, a => a
  | (k+1), a => Sum.inl (bumpAdd E A n k a)

/-- Bumping a generator up from stage `n` to stage `n + k` preserves `emb`. -/
theorem bumpAdd_emb (E : 𝒜 → 𝒜) (n : ℕ) : ∀ (k : ℕ) (a : (stageSeq E A n).Ty),
    (stageSeq E A (n+k)).emb (bumpAdd E A n k a) = (stageSeq E A n).emb a
  | 0, _ => rfl
  | (k+1), a => (bump1_emb E (n + k) _).trans (bumpAdd_emb E n k a)

/-- `emb` is preserved under casting the stage index along an equality. -/
theorem castStage_emb (E : 𝒜 → 𝒜) (A : S → 𝒜) {n n' : ℕ} (h : n = n')
    (a : (stageSeq E A n).Ty) :
    (stageSeq E A n').emb (h ▸ a) = (stageSeq E A n).emb a := by
  cases h; rfl

/-- If `X` and `Y` are both in the range of `carrier E A`, they arise at a common stage. -/
theorem common_stage (E : 𝒜 → 𝒜) {X Y : 𝒜} (hX : generated E A X) (hY : generated E A Y) :
    ∃ (k : ℕ) (a b : (stageSeq E A k).Ty),
      (stageSeq E A k).emb a = X ∧ (stageSeq E A k).emb b = Y := by
  obtain ⟨⟨n, a⟩, ha⟩ := hX
  obtain ⟨⟨m, b⟩, hb⟩ := hY
  exact ⟨n + m, bumpAdd E A n m a, (Nat.add_comm m n) ▸ (bumpAdd E A m n b),
    (bumpAdd_emb E n m a).trans ha,
    (castStage_emb E A _ _).trans ((bumpAdd_emb E m n b).trans hb)⟩

/-- `generated E A` contains the zero object chosen at stage `0`. -/
theorem has_zero (E : 𝒜 → 𝒜) : ∃ Z : 𝒜, IsZero Z ∧ generated E A Z :=
  ⟨(HasZeroObject.zero (C := 𝒜)).choose, (HasZeroObject.zero (C := 𝒜)).choose_spec,
    ⟨0, ULift.up none⟩, rfl⟩

/-- `generated E A` contains every member of the family `A`, as a stage-`0` generator. -/
theorem contains_A (E : 𝒜 → 𝒜) (s : S) : generated E A (A s) :=
  ⟨⟨0, ULift.up (some s)⟩, rfl⟩

/-- `generated E A` is closed under binary biproducts. -/
theorem closed_biprod (E : 𝒜 → 𝒜) (X Y : 𝒜) (hX : generated E A X) (hY : generated E A Y) :
    generated E A (X ⊞ Y) := by
  obtain ⟨k, a, b, rfl, rfl⟩ := common_stage E hX hY
  exact ⟨⟨k+1, Sum.inr (Sum.inl (a, b))⟩, rfl⟩

/-- `generated E A` is closed under kernels of morphisms between its members. -/
theorem closed_kernel (E : 𝒜 → 𝒜) {X Y : 𝒜} (f : X ⟶ Y) (hX : generated E A X)
    (hY : generated E A Y) :
    generated E A (kernel f) := by
  have : LocallySmall.{max v w} 𝒜 := locallySmall_max.{w}
  obtain ⟨k, a, b, rfl, rfl⟩ := common_stage E hX hY
  refine ⟨⟨k+1, Sum.inr (Sum.inr (Sum.inl ⟨a, b, equivShrink _ f⟩))⟩, ?_⟩
  rw [carrier, kernel_emb, Equiv.symm_apply_apply]

/-- `generated E A` is closed under cokernels of morphisms between its members. -/
theorem closed_cokernel (E : 𝒜 → 𝒜) {X Y : 𝒜} (f : X ⟶ Y) (hX : generated E A X)
    (hY : generated E A Y) :
    generated E A (cokernel f) := by
  have : LocallySmall.{max v w} 𝒜 := locallySmall_max.{w}
  obtain ⟨k, a, b, rfl, rfl⟩ := common_stage E hX hY
  refine ⟨⟨k+1, Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨a, b, equivShrink _ f⟩)))⟩, ?_⟩
  rw [carrier, cokernel_emb, Equiv.symm_apply_apply]

/-- `generated E A` is closed under the unary operation `E`. -/
theorem closed_unary (E : 𝒜 → 𝒜) (X : 𝒜) (hX : generated E A X) : generated E A (E X) := by
  obtain ⟨⟨n, a⟩, rfl⟩ := hX
  exact ⟨⟨n+1, Sum.inr (Sum.inr (Sum.inr (Sum.inr a)))⟩, rfl⟩

/-- The objects of `(generated E A).FullSubcategory` are the subtype of `𝒜` cut out by
`generated E A`. -/
def fullSubcatEquiv (E : 𝒜 → 𝒜) (A : S → 𝒜) :
    (generated E A).FullSubcategory ≃ {X : 𝒜 // generated E A X} where
  toFun x := ⟨x.obj, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `(generated E A).FullSubcategory` is `max v w`-small: its objects are the range of
`carrier E A`, whose domain `Σ n, (stageSeq E A n).Ty` already lives in `Type (max v w)`. -/
theorem small_fullSubcat (E : 𝒜 → 𝒜) (A : S → 𝒜) :
    Small.{max v w} (generated E A).FullSubcategory := by
  have : Small.{max v w} {X : 𝒜 // generated E A X} := small_range (carrier E A)
  exact small_map (fullSubcatEquiv E A)

end AbClosureConstr
