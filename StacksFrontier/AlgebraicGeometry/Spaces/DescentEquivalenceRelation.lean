module

public import Mathlib.CategoryTheory.EquivalenceRelation

/-!
# Pulling back an internal equivalence relation along a pair of cartesian squares

Let `p₁, p₂ : R ⇉ U` be an internal equivalence relation in a category, let `q : P ⟶ U` be an
object over `U`, and let `f₁, f₂ : Q ⇉ P` together with `k : Q ⟶ R` be a candidate relation
over it, meaning that both squares
```
Q --f₁--> P        Q --f₂--> P
|         |        |         |
k         q        k         q
v         v        v         v
R --p₁--> U        R --p₂--> U
```
are cartesian.  Then `f₁` and `f₂` are automatically jointly monic, and each of reflexivity,
symmetry and transitivity of `f₁, f₂` reduces to a *single* equation: the two cartesian squares
produce canonical candidates `ρ : P ⟶ Q`, `σ : Q ⟶ Q` and `τ : Q ×_P Q ⟶ Q` for the three
witnesses, each of which satisfies its condition against `f₁` by construction, so that only its
condition against `f₂` remains.  Those three remaining equations are the normalisation and
cocycle conditions of the descent datum, and they do not follow from the two cartesian squares:
if `φ` is an automorphism of `P` over `U` then replacing `f₂` by `φ ≫ f₂` leaves both squares
cartesian while destroying reflexivity unless `φ = 𝟙`.

## Main results

* `Stacks.Descent.jointlyMono₂_of_isPullback`: joint monicity of `f₁, f₂` is automatic.
* `Stacks.Descent.reflHom_comp_fst`, `Stacks.Descent.symHom_comp_fst` and
  `Stacks.Descent.transHom_comp_fst`: the canonical candidate witnesses satisfy their first
  condition by construction.
* `Stacks.Descent.eq_reflHom`, `Stacks.Descent.eq_symHom` and `Stacks.Descent.eq_transHom`: the
  canonical candidates are the *only* possible witnesses, so the three remaining equations are
  not merely sufficient but equivalent to the relation being an equivalence relation.
* `Stacks.Descent.reflexiveRelation_of_isPullback`,
  `Stacks.Descent.symmetricRelation_of_isPullback` and
  `Stacks.Descent.transitiveRelation_of_isPullback`: each of the three structures follows from
  one equation.
* `Stacks.Descent.equivalenceRelation_of_isPullback` and
  `Stacks.Descent.isEquivalenceRelation_of_isPullback`: `f₁, f₂` is an internal equivalence
  relation as soon as the three remaining equations hold.

## Implementation notes

The joint monicity of `f₁, f₂` is the only one of the four conditions that is free, and it uses
the joint monicity of `p₁, p₂` rather than either square alone: a pair of maps into `Q` agreeing
after `f₁` and after `f₂` agrees after `k ≫ p₁` and after `k ≫ p₂`, hence after `k`, and then
the first square separates it.

`Stacks.Descent.equivalenceRelation_of_isPullback` takes the three witnesses existentially
rather than as the canonical `ρ`, `σ`, `τ`, so that a consumer who has produced witnesses by
other means can use it directly; the canonical candidates and the one-equation reductions are
stated separately for a consumer who wants to see exactly which equation is at stake.

The transitivity pullback of `f₂` against `f₁` is taken as an explicit limiting cone, exactly as
in `CategoryTheory.TransitiveRelation`, so that no `HasPullbacks` hypothesis is needed.

Each of the three uniqueness statements goes through the base relation: a witness and the
canonical candidate agree after `k` because `p₁, p₂` are jointly monic and both composites are
pinned by the two squares, and then the first square separates them.

## References

* [Stacks Project, Tag 0263](https://stacks.math.columbia.edu/tag/0263)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 084C](https://stacks.math.columbia.edu/tag/084C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Descent

variable {C : Type*} [Category* C] {R U P Q : C} {p₁ p₂ : R ⟶ U} {q : P ⟶ U} {k : Q ⟶ R}
  {f₁ f₂ : Q ⟶ P}

/-- Two maps into `Q` agree if they agree after `f₁` and after `k ≫ p₂`, given that `p₁, p₂` are
jointly monic and the first square is cartesian. -/
private theorem eq_of_comp_fst_of_comp_base_snd {X : C} (hp : JointlyMono₂ p₁ p₂)
    (h₁ : IsPullback f₁ k q p₁) {a b : X ⟶ Q} (ha : a ≫ f₁ = b ≫ f₁)
    (hb : (a ≫ k) ≫ p₂ = (b ≫ k) ≫ p₂) : a = b :=
  h₁.hom_ext ha (hp.right_cancellation _ _
    (by rw [Category.assoc, Category.assoc, ← h₁.w, ← Category.assoc, ← Category.assoc, ha]) hb)

/-- **Joint monicity is inherited.** If both squares are cartesian and `p₁, p₂` are jointly
monic, then so are `f₁, f₂`. -/
theorem jointlyMono₂_of_isPullback (hp : JointlyMono₂ p₁ p₂) (h₁ : IsPullback f₁ k q p₁)
    (h₂ : IsPullback f₂ k q p₂) : JointlyMono₂ f₁ f₂ where
  right_cancellation _ _ _ hu hv :=
    eq_of_comp_fst_of_comp_base_snd hp h₁ hu
      (by rw [Category.assoc, Category.assoc, ← h₂.w, ← Category.assoc, ← Category.assoc, hv])

/-! ### The canonical candidate witnesses -/

/-- The canonical candidate for reflexivity of `f₁, f₂`: the lift of the identity of `P` and of
the reflexivity section of the base relation through the first cartesian square. -/
def reflHom (e : ReflexiveRelation p₁ p₂) (h₁ : IsPullback f₁ k q p₁) : P ⟶ Q :=
  h₁.lift (𝟙 P) (q ≫ e.r) (by rw [Category.id_comp, Category.assoc, e.reflexivity₁,
    Category.comp_id])

/-- The canonical reflexivity candidate `reflHom e h₁` is a section of `f₁`. -/
@[simp]
theorem reflHom_comp_fst (e : ReflexiveRelation p₁ p₂) (h₁ : IsPullback f₁ k q p₁) :
    reflHom e h₁ ≫ f₁ = 𝟙 P :=
  h₁.lift_fst _ _ _

/-- The canonical reflexivity candidate `reflHom e h₁` followed by `k` is `q ≫ e.r`. -/
@[simp]
theorem reflHom_comp_snd_base (e : ReflexiveRelation p₁ p₂) (h₁ : IsPullback f₁ k q p₁) :
    reflHom e h₁ ≫ k = q ≫ e.r :=
  h₁.lift_snd _ _ _

/-- The canonical candidate for symmetry of `f₁, f₂`: the lift of `f₂` and of the symmetry
morphism of the base relation through the first cartesian square. -/
def symHom (e : SymmetricRelation p₁ p₂) (h₁ : IsPullback f₁ k q p₁)
    (h₂ : IsPullback f₂ k q p₂) : Q ⟶ Q :=
  h₁.lift f₂ (k ≫ e.s) (by rw [h₂.w, Category.assoc, e.symmetry₁])

/-- The canonical symmetry candidate `symHom e h₁ h₂` followed by `f₁` equals `f₂`. -/
@[simp]
theorem symHom_comp_fst (e : SymmetricRelation p₁ p₂) (h₁ : IsPullback f₁ k q p₁)
    (h₂ : IsPullback f₂ k q p₂) : symHom e h₁ h₂ ≫ f₁ = f₂ :=
  h₁.lift_fst _ _ _

/-- The canonical symmetry candidate `symHom e h₁ h₂` followed by `k` is `k ≫ e.s`. -/
@[simp]
theorem symHom_comp_snd_base (e : SymmetricRelation p₁ p₂) (h₁ : IsPullback f₁ k q p₁)
    (h₂ : IsPullback f₂ k q p₂) : symHom e h₁ h₂ ≫ k = k ≫ e.s :=
  h₁.lift_snd _ _ _

section Trans

/-- A composable pair of points of `f₁, f₂` gives a composable pair of points of the base
relation. -/
theorem transBase_condition (h₁ : IsPullback f₁ k q p₁) (h₂ : IsPullback f₂ k q p₂)
    (c : PullbackCone f₂ f₁) : (c.fst ≫ k) ≫ p₂ = (c.snd ≫ k) ≫ p₁ := by
  rw [Category.assoc, Category.assoc, ← h₁.w, ← h₂.w, ← Category.assoc, ← Category.assoc,
    c.condition]

/-- The map to the base relation's transitivity pullback induced by a composable pair of points
of `f₁, f₂`. -/
def transBase (e : TransitiveRelation p₁ p₂) (h₁ : IsPullback f₁ k q p₁)
    (h₂ : IsPullback f₂ k q p₂) (c : PullbackCone f₂ f₁) : c.pt ⟶ e.c.pt :=
  PullbackCone.IsLimit.lift e.isLimit (c.fst ≫ k) (c.snd ≫ k) (transBase_condition h₁ h₂ c)

/-- The map `transBase e h₁ h₂ c` followed by the first projection `e.c.fst` is `c.fst ≫ k`. -/
@[simp]
theorem transBase_comp_fst (e : TransitiveRelation p₁ p₂) (h₁ : IsPullback f₁ k q p₁)
    (h₂ : IsPullback f₂ k q p₂) (c : PullbackCone f₂ f₁) :
    transBase e h₁ h₂ c ≫ e.c.fst = c.fst ≫ k :=
  PullbackCone.IsLimit.lift_fst _ _ _ _

/-- The map `transBase e h₁ h₂ c` followed by the second projection `e.c.snd` is `c.snd ≫ k`. -/
@[simp]
theorem transBase_comp_snd (e : TransitiveRelation p₁ p₂) (h₁ : IsPullback f₁ k q p₁)
    (h₂ : IsPullback f₂ k q p₂) (c : PullbackCone f₂ f₁) :
    transBase e h₁ h₂ c ≫ e.c.snd = c.snd ≫ k :=
  PullbackCone.IsLimit.lift_snd _ _ _ _

/-- The composite in the base relation of a composable pair of points of `f₁, f₂` lies over the
image of the first point. -/
theorem transHom_condition (e : TransitiveRelation p₁ p₂) (h₁ : IsPullback f₁ k q p₁)
    (h₂ : IsPullback f₂ k q p₂) (c : PullbackCone f₂ f₁) :
    (c.fst ≫ f₁) ≫ q = (transBase e h₁ h₂ c ≫ e.t) ≫ p₁ := by
  have h : transBase e h₁ h₂ c ≫ e.t ≫ p₁ = c.fst ≫ f₁ ≫ q := by
    rw [e.transitivity₁, ← Category.assoc, transBase_comp_fst e h₁ h₂ c, Category.assoc,
      ← h₁.w]
  rw [Category.assoc, Category.assoc, h]

/-- The canonical candidate for transitivity of `f₁, f₂`: the lift of the first projection
followed by `f₁`, and of the composite in the base relation, through the first cartesian
square. -/
def transHom (e : TransitiveRelation p₁ p₂) (h₁ : IsPullback f₁ k q p₁)
    (h₂ : IsPullback f₂ k q p₂) (c : PullbackCone f₂ f₁) : c.pt ⟶ Q :=
  h₁.lift (c.fst ≫ f₁) (transBase e h₁ h₂ c ≫ e.t) (transHom_condition e h₁ h₂ c)

/-- The canonical transitivity candidate `transHom e h₁ h₂ c` followed by `f₁` equals
`c.fst ≫ f₁`. -/
@[simp]
theorem transHom_comp_fst (e : TransitiveRelation p₁ p₂) (h₁ : IsPullback f₁ k q p₁)
    (h₂ : IsPullback f₂ k q p₂) (c : PullbackCone f₂ f₁) :
    transHom e h₁ h₂ c ≫ f₁ = c.fst ≫ f₁ :=
  h₁.lift_fst _ _ _

/-- The canonical transitivity candidate `transHom e h₁ h₂ c` followed by `k` is
`transBase e h₁ h₂ c ≫ e.t`. -/
@[simp]
theorem transHom_comp_snd_base (e : TransitiveRelation p₁ p₂) (h₁ : IsPullback f₁ k q p₁)
    (h₂ : IsPullback f₂ k q p₂) (c : PullbackCone f₂ f₁) :
    transHom e h₁ h₂ c ≫ k = transBase e h₁ h₂ c ≫ e.t :=
  h₁.lift_snd _ _ _

end Trans

/-! ### The canonical candidates are the only possible witnesses -/

/-- A reflexivity witness for `f₁, f₂` is the canonical candidate `ρ`. -/
theorem eq_reflHom (e : ReflexiveRelation p₁ p₂) (h₁ : IsPullback f₁ k q p₁)
    (h₂ : IsPullback f₂ k q p₂) {ρ : P ⟶ Q} (hρ₁ : ρ ≫ f₁ = 𝟙 P) (hρ₂ : ρ ≫ f₂ = 𝟙 P) :
    ρ = reflHom e h₁ := by
  refine eq_of_comp_fst_of_comp_base_snd e.toJointlyMono₂ h₁ (by rw [hρ₁, reflHom_comp_fst]) ?_
  rw [reflHom_comp_snd_base, Category.assoc, ← h₂.w, ← Category.assoc, hρ₂, Category.id_comp,
    Category.assoc, e.reflexivity₂, Category.comp_id]

/-- A symmetry witness for `f₁, f₂` is the canonical candidate `σ`. -/
theorem eq_symHom (e : SymmetricRelation p₁ p₂) (h₁ : IsPullback f₁ k q p₁)
    (h₂ : IsPullback f₂ k q p₂) {σ : Q ⟶ Q} (hσ₁ : σ ≫ f₁ = f₂) (hσ₂ : σ ≫ f₂ = f₁) :
    σ = symHom e h₁ h₂ := by
  refine eq_of_comp_fst_of_comp_base_snd e.toJointlyMono₂ h₁ (by rw [hσ₁, symHom_comp_fst]) ?_
  rw [symHom_comp_snd_base, Category.assoc, ← h₂.w, ← Category.assoc, hσ₂, h₁.w, Category.assoc,
    e.symmetry₂]

/-- A transitivity witness for `f₁, f₂` is the canonical candidate `τ`. -/
theorem eq_transHom (e : TransitiveRelation p₁ p₂) (h₁ : IsPullback f₁ k q p₁)
    (h₂ : IsPullback f₂ k q p₂) (c : PullbackCone f₂ f₁) {τ : c.pt ⟶ Q}
    (hτ₁ : τ ≫ f₁ = c.fst ≫ f₁) (hτ₂ : τ ≫ f₂ = c.snd ≫ f₂) :
    τ = transHom e h₁ h₂ c := by
  refine eq_of_comp_fst_of_comp_base_snd e.toJointlyMono₂ h₁ (by rw [hτ₁, transHom_comp_fst]) ?_
  have hR : transBase e h₁ h₂ c ≫ e.t ≫ p₂ = c.snd ≫ f₂ ≫ q := by
    rw [e.transitivity₂, ← Category.assoc, transBase_comp_snd e h₁ h₂ c, Category.assoc, ← h₂.w]
  rw [transHom_comp_snd_base, Category.assoc, ← h₂.w, ← Category.assoc, hτ₂, Category.assoc,
    Category.assoc, hR]

/-! ### The three conditions -/

/-- **Reflexivity from one equation.** The pulled-back relation is reflexive as soon as the
canonical candidate `ρ` is a section of `f₂` as well as of `f₁`. -/
def reflexiveRelation_of_isPullback (e : ReflexiveRelation p₁ p₂)
    (h₁ : IsPullback f₁ k q p₁) (h₂ : IsPullback f₂ k q p₂)
    (hr : reflHom e h₁ ≫ f₂ = 𝟙 P) : ReflexiveRelation f₁ f₂ where
  __ := jointlyMono₂_of_isPullback e.toJointlyMono₂ h₁ h₂
  r := reflHom e h₁
  reflexivity₁ := reflHom_comp_fst e h₁
  reflexivity₂ := hr

/-- **Symmetry from one equation.** The pulled-back relation is symmetric as soon as the
canonical candidate `σ` interchanges `f₁` and `f₂` in the second direction as well. -/
def symmetricRelation_of_isPullback (e : SymmetricRelation p₁ p₂)
    (h₁ : IsPullback f₁ k q p₁) (h₂ : IsPullback f₂ k q p₂)
    (hs : symHom e h₁ h₂ ≫ f₂ = f₁) : SymmetricRelation f₁ f₂ where
  __ := jointlyMono₂_of_isPullback e.toJointlyMono₂ h₁ h₂
  s := symHom e h₁ h₂
  symmetry₁ := symHom_comp_fst e h₁ h₂
  symmetry₂ := hs

/-- **Transitivity from one equation.** The pulled-back relation is transitive as soon as the
canonical candidate `τ` composes correctly against `f₂` as well as against `f₁`. -/
def transitiveRelation_of_isPullback (e : TransitiveRelation p₁ p₂)
    (h₁ : IsPullback f₁ k q p₁) (h₂ : IsPullback f₂ k q p₂) (c : PullbackCone f₂ f₁)
    (hc : IsLimit c) (ht : transHom e h₁ h₂ c ≫ f₂ = c.snd ≫ f₂) :
    TransitiveRelation f₁ f₂ where
  __ := jointlyMono₂_of_isPullback e.toJointlyMono₂ h₁ h₂
  c := c
  isLimit := hc
  t := transHom e h₁ h₂ c
  transitivity₁ := transHom_comp_fst e h₁ h₂ c
  transitivity₂ := ht

/-! ### The descended equivalence relation -/

/-- **An internal equivalence relation pulls back along a pair of cartesian squares, given the
normalisation and cocycle conditions.** The witnesses are taken as hypotheses: they are the
content that the two cartesian squares do not supply. -/
def equivalenceRelation_of_isPullback (e : EquivalenceRelation p₁ p₂)
    (h₁ : IsPullback f₁ k q p₁) (h₂ : IsPullback f₂ k q p₂) (c : PullbackCone f₂ f₁)
    (hc : IsLimit c) (hr : ∃ ρ : P ⟶ Q, ρ ≫ f₁ = 𝟙 P ∧ ρ ≫ f₂ = 𝟙 P)
    (hs : ∃ σ : Q ⟶ Q, σ ≫ f₁ = f₂ ∧ σ ≫ f₂ = f₁)
    (ht : ∃ τ : c.pt ⟶ Q, τ ≫ f₁ = c.fst ≫ f₁ ∧ τ ≫ f₂ = c.snd ≫ f₂) :
    EquivalenceRelation f₁ f₂ :=
  { __ := jointlyMono₂_of_isPullback e.toJointlyMono₂ h₁ h₂
    r := hr.choose
    reflexivity₁ := hr.choose_spec.1
    reflexivity₂ := hr.choose_spec.2
    s := hs.choose
    symmetry₁ := hs.choose_spec.1
    symmetry₂ := hs.choose_spec.2
    c := c
    isLimit := hc
    t := ht.choose
    transitivity₁ := ht.choose_spec.1
    transitivity₂ := ht.choose_spec.2 }

/-- **The typeclass form.** If `p₁, p₂` is an internal equivalence relation, both squares are
cartesian, the transitivity pullback of `f₂` against `f₁` exists, and the normalisation and
cocycle witnesses are available, then `f₁, f₂` is an internal equivalence relation. -/
theorem isEquivalenceRelation_of_isPullback (e : EquivalenceRelation p₁ p₂)
    (h₁ : IsPullback f₁ k q p₁) (h₂ : IsPullback f₂ k q p₂) (c : PullbackCone f₂ f₁)
    (hc : IsLimit c) (hr : ∃ ρ : P ⟶ Q, ρ ≫ f₁ = 𝟙 P ∧ ρ ≫ f₂ = 𝟙 P)
    (hs : ∃ σ : Q ⟶ Q, σ ≫ f₁ = f₂ ∧ σ ≫ f₂ = f₁)
    (ht : ∃ τ : c.pt ⟶ Q, τ ≫ f₁ = c.fst ≫ f₁ ∧ τ ≫ f₂ = c.snd ≫ f₂) :
    IsEquivalenceRelation f₁ f₂ :=
  (equivalenceRelation_of_isPullback e h₁ h₂ c hc hr hs ht).isEquivalenceRelation

/-- The canonical candidates, assembled: if each of the three canonical witnesses satisfies its
one remaining equation, the pulled-back relation is an internal equivalence relation. -/
theorem isEquivalenceRelation_of_canonical (e : EquivalenceRelation p₁ p₂)
    (h₁ : IsPullback f₁ k q p₁) (h₂ : IsPullback f₂ k q p₂) (c : PullbackCone f₂ f₁)
    (hc : IsLimit c) (hr : reflHom e.toReflexiveRelation h₁ ≫ f₂ = 𝟙 P)
    (hs : symHom e.toSymmetricRelation h₁ h₂ ≫ f₂ = f₁)
    (ht : transHom e.toTransitiveRelation h₁ h₂ c ≫ f₂ = c.snd ≫ f₂) :
    IsEquivalenceRelation f₁ f₂ :=
  isEquivalenceRelation_of_isPullback e h₁ h₂ c hc
    ⟨reflHom e.toReflexiveRelation h₁, reflHom_comp_fst _ _, hr⟩
    ⟨symHom e.toSymmetricRelation h₁ h₂, symHom_comp_fst _ _ _, hs⟩
    ⟨transHom e.toTransitiveRelation h₁ h₂ c, transHom_comp_fst _ _ _ _, ht⟩

end Stacks.Descent

end
