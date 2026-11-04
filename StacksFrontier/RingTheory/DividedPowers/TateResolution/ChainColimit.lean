module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableExtension.Construction

/-! # The colimit of an `ω`-chain of graded divided power algebras

The colimit machinery of
`StacksFrontier/RingTheory/DividedPowers/TateResolution/SetVariableExtension/Construction.lean`
is indexed by the finite subsets of a type, because that is the shape in which a set of
variables is adjoined. The square-zero lift of Tag 09PS instead needs the colimit of a
*chain*: one stage for each degree, the stage in degree `n + 1` being obtained from the
stage in degree `n` by adjoining the variables of degree `n + 1`.

This file reindexes such a chain as a diagram over finite subsets. A chain
`B : ℕ → GradedDPAlgebra R` with transition morphisms `step n : B n ⟶ B (n + 1)` is turned
into a diagram over `Finset ℕ` by `S ↦ B (S.sup id)`, which is cofinal in the chain, and the
colimit of that diagram is taken. The result is a graded divided power algebra together with
a morphism out of each stage of the chain, and it has the universal property of the colimit
of the chain: a family of morphisms out of the stages compatible with the `step` maps
extends uniquely.

## Main definitions

* `DividedPowers.TateResolution.chainMap` — the composite transition morphism
  `B m ⟶ B k` attached to an inequality `m ≤ k`, built by `Nat.leRec` so that no
  cast across `m + (k - m) = k` is needed.
* `DividedPowers.TateResolution.chainColimit` — the colimit of the chain.
* `DividedPowers.TateResolution.chainColimitInclusion` — the morphism from the `n`-th stage
  of the chain into the colimit.

## Main results

* `DividedPowers.TateResolution.chainColimit_existsUnique_lift` — the universal property.
* `DividedPowers.TateResolution.chainColimit_exists_stage` — every element of the colimit
  comes from a stage, and `DividedPowers.TateResolution.chainColimit_mem_grade_iff` — every
  homogeneous element of the colimit comes from a homogeneous element of a stage.
* `DividedPowers.TateResolution.chainColimitInclusion_injective` — when every `step` is
  injective, so is every structure map.

## Implementation notes

`chainMap` is defined with `Nat.leRec` rather than by recursion on `k - m`. Recursion on the
difference produces a morphism `B m ⟶ B (m + (k - m))`, and transporting it along
`m + (k - m) = k` leaves an `Eq.mpr` in front of every application, which no `rw` can see
through. `Nat.leRec` recurses on the inequality itself and so lands in `B k` on the nose;
its two reduction rules `Nat.leRec_self` and `Nat.leRec_succ` give the identity and successor
equations directly. Proofs of `m ≤ k` need never be matched up, since they are proofs of a
proposition and so definitionally equal.

The `n`-th structure map into the colimit is the structure map of the stage `{n}` of the
reindexed diagram precomposed with `chainMap` along `n ≤ ({n} : Finset ℕ).sup id`. The
composite is used rather than the structure map alone because `({n} : Finset ℕ).sup id` is
*equal* to `n` but not definitionally so, and the extra `chainMap` costs nothing: it is the
identity up to the proof-irrelevant inequality.

## References

* [Stacks Project, Tag 0F4I](https://stacks.math.columbia.edu/tag/0F4I)
* [Stacks Project, Tag 09PS](https://stacks.math.columbia.edu/tag/09PS)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v z

attribute [local instance] GradedDPAlgebra.ring GradedDPAlgebra.algebra
  GradedDPAlgebra.graded GradedDPAlgebra.strict

attribute [local instance] gradedLimitGradedAlgebra gradedLimitStrictlyGradedComm

section Composition

variable {R : Type u} [CommRing R]

/-- Composition of morphisms of graded divided power algebras is associative. -/
public theorem GradedDPHom.comp_assoc {A : GradedDPAlgebra.{u, v} R}
    {B C D : GradedDPAlgebra.{u, v} R}
    (h : GradedDPHom C D) (g : GradedDPHom B C) (f : GradedDPHom A B) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  GradedDPHom.ext rfl

/-- The identity morphism of graded divided power algebras is a left unit for composition. -/
public theorem GradedDPHom.id_comp {A B : GradedDPAlgebra.{u, v} R} (f : GradedDPHom A B) :
    (GradedDPHom.id B).comp f = f :=
  GradedDPHom.ext (AlgHom.id_comp f.hom)

end Composition

section Chain

variable {R : Type u} [CommRing R] (B : ℕ → GradedDPAlgebra.{u, v} R)
  (step : ∀ n : ℕ, GradedDPHom (B n) (B (n + 1)))

/-- The transition morphism of the chain attached to an inequality `m ≤ k`: the composite of
the `step` morphisms from the `m`-th stage up to the `k`-th. -/
public noncomputable def chainMap {m : ℕ} : ∀ {k : ℕ}, m ≤ k → GradedDPHom (B m) (B k) :=
  Nat.leRec (GradedDPHom.id (B m)) fun {k} _ ih => (step k).comp ih

/-- The transition morphism along a reflexive inequality is the identity. -/
public theorem chainMap_self (m : ℕ) :
    chainMap B step (Nat.le_refl m) = GradedDPHom.id (B m) :=
  Nat.leRec_self _ _

/-- The transition morphism up to the successor stage is the last `step` after the previous
transition morphism. -/
public theorem chainMap_succ {m k : ℕ} (h : m ≤ k) (h' : m ≤ k + 1) :
    chainMap B step h' = (step k).comp (chainMap B step h) :=
  Nat.leRec_succ _ _ h

/-- The transition morphisms of the chain compose. -/
public theorem chainMap_trans {m k l : ℕ} (h₁ : m ≤ k) (h₂ : k ≤ l) :
    (chainMap B step h₂).comp (chainMap B step h₁) = chainMap B step (h₁.trans h₂) := by
  induction h₂ with
  | refl => rw [chainMap_self, GradedDPHom.id_comp]
  | step h ih =>
      rw [chainMap_succ B step h, chainMap_succ B step (h₁.trans h),
        GradedDPHom.comp_assoc, ih]

/-- The transition morphism along a reflexive inequality acts as the identity. -/
public theorem chainMap_hom_self (m : ℕ) (x : (B m).carrier) :
    (chainMap B step (Nat.le_refl m)).hom x = x := by
  rw [chainMap_self]
  rfl

/-- The transition morphisms of the chain compose, on elements. -/
public theorem chainMap_hom_trans {m k l : ℕ} (h₁ : m ≤ k) (h₂ : k ≤ l) (x : (B m).carrier) :
    (chainMap B step h₂).hom ((chainMap B step h₁).hom x) =
      (chainMap B step (h₁.trans h₂)).hom x :=
  congrArg (fun g : GradedDPHom (B m) (B l) => g.hom x) (chainMap_trans B step h₁ h₂)

/-- The chain reindexed over the finite subsets of `ℕ`: the stage at `S` is the stage of the
chain at the largest element of `S`. The finite subsets of `ℕ` are cofinal in the chain, so
this loses nothing, and it is the index shape the colimit machinery takes. -/
public noncomputable abbrev chainStage (S : Finset ℕ) : GradedDPAlgebra.{u, v} R :=
  B (S.sup id)

/-- The transition morphism of the reindexed diagram. -/
public noncomputable def chainStageMap (S T : Finset ℕ) (h : S ⊆ T) :
    GradedDPHom (chainStage B S) (chainStage B T) :=
  chainMap B step (Finset.sup_mono h)

/-- The reindexed diagram is a directed system. -/
public instance chainDirectedSystem :
    DirectedSystem (fun S : Finset ℕ => (chainStage B S).carrier)
      (fun S T h => (chainStageMap B step S T h).hom) where
  map_self := fun {_} x => chainMap_hom_self B step _ x
  map_map := fun {_ _ _} _ _ x => chainMap_hom_trans B step _ _ x

/-- The colimit of an `ω`-chain of graded divided power algebras. -/
public noncomputable abbrev chainColimit : GradedDPAlgebra.{u, v} R :=
  gradedDirectLimit (chainStage B) (chainStageMap B step)

/-- The structure morphism of the reindexed diagram into the colimit. -/
public noncomputable abbrev chainStageInclusion (S : Finset ℕ) :
    GradedDPHom (chainStage B S) (chainColimit B step) :=
  gradedDirectLimitInclusion (chainStage B) (chainStageMap B step) S

/-- The morphism from the `n`-th stage of the chain into the colimit. -/
public noncomputable def chainColimitInclusion (n : ℕ) :
    GradedDPHom (B n) (chainColimit B step) :=
  (chainStageInclusion B step {n}).comp
    (chainMap B step (show n ≤ ({n} : Finset ℕ).sup id from
      Finset.le_sup (f := id) (Finset.mem_singleton_self n)))

/-- Every structure morphism of the reindexed diagram, precomposed with a transition
morphism of the chain reaching its index, is the structure morphism of the chain. -/
public theorem chainStageInclusion_chainMap (n : ℕ) (S : Finset ℕ) (h : n ≤ S.sup id)
    (x : (B n).carrier) :
    (chainStageInclusion B step S).hom ((chainMap B step h).hom x) =
      (chainColimitInclusion B step n).hom x := by
  classical
  have hsing : n ≤ ({n} : Finset ℕ).sup id :=
    Finset.le_sup (f := id) (Finset.mem_singleton_self n)
  have hS : S ⊆ S ∪ {n} := Finset.subset_union_left
  have hT : ({n} : Finset ℕ) ⊆ S ∪ {n} := Finset.subset_union_right
  have key : ∀ (U : Finset ℕ) (hU : U ⊆ S ∪ {n}) (hm : n ≤ U.sup id),
      (chainStageInclusion B step U).hom ((chainMap B step hm).hom x) =
        (chainStageInclusion B step (S ∪ {n})).hom
          ((chainMap B step (hm.trans (Finset.sup_mono hU))).hom x) := by
    intro U hU hm
    rw [← chainMap_hom_trans B step hm (Finset.sup_mono hU)]
    exact (gradedLimitInclusion_map (chainStage B) (chainStageMap B step) hU _).symm
  show (chainStageInclusion B step S).hom ((chainMap B step h).hom x) =
    (chainStageInclusion B step {n}).hom ((chainMap B step hsing).hom x)
  rw [key S hS h, key {n} hT hsing]

/-- The structure morphisms of the chain are compatible with its transition morphisms. -/
public theorem chainColimitInclusion_chainMap {n m : ℕ} (h : n ≤ m) (x : (B n).carrier) :
    (chainColimitInclusion B step m).hom ((chainMap B step h).hom x) =
      (chainColimitInclusion B step n).hom x := by
  have hsing : m ≤ ({m} : Finset ℕ).sup id :=
    Finset.le_sup (f := id) (Finset.mem_singleton_self m)
  rw [chainColimitInclusion]
  show (chainStageInclusion B step {m}).hom
      ((chainMap B step hsing).hom ((chainMap B step h).hom x)) = _
  rw [chainMap_hom_trans B step h hsing]
  exact chainStageInclusion_chainMap B step n {m} (h.trans hsing) x

/-- The structure morphisms of the chain are compatible with the `step` morphisms. -/
public theorem chainColimitInclusion_step (n : ℕ) (x : (B n).carrier) :
    (chainColimitInclusion B step (n + 1)).hom ((step n).hom x) =
      (chainColimitInclusion B step n).hom x := by
  have hstep : ((step n).comp (chainMap B step (Nat.le_refl n))).hom x = (step n).hom x := by
    show (step n).hom ((chainMap B step (Nat.le_refl n)).hom x) = _
    rw [chainMap_hom_self]
  rw [← hstep, ← chainMap_succ B step (Nat.le_refl n) (Nat.le_succ n)]
  exact chainColimitInclusion_chainMap B step (Nat.le_succ n) x

/-- A stage-wise family of functions compatible with the `step` morphisms is compatible with all
transition morphisms. -/
private theorem comp_chainMap_eq {M : Type*} (g : ∀ n : ℕ, (B n).carrier → M)
    (hg : ∀ (n : ℕ) (x : (B n).carrier), g (n + 1) ((step n).hom x) = g n x)
    {m k : ℕ} (h : m ≤ k) (x : (B m).carrier) : g k ((chainMap B step h).hom x) = g m x := by
  induction h with
  | refl => rw [chainMap_hom_self]
  | step h ih => rw [chainMap_succ B step h, ← ih]; exact hg _ _

private theorem chainStageInclusion_eq_chainColimitInclusion (S : Finset ℕ)
    (y : (chainStage B S).carrier) :
    (chainStageInclusion B step S).hom y =
      (chainColimitInclusion B step (S.sup id)).hom y := by
  rw [← chainStageInclusion_chainMap B step (S.sup id) S (Nat.le_refl _) y, chainMap_hom_self]

/-- Every element of the colimit comes from a stage of the chain. -/
public theorem chainColimit_exists_stage (x : (chainColimit B step).carrier) :
    ∃ (n : ℕ) (y : (B n).carrier), (chainColimitInclusion B step n).hom y = x := by
  induction x using DirectLimit.induction (fun S T h => (chainStageMap B step S T h).hom) with
  | ih S y =>
      refine ⟨S.sup id, y, ?_⟩
      exact (chainStageInclusion_eq_chainColimitInclusion B step S y).symm

/-- A homogeneous element of the colimit comes from a homogeneous element of the same degree
at some stage of the chain. -/
public theorem chainColimit_mem_grade_iff (m : ℕ) (x : (chainColimit B step).carrier) :
    x ∈ (chainColimit B step).grade m ↔
      ∃ (n : ℕ) (y : (B n).carrier), y ∈ (B n).grade m ∧
        (chainColimitInclusion B step n).hom y = x := by
  refine ⟨?_, fun ⟨n, y, hy, hx⟩ => hx ▸ (chainColimitInclusion B step n).map_grade m y hy⟩
  rintro ⟨S, y, hy, rfl⟩
  refine ⟨S.sup id, y, hy, ?_⟩
  exact (chainStageInclusion_eq_chainColimitInclusion B step S y).symm

/-- The divided powers of the colimit restrict to those of each stage of the chain. -/
public theorem chainColimitInclusion_dpow (n k : ℕ) (x : (B n).carrier)
    (hx : x ∈ positiveEvenPart (B n).grade) :
    (chainColimit B step).gamma.dpow k ((chainColimitInclusion B step n).hom x) =
      (chainColimitInclusion B step n).hom ((B n).gamma.dpow k x) :=
  (chainColimitInclusion B step n).map_dpow k x hx

/-- When every transition morphism of the chain is injective, so is every transition
morphism of the reindexed diagram. -/
public theorem chainMap_injective (hstep : ∀ n, Function.Injective (step n).hom)
    {m k : ℕ} (h : m ≤ k) : Function.Injective (chainMap B step h).hom := by
  induction h with
  | refl => intro x y hxy; rwa [chainMap_hom_self, chainMap_hom_self] at hxy
  | step h ih =>
      intro x y hxy
      rw [chainMap_succ B step h] at hxy
      exact ih (hstep _ hxy)

/-- When every transition morphism of the chain is injective, so is every structure morphism
into the colimit. -/
public theorem chainColimitInclusion_injective (hstep : ∀ n, Function.Injective (step n).hom)
    (n : ℕ) : Function.Injective (chainColimitInclusion B step n).hom := by
  have hsing : n ≤ ({n} : Finset ℕ).sup id :=
    Finset.le_sup (f := id) (Finset.mem_singleton_self n)
  have hstage : Function.Injective (chainStageInclusion B step ({n} : Finset ℕ)).hom :=
    DirectLimit.mk_injective (fun S T h => (chainStageMap B step S T h).hom)
      (fun _ _ h => chainMap_injective B step hstep (Finset.sup_mono h)) {n}
  intro x y hxy
  refine chainMap_injective B step hstep hsing (hstage ?_)
  exact hxy

/-- The universal property of the colimit of the chain: a family of morphisms out of the
stages which is compatible with the `step` morphisms extends uniquely to a morphism out of
the colimit. -/
public theorem chainColimit_existsUnique_lift (D : GradedDPAlgebra.{u, z} R)
    (g : ∀ n : ℕ, GradedDPHom (B n) D)
    (hg : ∀ (n : ℕ) (x : (B n).carrier), (g (n + 1)).hom ((step n).hom x) = (g n).hom x) :
    ∃! F : GradedDPHom (chainColimit B step) D,
      ∀ (n : ℕ) (x : (B n).carrier),
        F.hom ((chainColimitInclusion B step n).hom x) = (g n).hom x := by
  have hchain := fun {m k : ℕ} (h : m ≤ k) (x : (B m).carrier) =>
    comp_chainMap_eq B step (fun n => (g n).hom) hg h x
  obtain ⟨F, hF, hFuniq⟩ := gradedDirectLimit_existsUnique_lift (chainStage B)
    (chainStageMap B step) D (fun S => g (S.sup id))
    (fun _ _ h x => hchain (Finset.sup_mono h) x)
  refine ⟨F, ?_, ?_⟩
  · intro n x
    rw [chainColimitInclusion]
    show F.hom ((chainStageInclusion B step {n}).hom ((chainMap B step _).hom x)) = _
    rw [hF {n}, hchain]
  · intro F' hF'
    refine hFuniq F' ?_
    intro S y
    rw [chainStageInclusion_eq_chainColimitInclusion]
    exact hF' (S.sup id) y

/-- The structure morphism of the reindexed diagram, read as a morphism of the chain. -/
public theorem chainStageInclusion_eq (S : Finset ℕ) (y : (chainStage B S).carrier) :
    (chainStageInclusion B step S).hom y =
      (chainColimitInclusion B step (S.sup id)).hom y := by
  exact chainStageInclusion_eq_chainColimitInclusion B step S y

/-- The additive analogue of `DividedPowers.TateResolution.chainColimit_existsUnique_lift`: a
family of additive maps out of the stages of the chain which is compatible with the `step`
morphisms extends uniquely to an additive map out of the colimit. This is the form a derivation
needs, a derivation not being a ring homomorphism. -/
public theorem chainColimit_existsUnique_addHom {M : Type z} [AddCommGroup M]
    (g : ∀ n : ℕ, (B n).carrier →+ M)
    (hg : ∀ (n : ℕ) (x : (B n).carrier), g (n + 1) ((step n).hom x) = g n x) :
    ∃! G : (chainColimit B step).carrier →+ M,
      ∀ (n : ℕ) (x : (B n).carrier),
        G ((chainColimitInclusion B step n).hom x) = g n x := by
  have hchain := fun {m k : ℕ} (h : m ≤ k) (x : (B m).carrier) =>
    comp_chainMap_eq B step (fun n => g n) hg h x
  let G : (chainColimit B step).carrier →+ M :=
    { toFun := DirectLimit.lift (fun S T h => (chainStageMap B step S T h).hom)
        (fun S y => g (S.sup id) y) (fun _ _ h y => (hchain (Finset.sup_mono h) y).symm)
      map_zero' := DirectLimit.lift_zero _ _
      map_add' := DirectLimit.lift_add _ _ }
  have hG : ∀ (n : ℕ) (x : (B n).carrier),
      G ((chainColimitInclusion B step n).hom x) = g n x := fun _ x => hchain _ x
  refine ⟨G, hG, ?_⟩
  intro G' hG'
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨n, y, rfl⟩ := chainColimit_exists_stage B step x
  rw [hG' n y, hG n y]

end Chain

end DividedPowers.TateResolution

end
