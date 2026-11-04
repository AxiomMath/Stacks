module

public import StacksFrontier.Deformation.Formal.MinimalVersal.Helpers

/-!
# The minimal stages of a formal object

Under Schlessinger's condition (S1) one can choose, level by level, a minimal descent object of
each level of a formal object so that the pushforward of each stage along the transition morphism
is the preceding stage. These choices and their transition morphisms are the input for the tower
of subalgebras whose inverse limit is the smallest base.

## Main definitions

* `Deformation.minimalPreimageData`: a minimal descent object at level `n + 1` whose pushforward
  along the transition map is isomorphic to a given minimal descent object at level `n`.
* `Deformation.minimalStages`: a choice, at each level of a formal object, of a minimal descent
  object of that level whose pushforward along the transition map is the previous one.
* `Deformation.stageComparisonIso`: the chosen isomorphism identifying the pushforward of the
  stage at level `n + 1` with the stage at level `n`.
* `Deformation.stageBaseTransition`: the transition map between the bases of two consecutive
  minimal stages.
* `Deformation.stageObjectTransition`: the transition morphism between two consecutive minimal
  stages, lying over `stageBaseTransition`.
* `Deformation.formalTransitionToZero`: the composite of the transition morphisms of a formal
  object from level `n` down to level `0`.
* `Deformation.formalTransitionToZeroBase`: the base map of `formalTransitionToZero`, from the
  `n`-th adic truncation to the zeroth.
* `Deformation.stageObjectToZero`: the composite of the transition morphisms of the minimal stages
  from level `n` down to level `0`.

## Main results

* `Deformation.minimalStages_spec`: the chosen minimal stages are minimal, and the pushforward of
  the stage at level `n + 1` along the transition map is isomorphic to the stage at level `n`.
* `Deformation.stageObjectTransition_map`: `stageObjectTransition` lies over `stageBaseTransition`
  by construction.
* `Deformation.stageObjectTransition_fac`: the transition morphisms of the minimal stages commute
  with their arrows into the levels of the formal object.
* `Deformation.formalTransitionToZeroBase_mk`: `formalTransitionToZeroBase` is the canonical map
  of quotients, computed on representatives.
* `Deformation.formalTransitionToZero_lift`: `formalTransitionToZero` lies over
  `formalTransitionToZeroBase`.

## References

* [Stacks Project, Tag 06T2](https://stacks.math.columbia.edu/tag/06T2)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u v w uF vF

namespace Deformation

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
variable {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}


section
variable [IsNoetherianRing Λ] [Module.Finite Λ k]
/-- A minimal descent object at level `n + 1` whose pushforward along the transition map is
isomorphic to a given minimal descent object at level `n`. -/
noncomputable def minimalPreimageData
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p) (n : ℕ)
    (X : DescentObject p (ξ.level n)) (hX : IsMinimalObject X) :
    {Y : DescentObject p (ξ.level (n + 1)) //
      IsMinimalObject Y ∧ Nonempty
        ((descentPushforward p hp (ξ.transition n)).functor.obj Y ≅ X)} := by
  classical
  let h := exists_minimal_preimage p hp hS1
    (ξ.transition n) (formal_transition_surjective ξ n) X hX
  exact ⟨Classical.choose h, (Classical.choose_spec h).1,
    (Classical.choose_spec h).2⟩



/-- A choice, at each level of a formal object, of a minimal descent object of that level whose
pushforward along the transition map is the previous one. -/
noncomputable def minimalStages
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p) : ∀ n, DescentObject p (ξ.level n) := by
  classical
  let stage : ∀ n, {Y : DescentObject p (ξ.level n) // IsMinimalObject Y} :=
    Nat.rec
      ⟨identityDescent (p := p) (ξ.level 0),
        identityDescent_isMinimal hp (ξ.level 0)
          (level_zero_maximalIdeal_eq_bot ξ)⟩
      (fun n prev =>
        ⟨(minimalPreimageData hp hS1 ξ n prev.1 prev.2).1,
          (minimalPreimageData hp hS1 ξ n prev.1 prev.2).2.1⟩)
  exact fun n => (stage n).1


/-- The chosen minimal stages are minimal, and the pushforward of the stage at level `n + 1` along
the transition map is isomorphic to the stage at level `n`. -/
theorem minimalStages_spec
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p) :
    (∀ n, IsMinimalObject (minimalStages hp hS1 ξ n)) ∧
    (∀ n, Nonempty
      ((descentPushforward p hp (ξ.transition n)).functor.obj
        (minimalStages hp hS1 ξ (n + 1)) ≅ minimalStages hp hS1 ξ n)) := by
  have h : ∀ n, IsMinimalObject (minimalStages hp hS1 ξ n) := fun n => by
    induction n with
    | zero => exact identityDescent_isMinimal hp (ξ.level 0) (level_zero_maximalIdeal_eq_bot ξ)
    | succ n ih => exact (minimalPreimageData hp hS1 ξ n _ ih).2.1
  exact ⟨h, fun n => (minimalPreimageData hp hS1 ξ n _ (h n)).2.2⟩

/-- The chosen isomorphism identifying the pushforward of the stage at level `n + 1` with the stage
at level `n`. -/
noncomputable def stageComparisonIso
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p) (n : ℕ) :
    (descentPushforward p hp (ξ.transition n)).functor.obj
      (minimalStages hp hS1 ξ (n + 1)) ≅ minimalStages hp hS1 ξ n :=
  Classical.choice ((minimalStages_spec hp hS1 ξ).2 n)

/-- The transition map between the bases of two consecutive minimal stages. -/
noncomputable def stageBaseTransition
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p) (n : ℕ) :
    p.obj (minimalStages hp hS1 ξ (n + 1)).obj.left ⟶
      p.obj (minimalStages hp hS1 ξ n).obj.left := by
  let D := descentPushforward p hp (ξ.transition n)
  exact p.map (D.inclusion (minimalStages hp hS1 ξ (n + 1)) ≫
    (stageComparisonIso hp hS1 ξ n).hom.hom.left)

/-- The transition morphism between two consecutive minimal stages, lying over
`stageBaseTransition`. -/
noncomputable def stageObjectTransition
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p) (n : ℕ) :
    (minimalStages hp hS1 ξ (n + 1)).obj.left ⟶
      (minimalStages hp hS1 ξ n).obj.left := by
  let D := descentPushforward p hp (ξ.transition n)
  exact D.inclusion (minimalStages hp hS1 ξ (n + 1)) ≫
    (stageComparisonIso hp hS1 ξ n).hom.hom.left

/-- `stageObjectTransition` lies over `stageBaseTransition` by construction. -/
theorem stageObjectTransition_map
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p) (n : ℕ) :
    p.map (stageObjectTransition hp hS1 ξ n) =
      stageBaseTransition hp hS1 ξ n := rfl

/-- The transition morphisms of the minimal stages commute with their arrows into the levels of the
formal object. -/
theorem stageObjectTransition_fac
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p) (n : ℕ) :
    stageObjectTransition hp hS1 ξ n ≫ (minimalStages hp hS1 ξ n).obj.hom =
      (minimalStages hp hS1 ξ (n + 1)).obj.hom ≫ ξ.transition n := by
  simp only [stageObjectTransition, Category.assoc, Over.w (stageComparisonIso hp hS1 ξ n).hom.hom]
  exact (descentPushforward p hp (ξ.transition n)).inclusion_fac _

/-- The composite of the transition morphisms of a formal object from level `n` down to level `0`.
-/
noncomputable def formalTransitionToZero
    (ξ : FormalObject p) : ∀ n, ξ.level n ⟶ ξ.level 0
  | 0 => 𝟙 _
  | n + 1 => ξ.transition n ≫ formalTransitionToZero ξ n

/-- The base map of `formalTransitionToZero`, from the `n`-th adic truncation to the zeroth. -/
noncomputable def formalTransitionToZeroBase
    (ξ : FormalObject p) : ∀ n,
      AdicTruncation.obj ξ.base n ⟶ AdicTruncation.obj ξ.base 0
  | 0 => 𝟙 _
  | n + 1 => AdicTruncation.transition ξ.base n ≫ formalTransitionToZeroBase ξ n

omit [IsNoetherianRing Λ] [Module.Finite Λ k] in
/-- `formalTransitionToZeroBase` is the canonical map of quotients, computed on representatives. -/
theorem formalTransitionToZeroBase_mk
    (ξ : FormalObject p) (n : ℕ) (r : ξ.base) :
    (formalTransitionToZeroBase ξ n).hom
        (Ideal.Quotient.mk (AdicTruncation.ideal ξ.base n) r) =
      Ideal.Quotient.mk (AdicTruncation.ideal ξ.base 0) r := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (formalTransitionToZeroBase ξ n).hom
        (Ideal.Quotient.factorₐ Λ
          (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
          (Ideal.Quotient.mk (AdicTruncation.ideal ξ.base (n + 1)) r)) = _
      simp [ih]
      rfl

omit [IsNoetherianRing Λ] [Module.Finite Λ k] in
/-- `formalTransitionToZero` lies over `formalTransitionToZeroBase`. -/
theorem formalTransitionToZero_lift
    (ξ : FormalObject p) (n : ℕ) :
    p.IsHomLift (formalTransitionToZeroBase ξ n) (formalTransitionToZero ξ n) := by
  induction n with
  | zero =>
      change p.IsHomLift (𝟙 (AdicTruncation.obj ξ.base 0)) (𝟙 (ξ.level 0))
      exact IsHomLift.id (ξ.level_eq 0)
  | succ n ih =>
      dsimp [formalTransitionToZero, formalTransitionToZeroBase]
      exact @IsHomLift.comp _ _ _ _ p _ _ _ _ _ _
        (AdicTruncation.transition ξ.base n)
        (formalTransitionToZeroBase ξ n) (ξ.transition n)
        (formalTransitionToZero ξ n) (ξ.transition_lift n) ih

/-- The composite of the transition morphisms of the minimal stages from level `n` down to level
`0`. -/
noncomputable def stageObjectToZero
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p) : ∀ n,
      (minimalStages hp hS1 ξ n).obj.left ⟶
        (minimalStages hp hS1 ξ 0).obj.left
  | 0 => 𝟙 _
  | n + 1 => stageObjectTransition hp hS1 ξ n ≫ stageObjectToZero hp hS1 ξ n

end

end Deformation

end
