module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.ChainColimit
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.TowerPresentation

/-! # A chain of set-variable divided power extensions

`StacksFrontier/RingTheory/DividedPowers/TateResolution/ChainColimit.lean` builds the colimit of an
`ω`-chain `B : ℕ → GradedDPAlgebra R` of graded divided power algebras from the transition
morphisms alone. Nothing in that file knows *why* one stage sits inside the next. This file adds
the one hypothesis that makes the colimit presentable — that each step is a set-variable divided
power extension of Tag 0F4I, in the sense of
`DividedPowers.TateResolution.IsSetVariableExtension` — and draws from it the two facts a
presentation of the colimit needs:

* the finite variable stages of the whole family of adjoined variables cover the colimit, and
* the colimit is free on its base together with its variables, for a target in **any** universe.

For the particular chain of
`StacksFrontier/RingTheory/DividedPowers/TateResolution/DividedPowerTower.lean` both are
`DividedPowers.TateResolution.towerColimit_finite_support` and
`DividedPowers.TateResolution.towerColimit_exists_gradedDPHom`. They are proved here with the
chain abstract, because a second chain — the one whose variables in degree `n + 1` are indexed by
the cycles of degree `n` of the `n`-th stage, which is Tate's construction of Tag 09PN — cannot be
obtained from `DividedPowers.TateResolution.towerStage`: that definition fixes the index types in
advance, while Tate's depend on the stage already built.

## Main results

* `DividedPowers.TateResolution.setVariableChain_finite_support` — the finite variable stages cover
  any graded divided power algebra exhausted by the stages of such a chain, and
  `DividedPowers.TateResolution.chainColimit_finite_support` — that statement at the colimit
  itself.
* `DividedPowers.TateResolution.chainColimit_exists_gradedDPHom` — the mapping property of the
  colimit, with the universe of the target free.

## Implementation notes

*Why the target universe of the mapping property must be free.* The universal property of one step
of `DividedPowers.TateResolution.towerStage` is
`DividedPowers.TateResolution.towerStep_existsUnique_lift`, and it is available only for targets in
the single universe that was fixed when the stage was chosen: the target universe is quantified
*inside* the existential of
`DividedPowers.TateResolution.exists_setVariableDividedPowerExtension`, hence occurs in the
universe of the stage. In particular it is never the universe of the colimit, so it cannot be used
to map the colimit into an algebra built out of the colimit's own carrier, which is exactly what
freeness needs. `DividedPowers.TateResolution.IsSetVariableExtension.existsUnique_ringHom` removes
this restriction: the recorded *shape* of the output determines the extension, and from it the
mapping property is proved with the target universe free. Assembling those steps along the chain by
`DividedPowers.TateResolution.chainColimit_existsUnique_lift`, whose target universe is free
already, gives `DividedPowers.TateResolution.chainColimit_exists_gradedDPHom` with the same
freedom.

*Why the covering statement is proved for an abstract bundle first.* The colimit's carrier is a
*reducible* abbreviation ending in a `DirectLimit`, so instance search unfolds it and picks up the
`DirectLimit` instances rather than the bundle's own; every unification of a `Subring` of the
colimit against a lemma then becomes expensive enough to exhaust the heartbeat budget.
`DividedPowers.TateResolution.setVariableChain_finite_support` therefore takes the target bundle,
the family of variables and its index type abstract — the bundle's own fields `grade` and `gamma`
are supplied where `inferInstance` would be written — and
`DividedPowers.TateResolution.chainColimit_finite_support` is one cheap instantiation of it.

## References

* [Stacks Project, Tag 0F4I](https://stacks.math.columbia.edu/tag/0F4I)
* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
* [Stacks Project, Tag 09PS](https://stacks.math.columbia.edu/tag/09PS)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w y z

section SetVariableChain

attribute [local instance] GradedDPAlgebra.ring GradedDPAlgebra.algebra
  GradedDPAlgebra.graded GradedDPAlgebra.strict

attribute [local instance] gradedLimitGradedAlgebra gradedLimitStrictlyGradedComm

variable {R : Type u} [CommRing R] (B : ℕ → GradedDPAlgebra.{u, v} R)
  (step : ∀ n : ℕ, GradedDPHom (B n) (B (n + 1))) (Jdx : ℕ → Type w)
  (gen : (n : ℕ) → Jdx n → (B (n + 1)).carrier) (deg : ℕ → ℕ) (hdeg : ∀ n : ℕ, 0 < deg n)
  (hext : ∀ n : ℕ, IsSetVariableExtension (B n).grade (B n).gamma (B (n + 1)).grade
    (B (n + 1)).gamma (step n).hom (gen n) (deg n) (hdeg n))

include hext in
/-- **Every stage of a chain of set-variable extensions maps into the union of the finite variable
stages.** The base lands there as a coefficient; each successor stage is generated over its
predecessor by the variables adjoined at that step and their divided powers, each of which is
accounted for by the family `TT` of all variables of the chain. -/
public theorem setVariableChain_mem_variableStageUnion (D : GradedDPAlgebra.{u, y} R)
    (incl : (n : ℕ) → GradedDPHom (B n) D) {K : ℕ → Type z}
    (TT : (Σ n : ℕ, K n) → D.carrier)
    (hTT : ∀ (n : ℕ) (j : Jdx n), ∃ k : Σ m : ℕ, K m,
      TT k = (incl (n + 1)).hom (gen n j))
    (hstep : ∀ (n : ℕ) (x : (B n).carrier),
      (incl (n + 1)).hom ((step n).hom x) = (incl n).hom x) :
    ∀ (n : ℕ) (b : (B n).carrier),
      (incl n).hom b ∈ variableStageUnion D.gamma (incl 0).hom TT := by
  intro n
  induction n with
  | zero =>
      intro b
      exact coefficient_mem_variableStageUnion D.gamma (incl 0).hom TT b
  | succ n ih =>
      choose k hk using hTT n
      exact setVariableExtension_map_mem_subring (B (n + 1)).gamma (gen n) (hext n)
        D.grade D.gamma (variableStageUnion D.gamma (incl 0).hom TT) (incl (n + 1)).hom
        (incl (n + 1)).map_dpow (fun a => by rw [hstep n a]; exact ih a)
        (fun j => hk j ▸ generator_mem_variableStageUnion D.gamma (incl 0).hom TT (k j))
        (fun j m => hk j ▸ dpow_generator_mem_variableStageUnion D.gamma (incl 0).hom TT (k j) m)

include hext in
/-- **The finite variable stages cover a graded divided power algebra exhausted by the stages of a
chain of set-variable extensions.** Stated for an abstract bundle rather than for the colimit: the
colimit's carrier is a reducible abbreviation for a `DirectLimit`, so instance search unfolds it
and every unification against a `Subring` of it becomes expensive. Proved here with the bundle a
variable, it is cheap to instantiate. -/
public theorem setVariableChain_finite_support (D : GradedDPAlgebra.{u, y} R)
    (incl : (n : ℕ) → GradedDPHom (B n) D) {K : ℕ → Type z}
    (TT : (Σ n : ℕ, K n) → D.carrier)
    (hTT : ∀ (n : ℕ) (j : Jdx n), ∃ k : Σ m : ℕ, K m,
      TT k = (incl (n + 1)).hom (gen n j))
    (hstep : ∀ (n : ℕ) (x : (B n).carrier),
      (incl (n + 1)).hom ((step n).hom x) = (incl n).hom x)
    (hcover : ∀ x : D.carrier, ∃ (n : ℕ) (b : (B n).carrier), (incl n).hom b = x)
    (x : D.carrier) :
    ∃ S : Finset (Σ n : ℕ, K n), x ∈ finiteVariableStage D.gamma (incl 0).hom TT S := by
  obtain ⟨n, b, hb⟩ := hcover x
  rw [← hb]
  exact setVariableChain_mem_variableStageUnion B step Jdx gen deg hdeg hext D incl TT hTT
    hstep n b

include hext in
/-- **The finite variable stages cover the colimit of a chain of set-variable extensions.** Every
element of the colimit comes from a stage of the chain, and each stage is generated over the
previous one by the variables adjoined at that step together with their divided powers. -/
public theorem chainColimit_finite_support {K : ℕ → Type z}
    (TT : (Σ n : ℕ, K n) → (chainColimit B step).carrier)
    (hTT : ∀ (n : ℕ) (j : Jdx n), ∃ k : Σ m : ℕ, K m,
      TT k = (chainColimitInclusion B step (n + 1)).hom (gen n j))
    (x : (chainColimit B step).carrier) :
    ∃ S : Finset (Σ n : ℕ, K n),
      x ∈ finiteVariableStage (chainColimit B step).gamma
        (chainColimitInclusion B step 0).hom TT S :=
  setVariableChain_finite_support B step Jdx gen deg hdeg hext (chainColimit B step)
    (chainColimitInclusion B step) TT hTT (chainColimitInclusion_step B step)
    (chainColimit_exists_stage B step) x

include hext in
/-- **The mapping property of the colimit of a chain of set-variable extensions, with the target
universe free.** A morphism out of the base of the chain together with a homogeneous value of the
prescribed degree for each adjoined variable extends to a morphism of graded divided power
algebras out of the colimit, for a target in *any* universe.

`DividedPowers.TateResolution.chainColimit_existsUnique_lift` already has a free target universe,
but it asks for a compatible family of morphisms out of *every* stage. Producing that family from
the base and the variables alone is what needs the step-by-step mapping property at a free target
universe, which is
`DividedPowers.TateResolution.IsSetVariableExtension.existsUnique_ringHom`. The extra generality
over a universal property read off a chosen stage is what lets the colimit be mapped into an
algebra built out of its own carrier, which is how freeness of the colimit over its base is
established. -/
public theorem chainColimit_exists_gradedDPHom (E : GradedDPAlgebra.{u, y} R)
    (g : GradedDPHom (B 0) E) (t : (n : ℕ) → Jdx n → E.carrier)
    (ht : ∀ (n : ℕ) (j : Jdx n), t n j ∈ E.grade (deg n)) :
    ∃ F : GradedDPHom (chainColimit B step) E,
      (∀ a : (B 0).carrier,
        F.hom ((chainColimitInclusion B step 0).hom a) = g.hom a) ∧
      (∀ (n : ℕ) (j : Jdx n),
        F.hom ((chainColimitInclusion B step (n + 1)).hom (gen n j)) = t n j) := by
  classical
  -- One step of the chain, by the mapping property of a set-variable extension.
  have hone : ∀ (k : ℕ) (Gk : GradedDPHom (B k) E),
      ∃ Gk1 : GradedDPHom (B (k + 1)) E,
        (∀ x : (B k).carrier, Gk1.hom ((step k).hom x) = Gk.hom x) ∧
        (∀ j : Jdx k, Gk1.hom (gen k j) = t k j) := by
    intro k Gk
    obtain ⟨g1, hg1, -⟩ := (hext k).existsUnique_ringHom E.grade E.gamma Gk.hom.toRingHom
      (t k) Gk.map_grade Gk.map_dpow (ht k)
    have hcomm : ∀ r : R, g1 (algebraMap R (B (k + 1)).carrier r) =
        algebraMap R E.carrier r := by
      intro r
      rw [← (step k).hom.commutes r, hg1.1]
      exact Gk.hom.commutes r
    exact ⟨⟨{ toRingHom := g1, commutes' := hcomm }, hg1.2.2.1, hg1.2.2.2⟩, hg1.1, hg1.2.1⟩
  choose stepHom hstepRestrict hstepGen using hone
  let G : (n : ℕ) → GradedDPHom (B n) E := fun n => Nat.rec g (fun k Gk => stepHom k Gk) n
  obtain ⟨F, hF, -⟩ := chainColimit_existsUnique_lift B step E G fun k => hstepRestrict k (G k)
  exact ⟨F, hF 0, fun n j => (hF (n + 1) _).trans (hstepGen n (G n) j)⟩

end SetVariableChain

end DividedPowers.TateResolution

end
