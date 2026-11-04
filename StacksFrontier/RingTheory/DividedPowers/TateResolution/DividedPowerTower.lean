module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.ChainColimit
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableDerivation

/-! # The `ω`-tower of set-variable divided power extensions

Tag 0F4I adjoins to a graded divided power algebra a set of variables of a *single* positive
degree. A divided power polynomial algebra has variables in every positive degree, so it is
obtained by iterating that construction: one step for each degree, the step at `n + 1`
adjoining a prescribed set `Jdx n` of variables of degree `n + 1`, and the whole algebra being
the colimit of the resulting `ω`-chain.

This file performs that iteration. Each step produces a *fresh* carrier with fresh `Ring`,
`Algebra`, `GradedAlgebra`, `IsStrictlyGradedComm` and `DividedPowerStructure` structures, which
is why the stages are carried as `DividedPowers.TateResolution.GradedDPAlgebra` bundles: the
instances depend on the stage index and so cannot be supplied by the ambient instance cache.

## Main definitions

* `DividedPowers.TateResolution.towerStage` — the `n`-th stage of the tower.
* `DividedPowers.TateResolution.towerStep` — the morphism from the `n`-th stage to the next.
* `DividedPowers.TateResolution.towerGenerator` — the variables of degree `n + 1`, as elements
  of the stage `n + 1`.
* `DividedPowers.TateResolution.towerColimit` — the colimit of the tower, with
  `DividedPowers.TateResolution.towerInclusion` the morphism out of each stage.

## Main results

* `DividedPowers.TateResolution.exists_setVariableExtension_bundled` — the construction of
  Tag 0F4I restated for `GradedDPAlgebra` bundles, with its output packaged as an
  `DividedPowers.TateResolution.IsSetVariableExtension` and its universal property as a
  statement about `GradedDPAlgebra` morphisms.
* `DividedPowers.TateResolution.towerStage_isSetVariableExtension` — each step of the tower is
  a set-variable divided power extension in the sense of
  `DividedPowers.TateResolution.IsSetVariableExtension`, which is the hypothesis under which a
  graded derivation extends across it.
* `DividedPowers.TateResolution.towerColimit_existsUnique_lift` — the universal property of
  the colimit of the tower: a morphism out of the base together with a homogeneous value for
  each variable determines a unique morphism out of the colimit.

## Implementation notes

The universal property of one step is available only for targets in a *fixed* universe, because
`DividedPowers.TateResolution.exists_setVariableDividedPowerExtension` quantifies the target
universe inside the existential, so the stage chosen from it depends on that universe. The
tower is therefore stated with the target universe `z` appearing in the universe of its stages,
`max u v z`: that way `z` is visible in the type of `towerStage` and two occurrences of the
tower in one development cannot silently pick different stages. The cost is one `ULift` on the
index types at the point of application, which is harmless — the application wants a bijection
of index sets anyway.

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

section Bundled

variable {R : Type u} [CommRing R]

/-- The set-variable divided power extension of Tag 0F4I, restated for `GradedDPAlgebra`
bundles: adjoining a set `J` of variables of a single positive degree `d` to `A` produces a
graded divided power algebra `C`, a coefficient morphism, and a family of homogeneous variables
presenting `C` as a set-variable extension of `A`, with the universal property that a morphism
out of `A` together with a homogeneous value for each variable extends uniquely.

The universe of `C` is inflated to include the universe `z` of the targets of the universal
property. That is not needed for the construction — `C` could be built in `max u v w` — but it
makes `z` visible in the statement, which is what lets the stage be *chosen* from this
existential and still be independent of how the universal property is later used. -/
public theorem exists_setVariableExtension_bundled
    (A : GradedDPAlgebra.{u, max u v z} R) (J : Type v) (d : ℕ) (hd : 0 < d) :
    ∃ (C : GradedDPAlgebra.{u, max u v z} R) (ι : GradedDPHom A C) (T : J → C.carrier),
      IsSetVariableExtension A.grade A.gamma C.grade C.gamma ι.hom T d hd ∧
      ∀ (D : GradedDPAlgebra.{u, z} R) (g : GradedDPHom A D) (t : J → D.carrier),
        (∀ j : J, t j ∈ D.grade d) →
        ∃! F : GradedDPHom C D,
          (∀ a : A.carrier, F.hom (ι.hom a) = g.hom a) ∧ (∀ j : J, F.hom (T j) = t j) := by
  obtain ⟨C, ringC, algebraC, Cᵢ, gradedC, strictC, δ, ι, T, hinj, hgrade, hdpow, hgen,
    hfin, hsucc, hup⟩ :=
    exists_setVariableDividedPowerExtension.{u, max u v z, v, z} A.grade A.gamma J
      (fun _ => d) (fun _ => hd)
  let _ : Ring C := ringC
  let _ : Algebra R C := algebraC
  let _ : GradedAlgebra Cᵢ := gradedC
  let _ : IsStrictlyGradedComm Cᵢ := strictC
  let C₀ : GradedDPAlgebra.{u, max u v z} R := ⟨C, ringC, algebraC, Cᵢ, gradedC, strictC, δ⟩
  refine ⟨C₀, ⟨ι, hgrade, hdpow⟩, T, ⟨hinj, hgrade, hdpow, hgen, hfin, ?_⟩, ?_⟩
  · -- The successor clause of `exists_setVariableDividedPowerExtension` additionally records
    -- that the algebra structure on a finite stage restricts the one on `C`.
    -- `IsSetVariableExtension.successor` does not ask for that, so it is discarded here.
    intro S j hj
    obtain ⟨aS, -, Sᵢ, gS, cS, δS, hstage⟩ := hsucc S j hj
    exact ⟨aS, Sᵢ, gS, cS, δS, hstage⟩
  intro D g t ht
  obtain ⟨F, hF, hFuniq⟩ := hup (D := D.carrier) D.grade D.gamma g.hom t g.map_grade
    g.map_dpow ht
  refine ⟨⟨F, hF.2.2.1, hF.2.2.2⟩, ⟨hF.1, hF.2.1⟩, ?_⟩
  intro F' hF'
  exact GradedDPHom.ext (hFuniq F'.hom ⟨hF'.1, hF'.2, F'.map_grade, F'.map_dpow⟩)

end Bundled

section Tower

variable {R : Type u} [CommRing R] (A₀ : GradedDPAlgebra.{u, max u v z} R) (Jdx : ℕ → Type v)

/-- The `n`-th stage of the `ω`-tower: the base `A₀` with the variables of each degree up to
`n` adjoined. -/
public noncomputable def towerStage : ℕ → GradedDPAlgebra.{u, max u v z} R
  | 0 => A₀
  | n + 1 =>
      (exists_setVariableExtension_bundled.{u, v, z} (towerStage n) (Jdx n) (n + 1)
        n.succ_pos).choose

/-- The zeroth stage of the tower is its base. -/
@[simp]
public theorem towerStage_zero : towerStage A₀ Jdx 0 = A₀ := rfl

/-- The morphism from the `n`-th stage of the tower to the next, adjoining the variables of
degree `n + 1`. -/
public noncomputable def towerStep (n : ℕ) :
    GradedDPHom (towerStage A₀ Jdx n) (towerStage A₀ Jdx (n + 1)) :=
  (exists_setVariableExtension_bundled.{u, v, z} (towerStage A₀ Jdx n) (Jdx n) (n + 1)
    n.succ_pos).choose_spec.choose

/-- The variables of degree `n + 1`, as elements of the stage `n + 1`. -/
public noncomputable def towerGenerator (n : ℕ) (j : Jdx n) :
    (towerStage A₀ Jdx (n + 1)).carrier :=
  (exists_setVariableExtension_bundled.{u, v, z} (towerStage A₀ Jdx n) (Jdx n) (n + 1)
    n.succ_pos).choose_spec.choose_spec.choose j

/-- Each step of the tower is a set-variable divided power extension in the sense of
`DividedPowers.TateResolution.IsSetVariableExtension`. This is the hypothesis under which a
graded derivation of a stage extends across the step. -/
public theorem towerStage_isSetVariableExtension (n : ℕ) :
    IsSetVariableExtension (towerStage A₀ Jdx n).grade (towerStage A₀ Jdx n).gamma
      (towerStage A₀ Jdx (n + 1)).grade (towerStage A₀ Jdx (n + 1)).gamma
      (towerStep A₀ Jdx n).hom (towerGenerator A₀ Jdx n) (n + 1) n.succ_pos :=
  (exists_setVariableExtension_bundled.{u, v, z} (towerStage A₀ Jdx n) (Jdx n) (n + 1)
    n.succ_pos).choose_spec.choose_spec.choose_spec.1

/-- The universal property of one step of the tower. -/
public theorem towerStep_existsUnique_lift (n : ℕ) (D : GradedDPAlgebra.{u, z} R)
    (g : GradedDPHom (towerStage A₀ Jdx n) D) (t : Jdx n → D.carrier)
    (ht : ∀ j : Jdx n, t j ∈ D.grade (n + 1)) :
    ∃! F : GradedDPHom (towerStage A₀ Jdx (n + 1)) D,
      (∀ a : (towerStage A₀ Jdx n).carrier, F.hom ((towerStep A₀ Jdx n).hom a) = g.hom a) ∧
        (∀ j : Jdx n, F.hom (towerGenerator A₀ Jdx n j) = t j) :=
  (exists_setVariableExtension_bundled.{u, v, z} (towerStage A₀ Jdx n) (Jdx n) (n + 1)
    n.succ_pos).choose_spec.choose_spec.choose_spec.2 D g t ht

/-- Each step of the tower is injective: it is the coefficient map of a set-variable
extension. -/
public theorem towerStep_injective (n : ℕ) :
    Function.Injective (towerStep A₀ Jdx n).hom :=
  (towerStage_isSetVariableExtension A₀ Jdx n).coefficient_injective

/-- Each variable of degree `n + 1` is homogeneous of degree `n + 1`. -/
public theorem towerGenerator_mem (n : ℕ) (j : Jdx n) :
    towerGenerator A₀ Jdx n j ∈ (towerStage A₀ Jdx (n + 1)).grade (n + 1) :=
  (towerStage_isSetVariableExtension A₀ Jdx n).generator_mem j

/-- The colimit of the `ω`-tower: the graded divided power algebra obtained from `A₀` by
adjoining, for every `n`, the variables `Jdx n` in degree `n + 1`. -/
public noncomputable abbrev towerColimit : GradedDPAlgebra.{u, max u v z} R :=
  chainColimit (towerStage A₀ Jdx) (towerStep A₀ Jdx)

/-- The morphism from the `n`-th stage of the tower into its colimit. -/
public noncomputable abbrev towerInclusion (n : ℕ) :
    GradedDPHom (towerStage A₀ Jdx n) (towerColimit A₀ Jdx) :=
  chainColimitInclusion (towerStage A₀ Jdx) (towerStep A₀ Jdx) n

/-- The coefficient morphism of the tower: the inclusion of its base. -/
public noncomputable abbrev towerCoefficient : GradedDPHom A₀ (towerColimit A₀ Jdx) :=
  towerInclusion A₀ Jdx 0

/-- The variables of the tower, as elements of its colimit. -/
public noncomputable def towerVariable (n : ℕ) (j : Jdx n) : (towerColimit A₀ Jdx).carrier :=
  (towerInclusion A₀ Jdx (n + 1)).hom (towerGenerator A₀ Jdx n j)

/-- Each variable of the tower is homogeneous of its prescribed degree. -/
public theorem towerVariable_mem (n : ℕ) (j : Jdx n) :
    towerVariable A₀ Jdx n j ∈ (towerColimit A₀ Jdx).grade (n + 1) :=
  (towerInclusion A₀ Jdx (n + 1)).map_grade (n + 1) _ (towerGenerator_mem A₀ Jdx n j)

/-- Every structure morphism of the tower is injective, so in particular the colimit contains
its base. -/
public theorem towerInclusion_injective (n : ℕ) :
    Function.Injective (towerInclusion A₀ Jdx n).hom :=
  chainColimitInclusion_injective (towerStage A₀ Jdx) (towerStep A₀ Jdx)
    (towerStep_injective A₀ Jdx) n

/-- The universal property of the colimit of the tower: a morphism out of the base together
with a homogeneous value of degree `n + 1` for each variable of degree `n + 1` extends
uniquely to a morphism out of the colimit. -/
public theorem towerColimit_existsUnique_lift (D : GradedDPAlgebra.{u, z} R)
    (g : GradedDPHom A₀ D) (t : (n : ℕ) → Jdx n → D.carrier)
    (ht : ∀ (n : ℕ) (j : Jdx n), t n j ∈ D.grade (n + 1)) :
    ∃! F : GradedDPHom (towerColimit A₀ Jdx) D,
      (∀ a : A₀.carrier, F.hom ((towerCoefficient A₀ Jdx).hom a) = g.hom a) ∧
        (∀ (n : ℕ) (j : Jdx n), F.hom (towerVariable A₀ Jdx n j) = t n j) := by
  classical
  -- The family of morphisms out of the stages, built by recursion on the stage.
  have hlift := fun (k : ℕ) (Gk : GradedDPHom (towerStage A₀ Jdx k) D) =>
    towerStep_existsUnique_lift A₀ Jdx k D Gk (t k) (ht k)
  let G : (n : ℕ) → GradedDPHom (towerStage A₀ Jdx n) D := fun n => Nat.rec g
    (fun k Gk => (hlift k Gk).choose) n
  have hGzero : G 0 = g := rfl
  have hGstep : ∀ (k : ℕ) (x : (towerStage A₀ Jdx k).carrier),
      (G (k + 1)).hom ((towerStep A₀ Jdx k).hom x) = (G k).hom x := fun k =>
    (hlift k (G k)).choose_spec.1.1
  have hGgen : ∀ (k : ℕ) (j : Jdx k),
      (G (k + 1)).hom (towerGenerator A₀ Jdx k j) = t k j := fun k =>
    (hlift k (G k)).choose_spec.1.2
  obtain ⟨F, hF, hFuniq⟩ := chainColimit_existsUnique_lift (towerStage A₀ Jdx)
    (towerStep A₀ Jdx) D G hGstep
  refine ⟨F, ⟨fun a => (hF 0 a).trans (congrArg (fun k : GradedDPHom A₀ D => k.hom a) hGzero),
    fun n j => (hF (n + 1) _).trans (hGgen n j)⟩, ?_⟩
  intro F' hF'
  refine hFuniq F' ?_
  -- A morphism out of the colimit restricting correctly on the base and the variables
  -- restricts to `G n` on every stage, by induction on `n` and the universal property of the
  -- step.
  have key : ∀ (n : ℕ) (x : (towerStage A₀ Jdx n).carrier),
      F'.hom ((towerInclusion A₀ Jdx n).hom x) = (G n).hom x := by
    intro n
    induction n with
    | zero => intro x; exact hF'.1 x
    | succ k ih =>
        let F'' : GradedDPHom (towerStage A₀ Jdx (k + 1)) D :=
          F'.comp (towerInclusion A₀ Jdx (k + 1))
        have hF''step : ∀ x : (towerStage A₀ Jdx k).carrier,
            F''.hom ((towerStep A₀ Jdx k).hom x) = (G k).hom x := by
          intro x
          show F'.hom ((towerInclusion A₀ Jdx (k + 1)).hom ((towerStep A₀ Jdx k).hom x)) = _
          rw [chainColimitInclusion_step (towerStage A₀ Jdx) (towerStep A₀ Jdx) k x]
          exact ih x
        have hF''gen : ∀ j : Jdx k, F''.hom (towerGenerator A₀ Jdx k j) = t k j :=
          fun j => hF'.2 k j
        have huniq := (hlift k (G k)).unique ⟨hF''step, hF''gen⟩ ⟨hGstep k, hGgen k⟩
        intro x
        exact congrArg (fun l : GradedDPHom (towerStage A₀ Jdx (k + 1)) D => l.hom x) huniq
  exact key

end Tower

end DividedPowers.TateResolution

end
