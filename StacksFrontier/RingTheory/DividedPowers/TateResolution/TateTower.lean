module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.ChainPresentation
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.DegreeZeroGrading
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.DividedPowerTower
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableDifferential
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableLowDegree

/-! # Tate's dependent `ω`-tower

Tag 0F4I adjoins a prescribed set of variables of one positive degree to a graded divided power
algebra, and `StacksFrontier/RingTheory/DividedPowers/TateResolution/DividedPowerTower.lean`
iterates that over a family `Jdx : ℕ → Type v` of index sets fixed *in advance*. Tate's
construction of Tag 09PN is not of that form: the variables adjoined in degree `n + 1` are
indexed by the cycles of degree `n` of the stage just built, so each index set is only available
once the previous stage exists.

This file performs the dependent iteration. A stage is carried as a
`DividedPowers.TateResolution.TateDatum` — a graded divided power algebra bundled with a
compatible differential — together with the family of cycles the next step is to kill, the two
packaged as a `DividedPowers.TateResolution.TateStageData`. One step is the construction of
Tag 0F4I followed by the set-indexed form of Tag 09PM: the cycle condition on the prescribed
values is exactly what makes the extended graded derivation square-zero, so the step returns a
`TateDatum` again and the recursion closes.

The variables adjoined in degree `n + 1` are indexed by **all** cycles of degree `n`, with the
prescribed value on a variable being the cycle indexing it. The differential of a new variable is
then its own index by construction, which is what makes acyclicity of the colimit a two-line
consequence of `DividedPowers.TateResolution.exists_chainColimitInclusion_eq_of_mem_grade` rather
than a homology computation. Degree zero is the one exception: there every element is a cycle, so
the family to be killed must be prescribed, and it is the base's ideal `I`.

## Main definitions

* `DividedPowers.TateResolution.TateDatum` — a graded divided power algebra with a compatible
  differential.
* `DividedPowers.TateResolution.TateStageData` — such a datum together with the family of
  degree-`n` cycles whose killing variables the next step adjoins.
* `DividedPowers.TateResolution.tateStage` — the `n`-th stage of the tower, with
  `DividedPowers.TateResolution.tateAlgebra`,
  `DividedPowers.TateResolution.tateDifferential`,
  `DividedPowers.TateResolution.tateStep`, `DividedPowers.TateResolution.tateIndex`,
  `DividedPowers.TateResolution.tateCycle` and
  `DividedPowers.TateResolution.tateGenerator` its components.
* `DividedPowers.TateResolution.tateBase` — the base of the tower: a commutative algebra
  concentrated in degree zero with the zero differential, with a prescribed ideal as the family
  of cycles to be killed.
* `DividedPowers.TateResolution.tateColimit` — the colimit of the tower, with
  `DividedPowers.TateResolution.tateInclusion` the morphism out of each stage and
  `DividedPowers.TateResolution.tateVariable` the variables as elements of the colimit.

## Main results

* `DividedPowers.TateResolution.exists_tateStep` — one step of Tate's construction: adjoining
  variables of degree `e + 1` killing a prescribed family of cycles of degree `e` produces a
  set-variable divided power extension carrying a differential extending the given one and
  sending each new variable to the cycle it kills.
* `DividedPowers.TateResolution.tateStage_isSetVariableExtension` — each step of the tower is a
  set-variable divided power extension of degree `n + 1`, which is the hypothesis every
  statement about a chain of such extensions takes.
* `DividedPowers.TateResolution.tateStep_differential` and
  `DividedPowers.TateResolution.tateGenerator_differential` — the steps commute with the
  differentials, and the differential of a variable of degree `n + 1` is the degree-`n` cycle it
  was chosen to kill.
* `DividedPowers.TateResolution.exists_tateCycle_eq` — every cycle of degree `n + 1` of the
  stage `n + 1` is prescribed, so a variable killing it is adjoined at the next step.
* `DividedPowers.TateResolution.exists_tateColimit_boundary_of_cycle` and
  `DividedPowers.TateResolution.exists_tateColimit_boundary_of_base` — the colimit is acyclic in
  positive degrees and its degree-zero homology is the base modulo the prescribed ideal, for any
  operator on the colimit restricting to the differential of each stage.

## Implementation notes

Every stage lives in the single universe `max u v`, with `u` the universe of the base ring: the
index set adjoined at a step is a subtype of the *previous stage's* carrier, so a tower whose
stages grew in universe would not typecheck at all. That is why the stages are bundled: their
`Ring`, `Algebra`, `GradedAlgebra`, `IsStrictlyGradedComm` and `DividedPowerStructure` data
depend on the stage index and cannot be supplied from the ambient instance cache.

The universal property of a step, which
`DividedPowers.TateResolution.exists_setVariableExtension_bundled` also provides, is
deliberately discarded here. It quantifies the universe of its targets *inside* the existential,
so a tower keeping it cannot have its universal property applied to anything built from its own
carrier. A consumer needing the mapping property should take it from
`DividedPowers.TateResolution.IsSetVariableExtension.existsUnique_ringHom`, which is proved from
the predicate recorded by `tateStage_isSetVariableExtension` with the target universe free.

Only the *existence* half of Tag 09PN is treated here: the index sets are all the cycles of a
degree rather than a finite generating family, so the resulting resolution is not degreewise
finite. The finiteness statement of Tag 09PN needs the variables to be chosen from finite
generating families of the cycles instead.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
* [Stacks Project, Tag 09PM](https://stacks.math.columbia.edu/tag/09PM)
* [Stacks Project, Tag 0F4I](https://stacks.math.columbia.edu/tag/0F4I)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v y

attribute [local instance] GradedDPAlgebra.ring GradedDPAlgebra.algebra
  GradedDPAlgebra.graded GradedDPAlgebra.strict

attribute [local instance] gradedLimitGradedAlgebra gradedLimitStrictlyGradedComm

/-- A *Tate datum*: a graded divided power algebra together with a differential making it a
differential graded algebra and compatible with its divided powers. This is the object Tate's
construction iterates, and the shape its output has in every degree of the tower. -/
public structure TateDatum (R : Type u) [CommRing R] where
  /-- The underlying graded divided power algebra. -/
  algebra : GradedDPAlgebra.{u, max u v} R
  /-- The differential, lowering degree by one. -/
  differential : algebra.carrier →ₗ[R] algebra.carrier
  /-- The differential makes the grading a differential graded algebra. -/
  dga : IsDifferentialGradedAlgebra algebra.grade differential
  /-- The divided powers are compatible with the differential. -/
  compatible : IsCompatibleWithDifferential algebra.gamma differential

attribute [local instance] TateDatum.dga TateDatum.compatible

section Zero

variable {R : Type u} [CommRing R]

/-- A graded divided power algebra carrying the zero differential is a Tate datum: the zero map
vanishes in degree zero, lowers every degree, squares to zero, and satisfies both the Leibniz
rule and the divided power formula because every term of each is zero. This is the base of
Tate's tower, where nothing of positive degree has been adjoined yet. -/
public def tateDatumOfZeroDifferential (A : GradedDPAlgebra.{u, max u v} R) :
    TateDatum.{u, v} R where
  algebra := A
  differential := 0
  dga :=
    { d_grade_zero := fun _ => rfl
      d_mem := fun _ => Submodule.zero_mem _
      d_sq_zero := fun _ => rfl
      leibniz := fun _ _ => by simp }
  compatible := { d_dpow := fun _ _ => by simp }

end Zero

section Step

variable {R : Type u} [CommRing R]

/-- **One step of Tate's construction.** Adjoining to a Tate datum `B` a set `J` of variables of
degree `e + 1`, with a cycle of degree `e` prescribed as the value of the differential on each,
produces a Tate datum `C` presenting `C` as a set-variable divided power extension of `B` whose
differential extends that of `B` and sends each new variable to the cycle it was chosen to kill.

The algebra, its grading and its divided powers come from Tag 0F4I; the differential comes from
the set-indexed form of Tag 09PM, whose cycle hypothesis is exactly what makes the extended
graded derivation square-zero and so a differential again. The universal property that Tag 0F4I
also provides is dropped, as the module docstring explains. -/
public theorem exists_tateStep (B : TateDatum.{u, v} R) (J : Type (max u v)) (e : ℕ)
    (ev : J → B.algebra.carrier) (hev : ∀ j : J, ev j ∈ B.algebra.grade e)
    (hcycle : ∀ j : J, B.differential (ev j) = 0) :
    ∃ (C : TateDatum.{u, v} R) (ι : GradedDPHom B.algebra C.algebra)
      (T : J → C.algebra.carrier),
      IsSetVariableExtension B.algebra.grade B.algebra.gamma C.algebra.grade C.algebra.gamma
          ι.hom T (e + 1) e.succ_pos ∧
        (∀ a : B.algebra.carrier, C.differential (ι.hom a) = ι.hom (B.differential a)) ∧
        (∀ j : J, C.differential (T j) = ι.hom (ev j)) := by
  obtain ⟨C, ι, T, hC, -⟩ :=
    exists_setVariableExtension_bundled.{u, max u v, max u v} B.algebra J (e + 1) e.succ_pos
  obtain ⟨D, hD, -⟩ := existsUnique_differential_setVariableExtension B.algebra.grade
    B.algebra.gamma C.grade C.gamma ι.hom T (e + 1) e.succ_pos hC B.differential ev hev hcycle
  exact ⟨⟨C, D, hD.1, hD.2.2.2⟩, ι, T, hC, hD.2.1, hD.2.2.1⟩

end Step

section Tower

variable {R : Type u} [CommRing R]

/-- A stage of Tate's tower: a Tate datum together with the family of degree-`n` cycles whose
killing variables the next step adjoins.

The family is carried alongside the datum, rather than computed from it, for two reasons. It is
what makes the recursion a plain recursion on `ℕ`: the index set of a step depends on the stage
below it, so it cannot be fixed in advance. And it is what lets degree zero differ from the
rest: there every element is a cycle, so killing all of them would make the tower resolve the
zero algebra instead of the prescribed quotient. -/
public structure TateStageData (R : Type u) [CommRing R] (n : ℕ) where
  /-- The algebra of the stage, with its divided powers and its differential. -/
  datum : TateDatum.{u, v} R
  /-- The index set of the variables of degree `n + 1` that the next step adjoins. -/
  kill : Type (max u v)
  /-- The degree-`n` cycle that the variable indexed by `j` is to kill. -/
  value : kill → datum.algebra.carrier
  /-- Each prescribed value is homogeneous of degree `n`. -/
  value_mem : ∀ j : kill, value j ∈ datum.algebra.grade n
  /-- Each prescribed value is a cycle, which is what makes the extended differential
  square-zero. -/
  value_cycle : ∀ j : kill, datum.differential (value j) = 0

/-- The Tate datum obtained from a stage by adjoining a variable of degree `n + 1` for each of
its prescribed degree-`n` cycles. -/
public noncomputable def tateStepDatum {n : ℕ} (B : TateStageData.{u, v} R n) :
    TateDatum.{u, v} R :=
  (exists_tateStep B.datum B.kill n B.value B.value_mem B.value_cycle).choose

/-- The coefficient morphism of one step: the inclusion of a stage into the stage obtained from
it by adjoining the killing variables. -/
public noncomputable def tateStepHom {n : ℕ} (B : TateStageData.{u, v} R n) :
    GradedDPHom B.datum.algebra (tateStepDatum B).algebra :=
  (exists_tateStep B.datum B.kill n B.value B.value_mem B.value_cycle).choose_spec.choose

/-- The variables of degree `n + 1` adjoined by one step, as elements of its target. -/
public noncomputable def tateStepGenerator {n : ℕ} (B : TateStageData.{u, v} R n) :
    B.kill → (tateStepDatum B).algebra.carrier :=
  (exists_tateStep B.datum B.kill n B.value
    B.value_mem B.value_cycle).choose_spec.choose_spec.choose

/-- One step of the tower is a set-variable divided power extension of degree `n + 1`. This is
the predicate under which a graded derivation extends across the step, under which the degrees
below `n + 1` are untouched, and from which the mapping property is re-provable with the target
universe free. -/
public theorem tateStepHom_isSetVariableExtension {n : ℕ} (B : TateStageData.{u, v} R n) :
    IsSetVariableExtension B.datum.algebra.grade B.datum.algebra.gamma
      (tateStepDatum B).algebra.grade (tateStepDatum B).algebra.gamma
      (tateStepHom B).hom (tateStepGenerator B) (n + 1) n.succ_pos :=
  (exists_tateStep B.datum B.kill n B.value
    B.value_mem B.value_cycle).choose_spec.choose_spec.choose_spec.1

/-- The coefficient morphism of one step commutes with the differentials, so a step of the tower
is a morphism of differential graded algebras. -/
public theorem tateStepHom_differential {n : ℕ} (B : TateStageData.{u, v} R n)
    (a : B.datum.algebra.carrier) :
    (tateStepDatum B).differential ((tateStepHom B).hom a) =
      (tateStepHom B).hom (B.datum.differential a) :=
  (exists_tateStep B.datum B.kill n B.value
    B.value_mem B.value_cycle).choose_spec.choose_spec.choose_spec.2.1 a

/-- The differential of an adjoined variable is the cycle it was chosen to kill. -/
public theorem tateStepGenerator_differential {n : ℕ} (B : TateStageData.{u, v} R n)
    (j : B.kill) :
    (tateStepDatum B).differential (tateStepGenerator B j) = (tateStepHom B).hom (B.value j) :=
  (exists_tateStep B.datum B.kill n B.value
    B.value_mem B.value_cycle).choose_spec.choose_spec.choose_spec.2.2 j

/-- The stage above a given one: the target of its step, with **all** of its degree-`n + 1`
cycles prescribed as the family to be killed next, each by itself.

Prescribing all of them is what makes the colimit acyclic in positive degrees with no homology
computation: a cycle of degree `n + 1` indexes a variable of degree `n + 2` whose differential
is, by `DividedPowers.TateResolution.tateStepGenerator_differential`, that very cycle. -/
public noncomputable def tateNext {n : ℕ} (B : TateStageData.{u, v} R n) :
    TateStageData.{u, v} R (n + 1) where
  datum := tateStepDatum B
  kill := {a : (tateStepDatum B).algebra.carrier //
    a ∈ (tateStepDatum B).algebra.grade (n + 1) ∧ (tateStepDatum B).differential a = 0}
  value := Subtype.val
  value_mem := fun j => j.2.1
  value_cycle := fun j => j.2.2

/-- The `n`-th stage of Tate's tower over the base `A₀`: the base with, for each `k < n`, a
variable of degree `k + 1` adjoined for every prescribed cycle of degree `k` of the stage `k`. -/
public noncomputable def tateStage (A₀ : TateStageData.{u, v} R 0) :
    (n : ℕ) → TateStageData.{u, v} R n
  | 0 => A₀
  | n + 1 => tateNext (tateStage A₀ n)

variable (A₀ : TateStageData.{u, v} R 0)

/-- The stage zero of the tower is the prescribed base. -/
public theorem tateStage_zero : tateStage A₀ 0 = A₀ := rfl

/-- The stage `n + 1` of the tower is obtained from the stage `n` by killing its prescribed
cycles. -/
public theorem tateStage_succ (n : ℕ) : tateStage A₀ (n + 1) = tateNext (tateStage A₀ n) := rfl

/-- The `n`-th stage of the tower, as a graded divided power algebra. -/
public noncomputable abbrev tateAlgebra (n : ℕ) : GradedDPAlgebra.{u, max u v} R :=
  (tateStage A₀ n).datum.algebra

/-- The differential of the `n`-th stage of the tower. -/
public noncomputable abbrev tateDifferential (n : ℕ) :
    (tateAlgebra A₀ n).carrier →ₗ[R] (tateAlgebra A₀ n).carrier :=
  (tateStage A₀ n).datum.differential

/-- The index set of the variables of degree `n + 1` of the tower: for `n = 0` the prescribed
family of the base, and for positive `n` all the cycles of degree `n` of the stage `n`. -/
public abbrev tateIndex (n : ℕ) : Type (max u v) := (tateStage A₀ n).kill

/-- The degree-`n` cycle of the `n`-th stage that the variable indexed by `j` kills. -/
public noncomputable abbrev tateCycle (n : ℕ) (j : tateIndex A₀ n) :
    (tateAlgebra A₀ n).carrier := (tateStage A₀ n).value j

/-- The morphism from the `n`-th stage of the tower to the next, adjoining the variables of
degree `n + 1`. -/
public noncomputable def tateStep (n : ℕ) :
    GradedDPHom (tateAlgebra A₀ n) (tateAlgebra A₀ (n + 1)) :=
  tateStepHom (tateStage A₀ n)

/-- The variables of degree `n + 1` of the tower, as elements of its stage `n + 1`. -/
public noncomputable def tateGenerator (n : ℕ) (j : tateIndex A₀ n) :
    (tateAlgebra A₀ (n + 1)).carrier :=
  tateStepGenerator (tateStage A₀ n) j

/-- Each step of the tower is a set-variable divided power extension of degree `n + 1`. This is
the hypothesis every statement about a chain of such extensions takes, and in particular the one
under which the degrees below `n + 1` are untouched by the step. -/
public theorem tateStage_isSetVariableExtension (n : ℕ) :
    IsSetVariableExtension (tateAlgebra A₀ n).grade (tateAlgebra A₀ n).gamma
      (tateAlgebra A₀ (n + 1)).grade (tateAlgebra A₀ (n + 1)).gamma
      (tateStep A₀ n).hom (tateGenerator A₀ n) (n + 1) n.succ_pos :=
  tateStepHom_isSetVariableExtension (tateStage A₀ n)

/-- Each step of the tower commutes with the differentials of its two stages. -/
public theorem tateStep_differential (n : ℕ) (a : (tateAlgebra A₀ n).carrier) :
    tateDifferential A₀ (n + 1) ((tateStep A₀ n).hom a) =
      (tateStep A₀ n).hom (tateDifferential A₀ n a) :=
  tateStepHom_differential (tateStage A₀ n) a

/-- **The differential of a variable of degree `n + 1` is the degree-`n` cycle it kills.** This
is the identity that makes the tower a resolution: no computation decides what a new variable
bounds, the construction prescribes it. -/
public theorem tateGenerator_differential (n : ℕ) (j : tateIndex A₀ n) :
    tateDifferential A₀ (n + 1) (tateGenerator A₀ n j) =
      (tateStep A₀ n).hom (tateCycle A₀ n j) :=
  tateStepGenerator_differential (tateStage A₀ n) j

/-- Each cycle prescribed at the `n`-th stage is homogeneous of degree `n`. -/
public theorem tateCycle_mem (n : ℕ) (j : tateIndex A₀ n) :
    tateCycle A₀ n j ∈ (tateAlgebra A₀ n).grade n :=
  (tateStage A₀ n).value_mem j

/-- Each cycle prescribed at the `n`-th stage is indeed a cycle. -/
public theorem tateCycle_cycle (n : ℕ) (j : tateIndex A₀ n) :
    tateDifferential A₀ n (tateCycle A₀ n j) = 0 :=
  (tateStage A₀ n).value_cycle j

/-- **Every cycle of positive degree is prescribed.** A homogeneous cycle of degree `n + 1` of
the stage `n + 1` indexes one of the variables adjoined at the next step, and is the value that
variable's differential takes. Together with
`DividedPowers.TateResolution.tateGenerator_differential` this is the whole of acyclicity. -/
public theorem exists_tateCycle_eq (n : ℕ) {a : (tateAlgebra A₀ (n + 1)).carrier}
    (ha : a ∈ (tateAlgebra A₀ (n + 1)).grade (n + 1))
    (hda : tateDifferential A₀ (n + 1) a = 0) :
    ∃ j : tateIndex A₀ (n + 1), tateCycle A₀ (n + 1) j = a :=
  ⟨⟨a, ha, hda⟩, rfl⟩

/-- Every stage of the tower is a differential graded algebra. -/
public theorem tateDga (n : ℕ) :
    IsDifferentialGradedAlgebra (tateAlgebra A₀ n).grade (tateDifferential A₀ n) :=
  (tateStage A₀ n).datum.dga

/-- The divided powers of every stage of the tower are compatible with its differential. -/
public theorem tateCompatible (n : ℕ) :
    IsCompatibleWithDifferential (tateAlgebra A₀ n).gamma (tateDifferential A₀ n) :=
  (tateStage A₀ n).datum.compatible

/-- Each step of the tower is injective: it is the coefficient morphism of a set-variable
extension. -/
public theorem tateStep_injective (n : ℕ) : Function.Injective (tateStep A₀ n).hom :=
  (tateStage_isSetVariableExtension A₀ n).coefficient_injective

/-- Each variable of degree `n + 1` is homogeneous of degree `n + 1`. -/
public theorem tateGenerator_mem (n : ℕ) (j : tateIndex A₀ n) :
    tateGenerator A₀ n j ∈ (tateAlgebra A₀ (n + 1)).grade (n + 1) :=
  (tateStage_isSetVariableExtension A₀ n).generator_mem j

end Tower

section Base

variable {R : Type u} [CommRing R] (P : Type (max u v)) [CommRing P] [Algebra R P]

/-- **The base of Tate's tower.** A commutative `R`-algebra `P` concentrated in degree zero,
carrying the zero differential, with a prescribed ideal `I` as the family of degree-zero cycles
to be killed by the variables of degree one.

Degree zero is the one degree where the family cannot be all the cycles: the differential
vanishes on degree zero for any Tate datum, so every element of `P` is a cycle, and killing all
of them would resolve the zero algebra. Taking `I` to be the kernel of a presentation
`φ : P → S` is what makes the tower resolve `S`. -/
public noncomputable def tateBase (I : Ideal P) : TateStageData.{u, v} R 0 where
  datum := tateDatumOfZeroDifferential (degreeZeroDPAlgebra R P)
  kill := {p : P // p ∈ I}
  value := Subtype.val
  value_mem := fun _ => mem_degreeZeroGrade_zero R P _
  value_cycle := fun _ => rfl

/-- The algebra of the base of the tower is `P` concentrated in degree zero. -/
public theorem tateBase_algebra (I : Ideal P) :
    tateAlgebra (tateBase (R := R) P I) 0 = degreeZeroDPAlgebra R P := rfl

/-- The differential of the base of the tower is zero. -/
public theorem tateBase_differential (I : Ideal P) :
    tateDifferential (tateBase (R := R) P I) 0 = 0 := rfl

/-- The cycles killed above the base of the tower are exactly the elements of `I`. -/
public theorem exists_tateBase_cycle_eq (I : Ideal P) {p : P} (hp : p ∈ I) :
    ∃ j : tateIndex (tateBase (R := R) P I) 0, tateCycle (tateBase (R := R) P I) 0 j = p :=
  ⟨⟨p, hp⟩, rfl⟩

end Base

section Colimit

variable {R : Type u} [CommRing R] (A₀ : TateStageData.{u, v} R 0)

/-- The colimit of Tate's tower: the graded divided power algebra obtained from the base by
adjoining, in every degree, a variable for each prescribed cycle of the degree below. -/
public noncomputable abbrev tateColimit : GradedDPAlgebra.{u, max u v} R :=
  chainColimit (tateAlgebra A₀) (tateStep A₀)

/-- The morphism from the `n`-th stage of Tate's tower into its colimit. -/
public noncomputable abbrev tateInclusion (n : ℕ) :
    GradedDPHom (tateAlgebra A₀ n) (tateColimit A₀) :=
  chainColimitInclusion (tateAlgebra A₀) (tateStep A₀) n

/-- The coefficient morphism of Tate's tower: the inclusion of its base into the colimit. -/
public noncomputable abbrev tateCoefficient :
    GradedDPHom (tateAlgebra A₀ 0) (tateColimit A₀) :=
  tateInclusion A₀ 0

/-- The variables of degree `n + 1` of Tate's tower, as elements of its colimit. -/
public noncomputable def tateVariable (n : ℕ) (j : tateIndex A₀ n) : (tateColimit A₀).carrier :=
  (tateInclusion A₀ (n + 1)).hom (tateGenerator A₀ n j)

/-- Each variable of Tate's tower is homogeneous of its prescribed degree. -/
public theorem tateVariable_mem (n : ℕ) (j : tateIndex A₀ n) :
    tateVariable A₀ n j ∈ (tateColimit A₀).grade (n + 1) :=
  (tateInclusion A₀ (n + 1)).map_grade (n + 1) _ (tateGenerator_mem A₀ n j)

/-- Every structure morphism of Tate's tower into its colimit is injective, so the colimit
contains each of its stages. -/
public theorem tateInclusion_injective (n : ℕ) :
    Function.Injective (tateInclusion A₀ n).hom :=
  chainColimitInclusion_injective (tateAlgebra A₀) (tateStep A₀) (tateStep_injective A₀) n

/-- **The degree-`m` piece of the colimit is the image of the degree-`m` piece of the `m`-th
stage.** Every later step adjoins variables of degree greater than `m`, so neither that piece nor
the differential into it changes again. -/
public theorem exists_tateInclusion_eq_of_mem_grade (m : ℕ)
    {x : (tateColimit A₀).carrier} (hx : x ∈ (tateColimit A₀).grade m) :
    ∃ y : (tateAlgebra A₀ m).carrier, y ∈ (tateAlgebra A₀ m).grade m ∧
      (tateInclusion A₀ m).hom y = x :=
  exists_chainColimitInclusion_eq_of_mem_grade (tateAlgebra A₀) (tateStep A₀)
    (tateGenerator A₀) (tateStage_isSetVariableExtension A₀) m hx

/-- A variable of degree `n + 1` bounds, in the colimit, the image of the cycle it kills. -/
private theorem exists_tateColimit_boundary_of_index
    (D : (tateColimit A₀).carrier →ₗ[R] (tateColimit A₀).carrier)
    (hD : ∀ (n : ℕ) (x : (tateAlgebra A₀ n).carrier),
      D ((tateInclusion A₀ n).hom x) = (tateInclusion A₀ n).hom (tateDifferential A₀ n x))
    (n : ℕ) (j : tateIndex A₀ n) :
    ∃ b : (tateColimit A₀).carrier, b ∈ (tateColimit A₀).grade (n + 1) ∧
      D b = (tateInclusion A₀ n).hom (tateCycle A₀ n j) :=
  ⟨tateVariable A₀ n j, tateVariable_mem A₀ n j, by
    rw [tateVariable, hD, tateGenerator_differential,
      chainColimitInclusion_step (tateAlgebra A₀) (tateStep A₀) n]⟩

/-- **The colimit of Tate's tower is acyclic in positive degrees.** For any operator `D` on the
colimit restricting to the differential of each stage, a homogeneous cycle of degree `n + 1` is
the boundary of a homogeneous element of degree `n + 2`.

No homology is computed: the cycle is pulled back to the stage `n + 1`, is still a cycle there
because the inclusion is injective, and therefore indexes one of the variables of degree `n + 2`,
whose differential is that cycle by construction. -/
public theorem exists_tateColimit_boundary_of_cycle
    (D : (tateColimit A₀).carrier →ₗ[R] (tateColimit A₀).carrier)
    (hD : ∀ (n : ℕ) (x : (tateAlgebra A₀ n).carrier),
      D ((tateInclusion A₀ n).hom x) = (tateInclusion A₀ n).hom (tateDifferential A₀ n x))
    (n : ℕ) {a : (tateColimit A₀).carrier} (ha : a ∈ (tateColimit A₀).grade (n + 1))
    (hda : D a = 0) :
    ∃ b : (tateColimit A₀).carrier, b ∈ (tateColimit A₀).grade (n + 2) ∧ D b = a := by
  obtain ⟨y, hy, hya⟩ := exists_tateInclusion_eq_of_mem_grade A₀ (n + 1) ha
  have hdy : tateDifferential A₀ (n + 1) y = 0 := by
    refine tateInclusion_injective A₀ (n + 1) ?_
    rw [← hD (n + 1) y, hya, hda, map_zero]
  obtain ⟨j, hj⟩ := exists_tateCycle_eq A₀ n hy hdy
  rw [← hya, ← hj]
  exact exists_tateColimit_boundary_of_index A₀ D hD (n + 1) j

/-- **Every prescribed cycle of the base becomes a boundary in the colimit.** With the base's
family taken to be the kernel of a presentation, this is exactness of the colimit in degree
zero. -/
public theorem exists_tateColimit_boundary_of_base
    (D : (tateColimit A₀).carrier →ₗ[R] (tateColimit A₀).carrier)
    (hD : ∀ (n : ℕ) (x : (tateAlgebra A₀ n).carrier),
      D ((tateInclusion A₀ n).hom x) = (tateInclusion A₀ n).hom (tateDifferential A₀ n x))
    (j : tateIndex A₀ 0) :
    ∃ b : (tateColimit A₀).carrier, b ∈ (tateColimit A₀).grade 1 ∧
      D b = (tateCoefficient A₀).hom (tateCycle A₀ 0 j) :=
  exists_tateColimit_boundary_of_index A₀ D hD 0 j

/-- **The mapping property of the colimit of Tate's tower, with the target universe free.** A
morphism out of the base together with a homogeneous value of degree `n + 1` for each variable of
degree `n + 1` extends to a morphism of graded divided power algebras out of the colimit, for a
target in *any* universe.

This is `DividedPowers.TateResolution.chainColimit_exists_gradedDPHom` instantiated at the tower.
The free target universe is what lets the colimit be mapped into an algebra built out of its own
carrier, which a universal property read off a chosen stage cannot do: the construction of one
step quantifies its target universe inside its existential. -/
public theorem tateColimit_exists_gradedDPHom (E : GradedDPAlgebra.{u, y} R)
    (g : GradedDPHom (tateAlgebra A₀ 0) E) (t : (n : ℕ) → tateIndex A₀ n → E.carrier)
    (ht : ∀ (n : ℕ) (j : tateIndex A₀ n), t n j ∈ E.grade (n + 1)) :
    ∃ F : GradedDPHom (tateColimit A₀) E,
      (∀ a : (tateAlgebra A₀ 0).carrier, F.hom ((tateCoefficient A₀).hom a) = g.hom a) ∧
        (∀ (n : ℕ) (j : tateIndex A₀ n), F.hom (tateVariable A₀ n j) = t n j) :=
  chainColimit_exists_gradedDPHom (tateAlgebra A₀) (tateStep A₀) (tateIndex A₀)
    (tateGenerator A₀) (fun n => n + 1) (fun n => n.succ_pos)
    (tateStage_isSetVariableExtension A₀) E g t ht

end Colimit

section BaseColimit

variable {R : Type u} [CommRing R] (P : Type (max u v)) [CommRing P] [Algebra R P]
  (I : Ideal P)

/-- **The degree-zero part of the colimit of Tate's tower over a degree-zero base is the
base.** Nothing of degree zero is added by any step, and nothing of positive degree of the base
exists to be forgotten. -/
public theorem mem_tateColimit_grade_zero_iff
    (x : (tateColimit (tateBase (R := R) P I)).carrier) :
    x ∈ (tateColimit (tateBase (R := R) P I)).grade 0 ↔
      ∃ p : P, (tateCoefficient (tateBase (R := R) P I)).hom p = x := by
  refine ⟨fun hx => ?_, fun ⟨p, hp⟩ => ?_⟩
  · obtain ⟨y, -, hyx⟩ := exists_tateInclusion_eq_of_mem_grade (tateBase (R := R) P I) 0 hx
    exact ⟨y, hyx⟩
  · exact hp ▸ (tateCoefficient (tateBase (R := R) P I)).map_grade 0 p
      (mem_degreeZeroGrade_zero R P p)

end BaseColimit

end DividedPowers.TateResolution

end
