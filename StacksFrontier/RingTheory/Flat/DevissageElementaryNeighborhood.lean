module

public import StacksCore.Algebra.Module.FinitePresentation
public import StacksFrontier.RingTheory.Flat.CompleteDevissage
public import StacksFrontier.RingTheory.IntegralClosure.Basic

/-!
# Finiteness properties of a complete dévissage

The algebras occurring in a complete dévissage are finitely presented over the base, apart from
the first upper algebra `A₀`, which is finitely presented as soon as the original algebra `S` is.
Under that additional hypothesis, finite presentation of the original module is equivalent to
finite presentation of the modules at every stage, over either algebra at that stage.

## Main definitions

There are no new definitions.

## Main results

* `Module.CompleteDevissage.upperAlgebra_finitePresentation` gives finite presentation of the
  upper algebras after the first over the base. The lower algebras are smooth over the base, so
  Mathlib's instance `Algebra.Smooth.finitePresentation`, tagged here, gives theirs.
* `Module.CompleteDevissage.initialUpperAlgebra_finitePresentation` and
  `Module.CompleteDevissage.left_finitePresentation` give the remaining algebra and map
  finiteness statements when the original algebra is finitely presented. The already recorded
  finite-presentation properties of `S → A 0` and `B i → A (i + 1)` are also tagged here.
* The three lemmas whose names begin with `finitePresentation_iff` give the successive
  equivalences between finite presentation of the modules in the dévissage, that is, the four
  numbered conditions of Stacks 05HY.

## Implementation notes

Stages are numbered from zero, as in `Module.CompleteDevissage`; thus `A i.succ` denotes the
source's `A_i` for `i ≥ 2`. The four numbered module conditions in the source are stated as three
successive equivalences. Restriction of scalars along `B i → A i` supplies the `B i`-module
structure used below.

## References

* [Stacks Project, Tag 05HY](https://stacks.math.columbia.edu/tag/05HY)
-/

@[expose] public section

universe u v w

namespace Module.CompleteDevissage

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N]
  {r : Ideal R} [r.IsPrime]

add_to_stacks 05HY "finite presentation of the initial map"
  Module.CompleteDevissage.initial_finitePresentation

add_to_stacks 05HY "finite presentation of the transition maps"
  Module.CompleteDevissage.transition_finitePresentation

add_to_stacks 05HY "finite presentation of the lower algebras"
  Algebra.Smooth.finitePresentation

/-- For a finite, finitely presented ring map `f : B →+* A`, a module over `A` is finitely presented
over `A` iff it is finitely presented over `B` via restriction of scalars along `f`. -/
private theorem finitePresentation_compHom_iff {B A : Type*} [CommRing B] [CommRing A]
    (f : B →+* A) (hfp : f.FinitePresentation) (hf : f.Finite) (M : Type*) [AddCommGroup M]
    [Module A M] :
    letI : Module B M := Module.compHom M f
    Module.FinitePresentation A M ↔ Module.FinitePresentation B M := by
  let : Algebra B A := f.toAlgebra
  let : Module B M := Module.compHom M f
  let : IsScalarTower B A M :=
    ⟨fun b a m => by change (f b * a) • m = f b • (a • m); rw [mul_smul]⟩
  let : Algebra.FinitePresentation B A := RingHom.finitePresentation_algebraMap.mp hfp
  let : Module.Finite B A := RingHom.finite_algebraMap.mp hf
  exact (Module.FinitePresentation.restrictScalars_iff B A M).symm

/-- Except for the first one, every upper algebra in a complete dévissage is finitely
presented over the base. -/
@[stacks 05HY "finite presentation of the upper algebras after the first"]
public theorem upperAlgebra_finitePresentation (D : CompleteDevissage R S N r)
    (i : Fin D.stepCount) :
    Algebra.FinitePresentation R (D.A i.succ) := by
  let : Algebra (D.B i.castSucc) (D.A i.succ) := (D.toRight i).toRingHom.toAlgebra
  have hBA : Algebra.FinitePresentation (D.B i.castSucc) (D.A i.succ) :=
    RingHom.finitePresentation_algebraMap.mp (D.transition_finitePresentation i)
  exact Algebra.FinitePresentation.trans R (D.B i.castSucc) (D.A i.succ)

/-- If the original algebra is finitely presented over the base, so is the first upper
algebra in a complete dévissage. -/
@[stacks 05HY "finite presentation of the first upper algebra"]
public theorem initialUpperAlgebra_finitePresentation [Algebra.FinitePresentation R S]
    (D : CompleteDevissage R S N r) :
    Algebra.FinitePresentation R (D.A 0) := by
  let : Algebra S (D.A 0) := D.toA₀.toRingHom.toAlgebra
  have hSA : Algebra.FinitePresentation S (D.A 0) :=
    RingHom.finitePresentation_algebraMap.mp D.initial_finitePresentation
  exact Algebra.FinitePresentation.trans R S (D.A 0)

/-- When the original algebra is finitely presented over the base, every same-stage map
`B i → A i` in a complete dévissage is finitely presented. -/
@[stacks 05HY "finite presentation of the maps in the dévissage"]
public theorem left_finitePresentation [Algebra.FinitePresentation R S]
    (D : CompleteDevissage R S N r) (i : Fin (D.stepCount + 1)) :
    (D.toLeft i).toRingHom.FinitePresentation := by
  have hcomp : (D.toLeft i).toRingHom.comp (algebraMap R (D.B i)) =
      algebraMap R (D.A i) := by ext; simp
  have : Algebra.FinitePresentation R (D.A i) := by
    refine Fin.cases (initialUpperAlgebra_finitePresentation D) (fun j => ?_) i
    exact upperAlgebra_finitePresentation D j
  refine RingHom.FinitePresentation.of_comp_finiteType (algebraMap R (D.B i)) ?_
    (RingHom.finiteType_algebraMap.mpr Algebra.FiniteType.of_finitePresentation)
  rw [hcomp, RingHom.finitePresentation_algebraMap]
  infer_instance

/-- Condition (1) of Tag 05HY is equivalent to condition (2): finite presentation of the
original module is equivalent to finite presentation of the first stage over its upper
algebra. -/
@[stacks 05HY "equivalence of conditions (1) and (2)"]
public theorem finitePresentation_iff_initial_over_upper [Algebra.FinitePresentation R S]
    (D : CompleteDevissage R S N r) :
    Module.FinitePresentation S N ↔ Module.FinitePresentation (D.A 0) (D.M 0) := by
  let : Module S (D.M 0) := Module.compHom (D.M 0) D.toA₀.toRingHom
  exact (LinearEquiv.finitePresentation_iff D.initialEquiv).trans
    (finitePresentation_compHom_iff D.toA₀.toRingHom D.initial_finitePresentation
      (RingHom.Finite.of_surjective _ D.initial_surjective) (D.M 0)).symm

/-- At every stage of a complete dévissage whose original algebra is finitely presented, finite
presentation of the module over the upper algebra is equivalent to finite presentation over the
lower algebra. -/
private theorem finitePresentation_iff_restrictLeft [Algebra.FinitePresentation R S]
    (D : CompleteDevissage R S N r) (i : Fin (D.stepCount + 1)) :
    letI : Module (D.B i) (D.M i) := Module.compHom (D.M i) (D.toLeft i).toRingHom
    Module.FinitePresentation (D.A i) (D.M i) ↔ Module.FinitePresentation (D.B i) (D.M i) := by
  exact finitePresentation_compHom_iff (D.toLeft i).toRingHom (left_finitePresentation D i)
    (D.left_finite i) (D.M i)

/-- Conditions (2) and (3) of Tag 05HY are equivalent: at the first stage, finite
presentation over the upper algebra is equivalent to finite presentation after restriction
of scalars to the lower algebra. -/
@[stacks 05HY "equivalence of conditions (2) and (3)"]
public theorem finitePresentation_iff_initial_over_lower [Algebra.FinitePresentation R S]
    (D : CompleteDevissage R S N r) :
    letI : Module (D.B 0) (D.M 0) :=
      Module.compHom (D.M 0) (D.toLeft 0).toRingHom
    Module.FinitePresentation (D.A 0) (D.M 0) ↔
      Module.FinitePresentation (D.B 0) (D.M 0) := finitePresentation_iff_restrictLeft D 0

/-- Condition (3) of Tag 05HY is equivalent to condition (4): finite presentation at the
first lower algebra propagates precisely to finite presentation over both algebras at every
stage. -/
@[stacks 05HY "equivalence of conditions (3) and (4)"]
public theorem finitePresentation_iff_all_stages [Algebra.FinitePresentation R S]
    (D : CompleteDevissage R S N r) :
    letI : Module (D.B 0) (D.M 0) :=
      Module.compHom (D.M 0) (D.toLeft 0).toRingHom
    Module.FinitePresentation (D.B 0) (D.M 0) ↔
      ∀ i : Fin (D.stepCount + 1),
        Module.FinitePresentation (D.A i) (D.M i) ∧
          letI : Module (D.B i) (D.M i) :=
            Module.compHom (D.M i) (D.toLeft i).toRingHom
          Module.FinitePresentation (D.B i) (D.M i) := by
  have hnext : ∀ i : Fin D.stepCount,
      (let : Module (D.B i.castSucc) (D.M i.castSucc) :=
        Module.compHom (D.M i.castSucc) (D.toLeft i.castSucc).toRingHom
       Module.FinitePresentation (D.B i.castSucc) (D.M i.castSucc)) →
      Module.FinitePresentation (D.A i.succ) (D.M i.succ) := by
    intro i hi
    let : Module (D.B i.castSucc) (D.M i.castSucc) :=
      Module.compHom (D.M i.castSucc) (D.toLeft i.castSucc).toRingHom
    let : Module (D.B i.castSucc) (D.M i.succ) :=
      Module.compHom (D.M i.succ) (D.toRight i).toRingHom
    have hq : Module.FinitePresentation (D.B i.castSucc)
        (D.M i.castSucc ⧸ LinearMap.range (D.alpha i.castSucc)) :=
      Module.finitePresentation_of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
        (by rw [Submodule.ker_mkQ]; exact Submodule.fg_range (D.alpha i.castSucc))
    exact (finitePresentation_compHom_iff (D.toRight i).toRingHom
      (D.transition_finitePresentation i)
      (RingHom.Finite.of_surjective _ (D.transition_surjective i)) (D.M i.succ)).mpr
      ((LinearEquiv.finitePresentation_iff (D.cokerEquiv i)).mp hq)
  refine ⟨fun h => ?_, fun h => (h 0).2⟩
  have hb : ∀ i : Fin (D.stepCount + 1),
      (let : Module (D.B i) (D.M i) :=
        Module.compHom (D.M i) (D.toLeft i).toRingHom
       Module.FinitePresentation (D.B i) (D.M i)) := by
    intro i
    induction i using Fin.induction with
    | zero => exact h
    | succ i ih => exact (finitePresentation_iff_restrictLeft D i.succ).mp (hnext i ih)
  exact fun i => ⟨(finitePresentation_iff_restrictLeft D i).mpr (hb i), hb i⟩

end Module.CompleteDevissage

end
