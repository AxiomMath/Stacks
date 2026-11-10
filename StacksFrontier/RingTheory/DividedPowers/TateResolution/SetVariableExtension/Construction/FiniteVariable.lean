module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableExtension.Construction.OneVariableLift
import all StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableExtension.Construction.OneVariableLift
public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Basic
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.EvenVariable
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.EvenVariableDividedPowers
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.OddVariable
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableExtension.FiniteStage

/-!
# Finite-variable stages of a set-variable divided power extension

This file introduces the bundled graded divided power algebras `GradedDPAlgebra` and their
morphisms `GradedDPHom`, packages the odd and even one-variable extensions as a single
one-variable extension with a common universal property, iterates it to adjoin finitely many
variables of prescribed degrees, and assembles the resulting finite-variable stages, indexed by
the finite subsets of the index set, into a system of injective transition maps.
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w z

attribute [local instance] prodGradedAlgebra prodStrictlyGradedComm

/-- A graded divided power algebra over `R`, bundled: a nonnegatively graded strictly
graded-commutative `R`-algebra together with divided powers on its positive even part. This is
the vocabulary for the notion when it has to be quantified over — for instance as the objects of
a diagram whose colimit is taken, which is what the bundling is for.

The instances are carried as fields rather than as instance arguments, because the carrier is
produced by a construction and cannot be named in advance. Consumers introduce them with
`attribute [local instance] GradedDPAlgebra.ring GradedDPAlgebra.algebra
GradedDPAlgebra.graded GradedDPAlgebra.strict`, as this file does, or with `letI` locally. -/
public structure GradedDPAlgebra (R : Type u) [CommRing R] where
  /-- The underlying type. -/
  carrier : Type v
  /-- Its ring structure. -/
  ring : Ring carrier
  /-- Its `R`-algebra structure. -/
  algebra : letI := ring; Algebra R carrier
  /-- Its homogeneous pieces. -/
  grade : letI := ring; letI := algebra; ℕ → Submodule R carrier
  /-- The homogeneous pieces form a grading. -/
  graded : letI := ring; letI := algebra; GradedAlgebra grade
  /-- The grading is strictly graded commutative. -/
  strict : letI := ring; letI := algebra; IsStrictlyGradedComm grade
  /-- The divided powers on the positive even part. -/
  gamma : letI := ring; letI := algebra; letI := graded; letI := strict;
    DividedPowerStructure grade

attribute [local instance] GradedDPAlgebra.ring GradedDPAlgebra.algebra
  GradedDPAlgebra.graded GradedDPAlgebra.strict

/-- A morphism of graded divided power algebras: an `R`-algebra homomorphism preserving
homogeneous degrees and divided powers. The source and target may lie in different universes. -/
public structure GradedDPHom {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) (B : GradedDPAlgebra.{u, w} R) where
  /-- The underlying algebra homomorphism. -/
  hom : A.carrier →ₐ[R] B.carrier
  /-- It preserves homogeneous degrees. -/
  map_grade : ∀ m a, a ∈ A.grade m → hom a ∈ B.grade m
  /-- It preserves divided powers. -/
  map_dpow : ∀ n a, a ∈ positiveEvenPart A.grade →
    B.gamma.dpow n (hom a) = hom (A.gamma.dpow n a)

/-- A morphism of graded divided power algebras is determined by its underlying algebra
homomorphism. -/
public theorem GradedDPHom.ext {R : Type u} [CommRing R]
    {A : GradedDPAlgebra.{u, v} R} {B : GradedDPAlgebra.{u, w} R}
    {f g : GradedDPHom A B} (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The identity morphism of graded divided power algebras. -/
public def GradedDPHom.id {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) : GradedDPHom A A where
  hom := AlgHom.id R A.carrier
  map_grade := fun _ _ h => h
  map_dpow := fun _ _ _ => rfl

/-- The composite of two morphisms of graded divided power algebras. -/
public def GradedDPHom.comp {R : Type u} [CommRing R]
    {A : GradedDPAlgebra.{u, v} R} {B : GradedDPAlgebra.{u, w} R}
    {C : GradedDPAlgebra.{u, z} R} (g : GradedDPHom B C) (f : GradedDPHom A B) :
    GradedDPHom A C where
  hom := g.hom.comp f.hom
  map_grade := fun m a h => g.map_grade m _ (f.map_grade m a h)
  map_dpow := by
    intro n a ha
    change C.gamma.dpow n (g.hom (f.hom a)) = g.hom (f.hom (A.gamma.dpow n a))
    rw [g.map_dpow n _ (algHom_mem_positiveEvenPart A.grade B.grade f.hom f.map_grade ha),
      f.map_dpow n a ha]

private structure OneVariableExtension {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) (d : ℕ) where
  algebra : GradedDPAlgebra.{u,v} R
  coefficient : GradedDPHom A algebra
  generator : algebra.carrier
  generator_mem : generator ∈ algebra.grade d

private noncomputable def oneVariableExtension {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) (d : ℕ) (hd : 0 < d) : OneVariableExtension A d := by
  classical
  by_cases ho : Odd d
  · let B : GradedDPAlgebra R :=
      { carrier := OddVariableExtension A.grade d
        ring := inferInstance
        algebra := inferInstance
        grade := OddVariableExtension.grade A.grade d
        graded := inferInstance
        strict := inferInstance
        gamma := oddVariableDividedPowerStructure A.grade A.gamma d hd ho }
    exact
      { algebra := B
        coefficient :=
          { hom := OddVariableExtension.inclusionAlgHom A.grade d
            map_grade := fun m a ha =>
              OddVariableExtension.inclusion_mem_grade
                A.grade d m ha
            map_dpow := oddVariableDividedPowerStructure_isExtension
              A.grade A.gamma d hd ho }
        generator := OddVariableExtension.generator A.grade d
        generator_mem :=
          OddVariableExtension.generator_mem_grade A.grade d }
  · have he : Even d := (Nat.even_or_odd d).resolve_right ho
    let : Fact (Even d) := ⟨he⟩
    let B : GradedDPAlgebra R :=
      { carrier := EvenVariableAlgebra A.carrier
        ring := inferInstance
        algebra := inferInstance
        grade := EvenVariableAlgebra.grade A.grade d
        graded := inferInstance
        strict := inferInstance
        gamma := evenVariableDividedPowerStructure d hd A.gamma }
    exact
      { algebra := B
        coefficient :=
          { hom := EvenVariableAlgebra.coeffAlgHom
            map_grade := fun m a ha =>
              (EvenVariableAlgebra.coeffEmbedding_mem_grade_iff
                A.grade d m a).mpr ha
            map_dpow := fun n a ha =>
              dpow_coeffEmbedding d hd A.gamma n ha }
        generator := EvenVariableAlgebra.monomial 1 1
        generator_mem := by
          simpa only [one_mul] using
            EvenVariableAlgebra.monomial_one_mem_grade A.grade d 1 }

private theorem oneVariableExtension_existsUnique_lift {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) (d : ℕ) (hd : 0 < d)
    (B : GradedDPAlgebra.{u, w} R) (f : GradedDPHom A B)
    (t : B.carrier) (ht : t ∈ B.grade d) :
    ∃! g : GradedDPHom (oneVariableExtension A d hd).algebra B,
      (∀ a, g.hom ((oneVariableExtension A d hd).coefficient.hom a) = f.hom a) ∧
      g.hom (oneVariableExtension A d hd).generator = t := by
  classical
  by_cases ho : Odd d
  · rw [oneVariableExtension, dite_eq_left ho]
    obtain ⟨g, hg, hu⟩ := existsUnique_oddVariable_dividedPower_lift
      A.grade A.gamma B.grade B.gamma f.hom f.map_grade f.map_dpow d hd ho t ht
    refine ⟨⟨g, hg.2.2.1, hg.2.2.2⟩, ⟨hg.1, hg.2.1⟩, ?_⟩
    exact fun k hk => GradedDPHom.ext (hu k.hom ⟨hk.1, hk.2, k.map_grade, k.map_dpow⟩)
  · rw [oneVariableExtension, dite_eq_right ho]
    let : Fact (Even d) := ⟨(Nat.even_or_odd d).resolve_right ho⟩
    obtain ⟨g, hg, hu⟩ := existsUnique_evenVariable_dividedPower_lift
      A.grade A.gamma B.grade B.gamma f.hom f.map_grade f.map_dpow d hd t ht
    refine ⟨⟨g, hg.2.2.1, hg.2.2.2⟩, ⟨hg.1, hg.2.1⟩, ?_⟩
    exact fun k hk => GradedDPHom.ext (hu k.hom ⟨hk.1, hk.2, k.map_grade, k.map_dpow⟩)

private noncomputable def iteratedVariableAlgebra {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) :
    (n : ℕ) → (dg : ℕ → ℕ) → (∀ i, 0 < dg i) → GradedDPAlgebra.{u, v} R
  | 0, _, _ => A
  | n + 1, dg, hdg =>
      (oneVariableExtension
        (iteratedVariableAlgebra A n (fun i => dg (i + 1)) fun i => hdg (i + 1))
        (dg 0) (hdg 0)).algebra

private noncomputable def iteratedVariableCoefficient {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) :
    (n : ℕ) → (dg : ℕ → ℕ) → (hdg : ∀ i, 0 < dg i) →
      GradedDPHom A (iteratedVariableAlgebra A n dg hdg)
  | 0, _, _ => GradedDPHom.id A
  | n + 1, dg, hdg =>
      (oneVariableExtension
        (iteratedVariableAlgebra A n (fun i => dg (i + 1)) fun i => hdg (i + 1))
        (dg 0) (hdg 0)).coefficient.comp
          (iteratedVariableCoefficient A n (fun i => dg (i + 1)) fun i => hdg (i + 1))

private noncomputable def iteratedVariableGenerator {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) :
    (n : ℕ) → (dg : ℕ → ℕ) → (hdg : ∀ i, 0 < dg i) → Fin n →
      (iteratedVariableAlgebra A n dg hdg).carrier
  | 0, _, _ => Fin.elim0
  | n + 1, dg, hdg =>
      Fin.cases
        (oneVariableExtension
          (iteratedVariableAlgebra A n (fun i => dg (i + 1)) fun i => hdg (i + 1))
          (dg 0) (hdg 0)).generator
        fun i => (oneVariableExtension
            (iteratedVariableAlgebra A n (fun i => dg (i + 1)) fun i => hdg (i + 1))
            (dg 0) (hdg 0)).coefficient.hom
          (iteratedVariableGenerator A n (fun i => dg (i + 1)) (fun i => hdg (i + 1)) i)

private theorem iteratedVariableGenerator_mem {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) :
    ∀ (n : ℕ) (dg : ℕ → ℕ) (hdg : ∀ i, 0 < dg i) (i : Fin n),
      iteratedVariableGenerator A n dg hdg i ∈
        (iteratedVariableAlgebra A n dg hdg).grade (dg i)
  | 0, _, _, i => Fin.elim0 i
  | n + 1, dg, hdg, i => by
      refine Fin.cases ?_ (fun i => ?_) i
      · exact (oneVariableExtension
          (iteratedVariableAlgebra A n (fun i => dg (i + 1)) fun i => hdg (i + 1))
          (dg 0) (hdg 0)).generator_mem
      · exact (oneVariableExtension
          (iteratedVariableAlgebra A n (fun i => dg (i + 1)) fun i => hdg (i + 1))
          (dg 0) (hdg 0)).coefficient.map_grade (dg (i + 1)) _
            (iteratedVariableGenerator_mem A n (fun i => dg (i + 1))
              (fun i => hdg (i + 1)) i)

private theorem iteratedVariableAlgebra_existsUnique_lift {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) (B : GradedDPAlgebra.{u, w} R) (f : GradedDPHom A B)
    (n : ℕ) :
    ∀ (dg : ℕ → ℕ) (hdg : ∀ i, 0 < dg i) (t : Fin n → B.carrier),
      (∀ i : Fin n, t i ∈ B.grade (dg i)) →
      ∃! g : GradedDPHom (iteratedVariableAlgebra A n dg hdg) B,
        (∀ a, g.hom ((iteratedVariableCoefficient A n dg hdg).hom a) = f.hom a) ∧
        (∀ i, g.hom (iteratedVariableGenerator A n dg hdg i) = t i) := by
  induction n with
  | zero =>
    intro dg hdg t _
    refine ⟨f, ⟨fun _ => rfl, fun i => Fin.elim0 i⟩, ?_⟩
    exact fun g hg => GradedDPHom.ext (AlgHom.ext hg.1)
  | succ n ih =>
    intro dg hdg t ht
    obtain ⟨g₀, hg₀, hu₀⟩ := ih (fun i => dg (i + 1)) (fun i => hdg (i + 1))
      (fun i => t i.succ) (fun i => ht i.succ)
    obtain ⟨g, hg, hu⟩ := oneVariableExtension_existsUnique_lift
      (iteratedVariableAlgebra A n (fun i => dg (i + 1)) fun i => hdg (i + 1))
      (dg 0) (hdg 0) B g₀ (t 0) (ht 0)
    refine ⟨g, ⟨?_, ?_⟩, ?_⟩
    · intro a
      change g.hom ((oneVariableExtension
        (iteratedVariableAlgebra A n (fun i => dg (i + 1)) fun i => hdg (i + 1))
        (dg 0) (hdg 0)).coefficient.hom
          ((iteratedVariableCoefficient A n (fun i => dg (i + 1))
            fun i => hdg (i + 1)).hom a)) = f.hom a
      rw [hg.1, hg₀.1]
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · exact hg.2
      · change g.hom ((oneVariableExtension
          (iteratedVariableAlgebra A n (fun i => dg (i + 1)) fun i => hdg (i + 1))
          (dg 0) (hdg 0)).coefficient.hom
            (iteratedVariableGenerator A n (fun i => dg (i + 1))
              (fun i => hdg (i + 1)) i)) = t i.succ
        rw [hg.1, hg₀.2]
    · intro k hk
      have hk₀ : k.comp (oneVariableExtension
          (iteratedVariableAlgebra A n (fun i => dg (i + 1)) fun i => hdg (i + 1))
          (dg 0) (hdg 0)).coefficient = g₀ := hu₀ _ ⟨hk.1, fun i => hk.2 i.succ⟩
      apply hu k
      refine ⟨?_, hk.2 0⟩
      intro a
      exact congrArg (fun l => l.hom a) hk₀

private theorem iteratedVariableCoefficient_injective {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) (n : ℕ) (dg : ℕ → ℕ) (hdg : ∀ i, 0 < dg i) :
    Function.Injective (iteratedVariableCoefficient A n dg hdg).hom := by
  obtain ⟨r, hr, _⟩ := iteratedVariableAlgebra_existsUnique_lift A A (GradedDPHom.id A) n
    dg hdg (fun _ => 0) (fun _ => Submodule.zero_mem _)
  exact Function.LeftInverse.injective hr.1

private theorem oneVariableExtension_generated {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) (d : ℕ) (hd : 0 < d) :
    ∀ x : (oneVariableExtension A d hd).algebra.carrier,
      x ∈ finiteVariableStage (oneVariableExtension A d hd).algebra.gamma
        (oneVariableExtension A d hd).coefficient.hom
        (fun _ : Unit => (oneVariableExtension A d hd).generator) {()} := by
  classical
  by_cases ho : Odd d
  · rw [oneVariableExtension, dite_eq_left ho]
    intro x
    rw [← OddVariableExtension.inclusion_fst_add_inclusion_snd_mul_generator
      A.grade d x]
    apply Subring.add_mem
    · exact Subring.subset_closure (Or.inl ⟨x.fst,rfl⟩)
    · apply Subring.mul_mem
      · exact Subring.subset_closure (Or.inl ⟨x.snd,rfl⟩)
      · exact Subring.subset_closure (Or.inr ⟨(), by simp, Or.inl rfl⟩)
  · rw [oneVariableExtension, dite_eq_right ho]
    let : Fact (Even d) := ⟨(Nat.even_or_odd d).resolve_right ho⟩
    intro x
    induction x using EvenVariableAlgebra.induction_on with
    | zero => exact Subring.zero_mem _
    | add n a x hx =>
      apply Subring.add_mem _ _ hx
      have hm : EvenVariableAlgebra.monomial n a =
          EvenVariableAlgebra.coeffEmbedding a *
            (evenVariableDividedPowerStructure d hd A.gamma).dpow n
              (EvenVariableAlgebra.monomial 1 1) := by
        rw [evenVariable_dpow_generator]
        simp [EvenVariableAlgebra.coeffEmbedding_apply,
          EvenVariableAlgebra.monomial_mul_monomial]
      rw [hm]
      apply Subring.mul_mem
      · exact Subring.subset_closure (Or.inl ⟨a,rfl⟩)
      · exact Subring.subset_closure (Or.inr ⟨(), by simp, Or.inr ⟨n,rfl⟩⟩)

private theorem iteratedVariableAlgebra_generated {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) (n : ℕ) :
    ∀ (dg : ℕ → ℕ) (hdg : ∀ i, 0 < dg i) (x : (iteratedVariableAlgebra A n dg hdg).carrier),
      x ∈ finiteVariableStage (iteratedVariableAlgebra A n dg hdg).gamma
        (iteratedVariableCoefficient A n dg hdg).hom
        (iteratedVariableGenerator A n dg hdg) Finset.univ := by
  classical
  induction n with
  | zero =>
    intro _ _ x
    exact Subring.subset_closure (Or.inl ⟨x, rfl⟩)
  | succ n ih =>
    intro dg hdg
    let B := iteratedVariableAlgebra A n (fun i => dg (i + 1)) fun i => hdg (i + 1)
    let E := oneVariableExtension B (dg 0) (hdg 0)
    let Q := finiteVariableStage (iteratedVariableAlgebra A (n + 1) dg hdg).gamma
      (iteratedVariableCoefficient A (n + 1) dg hdg).hom
      (iteratedVariableGenerator A (n + 1) dg hdg) Finset.univ
    have hc (x : B.carrier) : E.coefficient.hom x ∈ Q := by
      refine (Subring.closure_le
        (t := Q.comap (E.coefficient.hom : B.carrier →+* E.algebra.carrier))).2 ?_
        (ih (fun i => dg (i + 1)) (fun i => hdg (i + 1)) x)
      rintro y (⟨a, rfl⟩ | ⟨i, hi, rfl | ⟨m, rfl⟩⟩)
      · exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
      · exact Subring.subset_closure (Or.inr ⟨i.succ, by simp, Or.inl rfl⟩)
      · by_cases hp : iteratedVariableGenerator A n (fun i => dg (i + 1))
            (fun i => hdg (i + 1)) i ∈ positiveEvenPart B.grade
        · change E.coefficient.hom _ ∈ Q
          rw [← E.coefficient.map_dpow m _ hp]
          exact Subring.subset_closure (Or.inr ⟨i.succ, by simp, Or.inr ⟨m, rfl⟩⟩)
        · change E.coefficient.hom _ ∈ Q
          rw [B.gamma.dpow_null hp, map_zero]
          exact Q.zero_mem
    intro x
    refine (Subring.closure_le (t := Q)).2 ?_ (oneVariableExtension_generated B (dg 0) (hdg 0) x)
    rintro y (⟨a, rfl⟩ | ⟨i, hi, rfl | ⟨m, rfl⟩⟩)
    · exact hc a
    · exact Subring.subset_closure (Or.inr ⟨0, by simp, Or.inl rfl⟩)
    · exact Subring.subset_closure (Or.inr ⟨0, by simp, Or.inr ⟨m, rfl⟩⟩)

/-- The degrees of the variables of a finite stage, read off through the chosen enumeration of
the indexing set by an initial segment of `ℕ`, with the irrelevant value `1` outside it. -/
private noncomputable def stageDeg {J : Type w} (deg : J → ℕ) (S : Finset J) (i : ℕ) : ℕ :=
  if h : i < Fintype.card S then deg ((Fintype.equivFin S).symm ⟨i, h⟩) else 1

private theorem stageDeg_pos {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j) (S : Finset J)
    (i : ℕ) : 0 < stageDeg deg S i := by
  rw [stageDeg]
  split_ifs with h
  · exact hdeg _
  · exact Nat.one_pos

private theorem stageDeg_symm {J : Type w} (deg : J → ℕ) (S : Finset J)
    (i : Fin (Fintype.card S)) :
    stageDeg deg S i = deg ((Fintype.equivFin S).symm i) := by
  rw [stageDeg, dite_eq_left i.isLt]

private theorem stageDeg_equivFin {J : Type w} (deg : J → ℕ) (S : Finset J) (j : S) :
    stageDeg deg S (Fintype.equivFin S j) = deg j := by
  rw [stageDeg_symm, Equiv.symm_apply_apply]

private noncomputable abbrev finiteVariableAlgebra {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j)
    (S : Finset J) : GradedDPAlgebra.{u,v} R :=
  iteratedVariableAlgebra A (Fintype.card S) (stageDeg deg S) (stageDeg_pos deg hdeg S)

private noncomputable def finiteVariableCoefficient {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j)
    (S : Finset J) : GradedDPHom A (finiteVariableAlgebra A deg hdeg S) :=
  iteratedVariableCoefficient A (Fintype.card S) (stageDeg deg S) (stageDeg_pos deg hdeg S)

private noncomputable def finiteVariableGenerator {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j)
    (S : Finset J) (j : S) : (finiteVariableAlgebra A deg hdeg S).carrier :=
  iteratedVariableGenerator A (Fintype.card S) (stageDeg deg S) (stageDeg_pos deg hdeg S)
    (Fintype.equivFin S j)

private theorem finiteVariableGenerator_mem {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j)
    (S : Finset J) (j : S) :
    finiteVariableGenerator A deg hdeg S j ∈
      (finiteVariableAlgebra A deg hdeg S).grade (deg j) := by
  rw [← stageDeg_equivFin deg S j]
  exact iteratedVariableGenerator_mem A _ _ _ _

private theorem finiteVariableAlgebra_existsUnique_lift {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j) (S : Finset J)
    (B : GradedDPAlgebra.{u, z} R) (f : GradedDPHom A B)
    (t : S → B.carrier) (ht : ∀ i : S, t i ∈ B.grade (deg i)) :
    ∃! g : GradedDPHom (finiteVariableAlgebra A deg hdeg S) B,
      (∀ a, g.hom ((finiteVariableCoefficient A deg hdeg S).hom a) = f.hom a) ∧
      (∀ i, g.hom (finiteVariableGenerator A deg hdeg S i) = t i) := by
  classical
  obtain ⟨g, hg, hu⟩ := iteratedVariableAlgebra_existsUnique_lift A B f (Fintype.card S)
    (stageDeg deg S) (stageDeg_pos deg hdeg S) (fun i => t ((Fintype.equivFin S).symm i))
    (fun i => by rw [stageDeg_symm]; exact ht _)
  refine ⟨g, ⟨hg.1, ?_⟩, ?_⟩
  · intro i
    simpa only [finiteVariableGenerator, Equiv.symm_apply_apply] using
      hg.2 (Fintype.equivFin S i)
  · intro k hk
    apply hu k
    refine ⟨hk.1, ?_⟩
    intro i
    simpa only [finiteVariableGenerator, Equiv.apply_symm_apply] using
      hk.2 ((Fintype.equivFin S).symm i)

private theorem finiteVariableAlgebra_hom_ext {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j) (S : Finset J)
    (B : GradedDPAlgebra.{u, z} R)
    {f g : GradedDPHom (finiteVariableAlgebra A deg hdeg S) B}
    (hcoeff : ∀ a, f.hom ((finiteVariableCoefficient A deg hdeg S).hom a) =
      g.hom ((finiteVariableCoefficient A deg hdeg S).hom a))
    (hgen : ∀ i, f.hom (finiteVariableGenerator A deg hdeg S i) =
      g.hom (finiteVariableGenerator A deg hdeg S i)) : f = g := by
  obtain ⟨k, hk, hu⟩ := finiteVariableAlgebra_existsUnique_lift A deg hdeg S B
    (g.comp (finiteVariableCoefficient A deg hdeg S))
    (fun i => g.hom (finiteVariableGenerator A deg hdeg S i))
    (fun i : S => g.map_grade (deg i) _ (finiteVariableGenerator_mem A deg hdeg S i))
  exact (hu f ⟨hcoeff, hgen⟩).trans (hu g ⟨fun _ => rfl, fun _ => rfl⟩).symm

private noncomputable def finiteVariableMap {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j)
    {S T : Finset J} (h : S ⊆ T) :
    GradedDPHom (finiteVariableAlgebra A deg hdeg S) (finiteVariableAlgebra A deg hdeg T) :=
  (finiteVariableAlgebra_existsUnique_lift A deg hdeg S (finiteVariableAlgebra A deg hdeg T)
    (finiteVariableCoefficient A deg hdeg T)
    (fun i => finiteVariableGenerator A deg hdeg T ⟨i, h i.property⟩)
    (fun i : S => finiteVariableGenerator_mem A deg hdeg T ⟨i.val, h i.property⟩)).choose

private theorem finiteVariableMap_spec {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j)
    {S T : Finset J} (h : S ⊆ T) :
    (∀ a, (finiteVariableMap A deg hdeg h).hom ((finiteVariableCoefficient A deg hdeg S).hom a) =
      (finiteVariableCoefficient A deg hdeg T).hom a) ∧
    ∀ i : S, (finiteVariableMap A deg hdeg h).hom (finiteVariableGenerator A deg hdeg S i) =
      finiteVariableGenerator A deg hdeg T ⟨i, h i.property⟩ :=
  (finiteVariableAlgebra_existsUnique_lift A deg hdeg S (finiteVariableAlgebra A deg hdeg T)
    (finiteVariableCoefficient A deg hdeg T)
    (fun i => finiteVariableGenerator A deg hdeg T ⟨i, h i.property⟩)
    (fun i : S => finiteVariableGenerator_mem A deg hdeg T ⟨i.val, h i.property⟩)).choose_spec.1

private theorem finiteVariableMap_coefficient {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j)
    {S T : Finset J} (h : S ⊆ T) (a : A.carrier) :
    (finiteVariableMap A deg hdeg h).hom ((finiteVariableCoefficient A deg hdeg S).hom a) =
      (finiteVariableCoefficient A deg hdeg T).hom a :=
  (finiteVariableMap_spec A deg hdeg h).1 a

private theorem finiteVariableMap_generator {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j)
    {S T : Finset J} (h : S ⊆ T) (i : S) :
    (finiteVariableMap A deg hdeg h).hom (finiteVariableGenerator A deg hdeg S i) =
      finiteVariableGenerator A deg hdeg T ⟨i, h i.property⟩ :=
  (finiteVariableMap_spec A deg hdeg h).2 i

private theorem finiteVariableMap_self {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j)
    (S : Finset J) :
    finiteVariableMap A deg hdeg (Finset.Subset.refl S) =
      GradedDPHom.id (finiteVariableAlgebra A deg hdeg S) := by
  apply finiteVariableAlgebra_hom_ext A deg hdeg S
  · exact finiteVariableMap_coefficient A deg hdeg _
  · exact finiteVariableMap_generator A deg hdeg _

private theorem finiteVariableMap_comp {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j)
    {S T U : Finset J} (h : S ⊆ T) (k : T ⊆ U) :
    (finiteVariableMap A deg hdeg k).comp (finiteVariableMap A deg hdeg h) =
      finiteVariableMap A deg hdeg (h.trans k) := by
  apply finiteVariableAlgebra_hom_ext A deg hdeg S
  · intro a
    change (finiteVariableMap A deg hdeg k).hom
      ((finiteVariableMap A deg hdeg h).hom ((finiteVariableCoefficient A deg hdeg S).hom a)) = _
    simp only [finiteVariableMap_coefficient]
  · intro i
    change (finiteVariableMap A deg hdeg k).hom
      ((finiteVariableMap A deg hdeg h).hom (finiteVariableGenerator A deg hdeg S i)) = _
    simp only [finiteVariableMap_generator]

private theorem finiteVariableMap_injective {R : Type u} [CommRing R]
    (A : GradedDPAlgebra.{u, v} R) {J : Type w} (deg : J → ℕ) (hdeg : ∀ j, 0 < deg j)
    {S T : Finset J} (h : S ⊆ T) : Function.Injective (finiteVariableMap A deg hdeg h).hom := by
  classical
  let t (i : T) := if hi : i.val ∈ S then finiteVariableGenerator A deg hdeg S ⟨i, hi⟩ else 0
  obtain ⟨r, hr, _⟩ := finiteVariableAlgebra_existsUnique_lift A deg hdeg T
    (finiteVariableAlgebra A deg hdeg S) (finiteVariableCoefficient A deg hdeg S) t
    (fun i : T => by
      dsimp only [t]
      split_ifs with hi
      · exact finiteVariableGenerator_mem A deg hdeg S ⟨i.val, hi⟩
      · exact Submodule.zero_mem _)
  have heq : r.comp (finiteVariableMap A deg hdeg h) =
      GradedDPHom.id (finiteVariableAlgebra A deg hdeg S) := by
    apply finiteVariableAlgebra_hom_ext A deg hdeg S
    · intro a
      change r.hom ((finiteVariableMap A deg hdeg h).hom
        ((finiteVariableCoefficient A deg hdeg S).hom a)) = _
      rw [finiteVariableMap_coefficient, hr.1]
      rfl
    · intro i
      change r.hom ((finiteVariableMap A deg hdeg h).hom
        (finiteVariableGenerator A deg hdeg S i)) = _
      rw [finiteVariableMap_generator, hr.2]
      simp only [t, dite_eq_left i.property]
      rfl
  have hl : Function.LeftInverse r.hom (finiteVariableMap A deg hdeg h).hom := fun x =>
    congrArg (fun k => k.hom x) heq
  exact hl.injective

end DividedPowers.TateResolution
