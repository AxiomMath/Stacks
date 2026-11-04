module

public import StacksFrontier.RingTheory.Flat.CompleteDevissage

/-!
# A complete dévissage is a single stage followed by a complete dévissage of the cokernel

A complete dévissage of `N/S/R` over a prime `r` (`Module.CompleteDevissage`) is a chain of
`stepCount + 1` stages. This file isolates the data of one stage as `Module.DevissageStage` and
relates complete dévissages of different lengths:

* `Module.DevissageStage.toCompleteDevissage` turns a stage whose map `alpha` is surjective into a
  complete dévissage with one stage;
* `Module.CompleteDevissage.cons` prepends a stage to a complete dévissage of the cokernel of that
  stage's map;
* `Module.CompleteDevissage.head` is the first stage of a complete dévissage, and
  `Module.CompleteDevissage.tail` is what is left of it after the first stage is removed, a
  complete dévissage of the cokernel of the first map.

## Main definitions

* `Module.DevissageStage R S N r` is the data of a single stage of a complete dévissage of
  `N/S/R` over `r`: the two algebras, the module, the surjection from `S`, the finite map from the
  lower algebra, and the map out of a finite free module together with its fibre condition.
* `Module.DevissageStage.toCompleteDevissage`, `Module.CompleteDevissage.cons`,
  `Module.CompleteDevissage.head` and `Module.CompleteDevissage.tail`.
* `Module.CompleteDevissage.finCases`: a case split on `Fin (n + 1)` into the zero index and the
  successors.

## Main results

* `Module.nonempty_completeDevissage_of_surjective_alpha`: a stage whose map is surjective is a
  complete dévissage.
* `Module.nonempty_completeDevissage_of_nonempty_cokernel`: a stage whose cokernel carries a
  complete dévissage extends to a complete dévissage.
* `Module.CompleteDevissage.stepCount_tail`: the tail has one stage fewer.

## References

* [Stacks Project, Tag 05HX](https://stacks.math.columbia.edu/tag/05HX)
* [Stacks Project, Tag 05I1](https://stacks.math.columbia.edu/tag/05I1)
* [Stacks Project, Tag 05I4](https://stacks.math.columbia.edu/tag/05I4)
-/

@[expose] public section

open AlgebraicGeometry

universe u v w

namespace Module

/-- The data of a single stage of a complete dévissage of `N/S/R` over a prime `r` of `R`.

`A` and `B` are `R`-algebras, `M` is a finite `A`-module, `S → A` is a surjection of finite
presentation identifying `N` with `M`, the map `B → A` is finite, `B` is smooth over `R` with
geometrically irreducible fibres, and `alpha` maps a finite free `B`-module to `M` viewed as a
`B`-module, becoming an isomorphism over the residue field of `rB`. -/
public structure DevissageStage (R : Type u) (S : Type v) (N : Type w) [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S] [AddCommGroup N] [Module S N]
    [Module.Finite S N] (r : Ideal R) [r.IsPrime] where
  /-- The upper `R`-algebra of the stage. -/
  A : Type u
  /-- The lower `R`-algebra of the stage. -/
  B : Type u
  [commRingA : CommRing A]
  [commRingB : CommRing B]
  [algebraRA : Algebra R A]
  [algebraRB : Algebra R B]
  /-- The module on the upper algebra. -/
  M : Type w
  [addCommGroupM : AddCommGroup M]
  [moduleAM : Module A M]
  /-- The map from `S` to the upper algebra. -/
  toA₀ : S →ₐ[R] A
  /-- The map from the lower algebra to the upper algebra. -/
  toLeft : B →ₐ[R] A
  /-- The rank of the finite free module of the stage. -/
  multiplicity : ℕ
  /-- The map from the finite free `B`-module into `M`. -/
  alpha : letI : Module B M := Module.compHom M toLeft.toRingHom;
    (Fin multiplicity →₀ B) →ₗ[B] M
  /-- `M` is finite over `A`. -/
  finiteM : @Module.Finite A M _ _ moduleAM
  /-- The map from `S` to the upper algebra is surjective. -/
  initial_surjective : Function.Surjective toA₀
  /-- The map from `S` to the upper algebra is of finite presentation. -/
  initial_finitePresentation : toA₀.toRingHom.FinitePresentation
  /-- The map from the lower algebra to the upper algebra is finite. -/
  left_finite : toLeft.toRingHom.Finite
  /-- The lower algebra is smooth over the base. -/
  smooth : letI := algebraRB; Algebra.Smooth R B
  /-- The morphism `Spec(B) → Spec(R)` has geometrically irreducible fibres. -/
  geometricallyIrreducibleFibers :
    GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap R B)))
  /-- `N` is `M` after restricting scalars along `S → A`. -/
  initialEquiv : letI : Module S M := Module.compHom M toA₀.toRingHom; N ≃ₗ[S] M
  /-- The extended ideal `rB` is prime. -/
  map_isPrime : (Ideal.map (algebraMap R B) r).IsPrime
  /-- After passing to the residue field of `rB`, `alpha` is an isomorphism. -/
  fiber_bijective : let p := Ideal.map (algebraMap R B) r;
    letI : p.IsPrime := map_isPrime
    letI : Module B M := Module.compHom M toLeft.toRingHom
    Function.Bijective (alpha.baseChange p.ResidueField)

namespace DevissageStage

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N] {r : Ideal R}
  [r.IsPrime]

/-- The upper algebra of a stage is a commutative ring. -/
public instance (E : DevissageStage R S N r) : CommRing E.A := E.commRingA

/-- The lower algebra of a stage is a commutative ring. -/
public instance (E : DevissageStage R S N r) : CommRing E.B := E.commRingB

/-- The upper algebra of a stage is an `R`-algebra. -/
public instance (E : DevissageStage R S N r) : Algebra R E.A := E.algebraRA

/-- The lower algebra of a stage is an `R`-algebra. -/
public instance (E : DevissageStage R S N r) : Algebra R E.B := E.algebraRB

/-- The module of a stage is an additive commutative group. -/
public instance (E : DevissageStage R S N r) : AddCommGroup E.M := E.addCommGroupM

/-- The module of a stage is a module over the upper algebra. -/
public instance (E : DevissageStage R S N r) : Module E.A E.M := E.moduleAM

/-- The module of a stage is finite over the upper algebra. -/
public instance (E : DevissageStage R S N r) : Module.Finite E.A E.M := E.finiteM

/-- The lower algebra of a stage is smooth over `R`. -/
public instance (E : DevissageStage R S N r) : Algebra.Smooth R E.B := E.smooth

/-- The morphism `Spec(E.B) → Spec(R)` has geometrically irreducible fibres. -/
public instance (E : DevissageStage R S N r) :
    GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap R E.B))) :=
  E.geometricallyIrreducibleFibers

/-- The ideal `rE.B` is prime. -/
public instance (E : DevissageStage R S N r) :
    (Ideal.map (algebraMap R E.B) r).IsPrime := E.map_isPrime

/-- The lower algebra of a stage acts on the stage module through `toLeft`. -/
public instance moduleBM (E : DevissageStage R S N r) : Module E.B E.M :=
  Module.compHom E.M E.toLeft.toRingHom

/-- The upper algebra of a stage is an algebra over the lower one through `toLeft`. -/
public instance algebraBA (E : DevissageStage R S N r) : Algebra E.B E.A :=
  E.toLeft.toRingHom.toAlgebra

/-- The scalar tower `R → E.B → E.A`. -/
public instance (E : DevissageStage R S N r) : IsScalarTower R E.B E.A :=
  IsScalarTower.of_algebraMap_eq fun x => (E.toLeft.commutes x).symm

/-- The scalar tower `E.B → E.A → E.M`. -/
public instance (E : DevissageStage R S N r) : IsScalarTower E.B E.A E.M :=
  ⟨fun b a m => by change (E.toLeft b * a) • m = E.toLeft b • (a • m); rw [mul_smul]⟩

/-- The upper algebra of a stage is finite over the lower one. -/
public instance (E : DevissageStage R S N r) : Module.Finite E.B E.A :=
  RingHom.finite_algebraMap.mp E.left_finite

/-- The module of a stage is finite over the lower algebra. -/
public instance (E : DevissageStage R S N r) : Module.Finite E.B E.M :=
  Module.Finite.trans E.A E.M

/-- The cokernel of the map of a stage is a finite module over the lower algebra. -/
public instance (E : DevissageStage R S N r) :
    Module.Finite E.B (E.M ⧸ LinearMap.range E.alpha) :=
  Module.Finite.of_surjective (LinearMap.range E.alpha).mkQ (Submodule.mkQ_surjective _)

/-- A stage whose map is surjective, as a complete dévissage with one stage. -/
public def toCompleteDevissage (E : DevissageStage R S N r)
    (hsurj : Function.Surjective E.alpha) :
    CompleteDevissage R S N r where
  stepCount := 0
  A _ := E.A
  B _ := E.B
  M _ := E.M
  toA₀ := E.toA₀
  toLeft _ := E.toLeft
  toRight i := Fin.elim0 i
  multiplicity _ := E.multiplicity
  alpha _ := E.alpha
  finiteM _ := E.finiteM
  initial_surjective := E.initial_surjective
  initial_finitePresentation := E.initial_finitePresentation
  transition_surjective i := Fin.elim0 i
  transition_finitePresentation i := Fin.elim0 i
  left_finite _ := E.left_finite
  smooth _ := E.smooth
  geometricallyIrreducibleFibers _ := E.geometricallyIrreducibleFibers
  initialEquiv := E.initialEquiv
  cokerEquiv i := Fin.elim0 i
  map_isPrime _ := E.map_isPrime
  fiber_bijective _ := E.fiber_bijective
  final_surjective := hsurj

/-- The complete dévissage of a stage has `stepCount = 0`. -/
@[simp]
public theorem stepCount_toCompleteDevissage (E : DevissageStage R S N r)
    (hsurj : Function.Surjective E.alpha) :
    (E.toCompleteDevissage hsurj).stepCount = 0 :=
  rfl

end DevissageStage

namespace CompleteDevissage

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N] {r : Ideal R}
  [r.IsPrime]

/-- A case split on `Fin (n + 1)` into the zero index and the successors, defined by matching on
the underlying natural number. -/
public def finCases {n : ℕ} {motive : Fin (n + 1) → Sort*} (zero : motive 0)
    (succ : ∀ i : Fin n, motive i.succ) : ∀ i, motive i
  | ⟨0, _⟩ => zero
  | ⟨j + 1, h⟩ => succ ⟨j, Nat.lt_of_succ_lt_succ h⟩

/-- `finCases zero succ` takes the value `zero` at `0`. -/
@[simp]
public theorem finCases_zero {n : ℕ} {motive : Fin (n + 1) → Sort*} (zero : motive 0)
    (succ : ∀ i : Fin n, motive i.succ) :
    finCases zero succ 0 = zero :=
  rfl

/-- `finCases zero succ` takes the value `succ i` at `i.succ`. -/
@[simp]
public theorem finCases_succ {n : ℕ} {motive : Fin (n + 1) → Sort*} (zero : motive 0)
    (succ : ∀ i : Fin n, motive i.succ) (i : Fin n) :
    finCases zero succ i.succ = succ i :=
  rfl

/-- The first stage of a complete dévissage. -/
public def head (D : CompleteDevissage R S N r) : DevissageStage R S N r where
  A := D.A 0
  B := D.B 0
  M := D.M 0
  toA₀ := D.toA₀
  toLeft := D.toLeft 0
  multiplicity := D.multiplicity 0
  alpha := D.alpha 0
  finiteM := D.finiteM 0
  initial_surjective := D.initial_surjective
  initial_finitePresentation := D.initial_finitePresentation
  left_finite := D.left_finite 0
  smooth := D.smooth 0
  geometricallyIrreducibleFibers := D.geometricallyIrreducibleFibers 0
  initialEquiv := D.initialEquiv
  map_isPrime := D.map_isPrime 0
  fiber_bijective := D.fiber_bijective 0

/-- The upper algebra of the first stage. -/
@[simp] public theorem head_A (D : CompleteDevissage R S N r) : D.head.A = D.A 0 := rfl

/-- The lower algebra of the first stage. -/
@[simp] public theorem head_B (D : CompleteDevissage R S N r) : D.head.B = D.B 0 := rfl

/-- The module of the first stage. -/
@[simp] public theorem head_M (D : CompleteDevissage R S N r) : D.head.M = D.M 0 := rfl

/-- The multiplicity of the first stage. -/
@[simp] public theorem head_multiplicity (D : CompleteDevissage R S N r) :
    D.head.multiplicity = D.multiplicity 0 := rfl

/-- The map from `S` of the first stage. -/
@[simp] public theorem head_toA₀ (D : CompleteDevissage R S N r) : D.head.toA₀ = D.toA₀ := rfl

/-- The map from the lower to the upper algebra of the first stage. -/
@[simp] public theorem head_toLeft (D : CompleteDevissage R S N r) :
    D.head.toLeft = D.toLeft 0 := rfl

/-- The map of the first stage. -/
@[simp] public theorem head_alpha (D : CompleteDevissage R S N r) :
    D.head.alpha = D.alpha 0 := rfl

/-- Prepending a stage to a complete dévissage of its cokernel: given a stage `E` of a dévissage
of `N/S/R` over `r` and a complete dévissage `D` of `Coker (E.alpha) / E.B / R` over `r`, the
complete dévissage of `N/S/R` over `r` with first stage `E` followed by the stages of `D`. -/
public def cons (E : DevissageStage R S N r)
    (D : CompleteDevissage R E.B (E.M ⧸ LinearMap.range E.alpha) r) :
    CompleteDevissage R S N r where
  stepCount := D.stepCount + 1
  A := finCases E.A D.A
  B := finCases E.B D.B
  M := finCases E.M D.M
  commRingA := finCases E.commRingA D.commRingA
  commRingB := finCases E.commRingB D.commRingB
  algebraRA := finCases E.algebraRA D.algebraRA
  algebraRB := finCases E.algebraRB D.algebraRB
  addCommGroupM := finCases E.addCommGroupM D.addCommGroupM
  moduleAM := finCases E.moduleAM D.moduleAM
  toA₀ := E.toA₀
  toLeft := finCases E.toLeft D.toLeft
  toRight := finCases D.toA₀ D.toRight
  multiplicity := finCases E.multiplicity D.multiplicity
  alpha := finCases E.alpha D.alpha
  finiteM := finCases E.finiteM D.finiteM
  initial_surjective := E.initial_surjective
  initial_finitePresentation := E.initial_finitePresentation
  transition_surjective := finCases D.initial_surjective D.transition_surjective
  transition_finitePresentation :=
    finCases D.initial_finitePresentation D.transition_finitePresentation
  left_finite := finCases E.left_finite D.left_finite
  smooth := finCases E.smooth D.smooth
  geometricallyIrreducibleFibers :=
    finCases E.geometricallyIrreducibleFibers D.geometricallyIrreducibleFibers
  initialEquiv := E.initialEquiv
  cokerEquiv := finCases D.initialEquiv D.cokerEquiv
  map_isPrime := finCases E.map_isPrime D.map_isPrime
  fiber_bijective := finCases E.fiber_bijective D.fiber_bijective
  final_surjective := D.final_surjective

section ConsSimp

variable (E : DevissageStage R S N r)
  (D : CompleteDevissage R E.B (E.M ⧸ LinearMap.range E.alpha) r)

/-- `cons E D` has one stage more than `D`. -/
@[simp]
public theorem stepCount_cons : (cons E D).stepCount = D.stepCount + 1 := rfl

/-- The first upper algebra of `cons E D` is that of `E`. -/
@[simp]
public theorem A_cons_zero : (cons E D).A 0 = E.A := rfl

/-- The upper algebras of `cons E D` after the first are those of `D`. -/
@[simp]
public theorem A_cons_succ (i : Fin (D.stepCount + 1)) : (cons E D).A i.succ = D.A i := rfl

/-- The first lower algebra of `cons E D` is that of `E`. -/
@[simp]
public theorem B_cons_zero : (cons E D).B 0 = E.B := rfl

/-- The lower algebras of `cons E D` after the first are those of `D`. -/
@[simp]
public theorem B_cons_succ (i : Fin (D.stepCount + 1)) : (cons E D).B i.succ = D.B i := rfl

/-- The first module of `cons E D` is that of `E`. -/
@[simp]
public theorem M_cons_zero : (cons E D).M 0 = E.M := rfl

/-- The modules of `cons E D` after the first are those of `D`. -/
@[simp]
public theorem M_cons_succ (i : Fin (D.stepCount + 1)) : (cons E D).M i.succ = D.M i := rfl

/-- The first multiplicity of `cons E D` is that of `E`. -/
@[simp]
public theorem multiplicity_cons_zero : (cons E D).multiplicity 0 = E.multiplicity := rfl

/-- The multiplicities of `cons E D` after the first are those of `D`. -/
@[simp]
public theorem multiplicity_cons_succ (i : Fin (D.stepCount + 1)) :
    (cons E D).multiplicity i.succ = D.multiplicity i := rfl

end ConsSimp

/-- The map of a complete dévissage is surjective at every index `i` equal to the last one. -/
public theorem final_surjective_of_eq_last (D : CompleteDevissage R S N r)
    (i : Fin (D.stepCount + 1)) (hi : i = Fin.last D.stepCount) :
    letI : Module (D.B i) (D.M i) := Module.compHom (D.M i) (D.toLeft i).toRingHom
    Function.Surjective (D.alpha i) := by
  subst hi
  exact D.final_surjective

/-- What is left of a complete dévissage after its first stage is removed: a complete dévissage
of the cokernel of the first map over the first lower algebra, whose stages are the stages
`1, …, stepCount` of the original. It takes as hypothesis that the original has more than one
stage (`D.stepCount ≠ 0`). -/
public def tail (D : CompleteDevissage R S N r) (hpos : D.stepCount ≠ 0) :
    CompleteDevissage R D.head.B (D.head.M ⧸ LinearMap.range D.head.alpha) r :=
  letI h : D.stepCount - 1 + 1 = D.stepCount := Nat.succ_pred_eq_of_ne_zero hpos
  { stepCount := D.stepCount - 1
    A i := D.A (Fin.cast h i).succ
    B i := D.B (Fin.cast h i).succ
    M i := D.M (Fin.cast h i).succ
    commRingA i := D.commRingA _
    commRingB i := D.commRingB _
    algebraRA i := D.algebraRA _
    algebraRB i := D.algebraRB _
    addCommGroupM i := D.addCommGroupM _
    moduleAM i := D.moduleAM _
    toA₀ := D.toRight (Fin.cast h 0)
    toLeft i := D.toLeft (Fin.cast h i).succ
    toRight i := D.toRight (Fin.cast h i.succ)
    multiplicity i := D.multiplicity (Fin.cast h i).succ
    alpha i := D.alpha (Fin.cast h i).succ
    finiteM i := D.finiteM _
    initial_surjective := D.transition_surjective _
    initial_finitePresentation := D.transition_finitePresentation _
    transition_surjective i := D.transition_surjective _
    transition_finitePresentation i := D.transition_finitePresentation _
    left_finite i := D.left_finite _
    smooth i := D.smooth _
    geometricallyIrreducibleFibers i := D.geometricallyIrreducibleFibers _
    initialEquiv := D.cokerEquiv (Fin.cast h 0)
    cokerEquiv i := D.cokerEquiv (Fin.cast h i.succ)
    map_isPrime i := D.map_isPrime _
    fiber_bijective i := D.fiber_bijective _
    final_surjective :=
      D.final_surjective_of_eq_last _ (Fin.ext (by simpa using h)) }

section TailSimp

variable (D : CompleteDevissage R S N r) (hpos : D.stepCount ≠ 0)

/-- The tail has one stage fewer. -/
@[simp]
public theorem stepCount_tail : (D.tail hpos).stepCount = D.stepCount - 1 := rfl

/-- The upper algebras of the tail are those of the original after the first. -/
@[simp]
public theorem A_tail (i : Fin (D.stepCount - 1 + 1)) :
    (D.tail hpos).A i = D.A (Fin.cast (Nat.succ_pred_eq_of_ne_zero hpos) i).succ := rfl

/-- The lower algebras of the tail are those of the original after the first. -/
@[simp]
public theorem B_tail (i : Fin (D.stepCount - 1 + 1)) :
    (D.tail hpos).B i = D.B (Fin.cast (Nat.succ_pred_eq_of_ne_zero hpos) i).succ := rfl

/-- The modules of the tail are those of the original after the first. -/
@[simp]
public theorem M_tail (i : Fin (D.stepCount - 1 + 1)) :
    (D.tail hpos).M i = D.M (Fin.cast (Nat.succ_pred_eq_of_ne_zero hpos) i).succ := rfl

/-- The multiplicities of the tail are those of the original after the first. -/
@[simp]
public theorem multiplicity_tail (i : Fin (D.stepCount - 1 + 1)) :
    (D.tail hpos).multiplicity i =
      D.multiplicity (Fin.cast (Nat.succ_pred_eq_of_ne_zero hpos) i).succ := rfl

end TailSimp

end CompleteDevissage

section Existence

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N] {r : Ideal R}
  [r.IsPrime]

/-- If the map `alpha` of a stage is surjective, then `N/S/R` has a complete dévissage over
`r`. -/
public theorem nonempty_completeDevissage_of_surjective_alpha (E : DevissageStage R S N r)
    (hsurj : Function.Surjective E.alpha) :
    Nonempty (CompleteDevissage R S N r) :=
  ⟨E.toCompleteDevissage hsurj⟩

/-- If the cokernel of the map of a stage carries a complete dévissage over the lower algebra of
that stage, then `N/S/R` carries one over `r`. -/
public theorem nonempty_completeDevissage_of_nonempty_cokernel (E : DevissageStage R S N r)
    (h : Nonempty (CompleteDevissage R E.B (E.M ⧸ LinearMap.range E.alpha) r)) :
    Nonempty (CompleteDevissage R S N r) :=
  h.map (CompleteDevissage.cons E)

end Existence

end Module

end
