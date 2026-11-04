module

public import StacksFrontier.RingTheory.Flat.CompleteDevissage

/-!
# Assembling a complete dévissage one stage at a time

A complete dévissage of `N/S/R` over a prime `r` of `R` (Stacks 05HX) is recorded by
`Module.CompleteDevissage` as a family of stages indexed by `Fin (stepCount + 1)`. The
constructions that produce one are recursive: the scheme-theoretic complete dévissage of
Stacks 05HH is a head stage followed by a complete dévissage of the cokernel of that stage, and
translating it into algebra needs the ability to put one algebraic stage in front of an
algebraic dévissage of that cokernel.

This file isolates the datum of a single stage as `Module.DevissageStageData` and supplies the
two introduction rules: `Module.CompleteDevissage.ofStage`, a dévissage with exactly one stage, and
`Module.CompleteDevissage.consStageData`, which prepends a stage. Together they are an introduction
principle for `Module.CompleteDevissage` matching the recursive shape of
`AlgebraicGeometry.DevissageChain`, whose constructors `last` and `more` they correspond to.
In the other direction `Module.CompleteDevissage.stages` reads off the stages of a dévissage
one at a time.

## Main definitions

* `Module.DevissageStageData R r` is the datum `(A, B, M, α)` of one stage of a complete
  dévissage over the prime `r` of `R`, with the conditions of Stacks 05HX that concern a
  single stage in isolation.
* `Module.DevissageStageData.coker` is the cokernel `M ⧸ range α` of the stage map, the module
  dévissed by the next stage.
* `Module.DevissageStageData.Pointed` is the pointed datum of a stage of a dévissage *at* a prime:
  the two chosen primes with the conditions of Stacks 05HZ that concern a single stage.
* `Module.CompleteDevissage.stages` is the family of stages of a complete dévissage, and
  `Module.NonemptyCompleteDevissageAt.pointedStages` the family of their pointed data.
* `Module.CompleteDevissage.ofStage` is the complete dévissage consisting of a single stage
  whose map is surjective, and `Module.NonemptyCompleteDevissageAt.ofStage` its pointed form.
* `Module.CompleteDevissage.consStageData` prepends a stage to a complete dévissage of a module
  identified with the cokernel of that stage, and
  `Module.NonemptyCompleteDevissageAt.cons` prepends a pointed stage.

## Main results

* `Module.CompleteDevissage.stages_ofStage`,
  `Module.CompleteDevissage.stages_consStageData_zero` and
  `Module.CompleteDevissage.stages_consStageData_succ`: the stages of the two constructions.
* `Module.CompleteDevissage.stepCount_ofStage` and
  `Module.CompleteDevissage.stepCount_consStageData`: their lengths.
* `Module.DevissageStageData.consPointed_zero` and
  `Module.DevissageStageData.consPointed_succ`: the pointed data of the stages of a chain with
  a pointed stage prepended.

## Implementation notes

`Module.DevissageStageData` carries exactly those conditions of Stacks 05HX that a single stage
satisfies on its own, so it mentions neither the module being dévissed nor the algebra it lives
over: a stage in the middle of a dévissage sits over the lower algebra of the previous stage,
not over the original one. The data relating the first stage to `N/S` — the surjection `S → A`
and the identification of `N` with `M` — are therefore arguments of `ofStage` and
`consStageData` rather than fields of a stage, and the vanishing of the cokernel, which only
the final stage satisfies, is an argument of `ofStage` alone.

The families of a prepended dévissage are obtained by prepending to the family of *stages*,
with `Fin.cons`, every field of the result being a projection of that one family. Doing it field
by field instead — one `Fin.cons` for the algebras, one for the modules, one for the maps —
is what one writes first and it does not typecheck in reasonable time: the stage maps and the
fibre conditions have large dependent types, and each field then forces the unifier to reduce
`Fin.cons` against a different large motive, tens of thousands of times over. Prepending to a
single family of stages makes each of those reductions a reduction of `Fin.cons` against the
*constant* motive `Module.DevissageStageData R r`, followed by a projection of a constructor. The
index arithmetic relating the two indexings, `(Fin.succ i).castSucc = (Fin.castSucc i).succ`
and `Fin.last (n + 1) = Fin.succ (Fin.last n)`, holds definitionally, so nothing is transported.

A stage is prepended to a dévissage of an arbitrary module `N'` together with a linear
equivalence `coker ≃ₗ[B] N'`, rather than to a dévissage of the cokernel itself. The field
`Module.CompleteDevissage.cokerEquiv` is stated up to isomorphism anyway, and a consumer
translating a scheme-theoretic dévissage has a dévissage of the global sections of the cokernel
sheaf, which are only isomorphic to the cokernel of the induced map of global sections.

For the pointed notion the tail is taken as a `Module.CompleteDevissage` together with a family
of pointed data, rather than as a `Module.NonemptyCompleteDevissageAt` of the cokernel. A
dévissage at a prime carries its base prime as `q.under R`, so a tail recorded that way would
be a dévissage over `(lowerPrime 0).under R`, which is only propositionally equal to the base
prime of the head and would have to be transported. Splitting the tail into its dévissage and
its pointed data keeps the base prime fixed and avoids the transport; the compatibility of the
chosen primes along the maps of the chain becomes three explicit hypotheses.

The module structure on the stage module `M` over the lower algebra `B`, obtained by restricting
scalars along `B → A`, is declared as an instance. It is the structure the field
`Module.CompleteDevissage.alpha` uses in the type of the stage maps, so the two agree
syntactically and a stage map can be read as a `B`-linear map with no transport.

## References

* [Stacks Project, Tag 05HX](https://stacks.math.columbia.edu/tag/05HX)
* [Stacks Project, Tag 05HZ](https://stacks.math.columbia.edu/tag/05HZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry

universe u v w

namespace Module

/-- One stage `(A, B, M, α)` of a complete dévissage over a prime `r` of `R`.

`A` and `B` are `R`-algebras, `M` is a finite `A`-module, `B → A` is finite, `B` is smooth over
`R` with geometrically irreducible fibres, and `α : B^(⊕ multiplicity) → M` becomes an
isomorphism over the residue field of the prime `rB`. These are the conditions of Stacks 05HX
that a single stage satisfies on its own; the surjection from the algebra being dévissed, the
identification of the module being dévissed and the vanishing of the final cokernel relate a
stage to its neighbours and are not recorded here. -/
public structure DevissageStageData (R : Type u) [CommRing R] (r : Ideal R) [r.IsPrime] where
  /-- The upper `R`-algebra of the stage. -/
  A : Type u
  /-- The lower `R`-algebra of the stage. -/
  B : Type u
  [commRingA : CommRing A]
  [commRingB : CommRing B]
  [algebraRA : Algebra R A]
  [algebraRB : Algebra R B]
  /-- The module of the stage. -/
  M : Type w
  [addCommGroupM : AddCommGroup M]
  [moduleAM : Module A M]
  /-- The map from the lower to the upper algebra. -/
  toLeft : B →ₐ[R] A
  /-- The rank of the finite free module of the stage. -/
  multiplicity : ℕ
  /-- The map from the finite free `B`-module into `M`. -/
  alpha : letI : Module B M := Module.compHom M toLeft.toRingHom
    (Fin multiplicity →₀ B) →ₗ[B] M
  /-- The module of the stage is finite over the upper algebra. -/
  finiteM : Module.Finite A M
  /-- The map from the lower to the upper algebra is finite. -/
  finite_toLeft : toLeft.toRingHom.Finite
  /-- The lower algebra is smooth over `R`. -/
  smooth : Algebra.Smooth R B
  /-- The morphism `Spec B → Spec R` has geometrically irreducible fibres. -/
  geometricallyIrreducibleFibers :
    GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap R B)))
  /-- The extended ideal `rB` is prime. -/
  map_isPrime : (Ideal.map (algebraMap R B) r).IsPrime
  /-- After passing to the residue field of `rB`, the map of the stage is an isomorphism. -/
  fiber_bijective : let p := Ideal.map (algebraMap R B) r
    letI : p.IsPrime := map_isPrime
    letI : Module B M := Module.compHom M toLeft.toRingHom
    Function.Bijective (alpha.baseChange p.ResidueField)

namespace DevissageStageData

variable {R : Type u} [CommRing R] {r : Ideal R} [r.IsPrime] (st : DevissageStageData.{u, w} R r)

/-- The ring structure of the upper algebra of a stage. -/
public instance : CommRing st.A := st.commRingA

/-- The ring structure of the lower algebra of a stage. -/
public instance : CommRing st.B := st.commRingB

/-- The `R`-algebra structure of the upper algebra of a stage. -/
public instance : Algebra R st.A := st.algebraRA

/-- The `R`-algebra structure of the lower algebra of a stage. -/
public instance : Algebra R st.B := st.algebraRB

/-- The additive group structure of the module of a stage. -/
public instance : AddCommGroup st.M := st.addCommGroupM

/-- The module of a stage is a module over the upper algebra. -/
public instance : Module st.A st.M := st.moduleAM

/-- The module of a stage is finite over the upper algebra. -/
public instance : Module.Finite st.A st.M := st.finiteM

/-- The lower algebra of a stage is smooth over `R`. -/
public instance : Algebra.Smooth R st.B := st.smooth

/-- The morphism `Spec B → Spec R` of a stage has geometrically irreducible fibres. -/
public instance :
    GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap R st.B))) :=
  st.geometricallyIrreducibleFibers

/-- The extension `rB` of the prime `r` to the lower algebra of a stage is prime. -/
public instance : (Ideal.map (algebraMap R st.B) r).IsPrime := st.map_isPrime

/-- The module of a stage, as a module over the lower algebra via the map of algebras. -/
public instance moduleBM : Module st.B st.M := Module.compHom st.M st.toLeft.toRingHom

/-- The module of a stage is finite over the lower algebra, because it is finite over the upper
one and the upper algebra is finite over the lower one. -/
public instance : Module.Finite st.B st.M := by
  let _ : Algebra st.B st.A := st.toLeft.toRingHom.toAlgebra
  have : Module.Finite st.B st.A := st.finite_toLeft
  have : IsScalarTower st.B st.A st.M := ⟨fun x y z => by
    change (st.toLeft x * y) • z = st.toLeft x • y • z
    rw [mul_smul]⟩
  exact Module.Finite.trans st.A st.M

/-- The cokernel of the map of a stage, as a module over the lower algebra. It is the module
dévissed by the next stage. -/
public abbrev coker : Type w := st.M ⧸ LinearMap.range st.alpha

/-- The pointed data of a stage of a complete dévissage at a prime: a prime of the lower
algebra lying over `r` with purely transcendental residue extension, the unique prime of the
upper algebra above it, and the equality of the relative dimension of the lower algebra with
the local dimension of the support of the fibre module there.

These are the conditions of Stacks 05HZ that concern a single stage in isolation; the
compatibility of the chosen primes with the maps between consecutive stages relates a stage to
its neighbours and is not recorded here. -/
public structure Pointed where
  /-- The chosen prime of the lower algebra. -/
  lowerPrime : Ideal st.B
  /-- The chosen lower ideal is prime. -/
  lowerPrime_isPrime : lowerPrime.IsPrime
  /-- The chosen lower prime lies over `r`. -/
  lowerPrime_liesOver : lowerPrime.LiesOver r
  /-- The residue field at the chosen lower prime is purely transcendental over the residue
  field of `r`. -/
  residueField_purelyTranscendental :
    letI : lowerPrime.IsPrime := lowerPrime_isPrime
    letI : Algebra r.ResidueField lowerPrime.ResidueField :=
      (Ideal.ResidueField.mapₐ r lowerPrime (Algebra.ofId R st.B)
        lowerPrime_liesOver.over).toRingHom.toAlgebra
    PurelyTranscendental r.ResidueField lowerPrime.ResidueField
  /-- The chosen prime of the upper algebra. -/
  upperPrime : Ideal st.A
  /-- The chosen upper ideal is prime. -/
  upperPrime_isPrime : upperPrime.IsPrime
  /-- The chosen upper prime lies over the chosen lower prime. -/
  upperPrime_under : upperPrime.comap st.toLeft.toRingHom = lowerPrime
  /-- The chosen upper prime is the unique prime above the chosen lower prime. -/
  upperPrime_unique : ∀ p : Ideal st.A, p.IsPrime →
    p.comap st.toLeft.toRingHom = lowerPrime → p = upperPrime
  /-- The point of the fibre ring corresponding to the chosen lower prime belongs to the
  support of the fibre module. -/
  lowerPrime_mem_fiberSupport :
    letI : Module st.B st.M := Module.compHom st.M st.toLeft.toRingHom
    letI : Algebra st.B (r.Fiber st.B) := Algebra.TensorProduct.rightAlgebra
    (PrimeSpectrum.primesOverOrderIsoFiber R st.B r
        ⟨lowerPrime, lowerPrime_isPrime, lowerPrime_liesOver⟩) ∈
      Module.support (r.Fiber st.B) (TensorProduct st.B (r.Fiber st.B) st.M)
  /-- The relative dimension of the lower algebra is the local dimension of the support of the
  fibre module at the chosen lower prime. -/
  relativeDimension_eq_support :
    letI : lowerPrime.IsPrime := lowerPrime_isPrime
    letI : Module st.B st.M := Module.compHom st.M st.toLeft.toRingHom
    letI : Algebra st.B (r.Fiber st.B) := Algebra.TensorProduct.rightAlgebra
    Algebra.relativeDimension R st.B =
      topologicalKrullDimAt
        (↥(Module.support (r.Fiber st.B) (TensorProduct st.B (r.Fiber st.B) st.M)))
        ⟨PrimeSpectrum.primesOverOrderIsoFiber R st.B r
            ⟨lowerPrime, lowerPrime_isPrime, lowerPrime_liesOver⟩,
          lowerPrime_mem_fiberSupport⟩

/-- Prepending a stage to a family of stages. -/
public def consStages {n : ℕ} (T : Fin (n + 1) → DevissageStageData.{u, w} R r) :
    Fin (n + 1 + 1) → DevissageStageData.{u, w} R r :=
  Fin.cons st T

/-- The first stage of a family with a stage prepended is that stage. -/
@[simp]
public lemma consStages_zero {n : ℕ} (T : Fin (n + 1) → DevissageStageData.{u, w} R r) :
    st.consStages T 0 = st := rfl

/-- The later stages of a family with a stage prepended are the stages of the family. -/
@[simp]
public lemma consStages_succ {n : ℕ} (T : Fin (n + 1) → DevissageStageData.{u, w} R r)
    (i : Fin (n + 1)) : st.consStages T i.succ = T i := rfl

/-- Prepending the pointed data of a stage to a family of pointed data. -/
public def consPointed {n : ℕ} (T : Fin (n + 1) → DevissageStageData.{u, w} R r) (P : st.Pointed)
    (PT : ∀ i, (T i).Pointed) : ∀ i, (st.consStages T i).Pointed :=
  Fin.cons P PT

/-- The first pointed datum of a family with a pointed datum prepended is that datum. -/
@[simp]
public lemma consPointed_zero {n : ℕ} (T : Fin (n + 1) → DevissageStageData.{u, w} R r)
    (P : st.Pointed) (PT : ∀ i, (T i).Pointed) : st.consPointed T P PT 0 = P := rfl

/-- The later pointed data of a family with a pointed datum prepended are those of the family. -/
@[simp]
public lemma consPointed_succ {n : ℕ} (T : Fin (n + 1) → DevissageStageData.{u, w} R r)
    (P : st.Pointed) (PT : ∀ i, (T i).Pointed) (i : Fin (n + 1)) :
    st.consPointed T P PT i.succ = PT i := rfl

end DevissageStageData

namespace CompleteDevissage

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N] {r : Ideal R}
  [r.IsPrime]

/-- The stages of a complete dévissage, one at a time. -/
public def stages (D : CompleteDevissage R S N r) (i : Fin (D.stepCount + 1)) :
    DevissageStageData.{u, w} R r where
  A := D.A i
  B := D.B i
  commRingA := D.commRingA i
  commRingB := D.commRingB i
  algebraRA := D.algebraRA i
  algebraRB := D.algebraRB i
  M := D.M i
  addCommGroupM := D.addCommGroupM i
  moduleAM := D.moduleAM i
  toLeft := D.toLeft i
  multiplicity := D.multiplicity i
  alpha := D.alpha i
  finiteM := D.finiteM i
  finite_toLeft := D.left_finite i
  smooth := D.smooth i
  geometricallyIrreducibleFibers := D.geometricallyIrreducibleFibers i
  map_isPrime := D.map_isPrime i
  fiber_bijective := D.fiber_bijective i

/-- A single stage whose map is surjective, together with a presentation of the algebra being
dévissed and an identification of the module being dévissed, is a complete dévissage. This is
the base case of the recursive construction of a complete dévissage, matching
`AlgebraicGeometry.DevissageChain.last`. -/
public def ofStage (st : DevissageStageData.{u, w} R r) (toA : S →ₐ[R] st.A)
    (hsurj : Function.Surjective toA) (hfp : toA.toRingHom.FinitePresentation)
    (equiv : letI : Module S st.M := Module.compHom st.M toA.toRingHom
      N ≃ₗ[S] st.M)
    (hfinal : Function.Surjective st.alpha) : CompleteDevissage R S N r where
  stepCount := 0
  A := fun _ => st.A
  B := fun _ => st.B
  M := fun _ => st.M
  toA₀ := toA
  toLeft := fun _ => st.toLeft
  toRight := fun i => i.elim0
  multiplicity := fun _ => st.multiplicity
  alpha := fun _ => st.alpha
  finiteM := fun _ => st.finiteM
  initial_surjective := hsurj
  initial_finitePresentation := hfp
  transition_surjective := fun i => i.elim0
  transition_finitePresentation := fun i => i.elim0
  left_finite := fun _ => st.finite_toLeft
  smooth := fun _ => st.smooth
  geometricallyIrreducibleFibers := fun _ => st.geometricallyIrreducibleFibers
  initialEquiv := equiv
  cokerEquiv := fun i => i.elim0
  map_isPrime := fun _ => st.map_isPrime
  fiber_bijective := fun _ => st.fiber_bijective
  final_surjective := hfinal

/-- Prepending a stage to a complete dévissage of its cokernel gives a complete dévissage. This
is the recursive step in the construction of a complete dévissage, matching
`AlgebraicGeometry.DevissageChain.more`.

The tail dévisses an arbitrary module `N'` identified with the cokernel of the stage by `e`. -/
public def consStageData (st : DevissageStageData.{u, w} R r) (toA : S →ₐ[R] st.A)
    (hsurj : Function.Surjective toA) (hfp : toA.toRingHom.FinitePresentation)
    (equiv : letI : Module S st.M := Module.compHom st.M toA.toRingHom
      N ≃ₗ[S] st.M)
    {N' : Type w} [AddCommGroup N'] [Module st.B N'] [Module.Finite st.B N']
    (e : st.coker ≃ₗ[st.B] N') (D : CompleteDevissage R st.B N' r) :
    CompleteDevissage R S N r :=
  letI : Module st.B (D.M 0) := Module.compHom (D.M 0) D.toA₀.toRingHom
  { stepCount := D.stepCount + 1
    A := fun i => (st.consStages D.stages i).A
    B := fun i => (st.consStages D.stages i).B
    M := fun i => (st.consStages D.stages i).M
    commRingA := fun i => (st.consStages D.stages i).commRingA
    commRingB := fun i => (st.consStages D.stages i).commRingB
    algebraRA := fun i => (st.consStages D.stages i).algebraRA
    algebraRB := fun i => (st.consStages D.stages i).algebraRB
    addCommGroupM := fun i => (st.consStages D.stages i).addCommGroupM
    moduleAM := fun i => (st.consStages D.stages i).moduleAM
    toA₀ := toA
    toLeft := fun i => (st.consStages D.stages i).toLeft
    toRight := Fin.cons D.toA₀ D.toRight
    multiplicity := fun i => (st.consStages D.stages i).multiplicity
    alpha := fun i => (st.consStages D.stages i).alpha
    finiteM := fun i => (st.consStages D.stages i).finiteM
    initial_surjective := hsurj
    initial_finitePresentation := hfp
    transition_surjective := Fin.cons D.initial_surjective D.transition_surjective
    transition_finitePresentation :=
      Fin.cons D.initial_finitePresentation D.transition_finitePresentation
    left_finite := fun i => (st.consStages D.stages i).finite_toLeft
    smooth := fun i => (st.consStages D.stages i).smooth
    geometricallyIrreducibleFibers := fun i =>
      (st.consStages D.stages i).geometricallyIrreducibleFibers
    initialEquiv := equiv
    cokerEquiv :=
      Fin.cons (show st.coker ≃ₗ[st.B] D.M 0 from e.trans D.initialEquiv) D.cokerEquiv
    map_isPrime := fun i => (st.consStages D.stages i).map_isPrime
    fiber_bijective := fun i => (st.consStages D.stages i).fiber_bijective
    final_surjective := D.final_surjective }

/-- A one-stage dévissage has one stage. -/
@[simp]
public lemma stepCount_ofStage (st : DevissageStageData.{u, w} R r) (toA : S →ₐ[R] st.A)
    (hsurj : Function.Surjective toA) (hfp : toA.toRingHom.FinitePresentation)
    (equiv : letI : Module S st.M := Module.compHom st.M toA.toRingHom
      N ≃ₗ[S] st.M)
    (hfinal : Function.Surjective st.alpha) :
    (ofStage (N := N) st toA hsurj hfp equiv hfinal).stepCount = 0 := rfl

/-- The only stage of a one-stage dévissage is the given one. -/
@[simp]
public lemma stages_ofStage (st : DevissageStageData.{u, w} R r) (toA : S →ₐ[R] st.A)
    (hsurj : Function.Surjective toA) (hfp : toA.toRingHom.FinitePresentation)
    (equiv : letI : Module S st.M := Module.compHom st.M toA.toRingHom
      N ≃ₗ[S] st.M)
    (hfinal : Function.Surjective st.alpha) (i : Fin 1) :
    (ofStage (N := N) st toA hsurj hfp equiv hfinal).stages i = st := rfl

/-- Prepending a stage lengthens a dévissage by one stage. -/
@[simp]
public lemma stepCount_consStageData (st : DevissageStageData.{u, w} R r) (toA : S →ₐ[R] st.A)
    (hsurj : Function.Surjective toA) (hfp : toA.toRingHom.FinitePresentation)
    (equiv : letI : Module S st.M := Module.compHom st.M toA.toRingHom
      N ≃ₗ[S] st.M)
    {N' : Type w} [AddCommGroup N'] [Module st.B N'] [Module.Finite st.B N']
    (e : st.coker ≃ₗ[st.B] N') (D : CompleteDevissage R st.B N' r) :
    (consStageData (N := N) st toA hsurj hfp equiv e D).stepCount = D.stepCount + 1 := rfl

/-- The first stage of a dévissage with a stage prepended is that stage. -/
@[simp]
public lemma stages_consStageData_zero (st : DevissageStageData.{u, w} R r) (toA : S →ₐ[R] st.A)
    (hsurj : Function.Surjective toA) (hfp : toA.toRingHom.FinitePresentation)
    (equiv : letI : Module S st.M := Module.compHom st.M toA.toRingHom
      N ≃ₗ[S] st.M)
    {N' : Type w} [AddCommGroup N'] [Module st.B N'] [Module.Finite st.B N']
    (e : st.coker ≃ₗ[st.B] N') (D : CompleteDevissage R st.B N' r) :
    (consStageData (N := N) st toA hsurj hfp equiv e D).stages 0 = st := rfl

/-- The later stages of a dévissage with a stage prepended are the stages of the tail. -/
@[simp]
public lemma stages_consStageData_succ (st : DevissageStageData.{u, w} R r) (toA : S →ₐ[R] st.A)
    (hsurj : Function.Surjective toA) (hfp : toA.toRingHom.FinitePresentation)
    (equiv : letI : Module S st.M := Module.compHom st.M toA.toRingHom
      N ≃ₗ[S] st.M)
    {N' : Type w} [AddCommGroup N'] [Module st.B N'] [Module.Finite st.B N']
    (e : st.coker ≃ₗ[st.B] N') (D : CompleteDevissage R st.B N' r)
    (i : Fin (D.stepCount + 1)) :
    (consStageData (N := N) st toA hsurj hfp equiv e D).stages i.succ = D.stages i := rfl

end CompleteDevissage

namespace NonemptyCompleteDevissageAt

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N] {q : Ideal S}
  [q.IsPrime]

/-- The pointed data of each stage of a complete dévissage at a prime. -/
public def pointedStages (E : NonemptyCompleteDevissageAt R S N q)
    (i : Fin (E.toCompleteDevissage.stepCount + 1)) :
    (E.toCompleteDevissage.stages i).Pointed where
  lowerPrime := E.lowerPrime i
  lowerPrime_isPrime := E.lowerPrime_isPrime i
  lowerPrime_liesOver := E.lowerPrime_liesOver i
  residueField_purelyTranscendental := E.residueField_purelyTranscendental i
  upperPrime := E.upperPrime i
  upperPrime_isPrime := E.upperPrime_isPrime i
  upperPrime_under := E.upperPrime_under i
  upperPrime_unique := E.upperPrime_unique i
  lowerPrime_mem_fiberSupport := E.lowerPrime_mem_fiberSupport i
  relativeDimension_eq_support := E.relativeDimension_eq_support i

/-- A single pointed stage whose map is surjective and whose upper prime contracts to `q` is a
nonempty complete dévissage of `N/S/R` at `q`. -/
public def ofStage (st : DevissageStageData.{u, w} R (q.under R)) (P : st.Pointed)
    (toA : S →ₐ[R] st.A) (hsurj : Function.Surjective toA)
    (hfp : toA.toRingHom.FinitePresentation)
    (equiv : letI : Module S st.M := Module.compHom st.M toA.toRingHom
      N ≃ₗ[S] st.M)
    (hfinal : Function.Surjective st.alpha)
    (hinit : P.upperPrime.comap toA.toRingHom = q) :
    NonemptyCompleteDevissageAt R S N q where
  toCompleteDevissage := CompleteDevissage.ofStage st toA hsurj hfp equiv hfinal
  lowerPrime := fun _ => P.lowerPrime
  lowerPrime_isPrime := fun _ => P.lowerPrime_isPrime
  lowerPrime_liesOver := fun _ => P.lowerPrime_liesOver
  residueField_purelyTranscendental := fun _ => P.residueField_purelyTranscendental
  upperPrime := fun _ => P.upperPrime
  upperPrime_isPrime := fun _ => P.upperPrime_isPrime
  upperPrime_under := fun _ => P.upperPrime_under
  upperPrime_unique := fun _ => P.upperPrime_unique
  initial_under := hinit
  transition_under := fun i => i.elim0
  lowerPrime_mem_fiberSupport := fun _ => P.lowerPrime_mem_fiberSupport
  relativeDimension_eq_support := fun _ => P.relativeDimension_eq_support

/-- Prepending a pointed stage to a complete dévissage of its cokernel, itself equipped with
pointed data compatible with the stage, gives a nonempty complete dévissage at `q`.

The compatibility conditions are the contraction of the first upper prime to `q`, the
contraction of the tail's first upper prime to the stage's lower prime, and the contractions
inside the tail. -/
public def cons (st : DevissageStageData.{u, w} R (q.under R)) (P : st.Pointed)
    (toA : S →ₐ[R] st.A) (hsurj : Function.Surjective toA)
    (hfp : toA.toRingHom.FinitePresentation)
    (equiv : letI : Module S st.M := Module.compHom st.M toA.toRingHom
      N ≃ₗ[S] st.M)
    {N' : Type w} [AddCommGroup N'] [Module st.B N'] [Module.Finite st.B N']
    (e : st.coker ≃ₗ[st.B] N') (D : CompleteDevissage R st.B N' (q.under R))
    (PD : ∀ i, (D.stages i).Pointed)
    (hinit : P.upperPrime.comap toA.toRingHom = q)
    (hlink : (PD 0).upperPrime.comap D.toA₀.toRingHom = P.lowerPrime)
    (hlinks : ∀ i : Fin D.stepCount,
      (PD i.succ).upperPrime.comap (D.toRight i).toRingHom = (PD i.castSucc).lowerPrime) :
    NonemptyCompleteDevissageAt R S N q where
  toCompleteDevissage := CompleteDevissage.consStageData st toA hsurj hfp equiv e D
  lowerPrime := fun i => (st.consPointed D.stages P PD i).lowerPrime
  lowerPrime_isPrime := fun i => (st.consPointed D.stages P PD i).lowerPrime_isPrime
  lowerPrime_liesOver := fun i => (st.consPointed D.stages P PD i).lowerPrime_liesOver
  residueField_purelyTranscendental := fun i =>
    (st.consPointed D.stages P PD i).residueField_purelyTranscendental
  upperPrime := fun i => (st.consPointed D.stages P PD i).upperPrime
  upperPrime_isPrime := fun i => (st.consPointed D.stages P PD i).upperPrime_isPrime
  upperPrime_under := fun i => (st.consPointed D.stages P PD i).upperPrime_under
  upperPrime_unique := fun i => (st.consPointed D.stages P PD i).upperPrime_unique
  initial_under := hinit
  transition_under := Fin.cons hlink hlinks
  lowerPrime_mem_fiberSupport := fun i =>
    (st.consPointed D.stages P PD i).lowerPrime_mem_fiberSupport
  relativeDimension_eq_support := fun i =>
    (st.consPointed D.stages P PD i).relativeDimension_eq_support

end NonemptyCompleteDevissageAt

end Module

end
