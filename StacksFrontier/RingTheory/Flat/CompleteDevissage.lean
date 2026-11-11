module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.Support
public import StacksCore.FieldTheory.PurelyTranscendental
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.RelativeDimension.Defs

/-!
# Complete dévissages

Let `R → S` be a ring map of finite type, let `N` be a finite `S`-module and let `r` be a prime
of `R`. A *complete dévissage of `N/S/R` over `r`* is a finite nonempty zigzag of `R`-algebras
```
    A₀      A₁           Aₙ
  ↗    ↖  ↗    ↖  …  ↖  ↗
S        B₀        B₁        Bₙ
```
together with finite `Aᵢ`-modules `Mᵢ` and `Bᵢ`-module maps `αᵢ : Bᵢ^(⊕ rᵢ) → Mᵢ` satisfying the
presentation, finiteness, smoothness, fibre and cokernel conditions of Stacks 05HX.  A *complete
dévissage at a prime `q` of `S`* adds a compatible system of primes `qᵢ ⊆ Bᵢ` with the pure
transcendence, uniqueness and relative dimension conditions of Stacks 05HZ, and also allows the
empty dévissage of the zero module.

## Main definitions

* `Module.CompleteDevissage R S N r` is a complete dévissage of `N/S/R` over `r` (Stacks 05HX).
* `Module.NonemptyCompleteDevissageAt R S N q` records the stage data of a nonempty complete
  dévissage of `N/S/R` at `q`.
* `Module.CompleteDevissageAt R S N q` is a complete dévissage of `N/S/R` at `q` (Stacks 05HZ),
  allowing the empty dévissage of the zero module.

## Implementation notes

The base ring, the original algebra and the original module have independent universes.  The
stage algebras live in the base ring's universe, which costs no generality because an algebra of
finite type over `R` can be presented in `R`'s universe, and is what lets the fibre conditions be
stated as properties of `Spec.map`.  The stage modules live in the original module's universe.

The stages are indexed from zero: `Fin (stepCount + 1)` corresponds to the source's `1, …, n`,
while `Fin stepCount` indexes the arrows between consecutive stages.  The finite direct sum
`Bᵢ^(⊕ rᵢ)` is represented by `Fin rᵢ →₀ Bᵢ`.  The condition on `αᵢ` over the residue field is
expressed by bijectivity of its scalar extension; its source and target are canonically the
finite direct sum of residue fields and `Mᵢ ⊗[Bᵢ] κ(rBᵢ)`.

The ideal `rBᵢ` is recorded as prime so that its residue field can be formed.  This is a
consequence of smoothness and geometric irreducibility of the fibre and is proof data rather than
an additional mathematical condition.  Vanishing of the final cokernel is expressed as
surjectivity of the final map.

For a dévissage at `q` the prime of the base is canonically `q.under R`, so it is not carried as
redundant data.  The fibre ring is Mathlib's `(q.under R).Fiber Bᵢ = κ(q.under R) ⊗[R] Bᵢ`, and
the fibre module is presented canonically as this ring tensored with `Mᵢ` over `Bᵢ`; by
associativity of tensor products this is the source's `Mᵢ ⊗[R] κ(q.under R)`.  The point of the
fibre corresponding to `qᵢ` is supplied by `PrimeSpectrum.primesOverOrderIsoFiber`.  Support is
taken over the fibre ring, not over `Bᵢ` by restriction of scalars.  The `Bᵢ`-algebra structure
on the fibre ring is `Algebra.TensorProduct.rightAlgebra`, and the fibre ring acts on the fibre
module by multiplication on its first tensor factor.  The proof that this point belongs to the
module's support is recorded so that the pointed local dimension can be formed.  The transition
contraction uses the map `Bᵢ → Aᵢ₊₁`.

The empty dévissage is a separate constructor of `Module.CompleteDevissageAt` and requires the
original module to be zero.  It has no stage primes and imposes no support condition.  Stacks
05HZ as printed has no empty case: its dévissages have stages `1, …, n` with `n ≥ 1`, and
condition (4) places the first stage prime in the support of the fibre module, which forces
`q` into the support of `N`.  So upstream no complete dévissage at `q` of `N` exists when
`N_q = 0`, and the existence results Stacks 05I1 and 05HR need `N_q ≠ 0` as printed.  Admitting
the empty dévissage of the zero module is the repository's convention for that case (recorded in
`errata.md`); the nonempty case retains every condition of Stacks 05HZ.

## References

* [Stacks Project, Tag 05HX](https://stacks.math.columbia.edu/tag/05HX)
* [Stacks Project, Tag 05HZ](https://stacks.math.columbia.edu/tag/05HZ)
-/

@[expose] public section

open AlgebraicGeometry

universe u v w

namespace Module

/-- A **complete dévissage** of a finite `S`-module `N` over a prime ideal `r` of `R`.

There are `stepCount + 1` stages. At stage `i`, `A i` and `B i` are `R`-algebras,
`M i` is a finite `A i`-module, and `alpha i` maps a finite free `B i`-module to `M i`
viewed as a `B i`-module through `toLeft i`. The maps `toRight` connect consecutive stages. -/
@[stacks 05HX]
public structure CompleteDevissage (R : Type u) (S : Type v) (N : Type w) [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S] [AddCommGroup N] [Module S N]
    [Module.Finite S N] (r : Ideal R) [r.IsPrime] where
  /-- The number of transitions; the number of stages is `stepCount + 1`. -/
  stepCount : ℕ
  /-- The upper `R`-algebras in the dévissage. -/
  A : Fin (stepCount + 1) → Type u
  /-- The lower `R`-algebras in the dévissage. -/
  B : Fin (stepCount + 1) → Type u
  [commRingA : ∀ i, CommRing (A i)]
  [commRingB : ∀ i, CommRing (B i)]
  [algebraRA : ∀ i, Algebra R (A i)]
  [algebraRB : ∀ i, Algebra R (B i)]
  /-- The modules on the upper algebras. -/
  M : (i : Fin (stepCount + 1)) → Type w
  [addCommGroupM : ∀ i, AddCommGroup (M i)]
  [moduleAM : ∀ i, Module (A i) (M i)]
  /-- The map from `S` to the first upper algebra. -/
  toA₀ : S →ₐ[R] A 0
  /-- The map from each lower algebra to the upper algebra at the same stage. -/
  toLeft : ∀ i, B i →ₐ[R] A i
  /-- The map from a lower algebra to the upper algebra at the next stage. -/
  toRight : ∀ i : Fin stepCount, B i.castSucc →ₐ[R] A i.succ
  /-- The rank of the finite free module at each stage. -/
  multiplicity : Fin (stepCount + 1) → ℕ
  /-- The map from the finite free `B i`-module into `M i`. -/
  alpha : ∀ i, letI : Module (B i) (M i) := Module.compHom (M i) (toLeft i).toRingHom;
    (Fin (multiplicity i) →₀ B i) →ₗ[B i] M i
  /-- Every `M i` is finite over `A i`. -/
  finiteM : ∀ i, @Module.Finite (A i) (M i) _ _ (moduleAM i)
  /-- The map from `S` to the first upper algebra is surjective. -/
  initial_surjective : Function.Surjective toA₀
  /-- The map from `S` to the first upper algebra is of finite presentation. -/
  initial_finitePresentation : toA₀.toRingHom.FinitePresentation
  /-- Every map from a lower algebra to the next upper algebra is surjective. -/
  transition_surjective : ∀ i, Function.Surjective (toRight i)
  /-- Every map from a lower algebra to the next upper algebra is of finite presentation. -/
  transition_finitePresentation : ∀ i, (toRight i).toRingHom.FinitePresentation
  /-- Every map from a lower algebra to the upper algebra at the same stage is finite. -/
  left_finite : ∀ i, (toLeft i).toRingHom.Finite
  /-- Every lower algebra is smooth over `R`. -/
  smooth : ∀ i, letI := algebraRB i; Algebra.Smooth R (B i)
  /-- The morphism `Spec(B i) → Spec(R)` has geometrically irreducible fibres. -/
  geometricallyIrreducibleFibers : ∀ i,
    GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap R (B i))))
  /-- The original module is the first module after restricting scalars along `S → A 0`. -/
  initialEquiv : letI : Module S (M 0) := Module.compHom (M 0) toA₀.toRingHom; N ≃ₗ[S] M 0
  /-- The cokernel at a nonfinal stage is the module at the next stage. -/
  cokerEquiv : ∀ i : Fin stepCount,
    letI : Module (B i.castSucc) (M i.castSucc) :=
      Module.compHom (M i.castSucc) (toLeft i.castSucc).toRingHom
    letI : Module (B i.castSucc) (M i.succ) :=
      Module.compHom (M i.succ) (toRight i).toRingHom
    (M i.castSucc ⧸ LinearMap.range (alpha i.castSucc)) ≃ₗ[B i.castSucc] M i.succ
  /-- The extended ideal `rB i` is prime. This is proof data supplied by the preceding
  smoothness and fibre hypotheses. -/
  map_isPrime : ∀ i, (Ideal.map (algebraMap R (B i)) r).IsPrime
  /-- After passing to the residue field of `rB i`, `alpha i` is an isomorphism. -/
  fiber_bijective : ∀ i, let p := Ideal.map (algebraMap R (B i)) r;
    letI : p.IsPrime := map_isPrime i
    letI : Module (B i) (M i) := Module.compHom (M i) (toLeft i).toRingHom
    Function.Bijective ((alpha i).baseChange p.ResidueField)
  /-- The cokernel of the map at the final stage vanishes. -/
  final_surjective : let i := Fin.last stepCount;
    letI : Module (B i) (M i) := Module.compHom (M i) (toLeft i).toRingHom
    Function.Surjective (alpha i)

namespace CompleteDevissage

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N] {r : Ideal R}
  [r.IsPrime]

/-- The upper algebra at each stage is a commutative ring. -/
public instance (D : CompleteDevissage R S N r) (i : Fin (D.stepCount + 1)) :
    CommRing (D.A i) := D.commRingA i

/-- The lower algebra at each stage is a commutative ring. -/
public instance (D : CompleteDevissage R S N r) (i : Fin (D.stepCount + 1)) :
    CommRing (D.B i) := D.commRingB i

/-- The upper algebra at each stage is an `R`-algebra. -/
public instance (D : CompleteDevissage R S N r) (i : Fin (D.stepCount + 1)) :
    Algebra R (D.A i) := D.algebraRA i

/-- The lower algebra at each stage is an `R`-algebra. -/
public instance (D : CompleteDevissage R S N r) (i : Fin (D.stepCount + 1)) :
    Algebra R (D.B i) := D.algebraRB i

/-- The module at each stage is an additive commutative group. -/
public instance (D : CompleteDevissage R S N r) (i : Fin (D.stepCount + 1)) :
    AddCommGroup (D.M i) := D.addCommGroupM i

/-- The module at each stage is a module over the upper algebra at that stage. -/
public instance (D : CompleteDevissage R S N r) (i : Fin (D.stepCount + 1)) :
    Module (D.A i) (D.M i) := D.moduleAM i

/-- The module at each stage is finite over the upper algebra at that stage. -/
public instance (D : CompleteDevissage R S N r) (i : Fin (D.stepCount + 1)) :
    Module.Finite (D.A i) (D.M i) := D.finiteM i

/-- The lower algebra at each stage is smooth over `R`. -/
public instance (D : CompleteDevissage R S N r) (i : Fin (D.stepCount + 1)) :
    Algebra.Smooth R (D.B i) := D.smooth i

/-- The fibres of `Spec` of the lower algebra at each stage over `Spec R` are geometrically
  irreducible. -/
public instance (D : CompleteDevissage R S N r) (i : Fin (D.stepCount + 1)) :
    GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap R (D.B i)))) :=
  D.geometricallyIrreducibleFibers i

/-- The extension of `r` to the lower algebra at each stage is prime. -/
public instance (D : CompleteDevissage R S N r) (i : Fin (D.stepCount + 1)) :
    (Ideal.map (algebraMap R (D.B i)) r).IsPrime := D.map_isPrime i

end CompleteDevissage

/-- A **nonempty complete dévissage at `q`** of a finite `S`-module `N`.

At every stage this records a prime `lowerPrime i` of the smooth algebra `B i`, the unique
prime `upperPrime i` of `A i` above it, and compatibility of these primes with the initial
and transition maps.  The residue extension at `lowerPrime i` is purely transcendental, and
the relative dimension of `B i` equals the local dimension of the support of the fibre
module. -/
public structure NonemptyCompleteDevissageAt (R : Type u) (S : Type v) (N : Type w)
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    [AddCommGroup N] [Module S N] [Module.Finite S N]
    (q : Ideal S) [q.IsPrime] where
  /-- The underlying complete dévissage over the prime below `q`. -/
  toCompleteDevissage : CompleteDevissage R S N (q.under R)
  /-- The chosen prime of the lower algebra at each stage. -/
  lowerPrime : ∀ i, Ideal (toCompleteDevissage.B i)
  /-- Each chosen lower ideal is prime. -/
  lowerPrime_isPrime : ∀ i, (lowerPrime i).IsPrime
  /-- Each chosen lower prime lies over the prime below `q`. -/
  lowerPrime_liesOver : ∀ i, (lowerPrime i).LiesOver (q.under R)
  /-- The residue field at every chosen lower prime is purely transcendental over the
  residue field of the prime below `q`. -/
  residueField_purelyTranscendental : ∀ i,
    letI : (lowerPrime i).IsPrime := lowerPrime_isPrime i
    letI : Algebra (q.under R).ResidueField (lowerPrime i).ResidueField :=
      (Ideal.ResidueField.mapₐ (q.under R) (lowerPrime i)
        (Algebra.ofId R (toCompleteDevissage.B i))
        (lowerPrime_liesOver i).over).toRingHom.toAlgebra
    PurelyTranscendental (q.under R).ResidueField (lowerPrime i).ResidueField
  /-- The chosen prime of the upper algebra at each stage. -/
  upperPrime : ∀ i, Ideal (toCompleteDevissage.A i)
  /-- Each chosen upper ideal is prime. -/
  upperPrime_isPrime : ∀ i, (upperPrime i).IsPrime
  /-- The chosen upper prime lies over the chosen lower prime. -/
  upperPrime_under : ∀ i,
    (upperPrime i).comap (toCompleteDevissage.toLeft i).toRingHom = lowerPrime i
  /-- The chosen upper prime is the unique prime above the chosen lower prime. -/
  upperPrime_unique : ∀ i (p : Ideal (toCompleteDevissage.A i)),
    p.IsPrime →
      p.comap (toCompleteDevissage.toLeft i).toRingHom = lowerPrime i →
        p = upperPrime i
  /-- The original prime is the contraction of the first upper prime. -/
  initial_under :
    (upperPrime 0).comap toCompleteDevissage.toA₀.toRingHom = q
  /-- Consecutive stages carry compatible primes. -/
  transition_under : ∀ i : Fin toCompleteDevissage.stepCount,
    (upperPrime i.succ).comap (toCompleteDevissage.toRight i).toRingHom =
      lowerPrime i.castSucc
  /-- The point of the fibre ring corresponding to the chosen lower prime belongs to the support
  of the fibre module. -/
  lowerPrime_mem_fiberSupport : ∀ i,
    letI : Module (toCompleteDevissage.B i) (toCompleteDevissage.M i) :=
      Module.compHom (toCompleteDevissage.M i)
        (toCompleteDevissage.toLeft i).toRingHom
    letI : Algebra (toCompleteDevissage.B i)
        ((q.under R).Fiber (toCompleteDevissage.B i)) :=
      Algebra.TensorProduct.rightAlgebra
    (PrimeSpectrum.primesOverOrderIsoFiber R (toCompleteDevissage.B i) (q.under R)
        ⟨lowerPrime i, lowerPrime_isPrime i, lowerPrime_liesOver i⟩) ∈
      Module.support ((q.under R).Fiber (toCompleteDevissage.B i))
        (TensorProduct (toCompleteDevissage.B i)
          ((q.under R).Fiber (toCompleteDevissage.B i)) (toCompleteDevissage.M i))
  /-- At each stage the relative dimension equals the local dimension of the support of the
  tensor-product fibre module at the chosen lower prime. -/
  relativeDimension_eq_support : ∀ i,
    letI : (lowerPrime i).IsPrime := lowerPrime_isPrime i
    letI : Module (toCompleteDevissage.B i) (toCompleteDevissage.M i) :=
      Module.compHom (toCompleteDevissage.M i)
        (toCompleteDevissage.toLeft i).toRingHom
    letI : Algebra (toCompleteDevissage.B i)
        ((q.under R).Fiber (toCompleteDevissage.B i)) :=
      Algebra.TensorProduct.rightAlgebra
    Algebra.relativeDimension R (toCompleteDevissage.B i) =
      topologicalKrullDimAt
        (↥(Module.support ((q.under R).Fiber (toCompleteDevissage.B i))
          (TensorProduct (toCompleteDevissage.B i)
            ((q.under R).Fiber (toCompleteDevissage.B i)) (toCompleteDevissage.M i))))
        ⟨PrimeSpectrum.primesOverOrderIsoFiber R (toCompleteDevissage.B i) (q.under R)
            ⟨lowerPrime i, lowerPrime_isPrime i, lowerPrime_liesOver i⟩,
          lowerPrime_mem_fiberSupport i⟩

namespace NonemptyCompleteDevissageAt

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N]
  {q : Ideal S} [q.IsPrime]

/-- The chosen lower prime at each stage is prime. -/
public instance (D : NonemptyCompleteDevissageAt R S N q)
    (i : Fin (D.toCompleteDevissage.stepCount + 1)) :
    (D.lowerPrime i).IsPrime := D.lowerPrime_isPrime i

/-- The chosen upper prime at each stage is prime. -/
public instance (D : NonemptyCompleteDevissageAt R S N q)
    (i : Fin (D.toCompleteDevissage.stepCount + 1)) :
    (D.upperPrime i).IsPrime := D.upperPrime_isPrime i

/-- The chosen lower prime at each stage lies over the prime below `q`. -/
public instance (D : NonemptyCompleteDevissageAt R S N q)
    (i : Fin (D.toCompleteDevissage.stepCount + 1)) :
    (D.lowerPrime i).LiesOver (q.under R) := D.lowerPrime_liesOver i

/-- The residue field at the chosen lower prime is an algebra over the residue field of the
  prime below `q`. -/
public noncomputable instance (D : NonemptyCompleteDevissageAt R S N q)
    (i : Fin (D.toCompleteDevissage.stepCount + 1)) :
    Algebra (q.under R).ResidueField (D.lowerPrime i).ResidueField :=
  (Ideal.ResidueField.mapₐ (q.under R) (D.lowerPrime i)
    (Algebra.ofId R (D.toCompleteDevissage.B i))
    (D.lowerPrime_liesOver i).over).toRingHom.toAlgebra

/-- The residue field at the chosen lower prime is purely transcendental over the residue
  field of the prime below `q`. -/
public instance (D : NonemptyCompleteDevissageAt R S N q)
    (i : Fin (D.toCompleteDevissage.stepCount + 1)) :
    PurelyTranscendental (q.under R).ResidueField (D.lowerPrime i).ResidueField :=
  D.residueField_purelyTranscendental i

end NonemptyCompleteDevissageAt

/-- A **complete dévissage at `q`** is either the empty dévissage of the zero module,
or a nonempty dévissage with the prime and dimension conditions of Stacks 05HZ.  The empty case
is the repository's convention for `N = 0`; Stacks 05HZ as printed has no empty case. -/
@[stacks 05HZ "the empty dévissage of N = 0 is added as the repository's convention; the \
  nonempty case is the printed definition"]
public inductive CompleteDevissageAt (R : Type u) (S : Type v) (N : Type w)
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    [AddCommGroup N] [Module S N] [Module.Finite S N]
    (q : Ideal S) [q.IsPrime] where
  /-- The empty dévissage exists precisely for the zero module. -/
  | empty (isZero : Subsingleton N)
  /-- A nonempty family of stages satisfying the pointed dévissage conditions. -/
  | nonempty (data : NonemptyCompleteDevissageAt R S N q)

namespace CompleteDevissageAt

variable {R : Type u} {S : Type v} {N : Type w}
  [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
  [AddCommGroup N] [Module S N] [Module.Finite S N] {q : Ideal S} [q.IsPrime]

/-- The number of stages, including zero for an empty dévissage. -/
public def length : CompleteDevissageAt R S N q → ℕ
  | .empty _ => 0
  | .nonempty D => D.toCompleteDevissage.stepCount + 1

/-- The smooth lower algebra at each stage. -/
public def lowerAlgebra (D : CompleteDevissageAt R S N q) : Fin D.length → Type u :=
  match D with
  | .empty _ => Fin.elim0
  | .nonempty D => D.toCompleteDevissage.B

/-- The lower algebra at each stage is a commutative ring. -/
public instance (D : CompleteDevissageAt R S N q) (i : Fin D.length) :
    CommRing (D.lowerAlgebra i) := by
  cases D with
  | empty _ => exact Fin.elim0 i
  | nonempty D => exact D.toCompleteDevissage.commRingB i

/-- The lower algebra at each stage is an `R`-algebra. -/
public instance (D : CompleteDevissageAt R S N q) (i : Fin D.length) :
    Algebra R (D.lowerAlgebra i) := by
  cases D with
  | empty _ => exact Fin.elim0 i
  | nonempty D => exact D.toCompleteDevissage.algebraRB i

/-- The rank of the finite free module at each stage. -/
public def multiplicity (D : CompleteDevissageAt R S N q) : Fin D.length → ℕ :=
  match D with
  | .empty _ => Fin.elim0
  | .nonempty D => D.toCompleteDevissage.multiplicity

end CompleteDevissageAt

end Module

end
