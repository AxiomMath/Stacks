module

public import StacksFrontier.AlgebraicGeometry.Flatness.FinitePresentationStalk

/-!
# The dévissage route to finite presentation of a flat stalk

`StacksFrontier.AlgebraicGeometry.Flatness.FinitePresentationStalk` proves Stacks 05I7, that the
stalk of a finite type quasi-coherent module which is flat over the base at a point is a finitely
presented module over the local ring at that point, granted
`Stacks.Flatness.ExistsSpreadOutFinitePresentation`, the local-algebra form of Stacks 05I5. This
file replaces that hypothesis by the *existence of a complete dévissage* after the same spreading
out, which is the local-algebra form of Stacks 05I1, together with the constructibility input of
Stacks 05FT.

The resulting statement is **logically weaker** than the one it is derived from: the existence of
a dévissage implies the spreading out of finite presentation — that implication is
`Stacks.Flatness.existsSpreadOutFinitePresentation_of_existsSpreadOutCompleteDevissage` below —
and no converse is proved or expected, since a dévissage carries smooth lower algebras with
geometrically irreducible fibres and a stagewise system of maps out of finite free modules, none
of which finite presentation alone provides. The point of the reduction is not logical strength
but that it is the form the dévissage machinery of
`StacksFrontier.RingTheory.Flat.DevissageProjectiveStages` and
`StacksFrontier.RingTheory.Flat.DevissageLocalize` actually produces.

## What is new about the input

Stacks 05I4 is available in this repository as
`Module.CompleteDevissageAt.finitePresentation_of_flat`, whose argument is a
`Module.CompleteDevissageAt`, i.e. a `Module.CompleteDevissage` together with the
twelve extra fields of `Module.NonemptyCompleteDevissageAt`. Only nine of those twelve are
used: the recursion `Module.CompleteDevissage.flat_localizedModule_stage` and the injectivity
lemma `Module.CompleteDevissage.injective_alpha` take the stage primes and their compatibilities
as explicit arguments, and never mention

* `residueField_purelyTranscendental`,
* `lowerPrime_mem_fiberSupport`, or
* `relativeDimension_eq_support`.

`Module.CompleteDevissage.PrimeData` below packages exactly the nine that are used, and
`Module.CompleteDevissage.finitePresentation_of_flat` draws the finite-presentation conclusion of
Stacks 05I4 from a plain dévissage carrying such prime data. So a construction of a dévissage
need not establish pure transcendence of the residue field extensions nor compute the relative
dimension against the pointed local dimension of the fibre support in order to reach Stacks 05I7.
It also drops the hypothesis `q.under R = IsLocalRing.maximalIdeal R` carried by
`Stacks.Flatness.exists_flatLocalExtension_finitePresentation_of_completeDevissage`, which is a
consequence of the prime data rather than an extra assumption.

## Main definitions

* `Module.CompleteDevissage.PrimeData` is the system of stage primes of a dévissage at a prime
  `q` of the original algebra, with the nine conditions that Stacks 05I4's finite-presentation
  conclusion uses.
* `Stacks.Flatness.ExistsSpreadOutCompleteDevissage` is the local-algebra obligation that
  replaces `Stacks.Flatness.ExistsSpreadOutFinitePresentation`: the same spreading out, but
  producing a complete dévissage with prime data instead of finite presentation.

## Main results

* `Module.CompleteDevissage.finitePresentation_of_flat` is Stacks 05I4's finite presentation from
  a plain complete dévissage with prime data.
* `Module.NonemptyCompleteDevissageAt.primeData` extracts the prime data from a dévissage at a
  prime, so the new input is implied by the old one.
* `Stacks.Flatness.existsSpreadOutFinitePresentation_of_existsSpreadOutCompleteDevissage` derives
  the spreading out of finite presentation from the spreading out of a dévissage.
* `AlgebraicGeometry.finitePresentation_stalk_of_existsSpreadOutCompleteDevissage` is Stacks 05I7
  granted that obligation and the constructibility input of Stacks 05FT.
* `Stacks.Flatness.exists_spreadOut_finitePresentation_of_isNoetherianRing` proves the conclusion
  of `Stacks.Flatness.ExistsSpreadOutFinitePresentation` outright over a Noetherian local base,
  with no spreading out at all. This is the instance in which the two obligations visibly differ:
  over a Noetherian base the finite-presentation obligation is a theorem, while the existence of
  a complete dévissage remains the full content of Stacks 05I1.

## Implementation notes

The prime data is a structure rather than a conjunction of hypotheses because the upper primes
are quantified over the stage index and referred to by the uniqueness and compatibility
conditions, and because it has to be existentially quantified in
`Stacks.Flatness.ExistsSpreadOutCompleteDevissage` after the dévissage it depends on.

The obligation is stated with the spread-out module written as the tensor product `A' ⊗[A] N`,
matching `Stacks.Flatness.ExistsSpreadOutFinitePresentation` clause for clause so that the two
can be compared directly; the `R'`-module structure and scalar tower on it are found by instance
search and are not carried as data.

## References

* [Stacks Project, Tag 05I7](https://stacks.math.columbia.edu/tag/05I7)
* [Stacks Project, Tag 05I5](https://stacks.math.columbia.edu/tag/05I5)
* [Stacks Project, Tag 05I4](https://stacks.math.columbia.edu/tag/05I4)
* [Stacks Project, Tag 05I1](https://stacks.math.columbia.edu/tag/05I1)
* [Stacks Project, Tag 05FT](https://stacks.math.columbia.edu/tag/05FT)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Module.CompleteDevissage

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N] {r : Ideal R}
  [r.IsPrime]

/-- The **stage primes of a complete dévissage at a prime `q`**, with the conditions that the
finite-presentation conclusion of Stacks 05I4 uses.

At every stage this records a prime of the lower algebra lying over the prime `r` of the base,
the unique prime of the upper algebra above it, and compatibility of these primes with the
surjections `S → A₀` and `Bᵢ → Aᵢ₊₁`.

These are nine of the twelve fields that `Module.NonemptyCompleteDevissageAt` adds to a
`Module.CompleteDevissage`; the three it omits —  pure transcendence of the residue field
extension at each stage prime, membership of the corresponding point of the fibre in the support
of the fibre module, and the equality of the relative dimension with the pointed local dimension
of that support — are not used by `Module.CompleteDevissage.finitePresentation_of_flat`. -/
structure PrimeData (D : CompleteDevissage R S N r) (q : Ideal S) where
  /-- The chosen prime of the lower algebra at each stage. -/
  lowerPrime : ∀ i, Ideal (D.B i)
  /-- Each chosen lower ideal is prime. -/
  lowerPrime_isPrime : ∀ i, (lowerPrime i).IsPrime
  /-- Each chosen lower prime contracts to the prime of the base. -/
  lowerPrime_under : ∀ i, (lowerPrime i).comap (algebraMap R (D.B i)) = r
  /-- The chosen prime of the upper algebra at each stage. -/
  upperPrime : ∀ i, Ideal (D.A i)
  /-- Each chosen upper ideal is prime. -/
  upperPrime_isPrime : ∀ i, (upperPrime i).IsPrime
  /-- The chosen upper prime contracts to the chosen lower prime. -/
  upperPrime_under : ∀ i, (upperPrime i).comap (D.toLeft i).toRingHom = lowerPrime i
  /-- The chosen upper prime is the unique prime above the chosen lower prime. -/
  upperPrime_unique : ∀ i (p : Ideal (D.A i)), p.IsPrime →
    p.comap (D.toLeft i).toRingHom = lowerPrime i → p = upperPrime i
  /-- The given prime of `S` is the contraction of the first upper prime. -/
  initial_under : (upperPrime 0).comap D.toA₀.toRingHom = q
  /-- Consecutive stages carry compatible primes. -/
  transition_under : ∀ i : Fin D.stepCount,
    (upperPrime i.succ).comap (D.toRight i).toRingHom = lowerPrime i.castSucc

/-- **The prime of `S` carried by prime data lies over the prime of the base.** This is why
`Module.CompleteDevissage.finitePresentation_of_flat` needs no hypothesis relating `q` to the
maximal ideal, unlike
`Stacks.Flatness.exists_flatLocalExtension_finitePresentation_of_completeDevissage`.

At stage zero the prime of `S` is the contraction of the first upper prime, which contracts to
the first lower prime along `B₀ → A₀`, which in turn contracts to the prime of the base; and both
`S → A₀` and `B₀ → A₀` are `R`-algebra maps, so contracting through either computes the
contraction of the first upper prime to `R`. -/
theorem PrimeData.under_eq {D : CompleteDevissage R S N r} {q : Ideal S} (pd : D.PrimeData q) :
    q.comap (algebraMap R S) = r := by
  have h0 : D.toA₀.toRingHom.comp (algebraMap R S) = algebraMap R (D.A 0) :=
    D.toA₀.comp_algebraMap
  have h1 : (D.toLeft 0).toRingHom.comp (algebraMap R (D.B 0)) = algebraMap R (D.A 0) :=
    (D.toLeft 0).comp_algebraMap
  rw [← pd.initial_under, Ideal.comap_comap, h0, ← h1, ← Ideal.comap_comap,
    pd.upperPrime_under 0, pd.lowerPrime_under 0]

/-- **Stacks Project, Tag 05I4, finite presentation, from a complete dévissage over the closed
point together with prime data.**

Let `R` be a local ring, let `S` be an `R`-algebra of finite presentation and let `N` be a finite
`S`-module which is flat over `R` after localizing at a prime `q` of `S`. If `N/S/R` carries a
complete dévissage over the maximal ideal of `R` and a compatible system of stage primes over
`q`, then `N` is a finitely presented `S`-module.

This is `Module.CompleteDevissageAt.finitePresentation_of_flat` with its argument replaced by a
plain `Module.CompleteDevissage` and the nine stage-prime conditions it uses, in place of a
`Module.CompleteDevissageAt`. The proof is the composition of three steps from the library: the
lower
algebras are projective over `R` by Stacks 05FT — unconditionally, since the constructibility of
the geometrically integral fibre locus is a theorem, with Stacks 056T
supplied by `AlgebraicGeometry.geometricallyReduced_of_smooth`; the downward recursion of
Stacks 05I4 then
propagates flatness at `q` to flatness of every stage module at its stage prime; Stacks 05I3
turns that into injectivity of every `alpha i`; and the dévissage then presents `N`.

The hypothesis that `q` lies over the maximal ideal of `R` is not needed: it follows from
`Module.CompleteDevissage.PrimeData.initial_under` and
`Module.CompleteDevissage.PrimeData.lowerPrime_under` at stage zero. -/
theorem finitePresentation_of_flat [IsLocalRing R] [Module R N] [IsScalarTower R S N]
    [Algebra.FinitePresentation R S]
    (D : CompleteDevissage R S N (IsLocalRing.maximalIdeal R))
    {q : Ideal S} [q.IsPrime] (pd : D.PrimeData q)
    (hflat : Module.Flat R (LocalizedModule q.primeCompl N)) :
    Module.FinitePresentation S N := by
  have hproj : ∀ i, Module.Projective R (D.B i) := projective_lowerAlgebra D
  exact D.finitePresentation_of_injective_alpha fun i =>
    D.injective_alpha rfl hproj pd.lowerPrime pd.lowerPrime_isPrime pd.lowerPrime_under
      (fun j => D.flat_localizedModule_stage rfl hproj q pd.lowerPrime pd.lowerPrime_isPrime
        pd.lowerPrime_under pd.upperPrime pd.upperPrime_isPrime pd.upperPrime_under
        pd.upperPrime_unique pd.initial_under pd.transition_under hflat j) i

end Module.CompleteDevissage

namespace Module.NonemptyCompleteDevissageAt

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N] {q : Ideal S}
  [q.IsPrime]

/-- A complete dévissage *at* a prime carries the prime data of its underlying dévissage: the
nine conditions of `Module.CompleteDevissage.PrimeData` are among its fields, the contraction of
a stage prime to the base being recorded as a `LiesOver` instance. -/
def primeData (E : NonemptyCompleteDevissageAt R S N q) :
    E.toCompleteDevissage.PrimeData q where
  lowerPrime := E.lowerPrime
  lowerPrime_isPrime := E.lowerPrime_isPrime
  lowerPrime_under i := ((E.lowerPrime_liesOver i).over).symm
  upperPrime := E.upperPrime
  upperPrime_isPrime := E.upperPrime_isPrime
  upperPrime_under := E.upperPrime_under
  upperPrime_unique := E.upperPrime_unique
  initial_under := E.initial_under
  transition_under := E.transition_under

end Module.NonemptyCompleteDevissageAt

namespace Stacks.Flatness

/-- **The local-algebra form of Stacks 05I1 in the shape Stacks 05I5 consumes it**: a finite
module over an algebra of finite presentation over a local ring, flat over that ring after
localizing at a prime of the closed fibre, acquires a complete dévissage after a flat local base
change together with a flat extension of the algebra.

This is `Stacks.Flatness.ExistsSpreadOutFinitePresentation` with its conclusion
`Module.FinitePresentation A' (A' ⊗[A] N)` replaced by the existence of a complete dévissage of
`A' ⊗[A] N` over the maximal ideal of `R'` with prime data over `q'`, plus flatness of the
localization of `A' ⊗[A] N` at `q'` over `R'`. Every other clause is identical, so the two
obligations can be compared clause by clause.

In the Stacks Project this is the algebraic content of Proposition 38.10.3's second proof: the
elementary étale neighbourhood and the dévissage come from Stacks 05HR, and the base change to
the local ring of the base is Stacks 05I1's localization step, available here as
`Module.CompleteDevissage.localizeAtPrime`. -/
def ExistsSpreadOutCompleteDevissage : Prop :=
  ∀ (R A : Type u) [CommRing R] [CommRing A] [IsLocalRing R] [Algebra R A]
    [Algebra.FinitePresentation R A] (q : Ideal A) [q.IsPrime],
    q.comap (algebraMap R A) = IsLocalRing.maximalIdeal R →
    ∀ (N : Type u) [AddCommGroup N] [Module A N] [Module.Finite A N] [Module R N]
      [IsScalarTower R A N], Module.Flat R (LocalizedModule q.primeCompl N) →
      ∃ (R' : Type u) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R')
        (_ : IsLocalHom (algebraMap R R')) (_ : Module.Flat R R')
        (A' : Type u) (_ : CommRing A') (_ : Algebra R' A')
        (_ : Algebra.FinitePresentation R' A') (_ : Algebra A A') (_ : Module.Flat A A')
        (q' : Ideal A') (_ : q'.IsPrime),
        q = q'.comap (algebraMap A A') ∧
          Module.Flat R' (LocalizedModule q'.primeCompl (A' ⊗[A] N)) ∧
          ∃ D : Module.CompleteDevissage R' A' (A' ⊗[A] N) (IsLocalRing.maximalIdeal R'),
            Nonempty (D.PrimeData q')

/-- **The spreading out of finite presentation follows from the spreading out of a complete
dévissage**, granted the constructibility input of Stacks 05FT.

This is `Module.CompleteDevissage.finitePresentation_of_flat` applied to the dévissage supplied
by `Stacks.Flatness.ExistsSpreadOutCompleteDevissage`, over the local ring `R'` and the algebra
`A'` of finite presentation over it. Every other clause of the two obligations is the same and is
passed through unchanged.

Consequently `Stacks.Flatness.ExistsSpreadOutCompleteDevissage` is a *stronger* hypothesis than
`Stacks.Flatness.ExistsSpreadOutFinitePresentation`, and the Stacks 05I7 statement derived from
it below is correspondingly weaker than
`AlgebraicGeometry.finitePresentation_stalk_of_existsSpreadOut`. -/
theorem existsSpreadOutFinitePresentation_of_existsSpreadOutCompleteDevissage
    (H : ExistsSpreadOutCompleteDevissage.{u}) :
    ExistsSpreadOutFinitePresentation.{u} := by
  intro R A _ _ _ _ _ q _ hq N _ _ _ _ _ hflat
  obtain ⟨R', _, _, _, _, _, A', _, _, _, _, _, q', _, hqq', hflat', D, ⟨pd⟩⟩ :=
    H R A q hq N hflat
  exact ⟨R', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, A',
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, q',
    inferInstance, hqq', D.finitePresentation_of_flat pd hflat'⟩

/-- **The conclusion of `Stacks.Flatness.ExistsSpreadOutFinitePresentation` over a Noetherian
local base, with no spreading out.**

If the local base ring `R` is Noetherian then an `R`-algebra `A` of finite presentation is
Noetherian, so a finite `A`-module is already finitely presented and one may take `R' = R`,
`A' = A` and `q' = q`. Neither flatness of the module nor any étale localization is used.

This is the instance in which `Stacks.Flatness.ExistsSpreadOutFinitePresentation` and
`Stacks.Flatness.ExistsSpreadOutCompleteDevissage` visibly differ: the Noetherian case of the
former is this theorem, whereas the Noetherian case of the latter still asserts the existence of
a complete dévissage, which is the full content of Stacks 05I1. -/
theorem exists_spreadOut_finitePresentation_of_isNoetherianRing (R A : Type u) [CommRing R]
    [CommRing A] [IsLocalRing R] [IsNoetherianRing R] [Algebra R A]
    [Algebra.FinitePresentation R A] (q : Ideal A) [q.IsPrime] (N : Type u) [AddCommGroup N]
    [Module A N] [Module.Finite A N] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R')
      (_ : IsLocalHom (algebraMap R R')) (_ : Module.Flat R R')
      (A' : Type u) (_ : CommRing A') (_ : Algebra R' A')
      (_ : Algebra.FinitePresentation R' A') (_ : Algebra A A') (_ : Module.Flat A A')
      (q' : Ideal A') (_ : q'.IsPrime),
      q = q'.comap (algebraMap A A') ∧ Module.FinitePresentation A' (A' ⊗[A] N) := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  refine ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, A,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, q,
    inferInstance, (Ideal.comap_id q).symm, ?_⟩
  have : Module.FinitePresentation A N := Module.finitePresentation_of_finite A N
  exact Module.FinitePresentation.of_equiv (TensorProduct.lid A N).symm

end Stacks.Flatness

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 05I7, granted the local-algebra form of Tag 05I1 and the
constructibility input of Tag 05FT.** A quasi-coherent module of finite type which is flat over
the base at a point has a finitely presented stalk at that point.

This is `AlgebraicGeometry.finitePresentation_stalk_of_existsSpreadOut` with its hypothesis
discharged from `Stacks.Flatness.ExistsSpreadOutCompleteDevissage`, so that what remains open is
the existence of a complete dévissage after the spreading out rather than the finite presentation
it implies.

Being a stronger hypothesis, this is a weaker statement than
`AlgebraicGeometry.finitePresentation_stalk_of_existsSpreadOut`; it is recorded because the
dévissage is what the construction of Stacks 05HR produces and what
`Module.CompleteDevissage.localizeAtPrime` transports to the local ring of the base. -/
theorem finitePresentation_stalk_of_existsSpreadOutCompleteDevissage
    (H : Stacks.Flatness.ExistsSpreadOutCompleteDevissage.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (x : X)
    (hflat : IsFlatOverAt f.toLRSHom.toShHom F x) :
    letI : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    Module.FinitePresentation (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
  finitePresentation_stalk_of_existsSpreadOut
    (Stacks.Flatness.existsSpreadOutFinitePresentation_of_existsSpreadOutCompleteDevissage
      H) f F x hflat

end AlgebraicGeometry

end
