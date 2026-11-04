module

public import StacksFrontier.RingTheory.Flat.DevissageLength

/-!
# A complete dévissage exists: the one-stage dévissage of a field over itself

Every result about complete dévissages in this library — Stacks 05I3, Stacks 05I4, Stacks 05I7,
Stacks 05ID — takes a dévissage as a *hypothesis*. Before this file no term of
`Module.CompleteDevissage` was ever built: the only declaration producing a
`Module.DevissageStage` is `Module.CompleteDevissage.head`, which consumes a dévissage already,
and the only constructor of `Module.CompleteDevissageAt` ever applied is `empty`, which demands
`Subsingleton N`. So the recursion had no base case and nothing bottomed out; every one of those
theorems was open to the objection that its hypothesis set might be satisfiable only by the zero
module.

This file closes that objection for `Module.CompleteDevissage` by building one explicitly:
`Module.CompleteDevissage.ofField`, the dévissage of a field `k` as a module over itself over
itself, with one stage, lower algebra `k`, and multiplicity `1`. It is not the empty dévissage —
`k` is nontrivial and the stage count is `0`, so there is exactly one stage — and so the
conclusion of Stacks 05I4 at this dévissage is an isomorphism onto a direct sum over a *nonempty*
index type.

## Main results

* `AlgebraicGeometry.GeometricallyIrreducible.of_isIso`: an isomorphism of schemes has
  geometrically irreducible fibres. Needed for the `geometricallyIrreducibleFibers` field, and
  absent from Mathlib, which has the base change, composition and restriction instances for
  `GeometricallyIrreducible` but nothing for an isomorphism or an identity.
* `LinearEquiv.bijective_baseChange`: the base change of a linear equivalence along any algebra
  is bijective. Needed for the `fiber_bijective` field.
* `Module.CompleteDevissage.ofField`: the dévissage itself, for an arbitrary prime of `k` (which
  is necessarily `⊥`), so that it can be plugged in at `q.under R` with no transport.
* `Module.nonempty_completeDevissage_field` and `Module.nonempty_devissageStage_field`: the two
  structures are inhabited. The second breaks the circularity described above, since
  `Module.DevissageStage` is the input of `Module.CompleteDevissage.cons` and of
  `Module.nonempty_completeDevissage_of_surjective_alpha`.

## What this does not witness

It does **not** witness `Module.NonemptyCompleteDevissageAt`, and therefore does not witness the
nonempty branch of `Module.CompleteDevissageAt`, which is what Stacks 05I4 is stated over. That
structure carries twelve further fields on top of a `Module.CompleteDevissage`, and nine of them
are routine for the dévissage below (`lowerPrime`, `lowerPrime_isPrime`, `lowerPrime_liesOver`,
`upperPrime`, `upperPrime_isPrime`, `upperPrime_under`, `upperPrime_unique`, `initial_under`,
`transition_under`: take every prime to be `⊥`, and `transition_under` is empty because there are
no transitions). The three that are not routine are
`Module.NonemptyCompleteDevissageAt.residueField_purelyTranscendental`,
`.lowerPrime_mem_fiberSupport` and `.relativeDimension_eq_support`, which occur in no proof
anywhere in the library and so have no supporting API. Discharging them for `k/k/k` amounts to
three identifications: that `PurelyTranscendental F F` holds along the residue-field map induced
by an isomorphism; that the support of the fibre module of `k` over `k` at `⊥` is the whole
one-point spectrum; and that both `Algebra.relativeDimension k k` and the pointed
`topologicalKrullDimAt` of that one-point support are `0`. Until those are in place, the
hypothesis set of Stacks 05I4 as stated over `Module.CompleteDevissageAt` has no witness with
`N` nonzero, and that should be read as an open obligation rather than as a defect in the
statements.

## References

* [Stacks Project, Tag 05HX](https://stacks.math.columbia.edu/tag/05HX)
* [Stacks Project, Tag 05HZ](https://stacks.math.columbia.edu/tag/05HZ)
* [Stacks Project, Tag 05I4](https://stacks.math.columbia.edu/tag/05I4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

/-- **An isomorphism of schemes has geometrically irreducible fibres.** For any field `K` and any
`y : Spec K ⟶ Y`, the base change of an isomorphism `f : X ⟶ Y` along `y` is an isomorphism onto
`Spec K`, which is irreducible because `K` is a domain.

Mathlib's `AlgebraicGeometry.GeometricallyIrreducible` has the base change, composition, open
immersion and restriction instances but none for an isomorphism. -/
public theorem AlgebraicGeometry.GeometricallyIrreducible.of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f] : GeometricallyIrreducible f := by
  constructor
  rw [geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ y
  exact (asIso (pullback.snd f y)).schemeIsoToHomeo.irreducibleSpace_iff.mpr inferInstance

/-- **The base change of a linear equivalence is bijective.** The base change of `e.symm` is a
two-sided inverse, by functoriality of `LinearMap.baseChange`. -/
public theorem LinearEquiv.bijective_baseChange {R M N A : Type*} [CommRing R] [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N] [CommRing A] [Algebra R A] (e : M ≃ₗ[R] N) :
    Function.Bijective (e.toLinearMap.baseChange A) := by
  exact (LinearEquiv.baseChange R A M N e).bijective

namespace Module

variable (k : Type u) [Field k]

/-- The extension of a prime of a field along the identity is prime: the prime is `⊥`, whose
extension is `⊥`, and `k` is a domain. -/
public theorem isPrime_map_algebraMap_self (r : Ideal k) [r.IsPrime] :
    (Ideal.map (algebraMap k k) r).IsPrime := by
  have hr : r = ⊥ := (Ideal.eq_bot_or_top r).resolve_right (‹r.IsPrime›).ne_top
  rw [hr, Ideal.map_bot]
  exact Ideal.isPrime_bot

/-- **A complete dévissage of `k/k/k` at any prime of a field `k`.** There is one stage: the
upper algebra, the lower algebra and the module are all `k`, every structure map is the identity,
and the multiplicity is `1`, so `alpha` is the canonical equivalence `(Fin 1 →₀ k) ≃ₗ[k] k`.

Every condition of Stacks 05HX holds for trivial reasons: `k` is smooth over itself, the
identity on `Spec k` has geometrically irreducible fibres by
`AlgebraicGeometry.GeometricallyIrreducible.of_isIso`, `alpha` is bijective so it is surjective
and stays bijective after any base change, and the fields indexed by `Fin stepCount` are empty
because `stepCount = 0`.

This is the base case that `Module.CompleteDevissage.head` and `Module.CompleteDevissage.cons`
never provided. -/
public noncomputable def CompleteDevissage.ofField (r : Ideal k) [r.IsPrime] :
    CompleteDevissage k k k r := by
  refine
    { stepCount := 0
      A := fun _ => k
      B := fun _ => k
      M := fun _ => k
      toA₀ := AlgHom.id k k
      toLeft := fun _ => AlgHom.id k k
      toRight := fun i => Fin.elim0 i
      multiplicity := fun _ => 1
      alpha := fun _ => (Finsupp.uniqueLinearEquiv k k (0 : Fin 1)).toLinearMap
      finiteM := fun _ => inferInstance
      initial_surjective := Function.surjective_id
      initial_finitePresentation := RingHom.FinitePresentation.id k
      transition_surjective := fun i => Fin.elim0 i
      transition_finitePresentation := fun i => Fin.elim0 i
      left_finite := fun _ => RingHom.Finite.id k
      smooth := fun _ => inferInstance
      geometricallyIrreducibleFibers := fun _ => ?_
      initialEquiv := LinearEquiv.refl k k
      cokerEquiv := fun i => Fin.elim0 i
      map_isPrime := fun _ => isPrime_map_algebraMap_self k r
      fiber_bijective := fun _ => ?_
      final_surjective := ?_ }
  · rw [show CommRingCat.ofHom (algebraMap k k) = 𝟙 (CommRingCat.of k) from rfl]
    exact GeometricallyIrreducible.of_isIso _
  · exact LinearEquiv.bijective_baseChange (Finsupp.uniqueLinearEquiv k k (0 : Fin 1))
  · exact (Finsupp.uniqueLinearEquiv k k (0 : Fin 1)).surjective

/-- The one-stage dévissage of `Module.CompleteDevissage.ofField` has stage count `0`, hence
exactly one stage. In particular it is not an empty family: the index type `Fin (stepCount + 1)`
of its stages is nonempty. -/
@[simp]
public theorem CompleteDevissage.stepCount_ofField (r : Ideal k) [r.IsPrime] :
    (CompleteDevissage.ofField k r).stepCount = 0 := rfl

/-- The multiplicity of the single stage of `Module.CompleteDevissage.ofField` is `1`, so the
summand it contributes is `k` itself and not a zero module. -/
@[simp]
public theorem CompleteDevissage.multiplicity_ofField (r : Ideal k) [r.IsPrime]
    (i : Fin ((CompleteDevissage.ofField k r).stepCount + 1)) :
    (CompleteDevissage.ofField k r).multiplicity i = 1 := rfl

/-- **`Module.CompleteDevissage` is inhabited**, with a nonzero module: the hypothesis of every
theorem in this library that takes a complete dévissage is satisfiable, and not only by the zero
module. -/
public theorem nonempty_completeDevissage_field (r : Ideal k) [r.IsPrime] :
    Nonempty (CompleteDevissage k k k r) :=
  ⟨CompleteDevissage.ofField k r⟩

/-- **`Module.DevissageStage` is inhabited.** This is what breaks the circularity in the dévissage
API: `Module.CompleteDevissage.head` is the only producer of a stage and needs a dévissage, while
`Module.CompleteDevissage.cons` and
`Module.nonempty_completeDevissage_of_surjective_alpha` consume one. -/
public theorem nonempty_devissageStage_field (r : Ideal k) [r.IsPrime] :
    Nonempty (DevissageStage k k k r) :=
  ⟨(CompleteDevissage.ofField k r).head⟩

end Module

end
