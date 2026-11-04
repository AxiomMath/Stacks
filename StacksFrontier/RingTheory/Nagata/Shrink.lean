module

public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import StacksFrontier.RingTheory.Nagata.Defs

/-!
# Reading N-2 at an arbitrary extension: shrinking into the base ring's universe

The Nagata conditions of `StacksFrontier.RingTheory.Nagata.Defs` test a ring against the finite field
extensions of its fraction field that live in **the ring's own universe**. Nothing is lost by that
— a finite extension of a field in `Type u` is `Small.{u}` — but every argument that has to move
one of those conditions between universes needs the shrinking machinery, and needs it *before*
any of the Nagata files. That is what this module is: it sits directly on `Nagata.Defs` and is
imported across the Nagata tree.

## Main results

* `small_of_finite_field`: a finite-dimensional vector space over a field in `Type u` is
  `Small.{u}` — the fact that makes the shrinking possible at all.
* `shrink_isScalarTower`: a scalar tower transports onto the shrunk copy.
* `Module.Finite.integralClosure_of_ringEquiv`: module-finiteness of an integral closure inside a
  fixed ring passes along a ring isomorphism of the base, across universes.
* `module_finite_integralClosure_of_isJapaneseRing`: an N-2 domain has module-finite integral
  closure in any finite extension of any of its fraction fields, in any universes. This is the
  form every consumer wants, and it lives here — upstream of the whole Nagata tree — because four
  files had grown their own private copy of it.

## Implementation notes

The shrinking lemmas are needed both by `Nagata.Basic` and by the transport lemmas of
`Nagata.Japanese`; `Nagata.Basic` is downstream of `Nagata.Japanese`, so they live here rather than
being duplicated. `Nagata.Basic` imports this module, so its own uses are unaffected.

`module_finite_integralClosure_of_isJapaneseRing` is here for the same reason, one level further
out: four files need it, and the only home visible to all of them without
dragging in `Nagata.Japanese`’s scheme theory is a module resting on `Nagata.Defs` alone.

`Module.Finite.of_equiv_equiv` is what carries finiteness when both the base ring and the ambient
ring move, and `RingEquiv.isIntegral_iff` is what identifies the two integral closures; neither
constrains universes, so the third lemma is polymorphic in all three.
-/

@[expose] public section

universe u v w uR uS

/-- A finite-dimensional vector space over a field `E : Type u` is `Small.{u}`
(its cardinality is bounded by `E`, since it is `E`-linearly isomorphic to `Fin n → E`). -/
theorem small_of_finite_field {E : Type u} [Field E] (M : Type v) [AddCommGroup M] [Module E M]
    [Module.Finite E M] : Small.{u} M := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin (R := E) (M := M)
  refine small_of_surjective (f := Fintype.linearCombination E f) ?_
  rwa [← LinearMap.range_eq_top, Fintype.range_linearCombination]

/-- Shrinking a ring along `Small` transports a scalar tower `R ⊂ S ⊂ M`. -/
theorem shrink_isScalarTower {R : Type uR} {S : Type uS} {M : Type v}
    [CommRing R] [CommRing S] [CommRing M]
    [Algebra R S] [Algebra R M] [Algebra S M] [IsScalarTower R S M]
    [Small.{w} M] :
    IsScalarTower R S (Shrink.{w} M) := by
  refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
  apply (Shrink.algEquiv S M).injective
  rw [(Shrink.algEquiv S M).commutes, ← IsScalarTower.algebraMap_apply R S M]
  exact (Shrink.algEquiv R M).commutes x

/-- Module-finiteness of the integral closure inside a fixed ring passes along a ring isomorphism
of the base, across universes.

The two integral closures have the same elements, by `RingEquiv.isIntegral_iff`, so the identity
on `L` induces a ring isomorphism between them over which the base isomorphism is compatible;
`Module.Finite.of_equiv_equiv` then moves finiteness across both at once. -/
theorem Module.Finite.integralClosure_of_ringEquiv {R : Type u} {S : Type v} {L : Type w}
    [CommRing R] [CommRing S] [CommRing L] [Algebra R L] [Algebra S L] (e : R ≃+* S)
    (hcomp : (algebraMap S L).comp (e : R →+* S) = algebraMap R L)
    (h : Module.Finite R (integralClosure R L)) :
    Module.Finite S (integralClosure S L) := by
  have hmem : ∀ x : L, x ∈ integralClosure R L ↔ x ∈ integralClosure S L := fun x => by
    simpa only [mem_integralClosure_iff] using RingEquiv.isIntegral_iff e hcomp x
  let e₂ : ↥(integralClosure R L) ≃+* ↥(integralClosure S L) :=
    { toFun := fun z => ⟨z.1, (hmem z.1).mp z.2⟩
      invFun := fun z => ⟨z.1, (hmem z.1).mpr z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  exact Module.Finite.of_equiv_equiv e e₂ (by
    ext r
    show algebraMap S L (e r) = algebraMap R L r
    rw [← hcomp]
    rfl)

/-- **An N-2 domain has module-finite integral closure in any finite extension of any of its
fraction fields, whatever universes those live in.**

`IsJapaneseRing A` reads the condition only at `FractionRing A` and only for extensions in `A`'s
own universe; this is the form every consumer actually wants. Both restrictions come off here, and
this is the one place either costs anything:

* an arbitrary field of fractions `F` is identified with `FractionRing A` by
  `FractionRing.algEquiv`, along which `L` becomes a finite extension of `FractionRing A`;
* `L` is then finite-dimensional over `FractionRing A : Type u`, hence `Small.{u}` by
  `small_of_finite_field`, so `Shrink.{u} L` is a legitimate test object for the hypothesis, and
  the resulting finiteness returns to `L` along `Shrink.algEquiv`, an `A`-algebra equivalence, so
  the base ring never moves. -/
theorem module_finite_integralClosure_of_isJapaneseRing {A : Type u} [CommRing A] [IsDomain A]
    (hA : IsJapaneseRing A) (F : Type w) [Field F] [Algebra A F] [IsFractionRing A F]
    (L : Type v) [Field L] [Algebra A L] [Algebra F L] [IsScalarTower A F L]
    [FiniteDimensional F L] :
    Module.Finite A (integralClosure A L) := by
  -- Replace `F` by `FractionRing A`, which is where the hypothesis reads.
  let e : FractionRing A ≃ₐ[A] F := FractionRing.algEquiv A F
  let _ : Algebra (FractionRing A) L := ((algebraMap F L).comp e.toRingHom).toAlgebra
  have hmap : algebraMap (FractionRing A) L = (algebraMap F L).comp e.toRingHom :=
    RingHom.algebraMap_toAlgebra _
  have htowerA : IsScalarTower A (FractionRing A) L :=
    .of_algebraMap_eq fun x => by simp [hmap, ← IsScalarTower.algebraMap_apply]
  have hfin : Module.Finite (FractionRing A) L := by
    rw [← RingHom.finite_algebraMap, hmap]
    exact (RingHom.finite_algebraMap.mpr inferInstance).comp (RingEquiv.finite e.toRingEquiv)
  -- Now shrink `L` into `A`'s universe, where the hypothesis applies.
  have hsmall : Small.{u} L := small_of_finite_field (E := FractionRing A) L
  have htower : IsScalarTower A (FractionRing A) (Shrink.{u} L) :=
    shrink_isScalarTower (R := A) (S := FractionRing A) (M := L)
  have hfd : FiniteDimensional (FractionRing A) (Shrink.{u} L) :=
    Module.Finite.equiv (Shrink.algEquiv (FractionRing A) L).symm.toLinearEquiv
  -- The `FiniteDimensional` instance on the shrunk copy is supplied rather than synthesized.
  have hshrunk : Module.Finite A (integralClosure A (Shrink.{u} L)) :=
    @IsJapaneseRing.finite A _ _ hA (Shrink.{u} L) _ _ _ htower hfd
  exact Module.Finite.equiv (Shrink.algEquiv A L).mapIntegralClosure.toLinearEquiv

end
