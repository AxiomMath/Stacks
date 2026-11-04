module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Flatness of a finite product of modules and of algebras

A product indexed by a finite type is the direct sum of its factors, and arbitrary direct sums
of flat modules are flat.  Hence a finite product of flat modules is flat, and the ring
homomorphism `RingHom.pi f` into a finite product of algebras is flat as soon as each `f i`
is.

Faithful flatness of such a product map is
`StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.RingHomPi`'s
`RingHom.FaithfullyFlat.pi`; what is proved here is only that it is insensitive to raising the
universe of all the rings involved, since the universe lift is a ring isomorphism on each
factor.

## Main results

* `Module.Flat.pi`: a product of flat modules over a finite index type is flat.
* `RingHom.Flat.pi`: `RingHom.pi f` is flat when each component is.
* `RingHom.FaithfullyFlat.pi_ulift`: faithful flatness of `RingHom.pi f` is unchanged by raising
  the universe of all the rings.
-/

@[expose] public section

universe u v w t

/-- A product of flat modules over a finite index type is flat: the product is the direct sum,
and direct sums of flat modules are flat. -/
public theorem Module.Flat.pi {R : Type u} [CommRing R] {ι : Type v} [_root_.Finite ι]
    (M : ι → Type w) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Flat R (M i)] : Module.Flat R (∀ i, M i) := by
  classical
  cases nonempty_fintype ι
  exact Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype R ι M).symm

/-- A ring homomorphism into a product, over a finite index type, of flat algebras is flat. -/
public theorem RingHom.Flat.pi {R : Type u} [CommRing R] {ι : Type v} [_root_.Finite ι]
    {A : ι → Type w} [∀ i, CommRing (A i)] (f : ∀ i, R →+* A i) (hf : ∀ i, (f i).Flat) :
    (RingHom.pi f).Flat := by
  let inst : ∀ i, Algebra R (A i) := fun i ↦ (f i).toAlgebra
  have hflat : ∀ i, Module.Flat R (A i) := fun i ↦ hf i
  exact RingHom.flat_algebraMap_iff.mpr (Module.Flat.pi A)

/-- Faithful flatness of a ring homomorphism into a product is unchanged by raising the universe
of all the rings: the universe lift is a ring isomorphism on each factor, and faithful flatness
is stable under composition with isomorphisms on either side. -/
public theorem RingHom.FaithfullyFlat.pi_ulift {R : Type u} [CommRing R] {ι : Type v}
    (A : ι → Type w) [∀ i, CommRing (A i)]
    (f : ∀ i, R →+* A i) (h : (RingHom.pi f).FaithfullyFlat) :
    (RingHom.pi (fun i ↦ (f i).ulift.{t, t})).FaithfullyFlat := by
  let e : (∀ i, A i) ≃+* ∀ i, ULift.{t} (A i) :=
    RingEquiv.piCongrRight (fun _ ↦ ULift.ringEquiv.symm)
  have hf : (RingHom.pi (fun i ↦ (f i).ulift.{t, t})) =
      e.toRingHom.comp ((RingHom.pi f).comp ULift.ringEquiv.toRingHom) := rfl
  rw [hf]
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective] at h ⊢
  have he := RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp
    (RingHom.FaithfullyFlat.of_bijective (f := e.toRingHom) e.bijective)
  have hd := RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp
    (RingHom.FaithfullyFlat.of_bijective
      (f := (ULift.ringEquiv : ULift.{t} R ≃+* R).toRingHom) ULift.ringEquiv.bijective)
  exact ⟨hd.1.comp h.1 |>.comp he.1, hd.2.comp (h.2.comp he.2)⟩

end
