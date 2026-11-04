module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# A field is flat over any domain inside it

If `A` is a domain and `K` a field containing it, then `K` is flat as an `A`-module: the
inclusion factors through the fraction field `Frac A`, which is flat over `A` because it is a
localisation, and `K` is flat over `Frac A` because it is free over a field.

## Main results

* `Module.Flat.of_isDomain_of_field`: a field `K` with a faithful `A`-algebra structure over a
  domain `A` is flat over `A`.
* `Module.Flat.of_subalgebra_of_field`: a field `K` is flat over each of its subalgebras.

## Implementation notes

Instance search does **not** find this: `Module.Flat A K` fails `synthInstance` for
`[CommRing A] [IsDomain A] [Field K] [Algebra A K] [FaithfulSMul A K]`, and `exact?` does not
close it either (it exhausts the default heartbeat budget).  Mathlib's
`Mathlib/RingTheory/Flat/Domain.lean` is about tensor products over a domain rather than about
this, and `Mathlib/RingTheory/Flat/TorsionFree.lean` gives the torsion-free criterion only over a
Dedekind domain.

The `FaithfulSMul A K` hypothesis is exactly the injectivity of `algebraMap A K` that
`IsFractionRing.lift` needs; for a subalgebra it holds, and `of_subalgebra_of_field` supplies it.

The second half, that a field is flat over a subfield, is `Module.Flat.of_free`; it is the first
half that needs the fraction field, because `A ⟶ K` is not a localisation.
-/

@[expose] public section

open scoped nonZeroDivisors

universe u

/-- A field `K` containing a domain `A` is flat as an `A`-module.  The inclusion factors through
`Frac A`, which is flat over `A` as a localisation, and `K` is free over the field `Frac A`. -/
theorem Module.Flat.of_isDomain_of_field (A : Type u) (K : Type u) [CommRing A] [IsDomain A]
    [Field K] [Algebra A K] [FaithfulSMul A K] : Module.Flat A K := by
  classical
  have hinj : Function.Injective (algebraMap A K) := FaithfulSMul.algebraMap_injective A K
  let F := FractionRing A
  let g : F →+* K := IsFractionRing.lift (A := A) (K := F) (g := algebraMap A K) hinj
  let _ : Algebra F K := g.toAlgebra
  have : IsScalarTower A F K := IsScalarTower.of_algebraMap_eq fun x =>
    (IsFractionRing.lift_algebraMap (A := A) (K := F) (g := algebraMap A K) hinj x).symm
  have : Module.Flat A F := IsLocalization.flat F A⁰
  have : Module.Flat F K := Module.Flat.of_free
  exact Module.Flat.trans A F K

/-- A field is flat over each of its subalgebras. -/
theorem Module.Flat.of_subalgebra_of_field {k : Type u} (K : Type u) [Field k] [Field K]
    [Algebra k K] (A : Subalgebra k K) : Module.Flat A K :=
  have : FaithfulSMul A K := ⟨fun {_ _} h => Subtype.ext (by simpa using h 1)⟩
  Module.Flat.of_isDomain_of_field A K

end
