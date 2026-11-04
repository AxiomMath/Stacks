module

public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.RingHom.Flat
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.RingTheory.Dualizing.GorensteinTransport

/-!
# A flat morphism with Gorenstein source, granting the closed-fibre statement

A flat morphism of locally Noetherian schemes whose source is Gorenstein should be a Gorenstein
morphism: being Gorenstein at a point means being flat there and having a Gorenstein local ring
on the fibre, and the local ring of the fibre is the quotient of the local ring of the source by
the extended maximal ideal of the local ring of the target. So the scheme-theoretic content is
entirely the ring-theoretic assertion that the *closed fibre* of a flat local homomorphism of
Noetherian local rings with Gorenstein target is Gorenstein.

**That ring-theoretic assertion IS proved in this library, so the two results below are
superseded.** The full equivalence is `Dualizing.isGorensteinLocalRing_iff_of_flat` in
`StacksFrontier/RingTheory/Dualizing/FlatLocalGorenstein.lean` (line 681, carrying `@[stacks 0BJL]`),
and `Stacks.Duality.isGorenstein_of_flat` in
`StacksFrontier/AlgebraicGeometry/Duality/GorensteinMorphismOfFlat.lean` already deduces the
scheme-level Tag 0C12 from it with no hypothesis at all.

The conditional forms below are kept as public declarations:
`Stacks.Duality.ClosedFibreGorensteinOfFlat` records the assertion as a `Prop`,
and the two results below take it as an explicit hypothesis, so nothing here assumes it silently.
New callers should use the unconditional route instead. Given the hypothesis, the passage from a
Gorenstein scheme to a Gorenstein morphism runs through
`AlgebraicGeometry.quotientStalkEquivFiberStalk`, which identifies the local ring of the fibre
with the quotient, and `Dualizing.isGorensteinLocalRing_of_ringEquiv`, which moves
Gorensteinness across that identification.

The companion assertion about the base, that the local ring of the target is Gorenstein at every
point of the image, needs no hypothesis and is already
`Stacks.Duality.isGorensteinLocalRing_stalk_of_flat`.

## Main definitions

* `Stacks.Duality.ClosedFibreGorensteinOfFlat` — the ring-theoretic statement about closed
  fibres of flat local homomorphisms. It is *proved* elsewhere, as
  `Dualizing.isGorensteinLocalRing_iff_of_flat` (Tag 0BJL); this definition is retained only
  because the two results below quantify over it.

## Main results

* `Stacks.Duality.isGorensteinLocalRing_fiberStalk_of_flat` — granting the closed-fibre
  statement, the local ring of the scheme-theoretic fibre of a flat morphism with Gorenstein
  source is Gorenstein.
* `AlgebraicGeometry.Scheme.Hom.isGorenstein_of_flat` — granting the closed-fibre statement, a
  flat morphism of locally Noetherian schemes with Gorenstein source is a Gorenstein morphism.

## Implementation notes

`Stacks.Duality.ClosedFibreGorensteinOfFlat` is a `Prop`-valued definition rather than a
hypothesis written out at each use, because its statement has to install the nontrivial, local
and Noetherian structures on the quotient before it can name the Gorenstein property of it.
Those structures are propositions, so the ones it installs and the ones a user has in context
agree.

The locally Noetherian structure on a fibre is not an instance, so both results below carry it
in their statements as a `letI` taken from `AlgebraicGeometry.isLocallyNoetherian_fiber`, in the
same shape as `AlgebraicGeometry.Scheme.Hom.IsGorensteinAt`.

## References

* [Stacks Project, Tag 0C04](https://stacks.math.columbia.edu/tag/0C04)
* [Stacks Project, Tag 0AWW](https://stacks.math.columbia.edu/tag/0AWW)
* [Stacks Project, Tag 0BJL](https://stacks.math.columbia.edu/tag/0BJL)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Duality

/-- **The closed-fibre statement for a flat local homomorphism.** For every flat local
homomorphism `A → B` of Noetherian local rings with `B` Gorenstein, the closed fibre
`B ⧸ m_A B` is Gorenstein.

This is a statement, not a theorem. It is the half of the Gorenstein criterion for a flat local
homomorphism that this library does not prove, and the results below take it as an explicit
hypothesis. The other half, that `A` itself is Gorenstein, is
`Stacks.Duality.isGorensteinLocalRing_of_flat`. -/
public def ClosedFibreGorensteinOfFlat : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B] [Module.Flat A B]
    [IsLocalHom (algebraMap A B)], Dualizing.IsGorensteinLocalRing B →
    let I := (IsLocalRing.maximalIdeal A).map (algebraMap A B)
    let _ : Nontrivial (B ⧸ I) :=
      Ideal.Quotient.nontrivial_iff.mpr
        (IsLocalRing.map_maximalIdeal_lt_top (algebraMap A B)).ne
    let _ : IsLocalRing (B ⧸ I) :=
      IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    let _ : IsNoetherianRing (B ⧸ I) := Ideal.Quotient.isNoetherianRing I
    Dualizing.IsGorensteinLocalRing (B ⧸ I)

/-- **Granting the closed-fibre statement, the local ring of the scheme-theoretic fibre of a
flat morphism with Gorenstein source is Gorenstein.**

The stalk map of `f` at `x` is a flat local homomorphism of Noetherian local rings whose target
is Gorenstein, so the hypothesis applies to it, and
`AlgebraicGeometry.quotientStalkEquivFiberStalk` identifies its closed fibre with the local ring
of the scheme-theoretic fibre. -/
public theorem isGorensteinLocalRing_fiberStalk_of_flat
    (h : ClosedFibreGorensteinOfFlat.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.IsGorenstein X] [IsLocallyNoetherian Y] [Flat f] (x : X) :
    letI : IsLocallyNoetherian (f.fiber (f x)) := isLocallyNoetherian_fiber f (f x)
    Dualizing.IsGorensteinLocalRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) := by
  let : IsLocallyNoetherian (f.fiber (f x)) := isLocallyNoetherian_fiber f (f x)
  let R := Y.presheaf.stalk (f x)
  let A := X.presheaf.stalk x
  let : Algebra R A := (f.stalkMap x).hom.toAlgebra
  let : IsLocalHom (algebraMap R A) := by
    rw [RingHom.algebraMap_toAlgebra]
    infer_instance
  let : Module.Flat R A := RingHom.flat_algebraMap_iff.mp <| by
    rw [RingHom.algebraMap_toAlgebra]
    exact AlgebraicGeometry.Flat.stalkMap f x
  let I : Ideal A := (IsLocalRing.maximalIdeal R).map (algebraMap R A)
  let : Nontrivial (A ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (IsLocalRing.map_maximalIdeal_lt_top (algebraMap R A)).ne
  let : IsLocalRing (A ⧸ I) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  let : IsNoetherianRing (A ⧸ I) := Ideal.Quotient.isNoetherianRing I
  have hI : I = Ideal.map (f.stalkMap x).hom (IsLocalRing.maximalIdeal R) := rfl
  exact Dualizing.isGorensteinLocalRing_of_ringEquiv
    (((Ideal.quotEquivOfEq hI).trans (quotientStalkEquivFiberStalk f x)).symm)
    (h R A (AlgebraicGeometry.IsGorenstein.isGorensteinLocalRing x))

end Stacks.Duality

namespace AlgebraicGeometry.Scheme.Hom

/-- **Granting the closed-fibre statement, a flat morphism of locally Noetherian schemes with
Gorenstein source is a Gorenstein morphism.**

Local Noetherianity of the fibres is not an extra assumption: it follows from local
Noetherianity of the source, so it is packaged existentially, as the Gorenstein-morphism
predicate requires a proof of it. -/
public theorem isGorenstein_of_flat (h : Stacks.Duality.ClosedFibreGorensteinOfFlat.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.IsGorenstein X]
    [IsLocallyNoetherian Y] [Flat f] :
    ∃ hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y), IsGorenstein f hf :=
  ⟨isLocallyNoetherian_fiber f, fun x =>
    ⟨AlgebraicGeometry.Flat.stalkMap f x,
      Stacks.Duality.isGorensteinLocalRing_fiberStalk_of_flat h f x⟩⟩

end AlgebraicGeometry.Scheme.Hom
