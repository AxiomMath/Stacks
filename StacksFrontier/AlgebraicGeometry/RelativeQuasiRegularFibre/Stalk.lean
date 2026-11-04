module

public import StacksFrontier.AlgebraicGeometry.RelativeQuasiRegularFibre.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.EssentialFinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# The local step of Stacks tag 063U at a stalk of a scheme

`RelativeQuasiRegularFibre/Basic.lean` proves that a quasi-regular sequence in the maximal ideal
of a flat local algebra, essentially of finite presentation and essentially of finite type, whose
quotient is again flat over the base, is a regular sequence. This file puts that statement where
Stacks tag 063U needs it: at the stalk `𝒪_{X, x}` of a morphism `p : X ⟶ S` which is flat and
locally of finite presentation.

All four hypotheses of the local step are discharged from `p` alone:

* flatness of the stalk map is `AlgebraicGeometry.Flat.stalkMap`;
* locality is `p.toLRSHom.prop x`;
* essential finite type is `AlgebraicGeometry.LocallyOfFiniteType.stalkMap`;
* essential finite *presentation* is
  `AlgebraicGeometry.LocallyOfFinitePresentation.essentiallyOfFinitePresentation_stalkMap`, of
  `StacksFrontier/AlgebraicGeometry/Flatness/EssentialFinitePresentation.lean`.

The last of these was recorded as a missing dependency of tag 063U. It is not missing.

## Main results

* `isRegular_of_isQuasiRegular_of_flat_quotient_hom`: the local step with the algebra structures
  given by a ring homomorphism rather than by instances, so that a caller who has only a map in
  hand need not install them.
* `isRegular_germ_of_isQuasiRegular`: the local step at a stalk of a flat, locally finitely
  presented morphism of schemes.

## Implementation notes

Flatness of the quotient is stated as `RingHom.Flat` of the composite `R → T → T/(f)` rather than
as `Module.Flat`, which would need an `Algebra` instance in the statement. Inside the proof the
`Algebra R (T/(f))` structure obtained from that composite and the one `Ideal.Quotient.algebra`
derives from `φ.toAlgebra` are definitionally equal, so the two `Module.Flat` statements are
interchanged by `have` and no transport lemma is needed.

## What is not done

Stacks tag 063U is **not** proved and no `stacks` attribute is attached. The hypothesis `hq`
here — flatness of the quotient of the stalk by the sequence — is what a proof of tag 063U would
get from flatness of `Z ⟶ S` together with an identification of `𝒪_{Z, x}` with that quotient;
neither that identification nor the shrinking needed at the points outside `Z` is supplied here.

## References

* [Stacks Project, Lemma 10.99.3 (Tag 0470)](https://stacks.math.columbia.edu/tag/0470)
* [Stacks Project, Lemma 31.23.4 (Tag 063U)](https://stacks.math.columbia.edu/tag/063U)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingTheory.Sequence

universe u

namespace Stacks.AlgebraicGeometry.RelativeQuasiRegularFibre

/-- **The local step of Stacks tag 063U, in ring-homomorphism form.** Let `φ : R → T` be a local
homomorphism of local rings which is flat, essentially of finite type and essentially of finite
presentation. A quasi-regular sequence `f` in the maximal ideal of `T` for which the composite
`R → T → T/(f)` is flat is a regular sequence in `T`. -/
theorem isRegular_of_isQuasiRegular_of_flat_quotient_hom {R T : Type u} [CommRing R] [CommRing T]
    [IsLocalRing R] [IsLocalRing T] (φ : R →+* T) [IsLocalHom φ] (hflat : φ.Flat)
    (heft : φ.EssFiniteType) (hefp : φ.EssentiallyOfFinitePresentation) {r : ℕ} (f : Fin r → T)
    (hmem : ∀ i, f i ∈ IsLocalRing.maximalIdeal T)
    (hqr : IsQuasiRegular T (List.ofFn f))
    (hq : ((Ideal.Quotient.mk (Ideal.span (Set.range f))).comp φ).Flat) :
    IsRegular T (List.ofFn f) := by
  let : Algebra R T := φ.toAlgebra
  have : Module.Flat R T := hflat
  have : Algebra.EssFiniteType R T := heft
  have hquot : Module.Flat R (T ⧸ Ideal.span (Set.range f)) := hq
  exact (isRegular_and_flat_quotient_of_isQuasiRegular hefp f hmem hqr hquot).1

/-- **The local step of Stacks tag 063U at a stalk.** Let `p : X ⟶ S` be flat and locally of
finite presentation and let `x` be a point of `X`. A quasi-regular sequence in the maximal ideal
of `𝒪_{X, x}` whose quotient is flat over `𝒪_{S, p x}` is a regular sequence in `𝒪_{X, x}`. -/
theorem isRegular_germ_of_isQuasiRegular {X S : Scheme.{u}} (p : X ⟶ S) [Flat p]
    [LocallyOfFinitePresentation p] (x : X) {r : ℕ} (f : Fin r → X.presheaf.stalk x)
    (hmem : ∀ i, f i ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hqr : IsQuasiRegular (X.presheaf.stalk x) (List.ofFn f))
    (hq : ((Ideal.Quotient.mk (Ideal.span (Set.range f))).comp (p.stalkMap x).hom).Flat) :
    IsRegular (X.presheaf.stalk x) (List.ofFn f) :=
  have : IsLocalHom (p.stalkMap x).hom := p.toLRSHom.prop x
  isRegular_of_isQuasiRegular_of_flat_quotient_hom (p.stalkMap x).hom
    (AlgebraicGeometry.Flat.stalkMap p x)
    (AlgebraicGeometry.LocallyOfFiniteType.stalkMap p x)
    (AlgebraicGeometry.LocallyOfFinitePresentation.essentiallyOfFinitePresentation_stalkMap p x)
    f hmem hqr hq

end Stacks.AlgebraicGeometry.RelativeQuasiRegularFibre

end
