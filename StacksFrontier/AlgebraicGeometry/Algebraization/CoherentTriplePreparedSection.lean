module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleClosedPointIdeal

/-!
# Transporting a global section of `T.F` to a section of a prepared extension

A prepared extension `P : PreparedExtension A f T` carries an isomorphism `P.alpha'` identifying
the pullback of `P.F'` to the punctured spectrum with `T.F`. Composed with
`Scheme.Modules.restrictFunctorIsoPullback`, this identifies the *restriction* of `P.F'` to the
punctured spectrum with `T.F`, and since the restriction of a module along the inclusion of an
open `U` has the same sections over `⊤` as the module itself has over `U`
(`Scheme.Modules.restrict_obj`), a global section of `T.F` transports to a section of `P.F'` over
the open `puncturedSpectrum A` of `Spec A` -- equivalently, by
`Stacks.Algebraization.puncturedSpectrum_eq_idealComplement`, over the ideal-sheaf complement
spelling that `Stacks.Algebraization.exists_idealPow_hom_of_preparedExtension` consumes.

## Main results

* `Stacks.Algebraization.PreparedExtension.restrictIso`: the restriction of `P.F'` to the
  punctured spectrum is isomorphic to `T.F`.
* `Stacks.Algebraization.PreparedExtension.sectionOfPuncturedSpectrum`: a global section of `T.F`
  transports to a section of `P.F'` over the punctured spectrum of `Spec A`.
* `Stacks.Algebraization.PreparedExtension.sectionOnIdealComplement`: the same section, read at
  the ideal-sheaf-complement spelling of the punctured spectrum.

## References

* [Stacks Project, Tag 0F23](https://stacks.math.columbia.edu/tag/0F23)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Algebraization

/-- **The restriction of a prepared extension's module to the punctured spectrum is `T.F`.** The
composite of `Scheme.Modules.restrictFunctorIsoPullback` (restriction along an open immersion is
isomorphic to pullback) with the prepared extension's own `alpha'` (the pullback of `P.F'` to the
punctured spectrum is isomorphic to `T.F`). -/
public noncomputable def PreparedExtension.restrictIso
    {A : Type u} [CommRing A] [IsLocalRing A] {f : A} {T : CoherentTriple A f}
    (P : PreparedExtension A f T) :
    P.F'.restrict (Stacks.Divisors.puncturedSpectrum A).ι ≅ T.F :=
  ((Scheme.Modules.restrictFunctorIsoPullback
      (Stacks.Divisors.puncturedSpectrum A).ι).app P.F').trans P.alpha'

/-- **A global section of `T.F` gives a section of `P.F'` over the punctured spectrum.** Pushed
backwards through `P.restrictIso` and identified with a section over the open
`puncturedSpectrum A` of `Spec A` via `Scheme.Opens.ι_image_top`. -/
public noncomputable def PreparedExtension.sectionOfPuncturedSpectrum
    {A : Type u} [CommRing A] [IsLocalRing A] {f : A} {T : CoherentTriple A f}
    (P : PreparedExtension A f T) (s : Γ(T.F, ⊤)) :
    Γ(P.F', Stacks.Divisors.puncturedSpectrum A) := by
  rw [← Scheme.Opens.ι_image_top (U := Stacks.Divisors.puncturedSpectrum A)]
  exact P.restrictIso.inv.app ⊤ s

/-- **The transported section, read at the ideal-sheaf-complement spelling of the punctured
spectrum.** The exact input type that
`Stacks.Algebraization.exists_idealPow_hom_of_preparedExtension` consumes. -/
public noncomputable def PreparedExtension.sectionOnIdealComplement
    {A : Type u} [CommRing A] [IsLocalRing A] {f : A} {T : CoherentTriple A f}
    (P : PreparedExtension A f T) (s : Γ(T.F, ⊤)) :
    Γ(P.F', Stacks.LocalCohomology.idealComplement
      (Scheme.Hom.ker (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))) := by
  rw [← puncturedSpectrum_eq_idealComplement]
  exact P.sectionOfPuncturedSpectrum s

end Stacks.Algebraization

end
