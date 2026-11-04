module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.Basic
public import StacksFrontier.RingTheory.Dualizing.FlatLocalGorenstein

/-!
# Gorenstein schemes: agreement with the notion for rings

Section 0AWV of the Stacks project ([Stacks, Tag 0AWV]) defines a scheme to be Gorenstein when it
is locally Noetherian and all of its local rings are Gorenstein (Definition 0AWW,
`AlgebraicGeometry.IsGorenstein`), and observes that this definition makes sense because a
Noetherian ring is Gorenstein if and only if all of its local rings are (Definition 0DW7,
`Dualizing.IsGorensteinRing`). The content of that observation is that the two notions agree on
an affine scheme: for a Noetherian ring `R`, `Spec R` is a Gorenstein scheme exactly when `R` is a
Gorenstein ring. This file proves it.

## Main results

* `AlgebraicGeometry.isGorenstein_Spec_iff` — `Spec R` is Gorenstein if and only if `R` is a
  Gorenstein ring, for a Noetherian ring `R`.

## Implementation notes

The local ring of `Spec R` at a prime `𝔭` is a localization of `R` at `𝔭`
(`AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk`), and the Gorenstein property of a
Noetherian local ring is invariant under ring isomorphisms
(`Dualizing.isGorensteinLocalRing_of_ringEquiv`).

## References

* [Stacks Project, Section 0AWV](https://stacks.math.columbia.edu/tag/0AWV)
* [Stacks Project, Tag 0AWW](https://stacks.math.columbia.edu/tag/0AWW)
* [Stacks Project, Tag 0DW7](https://stacks.math.columbia.edu/tag/0DW7)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

add_to_stacks 0AWV "the definition of the section: a scheme is Gorenstein if it is locally \
  Noetherian and all of its local rings are Gorenstein" AlgebraicGeometry.IsGorenstein

/-- The local ring of `Spec R` at `x` is isomorphic to the localization of `R` at `x`. -/
private theorem nonempty_ringEquiv_stalk_Spec (R : CommRingCat.{u}) (x : Spec R)
    [x.asIdeal.IsPrime] :
    Nonempty (Localization.AtPrime x.asIdeal ≃+* (Spec R).presheaf.stalk x) := by
  let : Algebra R ((Spec R).presheaf.stalk x) := StructureSheaf.stalkAlgebra R x
  have : IsLocalization.AtPrime ((Spec R).presheaf.stalk x) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R x
  exact ⟨(IsLocalization.algEquiv x.asIdeal.primeCompl _ _).toRingEquiv⟩

/-- **The definition of a Gorenstein scheme agrees with that of a Gorenstein ring** (Section
0AWV). For a Noetherian ring `R`, the scheme `Spec R` is Gorenstein if and only if `R` is a
Gorenstein ring, i.e. all of its local rings are Gorenstein. -/
@[stacks 0AWV "the definition makes sense: for a Noetherian ring R, Spec R is a Gorenstein scheme \
if and only if R is a Gorenstein ring"]
theorem isGorenstein_Spec_iff (R : CommRingCat.{u}) [IsNoetherianRing R] :
    IsGorenstein (Spec R) ↔ Dualizing.IsGorensteinRing R := by
  constructor
  · intro hX p hp
    let x : Spec R := ⟨p, hp⟩
    obtain ⟨e⟩ := nonempty_ringEquiv_stalk_Spec R x
    have := isNoetherianRing_of_ringEquiv _ e
    exact Dualizing.isGorensteinLocalRing_of_ringEquiv e (IsGorenstein.isGorensteinLocalRing x)
  · intro hR
    refine { isGorensteinLocalRing := fun x => ?_ }
    have : x.asIdeal.IsPrime := x.isPrime
    obtain ⟨e⟩ := nonempty_ringEquiv_stalk_Spec R x
    have := isNoetherianRing_of_ringEquiv _ e
    exact Dualizing.isGorensteinLocalRing_of_ringEquiv e.symm (hR x.asIdeal)

end AlgebraicGeometry

end
