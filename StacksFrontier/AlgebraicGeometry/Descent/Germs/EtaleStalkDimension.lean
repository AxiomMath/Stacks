module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.RingTheory.Etale.Height

/-!
# Étale morphisms preserve the dimension of local rings

An étale morphism of schemes does not change the Krull dimension of the local ring at a point:
the local ring of the source at a point and the local ring of the target at its image have the
same dimension.

## Main results

* `AlgebraicGeometry.ringKrullDim_stalk_eq_of_etale` states that the local rings at a point and
  at its image under an étale morphism have equal Krull dimension.

## Implementation notes

The local ring of a scheme at a point is the stalk of its structure sheaf, and its dimension is
`ringKrullDim`. Working on affine opens witnessing étaleness at the point, both stalks are
localisations of rings of sections at corresponding primes, so their dimensions are the heights
of those primes; the heights agree because an étale ring map preserves the height of a prime
lying over a given one.

## References

* [Stacks Project, Tag 04N8](https://stacks.math.columbia.edu/tag/04N8)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 04N8.** An étale morphism preserves the Krull dimension of local
rings at corresponding points. -/
@[stacks 04N8, ega "IV 17.6.4"]
theorem ringKrullDim_stalk_eq_of_etale {U V : Scheme.{u}} (f : U ⟶ V) [Etale f] (u : U) :
    ringKrullDim (U.presheaf.stalk u) = ringKrullDim (V.presheaf.stalk (f u)) := by
  obtain ⟨W, hW, huW, Z, hZ, hWZ, hf⟩ :=
    (etale_iff_forall_etaleAt f).mp ‹Etale f› u
  let q := (hW.primeIdealOf ⟨u, huW⟩).asIdeal
  let p := (hZ.primeIdealOf ⟨f u, hWZ huW⟩).asIdeal
  let _ := U.presheaf.algebra_section_stalk ⟨u, huW⟩
  let _ := V.presheaf.algebra_section_stalk ⟨f u, hWZ huW⟩
  let _ := hW.isLocalization_stalk ⟨u, huW⟩
  let _ := hZ.isLocalization_stalk ⟨f u, hWZ huW⟩
  have hpq : p = q.comap (f.appLE Z W hWZ).hom := congrArg PrimeSpectrum.asIdeal
    (IsAffineOpen.comap_primeIdealOf_appLE Z hZ W hW hWZ huW).symm
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q _,
    IsLocalization.AtPrime.ringKrullDim_eq_height p _]
  exact_mod_cast (RingHom.Etale.height_eq_height hf p q hpq).symm

end AlgebraicGeometry
