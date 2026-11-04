module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PropertyAPushforward

/-!
# Direct image of abelian sheaves along an integral or separated locally quasi-finite morphism

Let `f : X ⟶ Y` be a morphism of schemes which is either integral, or separated and locally
quasi-finite. Direct image of abelian sheaves along the induced morphism of small étale sites is
then faithful, reflects injections and surjections, and the counit `f^{-1} f_* F ⟶ F` of the
inverse-image/direct-image adjunction is surjective.

Either hypothesis supplies property (A), the first through the integral case and the second
through the separated locally quasi-finite case; the three conclusions are then the conclusions
of direct image along a morphism with property (A).

## Main results

* `AlgebraicGeometry.hasPropertyA_of_isIntegralHom_or_separated_locallyQuasiFinite` — a morphism
  which is integral, or separated and locally quasi-finite, has property (A).
* `smallEtalePushforwardAb_properties_of_isIntegralHom_or_locallyQuasiFinite` (in the namespace
  `Stacks.EtaleCohomology`) — for such a morphism the counit of the adjunction is surjective,
  direct image is faithful, and direct image reflects injections and surjections.

## Implementation notes

Abelian sheaves are sheaves valued in `Ab`, and injections and surjections of abelian sheaves are
the monomorphisms and the epimorphisms. Being quasi-finite in the sense of `LocallyQuasiFinite`
does not include being locally of finite type, so the second alternative is spelled out as
`IsSeparated f ∧ LocallyOfFiniteType f ∧ LocallyQuasiFinite f`.

## References

* [Stacks Project, Tag 04C9](https://stacks.math.columbia.edu/tag/04C9)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes which is integral, or separated and locally quasi-finite, has
property (A). -/
public theorem hasPropertyA_of_isIntegralHom_or_separated_locallyQuasiFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : IsIntegralHom f ∨ (IsSeparated f ∧ LocallyOfFiniteType f ∧ LocallyQuasiFinite f)) :
    HasPropertyA f := by
  intro U p hp u
  obtain hi | ⟨hsep, hft, hqf⟩ := hf
  · have := hi
    exact hasPropertyA_of_isIntegralHom f p u
  · have := hsep
    have := hft
    have := hqf
    exact hasPropertyA_of_locallyQuasiFinite f p u

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

/-- Let `f : X ⟶ Y` be a morphism of schemes which is either integral, or separated and locally
quasi-finite. Then the counit `f^{-1} f_* F ⟶ F` is surjective for every abelian sheaf `F` on the
small étale site of `X`, direct image of abelian sheaves along the small étale sites is faithful,
and it reflects injections and surjections. -/
@[stacks 04C9]
public theorem smallEtalePushforwardAb_properties_of_isIntegralHom_or_locallyQuasiFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : IsIntegralHom f ∨ (IsSeparated f ∧ LocallyOfFiniteType f ∧ LocallyQuasiFinite f)) :
    (∀ F : Sheaf (smallEtaleTopology X) Ab.{u + 1},
        Epi ((smallEtaleAdjunctionAb f).counit.app F)) ∧
      (smallEtalePushforwardAb f).Faithful ∧
      (smallEtalePushforwardAb f).ReflectsMonomorphisms ∧
      (smallEtalePushforwardAb f).ReflectsEpimorphisms :=
  have h := smallEtalePushforwardAb_properties_of_hasPropertyA f
    (hasPropertyA_of_isIntegralHom_or_separated_locallyQuasiFinite f hf)
  ⟨h.2.2.1, h.2.2.2, h.1, h.2.1⟩

end Stacks.EtaleCohomology

end
