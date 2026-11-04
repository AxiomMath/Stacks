module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleHilbertPolynomial

/-!
# The Euler characteristic of a coherent triple with both members zero

A coherent triple `T` whose two members are zero sits in the short exact sequence
`0 → T → T → T → 0` with both maps zero, so additivity of the Euler characteristic
([Stacks, Tag 0F26]) gives `χ(T) = χ(T) + χ(T)`, that is, `χ(T) = 0`.

## Main definitions

* `Stacks.Algebraization.CoherentTriple.zeroHom`: the zero endomorphism of a coherent triple.

## Main results

* `Stacks.Algebraization.CoherentTriple.shortExact_zero_of_isZero`: a coherent triple with both
  members zero sits in a short exact sequence with itself in all three places and both maps
  zero.
* `Stacks.Algebraization.CoherentTriple.eulerCharacteristic_eq_zero_of_isZero`: **the Euler
  characteristic of a coherent triple with both members zero vanishes.**

## References

* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
* [Stacks Project, Tag 0F26](https://stacks.math.columbia.edu/tag/0F26)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace Stacks.Algebraization

/-- The zero endomorphism of a coherent triple: both of its components are zero. -/
public noncomputable def CoherentTriple.zeroHom {A : Type u} [CommRing A] [IsLocalRing A] {f : A}
    (T : CoherentTriple A f) : T.Hom T where
  onPunctured := 0
  onClosedFibre := 0
  compatible := by simp

/-- A zero object sits in a short exact sequence with itself in all three places. -/
private theorem shortExact_zero_of_isZero_obj {C : Type*} [Category C] [Abelian C] {X : C}
    (hX : IsZero X) : (ShortComplex.mk (0 : X ⟶ X) (0 : X ⟶ X) (by simp)).ShortExact :=
  .mk' (ShortComplex.exact_of_isZero_X₂ _ hX) ⟨fun g h _ => hX.eq_of_tgt g h⟩
    ⟨fun g h _ => hX.eq_of_src g h⟩

/-- **A coherent triple with both members zero sits in a short exact sequence with itself in all
three places**, both maps being zero. -/
public theorem CoherentTriple.shortExact_zero_of_isZero {A : Type u} [CommRing A] [IsLocalRing A]
    {f : A} {T : CoherentTriple A f} (hF : IsZero T.F) (hF₀ : IsZero T.F₀) :
    CoherentTriple.ShortExact T.zeroHom T.zeroHom := by
  exact { zero_punctured := by simp [CoherentTriple.zeroHom]
          zero_closedFibre := by simp [CoherentTriple.zeroHom]
          punctured := shortExact_zero_of_isZero_obj hF
          closedFibre := shortExact_zero_of_isZero_obj hF₀ }

/-- **The Euler characteristic of a coherent triple with both members zero vanishes.** -/
public theorem CoherentTriple.eulerCharacteristic_eq_zero_of_isZero {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] {f : A} (hf : f ∈ maximalIdeal A) (hreg : IsRegular f)
    {T : CoherentTriple A f} (hF : IsZero T.F) (hF₀ : IsZero T.F₀) :
    T.eulerCharacteristic hf hreg = 0 := by
  have h := CoherentTriple.eulerCharacteristic_add_of_shortExact hf hreg
    (CoherentTriple.shortExact_zero_of_isZero hF hF₀)
  omega

end Stacks.Algebraization

end
